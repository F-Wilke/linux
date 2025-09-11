#include <linux/device.h>
#include <linux/fs.h>
#include <linux/types.h>
#include <linux/init.h>
#include <linux/kernel.h>
#include <linux/printk.h>
#include <linux/module.h>
#include <linux/mutex.h>
#include <linux/uaccess.h>

#include <linux/proc_fs.h>
#include <linux/seq_file.h>
#include <linux/slab.h> // For kmalloc 

#include <linux/mm.h> // For vm_area_struct and remap_pfn_range
#include <linux/io.h>
#include <linux/vmalloc.h>
#include <linux/sched.h>   
#include <linux/elf.h>


// add/remove sym/strtabs for inserted/deleted modules


// ELF headers
// #define BASE_VADDR 0x400000
#define ALIGNMENT  0x100
#define MAX_SYM_LEN 128
#define ELFOSABI_SYSV		0	/* Alias.  */
#define STV_DEFAULT	0		/* Default symbol visibility rules */
#define SEEK_SET	0
#define MODULE_NAME "ker_libkallsyms"


#define MALLOC(size) kmalloc(size, GFP_KERNEL)
#define FREE(ptr) kfree(ptr)
#define PRINT_ERR(msg) pr_err(msg)
#define PRINT_INFOF(...) pr_info(__VA_ARGS__)

#define ELF32_ST_INFO(bind, type)	(((bind) << 4) + ((type) & 0xf))
#define ELF64_ST_INFO(bind, type)	ELF32_ST_INFO ((bind), (type))

// In-memory representation of a symbol provider (kernel or module).
// strtab must start with a leading '\0'. st_name fields are OFFSETS.
typedef struct lks_module {
	Elf64_Sym *symtab;        // Symbol table (no enforced leading NULL entry)
	unsigned int num_symtab;  // Number of symbols in symtab
	char *strtab;             // String table (starts with '\0')
	unsigned int strtab_size; // Total size in bytes of strtab
	char *name;
    void* next;               // Optional descriptive name
} lks_module_t;
    

extern const unsigned long kallsyms_addresses[];
extern const u8 kallsyms_names[];

extern const unsigned int kallsyms_num_syms;
extern const unsigned long kallsyms_relative_base;

extern const char kallsyms_token_table[];
extern const u16 kallsyms_token_index[];

extern const unsigned int kallsyms_markers[];
extern const u8 kallsyms_seqs_of_names[];

//functions we need from kallsyms
unsigned int kallsyms_expand_symbol(unsigned int off, char *result, size_t maxlen);
char kallsyms_get_symbol_type(unsigned int off);


struct seq_file *seq_file;
unsigned long file_size;

char *kallsyms_name_types;
unsigned long kallsyms_names_size;
unsigned long kallsyms_per_cpu_names_size;
unsigned long kallsyms_first_non_per_cpu_name_pos;
unsigned long kallsyms_per_cpu_symbol_count;

struct vm_area_struct *global_vma;
unsigned long global_vma_pos;
void * global_write_pos;
void * global_write_start;

lks_module_t* modules_head = NULL;
size_t modules_count = 0;

char zeros[1024] = {0}; 

//build elf type from char
uint8_t GetElfTypeForSymType(char type) {
    uint8_t st_type = STT_NOTYPE;
    uint8_t st_bind = STB_GLOBAL;

    switch (type) {
        case 'V': // weak
        case 'v': // weak
        case 'W': // weak
        case 'w': 
            st_bind = STB_WEAK; // weak, implies func?
        case 'T': 
        case 't':
            st_type = STT_FUNC; // function
            break;
        case 'A': //per-cpu
            st_type = 6; // STT_TLS
            break;
        case 'D':  // data object
        case 'd': 
        case 'b': 
        case 'B': 
        case 'C': //no occurence at time of writing
        case 'R': 
        case 'r': 
        case 'S': 
        case 's': 
            st_type = STT_OBJECT; // data object
            break;
        case 'G': 
        case 'g': 
            st_type = STT_SECTION; // no type
            break;
            
        case 'i': // GNU indirect function (local)
        case 'I': // GNU indirect function (global) -> does not exist in kernel elf.h
        case 'U': // undefined
        case 'N': // debug symbol
        default:
            break;
    }

    return ELF64_ST_INFO(st_bind, st_type);
}

// Build a single lks_module_t from (kernel) symbol data.
lks_module_t* make_lks_mod(char* nameTypes, unsigned long * addresses, unsigned int num_syms,
    unsigned long names_size, unsigned long first_name_pos,
    unsigned int (*decompress_func)(unsigned int off, char *result, size_t maxlen)) {
    if (!addresses || !nameTypes || !decompress_func || num_syms == 0) {
        PRINT_ERR("libkallsyms: make_lks_mod invalid args");
        return NULL;
    }

    // Allocate symbol table
    Elf64_Sym *symtab = (Elf64_Sym*)MALLOC(sizeof(Elf64_Sym) * num_syms);
    if (!symtab) {
        PRINT_ERR("libkallsyms: symtab alloc failed");
        return NULL;
    }
    memset(symtab, 0, sizeof(Elf64_Sym) * num_syms);

    // String table (caller passes total compressed->expanded size). Ensure leading NUL.
    char *strtab = (char*)MALLOC(names_size + 1);
    if (!strtab) { FREE(symtab); PRINT_ERR("libkallsyms: strtab alloc failed"); return NULL; }
    memset(strtab, 0, names_size );
    unsigned int str_off = 0; // running offset in strtab

    unsigned int off = first_name_pos;
    char symBuffer[MAX_SYM_LEN];
    unsigned int i;
    for (i = 0; i < num_syms; i++) {
        off = decompress_func(off, symBuffer, MAX_SYM_LEN);
        size_t len = strlen(symBuffer);
        if (str_off + len + 1 > names_size) { // +1 for future safety
            PRINT_ERR("libkallsyms: strtab overflow in make_lks_mod");
            FREE(symtab); FREE(strtab); return NULL;
        }
        memcpy(&strtab[str_off], symBuffer, len);
        strtab[str_off + len] = '\0';

        Elf64_Sym *s = &symtab[i];
        s->st_name = str_off; // offset into strtab
        s->st_info = GetElfTypeForSymType(nameTypes[i]);
        s->st_other = STV_DEFAULT;
        if (addresses[i] & (0xffffULL << 48)) {
            s->st_shndx = 1; // heuristic .text
        } else {
            s->st_shndx = SHN_ABS;
        }
        s->st_value = addresses[i];
        s->st_size = sizeof(void*);

        if (!(i % 100)) {
            PRINT_INFOF("libkallsyms: make_lks_mod sym %u name=%s type=%c addr=%lx\n", i, &strtab[str_off], nameTypes[i], s->st_value);
        }
        str_off += len + 1;
    }

    lks_module_t *m = (lks_module_t*)MALLOC(sizeof(lks_module_t));
    if (!m) { FREE(symtab); FREE(strtab); return NULL; }
    m->symtab = symtab;
    m->num_symtab = num_syms;
    m->strtab = strtab;
    m->strtab_size = str_off; // used portion
    m->name = NULL;
    return m;
}


unsigned long elfMaker_calcSize(lks_module_t *mods, unsigned int num_modules, uint8_t type) {
    if (!mods || num_modules == 0) return 0;
    unsigned long total_syms = 0;
    unsigned long strTabLen = 1; // leading NUL
    unsigned int i;
    for (i = 0; i < num_modules; i++) {
        total_syms += mods[i].num_symtab;
        if (mods[i].strtab_size > 0)
            strTabLen += mods[i].strtab_size; // we treat each strtab_size as NOT including a leading NUL duplication
    }

    const int ph_offset = sizeof(Elf64_Ehdr);
    const int text_offset = ALIGNMENT;
    const int symtab_offset = text_offset + 0x100;
    const int strtab_offset = symtab_offset + sizeof(Elf64_Sym) * (total_syms + 1); // +1 null symbol
    const int dyn_offset = strtab_offset + strTabLen;
    const int shstrtab_offset = dyn_offset + sizeof(Elf64_Dyn) * 4 + 32;
    const int sh_offset = (shstrtab_offset/ALIGNMENT + 1) * ALIGNMENT;
    const int file_size = sh_offset + sizeof(Elf64_Shdr) * 5;
    (void)type; // Currently size unaffected by ET_REL vs ET_DYN (dynamic section space reserved regardless)
    return file_size;
}


int makeElf(uint8_t type, lks_module_t *lks_mods, unsigned int num_modules,
    size_t (*write_func)(const void *, size_t)) {
    if (type != ET_DYN && type != ET_REL) {
        PRINT_ERR("libkallsyms: Invalid ELF type");
        return -1;
    }
    if (!lks_mods || num_modules == 0) {
        PRINT_ERR("libkallsyms: makeElf no modules provided");
        return -1;
    }

    unsigned int i, j;
    unsigned long total_syms = 0;
    unsigned long strTabLen = 1; // leading NUL
    for (i = 0; i < num_modules; i++) {
        total_syms += lks_mods[i].num_symtab;
        // Add strings (ensure leading NUL once)
        if (lks_mods[i].strtab && lks_mods[i].strtab_size > 0) {
            //strtab does not include leading NUL
            strTabLen += lks_mods[i].strtab_size ;
        }
    }

    // Offsets for symbol name relocation when merging strtabs
    unsigned long *module_strtab_base_offset = (unsigned long*)MALLOC(sizeof(unsigned long) * num_modules);
    if (!module_strtab_base_offset) { PRINT_ERR("libkallsyms: alloc fail offsets"); return -1; }

    unsigned long runningStrOff = 1; // start after first NUL
    for (i = 0; i < num_modules; i++) {
        module_strtab_base_offset[i] = runningStrOff;
        if (lks_mods[i].strtab_size > 0)
            runningStrOff += lks_mods[i].strtab_size;
    }

    // === Setup section sizes and offsets ===
    const int ph_offset = sizeof(Elf64_Ehdr);
    const int text_offset = ALIGNMENT;
    const int symtab_offset = text_offset + 0x100;     // After code
    const int strtab_offset = symtab_offset + sizeof(Elf64_Sym) * (total_syms + 1); // +1 for null symbol
    const int dyn_offset = strtab_offset + strTabLen; 
    const int shstrtab_offset = dyn_offset + sizeof(Elf64_Dyn) * 4 + 32;
    const int sh_offset = (shstrtab_offset/ALIGNMENT + 1) * ALIGNMENT ;

    unsigned long cur_pos = 0;

    Elf64_Dyn dyn_entries[] = {
        { DT_SYMTAB, symtab_offset - text_offset },
        { DT_STRTAB, strtab_offset - text_offset },
        { DT_STRSZ, strTabLen},
        { DT_NULL, 0 }
    };

    // === ELF Header ===
    Elf64_Ehdr ehdr = {0};
    memcpy(ehdr.e_ident, ELFMAG, SELFMAG);
    ehdr.e_ident[EI_CLASS] = ELFCLASS64;
    ehdr.e_ident[EI_DATA] = ELFDATA2LSB;
    ehdr.e_ident[EI_VERSION] = EV_CURRENT;
    ehdr.e_ident[EI_OSABI] = ELFOSABI_SYSV;
    ehdr.e_type = type; // ET_DYN or ET_REL
    ehdr.e_machine = EM_X86_64;
    ehdr.e_version = EV_CURRENT;
    ehdr.e_entry = 0; // No entry point
    ehdr.e_phoff = ph_offset;
    ehdr.e_shoff = sh_offset;
    ehdr.e_flags = 0;
    ehdr.e_ehsize = sizeof(Elf64_Ehdr);
    ehdr.e_phentsize = sizeof(Elf64_Phdr);
    if (type == ET_DYN) {
        ehdr.e_phnum = 2;
    } else {
        ehdr.e_phnum = 1; // Only text and dynamic
    }
    ehdr.e_shentsize = sizeof(Elf64_Shdr);
    ehdr.e_shnum = 5;
    ehdr.e_shstrndx = 4; // Section header string table index

    PRINT_INFOF("libkallsyms: writing ELF header, size: %d\n", sizeof(ehdr));
    write_func(&ehdr, sizeof(ehdr));
    cur_pos += sizeof(ehdr);

    
    // === Program Header: PT_LOAD (text segment) ===
    // const uint64_t text_vaddr = BASE_VADDR + text_offset;
    Elf64_Phdr phdr = {0};
    phdr.p_type = PT_LOAD;
    phdr.p_offset = text_offset;
    phdr.p_vaddr = 0;
    phdr.p_paddr = 0;
    phdr.p_filesz = sh_offset - text_offset;
    phdr.p_memsz = phdr.p_filesz;
    phdr.p_flags = PF_R | PF_X;
    phdr.p_align = ALIGNMENT;

    PRINT_INFOF("libkallsyms: writing Program header, size: %d\n", sizeof(phdr));
    write_func(&phdr, sizeof(phdr));
    cur_pos += sizeof(phdr);
    
    Elf64_Phdr phdr_dynamic = {0};
    phdr_dynamic.p_type   = PT_DYNAMIC;
    phdr_dynamic.p_offset = dyn_offset;
    phdr_dynamic.p_vaddr  = dyn_offset - text_offset;
    phdr_dynamic.p_paddr  = phdr_dynamic.p_vaddr;
    phdr_dynamic.p_filesz = sizeof(dyn_entries);
    phdr_dynamic.p_memsz  = sizeof(dyn_entries);
    phdr_dynamic.p_flags  = PF_R;
    phdr_dynamic.p_align  = 8;
    
    PRINT_INFOF("libkallsyms: writing dynamic Program header, size: %d\n", sizeof(phdr_dynamic));
    if (type == ET_DYN) {
        write_func(&phdr_dynamic, sizeof(phdr_dynamic));
    }
    else {
        write_func(zeros, sizeof(phdr_dynamic)); // Write zeros if not ET_DYN
    }

    cur_pos += sizeof(phdr_dynamic);

    // Pad to text section
    PRINT_INFOF("libkallsyms: seeking text_offset\n");
    write_func(zeros, text_offset - cur_pos);
    cur_pos = text_offset;
    // seek_func(text_offset, SEEK_SET);
    
    // === Machine code: int my_func() { return 42; } ===
    // mov eax, 42; ret
    uint8_t code[] = {0xb8, 0x2a, 0x00, 0x00, 0x00, 0xc3};
    uint8_t code2[] = {0xb8, 0x2b, 0x00, 0x00, 0x00, 0xc3}; //myfunc2 -> return 43
    write_func(code, sizeof(code));
    write_func(code2, sizeof(code2));
    cur_pos += sizeof(code) + sizeof(code2);
    
    
    // seek_func(symtab_offset, SEEK_SET);
    PRINT_INFOF("libkallsyms: seeking symtab_offset\n");
    write_func(zeros, symtab_offset - cur_pos);
    cur_pos = symtab_offset;

    // === Symbol table ===
    Elf64_Sym sym_null = {0}; // First symbol must be NULL
    write_func(&sym_null, sizeof(sym_null));
    cur_pos += sizeof(sym_null);

    // Flatten all symbols
    unsigned long written_syms = 0;
    for (i = 0; i < num_modules; i++) {
        for (j = 0; j < lks_mods[i].num_symtab; j++) {
            Elf64_Sym out = lks_mods[i].symtab[j];
            // Remap name offset
            out.st_name = lks_mods[i].symtab[j].st_name + module_strtab_base_offset[i];
            write_func(&out, sizeof(out));
            written_syms++;
        }
    }
    cur_pos += sizeof(Elf64_Sym) * written_syms;
    PRINT_INFOF("libkallsyms: wrote unified symtable with %lu symbols\n", written_syms);
    
    // === String table for symbols ===
    // seek_func(strtab_offset, SEEK_SET);
    write_func(zeros, strtab_offset - cur_pos);
    cur_pos = strtab_offset;

    // Unified string table
    write_func("\0", 1); // leading NUL
    cur_pos++;
    for (i = 0; i < num_modules; i++) {
        if (!lks_mods[i].strtab || lks_mods[i].strtab_size == 0) continue;
        write_func(lks_mods[i].strtab, lks_mods[i].strtab_size);
        cur_pos += lks_mods[i].strtab_size;
    }
    // PRINT_INFOF("libkallsyms: Count: %lu\n", count);
    // PRINT_INFOF("libkallsyms: names_size: %lu\n", names_size);
    // PRINT_INFOF("libkallsyms: strTabLen: %lu\n", strTabLen);
    
    
    
    PRINT_INFOF("libkallsyms: seeking dyn_offset \n", strTabLen);
    write_func(zeros, dyn_offset - cur_pos);
    cur_pos = dyn_offset;
    
    if (type == ET_DYN) {
        // === Dynamic section ===
        PRINT_INFOF("libkallsyms: writing dyn_entrie \n", strTabLen);
        write_func(dyn_entries, sizeof(dyn_entries));
        cur_pos += sizeof(dyn_entries);
    }
    else {
        PRINT_INFOF("libkallsyms: not writing dynamic section for ET_REL\n");
    }
    



    // === Section header string table ===
    // Contains names of sections: ".text", ".symtab", ".strtab", ".shstrtab"
    PRINT_INFOF("libkallsyms: seeking shstrtab_offset\n", strTabLen);
    write_func(zeros, shstrtab_offset - cur_pos);
    cur_pos = shstrtab_offset;
    
    PRINT_INFOF("libkallsyms: writing shstrtab\n", strTabLen);
    const char shstrtab[] = "\0.text\0.symtab\0.strtab\0.shstrtab\0";
    write_func(shstrtab, sizeof(shstrtab));
    cur_pos += sizeof(shstrtab);
    
    
    // === Section headers ===
    // seek_func(sh_offset, SEEK_SET);
    PRINT_INFOF("libkallsyms: seeking sh_offset\n", strTabLen);
    write_func(zeros, sh_offset - cur_pos);
    cur_pos = sh_offset;
    
    PRINT_INFOF("libkallsyms: writing section headers\n", strTabLen);
    // Null section
    Elf64_Shdr sh_null = {0};
    write_func(&sh_null, sizeof(sh_null));
    cur_pos += sizeof(sh_null);

    // .text section
    Elf64_Shdr sh_text = {0};
    sh_text.sh_name = 1; // ".text"
    sh_text.sh_type = SHT_PROGBITS;
    sh_text.sh_flags = SHF_ALLOC | SHF_EXECINSTR;
    sh_text.sh_addr = 0; // no actual memory mapping
    sh_text.sh_offset = text_offset;
    sh_text.sh_size = sizeof(code) + sizeof(code2); // size of code
    sh_text.sh_addralign = 1;
    write_func(&sh_text, sizeof(sh_text));
    cur_pos += sizeof(sh_text);

    // .symtab section
    Elf64_Shdr sh_symtab = {0};
    sh_symtab.sh_name = 7; // ".symtab"
    sh_symtab.sh_type = SHT_SYMTAB;
    sh_symtab.sh_offset = symtab_offset;
    sh_symtab.sh_size = sizeof(Elf64_Sym) * (written_syms + 1); // +1 for null symbol
    sh_symtab.sh_link = 3; // Index of .strtab
    sh_symtab.sh_info = 1; // One local symbol
    sh_symtab.sh_addralign = 8;
    sh_symtab.sh_entsize = sizeof(Elf64_Sym);
    write_func(&sh_symtab, sizeof(sh_symtab));
    cur_pos += sizeof(sh_symtab);

    // .strtab section
    Elf64_Shdr sh_strtab = {0};
    sh_strtab.sh_name = 15; // ".strtab"
    sh_strtab.sh_type = SHT_STRTAB;
    sh_strtab.sh_offset = strtab_offset;
    sh_strtab.sh_size = strTabLen;
    sh_strtab.sh_addralign = 1;
    write_func(&sh_strtab, sizeof(sh_strtab));
    cur_pos += sizeof(sh_strtab);

    // .shstrtab section
    Elf64_Shdr sh_shstrtab = {0};
    sh_shstrtab.sh_name = 23; // ".shstrtab"
    sh_shstrtab.sh_type = SHT_STRTAB;
    sh_shstrtab.sh_offset = shstrtab_offset;
    sh_shstrtab.sh_size = sizeof(shstrtab);
    sh_shstrtab.sh_addralign = 1;
    write_func(&sh_shstrtab, sizeof(sh_shstrtab));
    cur_pos += sizeof(sh_shstrtab);

    PRINT_INFOF("libkallsyms: Wrote full elf file'\n");

    return 0;
}





size_t mywrite(const void* data, size_t size) {
    // pr_info("%s: mywrite called, data: %lx, size: %x", MODULE_NAME, data, size);
    if (seq_file == NULL) {
        pr_err("seq_file is NULL\n");
        return -1;
    }

    if (size > 1024) {
        pr_alert("%s: mywrite called with > 1024 len, data: %lx, size: %x\n", MODULE_NAME, data, size);
    }

    return seq_write(seq_file, data, size);
}


static int kallsyms_elf_show(struct seq_file *m, void *v) {
    // Custom logic to write an ELF-formatted in-memory symbol table
    int retVal;
    seq_file = m;
    
    pr_info("%s: starting kallsyms_elf_show", MODULE_NAME);
    retVal = makeElf(ET_DYN, modules_head, modules_count, &mywrite);
    // retVal = __main(&mywrite);
    if (retVal != 0) {
        pr_err("Failed to create ELF file\n");
    }
    return retVal;
}

static int kallsyms_elf_open(struct inode *inode, struct file *file) {
    pr_info("%s: kallsyms_elf_open called", MODULE_NAME);
    return single_open(file, kallsyms_elf_show, NULL);
}

loff_t kallsyms_lseek(struct file *file, loff_t offset, int whence)
{
	struct seq_file *m = file->private_data;
    pr_info("%s: kallsyms_lseek called, size is: %d", MODULE_NAME, file_size);

    if (whence == SEEK_END) {
        if (offset > 0)
            return -EINVAL;

        offset += file_size;
        return seq_lseek(file, offset, SEEK_SET);
    }

    return seq_lseek(file, offset, whence);
}

size_t mem_write(const void* data, size_t size) {
    // pr_info("%s: mem_write called, data: %lx, size: %x", MODULE_NAME, data, size);
    if (global_vma == NULL) {
        pr_err("global_vma is NULL\n");
        return -1;
    }
    void * write_end = global_write_start + file_size;

    if (size > 1024) {
        pr_alert("%s: mem_write called with > 1024 len, data: %lx, size: %x\n", MODULE_NAME, data, size);
    }

    if (global_write_pos == write_end) {
        return 0;
    }

    if (global_write_pos + size > write_end) {
        size = write_end - global_write_pos;
        pr_alert("%s: mem_write called with size > vm_end, new size: %lx\n", MODULE_NAME, size);
    }

    memcpy(global_write_pos, data, size);
    global_write_pos += size;
    
    return size;

}

static int kallsyms_mmap(struct file *file, struct vm_area_struct *vma) {
    pr_info("%s: kallsyms_mmap called, is_cow_mapping: %x, vma->vm_flags: %x\n", MODULE_NAME, is_cow_mapping(vma->vm_flags), vma->vm_flags);

    global_vma = vma;
    global_vma_pos = vma->vm_start;
    // Ensure the requested size does not exceed the file size
    // if (vma->vm_end - vma->vm_start < file_size) {
    //     pr_err("%s: mmap size has to be file size: vma->vm_end - vma->vm_start: %lx \n", MODULE_NAME, vma->vm_end - vma->vm_start);
    //     return -EINVAL;
    // }

    global_write_start = global_write_pos = vmalloc(vma->vm_end - vma->vm_start);
    if (!global_write_start) {
        pr_alert("%s: failed to allocate memory for mmap\n", MODULE_NAME);
        return -ENOMEM;
    }
    pr_info("%s: global_write_start: %lx, global_write_pos: %lx, pageAligned: %d, PAGE_ALIGN(PAGE_SIZE) = %d\n", MODULE_NAME, global_write_start, global_write_pos, PAGE_ALIGNED(vma->vm_start), PAGE_ALIGN(PAGE_SIZE));

    // Map the memory (example: using kmalloc'ed memory)
    int retVal = makeElf(ET_DYN, modules_head, modules_count, &mem_write);

    // Map the memory to user space using vm_insert_pages
    unsigned long size = vma->vm_end - vma->vm_start;
    unsigned long offset = 0;
    struct page **pages;
    unsigned int num_pages = size >> PAGE_SHIFT; // Number of pages to map
    unsigned int i;

    // Allocate an array of struct page pointers
    pages = kmalloc_array(num_pages, sizeof(struct page *), GFP_KERNEL);
    if (!pages) {
        pr_alert("%s: failed to allocate page array\n", MODULE_NAME);
        vfree(global_write_start);
        return -ENOMEM;
    }

    // Populate the array with pages corresponding to the vmalloc'ed memory
    for (i = 0; i < num_pages; i++) {
        pages[i] = vmalloc_to_page(global_write_start + (i << PAGE_SHIFT));
        if (!pages[i]) {
            pr_alert("%s: vmalloc_to_page failed for page %u\n", MODULE_NAME, i);
            kfree(pages);
            vfree(global_write_start);
            return -EFAULT;
        }
    }

    // Insert pages into the VMA
    unsigned long num_copy = num_pages;
    int err = vm_insert_pages(vma, vma->vm_start, pages, &num_copy);
    pr_info("%s: vm_insert_pages called, num_copy: %ld\n", MODULE_NAME, num_copy);
    if (err) {
        pr_err("%s: vm_insert_pages failed: %d\n", MODULE_NAME, err);
        kfree(pages);
        vfree(global_write_start);
        return err;
    }

    pr_info("%s: mmap successful\n", MODULE_NAME);

    // Free the page array (the pages themselves are managed by the VMA now)
    kfree(pages);
    
    // // Map the memory to user space
    // unsigned long start = vma->vm_start;
    // unsigned long size = vma->vm_end - vma->vm_start;
    // unsigned long offset = 0;
    // int count = 0;
    // int errCode = 0;

    // while (size > 0) {
    //     unsigned long pfn = vmalloc_to_pfn(global_write_start + offset);
    //     if (errCode = remap_pfn_range(vma, start, pfn, PAGE_SIZE, vma->vm_page_prot)) {
    //         vfree(global_write_start); // Free the allocated memory
    //         pr_err("%s: remap_pfn_range failed: %d\n", MODULE_NAME, errCode);
    //         return -EAGAIN;
    //     }
        
    //     if (count % 250 == 0) {
    //         pr_info("%s: remap_pfn_range called, start: %lx, pfn: %lx, size: %lx\n", MODULE_NAME, start, pfn, size);
    //     }
        
    //     start += PAGE_SIZE;
    //     offset += PAGE_SIZE;
    //     size -= PAGE_SIZE;
    // }
    
    
    pr_info("%s: mmap successful\n", MODULE_NAME);
    return retVal;
}

static const struct proc_ops kallsyms_elf_fops = {
    .proc_open    = kallsyms_elf_open,
    .proc_read    = seq_read,
    .proc_lseek   = kallsyms_lseek,
    .proc_release = single_release,
    .proc_mmap    = kallsyms_mmap,
};





















static int __init libkallsyms_init_syms(void) {

    pr_info("%s: creating array of name pointers\n", MODULE_NAME);
    
    kallsyms_name_types = (char*)kmalloc(kallsyms_num_syms, GFP_KERNEL);
    if (!kallsyms_name_types) {
        pr_alert("%s: failed to allocate memory for name pointers\n", MODULE_NAME);
        return -ENOMEM;
    }
    
    unsigned int pos;
    int i, len0,len1;
    char symBuffer[MAX_SYM_LEN] = {0};
    char is_per_cpu = 1;

    len0 = len1 = 0;
    // pos = &kallsyms_names[0];
    kallsyms_names_size = 0;


    pr_info("%s: &kallsyms_names[0]: %lx\n", MODULE_NAME, pos);
    for (i = 0, pos = 0; i < kallsyms_num_syms; i++) {
        
        kallsyms_name_types[i] = kallsyms_get_symbol_type(pos);

        pos = kallsyms_expand_symbol(pos, symBuffer, MAX_SYM_LEN);


        if (is_per_cpu && strcmp(symBuffer, "__per_cpu_end") == 0) {
            kallsyms_per_cpu_symbol_count = i + 1;
            pr_info("%s: found __per_cpu_end at symbol %d, pos: 0x%lx\n", MODULE_NAME, i, pos);
            kallsyms_first_non_per_cpu_name_pos = pos; //already points to next symbol
            is_per_cpu = 0; // no more per-cpu symbols
        }


        if (is_per_cpu)
            kallsyms_per_cpu_names_size += (char)strlen(symBuffer) + 1;   
        else
            kallsyms_names_size += (char)strlen(symBuffer) + 1;   
        
        if (i % 25000 == 0) {
            pr_info("%s: loaded symbol %d, length: %d, next pos: %lx, symbuf: %s\n", MODULE_NAME, i, (char)strlen(symBuffer), pos, symBuffer);
            pr_info("%s: len0: %d, len1: %d\n", MODULE_NAME, len0, len1);
            len0 = len1 = 0;
        }
    }

    pr_info("%s: created array of name pointers\n", MODULE_NAME);

    pr_info("%s: creating lks_module_t\n", MODULE_NAME);
    modules_head = make_lks_mod(&kallsyms_name_types[kallsyms_per_cpu_symbol_count], &kallsyms_addresses[kallsyms_per_cpu_symbol_count], kallsyms_num_syms - kallsyms_per_cpu_symbol_count,
        kallsyms_names_size, kallsyms_first_non_per_cpu_name_pos, &kallsyms_expand_symbol);
    modules_count = 1;
    pr_info("%s: created lks_module_t\n", MODULE_NAME);


    pr_info("%s: creating proc fs entry\n", MODULE_NAME);
    struct proc_dir_entry* proc_entry = proc_create("libkallsyms.so", 0777, NULL, &kallsyms_elf_fops);
    file_size = elfMaker_calcSize(modules_head, modules_count, ET_DYN);
    proc_set_size(proc_entry, file_size);
    pr_info("%s: proc fs entry created correctly\n", MODULE_NAME);

    
}
