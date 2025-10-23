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
#include <linux/types.h>
#include <linux/stddef.h>
#include <linux/string.h>


// add/remove sym/strtabs for inserted/deleted modules


// ELF headers
// #define BASE_VADDR 0x400000
#define ALIGNMENT  0x100
#define MAX_SYM_LEN 128
#define ELFOSABI_SYSV		0	/* Alias.  */
#define STV_DEFAULT	0		/* Default symbol visibility rules */
#define SEEK_SET	0
#define MODULE_NAME "ker_libkallsyms"


#define MALLOC(size) vmalloc(size)
#define FREE(ptr) vfree(ptr)
#define PRINT_ERR(msg) pr_err(msg)
#define PRINT_INFOF(...) pr_info(__VA_ARGS__)
#define LKS_LOCK(mu)   do { pr_info("%s: mutex_lock at %s:%d\n", MODULE_NAME, __func__, __LINE__); mutex_lock(mu); } while (0)
#define LKS_UNLOCK(mu) do { pr_info("%s: mutex_unlock at %s:%d\n", MODULE_NAME, __func__, __LINE__); mutex_unlock(mu); } while (0)

#define ELF32_ST_INFO(bind, type)	(((bind) << 4) + ((type) & 0xf))
#define ELF64_ST_INFO(bind, type)	ELF32_ST_INFO ((bind), (type))
#ifndef ELF64_ST_VISIBILITY
#define ELF64_ST_VISIBILITY(o)	((o) & 0x03)
#endif

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
    
/* Section header string table (restored .symtab/.strtab) */
static const char shstrtab[] =
    "\0.text"
    "\0.gnu.hash"
    "\0.dynsym"
    "\0.dynstr"
    "\0.gnu.version"
    "\0.gnu.version_d"
    "\0.dynamic"
    "\0.symtab"
    "\0.strtab"
    "\0.shstrtab\0";
/* Offsets (recomputed):
 *  .text=1
 *  .gnu.hash=7
 *  .dynsym=17
 *  .dynstr=25
 *  .gnu.version=33
 *  .gnu.version_d=46
 *  .dynamic=61
 *  .symtab=70
 *  .strtab=78
 *  .shstrtab=86
 */

/* External kallsyms data (attributes stripped for simplified build environment) */
extern const unsigned long kallsyms_addresses[] __weak;
extern const int kallsyms_offsets[] __weak;
extern const u8 kallsyms_names[] __weak;

/*
 * Tell the compiler that the count isn't in the small data section if the arch
 * has one (eg: FRV).
 */
extern const unsigned int kallsyms_num_syms
__section(".rodata") __attribute__((weak));

extern const unsigned long kallsyms_relative_base
__section(".rodata") __attribute__((weak));

extern const char kallsyms_token_table[] __weak;
extern const u16 kallsyms_token_index[] __weak;

extern const unsigned int kallsyms_markers[] __weak;

static unsigned long kallsyms_sym_address(int idx)
{
	if (!IS_ENABLED(CONFIG_KALLSYMS_BASE_RELATIVE))
		return kallsyms_addresses[idx];

	/* values are unsigned offsets if --absolute-percpu is not in effect */
	if (!IS_ENABLED(CONFIG_KALLSYMS_ABSOLUTE_PERCPU))
        return kallsyms_relative_base + (unsigned int)kallsyms_offsets[idx];

	/* ...otherwise, positive offsets are absolute values */
	if (kallsyms_offsets[idx] >= 0)
		return kallsyms_offsets[idx];

	/* ...and negative offsets are relative to kallsyms_relative_base - 1 */
	return kallsyms_relative_base - 1 - kallsyms_offsets[idx];
}

//functions we need from kallsyms, copied here to ensure CONFIG_SYMBIOTE is independent of CONFIG_KALLSYMS
static unsigned int kallsyms_expand_symbol(unsigned int off,
                   char *result, unsigned long maxlen)
{
	int len, skipped_first = 0;
	const char *tptr;
    const unsigned char *data;

	/* Get the compressed symbol length from the first symbol byte. */
	data = &kallsyms_names[off];
	len = *data;
	data++;

	/*
	 * Update the offset to return the offset for the next symbol on
	 * the compressed stream.
	 */
	off += len + 1;

	/*
	 * For every byte on the compressed symbol data, copy the table
	 * entry for that byte.
	 */
	while (len) {
		tptr = &kallsyms_token_table[kallsyms_token_index[*data]];
		data++;
		len--;

		while (*tptr) {
			if (skipped_first) {
				if (maxlen <= 1)
					goto tail;
				*result = *tptr;
				result++;
				maxlen--;
			} else
				skipped_first = 1;
			tptr++;
		}
	}

tail:
	if (maxlen)
		*result = '\0';

	/* Return to offset to the next symbol. */
	return off;
}

/*
 * Get symbol type information. This is encoded as a single char at the
 * beginning of the symbol name.
 */
static char kallsyms_get_symbol_type(unsigned int off)
{
	/*
	 * Get just the first code, look it up in the token table,
	 * and return the first char from this token.
	 */
	return kallsyms_token_table[kallsyms_token_index[kallsyms_names[off + 1]]];
}


static struct seq_file *seq_file;
static unsigned long file_size_dyn; /* size of ET_DYN output */
static unsigned long file_size_rel; /* size of ET_REL output */

static char *kallsyms_name_types;
static unsigned long kallsyms_names_size;
static unsigned long kallsyms_per_cpu_names_size;
static unsigned long kallsyms_first_non_per_cpu_name_pos;
static unsigned long kallsyms_per_cpu_symbol_count;

static struct vm_area_struct *global_vma;
static unsigned long global_vma_pos;
static void * global_write_pos;
static void * global_write_start;
static struct proc_dir_entry* proc_entry;     /* /proc/libkallsyms.so */
static struct proc_dir_entry* proc_entry_rel; /* /proc/libkallsyms.a  */

static lks_module_t* modules_head = NULL;
static lks_module_t* modules_tail = NULL;
static unsigned long modules_count = 0;
static DEFINE_MUTEX(modules_lock);

static char zeros[1024] = {0}; 

/* ===================== GNU Hash Section Construction =====================
 * This implementation is adapted (simplified) from binutils' elflink.c
 * (see lines ~7992-8165 in the provided context) to build a .gnu.hash
 * section for a given set of (dynamic) symbols. It intentionally focuses
 * on clarity and minimal external dependencies for this project. It does
 * NOT attempt to perfectly replicate all heuristics used by binutils
 * (e.g. sophisticated bucket count selection or bloom filter sizing).
 * Instead it provides a correct, small-symbol-count oriented generator
 * suitable for embedding inside this lightweight ELF builder.
 *
 * Format (.gnu.hash):
 *   u32 nbuckets
 *   u32 symoffset         (index of first symbol participating — usually
 *                          #local symbols in .dynsym)
 *   u32 bloom_size        (number of ELF word sized bloom filter words)
 *   u32 bloom_shift       (right shift count used for 2nd bloom bit)
 *   Elf_Addr bloom[bloom_size]
 *   u32 buckets[nbuckets]
 *   u32 chain[ndyn_syms - symoffset]
 *
 * Chain values are 32-bit GNU hash values with the low bit of the last
 * element in each bucket's chain set (terminator bit = 1).
 */

static unsigned int gnu_hash_compute(const char *name) {
    /* Standard GNU hash algorithm (see glibc / binutils sources). */
    unsigned int h = 5381U;
    unsigned char c;
    while ((c = (unsigned char)*name++) != 0) {
        h = (h << 5) + h + c; /* h * 33 + c */
    }
    return h;
}

/* === GNU Symbol Versioning Support === */
#ifndef SHT_GNU_verdef
#define SHT_GNU_verdef 0x6ffffffd
#endif
#ifndef SHT_GNU_versym
#define SHT_GNU_versym 0x6fffffff
#endif
#ifndef DT_VERSYM
#define DT_VERSYM    0x6ffffff0
#endif
#ifndef DT_VERDEF
#define DT_VERDEF    0x6ffffffc
#endif
#ifndef DT_VERDEFNUM
#define DT_VERDEFNUM 0x6ffffffd
#endif
#ifndef VER_FLG_BASE
#define VER_FLG_BASE 0x1
#endif
typedef struct { Elf64_Half vd_version, vd_flags, vd_ndx, vd_cnt; Elf64_Word vd_hash, vd_aux, vd_next; } lks_Elf64_Verdef;
typedef struct { Elf64_Word vda_name, vda_next; } lks_Elf64_Verdaux;
static unsigned int elf_sysv_hash(const unsigned char *name){ unsigned long h=0,g; while(*name){ h=(h<<4)+*name++; g=h&0xf0000000UL; if(g) h^=g>>24; h&=~g;} return (unsigned int)h; }

/* Simple helper: next prime-ish number for small bucket counts.
 * For tiny symbol sets this avoids pathological clustering while
 * staying trivial. Falls back to (n|1)+2 if table insufficient. */
static unsigned int small_next_prime(unsigned int n) {
    static const unsigned short primes[] = {
        1, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37,
        43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89,
        97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149,
    };
    unsigned int i;
    for (i = 0; i < sizeof(primes)/sizeof(primes[0]); ++i) {
        if (primes[i] >= n) return primes[i];
    }
    return (n | 1) + 2;
}

/* Conservative GNU bloom size: smallest power-of-two >= hashable/64 (at least 1).
 * Mirrors ld / gold style heuristic to keep bloom relatively compact while
 * still scaling with symbol count. For very small tables this yields 1. */
static unsigned int choose_bloom_size(unsigned long hashable) {
    unsigned long target = (hashable >> 6); /* hashable / 64 */
    unsigned int sz = 1;
    while (sz && sz < target) sz <<= 1; /* stops when sz >= target or overflow */
    if (sz == 0) sz = 1; /* overflow guard */
    return sz;
}

/* Reorder dynamic symbols so that symbols belonging to the same GNU hash bucket
 * become contiguous, as required by the GNU hash chain traversal algorithm.
 * We currently treat all symbols after the NULL @0 as global. A more refined
 * implementation could separate STB_LOCAL and start globals at symoffset.
 */
static Elf64_Sym *reorder_dynsym_for_gnu(const Elf64_Sym *in_syms,
                                         unsigned long dynsym_count,
                                         unsigned long symoffset,
                                         const char *strtab) {
    if (!in_syms || dynsym_count <= symoffset) return NULL;
    unsigned long hashable = dynsym_count - symoffset; /* number of symbols to hash */
    /* Must mirror small_next_prime & bucket heuristic in build_gnu_hash_section */
    unsigned int nbuckets = small_next_prime((unsigned int)(hashable / 4 + 1));
    if (nbuckets == 0) nbuckets = 1;

    /* First pass: assign each symbol to a bucket */
    unsigned int *bucket_counts = (unsigned int*)MALLOC(sizeof(unsigned int) * nbuckets);
    if (!bucket_counts) return NULL;
    memset(bucket_counts, 0, sizeof(unsigned int) * nbuckets);

    unsigned long i;
    for (i = symoffset; i < dynsym_count; ++i) {
        const Elf64_Sym *s = &in_syms[i];
        if (s->st_name == 0) continue; /* skip nameless */
        const char *name = strtab + s->st_name;
        unsigned int h = gnu_hash_compute(name);
        unsigned int b = h % nbuckets;
        bucket_counts[b]++;
    }

    /* Compute prefix sums to know where each bucket's run starts */
    unsigned long *bucket_offsets = (unsigned long*)MALLOC(sizeof(unsigned long) * nbuckets);
    if (!bucket_offsets) { FREE(bucket_counts); return NULL; }
    unsigned long running = symoffset; /* start placing after local(s) */
    for (i = 0; i < nbuckets; ++i) {
        bucket_offsets[i] = running;
        running += bucket_counts[i];
    }

    /* Output array */
    Elf64_Sym *out = (Elf64_Sym*)MALLOC(sizeof(Elf64_Sym) * dynsym_count);
    if (!out) { FREE(bucket_offsets); FREE(bucket_counts); return NULL; }
    /* Preserve symbol 0 (local null) untouched */
    if (symoffset > 0) memcpy(out, in_syms, sizeof(Elf64_Sym) * symoffset);

    /* Temp per-bucket position counters (re-use bucket_counts) */
    memset(bucket_counts, 0, sizeof(unsigned int) * nbuckets);

    for (i = symoffset; i < dynsym_count; ++i) {
        const Elf64_Sym *s = &in_syms[i];
        if (s->st_name == 0) continue; /* skip nameless (remain un-placed; they won't be hashed) */
        const char *name = strtab + s->st_name;
        unsigned int h = gnu_hash_compute(name);
        unsigned int b = h % nbuckets;
        unsigned long pos = bucket_offsets[b] + bucket_counts[b];
        out[pos] = *s;
        bucket_counts[b]++;
    }

    /* Any slots for nameless symbols that were skipped remain zeroed (already) */

    FREE(bucket_offsets);
    FREE(bucket_counts);
    return out;
}

/* Build a .gnu.hash section from an array of dynamic symbols.
 * Inputs:
 *   dynsyms      - pointer to first Elf64_Sym in dynamic symbol table
 *   dynsym_count - total number of dynamic symbols (including NULL @0)
 *   strtab       - corresponding string table (for names)
 *   symoffset    - index in dynsyms of first global (hashable) symbol
 *                  (all symbols < symoffset are skipped — typically locals)
 * Outputs:
 *   *out_buf/*out_size allocated with MALLOC (caller frees)
 * Return 0 on success, -1 on failure.
 */
int build_gnu_hash_section(const Elf64_Sym *dynsyms,
                           unsigned long dynsym_count,
                           const char *strtab,
                           unsigned long symoffset,
                           unsigned char **out_buf,
                           unsigned long *out_size) {
    if (!dynsyms || !strtab || !out_buf || !out_size) return -1;
    if (dynsym_count <= symoffset) return -1;

    unsigned long hashable = dynsym_count - symoffset;
    if (hashable == 0) return -1;

    /* Heuristic bucket count (borrow concept: average ~ 4 symbols/bucket). */
    unsigned int nbuckets = small_next_prime((unsigned int)(hashable / 4 + 1));
    if (nbuckets == 0) nbuckets = 1; /* ensure >=1 */

    /* Bloom filter sizing (conservative ld-like heuristic): power-of-two >= hashable/64 */
    unsigned int bloom_size = choose_bloom_size(hashable);
    const unsigned int bloom_shift = 6; /* typical value used by GNU ld for 64-bit */

    /* Temporary arrays to collect bucket membership and hashes. */
    unsigned int *buckets = (unsigned int*)MALLOC(sizeof(unsigned int) * nbuckets);
    if (!buckets) return -1;
    memset(buckets, 0, sizeof(unsigned int) * nbuckets);

    unsigned int *chain = (unsigned int*)MALLOC(sizeof(unsigned int) * hashable);
    if (!chain) { FREE(buckets); return -1; }
    memset(chain, 0, sizeof(unsigned int) * hashable);

    unsigned long long *bloom = (unsigned long long*)MALLOC(sizeof(unsigned long long) * bloom_size);
    if (!bloom) { FREE(buckets); FREE(chain); return -1; }
    memset(bloom, 0, sizeof(unsigned long long) * bloom_size);

    /* For post-processing to set chain terminator bits, store last symbol
     * index position per bucket during a first pass. We'll collect lists
     * in a simple chained manner using an auxiliary per-symbol next index. */
    int *bucket_last_sym = (int*)MALLOC(sizeof(int) * nbuckets);
    if (!bucket_last_sym) {
        FREE(bloom); FREE(chain); FREE(buckets); return -1;
    }
    unsigned long i;
    for (i = 0; i < nbuckets; ++i) bucket_last_sym[i] = -1;

    int *next_in_bucket = (int*)MALLOC(sizeof(int) * hashable);
    if (!next_in_bucket) {
        FREE(bucket_last_sym); FREE(bloom); FREE(chain); FREE(buckets); return -1; }
    for (i = 0; i < hashable; ++i) next_in_bucket[i] = -1;

    /* First pass: compute hashes, fill bloom, form bucket chains. */
    unsigned long si;
    for (si = symoffset; si < dynsym_count; ++si) {
        const Elf64_Sym *sym = &dynsyms[si];
        if (sym->st_name == 0) continue; /* skip nameless */
        const char *name = strtab + sym->st_name;
        unsigned int h = gnu_hash_compute(name);

        unsigned long rel_index = si - symoffset; /* index in chain array */
        chain[rel_index] = h & ~1U; //ensure we dont set terminator bit yet

        /* Bucket logic. */
        unsigned int b = h % nbuckets;
        if (buckets[b] == 0) {
            /* Store absolute dynsym index (not relative). */
            buckets[b] = (unsigned int)si;
        } else {
            /* Existing bucket -> chain off previous last symbol in this bucket. */
            int last = bucket_last_sym[b];
            if (last >= 0) next_in_bucket[last] = (int)rel_index;
        }
        bucket_last_sym[b] = (int)rel_index;

        /* Bloom filter: two bits per hash. */
        unsigned long long word_bits = 64ULL; /* 64-bit */
        unsigned long long word_index = (h / word_bits) % bloom_size;
        unsigned long long bit1 = h % word_bits;
        unsigned long long bit2 = (h >> bloom_shift) % word_bits;
        bloom[word_index] |= (1ULL << bit1) | (1ULL << bit2);
    }

    /* Second pass: set terminator bit (LSB=1) for last symbol in each bucket's chain. */
    unsigned int b;
    for (b = 0; b < nbuckets; ++b) {
        if (buckets[b] == 0) continue; /* empty bucket */
        int last_rel = bucket_last_sym[b];
        if (last_rel >= 0) chain[last_rel] |= 1U; /* mark end */
    }

    /* Serialize section layout. */
    unsigned long header_words = 4; /* nbuckets, symoffset, bloom_size, bloom_shift */
    unsigned long size = header_words * sizeof(unsigned int)
            + bloom_size * sizeof(unsigned long long)
            + nbuckets * sizeof(unsigned int)
            + hashable * sizeof(unsigned int);

    unsigned char *buf = (unsigned char*)MALLOC(size);
    if (!buf) {
        FREE(next_in_bucket); FREE(bucket_last_sym); FREE(bloom); FREE(chain); FREE(buckets); return -1;
    }
    unsigned char *p = buf;

    /* Write header fields. */
    unsigned int v;
    v = nbuckets;    memcpy(p, &v, 4); p += 4;
    v = (unsigned int)symoffset; memcpy(p, &v, 4); p += 4;
    v = bloom_size;  memcpy(p, &v, 4); p += 4;
    v = bloom_shift; memcpy(p, &v, 4); p += 4;

    /* Bloom filter */
    for (i = 0; i < bloom_size; ++i) { memcpy(p, &bloom[i], sizeof(unsigned long long)); p += sizeof(unsigned long long); }
    /* Buckets */
    for (i = 0; i < nbuckets; ++i) { memcpy(p, &buckets[i], 4); p += 4; }
    /* Chain (raw, already includes terminator bits) */
    for (i = 0; i < hashable; ++i) { memcpy(p, &chain[i], 4); p += 4; }

    *out_buf = buf;
    *out_size = size;

    FREE(next_in_bucket); FREE(bucket_last_sym); FREE(bloom); FREE(chain); FREE(buckets);
    return 0;
}

/* (Optional) future integration notes:
 * - To integrate .gnu.hash into the produced ELF we would need to create
 *   a .dynsym distinct from (or derived from) the existing .symtab, add
 *   both .gnu.hash and .dynsym section headers, and update the dynamic
 *   section (DT_GNU_HASH, DT_SYMTAB, DT_STRTAB, etc.). For now only the
 *   generator is provided per user request.
 */




//build elf type from char
static unsigned char GetElfTypeForSymType(char type) {
    unsigned char st_type = STT_NOTYPE;
    unsigned char st_bind = STB_GLOBAL;

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
static lks_module_t* make_lks_mod(char* nameTypes, unsigned long first_address_id, unsigned int num_syms,
    unsigned long names_size, unsigned long first_name_pos,
    unsigned int (*decompress_func)(unsigned int off, char *result, unsigned long maxlen)) {
    if (!nameTypes || !decompress_func || num_syms == 0) {
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
    unsigned long len = (unsigned long)strlen(symBuffer);
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
        unsigned long addr = kallsyms_sym_address(first_address_id + i);
        if (addr & (0xfffffffULL << 48)) {
            s->st_shndx = SHN_ABS;
        } else {
            s->st_shndx = 1; // heuristic .text
        }
        s->st_value = addr;
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
    m->next = NULL;
    return m;
}


static unsigned long elfMaker_calcSize(lks_module_t *mods, unsigned int num_modules, unsigned char type) {
    if (!mods || num_modules == 0) return 0;
    unsigned long total_syms = 0;
    unsigned long strTabLen = 1; // leading NUL
    unsigned int i = 0;
    lks_module_t *iter = mods;
    while (iter && i < num_modules) {
        total_syms += iter->num_symtab;
        if (iter->strtab_size > 0)
            strTabLen += iter->strtab_size; // does not include a leading NUL
        iter = (lks_module_t*)iter->next;
        i++;
    }
    if (type == ET_REL) {
        /* Minimal ET_REL: no program headers, no .dynsym/.dynstr/.gnu.* or .dynamic.
         * Keep only: .text, .symtab, .strtab, .shstrtab
         */
        const int text_offset = ALIGNMENT;
        /* Place symtab after a small gap for code (mirror previous 0x100 to keep spacing predictable) */
        const int symtab_offset = text_offset + 0x100;
        const int strtab_offset = symtab_offset + sizeof(Elf64_Sym) * (total_syms + 1);
        const int shstrtab_offset = strtab_offset + strTabLen;
        const int sh_offset = ((shstrtab_offset + sizeof(shstrtab))/ALIGNMENT + 1) * ALIGNMENT;
        const int file_size = sh_offset + sizeof(Elf64_Shdr) * 5; /* null + .text + .symtab + .strtab + .shstrtab */
        return file_size;
    } else {
        /* ET_DYN full: includes .dynsym/.dynstr/.gnu.hash/.gnu.version(_d)/.dynamic plus debug .symtab/.strtab */
        unsigned long debugStrTabLen = strTabLen + (4UL * total_syms);
        unsigned long hashable = total_syms;
        unsigned int nbuckets = 1;
        if (hashable) {
            unsigned long tmp = (hashable / 4) + 1;
            static const unsigned short primes[] = {1,3,5,7,11,13,17,19,23,29,31,37,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127,131,137,139,149};
            unsigned int pi;
            for (pi = 0; pi < sizeof(primes)/sizeof(primes[0]); ++pi) if (primes[pi] >= tmp) { nbuckets = primes[pi]; break; }
            if (nbuckets < tmp) nbuckets = ((unsigned)tmp | 1) + 2;
        }
        unsigned int bloom_size = choose_bloom_size(hashable);
        unsigned long gnu_hash_size = 16 + (unsigned long)bloom_size * 8 + (unsigned long)nbuckets * 4 + hashable * 4;
        unsigned long gnu_hash_padded = (gnu_hash_size + 7) & ~7UL;
        const int ph_offset = sizeof(Elf64_Ehdr);
        const int text_offset = ALIGNMENT;
        const int dynsym_offset = text_offset + 0x100; /* keep gap */
        const int dynstr_offset = dynsym_offset + sizeof(Elf64_Sym) * (total_syms + 1);
        unsigned long dynstr_padded_len = strTabLen;
        if (dynstr_padded_len & 7) dynstr_padded_len = (dynstr_padded_len + 7) & ~7UL;
        const int gnu_hash_offset = dynstr_offset + dynstr_padded_len; /* dynstr only, 8-aligned */
        const int dyn_offset = gnu_hash_offset + gnu_hash_padded;
        const int symtab_offset = (dyn_offset + sizeof(Elf64_Dyn) * 5 + 16 + 7) & ~7; /* 8-align */
        const int strtab_offset = symtab_offset + sizeof(Elf64_Sym) * (total_syms + 1);
        const int shstrtab_offset = strtab_offset + debugStrTabLen;
        const int sh_offset = ((shstrtab_offset + sizeof(shstrtab))/ALIGNMENT + 1) * ALIGNMENT;
        const int file_size = sh_offset + sizeof(Elf64_Shdr) * 11; /* null + .text + .gnu.hash + .dynsym + .dynstr + .gnu.version + .gnu.version_d + .dynamic + .symtab + .strtab + .shstrtab */
        return file_size;
    }
}


/* Helper to append a string to both dynstr and unified_strtab, updating length
 * and returning the starting offset via off_out. Returns 0 on success, -1 on failure. */
static int lks_append_to_strtabs(char **pdynstr,
                                 char **punified,
                                 unsigned long *p_strTabLen,
                                 const char *s,
                                 size_t slen,
                                 unsigned long *off_out)
{
    char *dyn = *pdynstr;
    char *uni = *punified;
    unsigned long old_len = *p_strTabLen;
    char *new_dyn = vmalloc(old_len + slen);
    char *new_uni = vmalloc(old_len + slen);
    if (!new_dyn || !new_uni) {
        PRINT_ERR("libkallsyms: version append alloc fail");
        if (new_dyn) vfree(new_dyn);
        if (new_uni) vfree(new_uni);
        return -1;
    }
    memcpy(new_dyn, dyn, old_len);
    memcpy(new_uni, uni, old_len);
    memcpy(new_dyn + old_len, s, slen);
    memcpy(new_uni + old_len, s, slen);
    *off_out = old_len;
    *p_strTabLen = old_len + slen;
    vfree(dyn); *pdynstr = new_dyn;
    FREE(uni);  *punified = new_uni;
    return 0;
}

static int makeElf(unsigned char type, lks_module_t *lks_mods, unsigned int num_modules,
    unsigned long (*write_func)(const void *, unsigned long)) {
    if (type != ET_DYN && type != ET_REL) {
        PRINT_ERR("libkallsyms: Invalid ELF type");
        return -1;
    }
    if (!lks_mods || num_modules == 0) {
        PRINT_ERR("libkallsyms: makeElf no modules provided");
        return -1;
    }
    unsigned int i = 0, j;
    unsigned long total_syms = 0;
    unsigned long strTabLen = 1;
    lks_module_t *iter = lks_mods;
    while (iter && i < num_modules) {
        total_syms += iter->num_symtab;
        if (iter->strtab && iter->strtab_size > 0) strTabLen += iter->strtab_size;
        iter = (lks_module_t*)iter->next; i++; }

    /* Build merged symbol table + unified strtab (this becomes .dynstr only) */
    Elf64_Sym *merged_syms = (Elf64_Sym*)MALLOC(sizeof(Elf64_Sym) * (total_syms + 1));
    if (!merged_syms) { PRINT_ERR("libkallsyms: merged_syms alloc failed"); return -1; }
    memset(merged_syms, 0, sizeof(Elf64_Sym) * (total_syms + 1));
    char *unified_strtab = (char*)MALLOC(strTabLen);
    if (!unified_strtab) { FREE(merged_syms); PRINT_ERR("libkallsyms: unified_strtab alloc failed"); return -1; }
    memset(unified_strtab, 0, strTabLen); unified_strtab[0] = '\0';

    /* Offsets for per-module names */
    unsigned long *module_strtab_base_offset = (unsigned long*)MALLOC(sizeof(unsigned long)*num_modules);
    if (!module_strtab_base_offset) { FREE(unified_strtab); FREE(merged_syms); PRINT_ERR("libkallsyms: alloc fail offsets"); return -1; }
    unsigned long runningStrOff = 1; i=0; iter = lks_mods;
    while (iter && i < num_modules) {
        module_strtab_base_offset[i] = runningStrOff;
        if (iter->strtab_size > 0) runningStrOff += iter->strtab_size;
        iter = (lks_module_t*)iter->next; i++; }

    /* Fill merged symbol table */
    unsigned long sym_write_idx = 1; i=0; iter = lks_mods;
    while (iter && i < num_modules) {
        for (j=0; j<iter->num_symtab; ++j) { Elf64_Sym s = iter->symtab[j]; s.st_name += module_strtab_base_offset[i]; merged_syms[sym_write_idx++] = s; }
        if (iter->strtab && iter->strtab_size>0) memcpy(unified_strtab + module_strtab_base_offset[i], iter->strtab, iter->strtab_size);
        iter = (lks_module_t*)iter->next; i++; }

    if (type == ET_REL) {
        /* Minimal ET_REL writer: only .text, .symtab, .strtab, .shstrtab; no program headers */
        const int text_offset = ALIGNMENT;
        const int symtab_offset = text_offset + 0x100;
        const int strtab_offset = symtab_offset + sizeof(Elf64_Sym) * (total_syms + 1);
        const int shstrtab_offset = strtab_offset + strTabLen;
        const int sh_offset = ((shstrtab_offset + sizeof(shstrtab))/ALIGNMENT + 1) * ALIGNMENT;

        PRINT_INFOF("libkallsyms(ET_REL): layout\n");
        PRINT_INFOF("  .text:     0x%x\n", text_offset);
        PRINT_INFOF("  .symtab:   0x%x\n", symtab_offset);
        PRINT_INFOF("  .strtab:   0x%x\n", strtab_offset);
        PRINT_INFOF("  .shstrtab: 0x%x\n", shstrtab_offset);
        PRINT_INFOF("  shdrs:     0x%x\n", sh_offset);

        unsigned long cur_pos = 0;

        // === ELF Header ===
        Elf64_Ehdr ehdr = {0};
        memcpy(ehdr.e_ident, ELFMAG, SELFMAG);
        ehdr.e_ident[EI_CLASS] = ELFCLASS64;
        ehdr.e_ident[EI_DATA] = ELFDATA2LSB;
        ehdr.e_ident[EI_VERSION] = EV_CURRENT;
        ehdr.e_ident[EI_OSABI] = ELFOSABI_SYSV;
        ehdr.e_type = ET_REL;
        ehdr.e_machine = EM_X86_64;
        ehdr.e_version = EV_CURRENT;
        ehdr.e_entry = 0;
        ehdr.e_phoff = 0;          // no program headers in ET_REL
        ehdr.e_shoff = sh_offset;
        ehdr.e_flags = 0;
        ehdr.e_ehsize = sizeof(Elf64_Ehdr);
        ehdr.e_phentsize = sizeof(Elf64_Phdr);
        ehdr.e_phnum = 0;
        ehdr.e_shentsize = sizeof(Elf64_Shdr);
        ehdr.e_shnum = 5;          // null + .text + .symtab + .strtab + .shstrtab
        ehdr.e_shstrndx = 4;       // index of .shstrtab

    PRINT_INFOF("libkallsyms(ET_REL): writing ELF header, size: %d\n", (int)sizeof(ehdr));
        write_func(&ehdr, sizeof(ehdr));
        cur_pos += sizeof(ehdr);

        // pad to .text
        write_func(zeros, text_offset - cur_pos);
        cur_pos = text_offset;

    // minimal code payload (same as ET_DYN for now)
    unsigned char code[] = {0xb8, 0x2a, 0x00, 0x00, 0x00, 0xc3};
    unsigned char code2[] = {0xb8, 0x2b, 0x00, 0x00, 0x00, 0xc3};
    PRINT_INFOF("libkallsyms(ET_REL): writing .text (size=%zu)\n", (size_t)(sizeof(code) + sizeof(code2)));
        write_func(code, sizeof(code));
        write_func(code2, sizeof(code2));
        cur_pos += sizeof(code) + sizeof(code2);

        // .symtab
    PRINT_INFOF("libkallsyms(ET_REL): writing .symtab count=%lu\n", (unsigned long)(total_syms + 1));
        write_func(zeros, symtab_offset - cur_pos); cur_pos = symtab_offset;
        write_func(merged_syms, sizeof(Elf64_Sym) * (total_syms + 1));
        cur_pos += sizeof(Elf64_Sym) * (total_syms + 1);

        // .strtab (use unified_strtab)
    PRINT_INFOF("libkallsyms(ET_REL): writing .strtab size=%lu\n", strTabLen);
        write_func(zeros, strtab_offset - cur_pos); cur_pos = strtab_offset;
        write_func(unified_strtab, strTabLen);
        cur_pos += strTabLen;

        // .shstrtab
    PRINT_INFOF("libkallsyms(ET_REL): writing .shstrtab size=%zu\n", sizeof(shstrtab));
        write_func(zeros, shstrtab_offset - cur_pos); cur_pos = shstrtab_offset;
        write_func(shstrtab, sizeof(shstrtab));
        cur_pos += sizeof(shstrtab);

        // Section headers
        write_func(zeros, sh_offset - cur_pos); cur_pos = sh_offset;

        // null
        Elf64_Shdr sh_null = {0};
        write_func(&sh_null, sizeof(sh_null)); cur_pos += sizeof(sh_null);

    // .text
        Elf64_Shdr sh_text = {0};
        sh_text.sh_name = 1; // ".text"
        sh_text.sh_type = SHT_PROGBITS;
        sh_text.sh_flags = SHF_ALLOC | SHF_EXECINSTR;
        sh_text.sh_addr = 0;
        sh_text.sh_offset = text_offset;
        sh_text.sh_size = sizeof(code) + sizeof(code2);
        sh_text.sh_addralign = 1;
        write_func(&sh_text, sizeof(sh_text)); cur_pos += sizeof(sh_text);

        // .symtab
        Elf64_Shdr sh_symtab = {0};
        sh_symtab.sh_name = 70; // .symtab
        sh_symtab.sh_type = SHT_SYMTAB;
        sh_symtab.sh_offset = symtab_offset;
        sh_symtab.sh_size = sizeof(Elf64_Sym) * (total_syms + 1);
        sh_symtab.sh_link = 3; // index of .strtab
        sh_symtab.sh_info = 1; // one local (NULL)
        sh_symtab.sh_addralign = 8;
        sh_symtab.sh_entsize = sizeof(Elf64_Sym);
        write_func(&sh_symtab, sizeof(sh_symtab)); cur_pos += sizeof(sh_symtab);

        // .strtab
        Elf64_Shdr sh_strtab = {0};
        sh_strtab.sh_name = 78; // .strtab
        sh_strtab.sh_type = SHT_STRTAB;
        sh_strtab.sh_offset = strtab_offset;
        sh_strtab.sh_size = strTabLen;
        sh_strtab.sh_addralign = 1;
        write_func(&sh_strtab, sizeof(sh_strtab)); cur_pos += sizeof(sh_strtab);

        // .shstrtab
        Elf64_Shdr sh_shstrtab = {0};
        sh_shstrtab.sh_name = 86; // .shstrtab
        sh_shstrtab.sh_type = SHT_STRTAB;
        sh_shstrtab.sh_offset = shstrtab_offset;
        sh_shstrtab.sh_size = sizeof(shstrtab);
        sh_shstrtab.sh_addralign = 1;
        write_func(&sh_shstrtab, sizeof(sh_shstrtab)); cur_pos += sizeof(sh_shstrtab);

        PRINT_INFOF("libkallsyms(ET_REL): Wrote minimal relocatable ELF (no dynamic sections)\n");

        /* cleanup */
        FREE(module_strtab_base_offset);
        FREE(unified_strtab);
        FREE(merged_syms);
        return 0;
    }

    /* === ET_DYN path === */
    /* Create .dynsym/.dynstr as (possibly reordered) copies for runtime */
    Elf64_Sym *dynsym = (Elf64_Sym*)MALLOC(sizeof(Elf64_Sym) * (total_syms + 1));
    if (!dynsym) { PRINT_ERR("libkallsyms: dynsym alloc failed"); FREE(module_strtab_base_offset); FREE(unified_strtab); FREE(merged_syms); return -1; }
    memcpy(dynsym, merged_syms, sizeof(Elf64_Sym) * (total_syms + 1));
    Elf64_Sym *reordered = reorder_dynsym_for_gnu(dynsym, total_syms + 1, 1, unified_strtab);
    if (reordered) { FREE(dynsym); dynsym = reordered; }
    char *dynstr = (char*)MALLOC(strTabLen);
    if (!dynstr) { PRINT_ERR("libkallsyms: dynstr alloc failed"); FREE(dynsym); FREE(module_strtab_base_offset); FREE(unified_strtab); FREE(merged_syms); return -1; }
    memcpy(dynstr, unified_strtab, strTabLen);

    /* Ensure both base version name and secondary version name exist in dynstr/unified */
    const char *base_name = "libkallsyms.so"; size_t base_name_len = strlen(base_name) + 1; unsigned long base_name_off = 0;
    const char *version_name = "ker";           size_t version_name_len = strlen(version_name) + 1; unsigned long version_name_off = 0;
    /* helper to find string offset */
    unsigned long scan = 0;
    while (scan < strTabLen) { size_t l = strlen(&dynstr[scan]); if (l==0){ scan++; continue;} if (!base_name_off && strcmp(&dynstr[scan], base_name)==0) base_name_off = scan; if (!version_name_off && strcmp(&dynstr[scan], version_name)==0) version_name_off = scan; if (base_name_off && version_name_off) break; scan += l + 1; }
    if (!base_name_off) {
        if (lks_append_to_strtabs(&dynstr, &unified_strtab, &strTabLen,
                                  base_name, base_name_len, &base_name_off) != 0) {
            FREE(dynsym); FREE(module_strtab_base_offset); vfree(dynstr); FREE(unified_strtab); FREE(merged_syms); return -1;
        }
    }
    if (!version_name_off) {
        if (lks_append_to_strtabs(&dynstr, &unified_strtab, &strTabLen,
                                  version_name, version_name_len, &version_name_off) != 0) {
            FREE(dynsym); FREE(module_strtab_base_offset); vfree(dynstr); FREE(unified_strtab); FREE(merged_syms); return -1;
        }
    }
    /* Build .gnu.hash against updated dynstr */
    unsigned char *gnu_hash_blob = NULL; unsigned long gnu_hash_size = 0; if (build_gnu_hash_section(dynsym, total_syms + 1, dynstr, 1, &gnu_hash_blob, &gnu_hash_size) != 0) { PRINT_ERR("libkallsyms: build_gnu_hash_section failed"); gnu_hash_size = 0; }
    unsigned long gnu_hash_padded = (gnu_hash_size + 7) & ~((unsigned long)7);
    /* versym table */
    unsigned long versym_count = total_syms + 1; unsigned long versym_size = versym_count * sizeof(Elf64_Half); Elf64_Half *versym = vmalloc(versym_size); if(!versym){ PRINT_ERR("libkallsyms: versym alloc fail"); if(gnu_hash_blob)vfree(gnu_hash_blob); FREE(dynsym); FREE(module_strtab_base_offset); vfree(dynstr); FREE(unified_strtab); FREE(merged_syms); return -1;} versym[0]=0; unsigned long sidx; for(sidx=1;sidx<versym_count;++sidx) versym[sidx]=2; /* version index 2 */
    /* verdef blob */
    lks_Elf64_Verdef verdef1={0}, verdef2={0}; lks_Elf64_Verdaux aux1={0}, aux2={0};
    unsigned int base_hash = elf_sysv_hash((const unsigned char*)base_name);
    unsigned int ker_hash  = elf_sysv_hash((const unsigned char*)version_name);
    /* BASE node (index 1) named after the file */
    verdef1.vd_version=1; verdef1.vd_flags=VER_FLG_BASE; verdef1.vd_ndx=1; verdef1.vd_cnt=1; verdef1.vd_hash=base_hash; verdef1.vd_aux=sizeof(lks_Elf64_Verdef); verdef1.vd_next=sizeof(lks_Elf64_Verdef)+sizeof(lks_Elf64_Verdaux);
    aux1.vda_name=base_name_off; aux1.vda_next=0;
    /* Second node (index 2) named 'ker' */
    verdef2.vd_version=1; verdef2.vd_flags=0; verdef2.vd_ndx=2; verdef2.vd_cnt=1; verdef2.vd_hash=ker_hash; verdef2.vd_aux=sizeof(lks_Elf64_Verdef); verdef2.vd_next=0;
    aux2.vda_name=version_name_off; aux2.vda_next=0;
    unsigned long verdef_size=(sizeof(lks_Elf64_Verdef)+sizeof(lks_Elf64_Verdaux))*2; unsigned char *verdef_blob=vmalloc(verdef_size); if(!verdef_blob){ PRINT_ERR("libkallsyms: verdef alloc fail"); if(gnu_hash_blob)vfree(gnu_hash_blob); vfree(versym); FREE(dynsym); FREE(module_strtab_base_offset); vfree(dynstr); FREE(unified_strtab); FREE(merged_syms); return -1;} unsigned char *vptr=verdef_blob; memcpy(vptr,&verdef1,sizeof(verdef1)); vptr+=sizeof(verdef1); memcpy(vptr,&aux1,sizeof(aux1)); vptr+=sizeof(aux1); memcpy(vptr,&verdef2,sizeof(verdef2)); vptr+=sizeof(verdef2); memcpy(vptr,&aux2,sizeof(aux2));

    /* Layout with version sections */
    const int ph_offset = sizeof(Elf64_Ehdr);
    const int text_offset = ALIGNMENT;
    const int dynsym_offset = text_offset + 0x100;
    const unsigned int dynsym_symoffset = 1; /* index of first global symbol (after NULL local) */
    const int dynstr_offset = dynsym_offset + sizeof(Elf64_Sym) * (total_syms + 1);
    
    unsigned long dynstr_padded_len = strTabLen;
    if (dynstr_padded_len & 7) dynstr_padded_len = (dynstr_padded_len + 7) & ~7UL;
    const int gnu_hash_offset = dynstr_offset + dynstr_padded_len; /* dynstr only, 8-aligned */
    
    const int versym_offset = gnu_hash_offset + gnu_hash_padded;
    const int verdef_offset = (versym_offset + versym_size + 7) & ~7;
    const int dyn_offset = (verdef_offset + verdef_size + 7) & ~7;
    /* Build separate debug .strtab with "@ker" appended to every symbol name */
    unsigned long debugStrExtraPerName = 4; /* length of "@ker" */
    unsigned long debugStrEst = strTabLen + debugStrExtraPerName * total_syms; /* estimation (exact below) */
    char *debug_strtab = vmalloc(debugStrEst ? debugStrEst : 1);
    if (!debug_strtab) { PRINT_ERR("libkallsyms: debug_strtab alloc fail"); if(gnu_hash_blob)vfree(gnu_hash_blob); vfree(versym); vfree(verdef_blob); FREE(dynsym); FREE(module_strtab_base_offset); vfree(dynstr); FREE(unified_strtab); FREE(merged_syms); return -1; }
    unsigned long *offset_map = vmalloc(strTabLen * sizeof(unsigned long));
    if (!offset_map) { PRINT_ERR("libkallsyms: offset_map alloc fail"); vfree(debug_strtab); if(gnu_hash_blob)vfree(gnu_hash_blob); vfree(versym); vfree(verdef_blob); FREE(dynsym); FREE(module_strtab_base_offset); vfree(dynstr); FREE(unified_strtab); FREE(merged_syms); return -1; }
    unsigned long orig_off = 0, new_off = 0; /* iterate through dynstr to build debug_strtab */
    while (orig_off < strTabLen) {
        const char *s = &unified_strtab[orig_off];
        size_t len = strlen(s);
        offset_map[orig_off] = new_off; /* record mapping */
        if (len == 0) { /* leading empty string */
            if (new_off >= debugStrEst) { /* expand */
                char *tmp = vmalloc(debugStrEst + 16);
                if (!tmp) { PRINT_ERR("libkallsyms: debug_strtab grow fail (empty) "); goto debug_strtab_fail; }
                memcpy(tmp, debug_strtab, new_off);
                vfree(debug_strtab); debug_strtab = tmp; debugStrEst += 16;
            }
            debug_strtab[new_off++] = '\0';
        } else {
            /* ensure capacity */
            unsigned long need = len + 4 + 1; /* original + "@ker" + nul */
            if (new_off + need > debugStrEst) {
                unsigned long grow = debugStrEst;
                if (grow < need) grow = need;
                char *tmp = vmalloc(debugStrEst + grow);
                if (!tmp) { PRINT_ERR("libkallsyms: debug_strtab grow fail"); goto debug_strtab_fail; }
                memcpy(tmp, debug_strtab, new_off);
                vfree(debug_strtab); debug_strtab = tmp; debugStrEst += grow;
            }
            memcpy(&debug_strtab[new_off], s, len);
            new_off += len;
            memcpy(&debug_strtab[new_off], "@ker", 4);
            new_off += 4;
            debug_strtab[new_off++]='\0';
        }
        orig_off += len + 1;
    }
    unsigned long debugStrTabLen = new_off; /* final size */
    /* Create symtab copy with adjusted name offsets */
    Elf64_Sym *symtab_syms = (Elf64_Sym*)MALLOC(sizeof(Elf64_Sym)*(total_syms+1));
    if (!symtab_syms) { PRINT_ERR("libkallsyms: symtab_syms alloc fail"); goto debug_strtab_fail; }
    memcpy(symtab_syms, merged_syms, sizeof(Elf64_Sym)*(total_syms+1));
    for (sidx=1; sidx < total_syms + 1; ++sidx) {
        unsigned long orig_name_off = merged_syms[sidx].st_name;
        if (orig_name_off < strTabLen) {
            symtab_syms[sidx].st_name = offset_map[orig_name_off];
        } else {
            PRINT_ERR("libkallsyms: st_name out of range when remapping");
            symtab_syms[sidx].st_name = 0;
        }
    }

    /* Now compute layout with separate debug .strtab */
    const int symtab_offset = (dyn_offset + sizeof(Elf64_Dyn)*8 + 7) & ~7; /* 8-align after dynamic */
    const int strtab_offset = symtab_offset + sizeof(Elf64_Sym) * (total_syms + 1);
    const int shstrtab_offset = strtab_offset + debugStrTabLen;
    const int sh_offset = ((shstrtab_offset + sizeof(shstrtab))/ALIGNMENT + 1) * ALIGNMENT;

    PRINT_INFOF("libkallsyms: ELF layout with .gnu.hash:\n");
    PRINT_INFOF("  ELF header:        0x%lx - 0x%lx\n", 0UL, (unsigned long)ph_offset);
    PRINT_INFOF("  Program headers:   0x%lx - 0x%lx\n", (unsigned long)ph_offset, (unsigned long)text_offset);
    PRINT_INFOF("  .text:             0x%lx - 0x%lx\n", (unsigned long)text_offset, (unsigned long)dynsym_offset);
    PRINT_INFOF("  .dynsym:           0x%lx - 0x%lx\n", (unsigned long)dynsym_offset, (unsigned long)dynstr_offset);
    PRINT_INFOF("  .dynstr:           0x%lx - 0x%lx\n", (unsigned long)dynstr_offset, (unsigned long)gnu_hash_offset);
    PRINT_INFOF("  .gnu.hash:         0x%lx - 0x%lx (size=%lu)\n", (unsigned long)gnu_hash_offset, (unsigned long)(gnu_hash_offset+gnu_hash_padded), gnu_hash_size);
    PRINT_INFOF("  .gnu.version:      0x%lx - 0x%lx (size=%lu)\n", (unsigned long)versym_offset, (unsigned long)(versym_offset+versym_size), versym_size);
    PRINT_INFOF("  .gnu.version_d:    0x%lx - 0x%lx (size=%lu)\n", (unsigned long)verdef_offset, (unsigned long)(verdef_offset+verdef_size), verdef_size);
    PRINT_INFOF("  .dynamic:          0x%lx - 0x%lx\n", (unsigned long)dyn_offset, (unsigned long)symtab_offset);
    PRINT_INFOF("  .symtab:           0x%lx - 0x%lx\n", (unsigned long)symtab_offset, (unsigned long)strtab_offset);
    PRINT_INFOF("  .strtab:           0x%lx - 0x%lx (size=%lu)\n", (unsigned long)strtab_offset, (unsigned long)shstrtab_offset, (unsigned long)debugStrTabLen);
    PRINT_INFOF("  .shstrtab:         0x%lx - 0x%lx\n", (unsigned long)shstrtab_offset, (unsigned long)sh_offset);
    PRINT_INFOF("  Section headers:   0x%lx\n", (unsigned long)sh_offset);

    unsigned long cur_pos = 0;

#ifndef DT_GNU_HASH
#define DT_GNU_HASH 0x6ffffef5
#endif
    Elf64_Dyn dyn_entries[] = {
        { DT_SYMTAB, dynsym_offset },
        { DT_STRTAB, dynstr_offset },
        { DT_STRSZ,  strTabLen }, /* size of .dynstr only */
        { DT_GNU_HASH, gnu_hash_offset },
        { DT_VERSYM, versym_offset },
        { DT_VERDEF, verdef_offset },
        { DT_VERDEFNUM, 2 },
        { DT_NULL, 0 }
    };

    // === ELF Header ===
    Elf64_Ehdr ehdr = {0};
    memcpy(ehdr.e_ident, ELFMAG, SELFMAG);
    ehdr.e_ident[EI_CLASS] = ELFCLASS64;
    ehdr.e_ident[EI_DATA] = ELFDATA2LSB;
    ehdr.e_ident[EI_VERSION] = EV_CURRENT;
    ehdr.e_ident[EI_OSABI] = ELFOSABI_SYSV;
    ehdr.e_type = ET_DYN;
    ehdr.e_machine = EM_X86_64;
    ehdr.e_version = EV_CURRENT;
    ehdr.e_entry = 0; // No entry point
    ehdr.e_phoff = ph_offset;
    ehdr.e_shoff = sh_offset;
    ehdr.e_flags = 0;
    ehdr.e_ehsize = sizeof(Elf64_Ehdr);
    ehdr.e_phentsize = sizeof(Elf64_Phdr);
    ehdr.e_phnum = 2; // PT_LOAD + PT_DYNAMIC
    ehdr.e_shentsize = sizeof(Elf64_Shdr);
    ehdr.e_shnum = 11; // null + .text + .gnu.hash + .dynsym + .dynstr + .gnu.version + .gnu.version_d + .dynamic + .symtab + .strtab + .shstrtab
    ehdr.e_shstrndx = 10; // index of .shstrtab

    PRINT_INFOF("libkallsyms: writing ELF header, size: %d\n", sizeof(ehdr));
    write_func(&ehdr, sizeof(ehdr));
    cur_pos += sizeof(ehdr);

    
    // === Program Header: PT_LOAD (text segment) ===
    // const uint64_t text_vaddr = BASE_VADDR + text_offset;
    Elf64_Phdr phdr = {0};
    phdr.p_type = PT_LOAD;
    phdr.p_offset = 0; //must be page aligned:  libkallsyms.so: ELF load command address/offset not page-aligned
    phdr.p_vaddr = 0;
    phdr.p_paddr = 0;
    /* Limit PT_LOAD to end of .dynamic (exclude non-ALLOC debug tables) */
    phdr.p_filesz = dyn_offset + sizeof(dyn_entries);
    phdr.p_memsz = phdr.p_filesz;
    phdr.p_flags = PF_R | PF_X;
    phdr.p_align = ALIGNMENT;

    PRINT_INFOF("libkallsyms: writing Program header, size: %d\n", sizeof(phdr));
    write_func(&phdr, sizeof(phdr));
    cur_pos += sizeof(phdr);

    Elf64_Phdr phdr_dynamic = {0};
    phdr_dynamic.p_type   = PT_DYNAMIC;
    phdr_dynamic.p_offset = dyn_offset;
    phdr_dynamic.p_vaddr  = dyn_offset;
    phdr_dynamic.p_paddr  = phdr_dynamic.p_vaddr;
    phdr_dynamic.p_filesz = sizeof(dyn_entries);
    write_func(&phdr_dynamic, sizeof(phdr_dynamic));

    cur_pos += sizeof(phdr_dynamic);

    // Pad to text section
    PRINT_INFOF("libkallsyms: seeking text_offset\n");
    write_func(zeros, text_offset - cur_pos);
    cur_pos = text_offset;
    // seek_func(text_offset, SEEK_SET);
    
    // === Machine code: int my_func() { return 42; } ===
    // mov eax, 42; ret
    unsigned char code[] = {0xb8, 0x2a, 0x00, 0x00, 0x00, 0xc3};
    unsigned char code2[] = {0xb8, 0x2b, 0x00, 0x00, 0x00, 0xc3}; //myfunc2 -> return 43
    write_func(code, sizeof(code));
    write_func(code2, sizeof(code2));
    cur_pos += sizeof(code) + sizeof(code2);
    
    
    /* write runtime .dynsym/.dynstr */
    /* .dynsym */
    write_func(zeros, dynsym_offset - cur_pos); cur_pos = dynsym_offset;
    write_func(dynsym, sizeof(Elf64_Sym) * (total_syms + 1));
    cur_pos += sizeof(Elf64_Sym) * (total_syms + 1);
    PRINT_INFOF("libkallsyms: wrote dynsym with %lu symbols (reordered)\n", (unsigned long)total_syms);
    
    // === String table for symbols ===
    // seek_func(strtab_offset, SEEK_SET);
    write_func(zeros, dynstr_offset - cur_pos);
    cur_pos = dynstr_offset;

    /* .dynstr */
    write_func(dynstr, strTabLen);
    if (dynstr_padded_len > strTabLen) {
        char pad[8] = {0};
        write_func(pad, dynstr_padded_len - strTabLen);
    }
    cur_pos += dynstr_padded_len;
    // PRINT_INFOF("libkallsyms: Count: %lu\n", count);
    // PRINT_INFOF("libkallsyms: names_size: %lu\n", names_size);
    // PRINT_INFOF("libkallsyms: strTabLen: %lu\n", strTabLen);
    
    
    
    /* .gnu.hash */
    PRINT_INFOF("libkallsyms: seeking gnu_hash_offset\n");
    write_func(zeros, gnu_hash_offset - cur_pos); cur_pos = gnu_hash_offset;
    if (gnu_hash_size) {
        write_func(gnu_hash_blob, gnu_hash_size);
        if (gnu_hash_padded > gnu_hash_size) 
            write_func(zeros, gnu_hash_padded - gnu_hash_size);
    }
    cur_pos += gnu_hash_padded;
    /* .gnu.version */
    write_func(zeros, versym_offset - cur_pos); 
    cur_pos = versym_offset; 
    write_func(versym, versym_size); 
    cur_pos += versym_size; 
    if (versym_size & 7){ unsigned long pad=8-(versym_size&7); write_func(zeros,pad); cur_pos+=pad; }
    /* .gnu.version_d */
    write_func(zeros, verdef_offset - cur_pos); cur_pos = verdef_offset; write_func(verdef_blob, verdef_size); cur_pos += verdef_size; if (verdef_size & 7){ unsigned long pad=8-(verdef_size&7); write_func(zeros,pad); cur_pos+=pad; }

    PRINT_INFOF("libkallsyms: seeking dyn_offset\n");
    write_func(zeros, dyn_offset - cur_pos); cur_pos = dyn_offset;
    write_func(dyn_entries, sizeof(dyn_entries)); cur_pos += sizeof(dyn_entries);
    /* .symtab (full) */
    PRINT_INFOF("libkallsyms: seeking symtab_offset\n");
    write_func(zeros, symtab_offset - cur_pos); cur_pos = symtab_offset;
    write_func(symtab_syms, sizeof(Elf64_Sym) * (total_syms + 1)); cur_pos += sizeof(Elf64_Sym) * (total_syms + 1);
    /* .strtab */
    PRINT_INFOF("libkallsyms: seeking strtab_offset\n");
    write_func(zeros, strtab_offset - cur_pos); cur_pos = strtab_offset;
    write_func(debug_strtab, debugStrTabLen); cur_pos += debugStrTabLen;
    

    // === Section header string table ===
    // Contains names of sections: ".text", ".symtab", ".strtab", ".shstrtab"
    PRINT_INFOF("libkallsyms: seeking shstrtab_offset\n", strTabLen);
    write_func(zeros, shstrtab_offset - cur_pos);
    cur_pos = shstrtab_offset;
    
    PRINT_INFOF("libkallsyms: writing shstrtab\n");
    write_func(shstrtab, sizeof(shstrtab));
    cur_pos += sizeof(shstrtab);
    
    
    // === Section headers ===
    // seek_func(sh_offset, SEEK_SET);
    PRINT_INFOF("libkallsyms: seeking sh_offset\n", strTabLen);
    write_func(zeros, sh_offset - cur_pos);
    cur_pos = sh_offset;
    
    PRINT_INFOF("libkallsyms: writing section headers\n");
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

    // .gnu.hash section
    Elf64_Shdr sh_gnu_hash = {0};
    sh_gnu_hash.sh_name = 7; // .gnu.hash
#ifndef SHT_GNU_HASH
#define SHT_GNU_HASH 0x6ffffff6
#endif
    sh_gnu_hash.sh_type = SHT_GNU_HASH;
    sh_gnu_hash.sh_flags = SHF_ALLOC;
    sh_gnu_hash.sh_addr = 0;
    sh_gnu_hash.sh_offset = gnu_hash_offset;
    sh_gnu_hash.sh_size = gnu_hash_padded;
    sh_gnu_hash.sh_addralign = 8;
    sh_gnu_hash.sh_link = 3; // link to .dynsym index
    sh_gnu_hash.sh_info = 0;
    write_func(&sh_gnu_hash, sizeof(sh_gnu_hash));
    cur_pos += sizeof(sh_gnu_hash);

    // .dynsym section header
    Elf64_Shdr sh_dynsym = {0};
    sh_dynsym.sh_name = 17; // .dynsym
    sh_dynsym.sh_type = SHT_DYNSYM;
    sh_dynsym.sh_offset = dynsym_offset;
    sh_dynsym.sh_size = sizeof(Elf64_Sym) * (total_syms + 1);
    sh_dynsym.sh_link = 4; // link to .dynstr
    sh_dynsym.sh_info = dynsym_symoffset; // index of first global symbol (last local + 1)
    sh_dynsym.sh_addralign = 8;
    sh_dynsym.sh_entsize = sizeof(Elf64_Sym);
    write_func(&sh_dynsym, sizeof(sh_dynsym)); cur_pos += sizeof(sh_dynsym);

    // .dynstr section header
    Elf64_Shdr sh_dynstr = {0};
    sh_dynstr.sh_name = 25; // .dynstr
    sh_dynstr.sh_type = SHT_STRTAB;
    sh_dynstr.sh_offset = dynstr_offset;
    sh_dynstr.sh_size = dynstr_padded_len;
    sh_dynstr.sh_addralign = 1;
    write_func(&sh_dynstr, sizeof(sh_dynstr)); cur_pos += sizeof(sh_dynstr);

    // .gnu.version section header
    Elf64_Shdr sh_versym = {0};
    sh_versym.sh_name = 33; /* .gnu.version */
    sh_versym.sh_type = SHT_GNU_versym; sh_versym.sh_flags = SHF_ALLOC;
    sh_versym.sh_offset = versym_offset; sh_versym.sh_size = versym_size; sh_versym.sh_link = 3; sh_versym.sh_addralign = 2; sh_versym.sh_entsize = sizeof(Elf64_Half);
    write_func(&sh_versym, sizeof(sh_versym)); cur_pos += sizeof(sh_versym);
    // .gnu.version_d section header
    Elf64_Shdr sh_verdef = {0};
    sh_verdef.sh_name = 46; /* .gnu.version_d */
    sh_verdef.sh_type = SHT_GNU_verdef; sh_verdef.sh_flags = SHF_ALLOC; sh_verdef.sh_offset = verdef_offset; sh_verdef.sh_size = verdef_size; sh_verdef.sh_link = 4; sh_verdef.sh_info = 2; sh_verdef.sh_addralign = 8;
    write_func(&sh_verdef, sizeof(sh_verdef)); cur_pos += sizeof(sh_verdef);
    // .dynamic section
    Elf64_Shdr sh_dynamic = {0};
    sh_dynamic.sh_name = 61; // .dynamic (new offset)
    sh_dynamic.sh_type = SHT_DYNAMIC;
    sh_dynamic.sh_flags = SHF_ALLOC;
    sh_dynamic.sh_addr = 0;
    sh_dynamic.sh_offset = dyn_offset;
    sh_dynamic.sh_size = sizeof(dyn_entries);
    sh_dynamic.sh_addralign = 8;
    sh_dynamic.sh_entsize = sizeof(Elf64_Dyn);
    sh_dynamic.sh_link = 4; // index of .dynstr
    write_func(&sh_dynamic, sizeof(sh_dynamic));
    cur_pos += sizeof(sh_dynamic);
    // .symtab section header
    Elf64_Shdr sh_symtab = {0};
    sh_symtab.sh_name = 70; // .symtab
    sh_symtab.sh_type = SHT_SYMTAB;
    sh_symtab.sh_offset = symtab_offset;
    sh_symtab.sh_size = sizeof(Elf64_Sym) * (total_syms + 1);
    sh_symtab.sh_link = 9; // index of .strtab
    sh_symtab.sh_info = 1; // one local (NULL)
    sh_symtab.sh_addralign = 8;
    sh_symtab.sh_entsize = sizeof(Elf64_Sym);
    write_func(&sh_symtab, sizeof(sh_symtab));
    cur_pos += sizeof(sh_symtab);

    // .strtab section header
    Elf64_Shdr sh_strtab = {0};
    sh_strtab.sh_name = 78; // .strtab
    sh_strtab.sh_type = SHT_STRTAB;
    sh_strtab.sh_offset = strtab_offset;
    sh_strtab.sh_size = debugStrTabLen;
    sh_strtab.sh_addralign = 1;
    write_func(&sh_strtab, sizeof(sh_strtab));
    cur_pos += sizeof(sh_strtab);

    // .shstrtab section
    Elf64_Shdr sh_shstrtab = {0};
    sh_shstrtab.sh_name = 86; // .shstrtab
    sh_shstrtab.sh_type = SHT_STRTAB;
    sh_shstrtab.sh_offset = shstrtab_offset;
    sh_shstrtab.sh_size = sizeof(shstrtab);
    sh_shstrtab.sh_addralign = 1;
    write_func(&sh_shstrtab, sizeof(sh_shstrtab));
    cur_pos += sizeof(sh_shstrtab);
    PRINT_INFOF("libkallsyms: Wrote full ELF with .gnu.hash\n");
    if (gnu_hash_blob) vfree(gnu_hash_blob);
    if (versym) vfree(versym);
    if (verdef_blob) vfree(verdef_blob);
    vfree(dynstr);
    FREE(dynsym);
    vfree(debug_strtab);
    vfree(offset_map);
    FREE(symtab_syms);
    FREE(unified_strtab);
    FREE(merged_syms);
    FREE(module_strtab_base_offset);
    return 0;

debug_strtab_fail:
    if (offset_map) vfree(offset_map);
    if (debug_strtab) vfree(debug_strtab);
    if (gnu_hash_blob) vfree(gnu_hash_blob);
    if (versym) vfree(versym);
    if (verdef_blob) vfree(verdef_blob);
    vfree(dynstr);
    FREE(dynsym);
    FREE(unified_strtab);
    FREE(merged_syms);
    FREE(module_strtab_base_offset);
    return -1;
}





static unsigned long mywrite(const void* data, unsigned long size) {
    // pr_info("%s: mywrite called, data: %lx, size: %x", MODULE_NAME, data, size);
    if (seq_file == NULL) {
        pr_err("seq_file is NULL\n");
        return -1;
    }

    if (size > 1024) {
        pr_alert("%s: mywrite called with > 1024 len, data: %lx, size: %x\n", MODULE_NAME, data, size);
    }

    return (unsigned long)seq_write(seq_file, data, size);
}


static int kallsyms_elf_show(struct seq_file *m, void *v) {
    // Custom logic to write an ELF-formatted in-memory symbol table
    int retVal;
    seq_file = m;
    
    pr_info("%s: starting kallsyms_elf_show", MODULE_NAME);
    LKS_LOCK(&modules_lock);
    retVal = makeElf(ET_DYN, modules_head, modules_count, &mywrite);
    LKS_UNLOCK(&modules_lock);
    // retVal = __main(&mywrite);
    if (retVal != 0) {
        pr_err("Failed to create ELF file\n");
    }
    return retVal;
}

/* === ET_REL procfs (.a) === */
static int kallsyms_ar_show(struct seq_file *m, void *v) {
    int retVal;
    seq_file = m;
    pr_info("%s: starting kallsyms_ar_show (ET_REL)", MODULE_NAME);
    LKS_LOCK(&modules_lock);
    retVal = makeElf(ET_REL, modules_head, modules_count, &mywrite);
    LKS_UNLOCK(&modules_lock);
    if (retVal != 0) {
        pr_err("Failed to create ET_REL ELF file\n");
    }
    return retVal;
}

static int kallsyms_elf_open(struct inode *inode, struct file *file) {
    pr_info("%s: kallsyms_elf_open called", MODULE_NAME);
    return single_open(file, kallsyms_elf_show, NULL);
}

static int kallsyms_ar_open(struct inode *inode, struct file *file) {
    pr_info("%s: kallsyms_ar_open called", MODULE_NAME);
    return single_open(file, kallsyms_ar_show, NULL);
}

static loff_t kallsyms_lseek(struct file *file, loff_t offset, int whence)
{
	struct seq_file *m = file->private_data;
    pr_info("%s: kallsyms_lseek called, size is: %lu", MODULE_NAME, file_size_dyn);

    if (whence == SEEK_END) {
        if (offset > 0)
            return -EINVAL;

        offset += file_size_dyn; //TODO: This can differ between calls and can be outdated due to insertions/removals
        return seq_lseek(file, offset, SEEK_SET);
    }

    return seq_lseek(file, offset, whence);
}

static loff_t kallsyms_ar_lseek(struct file *file, loff_t offset, int whence)
{
    struct seq_file *m = file->private_data;
    pr_info("%s: kallsyms_ar_lseek called, size is: %lu", MODULE_NAME, file_size_rel);

    if (whence == SEEK_END) {
        if (offset > 0)
            return -EINVAL;

        offset += file_size_rel;
        return seq_lseek(file, offset, SEEK_SET);
    }

    return seq_lseek(file, offset, whence);
}

static unsigned long mem_write(const void* data, unsigned long size) {
    // pr_info("%s: mem_write called, data: %lx, size: %x", MODULE_NAME, data, size);
    if (global_vma == NULL) {
        pr_err("global_vma is NULL\n");
        return -1;
    }
    void * write_end = global_write_start + file_size_dyn;

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
    int retVal;
    LKS_LOCK(&modules_lock);
    retVal = makeElf(ET_DYN, modules_head, modules_count, &mem_write);
    LKS_UNLOCK(&modules_lock);

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

static const struct proc_ops kallsyms_ar_fops = {
    .proc_open    = kallsyms_ar_open,
    .proc_read    = seq_read,
    .proc_lseek   = kallsyms_ar_lseek,
    .proc_release = single_release,
};




















//module insertion deletion hooks

static int lks_module_notify(struct notifier_block *nb, unsigned long op,
			     void *module)
{
    bool dryrun = false;
#ifdef DRYRUN
    if (modules_count > 2) {
        dryrun = true;
    }
#endif

    lks_module_t* new_mod = NULL;
    int ret = 0;
    struct module *mod = (struct module *)module;
    switch (op) {
        case MODULE_STATE_COMING:
            new_mod = vmalloc(sizeof(lks_module_t));
            if (!new_mod) {
                pr_alert("%s: failed to allocate memory for lks_module_t\n", MODULE_NAME);
                return -ENOMEM;
            }
            memset(new_mod, 0, sizeof(lks_module_t));

            //insert pointer to module kallsyms
            new_mod->name = mod->name;
            new_mod->next = NULL;

            struct mod_kallsyms *kallsyms = &mod->core_kallsyms;

            /* Build a filtered symtab/strtab that only contains publicly
             * available symbols (global/default visibility, defined).
             * We copy those into fresh vmalloc'ed buffers owned by new_mod.
             */
            do {
                Elf64_Sym *orig_sym = (Elf64_Sym *)kallsyms->symtab;
                const char *orig_str = (const char *)kallsyms->strtab;
                unsigned int orig_n  = kallsyms->num_symtab;

                /* First pass: count and total string length */
                unsigned int pub_count = 0; /* not including index 0 */
                unsigned long str_total = 1; /* leading NUL */
                unsigned int s;
                for (s = 1; s < orig_n; ++s) {
                    unsigned char bind = ELF64_ST_BIND(orig_sym[s].st_info);
                    unsigned char type = ELF64_ST_TYPE(orig_sym[s].st_info);
                    unsigned char vis  = ELF64_ST_VISIBILITY(orig_sym[s].st_other);
                    if ((bind == STB_GLOBAL || bind == STB_WEAK) &&
                        vis == STV_DEFAULT &&
                        orig_sym[s].st_shndx != SHN_UNDEF &&
                        type != STT_SECTION && type != STT_FILE) {
                        const char *name = orig_sym[s].st_name ? (orig_str + orig_sym[s].st_name) : "";
                        if (name && *name) {
                            ++pub_count;
                            str_total += strlen(name) + 1;
                        }
                    }
                }

                /* Allocate new tables */
                Elf64_Sym *new_sym = (Elf64_Sym *)vmalloc(sizeof(Elf64_Sym) * (pub_count + 1));
                char *new_str = (char *)vmalloc(str_total ? str_total : 1);
                if (!new_sym || !new_str) {
                    if (new_sym) vfree(new_sym);
                    if (new_str) vfree(new_str);
                    vfree(new_mod);
                    pr_alert("%s: failed to allocate filtered sym/str tables for %s\n", MODULE_NAME, mod->name);
                    return -ENOMEM;
                }

                /* Initialize string table */
                unsigned long woff = 0;
                new_str[woff++] = '\0';

                /* Preserve 0th symbol */
                memset(&new_sym[0], 0, sizeof(new_sym[0]));

                /* Second pass: copy filtered symbols and names */
                unsigned int out_idx = 1;
                for (s = 1; s < orig_n; ++s) {
                    unsigned char bind = ELF64_ST_BIND(orig_sym[s].st_info);
                    unsigned char type = ELF64_ST_TYPE(orig_sym[s].st_info);
                    unsigned char vis  = ELF64_ST_VISIBILITY(orig_sym[s].st_other);
                    if ((bind == STB_GLOBAL || bind == STB_WEAK) &&
                        vis == STV_DEFAULT &&
                        orig_sym[s].st_shndx != SHN_UNDEF &&
                        type != STT_SECTION && type != STT_FILE) {
                        const char *name = orig_sym[s].st_name ? (orig_str + orig_sym[s].st_name) : "";
                        if (!name || !*name)
                            continue;

                        /* Copy symbol and rewrite st_name */
                        new_sym[out_idx] = orig_sym[s];
                        new_sym[out_idx].st_name = (Elf64_Word)woff;
                        new_sym[out_idx].st_shndx = SHN_ABS; //mark as absolute to not confuse the runtime loader
                        size_t nlen = strlen(name) + 1;
                        memcpy(new_str + woff, name, nlen);
                        woff += nlen;
                        ++out_idx;
                    }
                }

                new_mod->symtab = new_sym;
                new_mod->num_symtab = out_idx; /* includes index 0 */
                new_mod->strtab = new_str;
                new_mod->strtab_size = woff;

                pr_info("%s: module %s filtered: %u/%u public symbols, strtab size: %lu\n",
                        MODULE_NAME, mod->name, out_idx ? (out_idx - 1) : 0, orig_n, woff);
            } while (0);

            if (dryrun) {
                vfree(new_mod);
                pr_info("%s: dryrun mode, not adding module %s\n", MODULE_NAME, mod->name);
                break;
            }
            LKS_LOCK(&modules_lock);
            if (modules_tail == NULL) {
                modules_head = new_mod;
                modules_tail = new_mod;
                modules_count = 1;
                LKS_UNLOCK(&modules_lock);
                pr_info("%s: module %s added as first module\n", MODULE_NAME, mod->name);
                break;
            }

            modules_tail->next = new_mod;
            modules_tail = new_mod;
            modules_count++;

            // recompute file sizes for both ET_DYN (.so) and ET_REL (.a)
            file_size_dyn = elfMaker_calcSize(modules_head, modules_count, ET_DYN);
            file_size_rel = elfMaker_calcSize(modules_head, modules_count, ET_REL);
            // set filesize on proc entries
            if (proc_entry) proc_set_size(proc_entry, file_size_dyn);
            if (proc_entry_rel) proc_set_size(proc_entry_rel, file_size_rel);

            LKS_UNLOCK(&modules_lock);

            pr_info("%s: module coming: %s\n", MODULE_NAME, mod->name);
            break;
        case MODULE_STATE_GOING:
            pr_info("%s: module going: %s\n", MODULE_NAME, mod->name);

            //remove from linked list
            {
                lks_module_t* prev = NULL;
                LKS_LOCK(&modules_lock);
                lks_module_t* curr = modules_head;
                while (curr) {
                    if (curr->name != NULL && mod->name != NULL &&strcmp(curr->name, mod->name) == 0) {
                        if (!dryrun) {
                            if (prev) {
                                prev->next = curr->next;
                            } else {
                                modules_head = curr->next;
                            }
                            if (curr == modules_tail) {
                                modules_tail = prev;
                            }

                            /* Free filtered tables we allocated on COMING */
                            if (curr->symtab)
                                vfree(curr->symtab);
                            if (curr->strtab)
                                vfree(curr->strtab);
                            vfree(curr);
                            modules_count--;

                            // recompute file sizes for both entries
                            file_size_dyn = elfMaker_calcSize(modules_head, modules_count, ET_DYN);
                            file_size_rel = elfMaker_calcSize(modules_head, modules_count, ET_REL);
                            if (proc_entry) proc_set_size(proc_entry, file_size_dyn);
                            if (proc_entry_rel) proc_set_size(proc_entry_rel, file_size_rel);
                        }
                        pr_info("%s: module %s removed, new count: %u\n", MODULE_NAME, mod->name, modules_count);
                        LKS_UNLOCK(&modules_lock);
                        break;
                    }
                    prev = curr;
                    curr = curr->next;
                }
                if (!curr) {
                    LKS_UNLOCK(&modules_lock);
                }
            }

            break;
    }

    return NOTIFY_OK;
}


struct notifier_block nb = {
    .notifier_call = lks_module_notify,
};








static int __init libkallsyms_init_syms(void) {

    pr_info("%s: creating array of name pointers\n", MODULE_NAME);

    kallsyms_name_types = (char*)vmalloc(kallsyms_num_syms * sizeof(char));
    if (!kallsyms_name_types) {
        pr_alert("%s: failed to allocate memory for name pointers\n", MODULE_NAME);
        return -ENOMEM;
    }
    
    unsigned int pos;
    int i;
    char symBuffer[MAX_SYM_LEN] = {0};
    char is_per_cpu = 1;

    // pos = &kallsyms_names[0];
    kallsyms_names_size = 0;


    for (i = 0, pos = 0; i < kallsyms_num_syms; i++) {
        
        kallsyms_name_types[i] = kallsyms_get_symbol_type(pos);

        pos = kallsyms_expand_symbol(pos, symBuffer, MAX_SYM_LEN);


        if (is_per_cpu && strcmp(symBuffer, "__per_cpu_end") == 0) {
            kallsyms_per_cpu_symbol_count = i + 1;
            pr_info("%s: found __per_cpu_end at symbol %d, pos: 0x%lx, address: 0x%lx\n", MODULE_NAME, i, pos, kallsyms_sym_address(i));
            kallsyms_first_non_per_cpu_name_pos = pos; //already points to next symbol
            is_per_cpu = 0; // no more per-cpu symbols
        }


        if (is_per_cpu)
            kallsyms_per_cpu_names_size += (unsigned long)strlen(symBuffer) + 1;   
        else
            kallsyms_names_size += (unsigned long)strlen(symBuffer) + 1;

        if (i % 25000 == 0) {
            pr_info("%s: loaded symbol %d, length: %lu, next pos: %lx, symbuf: %s, address: 0x%lx\n", MODULE_NAME, i, (unsigned long)strlen(symBuffer), pos, symBuffer, kallsyms_sym_address(i));
        }
    }

    if (is_per_cpu) {
        //never found __per_cpu_end, all symbols non per-cpu
        kallsyms_per_cpu_symbol_count = 0;
        kallsyms_per_cpu_names_size = 0;
        kallsyms_first_non_per_cpu_name_pos = 0; 
        pr_warn("%s: never found __per_cpu_end, all %d symbols are per-cpu\n", MODULE_NAME, kallsyms_num_syms);
    }

    pr_info("%s: created array of name pointers\n", MODULE_NAME);

    pr_info("%s: creating lks_module_t\n", MODULE_NAME);
    modules_head = make_lks_mod(
        &kallsyms_name_types[kallsyms_per_cpu_symbol_count], //char* nameTypes,
        kallsyms_per_cpu_symbol_count, //unsigned long first_address_id,
        kallsyms_num_syms - kallsyms_per_cpu_symbol_count, //unsigned int num_syms
        kallsyms_names_size, //unsigned long names_size,
        kallsyms_first_non_per_cpu_name_pos, //unsigned long first_name_pos,
        &kallsyms_expand_symbol //unsigned int (*decompress_func)(unsigned int off, char *result, size_t maxlen)
    ); 

    if (!modules_head) {
        pr_alert("%s: failed to create lks_module_t\n", MODULE_NAME);
        kfree(kallsyms_name_types);
        return -ENOMEM;
    }    
    modules_tail = modules_head;
    modules_count = 1;
    pr_info("%s: created lks_module_t\n", MODULE_NAME);


    pr_info("%s: creating proc fs entries (.so and .a)\n", MODULE_NAME);
    proc_entry = proc_create("libkallsyms.so", 0777, NULL, &kallsyms_elf_fops);
    proc_entry_rel = proc_create("libkallsyms.a", 0777, NULL, &kallsyms_ar_fops);
    file_size_dyn = elfMaker_calcSize(modules_head, modules_count, ET_DYN);
    file_size_rel = elfMaker_calcSize(modules_head, modules_count, ET_REL);
    if (proc_entry)     proc_set_size(proc_entry, file_size_dyn);
    if (proc_entry_rel) proc_set_size(proc_entry_rel, file_size_rel);
    pr_info("%s: proc fs entries created correctly (.so size=%lu, .a size=%lu)\n", MODULE_NAME, file_size_dyn, file_size_rel);

    //register module notifier
    int ret;
    ret = register_module_notifier(&nb);
    if (ret) {
        pr_alert("%s: failed to register module notifier\n", MODULE_NAME);
        return ret;
    }
    pr_info("%s: module notifier registered\n", MODULE_NAME);

    return 0;
    
}

late_initcall(libkallsyms_init_syms);