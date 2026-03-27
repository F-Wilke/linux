// SPDX-License-Identifier: GPL-2.0
#include <linux/compat.h>
#include <linux/errno.h>
#include <linux/sched.h>
#include <linux/sched/mm.h>
#include <linux/syscalls.h>
#include <linux/mm.h>
#include <linux/fs.h>
#include <linux/smp.h>
#include <linux/sem.h>
#include <linux/msg.h>
#include <linux/shm.h>
#include <linux/stat.h>
#include <linux/mman.h>
#include <linux/file.h>
#include <linux/utsname.h>
#include <linux/personality.h>
#include <linux/random.h>
#include <linux/uaccess.h>
#include <linux/elf.h>
#include <linux/hugetlb.h>

#include <asm/elf.h>
#include <asm/ia32.h>

#ifdef CONFIG_SYMBIOTE

struct SymbiReg {
  union {
    uint64_t raw;
    struct {
      uint64_t elevate     : 1; // Bit 0
      uint64_t query       : 1; // Bit 1
      uint64_t int_disable : 1; // Bit 2
      uint64_t debug       : 2; // Bit 3-4
      uint64_t no_smep     : 1; // Bit 5
      uint64_t no_smap     : 1; // Bit 6
      uint64_t toggle_smep : 1; // Bit 7
      uint64_t toggle_smap : 1; // Bit 8
      uint64_t ret         : 1; // Bit 9
      uint64_t fast_lower  : 1; // Bit 10
    };
  };
}__attribute__((packed));

uint64_t symbi_check_elevate(void);
uint64_t symbi_check_elevate(){
  return current->symbiote_elevated;
}

//this is to be called from an elevated process.
__attribute((unused)) __attribute((naked)) int symbi_fast_lower(void) {
    register long int rsp;
    __asm__ __volatile__("mov %%rsp, %0" : "=r" (rsp));
    if (rsp < 0) //we need to be on the user stack 
      return -1;

  current->symbiote_elevated = 0;

    // DO_IRET_LOWER;
    __asm__ __volatile__ ( 
      "cli;" 
      "lea 8(%%rsp), %%rax;" 
      "pushq $0x2b;" 
      "pushq %%rax;" 
      "pushq $0x202;"
      "pushq $0x33;"
      "pushq -8(%%rax);"
      "movq $0x0, %%rax;"
      "wrgsbase %%rax;"
      "iretq;" 
      ::: "memory" 
    ); 

}

void symbi_print_user_reg_state(struct pt_regs * regs){
  printk("IP %#lx\n", regs->ip);
  printk("SP %#lx\n", regs->sp);
  printk("CS %#lx\n", regs->cs);
  printk("SS %#lx\n", regs->ss);
  printk("FG %#lx\n", regs->flags);
  printk("\n");
}

void symbi_query(struct pt_regs* regs){
  int ret = symbi_check_elevate();
  if(ret & 1){
    regs->ss = 0x18;
    regs->cs = 0x10;
  }else{
    BUG_ON(regs->cs != 0x33);
    BUG_ON(regs->ss != 0x2b);
  }
}

void symbi_lower(struct pt_regs* regs, struct SymbiReg* sreg){
  if(current->symbiote_elevated == 1 ){
    current->symbiote_elevated = 0;
  } else{
    printk("Trying to lower non elevated task???\n");
  }

  // User interrupts better be enabled....
  if( (regs->flags & (1<<9)) == 0){
    if(sreg->debug){
      printk("Warning: attempted lowering with user interrupts disabled... enabling!");
    }
    regs->flags = regs->flags | (1<<9);
  }
  // Established at syscall entry.
  BUG_ON(regs->cs != 0x33);
  BUG_ON(regs->ss != 0x2b);
}

// Something is prob broken in my inline assembly, don't know why normal optimization breaks...
void __attribute__((optimize("O0"))) symbi_toggle_nosmap(int direction){
  // 1: disable smap
  // 0: enable smap
  uint64_t cr4;
  uint64_t x86_CR4_SMAP = 1 << 21; // XXX just trying the smap one

  asm volatile("movq %%cr4,%0" : "=r"( cr4 ));
  if(direction){
    cr4 &= ~x86_CR4_SMAP;
  }else{
    cr4 |= x86_CR4_SMAP;
  }
	asm volatile("mov %0,%%cr4": "+r" (cr4) : : "memory");
}

void symbi_toggle_nosmep(int direction){
  // 1: disable smep
  // 0: enable smep
  uint64_t cr4;
  uint64_t x86_CR4_SMEP = 1 << 20;

  /* printk("symbi_toggle_nosmep direction is %d\n", direction); */
  asm volatile("movq %%cr4,%0" : "=r"( cr4 ));
  // When this bit (20) is set, smep is enabled.
  if(direction){
    cr4 &= ~x86_CR4_SMEP;
  }else{
    cr4 |= x86_CR4_SMEP;
  }
	asm volatile("mov %0,%%cr4": "+r" (cr4) : : "memory");

}

void arch_apply_smep_smap(unsigned disable_smep, unsigned disable_smap) {
  symbi_toggle_nosmep(disable_smep);
  symbi_toggle_nosmap(disable_smap);
}


void symbi_elevate(struct pt_regs* regs, struct SymbiReg* sreg){
  // Swing symbiote reg
  if(current->symbiote_elevated == 1 ){
    printk("Already Elevated???\n");
  } else{
    /* printk("setting elevated\n"); */
    current->symbiote_elevated = 1;
  }

  // Modify stack memory used for iret. // x86 specific
  regs->ss = 0x18;
  regs->cs = 0x10;

  // Disable interrupts for user
  if(sreg->int_disable){
    /* printk("setting int disabled\n"); */
    regs->flags= regs->flags & (~(1<<9)); // x86 specific
  }
}

void symbi_debug_entry(struct pt_regs *regs, struct SymbiReg *sreg){
  printk("Elevate Syscall Case: ");
  // What case are we in?
  if(sreg->query){
    printk("Query\n");
  } else if(sreg->elevate){
    printk("Elevate\n");
  } else if(!sreg->elevate){
    printk("Lower\n");
  } else{
    printk("Error\n");
  }

  printk("Debug level is %d", sreg->debug);
  if(sreg->int_disable){
    printk("Return with interrupts disabled\n");
  }

  if(sreg->no_smep){
    printk("Return with SMEP disabled\n");
  } else {
    printk("Return with SMEP enabled\n");
  }

  if(sreg->no_smap){
    printk("Return with SMAP disabled\n");
  } else {
    printk("Return with SMAP enabled\n");
  }

  if(sreg->ret){
    printk("Return using ret instead of iret (switch NYI)\n");
  } else{
    printk("Return using iret instead of ret (switch NYI)\n");
  }

  if(sreg->fast_lower){
    printk("Should not have gotten to syscall on fast lower\n");
    printk("Shortcut this in symbi lib\n");
    while(1);
  }else{
    printk("Return using slow syscall-sysret lower\n");
  }

  printk("Was user elevated? %llx", symbi_check_elevate());
  printk("Syscall passed flags: %#llx\n", sreg->raw);
  printk("db: %x id: %x q: %x e: %x\n", sreg->debug, sreg->int_disable, sreg->query, sreg->elevate);

  printk("fl: %x ret: %x nosmap: %x nosmep: %x\n", sreg->fast_lower, sreg->ret, sreg->no_smap, sreg->no_smep);

  printk("User reg state inbound\n");
  symbi_print_user_reg_state(regs);
}

unsigned long arch_elevate(unsigned long flags){
  struct pt_regs *regs;

  /* local_irq_disable(); */
  struct SymbiReg sreg;
  sreg.raw = flags;

  // User's registers
  regs = (struct pt_regs *)this_cpu_read(cpu_current_top_of_stack) - 1;

  if(sreg.debug){
    symbi_debug_entry(regs, &sreg);
  }

  // Careful with order, obviously only executes first matching.
  if(sreg.query){
    symbi_query(regs);

  } else if(sreg.elevate){
    symbi_elevate(regs, &sreg);
    current->symbiote_disable_smap = sreg.no_smap;
    current->symbiote_disable_smep = sreg.no_smep;
    
  } else if(!sreg.elevate){
    symbi_lower(regs, &sreg);
    current->symbiote_disable_smap = 0;
    current->symbiote_disable_smep = 0;

  } else{
    // NOTE: Unconditional print and return.
    printk("Elevation error: Unexpected input %lx\n", flags);
    symbi_print_user_reg_state(regs);
    return -1;
  }

  if(sreg.toggle_smap){
    symbi_toggle_nosmap(sreg.no_smap);
  }
  if(sreg.toggle_smep){
    symbi_toggle_nosmep(sreg.no_smep);
  }


  if(sreg.debug){
    printk("Elevate bit now %llx", symbi_check_elevate());
    symbi_print_user_reg_state(regs);
    printk("Abt to ret from elevate syscall\n");
  }
  return symbi_check_elevate();
}
#endif

/*
 * Align a virtual address to avoid aliasing in the I$ on AMD F15h.
 */
static unsigned long get_align_mask(struct file *filp)
{
	if (filp && is_file_hugepages(filp))
		return huge_page_mask_align(filp);
	/* handle 32- and 64-bit case with a single conditional */
	if (va_align.flags < 0 || !(va_align.flags & (2 - mmap_is_ia32())))
		return 0;

	if (!(current->flags & PF_RANDOMIZE))
		return 0;

	return va_align.mask;
}

/*
 * To avoid aliasing in the I$ on AMD F15h, the bits defined by the
 * va_align.bits, [12:upper_bit), are set to a random value instead of
 * zeroing them. This random value is computed once per boot. This form
 * of ASLR is known as "per-boot ASLR".
 *
 * To achieve this, the random value is added to the info.align_offset
 * value before calling vm_unmapped_area() or ORed directly to the
 * address.
 */
static unsigned long get_align_bits(void)
{
	return va_align.bits & get_align_mask(NULL);
}

static int __init control_va_addr_alignment(char *str)
{
	/* guard against enabling this on other CPU families */
	if (va_align.flags < 0)
		return 1;

	if (*str == 0)
		return 1;

	if (!strcmp(str, "32"))
		va_align.flags = ALIGN_VA_32;
	else if (!strcmp(str, "64"))
		va_align.flags = ALIGN_VA_64;
	else if (!strcmp(str, "off"))
		va_align.flags = 0;
	else if (!strcmp(str, "on"))
		va_align.flags = ALIGN_VA_32 | ALIGN_VA_64;
	else
		pr_warn("invalid option value: 'align_va_addr=%s'\n", str);

	return 1;
}
__setup("align_va_addr=", control_va_addr_alignment);

SYSCALL_DEFINE6(mmap, unsigned long, addr, unsigned long, len,
		unsigned long, prot, unsigned long, flags,
		unsigned long, fd, unsigned long, off)
{
	if (off & ~PAGE_MASK)
		return -EINVAL;

	return ksys_mmap_pgoff(addr, len, prot, flags, fd, off >> PAGE_SHIFT);
}

static void find_start_end(unsigned long addr, unsigned long flags,
		unsigned long *begin, unsigned long *end)
{
	if (!in_32bit_syscall() && (flags & MAP_32BIT)) {
		/* This is usually used needed to map code in small
		   model, so it needs to be in the first 31bit. Limit
		   it to that.  This means we need to move the
		   unmapped base down for this case. This can give
		   conflicts with the heap, but we assume that glibc
		   malloc knows how to fall back to mmap. Give it 1GB
		   of playground for now. -AK */
		*begin = 0x40000000;
		*end = 0x80000000;
		if (current->flags & PF_RANDOMIZE) {
			*begin = randomize_page(*begin, 0x02000000);
		}
		return;
	}

	*begin	= get_mmap_base(1);
	if (in_32bit_syscall())
		*end = task_size_32bit();
	else
		*end = task_size_64bit(addr > DEFAULT_MAP_WINDOW);
}

static inline unsigned long stack_guard_placement(vm_flags_t vm_flags)
{
	if (vm_flags & VM_SHADOW_STACK)
		return PAGE_SIZE;

	return 0;
}

unsigned long
arch_get_unmapped_area(struct file *filp, unsigned long addr, unsigned long len,
		       unsigned long pgoff, unsigned long flags, vm_flags_t vm_flags)
{
	struct mm_struct *mm = current->mm;
	struct vm_area_struct *vma;
	struct vm_unmapped_area_info info = {};
	unsigned long begin, end;

	if (flags & MAP_FIXED)
		return addr;

	find_start_end(addr, flags, &begin, &end);

	if (len > end)
		return -ENOMEM;

	if (addr) {
		addr = PAGE_ALIGN(addr);
		vma = find_vma(mm, addr);
		if (end - len >= addr &&
		    (!vma || addr + len <= vm_start_gap(vma)))
			return addr;
	}

	info.length = len;
	info.low_limit = begin;
	info.high_limit = end;
	if (!(filp && is_file_hugepages(filp))) {
		info.align_offset = pgoff << PAGE_SHIFT;
		info.start_gap = stack_guard_placement(vm_flags);
	}
	if (filp) {
		info.align_mask = get_align_mask(filp);
		info.align_offset += get_align_bits();
	}

	return vm_unmapped_area(&info);
}

unsigned long
arch_get_unmapped_area_topdown(struct file *filp, unsigned long addr0,
			  unsigned long len, unsigned long pgoff,
			  unsigned long flags, vm_flags_t vm_flags)
{
	struct vm_area_struct *vma;
	struct mm_struct *mm = current->mm;
	unsigned long addr = addr0;
	struct vm_unmapped_area_info info = {};

	/* requested length too big for entire address space */
	if (len > TASK_SIZE)
		return -ENOMEM;

	/* No address checking. See comment at mmap_address_hint_valid() */
	if (flags & MAP_FIXED)
		return addr;

	/* for MAP_32BIT mappings we force the legacy mmap base */
	if (!in_32bit_syscall() && (flags & MAP_32BIT))
		goto bottomup;

	/* requesting a specific address */
	if (addr) {
		addr &= PAGE_MASK;
		if (!mmap_address_hint_valid(addr, len))
			goto get_unmapped_area;

		vma = find_vma(mm, addr);
		if (!vma || addr + len <= vm_start_gap(vma))
			return addr;
	}
get_unmapped_area:

	info.flags = VM_UNMAPPED_AREA_TOPDOWN;
	info.length = len;
	if (!in_32bit_syscall() && (flags & MAP_ABOVE4G))
		info.low_limit = SZ_4G;
	else
		info.low_limit = PAGE_SIZE;

	info.high_limit = get_mmap_base(0);
	if (!(filp && is_file_hugepages(filp))) {
		info.start_gap = stack_guard_placement(vm_flags);
		info.align_offset = pgoff << PAGE_SHIFT;
	}

	/*
	 * If hint address is above DEFAULT_MAP_WINDOW, look for unmapped area
	 * in the full address space.
	 *
	 * !in_32bit_syscall() check to avoid high addresses for x32
	 * (and make it no op on native i386).
	 */
	if (addr > DEFAULT_MAP_WINDOW && !in_32bit_syscall())
		info.high_limit += TASK_SIZE_MAX - DEFAULT_MAP_WINDOW;

	if (filp) {
		info.align_mask = get_align_mask(filp);
		info.align_offset += get_align_bits();
	}
	addr = vm_unmapped_area(&info);
	if (!(addr & ~PAGE_MASK))
		return addr;
	VM_BUG_ON(addr != -ENOMEM);

bottomup:
	/*
	 * A failed mmap() very likely causes application failure,
	 * so fall back to the bottom-up function here. This scenario
	 * can happen with large stack limits and large mmap()
	 * allocations.
	 */
	return arch_get_unmapped_area(filp, addr0, len, pgoff, flags, 0);
}
