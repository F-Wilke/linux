/* SPDX-License-Identifier: GPL-2.0 */
/*
 * symbi_sched.S - Voluntary context switch support for elevated CPCS tasks.
 *
 * An elevated Constant Privilege Constant Stack (CPCS) task runs at CPL0
 * on its user-mode stack.  Any path reaching __schedule() would crash:
 *
 *   1. __schedule() is entered on the user stack.
 *   2. switch_mm_irqs_off() switches CR3 -- the user stack is unmapped.
 *   3. Fault.
 *
 * Fix: __schedule() detects this case and calls symbi_voluntary_cs_asm()
 * (this file) before any lock or CR3 change.  This function:
 *
 *   1. Saves the user RSP (which holds __schedule__()'s return address) into
 *	callee-saved registers r13 on entry.
 *   2. Switches to the SP0 kernel stack for this CPU.
 *   3. Calls schedule() from the kernel stack.  The elevated check in
 *      __schedule() is false (kernel RSP has MSB set), so the full
 *      scheduler runs including context switch via __switch_to_asm, which
 *      saves/restores r12-r15 as part of normal kernel thread switching.
 *   4. On reschedule: switches RSP back to the user stack (now mapped again),
 *	and executes ret -- returning normally into __schedule() which
 *	then returns to the elevated task's call chain on the user stack.
 *
 * Design: modelled as a kernel thread context switch, with symmetric pivots.
 *   Switch-out: we start in a non-traditional setting -- context switch
 *     initiated on the elevated task's user stack -- and pivot to SP0 to
 *     issue a real call to schedule().  From that point the kernel thread
 *     switch path is completely standard: __switch_to_asm saves r12-r15/
 *     rbx/rbp and thread.sp on SP0, exactly as for any kernel thread.
 *     We use r13 to save the user stack rsp value.	
 *   Switch-in: the symmetric pivot -- schedule() returns on SP0 with
 *     r12-r15 restored  pivot back to the user stack using value saved in r13
 *     and ret -- returning into __schedule__()'s epilogue with RSP in
 *     exactly the state its compiler-generated epilogue expects.
 *   No iretq, no labels, no trampoline, no special objtool annotations.
 */

#include <linux/linkage.h>
#include <asm/nospec-branch.h>
#include <asm/percpu.h>

SYM_FUNC_START(symbi_voluntary_cs_asm)
	/*
	 * On entry: RSP points to the return address pushed by
	 * __schedule__()'s "call symbi_voluntary_cs_asm".  Save it so we
	 * can restore it before ret.  r13 is callee-saved: schedule()
	 * (and __switch_to_asm within it) will preserve it across any
	 * context switch and reschedule.
	 * RFLAGS: not saved. ABI treats them as caller clobbered, and 
	 *         __schedule() uses local_irq_enable() (not irqrestore),
	 *         guaranteeing IF=1 on return regardless of entry state.
	 */
	movq	%rsp, %r13		/* r13 = user RSP (-> return addr) */

	/* Switch from user stack to the SP0 kernel stack for this CPU. */
	movq	PER_CPU_VAR(cpu_current_top_of_stack), %rsp

	/*
	 * Call schedule() from the kernel stack.  The elevated CPCS check
	 * in __schedule() is false (kernel RSP: MSB set -> signed-negative),
	 * so the full scheduler runs without recursing into us.
	 */
	call	schedule

	/*
	 * Restore the user RSP (now pointing at __schedule__()'s return
	 * address on the mapped user stack) and return normally.
	 * __schedule__() continues with its return; epilogue, unwinding
	 * back to the elevated task's call chain.
	 */
	movq	%r13, %rsp
	RET    // use RET macro to be compliant with linux ret security mitigations
SYM_FUNC_END(symbi_voluntary_cs_asm)
