/* include/linux/symbiote_hook.h */
#pragma once
#include <linux/ptrace.h>

struct SymbiReg; /* your existing type */

typedef void (*symbi_hook_t)(struct pt_regs *regs,
                             const struct SymbiReg *sreg);


/* Register/unregister the single global hook */
int  symbi_register_hook(symbi_hook_t fn);
void symbi_unregister_hook(symbi_hook_t fn);