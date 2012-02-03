#ifndef __ARCH_FUNCS_H__
#define __ARCH_FUNCS_H__

/* TODO: Make this include arch-agnostic. */
#include "imm/machine.h"
#include "imm/symbol.h"

#include "isa.h"

/*
 * This file contains declarations of arch-specific functions called by the
 * generic code. An arch-specific implementation should implement these.
 */

void
read_code_ss(char *fname);

int
ss_max_inst_lat(de_inst_t *inst);

void
init_isa_ss(void);

int
inst_type(de_inst_t *inst);

int
ss_inst_fu(de_inst_t *inst);

const char *
sym_lookup_name(md_addr_t addr, int exact, enum sym_db_t db);

int
read_opt_ss(int argc, char **argv);

void
create_egraph_ss(void);

#endif /* __ARCH_FUNCS_H__ */
