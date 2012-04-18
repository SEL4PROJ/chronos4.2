/*******************************************************************************
 *
 * Chronos: A Timing Analyzer for Embedded Software
 * =============================================================================
 * http://www.comp.nus.edu.sg/~rpembed/chronos/
 *
 * Copyright (C) 2005 Xianfeng Li
 *
 * This program is free software; you can redistribute it and/or modify it under
 * the terms of the GNU General Public License as published by the Free Software
 * Foundation; either version 2, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public License for more
 * details.
 *
 * $Id: ss_readfile.c,v 1.2 2006/06/24 08:55:06 lixianfe Exp $
 *
 ******************************************************************************/

#include <stdio.h>
#include <errno.h>
#include <stdint.h>
#include "ecoff.h"
#include "symbol.h"
#include "../cfg.h"
#include "../common.h"
#include "../arch_funcs.h"
#include "machine.h"
#include "../mem_value.h"

// variables from readfile.c
extern prog_t	prog;
addr_t		*procs_addr; 
int		num_procs;



/* program text (code) segment base */
md_addr_t	ld_text_base = 0;
/* program text (code) size in bytes */
unsigned int	ld_text_size = 0;
unsigned	text_entry;
unsigned	text_offset;
extern struct	sym_sym_t **sym_textsyms;
extern int	sym_ntextsyms;


struct imm_file {
    /* The full text of the file. */
    char *file_contents;
    int file_size;

    int num_symbols;

    /* Number of instructions in the file. */
    int num_instructions;

    /* An array of pointers to the start of each line of the file. */
    char **line_pointers;

    /* Entry point for analysis. */
    unsigned long entry_point;
};

struct imm_file imm_file;


// tell from the name of the function whether it is a library function, if so, it
// means no subsequent user functions
#if 0
static int
is_lib_func(char *func_name)
{
    if ((strcmp(func_name, "__do_global_dtors") == 0)
	|| (strcmp(func_name, "__libc_init") == 0))
	return 1;
    else
	return 0;
}
#endif


// locate the start & end addr of the user code by excluding library functions,
// in addition, locate the main() entrance
#if 0
static void
lookup_addr(char *fname)
{
    int			i, size = 0, max_num_procs = 16;
    struct sym_sym_t	*sym;
    FILE *f = fopen(fname, "r");
    
    // TODO: save start & end addr...

    sym_loadsyms(fname, 1);
    //sym_dumptextsyms(stdout, 1);
    prog.start_addr = sym_textsyms[0]->addr;
    procs_addr = (md_addr_t *) calloc(max_num_procs, sizeof(md_addr_t));
    for (i=0; i < sym_ntextsyms; i++) {
	sym = sym_textsyms[i];
	if (is_lib_func(sym->name))
	    break;
	if (strcmp(sym->name, "main") == 0)
	    prog.main_addr = sym->addr;
	if (num_procs >= max_num_procs) {
	    max_num_procs *= 2;
	    procs_addr = (md_addr_t *) realloc(procs_addr,
		    max_num_procs * sizeof(md_addr_t));
	}
	procs_addr[num_procs++] = sym->addr;
	prog.code_size += sym->size;
    }
    prog.end_addr = prog.start_addr + prog.code_size;
}
#endif



// locate & read the text header of the program
#if 0
static void
read_text_head(FILE *fp)
{
    char line[1024];
    md_init_decoder();
    for (i=0; i<fhdr.f_nscns; i++) {
	fread(&shdr, sizeof(shdr), 1, fp);
	if (shdr.s_flags != ECOFF_STYP_TEXT)
	    continue;
	text_size = shdr.s_size;
	text_offset = shdr.s_scnptr;
	text_entry = shdr.s_vaddr;
/* amount of tail padding added to all loaded text segments */
#define TEXT_TAIL_PADDING 128

	ld_text_size = ((shdr.s_vaddr + shdr.s_size) - MD_TEXT_BASE) 
	    + TEXT_TAIL_PADDING;
    }
    text_offset += prog.start_addr - text_entry;
    ld_text_base = MD_TEXT_BASE;
}
#endif



static void
read_imm_file(char *fname)
{
    FILE *f;
    off_t size, read;
    int ret;
    char *buf;
    f = fopen(fname, "r");

    /* Determine file size. */
    fseeko(f, 0, SEEK_END);
    size = ftello(f);
    fseeko(f, 0, SEEK_SET);

    imm_file.file_contents = malloc(size + 1);
    assert(imm_file.file_contents != NULL);

    buf = imm_file.file_contents;
    read = 0;
    while (read < size) {
        ret = fread(buf + read, 1, size - read, f);
        if (ret < 0) {
            printf("read error: %s\n", strerror(errno));
            abort();
        }
        if (ret == 0) {
            printf("short read\n");
            abort();
        }
        read += ret;
    }
    imm_file.file_contents[size] = '\0';

    assert(read == size);

    fclose(f);
    imm_file.file_size = size;
}

static
void split_instruction_lines(void)
{
    /* Count number of instructions. */
    int num_instructions = 0;
    char *p = imm_file.file_contents;
    while (p < imm_file.file_contents + imm_file.file_size) {
        if (*p == '\n') {
            p++;
            continue;
        }

        char *s = p;
        while (s < imm_file.file_contents + imm_file.file_size && *s != '\n')
            s++;

        if (*p == 'i') {
            num_instructions++;
        }
        p = s + 1;
    }

    /* Now allocate memory for instructions, and parse. */
    imm_file.line_pointers = malloc(sizeof(char*) * num_instructions);
    assert(imm_file.line_pointers != NULL);

    p = imm_file.file_contents;
    int i = 0;
    while (p < imm_file.file_contents + imm_file.file_size) {
        if (*p == '\n') {
            p++;
            continue;
        }

        char *s = p;
        while (s < imm_file.file_contents + imm_file.file_size &&
                *s != '\n')
            s++;
        if (*s == '\n')
            *s = '\0';

        if (*p == 'i') { /* Instruction. */
            imm_file.line_pointers[i++] = p + 2;
        } else if (*p == 'e') { /* Entry point. */
            sscanf(p + 2, "%lx", &imm_file.entry_point);
        }

        p = s + 1;
    }

    assert(i == num_instructions);

    imm_file.num_instructions = num_instructions;

    printf("Read %d instructions\n", num_instructions);
}

static const char *next_token(const char *s) {
    // Advance to whitespace.
    while (*s != '\0' && *s != ' ')
        s++;

    if (*s == '\0')
        return NULL;

    // Advance to non-whitespace.
    while (*s != '\0' && *s == ' ')
        s++;

    if (*s == '\0')
        return NULL;

    return s;
}

static unsigned int
read_hex_u32(const char *s)
{
#if 0
    int ret;
    unsigned int val;
    assert(s[0] == '0');
    assert(s[1] == 'x' || s[1] == 'X');
    assert(isdigit(s[2]) || (toupper(s[2]) >= 'A' && toupper(s[2]) <= 'F'));
    ret = sscanf(s+2, "%lx", &val);
    assert(ret == 1);
    return val;
#else
    return strtol(s, NULL, 16);
#endif
}

static const struct {
    const char *s;
    int reg_no;
} regname_mapping[] = {
    { "r0",  MD_REG_R0  },
    { "r1",  MD_REG_R1  },
    { "r2",  MD_REG_R2  },
    { "r3",  MD_REG_R3  },
    { "r4",  MD_REG_R4  },
    { "r5",  MD_REG_R5  },
    { "r6",  MD_REG_R6  },
    { "r7",  MD_REG_R7  },
    { "r8",  MD_REG_R8  },
    { "r9",  MD_REG_R9  },
    { "r10", MD_REG_R10 },
    { "sl",  MD_REG_R10 },
    { "r11", MD_REG_R11 },
    { "fp",  MD_REG_R11 },
    { "r12", MD_REG_R12 },
    { "ip",  MD_REG_R12 },
    { "r13", MD_REG_R13 },
    { "sp",  MD_REG_R13 },
    { "r14", MD_REG_R14 },
    { "lr",  MD_REG_R14 },
    { "r15", MD_REG_R15 },
    { "pc",  MD_REG_R15 },
};

int
regstr_to_regnum(const char *s) {
    int i;
    for (i = 0; i < sizeof(regname_mapping)/sizeof(regname_mapping[0]); i++) {
        if (strcmp(s, regname_mapping[i].s) == 0)
            return regname_mapping[i].reg_no;
    }
    return -1;
}

const char*
regnum_to_regstr(int reg_num) {
    int i;
    for (i = 0; i < sizeof(regname_mapping)/sizeof(regname_mapping[0]); i++) {
        if (reg_num == regname_mapping[i].reg_no)
            return regname_mapping[i].s;
    }
    return NULL;
}

static int
take_condition(char *cond_str) {
    if (*cond_str == '_')
        return COND_MIN;
    if (strcmp(cond_str, "eq") == 0)
        return COND_EQ;
    else if (strcmp(cond_str, "ne")== 0)
        return COND_NE;
    else if (strcmp(cond_str, "cs") == 0)
        return COND_CS;
    else if (strcmp(cond_str, "hs") == 0)
        return COND_HS;
    else if (strcmp(cond_str, "cc") == 0)
        return COND_CC;
    else if (strcmp(cond_str, "lo") == 0)
        return COND_LO;
    else if (strcmp(cond_str, "mi") == 0)
        return COND_MI;
    else if (strcmp(cond_str, "pl") == 0)
        return COND_PL;
    else if (strcmp(cond_str, "vs") == 0)
        return COND_VS;
    else if (strcmp(cond_str, "vc") == 0)
        return COND_VC;
    else if (strcmp(cond_str, "hi") == 0)
        return COND_HI;
    else if (strcmp(cond_str, "ls") == 0)
        return COND_LS;
    else if (strcmp(cond_str, "ge") == 0)
        return COND_GE;
    else if (strcmp(cond_str, "lt") == 0)
        return COND_LT;
    else if (strcmp(cond_str, "gt") == 0)
        return COND_GT;
    else if (strcmp(cond_str, "le") == 0)
        return COND_LE;
    else if (strcmp(cond_str, "al") == 0)
        return COND_AL;
    printf("Can't process the cond %s.\n", cond_str);
    exit(-1);
    return COND_MAX;
}

// Returns the number of instructions generated.
static void
decode_instruction_line(const char *line, prog_t *prog)
{
    int ret;
    const char *s = line;
    char tmpbuf[20];
    char mnemonic[10];
    char condcode[10];
    char setstatus[10];
    int num_outedges = 0;
    int has_fallthrough = 0;
    static int cond_count = 0;

    // Ensure we have space for another 128 instructions (worst-case - should
    // improve how we handle this).
    if (prog->num_inst_alloc - prog->num_inst < 128) {
        if (prog->num_inst_alloc == 0) {
            prog->num_inst_alloc = 128;
        } else {
            prog->num_inst_alloc *= 2;
        }
        prog->code = realloc(prog->code,
                prog->num_inst_alloc * sizeof(*prog->code));
        assert(prog->code != NULL);
    }

    de_inst_t *inst = &prog->code[prog->num_inst++];
    memset(inst, 0, sizeof(*inst));

    // Read address.
    inst->addr = read_hex_u32(s);
    s = next_token(s);

    // Read size.
    ret = sscanf(s, "%d", &inst->size);
    assert(ret == 1);
    s = next_token(s);

    // startbb/contbb. Ignore for now.
    s = next_token(s);
    if (strncmp(s, "startbb", 7) == 0)
        cond_count = 0;
    else
        ++cond_count;

    // Next word should be "edges"
    assert(strncmp("edges ", s, 6) == 0);
    s = next_token(s);

    // Read in edges.
    while (1) {
        if (strncmp("call ", s, 5) == 0) {
            /* Read address. */
            uint32_t addr;
            s = next_token(s);
            addr = strtol(s, NULL, 16);
            if (addr != inst->addr + 4) {
                inst->num_targets++;
                inst->targets = realloc(inst->targets,
                        sizeof(*inst->targets) * inst->num_targets);
                inst->targets[inst->num_targets-1] = addr;
            } else {
                has_fallthrough = 1;
            }
            inst->is_call = 1;
            num_outedges++;
            if (addr == preemption_addr) 
                inst->preemption = 1;
        } else if (strncmp("tailcall ", s, 9) == 0) {
            /* Read address. */
            uint32_t addr;
            s = next_token(s);
            addr = strtol(s, NULL, 16);

            /* tailcalls always leave the function. */
            inst->num_targets++;
            inst->targets = realloc(inst->targets,
                    sizeof(*inst->targets) * inst->num_targets);
            inst->targets[inst->num_targets-1] = addr;
            inst->is_call = 1;
            inst->tailcall = 1;
            num_outedges++;
        } else if (strncmp("callret ", s, 8) == 0) {
            s = next_token(s);
            /* Read address. */
        } else if (strncmp("next ", s, 5) == 0) {
            /* Read address. */
            uint32_t addr;
            s = next_token(s);
            addr = strtol(s, NULL, 16);
            if (addr != inst->addr + 4) {
                inst->num_targets++;
                inst->targets = realloc(inst->targets,
                        sizeof(*inst->targets) * inst->num_targets);
                inst->targets[inst->num_targets-1] = addr;
            } else {
                has_fallthrough = 1;
            }
            num_outedges++;
        } else if (strncmp("return ", s, 7) == 0) {
            inst->is_ret = 1;
            num_outedges++;
        } else if (strncmp("end", s, 3) == 0) {
            s = next_token(s);
            break;
        } else {
            assert(!"Unknown edge type");
            abort();
        }
        s = next_token(s);
    }

    // Read mnemonic.
    ret = sscanf(s, "%s", mnemonic);
    assert(ret == 1);
    s = next_token(s);

    // Read condition.
    sscanf(s, "%s", condcode);
    assert(ret == 1);
    s = next_token(s);
    inst->conditional = (*condcode == '_')?0:1;
    inst->condition = take_condition(condcode);

    // Stop. If we have no fallthrough edge, then the conditional has been
    // revoked. This could occur when a CFG is pruned of dead edges, and the
    // fallthrough edge would normally lead to an error condition (infinite
    // loop) which gets purged from the CFG.
    if (!has_fallthrough) {
        inst->conditional = 0;
    }

    // Read setcc bit.
    sscanf(s, "%s", setstatus);
    assert(ret == 1);
    s = next_token(s);
    inst->s_bit = *setstatus == 's'?1:0;
        

    // We can decode the instruction from that information.
    inst->op_enum = opcode_str_to_enum(mnemonic, condcode, setstatus);

    // Read input/output registers.
    inst->in = NULL;
    inst->out = NULL;
    inst->num_in = 0;
    inst->num_out = 0;
    while (s != NULL) {
        if (strncmp(s, "input ", 6) == 0) {
            s = next_token(s);
            sscanf(s, "%s", tmpbuf);

            int reg_no = regstr_to_regnum(tmpbuf);
            if (reg_no != -1) {
                    inst->in = realloc(inst->in, sizeof(*inst->in) * (inst->num_in+1));
                    inst->in[inst->num_in] = reg_no;
                    inst->num_in++;
            } else if (*tmpbuf == '#') {
                inst->imm = atoi(tmpbuf + 1);
                inst->has_imm = 1;
            }
            else if (strcmp(tmpbuf, "memory") == 0) {
                inst->in = realloc(inst->in, sizeof(*inst->in) * (inst->num_in+1));
                inst->in[inst->num_in] = ARM_MEM_REG;
                inst->num_in++;
            }
        } else if (strncmp(s, "output ", 7) == 0) {
            s = next_token(s);
            sscanf(s, "%s", tmpbuf);

            int reg_no = regstr_to_regnum(tmpbuf);
            if (reg_no == -1) {
                if (strcmp(tmpbuf, "memory") == 0) {
                    reg_no = ARM_MEM_REG;
                    inst->out = realloc(inst->out, sizeof(*inst->out) * (inst->num_out+1));
                    inst->out[inst->num_out] = reg_no;
                    inst->num_out++;
                }
                else if (strcmp(tmpbuf, "writeback") == 0) {
                    inst->writeback = 1;
                }
                else if (strcmp(tmpbuf, "cc") != 0) {
                    printf("%s\n", tmpbuf);
                    assert(0);
                }
            }
            else {
                inst->out = realloc(inst->out, sizeof(*inst->out) * (inst->num_out+1));
                inst->out[inst->num_out] = reg_no;
                inst->num_out++;
            }
        } else if (strncmp(s, "shift ", 6) == 0) {
            s = next_token(s);
            sscanf(s, "%s", tmpbuf);

            int reg_no = regstr_to_regnum(tmpbuf);
            if (reg_no != -1) {
                inst->shift_val = reg_no;
                inst->last_shift = SHIFT_BY_REG;
            } else if (*tmpbuf == '#') {
                inst->shift_val = atoi(tmpbuf + 1);
                inst->last_shift = SHIFT_BY_IMM;
            }
            else
                assert(0);

            s = next_token(s);
            sscanf(s, "%s", tmpbuf);
            if (strcmp(tmpbuf, "lsl") == 0)
                inst->shift_mode = SHIFT_MODE_LSL;
            else if (strcmp(tmpbuf, "lsr") == 0)
                inst->shift_mode = SHIFT_MODE_LSR;
            else if (strcmp(tmpbuf, "asr") == 0)
                inst->shift_mode = SHIFT_MODE_ASR;
            else if (strcmp(tmpbuf, "ror") == 0)
                inst->shift_mode = SHIFT_MODE_ROR;
            else if (strcmp(tmpbuf, "rrx") == 0)
                inst->shift_mode = SHIFT_MODE_RRX;
            else {
                printf("Unknown shift mode %s\n", tmpbuf);
                assert(0);
            }
        } 
        else {
            break;
/*
            fprintf(stderr, "Invalid token on line: %s\n", s);
            abort();
*/
        }
        s = next_token(s);
    }

    unsigned inst_value = 0;
    if (s) 
        sscanf(s, "%x", &inst_value);

    // if movt and movw are consecutive, let the latter one be mov
    if (inst->has_imm) {
        if (inst->op_enum == MOVT) {
            int i = prog->num_inst - 2, cnt = 0;
            while (i > 0 && cnt < cond_count) {
                de_inst_t *prev_inst = &prog->code[i];
                if (prev_inst->op_enum == MOVW && inst->out[0] == prev_inst->out[0] 
                    && prev_inst->has_imm) 
                {
                    inst->imm = (inst->imm << 16) | prev_inst->imm;
                    inst->op_enum = MOV;
                    inst->num_in = 0;
                    inst->in = NULL;
                    //printf("0x%x movt r%d, 0x%x\n", inst->addr, inst->out[0], inst->imm);
                    break;
                }
                --i; ++cnt;
            }
        }
        else if (inst->op_enum == MOVW) {
            int i = prog->num_inst - 2, cnt = 0;
            while (i > 0 && cnt < cond_count) {
                de_inst_t *prev_inst = &prog->code[i];
                if (prev_inst->op_enum == MOVT && inst->out[0] == prev_inst->out[0]
                    && prev_inst->has_imm)
                {
                    inst->imm = inst->imm | (prev_inst->imm << 16);
                    inst->op_enum = MOV;
                    inst->num_in = 0;
                    inst->in = NULL;
                    //printf("0x%x movw r%d, 0x%x\n", inst->addr, inst->out[0], inst->imm);
                    break;
                }
                --i; ++cnt;
            }
        } 
    }

    if (inst->op_enum == NA) {
        global_memory_add(inst->addr, inst_value);
    }
 
    // raw asm instruction
    if (s) {
        s = next_token(s);
    }

    if (inst->op_enum == STM_U || inst->op_enum == LDM_L) {
        if (strncmp(s+4, "ia", 2) == 0)
            inst->offset_addr_mode = IA_ADDRESS_MODE;
        else if (strncmp(s+4, "ib", 2) == 0)
            inst->offset_addr_mode = IB_ADDRESS_MODE;
        else if (strncmp(s+4, "da", 2) == 0)
            inst->offset_addr_mode = DA_ADDRESS_MODE;
        else if (strncmp(s+4, "db", 2) == 0)
            inst->offset_addr_mode = DB_ADDRESS_MODE;
    }
    else if (inst->op_enum == LDR_L || inst->op_enum == LDR_H ||
             inst->op_enum == LDR_BL || inst->op_enum == STR_U ||
             inst->op_enum == STR_H || inst->op_enum == STR_B) 
    {
        char *p = strchr(s, ']');
        assert(p);
        char *q = strchr(p + 1, ',');
        if (q) 
            inst->offset_addr_mode = POST_INDEXED;
        else 
            inst->offset_addr_mode = strchr(p + 1, '!')?PRE_INDEXED:IMM_INDEXED;
    }

    // If we just did a tail call, the next instruction should be a fake
    // return.
    if (inst->tailcall) {
        inst = &prog->code[prog->num_inst++];
        memset(inst, 0, sizeof(*inst));

        inst->addr = inst[-1].addr; // Eewww..
        inst->size = 0;
        inst->is_ret = 1;
        inst->op_enum = OP_NA;
    }
}

// read the obj code, decode the inst and store them in prog
void
read_code_ss(char *fname)
{
    global_memory_init();

    sym_loadsyms(fname);
    read_imm_file(fname);
    split_instruction_lines();

    prog.num_inst = 0;
    prog.num_inst_alloc = 0;
    prog.code = NULL;

    /* Decode all instructions. */
    int i;
    for (i = 0; i < imm_file.num_instructions; i++) {
        decode_instruction_line(imm_file.line_pointers[i], &prog);
    }

    prog.main_addr = imm_file.entry_point;

    printf("Decoded all instructions\n");
}

