#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "../common.h"
#include "../isa.h"
#include "../arch_funcs.h"
#include "machine.h"



extern isa_t	*isa;
extern int	num_isa;


// initiate SimpleScalar ISA info by reading its machine.def file
void
init_isa_ss(void)
{
    int i, len;
    num_isa = OP_MAX;

    isa = (isa_t *) calloc(num_isa, sizeof(isa_t));
    CHECK_MEM(isa);
    for (i = 0; i < num_isa; i++) {
        isa[i].opcode = i;
        if (md_op2name[i] != NULL) {
            len = strlen(md_op2name[i]) + 1;
            isa[i].name = (char *) malloc(len);
            CHECK_MEM(isa[i].name);
            strcpy(isa[i].name, md_op2name[i]);
        }
    }
}

// return (decoded) instruction type
int
inst_type(de_inst_t *inst)
{
    if (inst->is_ret)
        return INST_RET;

    if (inst->is_call)
        return INST_CALL;

    if (inst->num_targets > 0)
        return inst->conditional ? INST_COND : INST_UNCOND;

    int i = inst->op_enum;
    if (md_op2flags[i] & F_ICOMP)
        return INST_ICOMP;
    else if (md_op2flags[i] & F_FCOMP)
        return INST_FCOMP;
    else if (md_op2flags[i] & F_LOAD)
        return INST_LOAD;
    else if (md_op2flags[i] & F_STORE)
        return INST_STORE;
    else if (md_op2flags[i] & F_COND)
        return INST_COND;
    else if (md_op2flags[i] & F_CALL)
        return INST_CALL;
#if 0
    else if ((md_op2flags[i] & (F_CTRL|F_UNCOND|F_DIRJMP))
            == (F_CTRL|F_UNCOND|F_DIRJMP))
        return INST_NOP;
#endif
    else if ((md_op2flags[i] & (F_CTRL|F_DIRJMP))
            == (F_CTRL|F_DIRJMP))
        return INST_NOP; // This is a branch with is never taken.
    else if ((md_op2flags[i] & (F_CTRL|F_UNCOND|F_INDIRJMP))
            == (F_CTRL|F_UNCOND|F_INDIRJMP))
        return INST_RET;
    else if (md_op2flags[i] & F_TRAP)
        return INST_TRAP;
    else if (md_op2flags[i] == NA)
        return INST_NOP;
    else {
        fprintf(stderr, "unidentified instruction type - 0x%x (%s at 0x%lx)\n",
                md_op2flags[i], isa[i].name, (long)inst->addr);
        exit(1);
    }
}

struct opcode_conv_t {
    const char *mnemonic;
    unsigned int s:1;
    enum md_opcode opcode;
};

static const struct opcode_conv_t opcodes[] = {
    { "nop",  0, NA },
    { "b",    0, BR },
    { "bl",   0, BRL },
    { "swi",  0, SWI },
    { "and",  0, AND },
    { "and",  1, ANDS },
    { "eor",  0, EOR },
    { "eor",  1, EORS },
    { "sub",  0, SUB },
    { "sub",  1, SUBS },
    { "rsb",  0, RSB },
    { "rsb",  1, RSBS },
    { "add",  0, ADD },
    { "add",  1, ADDS },
    { "adc",  0, ADC },
    { "adc",  1, ADCS },
    { "sbc",  0, SBC },
    { "sbc",  1, SBCS },
    { "rsc",  0, RSC },
    { "rsc",  1, RSCS },
    { "tst",  0, TSTS },
    { "teq",  0, TEQS },
    { "cmp",  0, CMPS },
    { "cmn",  0, CMNS },
    { "orr",  0, ORR },
    { "orr",  1, ORRS },
    { "mov",  0, MOV },
    { "mov",  1, MOVS },
    { "movw", 0, MOVW },
    { "movt", 0, MOVT },
    { "bic",  0, BIC },
    { "bic",  1, BICS },
    { "mvn",  0, MVN },
    { "mvn",  1, MVNS },
    { "lsl",  0, LSL },
    { "lsl",  1, LSLS },
    { "lsr",  0, LSR },
    { "lsr",  1, LSRS },
    { "asr",  0, ASR },
    { "asr",  1, ASRS },
    { "swp",  0, SWP },
    { "msr",  0, MSR_CPSR },
    { "mrs",  0, MRSI_CPSR },
    { "ldr",  0, LDR_L },
    { "ldrh", 0, LDR_H },
    { "ldrb", 0, LDR_BL },
    { "str",  0, STR_U },
    { "strh", 0, STR_H },
    { "strb", 0, STR_B },
    { "ldm",  0, LDM_L },
    { "stm",  0, STM_U },
    { "bx",   0, BX },
    { "blx",  0, BLX },
    { "mcr",  0, MCR },
    { "mrc",  0, MRC },
    { "dsb",  0, DSB },
    { "isb",  0, ISB },
    { "clz",  0, CLZ },
    { "bfi",  0, BFI },
    { "ubfx", 0, UBFX },
    { "uxtb", 0, UXTB },
};

int
opcode_str_to_enum(const char *mnemonic, const char *cc, const char *s)
{
    int i;
    unsigned int s_bit = 0;

    if (*s == 's') {
        s_bit = 1;
    } else {
        assert(*s == '_');
    }

    for (i = 0; i < sizeof(opcodes)/sizeof(opcodes[0]); i++) {
        const struct opcode_conv_t *op = &opcodes[i];
        if (strcmp(mnemonic, op->mnemonic) == 0 && s_bit == op->s) {
            return op->opcode;
        }
    }

    fprintf(stderr, "Unknown instruction: %s\n", mnemonic);
    return 0;
}

#if 0
void
decode_inst(de_inst_t *de_inst, const char *s)
{
    int	    op, type, offset, i, incr;
    int	    in[3], out[2];
    int	    num_in = 0, num_out = 0;
    char* inst_format;
    enum md_opcode mop;

    // get inst opcode and from the opcode get its type info
    MD_SET_OPCODE(mop, inst);
    op = MD_OP_ENUM(mop);
    de_inst->op_enum = 0x1; // One opcode to rule them all.
    de_inst->size = sizeof(md_inst_t);
    type = isa[op].type;

    /* Get the instruction format */
    inst_format = MD_OP_FORMAT(op);

    /* sudiptac ::: Set the immediate field. Needed for 
     * address analysis */
    while(*inst_format) {
        switch(*inst_format)
        {
            case 'o':
            case 'i':
#ifdef _DEBUG
                printf("Immediate value = %d\n", IMM);
#endif
                de_inst->imm = IMM;
                break;
            case 'H':
#ifdef _DEBUG
                printf("Immediate value = %d\n", SHAMT);
#endif
                de_inst->imm = SHAMT;
                break;
            case 'u':
#ifdef _DEBUG
                printf("Immediate value = %u\n", UIMM);
#endif
                de_inst->imm = UIMM;
                break;
            case 'U':
#ifdef _DEBUG
                printf("Immediate value = %d\n", UIMM);
#endif
                de_inst->imm = UIMM;
                break;
            default:
                /* Do nothing */	 
                ;
                /* sudiptac: Default code may need to be 
                 * modified */
            }
        inst_format++;
    }

    // if inst is a ctr transfer, compute the target addr
    if (type == INST_COND) {
        offset = ((int)((short)(inst.b & 0xffff))) << 2;
        de_inst->target = de_inst->addr + sizeof(md_inst_t) + offset;
    } else if ((type == INST_UNCOND) || (type == INST_CALL)) {
        offset = (inst.b & 0x3ffffff) << 2;
        de_inst->target = (de_inst->addr & 0xf0000000) | offset;
    }

    // decode the input/output info
    switch(op) {
#define DEFINST(OP, MSK, NAME, FMT, FU, CLASS, O1,O2, IN1, IN2, IN3) \
    case OP: \
        in[0] = IN1; in[1] = IN2; in[2] = IN3; \
        out[0] = O1; out[1] = O2; \
        break;
#include "machine.def"
#undef DEFINST
    default:
        in[0] = in[1] = in[2] = NA;
        out[0] = out[1] = NA;
    }
    incr = 0;
    for (i = 0; i <= 2; i++) {
        if (in[i] != NA) {
        num_in++;
            //incr = 1;
        }
    }
    incr = 0;
    for (i = 0; i <= 1; i++) {
        if (out[i] != NA) { 
        num_out++;
            //incr = 1;
        }
    }
    if(!strcmp(isa[op].name, "lb") || !strcmp(isa[op].name, "lh") ||
        !strcmp(isa[op].name, "lw") || !strcmp(isa[op].name, "lhu") ||
        !strcmp(isa[op].name, "lwl") || !strcmp(isa[op].name, "lwr") ||
        !strcmp(isa[op].name, "l.d") || !strcmp(isa[op].name, "l.s"))
    {
        if(in[2] != NA)
            num_in = 2;
        else
            num_in = 1;
    }
    if(!strcmp(isa[op].name, "sb") || !strcmp(isa[op].name, "sh") ||
        !strcmp(isa[op].name, "sw") || !strcmp(isa[op].name, "swl") ||
        !strcmp(isa[op].name, "swr") || !strcmp(isa[op].name, "s.d") ||
        !strcmp(isa[op].name, "s.s"))
    {
        if(in[2] != NA)
            num_in = 3;
        else
            num_in = 2;
    }

    de_inst->in = (int *) calloc(num_in, sizeof(int));
    CHECK_MEM(de_inst->in);
    de_inst->num_in = 0;
    if(!strcmp(isa[op].name, "lb") || !strcmp(isa[op].name, "lh") ||
        !strcmp(isa[op].name, "lw") || !strcmp(isa[op].name, "lhu") ||
        !strcmp(isa[op].name, "lwl") || !strcmp(isa[op].name, "lwr") ||
        !strcmp(isa[op].name, "l.d") || !strcmp(isa[op].name, "l.s"))
    {	  
		for (i = 0; i < num_in; i++) 
		  de_inst->in[de_inst->num_in++] = in[i+1];
	 }
	 else if(!strcmp(isa[op].name, "sb") || !strcmp(isa[op].name, "sh") ||
		  !strcmp(isa[op].name, "sw") || !strcmp(isa[op].name, "swl") ||
		  !strcmp(isa[op].name, "swr") || !strcmp(isa[op].name, "s.d") || 
		  !strcmp(isa[op].name, "s.s"))
	 { 	  
		for (i = 0; i < num_in; i++) 
		  de_inst->in[de_inst->num_in++] = in[i];
	 }	  
	 else
	 {
		for (i = 0; i <= 2; i++) {
		  //if (in[i] != NA)
			de_inst->in[de_inst->num_in++] = in[i];
		}
	 }
    de_inst->out = (int *) calloc(num_out, sizeof(int));
    CHECK_MEM(de_inst->out);
    de_inst->num_out = 0;
    for (i = 0; i <= 1; i++) {
		//if (out[i] != NA)
		  de_inst->out[de_inst->num_out++] = out[i];
    }
}
#endif



int
ss_inst_fu(de_inst_t *inst)
{
    return MD_OP_FUCLASS(inst->op_enum);
}



extern range_t fu_lat[];
int
ss_max_inst_lat(de_inst_t *inst)
{
    int	    fu;

    fu = ss_inst_fu(inst);
    return fu_lat[fu].hi;
}
