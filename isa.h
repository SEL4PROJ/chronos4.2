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
 * $Id: isa.h,v 1.2 2006/06/24 08:54:56 lixianfe Exp $
 *
 ******************************************************************************/

#ifndef ISA_H
#define ISA_H
#include "address.h"
#include "cache.h"

// instruction types broadly in three groups:
// computation,
// memory access
// control flow transfer
enum inst_type_t {
    INST_NOP = 0,   // instr. doing nothing
    // (1) computation
    INST_ICOMP,	    // integer arithmetic instr.
    INST_FCOMP,	    // floating-point arithmetic instr.
    // (2) memory access
    INST_LOAD,
    INST_STORE,
    // (3) control flow transfer
    INST_COND, // conditional jumps
    INST_UNCOND,
    INST_CALL,
    INST_RET,
    // (4) trap instr such as syscall, break, etc
    INST_TRAP
};

enum offset_mode_t {
    IMM_INDEXED = 0,
    PRE_INDEXED,
    POST_INDEXED
};

enum address_mode_t {
    NO_ADDRESS_NODE = 0,
    IA_ADDRESS_MODE,
    IB_ADDRESS_MODE,
    DA_ADDRESS_MODE,
    DB_ADDRESS_MODE
};

enum operand_shift_t {
    NO_SHIFT = 0,
    SHIFT_BY_IMM,
    SHIFT_BY_REG
};

enum shift_mode_t {
    SHIFT_MODE_LSL = 0,
    SHIFT_MODE_LSR,
    SHIFT_MODE_ASR,
    SHIFT_MODE_ROR,
    SHIFT_MODE_RRX
};

// each instruction type has the following fields useful for analysis
typedef struct {
    int	    opcode;	// inst opcode
    int	    type;	// inst type
    char    *name;	// inst name
} isa_t;

/* decoded instruction type */
struct de_inst_t {
    addr_t  addr;
    addr_t  r_addr;
    int	    op_enum;	    	/* continuous numbered opcode 
										   (orginal non-contenuous) */
    int	    size;

    unsigned int     is_ret:1;
    unsigned int     is_call:1;
    // TODO: Should this maybe ascend and conditional become jumps with extra
    // nodes?
    unsigned int has_imm:1;
    unsigned int conditional:1;
    unsigned int s_bit:1;
    unsigned int condition:5;
    unsigned int last_shift:2;
    unsigned int shift_mode:3;
    unsigned int offset_addr_mode:3;
    unsigned int writeback:1;
    unsigned int tailcall:1;
    unsigned int preemption:1;
    unsigned int pc_changed:1;
    unsigned int flag:10;

    int	    num_in, num_out;	/* number of input/output operands */
    int	    *in, *out;		   /* input/output operands (registers) */
    long    imm;					/* Immediate integer value. For base 
										 * indexing and immediate addressing
										 * mode */
    int     shift_val;
    addr_t  *targets;				/* target addr for control transfer inst */
    int num_targets;

	 acs_p** 	acs_in;		/* abstract data cache state at the entry 
													 * point of the instruction */
	 acs_p** 	acs_out;		/* abstract data cache state at the exit 
													 * point of the instruction */ 
	 ric_p* 	abs_reg;				/* Abstract register value at entry point 
										 * of an instruction */ 
	 ACCESS_T data_access;		/* data access classification(hit/not known) 
										 * for load/store instructions */ 
	 ACCESS_T inst_access;		/* Instruction access classification */
	 ACCESS_T l2_inst_access;	/* L2 Instruction access classification */
	 ACCESS_T u1_data_access;	/* unified D/I cache access classification */
	 ric_p mod_addr;
};
#ifndef DE_INST_T_DEFINED
#define DE_INST_T_DEFINED
typedef struct de_inst_t de_inst_t;
#endif

void
init_isa(void);
int
max_inst_lat(de_inst_t *inst);

#endif
