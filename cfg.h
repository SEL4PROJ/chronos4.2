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
 * $Id: cfg.h,v 1.2 2006/06/24 08:54:56 lixianfe Exp $
 *
 ******************************************************************************/

#ifndef CFG_H
#define CFG_H


#include <stdio.h>
#include "isa.h"


#define NOT_TAKEN	0
#define TAKEN		1
#define BOTH_BRANCHES	2
#define CONDITIONAL_POP 4
#define LOOP_HEAD	1
#define LOOP_TAIL	2


typedef enum {CTRL_SEQ, CTRL_COND, CTRL_UNCOND, CTRL_CALL, CTRL_RET} bb_type_t;
 

typedef struct cfg_edge_t   cfg_edge_t;
typedef struct proc_t	    proc_t;

// control flow graph node (basic block) type
typedef struct {
    int		id;		// basic block id (per procedure)
    proc_t  	*proc;		// up-link to the procedure containing it
    addr_t	sa;		// block start addr
    int		size;		// size (in bytes)
    int		num_inst;	// number of instructions
    de_inst_t   *code;		// pointer to the first instruction

    bb_type_t	type;		
    cfg_edge_t	*out_n, *out_t;	// outgoing edges (non-taken/taken) 
    int		num_in;		// number of incoming edges
    cfg_edge_t	**in;		// incoming edges

    proc_t	*callee;	// points to a callee if callee_addr not NULL

    int		loop_role;	// whether it is a loop head, tail, or neither

    int		flags;		// for traverse usage

              						/* A data structure holding abstract register */  
	 ric_p* in_abs_reg_value;	/* values. Register numbers can directly be */
	 ric_p* out_abs_reg_value; /* indexed in this structure */

	 abs_mem_p in_abs_mem_value;  /* A data structure holding value in abstract */
	 abs_mem_p out_abs_mem_value; /*  memory locations */


     /*** HBK: for scope-aware data cache analysis ***/
     void   *d_instlist;
     int    num_d_inst;

} cfg_node_t;



// control flow graph edge type
struct cfg_edge_t {
    cfg_node_t  *src, *dst;	// src -> dst
    int fallthrough;
};



// procedure type
struct proc_t {
    int		id;		// proc id
    addr_t	sa;		// proc start addr
    int		size;		// size (in bytes)
    int		num_inst;	// number of instructions
    de_inst_t   *code;		// instructions

    int		num_bb;		// number of basic blocks
    cfg_node_t	*cfg;		// cfg nodes with num_bb nodes

    int		flags;
};

// symbol table (address range of global variable
typedef struct {
    char* name;
    addr_t addr;
    int size;
} symbol_i;


// program type
typedef struct {
    de_inst_t	*code;		// decoded program text
    int		    code_size;	// code size (in bytes)
    int		    num_inst;	// number of instructions
    addr_t	    start_addr, end_addr, main_addr;
    proc_t	    *procs;		// procedures
    symbol_i    *p_info;    // procedure symbol info
    symbol_i    *v_info;    // global variable symbol info
    int         num_vars;   // number of global variables
    int		    num_procs;	// number of procedures
    int		    main_proc;	// index of the main proc
    int         num_inst_alloc; // space allocated for instructions
} prog_t;

#define MAX_OVRL_NODES 1024
#define OPT 1

struct col_data
{
	union {
		 proc_t* proc;
		 de_inst_t* inst;
	}u;
	int type;
	struct col_data* next;
};

typedef struct col_data* col_data_p;
typedef struct col_data col_data_s;

/* Describes the data structures used for layout formation */
struct ovrl_graph {
	union {
		 proc_t* proc;
		 de_inst_t* inst;
		 col_data_p pref;
	}u;
	int type;
	int invalid;
	/* execution count by WCET */
	int freq;
	struct ovrl_graph* next;
};
typedef struct ovrl_graph* ovrl_graph_p;
typedef struct ovrl_graph ovrl_graph_s;

void
dump_cfg(FILE *fp, proc_t *proc);

void
build_cfgs(void);

int
bb_is_loop_head(cfg_node_t *bb);

int
bb_is_loop_tail(cfg_node_t *bb);

#endif
