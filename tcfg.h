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
 * $Id: tcfg.h,v 1.2 2006/06/24 08:54:57 lixianfe Exp $
 *
 * Construct a flow graph transformed from the original CFG due to function
 * inlining, loop unrolling ...
 *
 ******************************************************************************/

#ifndef TCFG_H
#define TCFG_H

#include "cfg.h"
#include "common.h"

// in many cases, two virtual nodes are assumed to exist: one is a "virtual
// start" node preceding the start node of the tcfg; the other is the "virtual
// end" node following end nodes of the tcfg
#define V_START_ID  -1
#define V_END_ID    -2
#define TCFG_STEP_SIZE 64

struct context_t {
    addr_t callsite;
    struct context_t *parent;
};
typedef struct context_t context_t;

typedef struct tcfg_edge_t tcfg_edge_t;

// transformed CFG node type (basic block instance)
struct tcfg_node {
    cfg_node_t	*bb;	// pointer to the physical basic block
    int		id;	// global id in tcfg (has nothing to do with its bb id)
    tcfg_edge_t	*in, *out;  // incoming and outgoing edges
    unsigned	flags;
    int           loop_id;     // vivy: for infeasible path constraints
    int           exec_count;  // vivy: for infeasible path constraints
	 int 				anal_count;		
	 int 				dcache_delay; 		/* For data cache analysis */ 	
	 int 				inst_cache_delay;	/* For instruction cache analysis using abstract
												 * interpretation */	 
	 int 				n_persistence;		/* Number of persistence instruction */
	 int 				n_data_persistence;		/* Number of persistence data blocks */
	 int 				n_u1_persistence;			/* Number of persistence instruction in Unified cache*/
	 int 				n_u1_data_persistence;	/* Number of persistence data blocks in unified cache */
	 int 				n_l2_persistence;	/* Number of instruction in l2 instruction cache */

    char is_unconditional;
    /*HBK: for cache analysis on tcfg*/
    int                 max_miss;
    acs_p** acs_in;
    acs_p** acs_out;
    context_t *ctx;

        worklist_p* mpa_acs_in;
        worklist_p* mpa_acs_out;
#if 0
        worklist_p mpa_acsin_arr, mpa_acsout_arr;
        worklist_p mpa_lp_in, mpa_lp_out;
        worklist_p mpa_acsl2in_arr, mpa_acsl2out_arr;
        worklist_p mpa_lpl2_in, mpa_lpl2_out;
#endif
        worklist_p* address_set;
        worklist_p* addrset_l1;
        worklist_p* addrset_l2;

};

#ifndef TCFG_NODE_T_DEFINED
#define TCFG_NODE_T_DEFINED
typedef struct tcfg_node tcfg_node_t;
#endif



// since the numbers of outgoing/incoming edges of each tcfg node vary widely, a
// double link list is used, e.g., given any tcfg edge connecting src->dst, all
// outgoing edges of src can be traversed by going along two directions: going along
// prev_out will traverse all earlier out edges of src, and going along next_out will
// traverse all later out edges of src; similary for the incoming edges of dst
struct tcfg_edge_t {
    int		id;
    int		branch;		// TAKEN or NOT_TAKEN
    tcfg_node_t	*src, *dst;
    tcfg_edge_t *next_out;	// next outgoing edge of src
    tcfg_edge_t *next_in;	// next incoming edge of dst
    int		flags;
    int         is_backedge;
};



typedef struct tcfg_nlink_t tcfg_nlink_t;
struct tcfg_nlink_t {
    tcfg_node_t	    *bbi;
    tcfg_nlink_t    *next;
};


typedef struct tcfg_elink_t tcfg_elink_t;

struct tcfg_elink_t {
    tcfg_edge_t	    *edge;
    tcfg_elink_t    *next;
};



void
prog_tran(char *obj_file);



void
clear_bbi_flags(void);



int
bbi_type(tcfg_node_t *bbi);



void
dump_tcfg(FILE *fp);


int
bbi_backedge(tcfg_edge_t *edge);

int
bbi_pid(tcfg_node_t *bbi);

int
bbi_bid(tcfg_node_t *bbi);

int
cond_bbi(tcfg_node_t *bbi);

void
clear_tcfg_edge_flags(void);

int
test_depth(int pid, int depth);

void
add_start_point(tcfg_node_t *bbi);

void 
virtual_unroll(void);

void
collect_tcfg_edges(void);

void
build_bbi_map(void);

void 
set_topological_tcfg(void);

int 
all_predecessors_visited(tcfg_node_t* bbi, char* visited);

void
dump_map_file(char *obj_file);

extern tcfg_node_t     **start_point;
extern unsigned        num_start_point;

int num_topo_tcfg;
int* topo_tcfg;
int num_topo_tcfg_loops;
int* topo_tcfg_loops;

#endif
