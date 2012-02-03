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
 * $Id: cfg.c,v 1.2 2006/06/24 08:54:56 lixianfe Exp $
 *
 ******************************************************************************/


#include <stdio.h>
#include <stdlib.h>
#include "common.h"
#include "cfg.h"
#include "jptable.h"
#include "arch_funcs.h"


extern isa_t	*isa;
extern prog_t	prog;

// lookup addr in code, return the index if found, otherwise return -1
// since instr. addresses are in sorted order, we can use binary search
static int
lookup_addr(de_inst_t *code, int num, addr_t addr)
{
    int	    hi = num - 1, lo = 0, i;

    while (hi >= lo) {
	i = (hi + lo) / 2;
	if (code[i].addr == addr) {
            if (code[i].size == 0 && code[i].is_ret == 1 && code[i].op_enum == OP_NA) {
                 // it should be a fake return
                 if (code[i-1].addr == addr)
                     return i-1;
                 else
                     assert(code[i].addr == code[i-1].addr);
            }
	    return i;
        }
	else if (code[i].addr > addr)
	    hi = i - 1;
	else
	    lo = i + 1;
    }
    return -1;
}



// scan the decoded instr. and mark the locations in proc_entries if the
// corresponding instr. is the proc entry; it returns number fo procs
static int
scan_procs(int *proc_ent)
{
    int	    main_id, i, tid;

    prog.num_procs = 0;
    for (i = 0; i < prog.num_inst; i++) {
	// check whether this instr. is the main entrance; mark it if so
	if (prog.code[i].addr == prog.main_addr) {
            printf("Found main procedure at 0x%x\n", prog.main_addr);
	    if (proc_ent[i] == 0) {
		proc_ent[i] = 1;
		prog.num_procs++;
		main_id = i;
	    }
	} 
        if (inst_type(&prog.code[i]) == INST_CALL) {
	    // check the target addr of a call; mark it as proc entrance if not
	    // marked yet.
            assert(prog.code[i].num_targets == 1);
#if 0
            printf("Found call from %x to %x\n",
                    prog.code[i].addr, prog.code[i].targets[0]);
#endif
	    tid = lookup_addr(prog.code, prog.num_inst, prog.code[i].targets[0]);
	    if (tid == -1) {
		   fprintf(stderr, "no match for call: %x\n", prog.code[i].targets[0]);
		   exit(1);
	    }
	    if (proc_ent[tid] == 0) {
		proc_ent[tid] = 1;
		prog.num_procs++;
	    }
	}
    }
    return main_id;
}

/* liangyun */
extern int bjptb;

// scan the code of a proc and mark the location if it corresponds to a block entry
static void
scan_blocks(int *bb_ent, proc_t *proc)
{
    int		i, j, type, tid;
    de_inst_t	*inst;

    bb_ent[0] = 1;
    proc->num_bb = 1;

    for (i = 0; i < proc->num_inst; i++) {
	inst = &proc->code[i];
	type = inst_type(inst);
	if ((type == INST_COND) || (type == INST_UNCOND)) {
	    /* Each BB can have up to two targets (taken and not taken).
	       In the event of having multiple outgoing edges, we construct
	       a chain of BBs - one for each edge, with the not-taken edge
	       leading to the next BB in the chain.  */

	    /* Eeek. This hack doesn't work if the last instruction in the
	     * function has multiple destinations. */
	    assert(inst->num_targets <= 1 || i+1 < proc->num_inst);

	    if (inst->num_targets > 0 && i+1 < proc->num_inst) {
		if (bb_ent[i+1] == 0) {
		    bb_ent[i+1] = 1;
		    proc->num_bb++;
#if 0
		    printf("BB starting at 0x%lx as after %sjump\n",
			    (unsigned long)proc->code[i+1].addr,
			    inst->num_targets > 1 ? "multiple " : "");
#endif
		}

		/* Magic flag for scan_blocks to signal it to create more basic
		 * blocks for the extra edges. */
		bb_ent[i+1] += inst->num_targets - 1;
		proc->num_bb += inst->num_targets - 1;
#if 0
		printf("Adding an extra %d bbs for 0x%x\n",
			inst->num_targets - 1,
			inst->addr);
#endif
	    }
	    for (j = 0; j < inst->num_targets; j++) {
		// check the branch target addr, mark it as block entry if not marked yet
		tid = lookup_addr(proc->code, proc->num_inst, inst->targets[j]);
		if (tid == -1) {
		    fprintf(stderr, "no match for branch target %x from %x\n",
			    inst->targets[j], inst->addr);
		    exit(1);
		}
		if (bb_ent[tid] == 0) {
		    bb_ent[tid] = 1;
		    proc->num_bb++;
#if 0
		    printf("BB starting at 0x%lx as jump target\n",
			    (unsigned long)proc->code[tid].addr);
#endif
		}
	    }

	    // if the fall-through addr has not been marked as a block entry yet,
	    // mark it as block entry
	    if (type == INST_COND && bb_ent[i+1] == 0) {
		bb_ent[i+1] = 1;
		proc->num_bb++;
#if 0
		printf("BB starting at 0x%lx as jump fallthrough\n",
			(unsigned long)proc->code[i+1].addr);
#endif
	    }
	} else if (type == INST_CALL) {
	    // for a call instr, simply mark the next instr as block entry
	    if (bb_ent[i+1] == 0) {
		bb_ent[i+1] = 1;
		proc->num_bb++;
#if 0
                printf("BB starting at 0x%lx as call return\n",
                        (unsigned long)proc->code[i+1].addr);
#endif
	    }
	} else if (type == INST_RET) {
	    // for a return instr, if it is not the last instr in the proc, mark the
	    // next instr as block entry
	    if ((i < proc->num_inst - 1) && (bb_ent[i+1] == 0)) {
		bb_ent[i+1] = 1;
		proc->num_bb++;                
#if 0
                printf("BB starting at 0x%lx as after return instruction\n",
                        (unsigned long)proc->code[i+1].addr);
#endif
	    }
	}
    }
}


// lookup a basic block in a proc with a match of its start addr to the searched addr
static cfg_node_t *
lookup_bb(cfg_node_t *cfg, int num, addr_t addr)
{
    int	    hi = num - 1, lo = 0, i;

    while (hi >= lo) {
	i = (hi + lo) / 2;
	if (cfg[i].sa == addr)
	    return &cfg[i];
	else if (cfg[i].sa > addr)
	    hi = i - 1;
	else
	    lo = i + 1;
    }
    return NULL;
}



// create a new cfg edge from src->dst, "taken" specifies whether this edge is a
// taken edge or a fall-through edge; note since the number of incoming edges of the
// dst block cannot be statically determined, the storage for its incoming edges is
// dynamically scaled.
static void
new_edge(cfg_node_t *src, cfg_node_t *dst, int taken)
{
    cfg_edge_t	*e = (cfg_edge_t *) malloc(sizeof(cfg_edge_t));
    CHECK_MEM(e);
    e->src = src; e->dst = dst;
    e->fallthrough = taken == 0;
    if (taken == NOT_TAKEN)
	src->out_n = e;
    else
	src->out_t = e;
    dst->num_in++;
    dst->in = (cfg_edge_t **) realloc(dst->in, dst->num_in * sizeof(cfg_edge_t *));
    CHECK_MEM(dst->in);
    dst->in[dst->num_in - 1] = e;
}

static int
is_active_bb(cfg_node_t *bb) {
    int i;
    for (i = 0; i < bb->num_inst; ++i) {
        int type = inst_type(&bb->code[i]);        
        if (type != INST_NOP)
            return 1;
    }
    return 0;
}

/* liangyun */
extern  int bjptb;

// create outgoing cfg edges for each basic block in the following way:
// - first check the type of the block's last instr
// - create fall-through edge or/and a control transfer edge according to its type
static void
create_cfg_edges(proc_t *proc)
{
    int		i, type;
    cfg_node_t	*bb, *bb1;
 
    int    num_targets_remaining = 0;
    int    is_conditional, is_tailcall;

    for (i = 0; i < proc->num_bb; i++) {
	bb = &proc->cfg[i];
	assert(bb->num_inst > 0);
	type = inst_type(&bb->code[bb->num_inst-1]);
	is_conditional = bb->code[bb->num_inst-1].conditional;
        is_tailcall = bb->code[bb->num_inst-1].tailcall;
	if (type == INST_COND || type == INST_UNCOND) {
	    bb->type = (type == INST_COND) ? CTRL_COND : CTRL_UNCOND;
	    /* Now, some magic to handle basic blocks with multiple outgoing
	     * edges. We should have created a series of identical BBs, one for
	     * each outgoing edge. Here, we just need to link them all
	     * together.
	     */
	    if (num_targets_remaining == 0) {
		num_targets_remaining = bb->code[bb->num_inst-1].num_targets;
	    }

	    if (num_targets_remaining > 0) {
		if (num_targets_remaining > 1) {
		    bb1 = &proc->cfg[i+1];

		    /* Ensure we're talking about the same bb as before. */
		    assert(bb->code[bb->num_inst-1].addr == bb1->code[bb1->num_inst-1].addr);

                    if (is_active_bb(bb1))
            		    /* Create a fall-through edge to the next block. */
	        	    new_edge(bb, bb1, NOT_TAKEN);
		}

		/* Create taken edges. */
		bb1 = lookup_bb(proc->cfg, proc->num_bb,
			bb->code[bb->num_inst-1].targets[
		    	    num_targets_remaining-1]);
	       	if (bb1 == NULL) {
	    	    fprintf(stderr, "cannot find block start with addr: %x\n",
	    		    bb->code[bb->num_inst-1].targets[num_targets_remaining-1]);
	    	    exit(1);
	    	}
		new_edge(bb, bb1, TAKEN);

		num_targets_remaining--;
	    }

	    if (num_targets_remaining == 0 && type == INST_COND) {
		// create fall-through edge
		bb1 = &proc->cfg[i+1];
		new_edge(bb, bb1, NOT_TAKEN);
	    }
	} else if (type == INST_RET) {
	    // do not create any edge
	    bb->type = CTRL_RET;
            
            if (is_conditional) {
                // create fall-through edge
                assert(i < proc->num_bb - 1);
                bb1 = &proc->cfg[i+1];
                new_edge(bb, bb1, NOT_TAKEN);
            }
	} else {
            // if it's nop without target, just skip
            if (type == INST_NOP && bb->code[bb->num_inst-1].num_targets == 0)
                continue;

            // if it's preemption point, break the cfg
            if (bb->code[bb->num_inst-1].preemption) {
                bb->type = CTRL_CALL;
                continue;
            }

	    // create fall-through edge (for seqencial block and call block) if
	    // current block is not the last one in the proc
            if (i < proc->num_bb - 1) {
		bb1 = &proc->cfg[i+1];
		new_edge(bb, bb1, NOT_TAKEN);
	    }
            // check if it's conditional tailcall
            if (is_conditional && is_tailcall) {
                if (i < proc->num_bb - 2) {
                    bb1 = &proc->cfg[i+1];
                    if (bb1->size == 0 && bb1->sa == bb->sa + bb->size - 4) {
                        bb1 = & proc->cfg[i+2];
                        new_edge(bb, bb1, NOT_TAKEN);
                    }
                }
            }
	    if (type == INST_CALL) 
		bb->type = CTRL_CALL;
	    else
		bb->type = CTRL_SEQ;
	}
    }
}



// lookup a proc with a match of its start addr to the searched addr
static proc_t *
lookup_proc(addr_t addr)
{
    int	    hi = prog.num_procs - 1, lo = 0, i;

    while (hi >= lo) {
	i = (hi + lo) / 2;
	if (prog.procs[i].sa == addr)
	    return &prog.procs[i];
	else if (prog.procs[i].sa > addr)
	    hi = i - 1;
	else
	    lo = i + 1;
    }
    return NULL;
}



int
bb_is_loop_head(cfg_node_t *bb)
{
    return (bb->loop_role & LOOP_HEAD);
}



int
bb_is_loop_tail(cfg_node_t *bb)
{
    return (bb->loop_role & LOOP_TAIL);
}


#if 0

static void
loop_check(proc_t *proc, int start, int end)
{
    cfg_node_t	*bb;
    Queue	worklist;

    bb = &proc->cfg[start];
    if (bb_is_loop_head(bb))
	return;
    if (start == end) {
	proc->cfg[start].loop_role = LOOP_HEAD | LOOP_TAIL;
	return;
    }

    init_queue(&worklist, sizeof(cfg_node_t *));
    enqueue(&worklist, &bb);
    bb->flags = end;
    while (!queue_empty(&worklist)) {
	bb = *((cfg_node_t **) dequeue(&worklist));
	if (bb->id == end) {
	    proc->cfg[start].loop_role = LOOP_HEAD;
	    proc->cfg[end].loop_role = LOOP_TAIL;
	    break;
	} 
	if ((bb->out_n != NULL) && (bb->out_n->dst->flags != end)) {
	    enqueue(&worklist, &bb->out_n->dst);
	    bb->out_n->dst->flags = end;
	}
	if ((bb->out_t != NULL) && (bb->out_t->dst->flags != end)) {
	    enqueue(&worklist, &bb->out_t->dst);
	    bb->out_t->dst->flags = end;
	}
    }
    free_queue(&worklist);
}
#endif

static void
find_backedges_recursive(proc_t *proc, int bb_id, int *visited, int *am_ancestor)
{
    cfg_node_t *bb;

    if (visited[bb_id])
        return;

    /* Extract bb. */
    assert(bb_id >= 0 && bb_id < proc->num_bb);
    bb = &proc->cfg[bb_id];

    /* Mark as visited. */
    visited[bb_id] = 1;

    /* We are now an ancestor of anything we visit. */
    am_ancestor[bb_id] = 1;

    /* Make it easier to iterate over these. */
    cfg_edge_t *edges[2];
    edges[0] = bb->out_t;
    edges[1] = bb->out_n;

    int i;
    for (i = 0; i < 2; i++) {
        cfg_edge_t *e = edges[i];
        if (e == NULL)
            continue;

        assert(e->src == bb);
        cfg_node_t *dst_bb = e->dst;

        int dst_bb_id = dst_bb->id;
        if (!visited[dst_bb_id]) {
            find_backedges_recursive(proc, dst_bb_id, visited, am_ancestor);
        } else if (am_ancestor[dst_bb_id]) {
            bb->loop_role |= LOOP_TAIL;
            dst_bb->loop_role |= LOOP_HEAD;
        }
    }

    /* No longer are we an ancestor. */
    am_ancestor[bb_id] = 0;
}

static void
identify_loops(proc_t *proc)
{
    int i;

    int *visited = (int*)calloc(proc->num_bb, sizeof(int));
    int *am_ancestor = (int*)calloc(proc->num_bb, sizeof(int));

    find_backedges_recursive(proc, 0, visited, am_ancestor);

    free(visited);
    free(am_ancestor);

    // Reset flags (although we didn't use them).
    for (i = 0; i < proc->num_bb; i++)
        proc->cfg[i].flags = 0;
}



// create a CFG for a proc in three steps:
// - find basic block entries and create basic blocks
// - set basic info for blocks
// - finish up the construction of CFG by connecting blocks with edges
static void
create_cfg(proc_t *proc)
{
    int		*bb_ent, i, bb_id = 0;
    int          num;

    cfg_node_t	*bb;
    addr_t	addr;
    proc_t	*callee;
    
    

    assert(proc->num_inst > 0);
    bb_ent = (int *) calloc(proc->num_inst, sizeof(int));
    CHECK_MEM(bb_ent);
    
    // find & create blocks
    scan_blocks(bb_ent, proc);
    proc->cfg = (cfg_node_t *) calloc(proc->num_bb, sizeof(cfg_node_t));
    CHECK_MEM(proc->cfg);

    // set basic info for blocks
#if 0
    printf("Procedure has %d instructions\n", proc->num_inst);
#endif
    for (i = 0; i < proc->num_inst; i++) {
	if (bb_ent[i]) {
	    // start of a new block
            num = bb_ent[i];
            while(num > 1){
                 // add dummy node
                 bb = &proc->cfg[bb_id];
                 bb->id = bb_id;
                 bb->proc = proc;
                 bb->sa   = proc->code[i - 1].addr; // previous instruction 
                 bb->size = proc->code[i - 1].size;
                 bb->num_inst = 1;
                 bb->code  = &proc->code[i - 1];
                 bb_id++;
                 num--;
            }
	    bb = &proc->cfg[bb_id];
	    bb->id = bb_id;
	    bb->proc = proc;
	    bb->sa = proc->code[i].addr;
	    bb->size = proc->code[i].size;
	    bb->num_inst = 1;
	    bb->code = &proc->code[i];
	    bb_id++;
	} else {
	    // continuation of current block
	    bb->size += proc->code[i].size;
	    bb->num_inst++;
	}
    }

#if 0
    for (i = 0; i < bb_id; i++) {
        printf("BB %d at 0x%lx has %d instructions\n",
                i, (unsigned long)proc->cfg[i].sa, proc->cfg[i].num_inst);
    }
#endif
    if (bb_id != proc->num_bb) {
        printf("Got %d basic blocks, wanted %d - had an extra %d\n",
		bb_id, proc->num_bb, bb_id - proc->num_bb);
        assert(bb_id == proc->num_bb);
    }
    free(bb_ent);

    // connect block with control transfer edges
    create_cfg_edges(proc);

    // build links from callers (basic blocks) to its callees (procs)
    for (i = 0; i < proc->num_bb; i++) {
	bb = &proc->cfg[i];
        if (bb->code[bb->num_inst-1].op_enum == LDR_L && bb->code[bb->num_inst-1].conditional)
            bb->flags |= CONDITIONAL_POP;
	if (bb->type == CTRL_CALL) {
	    assert(bb->code[bb->num_inst-1].num_targets == 1);
	    addr = bb->code[bb->num_inst-1].targets[0];
	    callee = lookup_proc(addr);
	    if (callee == NULL) {
		    //fprintf(stderr, "no proc mathces the callee addr: %x\n", addr);
		    //exit(1);
            bb->type = CTRL_SEQ;
	    }else
           bb->callee = callee;
	}
    }

    // identify loop heads/tails
    identify_loops(proc);
}



// identify procedures, and construct a control flow graph for each
void
build_cfgs()
{
    int	    *proc_ent, i, proc_id = 0, main_id;
    proc_t  *proc = NULL;

    proc_ent = (int *) calloc(prog.num_inst, sizeof(int));
    CHECK_MEM(proc_ent);

    // find & create procs
    main_id = scan_procs(proc_ent);
    prog.procs = (proc_t *) calloc(prog.num_procs, sizeof(proc_t));
    CHECK_MEM(prog.procs);

    // set basic info for procs
    for (i = 0; i < prog.num_inst; i++) {
	if (proc_ent[i]) {
	    // start of a new proc
	    proc = &prog.procs[proc_id];
	    proc->id = proc_id;
	    proc->sa = prog.code[i].addr;
	    proc->size = prog.code[i].size;
	    proc->num_inst = 1;
	    proc->code = &prog.code[i];
	    if (i == main_id)
		prog.main_proc = proc_id;
#if 0
		printf("Proc %d at 0x%x\n", proc_id, proc->sa);
#endif
	    proc_id++;
	} else {
	    // continuation of current proc
	    proc->size += prog.code[i].size;
#if 0
	    printf("%x: Proc %ld now ends at %x\n",
                    prog.code[i].addr,
                    proc - prog.procs, proc->sa + proc->size);
#endif
	    proc->num_inst++;

            assert(prog.code[i].addr + 4 == proc->sa + proc->size);
	}
    }
    free(proc_ent);

    assert(prog.num_procs == proc_id);

    // create CFG for each proc
    for (i = 0; i < prog.num_procs; i++) {
#if 0
        const char *s = sym_lookup_name(prog.procs[i].sa, 1, sdb_any);
        printf("Creating proc# %d (%d procs total) at %x %s (%d instructions)\n",
                i, prog.num_procs,
                prog.procs[i].sa,
                s,
                prog.procs[i].num_inst
                );
#endif
	create_cfg(&prog.procs[i]);
	//dump_cfg(stdout, &prog.procs[i]);
    }
}










void
dump_cfg(FILE *fp, proc_t *proc)
{
    cfg_node_t  *bb;
    int         i;

    fprintf(fp, "\nproc[%d] cfg:\n", proc->id);
    for (i = 0; i < proc->num_bb; i++) {
	bb = &proc->cfg[i];
	fprintf(fp, " %d : %08x : [ ", bb->id, bb->sa);
	if (bb->out_n != NULL)
	    fprintf(fp, " %d",  bb->out_n->dst->id);
	else
	    fprintf(fp, " ");
	fprintf(fp, " , ");
	if (bb->out_t != NULL)
	    fprintf(fp, " %d ",  bb->out_t->dst->id);
	else
	    fprintf(fp, " ");
	fprintf(fp, " ] ");
	if (bb->callee != NULL) {
	    fprintf(fp, " P%d", bb->callee->id);
	}
#if 0
	if (bb_is_loop_head(bb))
	    fprintf(fp, "/");
	if (bb_is_loop_tail(bb))
	    fprintf(fp, "\\");
#endif
	fprintf(fp, "\n");
    }
}


