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
 * $Id: pipeline.c,v 1.4 2006/07/23 09:20:46 lixianfe Exp $
 *
 * traverse t-cfg to formulate execution paths; and estimate their execution
 * timing bounds
 *
 ******************************************************************************/


#include <string.h>
#include <stdlib.h>
#include "isa.h"
#include "cfg.h"
#include "tcfg.h"
#include "cache.h"
#include "bpred.h"
#include "loops.h"
#include "estimate.h"
#include "exegraph.h"
#include "arch_funcs.h"
#include "scp_cache.h"
#include "pipeline.h"


extern tcfg_node_t  **tcfg;
extern int	    num_tcfg_nodes;
extern tcfg_edge_t  **tcfg_edges;
extern int	    num_tcfg_edges;
extern cache_t	    cache;
extern cache_t      cache_l2;
extern int	    bpred_scheme;
extern int	    enable_icache;
extern char	    ***hit_miss;
extern int	    *num_hit_miss;
extern loop_t	    ***bbi_hm_list;
extern int	    *num_bbi_hm_list;
extern de_inst_t    ***mp_insts;
extern int	    *num_mp_insts;
extern int	    num_eg_insts;
extern int	    **num_mblk_conflicts;
extern loop_t	    **loops;
extern loop_t	    **loop_map;		// bbi => loop
extern int	    num_tcfg_loops;
extern mem_blk_t    **mp_gen;
extern int          enable_il2cache;
extern int          enable_ul2cache;


int		pipe_stages = 5;
int		pipe_ibuf_size;
int		pipe_iwin_size;
int		prolog_size, pipe_iwin_size;
code_link_t	**prologs, **epilogs;
mas_inst_t	**bodies, *start_body;
int		**cpred_times, **mpred_times, start_time;



// temporary variables
// to indicate for each bbi whether it contains long latency instr
int		*mlat_bbi;
// to indicate for each edge, the shortest distance of producer to any long
// latency instr in edge->dst or its predecessors
int		*max_elog_len;
// the first multi-cycle latency instr along each mispred path
int		*mlat_mpinst;
// if est unit's source is BP_CPRED, the number of  mispred instr to be
// truncated at the end of the prolog
int		*num_plog_trunc;
mblk_tag_t	*tmp_cs;
/* sudiptac :::: for level 2 cache */
mblk_tag_t      *tmp_cs_l2;
int		num_plogs, num_elogs;

/************************************************/
extern int enable_scp_dcache;
extern int enable_scp_dl2cache;
int *** extend_cpred_times;
int* numberOfLoop;
int* numberofContext;

// if a bbi has mult-latency instructions, then set its corresponding entry
// to 1, such bbi has direct contribution to late contentions
static void
set_mlat_bbi(void)
{
    int		bbi_id, i;
    cfg_node_t	*bb;

    mlat_bbi = (int *) calloc(num_tcfg_nodes, sizeof(int));
    for (bbi_id = 0; bbi_id < num_tcfg_nodes; bbi_id++) {
	bb = tcfg[bbi_id]->bb;
	if (bb->num_inst > 0) {
	    for (i = bb->num_inst - 1; i >= 0; i--) {
		if (max_inst_lat(&bb->code[i]) > 1)
		    break;
	    }
	    mlat_bbi[bbi_id] = i;
	} else {
	    mlat_bbi[bbi_id] = 0;
	}
    }
}


#define MAX_REGS    256
int		    dep_regs[MAX_REGS];

static void
lookup_mlat(int orig, int dist, tcfg_node_t *bbi, int no_mlat)
{
    int		    i, k, tmp, r;
    de_inst_t	    *inst;
    tcfg_edge_t	    *e;

    if (no_mlat && (mlat_bbi[bbi->id] < 0)) {
	dist += bbi->bb->num_inst;
	if ((bbi->in == NULL) || (dist >= pipe_iwin_size))
	    return;
	for (e = bbi->in; e != NULL; e = e->next_in)
	    lookup_mlat(orig, dist, e->src, 1);
	return;
    }

    for (i = bbi->bb->num_inst - 1; i >= 0; i--) {
	inst = &bbi->bb->code[i];
	for (k = 0; k < inst->num_out; k++) {
	    r = inst->out[k];
	    if (dep_regs[r] == orig) {
		tmp = pipe_iwin_size - (dist + (bbi->bb->num_inst - i));
		max_elog_len[orig] = max(tmp, max_elog_len[orig]);
		return;
	    }
	}
	if (max_inst_lat(inst) > 1) {
	    for (k = 0; k < inst->num_in; k++) {
		r = inst->in[k];
		dep_regs[r] = orig;
	    }
	}
    }

    dist += bbi->bb->num_inst;
    if (dist < pipe_iwin_size) {
	for (e = bbi->in; e != NULL; e = e->next_in)
	    lookup_mlat(orig, dist, e->src, 0);
    }
}



static void
bound_elog_len(void)
{
    int		    i;

    max_elog_len = (int *) malloc(num_tcfg_nodes * sizeof(int));
    for (i = 0; i < MAX_REGS; i++)
	dep_regs[i] = -1;

    max_elog_len[0] = 0;
    if (mlat_bbi[0] >= 0)
	max_elog_len[0] = pipe_iwin_size - (tcfg[0]->bb->num_inst - mlat_bbi[0]);

    for (i = 1; i < num_tcfg_nodes; i++) {
	max_elog_len[i] = 0;
	lookup_mlat(i, 0, tcfg[i], 1);
    }
}



static void
find_mlat_mpinst(void)
{
    int		    i, k;

    mlat_mpinst = (int *) calloc(num_tcfg_edges, sizeof(int));
    num_plog_trunc = (int *) calloc(num_tcfg_edges, sizeof(int));

    for (i = 0; i < num_tcfg_edges; i++) {
	for (k = 0; k < num_mp_insts[i]; k++) {
	    if (max_inst_lat(mp_insts[i][k]) > 1) {
		mlat_mpinst[i] = k + 1;
		break;
	    }
	}
    }
}



// create a prologue from the reverse of path; and for the first node, skip the
// first num_skip instructions
static void
new_prolog(int log_set, tcfg_edge_t **path, int path_len, int num_skip)
{
    int		i, k, num = 0, num_mp = 0, tag, set, edge_id, 
                max_num_mp, set_l2, tag_l2;;
    tcfg_node_t	*bbi, *mbbi;
    Queue	queue;
    code_link_t	*plog;
    mas_inst_t	mas_inst;
    addr_t	sa;

    if (num_skip < 0)
	num_skip = 0;

    memset(tmp_cs, 0, cache.ns * sizeof(mblk_tag_t));

    /* sudiptac :::: for level 2 cache analysis */
    if (enable_il2cache || enable_ul2cache) {
        memset(tmp_cs_l2, 0, cache_l2.ns * sizeof(mblk_tag_t));
    }

    init_queue(&queue, sizeof(mas_inst_t));

    for (i = path_len-1; i >= 0; i--) {
	bbi = path[i]->src;
	sa = bbi->bb->sa;
	// copy code of e->src into prologue
	for (k = num_skip; k < bbi->bb->num_inst; k++) {
	    // bpred related
	    mas_inst.inst = &bbi->bb->code[k];
	    mas_inst.bbi_id = bbi->id;
            assert(bbi->id >= 0);
	    mas_inst.mblk_id = MBLK_ID(sa, mas_inst.inst->addr);
	    mas_inst.bp_flag = BP_CPRED;
	    // cache related
	    tag = TAG(mas_inst.inst->addr);
	    set = SET(mas_inst.inst->addr);
            tag_l2 = TAG_L2(mas_inst.inst->addr);
            set_l2 = SET_L2(mas_inst.inst->addr);

	    if (tmp_cs[set].valid == 0)
		mas_inst.ic_flag = IC_UNCLEAR;
	    else if (tmp_cs[set].tag == tag)
		mas_inst.ic_flag = IC_HIT;
	    else
		mas_inst.ic_flag = IC_MISS;
	    tmp_cs[set].valid = 1;
	    tmp_cs[set].tag = tag;

            /* sudiptac :::: for L2 cache analysis */
            if (enable_il2cache || enable_ul2cache) {
                if (tmp_cs_l2[set_l2].valid == 0)
                    mas_inst.ic_flag_l2 = IC_UNCLEAR;
                else if (tmp_cs_l2[set_l2].tag == tag_l2)
                    mas_inst.ic_flag_l2 = IC_HIT;
                else
                    mas_inst.ic_flag_l2 = IC_MISS;
                tmp_cs_l2[set_l2].valid = 1;
                tmp_cs_l2[set_l2].tag = tag_l2;
            }
            /******************************************************/
            if (enable_scp_dcache || enable_ul2cache) {
                int iType = inst_type(mas_inst.inst);
                if (iType == INST_LOAD) {
                    mas_inst.dc_flag = DC_UNCLEAR;
                    if (enable_scp_dl2cache || enable_ul2cache)
                        mas_inst.dc_flag_l2 = DC_UNCLEAR;
                    } else if (iType == INST_STORE) {
                        mas_inst.dc_flag = DC_STORE;
                        if (enable_scp_dl2cache || enable_ul2cache)
                            mas_inst.dc_flag_l2 = DC_STORE;
                    } else {
                        mas_inst.dc_flag = DC_HIT;
                        if (enable_scp_dl2cache || enable_ul2cache)
                            mas_inst.dc_flag_l2 = DC_HIT;
                    }
            } else {
                mas_inst.dc_flag = DC_HIT;
                mas_inst.dc_flag_l2 = DC_HIT;
            }
            /******************************************************/
	    enqueue(&queue, &mas_inst);
	    num++;
	}
	num_skip = 0;
	if ((bpred_scheme == NO_BPRED) || !cond_bbi(bbi))
	    continue;

	// mispred instructions
	edge_id = path[i]->id;
	if (mlat_mpinst[edge_id] > max_elog_len[bbi->id])
	    continue;

	max_num_mp = min(num_mp_insts[edge_id], max_elog_len[bbi->id]);
	if (bbi->out == path[i])
	    mbbi = bbi->out->next_out->dst;
	else
	    mbbi = bbi->out->dst;
	num_mp = 0;
	for (k = 0; k < max_num_mp; k++) {
	    if (num_mp >= mbbi->bb->num_inst) {
		mbbi = mbbi->out->dst;
		num_mp = 0;
	    }
	    mas_inst.inst = mp_insts[edge_id][k];
	    mas_inst.bbi_id = mbbi->id;
            assert(mbbi->id >= 0);
	    mas_inst.mblk_id = MBLK_ID(mbbi->bb->sa, mas_inst.inst->addr);

            /* sudiptac ::: for level 2 cache analysis */
            mas_inst.mblk_id_l2 = MBLK_ID_L2(sa, mas_inst.inst->addr);

	    if (i == 0)
		mas_inst.bp_flag = BP_MPRED;
	    else
		mas_inst.bp_flag = BP_UNCLEAR;
	    tag = TAG(mas_inst.inst->addr);
	    set = SET(mas_inst.inst->addr);
	    if (tmp_cs[set].valid == 0)
		mas_inst.ic_flag = IC_UNCLEAR;
	    else if (tmp_cs[set].tag == tag)
		mas_inst.ic_flag = IC_HIT;
	    else {
		mas_inst.ic_flag = IC_MISS;
		tmp_cs[set].valid = 1;
	    }

            /* sudiptac :::: for level 2 cache analysis */
            if (enable_il2cache || enable_ul2cache) {
                if (tmp_cs_l2[set_l2].valid == 0)
                    mas_inst.ic_flag_l2 = IC_UNCLEAR;
                else if (tmp_cs_l2[set_l2].tag == tag_l2)
                    mas_inst.ic_flag_l2 = IC_HIT;
                else {
                    mas_inst.ic_flag_l2 = IC_MISS;
                    tmp_cs_l2[set_l2].valid = 1;
                }
            }
            /******************************************************/
            if (enable_scp_dcache || enable_ul2cache) {
                int iType = inst_type(mas_inst.inst);
                if (iType == INST_LOAD) {
                    mas_inst.dc_flag = DC_UNCLEAR;
                    if (enable_scp_dl2cache || enable_ul2cache)
                        mas_inst.dc_flag_l2 = DC_UNCLEAR;
                } else if (iType == INST_STORE) {
                    mas_inst.dc_flag = DC_STORE;
                    if (enable_scp_dl2cache || enable_ul2cache)
                        mas_inst.dc_flag_l2 = DC_STORE;
                } else {
                    mas_inst.dc_flag = DC_HIT;
                    if (enable_scp_dl2cache || enable_ul2cache)
                        mas_inst.dc_flag_l2 = DC_HIT;
                }
            } else {
                mas_inst.dc_flag = DC_HIT;
                mas_inst.dc_flag_l2 = DC_HIT;
            }
            /******************************************************/

	    enqueue(&queue, &mas_inst);
	    num++;
	    num_mp++;
	}
	if (i == 0)
	    num_plog_trunc[log_set] = max_num_mp;
    }

    // copy code from temporary storage to the new prologue node
    plog = (code_link_t *) calloc(1, sizeof(code_link_t));
    CHECK_MEM(plog);
    plog->code = (mas_inst_t *) calloc(num, sizeof(mas_inst_t));
    CHECK_MEM(plog->code);
    for (k = 0; k < num; k++)
	plog->code[k] = *((mas_inst_t *) dequeue(&queue));
    plog->num_inst = num;
    plog->next = prologs[log_set];
    prologs[log_set] = plog;

    free_queue(&queue);
}



static void
trav_backward(int log_set, tcfg_edge_t **path, int path_len, int code_len)
{
    tcfg_node_t	*bbi;
    tcfg_edge_t	*e;

    assert(path_len > 0);
    assert(code_len >= 0);

    bbi = path[path_len-1]->src;
    code_len += bbi->bb->num_inst;
    if ((code_len >= prolog_size) || (bbi->in == NULL))
	new_prolog(log_set, path, path_len, code_len - prolog_size);
    else {
	for (e = bbi->in; e != NULL; e = e->next_in) {
	    // TODO: FIXME: bodgy hack.
	    // if (path_len >= prolog_size)
            //     return;

	    path[path_len] = e;
	    trav_backward(log_set, path, path_len+1, code_len);
	}
    }
}



// collect the set of prologue code for each edge e, where e->src is the last
// block of the prologue code
static void
collect_prologs(void)
{
    tcfg_edge_t	**path;
    int		i;

    path = (tcfg_edge_t **) calloc(prolog_size, sizeof(tcfg_edge_t *));
    CHECK_MEM(path);
    prologs = (code_link_t **) calloc(num_tcfg_edges, sizeof(code_link_t *));
    CHECK_MEM(prologs);

    for (i = 0; i < num_tcfg_edges; i++) {
	path[0] = tcfg_edges[i];
	trav_backward(i, path, 1, 0);
    }

    free(path);
}



// create an epilogue from the path
static int
new_epilog(int log_set, tcfg_edge_t **path, int path_len)
{
    int		i, k, num = 0, num1 = 0, m = 0, max_len, 
                hit_mlat = 0, set, tag, set_l2, tag_l2;
    tcfg_node_t	*bbi;
    Queue	queue;
    code_link_t	*elog;
    mas_inst_t	mas_inst;
    addr_t	sa;

    max_len  = max_elog_len[tcfg_edges[log_set]->src->id];
    memset(tmp_cs, 0, cache.ns * sizeof(mblk_tag_t));

    /* sudiptac :::: for level 2 cache */
    if (enable_il2cache || enable_ul2cache) {
        memset(tmp_cs_l2, 0, cache_l2.ns * sizeof(mblk_tag_t));
    }

    init_queue(&queue, sizeof(de_inst_t));
    for (i = 0; i < path_len; i++) {
	hit_mlat = 0;
	// copy code of e->dst
	bbi = path[i]->dst;
	sa = bbi->bb->sa;
	for (k = 0; (k < bbi->bb->num_inst) && (m < max_len); k++, m++) {
	    mas_inst.inst = &bbi->bb->code[k];
	    mas_inst.bbi_id = bbi->id;
	    assert(bbi->id >= 0);
	    mas_inst.mblk_id = MBLK_ID(sa, mas_inst.inst->addr);
            /* sudiptac ::: for level 2 cache analysis */
            mas_inst.mblk_id_l2 = MBLK_ID_L2(sa, mas_inst.inst->addr);
	    // bpred related
	    mas_inst.bp_flag = BP_CPRED;
	    // cache related
	    tag = TAG(mas_inst.inst->addr);
	    set = SET(mas_inst.inst->addr);
            /* sudiptac :::: for level 2 cache */
            tag_l2 = TAG_L2(mas_inst.inst->addr);
            set_l2 = SET_L2(mas_inst.inst->addr);

	    if (tmp_cs[set].valid == 0)
		mas_inst.ic_flag = IC_UNCLEAR;
	    else if (tmp_cs[set].tag == tag)
		mas_inst.ic_flag = IC_HIT;
	    else
		mas_inst.ic_flag = IC_MISS;
	    tmp_cs[set].valid = 1;
	    tmp_cs[set].tag = tag;

            /* sudiptac :::: for level 2 cache hierarchy */
            if (enable_il2cache || enable_ul2cache) {
                if (tmp_cs_l2[set_l2].valid == 0)
                    mas_inst.ic_flag_l2 = IC_UNCLEAR;
                else if (tmp_cs[set_l2].tag == tag_l2)
                    mas_inst.ic_flag_l2 = IC_HIT;
                else
                    mas_inst.ic_flag_l2 = IC_MISS;
                tmp_cs_l2[set_l2].valid = 1;
                tmp_cs_l2[set_l2].tag = tag_l2;
            }
            /******************************************************/
            mas_inst.dc_flag = mas_inst.dc_flag_l2 = DC_HIT;
            if (enable_scp_dcache || enable_ul2cache) {
                int iType = inst_type(mas_inst.inst);
                if (iType == INST_LOAD) {
                    mas_inst.dc_flag = DC_UNCLEAR;
                    if (enable_scp_dl2cache || enable_ul2cache)
                        mas_inst.dc_flag_l2 = DC_UNCLEAR;
                } else if (iType == INST_STORE) {
                    mas_inst.dc_flag = DC_STORE;
                    if (enable_scp_dl2cache || enable_ul2cache)
                        mas_inst.dc_flag_l2 = DC_STORE;
                } else {
                    mas_inst.dc_flag = DC_HIT;
                    if (enable_scp_dl2cache || enable_ul2cache)
                        mas_inst.dc_flag_l2 = DC_HIT;
                }
            } else {
                mas_inst.dc_flag = DC_HIT;
                mas_inst.dc_flag_l2 = DC_HIT;
            }
            /******************************************************/

	    enqueue(&queue, &mas_inst);
	    if  (max_inst_lat(mas_inst.inst) > 1) {
		num1 = num + k + 1;
		hit_mlat = 1;
	    }
	}
	num += k;
    }

    if ((num1 == 0) || (hit_mlat == 0)) {
	free_queue(&queue);
	return 0;
    }

    // copy code from tmporary storage to the new epilogue node
    elog = (code_link_t *) calloc(1, sizeof(code_link_t));
    CHECK_MEM(elog);
    elog->code = (mas_inst_t *) calloc(num1, sizeof(mas_inst_t));
    CHECK_MEM(elog->code);
    for (k = 0; k < num1; k++) {
	elog->code[k] = *((mas_inst_t *) dequeue(&queue));
    }
    elog->num_inst = num1;
    elog->next = epilogs[log_set];
    epilogs[log_set] = elog;

    free_queue(&queue);
    return 1;
}



static int
trav_forward(int log_set, tcfg_edge_t **path, int path_len, int code_len)
{
    tcfg_node_t	*bbi;
    tcfg_edge_t	*e;
    int		elog_created = 0, tmp;

    assert(path_len > 0);
    assert(code_len >= 0);

    bbi = path[path_len-1]->dst;
    code_len += bbi->bb->num_inst;
    if ((code_len >= max_elog_len[path[0]->src->id]) || (bbi->out == NULL)) {
	if (mlat_bbi[bbi->id] >= 0)
	    elog_created = new_epilog(log_set, path, path_len);
    } else {
	for (e = bbi->out; e != NULL; e = e->next_out) {
	    // TODO: FIXME: bodgy hack.
	    // if (path_len >= pipe_iwin_size)
            //    return 0;

	    path[path_len] = e;
	    tmp = trav_forward(log_set, path, path_len+1, code_len);
	    elog_created |= tmp;
	}
	if ((elog_created == 0) && (mlat_bbi[bbi->id] >= 0))
	    elog_created = new_epilog(log_set, path, path_len);
    }
    return elog_created;
}



// collect the set of epilogue code for each edge e, where e->dst is the first
// block of the epilogue code
static void
collect_epilogs(void)
{
    tcfg_edge_t	    **path;
    int		    i;

    path = (tcfg_edge_t **) calloc(pipe_iwin_size, sizeof(tcfg_edge_t *));
    CHECK_MEM(path);
    epilogs = (code_link_t **) calloc(num_tcfg_edges, sizeof(code_link_t *));
    CHECK_MEM(epilogs);

    for (i = 0; i < num_tcfg_edges; i++) {
	if (max_elog_len[tcfg_edges[i]->src->id] == 0)
	    continue;
	path[0] = tcfg_edges[i];
	trav_forward(i, path, 1, 0);
    }

    free(path);
}



static void
collect_bodies(void)
{
    int		i, k, num;
    tcfg_node_t	*bbi;

    num = tcfg[0]->bb->num_inst;
    start_body = (mas_inst_t *) calloc(num, sizeof(mas_inst_t));
    CHECK_MEM(start_body);
    for (k = 0; k < num; k++) {
	start_body[k].inst = &tcfg[0]->bb->code[k];
	start_body[k].bp_flag = BP_CPRED;
    }
    bodies = (mas_inst_t **) calloc(num_tcfg_edges, sizeof(mas_inst_t *));
    CHECK_MEM(bodies);
    for (i = 0; i < num_tcfg_edges; i++) {
	bbi = tcfg_edges[i]->dst;
	num = bbi->bb->num_inst;
	bodies[i] = (mas_inst_t *) calloc(num, sizeof(mas_inst_t));
	CHECK_MEM(bodies[i]);
	for (k = 0; k < num; k++) {
	    bodies[i][k].inst = &bbi->bb->code[k];
	    bodies[i][k].bbi_id = bbi->id;
	    assert(bbi->id >= 0);
	    bodies[i][k].bp_flag = BP_CPRED;
            /*Initialise (ic)dc_flag & (ic)dc_flag_l2*/
            bodies[i][k].dc_flag = bodies[i][k].ic_flag = IC_HIT;
            bodies[i][k].dc_flag_l2 = bodies[i][k].ic_flag_l2 = IC_HIT;
	}
    }
}



static void
set_body_hitmiss(int edge_id, int hm_id, int contextMask)
{
    int		    i, num, offset, offset_l2, mblk_id = 1, mblk_id_l2 = 1;
    int             offset_ul2, mblk_id_ul2 = 1;
    tcfg_node_t	    *bbi;
    loop_t	    *lp = NULL;

    assert(edge_id >= 0 && edge_id < num_tcfg_edges);

    bbi = tcfg_edges[edge_id]->dst; 
    //lp = bbi_hm_list[bbi->id][hm_id];
    num = bbi->bb->num_inst;
    if (num > 0) {
	bodies[edge_id][0].ic_flag = get_mblk_hitmiss(bbi, 0, lp);
    }

    /* sudiptac :::: set L2 cache CHMC flag */
    /* used for computing BB timing in add_inst (ss/ss_exegraph.c) */
    if (enable_il2cache)
            bodies[edge_id][0].ic_flag_l2 = get_mblk_hitmiss_l2(bbi, 0, lp);
    else if (enable_ul2cache)
            bodies[edge_id][0].ic_flag_l2 = get_mblk_hitmiss_ul2(bbi, 0, lp,
                            contextMask);

    for (i = 1; i < num; i++) {
	offset = CACHE_LINE(bbi->bb->code[i].addr);
	if (offset == 0) {
	    bodies[edge_id][i].ic_flag = get_mblk_hitmiss(bbi, mblk_id, lp);
	    mblk_id++;
	}
        if (enable_il2cache) {
            offset_l2 = CACHE_LINE_L2(bbi->bb->code[i].addr);
            //printf("offset=%d %d\n",offset_l2,cache_l2.l_msk);
            if (offset_l2 == 0) {
                /* sudiptac :::: set L2 cache CHMC flag */
                bodies[edge_id][i].ic_flag_l2 = get_mblk_hitmiss_l2(bbi,
                                                mblk_id_l2, lp);
                mblk_id_l2++;
            }
        } else if (enable_ul2cache) {
            offset_ul2 = CACHE_LINE_L2(bbi->bb->code[i].addr);
            //printf("offset=%d %d\n",offset_ul2,cache_l2.l_msk);
            if (offset_ul2 == 0) {
                bodies[edge_id][i].ic_flag_l2 = get_mblk_hitmiss_ul2(bbi,
                                                mblk_id_ul2, lp, contextMask);
                mblk_id_ul2++;
            }
        }
    }
}

int get_context_forward(int src_ctx, int src_length, int dst_legnth) {
        while (src_length < dst_legnth) {
                src_ctx = src_ctx << 1;
                src_length++;
        }
        while (src_length > dst_legnth) {
                src_ctx = src_ctx >> 1;
                src_length--;
        }
        return src_ctx;
}

int get_context_backward(int dst_ctx, int src_length, int dst_length) {
        while (src_length < dst_length) {
                dst_ctx = dst_ctx >> 1;
                dst_length--;
        }
        while (src_length > dst_length) {
                dst_ctx = (dst_ctx << 1) | 1;
                dst_length++;
        }
        return dst_ctx;
}

static void set_body_data_cache_hitmiss(int edge_id, int contextMask) {
        tcfg_edge_t* edge = tcfg_edges[edge_id];
        tcfg_node_t* src = edge->src;
        tcfg_node_t* dst = edge->dst;

        int i;
        for (i = 0; i < dst->bb->num_inst; i++) {
                int iType = inst_type((bodies[edge_id][i]).inst);
                if (iType == INST_LOAD) {
                        int srcContextBitLength = numberOfLoop[src->id] - 1;
                        int dstContextBitLength = numberOfLoop[dst->id] - 1;
                        int dstContext = get_context_forward(contextMask,
                                        srcContextBitLength, dstContextBitLength);
                        loop_t* inner_lp = loop_map[dst->id];
                        loop_t* ps_lp = NULL;
                        ps_lp = (loop_t*) scp_psloop_dl(&bodies[edge_id][i], 1);

                        if (ps_lp == NULL) {
                                bodies[edge_id][i].dc_flag = DC_UNCLEAR;
                        } else {
                                int distance = loop_dist(inner_lp, ps_lp);
                                if (distance < 0) {
#if 0
                                        printf("edge %d_%d\n", tcfg_edges[edge_id]->src->id,
                                                        tcfg_edges[edge_id]->dst->id);
                                        if (inner_lp == NULL
                                        )
                                        printf("inner_lp:NULL\n");
                                        else
                                        printf("inner_lp:%d\n", inner_lp->id);
                                        if (ps_lp == NULL) {
                                                printf("ps_lp:NULL\n");
                                        } else
                                        printf("ps_lp:%d\n", ps_lp->id);
                                        printf("BUGGG!!!!!???? %d\n", distance);
#endif
                                        exit(1);
                                }
                                int ps_ctx = dstContext & ((1 << distance) - 1);
                                if (ps_ctx == 0)
                                        bodies[edge_id][i].dc_flag = DC_MISS;
                                else
                                        bodies[edge_id][i].dc_flag = DC_HIT;
                        }

                        if (enable_scp_dl2cache || enable_ul2cache) {
                                loop_t* ps_lp_l2 = (loop_t*) scp_psloop_dl(&bodies[edge_id][i],
                                                2);
                                if (ps_lp_l2 == NULL) {
                                        bodies[edge_id][i].dc_flag_l2 = DC_UNCLEAR;
                                } else {
                                        int distance = loop_dist(inner_lp, ps_lp_l2);
                                        if (distance < 0) {
                                                printf("BUGGG!!!!!\n");
                                                exit(1);
                                        }
                                        int ps_ctx = dstContext & ((1 << distance) - 1);
                                        if (ps_ctx == 0)
                                                bodies[edge_id][i].dc_flag_l2 = DC_MISS;
                                        else
                                                bodies[edge_id][i].dc_flag_l2 = DC_HIT;
                                }
                        }

                } else if (iType == INST_STORE) {
                        bodies[edge_id][i].dc_flag = DC_STORE;
                        if (enable_scp_dl2cache || enable_ul2cache)
                                bodies[edge_id][i].dc_flag_l2 = DC_STORE;
                } else {
                        bodies[edge_id][i].dc_flag = DC_HIT;
                        if (enable_scp_dl2cache || enable_ul2cache)
                                bodies[edge_id][i].dc_flag_l2 = DC_HIT;
                }
        }
}

static void set_prolog_data_cache_hitmiss(int edge_id, mas_inst_t* code,
                int num_inst, int contextMask) {
        if (num_inst <= 0)
                return;
        int context = contextMask;
        int dst = tcfg_edges[edge_id]->src->id;
        int src = code[num_inst - 1].bbi_id;
        //printf("EDGE %d_%d context %d:\n", src, dst, contextMask);
        int i;
        for (i = num_inst - 1; i >= 0; i--) {
                src = code[i].bbi_id;
                int src_ctx_length = numberOfLoop[src] - 1;
                int dst_ctx_length = numberOfLoop[dst] - 1;
                context = get_context_backward(context, src_ctx_length, dst_ctx_length);
                //      printf("0x%x bbi_id:%d ctx:%d", code[i].inst->addr, code[i].bbi_id,
                //                      context);
                int iType = inst_type(code[i].inst);
                if (iType == INST_LOAD) {
                        loop_t* lp = loop_map[src];
                        loop_t* ps_lp = (loop_t*) scp_psloop_dl(&code[i], 1);
                        if (ps_lp == NULL) {
                                code[i].dc_flag = DC_UNCLEAR;
                        } else {
                                int distantce = loop_dist(ps_lp, lp);
                                if (distantce < 0) {
                                        printf("BUGGG\n");
                                        exit(1);
                                }
                                int ps_ctx = context & ((1 << distantce) - 1);
                                if (ps_ctx == 0)
                                        code[i].dc_flag = DC_MISS;
                                else
                                        code[i].dc_flag = DC_HIT;
                        }
                        if (enable_scp_dl2cache || enable_ul2cache) {
                                loop_t* ps_lp_l2 = (loop_t*) scp_psloop_dl(&code[i], 2);
                                if (ps_lp_l2 == NULL) {
                                        code[i].dc_flag_l2 = DC_UNCLEAR;
                                } else {
                                        int distance = loop_dist(lp, ps_lp_l2);
                                        if (distance < 0) {
                                                printf("BUGGGG\n");
                                                exit(1);
                                        }
                                        int ps_ctx = context & ((1 << distance) - 1);
                                        if (ps_ctx == 0)
                                                code[i].dc_flag_l2 = DC_MISS;
                                        else
                                                code[i].dc_flag_l2 = DC_HIT;
                                }
                        }
                } else if (iType == INST_STORE) {
                        code[i].dc_flag = DC_STORE;
                        if (enable_scp_dl2cache || enable_ul2cache)
                                code[i].dc_flag_l2 = DC_STORE;
                } else {
                        code[i].dc_flag = DC_HIT;
                        if (enable_scp_dl2cache || enable_ul2cache)
                                code[i].dc_flag_l2 = DC_STORE;
                }
                dst = src;
                //      printf(" dc_flag: %d\n", code[i].dc_flag);
        }
}

static void set_epilog_data_cache_hitmiss(int edge_id, mas_inst_t* code,
                int num_inst, int contextMask) {
        if (num_inst <= 0)
                return;
        tcfg_node_t* src_node = tcfg_edges[edge_id]->src;
        int src_id = src_node->id;
        int src_ctx_length = numberOfLoop[src_id] - 1;
        tcfg_node_t* dst_node = tcfg_edges[edge_id]->dst;
        int dst_id = dst_node->id;
        int dst_ctx_length = numberOfLoop[dst_id] - 1;
        int context = get_context_forward(contextMask, src_ctx_length,
                        dst_ctx_length);

        src_id = dst_id;
        int i;
        for (i = 0; i < num_inst; i++) {
                dst_id = code[i].bbi_id;
                src_ctx_length = numberOfLoop[src_id] - 1;
                dst_ctx_length = numberOfLoop[dst_id] - 1;
                context = get_context_forward(context, src_ctx_length, dst_ctx_length);
                int iType = inst_type(code[i].inst);
                if (iType == INST_LOAD) {
                        loop_t* lp = loop_map[dst_id];
                        loop_t* ps_lp = (loop_t*) scp_psloop_dl(&code[i], 1);
                        if (ps_lp == NULL) {
                                code[i].dc_flag = DC_UNCLEAR;
                        } else {
                                int distance = loop_dist(ps_lp, lp);
                                if (distance < 0) {
                                        printf("BUGGGG\n");
                                        exit(1);
                                }
                                int ps_ctx = context & ((1 << distance) - 1);
                                if (ps_ctx == 0)
                                        code[i].dc_flag = DC_MISS;
                                else
                                        code[i].dc_flag = DC_HIT;
                        }
                        if (enable_scp_dl2cache || enable_ul2cache) {
                                loop_t* ps_lp_l2 = (loop_t*) scp_psloop_dl(&code[i], 2);
                                if (ps_lp_l2 == NULL) {
                                        code[i].dc_flag_l2 = DC_UNCLEAR;
                                } else {
                                        int distance = loop_dist(lp, ps_lp_l2);
                                        if (distance < 0) {
                                                printf("BUGGGG\n");
                                                exit(1);
                                        }
                                        int ps_ctx = context & ((1 << distance) - 1);
                                        if (ps_ctx == 0)
                                                code[i].dc_flag_l2 = DC_MISS;
                                        else
                                                code[i].dc_flag_l2 = DC_HIT;
                                }
                        }
                } else if (iType == INST_STORE) {
                        code[i].dc_flag = DC_STORE;
                        if (enable_scp_dl2cache || enable_ul2cache)
                                code[i].dc_flag_l2 = DC_STORE;
                } else {
                        code[i].dc_flag = DC_HIT;
                        if (enable_scp_dl2cache || enable_ul2cache)
                                code[i].dc_flag_l2 = DC_HIT;
                }
                src_id = dst_id;
        }
}

static void
init_pa(void)
{
    prolog_size = pipe_ibuf_size + pipe_iwin_size;
}



static void
alloc_est_units(void)
{
    int		i, num_hm;

    cpred_times = (int **) calloc(num_tcfg_edges, sizeof(int *));
    mpred_times = (int **) calloc(num_tcfg_edges, sizeof(int *));

    extend_cpred_times = (int ***) calloc(num_tcfg_edges, sizeof(int**));
    numberOfLoop = (int*) calloc(num_tcfg_nodes, sizeof(int*));
    numberofContext = (int*) calloc(num_tcfg_nodes, sizeof(int*));

    CHECK_MEM(cpred_times);
    CHECK_MEM(mpred_times);

    for (i = 0; i < num_tcfg_nodes; i++) {
        loop_t* lp = (loop_t*) loop_map[tcfg[i]->id];
        numberOfLoop[i] = 0;
        while (lp != NULL) {
            numberOfLoop[i]++;
            lp = lp->parent;
        }
        numberofContext[i] = (1 << (numberOfLoop[i] - 1));
    }

    start_time = 0;
    for (i = 0; i < num_tcfg_edges; i++) {
	num_hm = 1;
	cpred_times[i] = (int *) calloc(num_hm, sizeof(int));
	CHECK_MEM(cpred_times);
	if (cond_bbi(tcfg_edges[i]->src)) {
	    mpred_times[i] = (int *) calloc(num_hm, sizeof(int));
	    CHECK_MEM(mpred_times);
	}
        int size = numberofContext[tcfg_edges[i]->src->id];
        if (enable_scp_dcache == 0)
            size = 1;
        //num_ex_cpred_times[i] = size*num_hm;
        extend_cpred_times[i] = (int**) calloc(size, sizeof(int*));
        int v;
        for (v = 0; v < numberofContext[tcfg_edges[i]->src->id]; v++) {
            extend_cpred_times[i][v] = (int*) calloc(num_hm, sizeof(int));
        }
    }
}



// edge_id: tcfg edge id;
// hm_id: id in the set of hit/miss combinations of tcfg_edge[edge_id]->dst
// bp: BP_CORRECT or BP_MISPRED
static void
ctx_unit_time(int edge_id, int bp, int contextMask)
{
    int		    num_p, num_e, num_b, t, *t_cpred, *t_mpred;
    tcfg_node_t	    *bbi;
    tcfg_edge_t	    *e;
    code_link_t	    *plog, *elog;
    int		    unit_estimated;
    loop_t	    *lp;

    t_cpred = &cpred_times[edge_id][0];
    t_mpred = &mpred_times[edge_id][0];
    //int* t_context = &extend_cpred_times[edge_id][contextMask][0];

    if (enable_icache)
        set_body_hitmiss(edge_id, 0, contextMask);
    if (enable_scp_dcache) 
        set_body_data_cache_hitmiss(edge_id, contextMask);

    bbi = tcfg_edges[edge_id]->dst;
    num_b = bbi->bb->num_inst;

    if (enable_icache)
	lp = bbi_hm_list[bbi->id][0];
    else
	lp = NULL;

    for (plog = prologs[edge_id]; plog != NULL; plog = plog->next) {
	num_p = plog->num_inst;
	if (num_p == 0)
	    continue;

	if (bpred_scheme != NO_BPRED && bp == BP_CPRED)
	    num_p -= num_plog_trunc[edge_id];
	unit_estimated = 0;
	for (e = bbi->out; e != NULL; e = e->next_out) {
	    for (elog = epilogs[e->id]; elog != NULL; elog = elog->next) {
		num_e = elog->num_inst;
		if (num_e == 0)
		    continue;

                /****************************************/
                if (enable_scp_dcache) {
                    set_prolog_data_cache_hitmiss(edge_id, plog->code, num_p, contextMask);
                    set_epilog_data_cache_hitmiss(edge_id, elog->code, num_e, contextMask);
                }
		create_egraph(plog->code, num_p, elog->code, num_e,
			bodies[edge_id], num_b, bp, lp);
		t = est_egraph();
		if ((bp == BP_CPRED) && (t > *t_cpred))
		    *t_cpred = t;
		if ((bp == BP_MPRED) && (t > *t_mpred))
		    *t_mpred = t;
		unit_estimated = 1;
	    }
	}
	if (unit_estimated == 1)
	    continue;
        if (enable_scp_dcache) {
            set_prolog_data_cache_hitmiss(edge_id, plog->code, num_p,
                                        contextMask);
        }
	create_egraph(plog->code, num_p, NULL, 0, bodies[edge_id], num_b, bp, lp);
	t = est_egraph();
	if ((bp == BP_CPRED) && (t > *t_cpred))
	    *t_cpred = t;
	if ((bp == BP_MPRED) && (t > *t_mpred))
	    *t_mpred = t;
    }
}



static void
est_start_unit(void)
{
    int		    num_b, num_e, offset, offset_l2, i, t, unit_estimated = 0;
    int             offset_ul2;
    tcfg_node_t	    *bbi = tcfg[0];
    tcfg_edge_t	    *e;
    code_link_t	    *elog;

    num_b = tcfg[0]->bb->num_inst;
    start_body[0].ic_flag = IC_MISS;
    /* sudiptac :::: for level 2 cache */
    /* set hit-miss flag for the entry basic block */
    if (enable_il2cache || enable_ul2cache)
        start_body[0].ic_flag_l2 = IC_MISS;

    for (i = 1; i < num_b; i++) {
	offset = CACHE_LINE(bbi->bb->code[i].addr);
	if (offset == 0)
	    start_body[i].ic_flag = IC_MISS;
        if (enable_il2cache) {
            /* sudiptac :::: for level 2 cache */
            offset_l2 = CACHE_LINE_L2(bbi->bb->code[i].addr);
            if (offset_l2 == 0)
                start_body[i].ic_flag_l2 = IC_MISS;
        } else if (enable_ul2cache) {
            offset_ul2 = CACHE_LINE_L2(bbi->bb->code[i].addr);
            if (offset_ul2 == 0)
                start_body[i].ic_flag_l2 = IC_MISS;
        }
    }

    /***************** for data cache analysis *******************/
    if (enable_scp_dcache) {
        for (i = 0; i < num_b; i++) {
            int iType = inst_type(start_body[i].inst);
            if (iType == INST_LOAD) {
                start_body[i].dc_flag = DC_UNCLEAR;
                if (enable_scp_dl2cache || enable_ul2cache)
                    start_body[i].dc_flag_l2 = DC_UNCLEAR;
            } else if (iType == INST_STORE) {
                start_body[i].dc_flag = DC_STORE;
                if (enable_scp_dl2cache || enable_ul2cache)
                    start_body[i].dc_flag_l2 = DC_STORE;
            } else {
                start_body[i].dc_flag = DC_HIT;
                if (enable_scp_dl2cache || enable_ul2cache)
                    start_body[i].dc_flag_l2 = DC_HIT;
            }
        }
    }
    /*************************************************************/

    for (e = bbi->out; e != NULL; e = e->next_out) {
	for (elog = epilogs[e->id]; elog != NULL; elog = elog->next) {
	    num_e = elog->num_inst;
	    if (num_e == 0)
		continue;
	    create_egraph(NULL, 0, elog->code, num_e, start_body, num_b,
		    BP_CPRED, loops[0]);
	    t = est_egraph();
	    if (t > start_time)
		start_time = t;
	    unit_estimated = 1;
	}
    }

    if (unit_estimated == 0) {
	create_egraph(NULL, 0, NULL, 0, start_body, num_b, BP_CPRED, loops[0]);
	t = est_egraph();
	if (t > start_time)
	    start_time = t;
    }
}



static void
est_units(void)
{
    int		    edge_id, est_mispred;
    tcfg_edge_t	    *e;

    alloc_est_units();
    est_start_unit();

    for (edge_id = 0; edge_id < num_tcfg_edges; edge_id++) {
        e = tcfg_edges[edge_id];
        tcfg_node_t* src = e->src;

        if ((bpred_scheme != NO_BPRED) && (cond_bbi(e->src)))
            est_mispred = 1;
        else
            est_mispred = 0;
        int contextMask = 0;
        for (contextMask = 0; contextMask < numberofContext[src->id];
                                contextMask++) {
             ctx_unit_time(edge_id, BP_CPRED, contextMask);
             if (est_mispred)
                 ctx_unit_time(edge_id, BP_MPRED, contextMask);
        }
    }
}






// handling cache misses caused by loop-exit mispreds
tcfg_elink_t    ***mp_affected_sets;
int		    ***mp_times;

// temporary variables that become useless after affected sets are collected
int		**mp_set_tags;
int		*num_mp_set_tags;



static void
get_loop_affected_sets(int lp_id, tcfg_edge_t *mp_edge, int num_inst)
{
    tcfg_edge_t		*edge;
    tcfg_elink_t	*elink;
    int			offset, i, k, set, tag;

    if (mp_edge == mp_edge->src->out)
	edge = mp_edge->next_out;
    else
	edge = mp_edge->src->out;
    if (edge->flags == 1)
	return;

    for (i = num_inst; i < num_mp_insts[edge->id]; i++) {
	offset = CACHE_LINE(mp_insts[edge->id][i]->addr);
	if (offset == 0)
	    break;
    }
    memset(num_mp_set_tags, 0, cache.ns * sizeof(int));
    for (; i < num_mp_insts[edge->id]; i++) {
	set = SET(mp_insts[edge->id][i]->addr);
	if (num_mp_set_tags[set] == cache.na)
	    continue;
	tag = TAG(mp_insts[edge->id][i]->addr);
	if (num_mp_set_tags[set] == 0) {
	    mp_set_tags[set][0] = tag;
	    num_mp_set_tags[set] = 1;
	} else {
	    for (k = 0; k < num_mp_set_tags[set]; k++) {
		if (tag == mp_set_tags[set][k])
		    break;
	    }
	    if (k == num_mp_set_tags[set]) {
		mp_set_tags[set][k] = tag;
		num_mp_set_tags[set]++;
	    }
	}
    }

    for (set = 0; set < cache.ns; set++) {
	i = num_mblk_conflicts[lp_id][set];
	if (i > cache.na)
	    continue;
	if ((num_mp_set_tags[set] + i) > cache.na) {
	    elink = (tcfg_elink_t *) calloc(1, sizeof(tcfg_elink_t *));
	    elink->edge = edge;
	    elink->next = mp_affected_sets[lp_id][set];
	    mp_affected_sets[lp_id][set] = elink;
	}
    }
}



static void
find_cond_exit(int lp_id, tcfg_edge_t *edge, int num_inst)
{
    if (cond_bbi(edge->src)) {
	get_loop_affected_sets(lp_id, edge, num_inst);
    } else {
	num_inst += edge->src->bb->num_inst;
	if (num_inst >= (pipe_ibuf_size + pipe_iwin_size - 1))
	    return;
	for (edge = edge->src->in; edge != NULL; edge = edge->next_in)
	    find_cond_exit(lp_id, edge, num_inst);
    }
}



// for each loop level, collect cache sets which are affected in terms of cache
// misses
static void
collect_affected_sets(void)
{
    tcfg_elink_t    *elink;
    loop_t	    *lp;
    int		    lp_id, set;

    mp_affected_sets = (tcfg_elink_t ***) calloc(num_tcfg_loops, sizeof(tcfg_elink_t **));
    for (lp_id = 1; lp_id < num_tcfg_loops; lp_id++)
	mp_affected_sets[lp_id] = (tcfg_elink_t **) calloc(cache.ns, sizeof(tcfg_elink_t *));

    mp_set_tags = (int **) calloc(cache.ns, sizeof(int *));
    for (set = 0; set < cache.ns; set++)
	mp_set_tags[set] = (int *) calloc(cache.na, sizeof(int));
    num_mp_set_tags = (int *) calloc(cache.ns, sizeof(int));
    
    for (lp_id = 1; lp_id < num_tcfg_loops; lp_id++) {
	lp = loops[lp_id];
	for (elink = lp->exits; elink != NULL; elink = elink->next)
	    find_cond_exit(lp_id, elink->edge, 0);
	clear_tcfg_edge_flags();
    }

    for (set = 0; set < cache.ns; set++)
	free(mp_set_tags[set]);
    free(mp_set_tags);
    free(num_mp_set_tags);
}



static void
mp_set_body_hitmiss(int edge_id, int hm_id, int set)
{
    int		    i, num, offset, mblk_id = 1, set1;
    tcfg_node_t	    *bbi;
    loop_t	    *lp;

    bbi = tcfg_edges[edge_id]->dst; 
    lp = bbi_hm_list[bbi->id][hm_id];
    num = bbi->bb->num_inst;
    set1 = SET(bbi->bb->sa);
    if (set1 == set)
	bodies[edge_id][0].ic_flag = IC_UNCLEAR;
    else
	bodies[edge_id][0].ic_flag = get_mblk_hitmiss(bbi, 0, lp);
    for (i = 1; i < num; i++) {
	offset = CACHE_LINE(bbi->bb->code[i].addr);
	if (offset == 0) {
	    set1 = SET(bbi->bb->code[i].addr);
	    if (set1 == set)
		bodies[edge_id][i].ic_flag = IC_UNCLEAR;
	    else
		bodies[edge_id][i].ic_flag = get_mblk_hitmiss(bbi, mblk_id, lp);
	    mblk_id++;
	}
    }
}



static void
ctx_mpmiss_time(int edge_id, int hm_id, int set, int bp)
{
    int		    num_p, num_e, num_b, t, *t_mp, unit_estimated;
    tcfg_node_t	    *bbi;
    tcfg_edge_t	    *e;
    code_link_t	    *plog, *elog;
    loop_t	    *lp;

    t_mp = &mp_times[edge_id][hm_id][set];
    if (enable_icache)
	mp_set_body_hitmiss(edge_id, hm_id, set);
    bbi = tcfg_edges[edge_id]->dst;
    num_b = bbi->bb->num_inst;

    if (enable_icache)
	lp = bbi_hm_list[bbi->id][hm_id];
    else
	lp = NULL;

    for (plog = prologs[edge_id]; plog != NULL; plog = plog->next) {
	num_p = plog->num_inst;
	if (num_p == 0)
	    continue;

	if (bpred_scheme != NO_BPRED && bp == BP_CPRED)
	    num_p -= num_plog_trunc[edge_id];
	unit_estimated = 0;
	for (e = bbi->out; e != NULL; e = e->next_out) {
	    for (elog = epilogs[e->id]; elog != NULL; elog = elog->next) {
		num_e = elog->num_inst;
		if (num_e == 0)
		    continue;
		create_egraph(plog->code, num_p, elog->code, num_e,
			bodies[edge_id], num_b, bp, lp);
		t = est_egraph();
		if (t > *t_mp)
		    *t_mp = t;
		unit_estimated = 1;
	    }
	}
	if (unit_estimated == 1)
	    continue;

	create_egraph(plog->code, num_p, NULL, 0, bodies[edge_id], num_b, bp, lp);
	t = est_egraph();
	if (t > *t_mp)
	    *t_mp = t;
    }
}



static void
est_mpmiss_times(void)
{
    int		    edge_id, num_hm, hm, bp, set;
    tcfg_node_t	    *bbi;
    tcfg_edge_t	    *e;
    loop_t	    *lp;

    mp_times = (int ***) calloc(num_tcfg_edges, sizeof(int **));

    for (edge_id = 0; edge_id < num_tcfg_edges; edge_id++) {
	e = tcfg_edges[edge_id];
	num_hm = num_hit_miss[e->dst->id];
	mp_times[edge_id] = (int **) calloc(num_hm, sizeof(int *));
	bbi = e->dst;
	if (cond_bbi(e->src))
	    bp = BP_MPRED;
	else
	    bp = BP_CPRED;
	for (hm = 0; hm < num_hm; hm++) {
	    mp_times[edge_id][hm] = (int *) calloc(cache.ns, sizeof(int));
	    lp = bbi_hm_list[bbi->id][hm];
	    if ((lp == NULL) || (lp->id == 0))
		continue;
	    for (set = 0; set < cache.ns; set++) {
		if (mp_affected_sets[lp->id][set] != NULL) {
		    ctx_mpmiss_time(edge_id, hm, set, bp);
		}
	    }
	}
    }
}



// estimate contributions of mispred raised cache misses to execution time
static void
handle_mpmiss(void)
{
    collect_affected_sets();
    est_mpmiss_times();
}



void
pipe_analysis()
{
    tmp_cs = (mblk_tag_t *) calloc(cache.ns, sizeof(mblk_tag_t));
    CHECK_MEM(tmp_cs);

    /* sudiptac :::: for level 2 cache analysis */
    if (enable_il2cache || enable_ul2cache) {
        tmp_cs_l2 = (mblk_tag_t *) calloc(cache_l2.ns, sizeof(mblk_tag_t));
        CHECK_MEM(tmp_cs_l2);
    }

    printf(" Step 1\n");
    init_pa();
    printf(" Step 2\n");
    set_mlat_bbi();
    printf(" Step 3\n");
    bound_elog_len();
    printf(" Step 4\n");
    if (bpred_scheme != BP_NONE)
	find_mlat_mpinst();

    printf(" Step 5\n");
    collect_bodies();
    printf(" Step 6\n");
    collect_prologs();
    printf(" Step 7\n");
    collect_epilogs();
    printf(" Step 8\n");
    est_units();

    printf(" Step 9\n");
    if (enable_icache && (bpred_scheme != NO_BPRED))
	handle_mpmiss();

    free(mlat_bbi);
    free(tmp_cs);
}






static void UNUSED
dump_xlogs(code_link_t **xlogs)
{
    tcfg_node_t	    *src, *dst;
    int		    i, k;
    code_link_t	    *log;
    mas_inst_t	    *mas_inst;

    for (i = 0; i < num_tcfg_edges; i++) {
	src = tcfg_edges[i]->src;
	dst = tcfg_edges[i]->dst;
	printf("\nedge: %d.%d -> %d.%d", bbi_pid(src), bbi_bid(src),
		bbi_pid(dst), bbi_bid(dst));
	for (log = xlogs[i]; log != NULL; log = log->next) {
	    for (k = 0; k < log->num_inst; k++) {
		mas_inst = &log->code[k];
		if ((k & 7) == 0)
		    printf("\n    %x", mas_inst->inst->addr);
		else
		    printf("  %x", mas_inst->inst->addr);
		if (mas_inst->bp_flag == BP_MPRED)
		    printf("/M");
		else if (mas_inst->bp_flag == BP_UNCLEAR)
		    printf("/U");
		else
		    printf("/C");
		if (mas_inst->ic_flag == IC_MISS)
		    printf("M");
		else if (mas_inst->ic_flag == IC_UNCLEAR)
		    printf("U");
		else
		    printf("H");
	    }
	    printf("\n    -------------------------------------------");
	    printf("-------------------------------------------\n");
	}
    }
}



void
dump_units_times()
{
    tcfg_edge_t	*e;
    int		edge_id, hm, num_hm;

    printf("dump timing estimates for basic blocks\n");
    for (edge_id = 0; edge_id < num_tcfg_edges; edge_id++) {
	e = tcfg_edges[edge_id];
	printf("%d.%d -> %d.%d\n",
		bbi_pid(e->src), bbi_bid(e->src), bbi_pid(e->dst), bbi_bid(e->dst));
	if (enable_icache) {
	    num_hm = num_hit_miss[tcfg_edges[edge_id]->dst->id];
	} else
	    num_hm = 1;
	for (hm = 0; hm < num_hm; hm++) {
	    printf("    hm[%d]: %d", hm, cpred_times[edge_id][hm]);
	    if ((bpred_scheme != NO_BPRED) && cond_bbi(e->src))
		printf(" %d(m)", mpred_times[edge_id][hm]);
	    printf("\n");
	}
    }
    printf("\n");
}



static void UNUSED
dump_unit_time(int edge_id, int hm, int bp)
{
    int		t;
    tcfg_edge_t	*e = tcfg_edges[edge_id];

    if (bp == BP_CPRED)
	t = cpred_times[edge_id][hm];
    else
	t = mpred_times[edge_id][hm];
    printf("    %d.%d -> %d.%d (hm:%d bp:%d): %d\n",
	    bbi_pid(e->src), bbi_bid(e->src), bbi_pid(e->dst), bbi_bid(e->dst),
	    hm, bp, t);
}



static void UNUSED
dump_edge_mp_times(int edge_id, int hm)
{
    int		*t, set;
    tcfg_edge_t	*e = tcfg_edges[edge_id];

    t = mp_times[edge_id][hm];
    printf("    %d.%d -> %d.%d (hm:%d): ",
	    bbi_pid(e->src), bbi_bid(e->src), bbi_pid(e->dst), bbi_bid(e->dst), hm);
    for (set = 0; set < cache.ns; set++) {
	if (t[set] != 0)
	    printf(" s[%d]=%d", set, t[set]);
    }
    printf("\n");
}



void
dump_mp_times()
{
    tcfg_edge_t	*e;
    loop_t	*lp;
    int		edge_id, hm, num_hm, set, *t;

    printf("dump mispred timing estimates for basic blocks\n");
    for (edge_id = 0; edge_id < num_tcfg_edges; edge_id++) {
	e = tcfg_edges[edge_id];
	printf("%d.%d -> %d.%d\n",
		bbi_pid(e->src), bbi_bid(e->src), bbi_pid(e->dst), bbi_bid(e->dst));
	num_hm = num_hit_miss[tcfg_edges[edge_id]->dst->id];
	for (hm = 0; hm < num_hm; hm++) {
	    lp = bbi_hm_list[e->dst->id][hm];
	    if (lp == NULL)
		continue;
	    printf("    hm[%d]:", hm);
	    t = mp_times[edge_id][hm];
	    for (set = 0; set < cache.ns; set++) {
		if (t[set] != 0)
		    printf(" s[%x]=%d", set, t[set]);
	    }
	    printf("\n");
	}
    }
    printf("\n");
}



void
dump_plog_stats()
{
    int		    i;
    code_link_t	    *p;
    int		    len_stat[48];

    printf("dump prolog len statistics\n");
    for (i = 0; i < 48; i++)
	len_stat[i] = 0;

    for (i = 0; i < num_tcfg_edges; i++) {
	for (p = prologs[i]; p != NULL; p = p->next) {
	    len_stat[p->num_inst]++;
	}
    }

    for (i = 0; i < 48; i++) {
	if (len_stat[i] > 0)
	    printf("len[%d]: %d\n", i, len_stat[i]);

    }
}



void
dump_elog_stats()
{
    int		    i;
    code_link_t	    *p;
    int		    len_stat[32];

    printf("dump epilog len statistics\n");
    for (i = 0; i < 32; i++)
	len_stat[i] = 0;

    for (i = 0; i < num_tcfg_edges; i++) {
	for (p = epilogs[i]; p != NULL; p = p->next) {
	    len_stat[p->num_inst]++;
	}
    }

    for (i = 0; i < 32; i++) {
	if (len_stat[i] > 0)
	    printf("len[%d]: %d\n", i, len_stat[i]);

    }
}



void
dump_context_stats()
{
    code_link_t	    *p;
    tcfg_edge_t	    *e;
    int		    i, *num_plogs, *num_elogs, num_ctxs, total = 0;

    dump_plog_stats();
    dump_elog_stats();

    num_plogs = (int *) calloc(num_tcfg_nodes, sizeof(int));
    num_elogs = (int *) calloc(num_tcfg_nodes, sizeof(int));

    printf("dump context statistics\n");
    for (i = 0; i < num_tcfg_nodes; i++) {
	for (e = tcfg[i]->in; e != NULL; e = e->next_in) {
	    for (p = prologs[e->id]; p != NULL; p = p->next)
		num_plogs[i]++;
	}
	for (e = tcfg[i]->out; e != NULL; e = e->next_out) {
	    for (p = epilogs[e->id]; p != NULL; p = p->next)
		num_elogs[i]++;
	}
	num_ctxs = max(num_plogs[i], 1) * max(num_elogs[i], 1);
	printf("%3d: (%3d, %3d/%2d) %6d\n", i, num_plogs[i], num_elogs[i], max_elog_len[i], num_ctxs);
	total += num_ctxs;
    }
    printf("\n-----------------------\ntotal: %d\n", total);

    free(num_plogs);
    free(num_elogs);
}



void
dump_elog_len()
{
    int		    i;

    printf("dump max_elog_len\n");
    for (i = 0; i < num_tcfg_nodes; i++) {
	printf("bbi[%d]/%x: %d\n", i, tcfg[i]->bb->sa, max_elog_len[i]);
    }
}



void
dump_mlat_mpinst()
{
    int		    i;

    printf("dump mlat_mpinst\n");
    for (i = 0; i < num_tcfg_edges; i++) {
	printf("edge[%d->%d]/%x->%x: %d\n", tcfg_edges[i]->src->id,
		tcfg_edges[i]->dst->id, tcfg_edges[i]->src->bb->sa,
		tcfg_edges[i]->dst->bb->sa, mlat_mpinst[i]);
    }
}
