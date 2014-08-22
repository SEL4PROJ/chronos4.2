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
 * $Id: loops.c,v 1.2 2006/06/24 08:54:57 lixianfe Exp $
 *
 * traverse tcfg to form a loop hierarchy and associate each bbi its loop level
 *
 *  v4.1:
 *      _ add loop operation: isPredecessor, cmpLpOrder 
 *      _ support dynamic loop bound
 *
 *  v4.0: as in Chronos-4.0 distribution
 *
 ******************************************************************************/


#include <stdlib.h>
#include "common.h"
#include "loops.h"



#if 0
#define D(x...) printf(x)
#else
#define D(x...) do { } while(0)
#endif

#define	loop_bbb_idx(id)    ((id) - lp_bbb_offset - num_bfg_nodes)

extern int	    num_tcfg_nodes;
extern int	    num_tcfg_edges;
extern tcfg_node_t  **tcfg;
extern tcfg_edge_t  **tcfg_edges;

loop_t	    **loops;
int	    num_tcfg_loops;
loop_t	    **loop_map;		// bbi => loop
loop_t	    ***loop_comm_ances;	// loop_comm_ances[lp1, lp2]

static void
loop_set_init(loop_set_t *set)
{
    set->num_loops = 0;
    set->num_alloced = 0;
    set->loop_ids = NULL;
}

static void
loop_set_free(loop_set_t *set)
{
    free(set->loop_ids);
    loop_set_init(set); // clear out values.
}

static int
loop_set_size(loop_set_t *set)
{
    return set->num_loops;
}

static void
loop_set_add(loop_set_t *set, int loop_id)
{
    // Add loop id, and maintain sorted order, sorted by
    // loops[loop_id]->head->flags, which stores the sequence number (in
    // discovery order).

    // Firstly check allocation size, ensuring we have enough space.
    if (set->num_loops + 1 > set->num_alloced) {
        if (set->num_alloced > 0)
            set->num_alloced *= 2;
        else
            set->num_alloced = 8;
        set->loop_ids = realloc(set->loop_ids, sizeof(*set->loop_ids) * set->num_alloced);
        CHECK_MEM(set->loop_ids);
    }

    int i;

#define key(x) (loops[(x)]->head->flags)
    // Find insertion position.
    for (i = 0; i < set->num_loops; i++) {
        // If it's already in the list, break.
        if (key(loop_id) == key(set->loop_ids[i]))
            return;

        if (key(loop_id) < key(set->loop_ids[i]))
            break;
    }
#undef key

    // i should now point to where loop_id will be inserted.
    // Everything from i upwards needs to be shuffled up.

    for ( ; i <= set->num_loops; i++) {
        int tmp = 0;
        if (i < set->num_loops)
            tmp = set->loop_ids[i];
        set->loop_ids[i] = loop_id;
        loop_id = tmp;
    }

    set->num_loops++;
}

static void
loop_set_merge(loop_set_t *dst, loop_set_t *src)
{
    int i;
    for (i = 0; i < src->num_loops; i++) {
        loop_set_add(dst, src->loop_ids[i]);
    }
}

static int
loop_set_get_innermost(loop_set_t *set)
{
    assert(set->num_loops > 0);
    return set->loop_ids[set->num_loops - 1];
}

static void
loop_set_remove_innermost(loop_set_t *set)
{
    assert(set->num_loops > 0);
    set->num_loops--;
}

/*check if lpId is inner loop of pLpId*/
int isInner(int lpId, int pLpId) {
    loop_t *lp, *pLp;

    lp  = loops[lpId];
    pLp = loops[pLpId];
    while (lp) {
        if (pLp->id == lp->id) return 1; 
        lp = lp->parent;
    }
    return 0;
}

int cmpLpOrder(int lpId1, int lpId2) {
    //lpId = -1 --> lpId is inner most possible loop
    if (lpId1==INNER_MOST) return -1;
    if (lpId2==INNER_MOST) return 1;
    if (lpId1== lpId2) return 0;   //same lpId -> sameOrder
    if (lpId1==0) return 1;         //lpId==0 --> main program (outer most loop)
    if (lpId2==0) return -1;        //lpId2 is outer loop of lpId1
    else if (lpId1 > lpId2) return 1;
    else return -1;
    //1: lpId1 before lpId2 in LPHG, either outer loop or loop appear before
    //-1: lpId2 before lpId1
    //0: same loop
#if 0
        if (lpId1 == lpId2)
        return 0;
        loop_t* lca_lp = loop_comm_ances[lpId1][lpId2];
        if (lca_lp->id == lpId1)
        return 1;
        else if (lca_lp->id == lpId2)
        return -1;
        else {
                /*lca_lp->id != lpId1 && lca_lp->id != lpId2*/
                printf("BUG in cmpLpOrder\n");
                exit(1);
        }
#endif
} 

int scp_cmpLpOrder(int lpID1, int lpID2) {
        if (lpID1 == lpID2)
                return 0;
        loop_t* lca_lp = loop_comm_ances[lpID1][lpID2];
        if (lca_lp->id == lpID1)
                return 1;
        else if (lca_lp->id == lpID2)
                return -1;
        else {
                /*lca_lp->id != lpId1 && lca_lp->id != lpId2*/
                printf("BUGs when calling scp_cmpLpOrder\n");
                exit(1);
        }
}

// create a new loop level with the head & tail being the src and dst of the edge e
static loop_t *
new_loop(tcfg_edge_t *e)
{
    loop_t	*lp;

    lp = (loop_t *) calloc(1, sizeof(loop_t));
    CHECK_MEM(lp);
    lp->id = num_tcfg_loops++;
    lp->head = e->dst; lp->tail = e->src;
	//printf("\nLoop %d Head %d Tail %d",lp->id,bbi_bid(lp->head),bbi_bid(lp->tail));
    if (lp->head->bb->id < lp->tail->bb->id) {
        lp->first_bb_id = lp->head->bb->id;
        lp->last_bb_id = lp->tail->bb->id; 
    }
    else {
        lp->first_bb_id = lp->tail->bb->id;
        lp->last_bb_id = lp->head->bb->id;
    }

    return lp;
}



void
set_loop_flags(int flag)
{
    int		i;

    for (i = 0; i < num_tcfg_loops; i++)
	loops[i]->flags = flag;
}



static void
find_loops(void)
{
    int		    i;
    tcfg_edge_t	    *e;

    num_tcfg_loops = 1;	    // the entire program is treated as a loop
    loop_map = (loop_t **) calloc(num_tcfg_nodes, sizeof(loop_t *));
    CHECK_MEM(loop_map);

    for (i = 0; i < num_tcfg_edges; i++) {
	e = tcfg_edges[i];
	if (bbi_backedge(e)) {
	    if (loop_map[e->dst->id] != NULL)
		continue;
	    if (bb_is_loop_head(e->dst->bb) && bb_is_loop_tail(e->src->bb)) 
		loop_map[e->dst->id] = loop_map[e->src->id] = new_loop(e);
	}
    }

    loops = (loop_t **) calloc(num_tcfg_loops, sizeof(loop_t *));
    CHECK_MEM(loops);
    // outmost loop: the entire program
    loops[0] = (loop_t *) calloc(1, sizeof(loop_t));
    loops[0]->head = tcfg[0];
    loop_map[0] = loops[0];
    CHECK_MEM(loops[0]);
    for (i = 0; i < num_tcfg_nodes; i++) {
	if (loop_map[i] != NULL)
	    loops[loop_map[i]->id] = loop_map[i];
    }
}

#if 0
// return 1 if e->dst exits the loop to which e->src belongs
static int
exit_loop(tcfg_edge_t *e)
{
    loop_t	    *lp;
    int		    head_bid, tail_bid, dst_bid;

    lp = loop_map[e->src->id];
    if (lp == loops[0])
	return 0;
    if (bbi_pid(e->dst) != bbi_pid(lp->head))
	return 0;
    
    head_bid = bbi_bid(lp->head); tail_bid = bbi_bid(lp->tail);
    dst_bid = bbi_bid(e->dst);
    if ((dst_bid > tail_bid) || (dst_bid < head_bid))
	return 1;
    else
	return 0;
}



static void
reg_loop_exit(tcfg_edge_t *e)
{
    loop_t		*lp;
    tcfg_elink_t	*elink;

    lp = loop_map[e->src->id];
    elink = (tcfg_elink_t *) calloc(1, sizeof(tcfg_elink_t *));
    elink->edge = e; elink->next = lp->exits;
    lp->exits = elink;
}



static void
deal_exit_edge(tcfg_edge_t *e)
{
    loop_t	    *lp;
    tcfg_node_t	    *dst;
    int		    head_bid, tail_bid, lp_pid, bid, pid;

    reg_loop_exit(e);
    dst = e->dst;
    if (loop_map[dst->id] != NULL) {
	if (dst != loop_map[dst->id]->head)
	    return;
	// hit a loop head
	if (loop_map[dst->id]->parent != NULL)
	    return;
	for (lp = loop_map[e->src->id]->parent; lp != loops[0]; lp = lp->parent) {
	    head_bid = bbi_bid(lp->head); tail_bid = bbi_bid(lp->tail);
	    lp_pid = bbi_pid(lp->head);
	    bid = bbi_bid(dst); pid = bbi_pid(dst);
	    if ((pid != lp_pid) || ((bid >= head_bid) && (bid <= tail_bid))) {
		loop_map[dst->id]->parent = lp;
		break;
	    }
	}
	if (loop_map[dst->id]->parent == NULL)
	    loop_map[dst->id]->parent = loops[0];
	return;
    }
    for (lp = loop_map[e->src->id]->parent; lp != loops[0]; lp = lp->parent) {
	head_bid = bbi_bid(lp->head); tail_bid = bbi_bid(lp->tail);
	lp_pid = bbi_pid(lp->head);
	bid = bbi_bid(dst); pid = bbi_pid(dst);
	if ((pid != lp_pid) || ((bid >= head_bid) && (bid <= tail_bid))) {
	    loop_map[dst->id] = lp;
	    break;
	}
    }
    if (loop_map[dst->id] == NULL)
	loop_map[dst->id] = loops[0];
}



static void
deal_other_edge(tcfg_edge_t *e)
{
    if (loop_map[e->dst->id] == NULL) {
	loop_map[e->dst->id] = loop_map[e->src->id];
    } else if (loop_map[e->dst->id] != loop_map[e->src->id]) {
	// hit a loop head
	loop_map[e->dst->id]->parent = loop_map[e->src->id];
    }
}
#endif

static void
map_dfs_helper(int node_id, int *visited, int *am_ancestor, int *node_seq, loop_set_t *loop_set)
{
    tcfg_node_t *node;
    tcfg_edge_t *e;
    loop_set_t this_loop_set;

    assert(node_id >= 0 && node_id < num_tcfg_nodes);

    if (visited[node_id]) {
        // Three cases:
        //  (1) node_id is a visited ancestor, therefore is a loop head and we
        //      are in its loop. In this case, an entry in loop_map has been
        //      created by find_loops() and we add this loop to our set.
        //  (2) node_id is a loop head but not an ancestor - in this case, as
        //      we should already know the parent of the loop, we add its
        //      parent to our loop set.
        //  (3) node_id is not a loop head, but we have visited already
        //      therefore we know what loop it lies in. Add the same loop as a
        //      candidate for us.

        if (loop_map[node_id] == NULL) {
            printf("ERROR: node %d (%x) is not mapped to a loop yet.\n", node_id, tcfg[node_id]->bb->sa);
            assert(loop_map[node_id] != NULL);
        }

        if (loop_set != NULL) {
            if (am_ancestor[node_id]) {
                // Case (1). We hit a back edge. Therefore this node has
                // already been mapped to a loop by find_loops().
                loop_set_add(loop_set, loop_map[node_id]->id);
            } else {
                // Case (2). If it's a loop head, use its parent loop.
                // Case (3). Otherwise, use it's loop.

                // Is there a simplier expression?
                if (loops[loop_map[node_id]->id]->head->id == node_id) {
                    loop_set_add(loop_set, loop_map[node_id]->parent->id);
                } else {
                    loop_set_add(loop_set, loop_map[node_id]->id);
                }
            }
        }
        return;
    }

    visited[node_id] = 1;

    assert(node_id >= 0 && node_id < num_tcfg_nodes);
    node = tcfg[node_id];

    (*node_seq)++;
    node->flags = *node_seq;

    // If we have no exit edges, then we are exiting the main program.
    // Turn this into an outer loop edge.
    if (node->out == NULL) {
        loop_map[node_id] = loops[0];

        if (loop_set != NULL)
            loop_set_add(loop_set, loop_map[node_id]->id);
        return;
    }

    am_ancestor[node_id] = 1;

    loop_set_init(&this_loop_set);
    for (e = node->out; e != NULL; e = e->next_out) {
        D("%d to %d\n", node_id, e->dst->id);
        map_dfs_helper(e->dst->id, visited, am_ancestor, node_seq, &this_loop_set);
    }

    am_ancestor[node_id] = 0;

    if (loop_set_size(&this_loop_set) == 0) {
        printf("ERROR: node %d leads to no loop heads.\n", node_id);
        assert(loop_set_size(&this_loop_set) > 0);
    }

    D("Node %d has loop set: [ ", node_id);
    int i;
    for (i = 0; i < this_loop_set.num_loops; i++)
        D("%d ", this_loop_set.loop_ids[i]);
    D("]");

    int my_loop_id = loop_set_get_innermost(&this_loop_set);
    assert(my_loop_id >= 0 && my_loop_id < num_tcfg_loops);
    assert(loops[my_loop_id] != NULL);
    loop_map[node_id] = loops[my_loop_id];
    D("Node %d is in loop %d\n", node_id, my_loop_id);
    if (tcfg[node_id]->bb->proc == loops[my_loop_id]->head->bb->proc) {
        if (tcfg[node_id]->bb->id < loops[my_loop_id]->first_bb_id)
            loops[my_loop_id]->first_bb_id = tcfg[node_id]->bb->id;
        if (tcfg[node_id]->bb->id > loops[my_loop_id]->last_bb_id)
            loops[my_loop_id]->last_bb_id = tcfg[node_id]->bb->id;
    }

    if (loop_map[node_id]->head->id == node_id) {
        D(" and was a loop head");
        loop_set_remove_innermost(&this_loop_set);

        // At this point we also know our parent.
        if (loop_set_size(&this_loop_set) == 0) {
            // This should only happen if we are the top loop.
            assert(node_id == 0);
        } else {
            int parent_loop_id = loop_set_get_innermost(&this_loop_set);
            assert(loops[parent_loop_id] != NULL);
            loop_map[node_id]->parent = loops[parent_loop_id];
        }
    }
    D("\n");

    if (loop_set != NULL)
        loop_set_merge(loop_set, &this_loop_set);

    loop_set_free(&this_loop_set);
}

static void
map_bbi_loop(void)
{
    int *visited = (int*)calloc(num_tcfg_nodes, sizeof(int));
    int *am_ancestor = (int*)calloc(num_tcfg_nodes, sizeof(int));
    int node_seq = 0;

    map_dfs_helper(0, visited, am_ancestor, &node_seq, NULL);

    free(visited);
    free(am_ancestor);

    clear_bbi_flags();
}

#if 0
static void
map_bbi_loop()
{
    Queue	    worklist;
    tcfg_node_t	    *src, *dst;
    tcfg_edge_t	    *e;

    init_queue(&worklist, sizeof(tcfg_node_t *));
    enqueue(&worklist, &tcfg[0]);
    tcfg[0]->flags = 1;
    while (!queue_empty(&worklist)) {
	src = *((tcfg_node_t **) dequeue(&worklist));
	for (e = src->out; e != NULL; e = e->next_out) {
	    dst = e->dst;
	    if (exit_loop(e))
		deal_exit_edge(e);
	    else if (dst->flags == 0)
		deal_other_edge(e);
	    
	    if (dst->flags == 0) {
		enqueue(&worklist, &dst);
		dst->flags = 1;
	    }
	}
    }
    clear_bbi_flags();
    free_queue(&worklist);
}

#endif

static void
search_common_ancestor(loop_t *x, loop_t *y)
{
    loop_t  *lp;
    long	flag = (long) x;

    for (lp = x; lp != NULL; lp = lp->parent) {
	if (lp == y) {
	    loop_comm_ances[x->id][y->id] = y;
	    loop_comm_ances[y->id][x->id] = y;
	    return;
	}
	lp->flags = flag;
    }
    for (lp = y; lp != NULL; lp = lp->parent) {
	if (lp->flags == flag) {
	    loop_comm_ances[x->id][y->id] = lp;
	    loop_comm_ances[y->id][x->id] = lp;
	    return;
	}
    }
    /* liangyun */
#if 1
    fprintf(stderr, "Oops, no common ancestor for two loops: %d, %d is found!\n",
	    x->id, y->id);
    exit(1);
#endif
}



// find common ancestors of any two loops
static void
loop_relations(void)
{
    int		i, j;

    // alloc the matrix for common ancestors
    loop_comm_ances = (loop_t ***) calloc(num_tcfg_loops, sizeof(loop_t **));
    for (i = 0; i < num_tcfg_loops; i++)
	loop_comm_ances[i] = (loop_t **) calloc(num_tcfg_loops, sizeof(loop_t *));

    for (i = 0; i < num_tcfg_loops; i++) {
	loop_comm_ances[i][i] = loops[i];
	for (j = i + 1; j < num_tcfg_loops; j++)
	    search_common_ancestor(loops[i], loops[j]);
    }
}



static void UNUSED
dump_loops(void)
{
    int		i;
    tcfg_node_t	*x, *y, *z;

    printf("\ndump loops\n");
    printf("----------------\n");
    for (i = 0; i < num_tcfg_nodes; i++) {
	x = tcfg[i];
	if (loop_map[i] == NULL)
	    continue;	// for non-reachable nods, such as block 2.51 in minver
	y = loop_map[i]->head; z = loop_map[i]->tail;
	if (y == tcfg[0])
	    printf("%d.%d: \t%d[start - end]\n",
		    bbi_pid(x), bbi_bid(x), loop_map[i]->id);
	else {
	    char parent_str[128] = "<nil>";
	    if (loop_map[i]->parent) {
		    snprintf(parent_str, sizeof(parent_str), "%d", loop_map[i]->parent->id);
		    parent_str[sizeof(parent_str)-1] = '\0';
	    }
	    printf("%d.%d: \t%d[%d.%d - %d.%d]  / parent:%s\n",
		    bbi_pid(x), bbi_bid(x), loop_map[i]->id,
		    bbi_pid(y), bbi_bid(y), bbi_pid(z), bbi_bid(z),
		    parent_str);
    }
    }

    printf("The loops are:\n");
    for (i = 0; i < num_tcfg_loops; i++) {
        tcfg_node_t *h = loops[i]->head;
        printf("Loop %2d: head bb is [%d.%d]0x%x, parent loop is ",
                i, bbi_pid(h), bbi_bid(h), h->bb->sa);
        if (loops[i]->parent)
            printf("%d\n", loops[i]->parent->id);
        else
            printf("nil\n");
    }
}



static void UNUSED
dump_loop_comm_ances(void)
{
    int		i, j;

    printf("\ndump loop common ancestors:\n");
    for (i = 0; i < num_tcfg_loops; i++) {
	for (j = 0; j < num_tcfg_loops; j++) {
	    if (loop_comm_ances[i][j] == NULL) {
		    printf("<NO>");
	    } else {
		    printf("%2d  ", loop_comm_ances[i][j]->id);
	    }
	}
	printf("\n");
    }
}



void
loop_process()
{
    find_loops();
    map_bbi_loop();
    //dump_loops();
    loop_relations();
    //dump_loop_comm_ances();
}

