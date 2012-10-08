
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
 * $Id: loops.h,v 1.2 2006/06/24 08:54:57 lixianfe Exp $
 *
 ******************************************************************************/


#ifndef LOOPS_H
#define LOOPS_H


#include "tcfg.h"


#define MAX_LOOP_NEST	32

#define LOOP_ENTRY	0
#define LOOP_EXIT	1


#ifndef LOOP_T_DEFINED
#define LOOP_T_DEFINED
typedef struct loop_t	loop_t;
#endif

#define LOOP_ANALYZED 0x2
// data structure for loop information

/*dynamic loop bound flag*/ 
#define EQL_LB 0x1      /*bound is equal to cur. iteration of loop rbId*/
#define INV_LB 0x2      /*bound is inverse with cur. iteration of loop rbId*/

typedef struct {
    int num_loops;
    int* loop_ids;
    int num_alloced;
} loop_set_t;

struct loop_t {
    int		        id;
    tcfg_node_t	    *head;	// [head, tail]
    tcfg_node_t	    *tail;
    int             first_bb_id;
    int             last_bb_id;
    loop_t	        *parent;
    tcfg_elink_t    *exits;
    long		        flags;
    int             bound;      //maximum lb        

    void*           biv_list;   //list of BIV in this loop
    int             exec;       //maximum exec count

    /*HBK: to support dynamic loop bound*/
    int             rBound;    //relative bound
    int             rType;     //type of relative loop bound
    int             rId;       //relative bound compared to loop rbId
    int             count;
};
int isInner(int lpId, int pLpId);       //return if lpId is inner pLpId
#define INNER_MOST -2
int cmpLpOrder(int lpId1, int lpId2);
int scp_cmpLpOrder(int lpId1 , int lpId2);

void
loop_process(void);

void
set_loop_flags(int flag);

extern int num_tcfg_loops;
extern loop_t **loop_map;
extern loop_t       **loops;
loop_t***       loop_comm_ances;

#endif
