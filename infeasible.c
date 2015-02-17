/*******************************************************************************
 *
 * Chronos: A Timing Analyzer for Embedded Software
 * =============================================================================
 * http://www.comp.nus.edu.sg/~rpembed/chronos/
 *
 * Infeasible path analysis for Chronos
 * Vivy Suhendra
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
 * 03/2007 infeasible.c
 *  v4.1:
 *      _ rewrite disassembly parser, change from bash shell to C, improve speed
 *      _ separate symbolic execution data type from infeasible.h
 *
 *  v4.0: as in Chronos-4.0 distribution
 *
 ******************************************************************************/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include "isa.h"
#include "cfg.h"
#include "tcfg.h"
#include "loops.h"
#include "infeasible.h"
#include "imm/machine.h"
#include "conflicts.h"

#define MD_INST_SIZE 0x8

extern prog_t prog;
extern isa_t  *isa;

extern int num_tcfg_nodes;
extern tcfg_node_t **tcfg;

extern tcfg_nlink_t ***bbi_map;
extern loop_t **loop_map;


/*
 * Determines a reverse topological ordering of the procedure call graph.
 */
static
int topo_call( int **callees, int *num_callee ) {

  int i, currp;

  int  *comefrom;     // keep the proc from which we came, to return to
  int  comefromsize;
  char *markfin;      // markfin: 0: unvisited, 1: visited but unfinished, 2: finished
  char fin;

  int countdone;

  comefrom = NULL;
  comefromsize = 0;
  markfin = (char*) calloc( prog.num_procs, sizeof(char) );
  callgraph = (int*) calloc( prog.num_procs, sizeof(int) );

  countdone = 0;

  // start from main procedure
  currp = prog.main_proc;

  while( countdone < prog.num_procs ) {

    fin = 1;
    for( i = 0; fin && i < num_callee[currp]; i++ )
      if( markfin[ callees[currp][i] ] != 2 )
	fin = 0;

    if( num_callee[currp] <= 0 || fin ) {  // finished
      markfin[currp] = 2;
      callgraph[countdone++] = currp;

      // returning
      if( !comefromsize )
	break;

      currp = comefrom[--comefromsize];
      continue;
    }

    markfin[currp] = 1;
    comefrom = (int*) realloc( comefrom, (comefromsize+1) * sizeof(int) );
    comefrom[comefromsize++] = currp;

    // go to next unvisited procedure call
    fin = 1;
    for( i = 0; fin && i < num_callee[currp]; i++ ) {
      if( markfin[callees[currp][i]] != 2 ) {
	currp = callees[currp][i];
	fin = 0;
      }
    }
    if( fin )
      printf( "Unvisited called procedure not detected.\n" ), exit(1);

  } // end while( countdone < num_bb )

  free( comefrom );
  free( markfin );

  return 0;
}

//HBK: rewrite readInstr() for faster implementation
UNUSED static
void editAsmStr(char *tmp) {
    int dbg = 0;
    int j, flag;
    FILE *dbgExec=stdout;
    flag = 0;
    if (dbg) fprintf(dbgExec,"\nProcess %s ->",tmp);
    for (j=0; j<strlen(tmp); j++) {
        if (tmp[j]==',' || tmp[j]=='\\' || tmp[j]=='(' || tmp[j]==')')
            tmp[j]=' ';
        if (tmp[j]=='<') { flag=1; tmp[j]=' '; }
        if (tmp[j]=='>') { flag=0; tmp[j]=' '; }
        if (flag==1) tmp[j]=' ';
    }
    if (dbg) fprintf(dbgExec,"%s",tmp);
}

#if 0
static UNUSED
void readInsn ( char *obj_file ) {
    int dbg = 0;
    int i,j,k;
    FILE *f;
    char tmp[120];
    int tmpAddr, curAddr;
    int curInsn;
    proc_t     *p;
    cfg_node_t *b;
    de_inst_t  *d;

    inf_proc_t *ip;
    inf_node_t *ib;
    insn_t     *is, *tmpIs;

    int n, len;
    int *num_callee = (int*) calloc(prog.num_procs, sizeof(int));
    int **callees = (int**) malloc(prog.num_procs*sizeof(int*));

    sprintf(tmp,"%s.dis",obj_file);
    f = fopen(tmp,"r");
    insn_t  *isList;
    /* Read preprocessing */
    num_insn_st = 0;
    insnlist_st = NULL;
    if (dbg) printf("\nPreprocessing instructions");
    while (fgets(tmp,120,f)) {
        if (strstr(tmp,"0040")==NULL) continue;//skip non-inst line
        editAsmStr(tmp);
        num_insn_st++;
        insnlist_st = (insn_t*) realloc( insnlist_st, 
                                    num_insn_st * sizeof(insn_t) );
        is = &(insnlist_st[num_insn_st-1]);
        is->r1[0]='\0';is->r2[0]='\0';is->r3[0]='\0';
        sscanf( tmp, "%x %s %s %s %s\n", 
                    &tmpAddr, is->op, is->r1, is->r2, is->r3 );
        sprintf(is->addr,"%x",tmpAddr);
        if (dbg) printf("\n\tInsn: addr:%s op:%s r1:%s r2:%s r3:%s",
            is->addr, is->op, is->r1, is->r2, is->r3);
        if (tmpAddr == prog.start_addr - MD_INST_SIZE) break;
    }
    isList = calloc(prog.num_inst,sizeof(insn_t));
    /* Read instruction */
    if (dbg) printf("\nProgram instructions");
    curAddr = prog.start_addr;
    for (i=0; i<prog.num_inst; i++) {
        is = &(isList[i]);
        sprintf(is->addr,"%x",curAddr);
        //if (1) printf("\nScan inst %x: ",curAddr);
        while (fgets(tmp,120,f)) {
            if (strstr(tmp,"0040")==NULL) continue;//skip non-inst line
            else break;
        }
        editAsmStr(tmp);
        is->r1[0]='\0';is->r2[0]='\0';is->r3[0]='\0';
        sscanf( tmp, "%x %s %s %s %s\n", 
                &tmpAddr, is->op, is->r1, is->r2, is->r3 );
        sprintf(is->addr,"%x",tmpAddr);
        if (dbg) printf("\n\tInsn: addr:%s op:%s r1:%s r2:%s r3:%s",
            is->addr, is->op, is->r1, is->r2, is->r3);
        //curAddr = curAddr+sizeof(MD_INST_SIZE); 
    }

    for (i=0; i<prog.num_procs; i++) callees[i] = NULL;
    
    curInsn = 0;
    inf_procs = (inf_proc_t*) malloc(prog.num_procs*sizeof(inf_proc_t));
    for (i=0; i<prog.num_procs; i++) {
        p = &(prog.procs[i]);
        ip= &(inf_procs[i]);
        
        ip->proc = p;
        ip->num_bb = p->num_bb;
        ip->inf_cfg = (inf_node_t*) malloc(ip->num_bb*sizeof(inf_node_t));

        for (j=0; j<ip->num_bb; j++) {
            b = &(p->cfg[j]);
            ib= &(ip->inf_cfg[j]);

            ib->bb = b;
            ib->num_insn = b->num_inst;
            ib->insnlist = (insn_t*) malloc (ib->num_insn*sizeof(insn_t));
            ib->num_assign = 0;
            ib->assignlist = NULL;
            ib->branch = NULL;
            ib->loop_id = -1;
            ib->exec_count = -1;
            ib->loop_role = b->loop_role;// copy loop_role of cfg block to inf block

            for (k=0; k<ib->num_insn; k++) {
                d = &(b->code[k]);
                is= &(ib->insnlist[k]);
                if (0) printf("\nFind insn %x: ",d->addr);

                do {//find the is, hopefully they are all available
                    tmpIs = &(isList[curInsn]);
                    curInsn = (curInsn+1)%prog.num_inst;
                    sscanf(tmpIs->addr,"%x",&curAddr);
                    if (0) printf(" %x",curAddr);
                } while (d->addr!=curAddr);

                strcpy(is->addr, tmpIs->addr);
                strcpy(is->op, tmpIs->op);
                strcpy(is->r1, tmpIs->r1);
                strcpy(is->r2, tmpIs->r2);
                strcpy(is->r3, tmpIs->r3);
                if (dbg) printf("\n\tInsn: addr:%s op:%s r1:%s r2:%s r3:%s",
                    is->addr, is->op, is->r1, is->r2, is->r3);
            }
        }
    }
    topo_call( callees, num_callee );

    // produced callgraph is in reverse order, so flip the array
    n = prog.num_procs - 1;
    len = prog.num_procs / 2;
    for( i = 0; i < len; i++ ) {
        int tmp        = callgraph[i];
        callgraph[i]   = callgraph[n-i];
        callgraph[n-i] = tmp;
    }

    free( num_callee );
    for( i = 0; i < prog.num_procs; i++ )
        free( callees[i] );
    free( callees );
    if (dbg) fflush(stdout);
}
#endif

static
void readInstr( char *obj_file ) {

  int i, j, k;

  // FILE *f;
  // char tmp[120];
  // int addr;

  proc_t     *p;
  cfg_node_t *b;
  de_inst_t  *d;

  inf_proc_t *ip;
  inf_node_t *ib;
  tcfg_node_t *bbi;

  // for call graph construction
  int n, len;
  int *num_callee = (int*) calloc( prog.num_procs, sizeof(int) );
  int **callees = (int**) malloc( prog.num_procs * sizeof(int*) );
  for( i = 0; i < prog.num_procs; i++ )
    callees[i] = NULL;
    

  // transfer information that is already parsed
  inf_procs = (inf_proc_t*) malloc( prog.num_procs * sizeof(inf_proc_t) );
  for( i = 0; i < prog.num_procs; i++ ) {
    p  = &(prog.procs[i]);
    ip = &(inf_procs[i]);

    ip->proc = p;
    ip->num_bb = p->num_bb;
    ip->inf_cfg = (inf_node_t*) malloc( ip->num_bb * sizeof(inf_node_t) );

    for( j = 0; j < ip->num_bb; j++ ) {
      b  = &(p->cfg[j]);
      ib = &(ip->inf_cfg[j]);
      //problem is in the bbi line
      tcfg_nlink_t **bbi_map_map = bbi_map[i];
      bbi = bbi_map[i][j]->bbi;

      ib->bb = b;
      ib->num_insn = b->num_inst;
      ib->insnlist = (de_inst_t **)malloc( ib->num_insn * sizeof(de_inst_t *) );
      ib->num_assign = 0;
      ib->assignlist = NULL;
      ib->branch = NULL;
      ib->loop_id = (loop_map[bbi->id] == NULL)?0:loop_map[bbi->id]->id;
      ib->exec_count = -1;
      

      for( k = 0; k < ib->num_insn; k++ ) {
	    if (b->code == NULL) {
	        d = NULL;
	    } else {
	        d  = &(b->code[k]);
	    }
	    ib->insnlist[k] = d;

#if 0
        sprintf( is->addr, "%x", d->addr );
        strcpy( is->op, isa[d->op_enum].name );
        is->r[0][0] = '\0';
        is->r[1][0] = '\0';
        is->r[2][0] = '\0';

        // for operands, read anew from .dis file, because these are not stored in de_inst_t
        sprintf( tmp, "sed -n '/^00%s/p' %s.dis | awk '{print $4}' > tline", is->addr, obj_file );
        system( tmp );
        system( "cat tline | tr ',' '\\ ' | tr '(' '\\ ' | tr ')' '\\ ' > topr" );

        f = fopen( "topr", "r" );
        fscanf( f, "%s %s %s", is->r[0], is->r[1], is->r[2] );
        fclose( f );
#endif

#if 0
        memset(is->r1, 0, sizeof(is->r1));
        memset(is->r2, 0, sizeof(is->r2));
        memset(is->r3, 0, sizeof(is->r3));

        sprintf(is->addr, "%x", d->addr);
        strcpy(is->op, MD_OP_NAME(d->op_enum));
        is->op_enum = d->op_enum;
        is->s_bit = d->s_bit;
        is->condition = d->condition;
        is->imm = d->imm; 
        is->has_imm = d->has_imm;
        int reg_idx = 0;
        int idx;
        for (idx = 0; idx < d->num_out; idx++) {
            switch (reg_idx) {
                case 0: strcpy(is->r1, regnum_to_regstr(d->out[idx]));break;
                case 1: strcpy(is->r2, regnum_to_regstr(d->out[idx]));break;
                case 2: strcpy(is->r3, regnum_to_regstr(d->out[idx]));break;
            }
            reg_idx++;
        }
        assert(reg_idx <= 1);
        for (idx = 0; idx < d->num_in; idx++) {
            switch (reg_idx) {
                case 0: strcpy(is->r1, regnum_to_regstr(d->in[idx]));break;
                case 1: strcpy(is->r2, regnum_to_regstr(d->in[idx]));break;
                case 2: strcpy(is->r3, regnum_to_regstr(d->in[idx]));break;
            }
            reg_idx++;
        }
#endif

      }
    }
  }

  topo_call( callees, num_callee );

  // produced callgraph is in reverse order, so flip the array
  n = prog.num_procs - 1;
  len = prog.num_procs / 2;
  for( i = 0; i < len; i++ ) {
    int tmp        = callgraph[i];
    callgraph[i]   = callgraph[n-i];
    callgraph[n-i] = tmp;
  }

  free( num_callee );
  for( i = 0; i < prog.num_procs; i++ )
    free( callees[i] );
  free( callees );
}


/*
 * Returns 1 if paft is pbef in the call graph; i.e. it is deeper in the chain of calls.
 * Assume there is no cyclic calls.
 */
static
char isDeeper( int paft, int pbef ) {

  int i;
  for( i = 0; i < prog.num_procs; i++ ) {
    if( callgraph[i] == paft )
      return 0;
    if( callgraph[i] == pbef )
      return 1;
  }
  return 0;
}


static
int setCountRec( tcfg_node_t *bbi, int count, int return_pid ) {

  tcfg_edge_t *e;

  if( bbi->exec_count >= count ) {
    printf( "Existing count tcfg %d(%d::%d) = %d\n", bbi->id, bbi->bb->proc->id, bbi->bb->id, bbi->exec_count );
    return 1;
  }
  bbi->exec_count = count;
  // printf( "Set count tcfg %d(%d::%d) = %d\n", bbi->id, bbi->bb->proc->id, bbi->bb->id, count );

  for( e = bbi->out; e != NULL; e = e->next_out ) {
    if( e->dst->bb->proc->id != return_pid )
      setCountRec( e->dst, count, return_pid );
  }
  return 0;
}


static UNUSED
int setCount( tcfg_node_t *bbi, int count ) {

  if( bbi->exec_count >= count ) {
    printf( "Existing count tcfg %d(%d::%d) = %d\n", bbi->id, bbi->bb->proc->id, bbi->bb->id, bbi->exec_count );
    return 1;
  }
  bbi->exec_count = count;
  //printf( "Set count tcfg %d(%d::%d) = %d\n", bbi->id, bbi->bb->proc->id, bbi->bb->id, count );

  // propagate to called procedure
  if( bbi->bb->callee != NULL && bbi->out != NULL )
    setCountRec( bbi->out->dst, count, bbi->bb->proc->id );

  return 0;
}


static
int setLoopIDRec( tcfg_node_t *bbi, int lpid, int return_pid ) {
    int dbg = 0;
  tcfg_edge_t *e;
  inf_loop_t *lp = &(inf_loops[lpid]);

  assert(bbi->loop_id >= -1 && bbi->loop_id < num_inf_loops);

  if( bbi->loop_id != -1 &&
        (bbi->loop_id == lpid || isDeeper( inf_loops[bbi->loop_id].pid, lp->pid )))
    return 1;

  bbi->loop_id = lpid;
  if (dbg) printf( "Set tcfg %d(%d::%d)  loop:%d  entry:(%d::%d)  bound:%d\n",
	  bbi->id, bbi->bb->proc->id, bbi->bb->id, lpid, lp->pid, lp->entry, lp->bound );

  for( e = bbi->out; e != NULL; e = e->next_out ) {
    if( e->dst->bb->proc->id != return_pid )
      setLoopIDRec( e->dst, lpid, return_pid );
  }
  return 0;
}


static
int setLoopID( tcfg_node_t *bbi, int lpid ) {
    int dbg = 0;

  inf_loop_t *lp = &(inf_loops[lpid]);

  if( bbi->loop_id == lpid || isDeeper( inf_loops[bbi->loop_id].pid, lp->pid ))
    return 1;

  bbi->loop_id = lpid;
  if (dbg) printf( "Set tcfg %d(%d::%d)  loop:%d  entry:(%d::%d)  bound:%d\n",
	  bbi->id, bbi->bb->proc->id, bbi->bb->id, lpid, lp->pid, lp->entry, lp->bound );

  // propagate to called procedure
  if( bbi->bb->callee != NULL && bbi->out != NULL )
    setLoopIDRec( bbi->out->dst, lpid, bbi->bb->proc->id );

  return 0;
}


/*
 * Recursively set loop id for reachable nodes.
 */
static
void markLoop( inf_proc_t *ip, inf_node_t *head, inf_node_t *ib, int lpid, char **checked ) {

  int i;
  tcfg_nlink_t *ndlink;
  inf_loop_t *lp = &(inf_loops[lpid]);

  // In case of nested loops, we rely on the assumption that the inner loop will have larger entry ID.
  // Update only if the new information is for the deeper level.
  if( ib->loop_id == -1 || inf_loops[ib->loop_id].entry < lp->entry ) {
    ib->loop_id = lpid;

    // propagate to tcfg nodes
    for( ndlink = bbi_map[ip->proc->id][ib->bb->id]; ndlink != NULL; ndlink = ndlink->next )
      setLoopID( ndlink->bbi, lpid );
  }
  (*checked)[ib->bb->id] = 1;
  //if( ib->bb->loop_role == LOOP_HEAD )
  if( ib == head ) {
    return;
  }

  for( i = 0; i < ib->bb->num_in; i++ ) {
    int pre = ib->bb->in[i]->src->id;
    //HBK: > or >= , can entry node considered in-loop?
    //Consider entry node in loop because it also executed LB times
    // Yao: lp->entry may not be the smallest node
    tcfg_node_t *bbi = bbi_map[ip->proc->id][pre]->bbi;
    if( !(*checked)[pre] && loop_map[bbi->id] && 
        loop_map[bbi->id]->id == lpid /*pre >= lp->entry*/ )
      markLoop( ip, head, &(ip->inf_cfg[pre]), lpid, checked );
  }
}

/*
 * Parses loop bound information and stores known block execution counts,
 * to be used in constraint formulation.
 */
static
int readBlockCounts( char *imm_file ) {

  FILE *f;
  char tmp[1024];
  int i;
  int pid, bid, count;
  unsigned entry;

  inf_proc_t *ip;

  for( i = 0; i < num_tcfg_nodes; i++ ) {
    tcfg[i]->loop_id = -1;
    tcfg[i]->exec_count = -1;
  }

#if 0
  // absolute counts
  sprintf( tmp, "cat %s.cons | tr 'c' '\\ ' | awk '$2 ~ \"=\" {print $1,$NF}' | tr '.' '\\ ' > counts", obj_file );
  system( tmp );
  f = fopen( "counts", "r" );
  while( fscanf( f, "%d %d %d", &pid, &bid, &count ) != EOF ) {

    tcfg_nlink_t *ndlink;

    //printf( "Detected absolute count %d::%d = %d\n", pid, bid, count );
    if( !include_proc[pid] ) {
      printf( "Ignoring count for excluded function.\n" );
      continue;
    }
    inf_procs[pid].inf_cfg[bid].exec_count = count;

    // propagate to tcfg nodes
    for( ndlink = bbi_map[pid][bid]; ndlink != NULL; ndlink = ndlink->next )
      setCount( ndlink->bbi, count );
  }
  fclose( f );
#endif

  num_inf_loops = num_tcfg_loops;
  inf_loops = calloc(num_inf_loops, sizeof(*inf_loops));
/*
  for( pid = 0; pid < prog.num_procs; pid++ ) {
    if( include_proc[pid] ) {
      ip = &(inf_procs[pid]);
      for( bid = 0; bid < ip->num_bb; bid++ )
        ip->inf_cfg[bid].loop_id = -1;
    }
  }
*/
  f = fopen(imm_file, "r" );
  while(fgets(tmp, sizeof(tmp), f) != NULL) {
    int ret;
    if (tmp[0] != 'l')
        continue;

    // Parse line of the form l <loop head address> <iter count>
    ret = sscanf(tmp + 2, "%i %i", &entry, &count);
    if (ret != 2) {
        printf("WARNING: Indecipherable line: %s\n", tmp);
        continue;
    }

    // Now we have to determine which procedure/basic block this belongs to.
    int pid = -1, bid = -1;
    for (pid = 0; pid < prog.num_procs; pid++) {
        proc_t *p = &prog.procs[pid];
        if (p->sa <= entry && entry < p->sa + p->size) {
            for (bid = 0; bid < p->num_bb; bid++) {
                cfg_node_t *bb = &p->cfg[bid];
                if (bb->sa <= entry && entry < bb->sa + bb->size) {
                    /* Bingo. It should be the head. */
                    if (bb->sa == entry) {
                        break;
                    } else {
                        printf("WARNING: loop entry 0x%x not at bb start "
                                "(0x%x,0x%x).\n",
                                entry, bb->sa, bb->sa + bb->size);
                    }
                }
            }
            if (bid != p->num_bb) {
                /* success. break out. */
                break;
            }
        }
    }
    if (pid == prog.num_procs) {
        printf("No BB found for loop at 0x%x\n", entry);
        continue;
    }

    int lpid, head, tail;
    loop_t *lpn;
    inf_loop_t *lp;
    inf_node_t *hd, *ta;

    char *checked;

    //printf( "Detected loop bound for %d::%d (entry: %d) = %d\n", pid, bid, entry, count );

    if(!include_proc[pid]) {
      printf( "Ignoring bound for excluded function.\n" );
      continue;
    }

    ip = &(inf_procs[pid]);

    // Find all loops in the TCFG that this bound corresponds to.
    for (lpid = 0; lpid < num_tcfg_loops; lpid++) {
      if (loops[lpid] == NULL ||
              loops[lpid]->head == NULL ||
              loops[lpid]->head->bb == NULL ||
              loops[lpid]->head->bb->sa != entry)
        continue;

      lp = &(inf_loops[lpid]);
      lp->pid = pid;
      lp->entry = loops[lpid]->head->bb->id;
      lp->bound = count;
      lp->loop_id = lpid;

      assert(loops[lpid]->head->bb->proc->id == pid &&
              loops[lpid]->head->bb->id == bid);
      loops[lpid]->count = count;

#if 0
      // mark all blocks in the loop body
      // traverse from tail upwards until head is found; all traversed block is in the loop
      lpn = loop_map[bbi_map[pid][bid]->bbi->id];
      if (lpn == NULL) {
          fprintf(stderr, "ERROR: No loop for tcfg node %d (pid: %d, bid: %d, addr: %x)\n",
                  bbi_map[pid][bid]->bbi->id,
                  pid, bid,
                  bbi_map[pid][bid]->bbi->bb->sa);
          continue;
      }
      head = bbi_bid( lpn->head );
      if (lpn->tail!=NULL)
          tail = bbi_bid( lpn->tail );
      else
          tail = bbi_bid(tcfg[num_tcfg_nodes-1]);
      hd = &(ip->inf_cfg[head]);
      ta = &(ip->inf_cfg[tail]);
      checked = (char*) calloc( ip->num_bb, sizeof(char) );
      markLoop( ip, hd, ta, lpid, &checked );
      free( checked );
#endif
    }
  }
  fclose( f );

  int lpid;
  inf_loop_t *lp;
  for (lpid = 0; lpid < num_tcfg_loops; lpid++) {
      lp = &(inf_loops[lpid]);
      if (lp->bound == 0) {
        printf("No loop bound for 0x%x\n", loops[lpid]->head->bb->sa);
      }
  }

  return 0;
}

void infeas_analysis( char *obj_file ) {
  int dbg = 1;
  if (dbg) {
    printf("\nAnalyze file |%s|\n",obj_file);fflush(stdout);
    printf( "Read Instr...\n" ); fflush(stdout);
    printf( "Read Block Counts...\n" ); fflush(stdout);
  }
  readInstr( obj_file );
  readBlockCounts( obj_file );

  //printInstructions();

  if (dbg) printf( "Starting symbolic execution...\n" ); fflush(stdout);
  execute();

  //printEffects(0);

  printf( "Starting conflict detection...\n" ); fflush(stdout);
  detectConflicts();
  printf( "Detected %d BB and %d BA\n", num_BB, num_BA ); fflush(stdout);
  //printEffects(1);
}

