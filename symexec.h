/*******************************************************************************
 *
 * Chronos: A Timing Analyzer for Embedded Software
 * =============================================================================
 * http://www.comp.nus.edu.sg/~rpembed/chronos/
 *
 * Symbolic execution of binary code
 * Vivy Suhendra - Huynh Bach Khoa
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
 * 03/2007 symexec.h
 *
 *  v4.1:
 *      _ completely rewrite the symbolic execution framework
 *          + intraprocedure execution, instead of intra basic block
 *          + memory modeling -> can trace value when saved to memory
 *          + richer value types: induction, expression, parameter
 *      _ temporary disable conflict pair detection
 *
 *  v4.0: as in Chronos-4.0 distribution
 *
 *
 ******************************************************************************/
#ifndef SYM_EXEC_H
#define SYM_EXEC_H
#include "common.h"
#include "loops.h"
#include "reg.h"

/*** PARAMETER VALUE TYPE ***
 *  Parameter value is dynamic value, statically unpredictable
 *  Denote as a string V<id>, same para -> same string
 *  For now, all parameters are T (unpredictable), no interpretation
 */
void setNewPara(char *para);

/*** INDUCTION VALUE TYPE ***
 *  Induction value is a type of register value
 *  Basic induction value (BIV):  (name, init, opr, stride)
 *  $i = $i opr k, opr: +,-,*,>>
 *  General induction value is an expression of basic induction value
 */
#define BIV_SAVED 0x1
struct BIV {
    de_inst_t   *insn;          //instruction performs inductive operation 
    //int     lpId;           //loop where induction
    reg_t   initVal;
    //char    opr[8];         //inductive operation, e.g + - * / >>
    unsigned opr;
    int     stride;
    // char    regName[10];  
    int     regName; 
    int     flag;
};
typedef struct BIV  biv_s;
//typedef struct BIV* biv_p;

int     updateInitVal(biv_p biVar, reg_t initVal);
int     bivEq(biv_p inVar1, biv_p inVar2);
void    cpyBIV(biv_p varDst, biv_p varSrc);
void    printBIV(FILE *fp, biv_p biVar);
void    freeBIV(biv_p *biv);

int     execute(void);

/*** MEMORY MODELING FRAMEWORK ***/
/* Model memory as a list of memory nodes 
 * Each node is a tuple < instAddr,writeAddr,writeValue >
 */
struct sym_memory_model {
    long    instAddr;               /*inst assigns value for this entry*/
    reg_t   writeAddr;              /*addr value of this entry*/
    reg_t   regValue;               /*reg. value saved in this entry*/
};
typedef struct sym_memory_model mem_s;
typedef struct sym_memory_model* mem_p;

/*** DATA CACHE INSTRUCTION TYPE ***/
typedef struct {
    de_inst_t   *insn;      
    expr_s      addrExpr;   /*Address expression */
    worklist_p  addr_set;   /*ScopeMem accessed in increasing order*/
    int         max_miss;   /*Maximum estimate cache misses*/
    int         max_exec;   /*Maximum number of executions*/
    int         resideLpId; /*Loop where this data reference reside*/
} dat_inst_t;

/*Return loopId where biv resides in*/
int     biv2LoopId(biv_p biv);
/*Expand address expression from biv format to normal expression format*/
void    expandAddrExpr(expr_p exp, reg_t *addrExpr);
void    printDataRef(FILE *fp, dat_inst_t* datInst);
int     getAddrD(dat_inst_t* datInst);

#ifndef INF_NODE_T_DEFINED
#define INF_NODE_T_DEFINED
struct inf_node_t;
typedef struct inf_node_t inf_node_t;
#endif

int isMemAccess(int inst_op);
void setDebugFile(char *fName);

int isLoadInst(int inst_op);
int isStoreInst(int inst_op);
loop_t* getIbLoop(inf_node_t *ib);

#endif
