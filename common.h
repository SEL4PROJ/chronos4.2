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
 * $Id: common.h,v 1.2 2006/06/24 08:54:56 lixianfe Exp $
 *
 ******************************************************************************/

#ifndef COMMON_H
#define COMMON_H

#include <stdio.h>
#include <assert.h>

#define NO_REG 18
#define NO_REGULAR_REG 16
#define ARM_STACK_REG   13
#define ARM_LINK_REG    14
#define ARM_PC_REG      15
// treat N, Z, C, V flags as a register
#define ARM_COND_FLAGS_REG   16
#define ARM_MEM_REG     17

#define UNUSED __attribute__((unused))
#define NORETURN __attribute__((noreturn))

#define	TARGET_SS	// Model SimpleScalar ISA and processor

#define SHOW_PROGRESS	0

#define BAD_RANGE	0
#define GOOD_RANGE	1
#define	MAX_INST	5120	/* maximum # of instructions can be processed */
#define MAX_BB		1024	/* maximum # of blocks can be processed */
#define	STACK_ELEMS	1024	/* initial stack capacity in terms of elements */
#define	QUEUE_ELEMS	1024    
#define HEAP_ELEMS	16
#define INFTY		99999

#define CHECK_MEM(p) \
if ((p) == NULL) { \
    fprintf(stderr, "out of memory (%s:%d)\n", __FILE__, __LINE__); \
    exit(1); \
}

#define	inst_num(code, size)	((size) / SS_INST_SIZE)
#define inst_size(code, n)	((n) * SS_INST_SIZE)
#define BETWEEN(x, a, b)	(((x) >= (a)) && ((x) <= (b)))
#define INSIDE(x, a, b)		(return (((x) > (a)) && ((x) < (b))))
#define max(x, y)		((x) > (y) ? (x) : (y))
#define min(x, y)		((x) < (y) ? (x) : (y))
#define SET_FLAG(x, flag_msk)	((x) |= (flag_msk))
#define RESET_FLAG(x, flag_msk)	((x) &= (~(flag_msk)))
#define TEST_FLAG(x, flag_msk)	((x) & (flag_msk))

#define mem_free(p) ((p) ? free(p) : 0)

typedef unsigned long long ticks;
#define CPU_MHZ 8000000000

int hexValue (char *hexStr);
ticks getticks(void);

// an interval [lo..hi]
typedef struct {
    int	    lo, hi;
} range_t;

// an interval [lo..hi]
typedef struct {
    short int	lo, hi;
} range16_t;

typedef struct {
    char lo, hi;
} range8_t;

// compare which one is more general
int
cmp_general(range_t *x, range_t *y);

// intersect operation
int
range_isect(range_t *x, range_t *y);

// union operation
void
range_union(range_t *x, range_t *y);



typedef struct stack_t {
    void    *base;
    void    *top;
    int	    esize;	/* element size */
    int	    capt;	/* capacity */
} Stack;



#ifndef QUEUE
#define QUEUE
typedef struct queue_t {
    void    *base;
    void    *head, *tail;   /* head points to oldest element */
    int	    esize;	    /* element size */
    int	    capt;	    /* capacity */
} Queue;

void
init_queue(Queue *queue, int elem_size);

void
free_queue(Queue *queue);

void
enqueue(Queue *queue, void *x);

int
queue_empty(Queue *queue);

void *
dequeue(Queue *queue);

void
clear_queue(Queue *queue);
#endif

#ifndef PRIORITY_QUEUE
#define PRIORITY_QUEUE
typedef struct priority_queue_t {
    struct priority_queue_t *next;
    void *elem;
    int  key;
} P_Queue;
#endif
void p_enqueue(P_Queue **headList, void *newItem, int key);
void* p_dequeue(P_Queue **headList);
int p_queue_empty(P_Queue **headList);

const void *
my_bsearch(const void *key, const void *base, size_t n, size_t size,
	int (*cmp)(const void *k, const void *datum));

void
my_insert(const void *x, void *base, void *y, int *nelem, int size);


void
init_stack(Stack *stack, int elem_size);
void
free_stack(Stack *stack);
void
stack_push(Stack *stack, void *x);
int
stack_empty(Stack *stack);
void *
stack_pop(Stack *stack);
void
clear_stack(Stack *stack);
void
copy_stack(Stack *y, Stack *x);


int
bits(unsigned x);

/* A work list for analysis */
struct worklist {
	void* data;
	struct worklist* next;
};
typedef struct worklist worklist_s;
typedef struct worklist* worklist_p;

int isEmpty(worklist_p Wlist);
void addToWorkList(worklist_p* Wlist, void* data);
void addAfterNode(void *data, worklist_p *prvNode, worklist_p *headNode);
void* removeOneFromWorkList(worklist_p* Wlist);
void freeList(worklist_p *Wlist);

/*get next token of str[] from position *pos to *token, pos is updated*/
int isDecNum(char c);
int isHexNum(char c);
int getNextElem(char *str, int *pos, char *token);

int getNextToken(char *token, char *str, char *pos, char *delim);

/* return log of a number to the base 2 */
int log_base2(int n);

#define fatal(fmt, args...)     \
  _fatal(__FILE__, __FUNCTION__, __LINE__, fmt, ## args)
void
_fatal(const char *file, const char *func, int line, const char *fmt, ...)
__attribute__ ((noreturn));

#endif
