#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include "cache.h"
#include "tcfg.h"
#include "address.h"
#include "common.h"
#include "bpred.h"
#include "loops.h"

#define CINFTY assoc_l2 

extern tcfg_node_t** tcfg;
extern int num_tcfg_nodes;
extern prog_t prog;

/* The instruction set */
extern isa_t* isa;
extern int gcd(int a, int b);

extern int nsets, bsize, assoc;
/* sudiptac ::: adding options for level 1 data cache */
extern int nsets_dl1, bsize_dl1, assoc_dl1, cache_dl1_lat;

/* sudiptac ::: adding options for level 2 cache 
 * (it could be unified or separate instruction cache) */
extern int nsets_l2, bsize_l2, assoc_l2, cache_dl2_lat, cache_il2_lat;
extern int mem_lat[2];
extern int enable_il2cache;
extern int enable_ul2cache;

/* cleekee: bpred info */
extern int bpred_scheme;
extern de_inst_t ***mp_insts;
extern int *num_mp_insts;

#ifdef _DEBUG
static void dumpCacheBB(acs_p** acs, FILE* fp);
int analysis = 0;
int unified = 0;
#endif
int l1_d1_ps = 0;
int l1_i1_ps = 0;
int i1_u1_ps = 0;
int u1_d1_ps = 0;
int opt = 0;
extern ric_p getAddrBaseOffset(de_inst_t* inst, int base, int offset, int opt);
extern ric_p getAddrBaseIndex(de_inst_t* inst, int base, int index, int opt);
int X, Y, B;

/* Error message routine */
void prerr(char* msg) {
	printf("PANIC ***** %s. Exiting now.......\n", msg);
	exit(-1);
}

/* cleekee: Print ACS (debugging purpose) - can remove */
void printAcs(acs_p** acs_print) {
	int i, numset;
	acs_p* acs_set_print = NULL;
	mem_blk_set_t* mem_blk_h_print = NULL;

	for (numset = 0; numset < MAX_CACHE_SET; numset++) {
		printf("set %i:\n", numset);
		for (i = 0; i < CACHE_SET_SIZE; i++) {
			acs_set_print = acs_print[numset];
			if (acs_set_print != NULL) {
				if (acs_set_print[i] != NULL
					)
					mem_blk_h_print = acs_set_print[i]->mem_blk_h;
				else
					printf("-");
			} else
				printf("N/A");

			while (mem_blk_h_print != NULL) {
				printf("%i ", mem_blk_h_print->block);
				mem_blk_h_print = mem_blk_h_print->next;
			}

			printf("\n");
		}
	}
	printf("\n");
}

/* Create a cache set */
acs_p* makeCacheSet(void) {
	acs_p* ret;

	/* To accomodate the victim cache block, cache-set size is set
	 * one more than the given parameter */
	ret = (acs_p *) malloc((CACHE_SET_SIZE + 1) * sizeof(acs_p));
	CHECK_MEM(ret);
	memset(ret, 0, (CACHE_SET_SIZE + 1) * sizeof(acs_p));

	return ret;
}

/* Free a set of linked memory blocks */
void freeMemBlock(mem_blk_set_t* head) {
	if (!head)
		return;

	freeMemBlock(head->next);
	head->next = NULL;

#ifdef _DELETE
	printf("Freeing mem block = %x\n", head);
#endif

	free(head);
}

/* Free an abstract cache line */
void freeCacheLine(acs_p acl) {
	if (!acl)
		return;

	freeMemBlock(acl->mem_blk_h);
	acl->mem_blk_h = NULL;

	free(acl);
}

/* Free an abstract cache set */
void freeCacheSet(acs_p* acs) {
	int i;

	if (!acs)
		return;

	for (i = 0; i <= CACHE_SET_SIZE; i++) {
		freeCacheLine(acs[i]);
		acs[i] = NULL;
	}

	free(acs);
}

/* Free an abstract cache state */
void freeCacheState(acs_p** acs) {
	int i;

	if (!acs)
		return;

	for (i = 0; i < MAX_CACHE_SET; i++) {
		freeCacheSet(acs[i]);
		acs[i] = NULL;
	}

	free(acs);
}

/* Get all memory referenced by this address range */
mem_blk_set_t* getMemoryBlocks(ric_p addr) {
	mem_blk_set_t* mem_set = NULL;
	mem_blk_set_t* temp;
	int i;
	int prev = -1;
	int count = 0;

	for (i = addr->lower_bound; i <= addr->upper_bound; i += addr->stride) {
		if (prev == GET_MEM(i)
			)
			continue;
		prev = GET_MEM(i);
		temp = (mem_blk_set_t *) malloc(sizeof(mem_blk_set_t));
		CHECK_MEM(temp);

		/* Assume that all addresses are aligned */
		temp->block = prev;
		temp->next = mem_set;
		mem_set = temp;
		count++;
		/* if number of memory blocks for this address set is more than 
		 * the cache size then the cache is flushed */
		if (count > MAX_CACHE_SET * CACHE_SET_SIZE
			)
			break;
		if (!addr->stride)
			break;
	}

	return mem_set;
}

/* Make an empty cache block */
acs_p makeEmpty(void) {
	acs_p ret;

	ret = (acs_p) malloc(sizeof(acs_s));
	CHECK_MEM(ret);
	/* Nothing in the cache block */
	ret->mem_blk_h = NULL;

	return ret;
}

/* Returns 1 if a particular memory block is present in a given
 * Cache block */
int isResident(mem_blk_set_t* mem_blk_h, mem_blk_set_t* item) {
	mem_blk_set_t* iter;

	for (iter = mem_blk_h; iter; iter = iter->next) {
		if (iter->block == item->block)
			return 1;
	}

	return 0;
}

/* Check for a given set of memory blocks whether its
 * superset (may not be proper) is present in any of 
 * the cache block */
int checkForInclusionSingle(acs_p* acs_in, mem_blk_set_t* mem_blk_set) {
	mem_blk_set_t* iter;
	int i;

	for (i = 0; i <= CACHE_SET_SIZE; i++) {
		for (iter = mem_blk_set; iter; iter = iter->next) {
			if (!acs_in[i])
				continue;
			else if (isResident(acs_in[i]->mem_blk_h, iter))
				break;
		}
		if (iter) {
			return i;
		}
	}

	/* oops .. Not found memory block in the cache */
	return -1;
}

/* Count the number of memory blocks present */
int getCardinality(mem_blk_set_t* mem_blk_set) {
	mem_blk_set_t* iter;
	int count = 0;

	for (iter = mem_blk_set; iter; iter = iter->next)
		count++;

	return count;
}

/* Make a copy of the cache block */
acs_p makeCopy(acs_p acs_in) {
	acs_p ret;
	mem_blk_set_t* iter;

	if (!acs_in)
		return NULL;

	ret = (acs_p) malloc(sizeof(acs_s));
	CHECK_MEM(ret);
	memset(ret, 0, sizeof(acs_s));
	ret->mem_blk_h = NULL;

	for (iter = acs_in->mem_blk_h; iter; iter = iter->next) {
		mem_blk_set_t* temp = (mem_blk_set_t *) malloc(sizeof(mem_blk_set_t));
		CHECK_MEM(temp);
		temp->block = iter->block;
		temp->next = ret->mem_blk_h;
		ret->mem_blk_h = temp;
	}

	return ret;
}

/* Make a cache block from a set of memory blocks */
acs_p makeCacheBlock(mem_blk_set_t* mem_blk_set) {
	acs_p ret;
	mem_blk_set_t* iter;

	if (!mem_blk_set)
		return NULL;

	ret = (acs_p) malloc(sizeof(acs_s));
	CHECK_MEM(ret);
	memset(ret, 0, sizeof(acs_s));
	ret->mem_blk_h = NULL;

	for (iter = mem_blk_set; iter; iter = iter->next) {
		mem_blk_set_t* temp = (mem_blk_set_t *) malloc(sizeof(mem_blk_set_t));
		CHECK_MEM(temp);
		temp->block = iter->block;
		temp->next = ret->mem_blk_h;
		ret->mem_blk_h = temp;
	}

	return ret;
}

/* Set intersection of the contents of two cache blocks */
/* and return the result */
acs_p Intersect(acs_p acs1, acs_p acs2) {
	acs_p ret;
	mem_blk_set_t* iter;

	if (!acs1 || !acs2)
		return NULL;

	ret = makeEmpty();

	for (iter = acs2->mem_blk_h; iter; iter = iter->next) {
		/* If the cache block is present in both of the 
		 * argument cache blocks, then it is present in 
		 * the return cache block. Useful for must 
		 * analysis */
		if (isResident(acs1->mem_blk_h, iter)) {
			mem_blk_set_t* temp = (mem_blk_set_t *) malloc(
					sizeof(mem_blk_set_t));
			CHECK_MEM(temp);
			temp->block = iter->block;
			temp->next = ret->mem_blk_h;
			ret->mem_blk_h = temp;
		}
	}

	return ret;
}

/* Set union of the contents of two cache blocks */
/* and return the result */
acs_p Union(acs_p acs1, acs_p acs2) {
	acs_p ret;
	mem_blk_set_t* iter;

	if (!acs1 && !acs2)
		return NULL;

	/* Copy the first cache block */
	ret = makeCopy(acs1);

	if (!acs2)
		return ret;

	for (iter = acs2->mem_blk_h; iter; iter = iter->next) {
		if (!ret) {
			ret = (acs_p) malloc(sizeof(acs_s));
			CHECK_MEM(ret);
			ret->mem_blk_h = NULL;
		}
		if (!isResident(ret->mem_blk_h, iter)) {
			mem_blk_set_t* temp = (mem_blk_set_t *) malloc(
					sizeof(mem_blk_set_t));
			CHECK_MEM(temp);
			temp->block = iter->block;
			temp->next = ret->mem_blk_h;
			ret->mem_blk_h = temp;
		}
	}

	return ret;
}

/* Set union of one cache block ans a set of memory blocks
 */
acs_p UnionCacheMem(acs_p acs1, mem_blk_set_t* mem_blk_set) {
	acs_p ret = NULL;
	mem_blk_set_t* iter;

	if (!mem_blk_set)
		return acs1;

	/* Copy the first cache block */
	ret = makeCopy(acs1);

	for (iter = mem_blk_set; iter; iter = iter->next) {
		if (!ret) {
			ret = (acs_p) malloc(sizeof(acs_s));
			memset(ret, 0, sizeof(acs_s));
		}
		if (!isResident(ret->mem_blk_h, iter)) {
			mem_blk_set_t* temp = (mem_blk_set_t *) malloc(
					sizeof(mem_blk_set_t));
			CHECK_MEM(temp);
			temp->block = iter->block;
			temp->next = ret->mem_blk_h;
			ret->mem_blk_h = temp;
		}
	}

	return ret;
}

/* check number of conflicting memory blocks with memory block containing 
 * instruction "cinst" inside basic block bbi */
int checkForConflicts(tcfg_node_t* bbi, de_inst_t* cinst, int age,
		char first_word, int *conflicts) {
	cfg_node_t* bb = bbi->bb;
	de_inst_t* inst = bb->code;
	int prev_blk = -1;
	int blk;
	int cblk;
	int shift = 0;

	if (first_word)
		cblk = GET_MEM(cinst->addr);
	else
		cblk = GET_MEM(cinst->addr + SIZE_OF_WORD);

	while (inst != cinst) {
		blk = GET_MEM(inst->addr);

		if (GET_SET(blk) == GET_SET(cblk) && blk != cblk) {
			/* sudiptac: make sure that you do not count multiple 
			 * conflicts from the same memory block */
			if (blk != prev_blk)
				shift++;
			prev_blk = blk;
		} else if (blk == cblk) {
			age = shift = 0;
			break;
		}

		inst++;
	}

	*conflicts = age + shift;

	if (age != -1 && age + shift < CACHE_SET_SIZE
		)
		return 1;

	return 0;
}

/* Check for a given set of memory blocks whether its
 * superset (may not be proper) is present in the entire 
 * cache */
int checkForOnePresence(acs_p** acs_in, mem_blk_set_t* mem_blk_set) {
	mem_blk_set_t* iter;
	int i, k;

	for (iter = mem_blk_set; iter; iter = iter->next) {
		k = GET_SET(iter->block);
		for (i = 0; i < CACHE_SET_SIZE; i++) {
			if (acs_in[k][i] && isResident(acs_in[k][i]->mem_blk_h, iter))
				return 1;
		}
	}

	return 0;
}

/* Check for a given set of memory blocks whether its
 * superset (may not be proper) is present in the entire 
 * cache */
int checkForPresence(acs_p** acs_in, mem_blk_set_t* mem_blk_set) {
	mem_blk_set_t* iter;
	int i, k;

	for (iter = mem_blk_set; iter; iter = iter->next) {
		k = GET_SET(iter->block);

		for (i = 0; i < CACHE_SET_SIZE; i++) {
			if (acs_in[k] && acs_in[k][i]
					&& isResident(acs_in[k][i]->mem_blk_h, iter))
				break;
		}

		if (i == CACHE_SET_SIZE
			)
			return -1;
	}

	/* return the position of memory block in the corresponding cache set */
	return i;
}

/* Check for a given set of memory blocks whether its
 * superset (may not be proper) is present in the entire 
 * cache */
int checkForVictim(acs_p** acs_in, mem_blk_set_t* mem_blk_set) {
	mem_blk_set_t* iter;
	int i;

	for (iter = mem_blk_set; iter; iter = iter->next) {
		for (i = 0; i < MAX_CACHE_SET; i++) {
			if (acs_in[i][PSEUDO]
					&& isResident(acs_in[i][PSEUDO]->mem_blk_h, iter))
				return 1;
		}
	}

	return 0;
}

/* Check for a given set of memory blocks whether its
 * superset (may not be proper) is present in any of 
 * the cache block */
int checkForInclusion(acs_p* acs_in, mem_blk_set_t* mem_blk_set) {
	mem_blk_set_t* iter;
	int i;

	for (i = 0; i < CACHE_SET_SIZE; i++) {
		for (iter = mem_blk_set; iter; iter = iter->next) {
			if (acs_in[i] && !isResident(acs_in[i]->mem_blk_h, iter))
				break;
		}
		if (!iter)
			return i;
	}

	/* oops .. Not found memory block in the cache */
	return -1;
}

/* Get the memory blocks mapping to the same set */
mem_blk_set_t* getMemoryBlockOfSet(mem_blk_set_t* mem_blk, int set) {
	mem_blk_set_t* head = NULL;
	mem_blk_set_t* iter;
	int st;

	if (!mem_blk)
		return NULL;

	for (iter = mem_blk; iter; iter = iter->next) {
		st = GET_SET(iter->block);
		if (st == set) {
			mem_blk_set_t* temp = (mem_blk_set_t *) malloc(
					sizeof(mem_blk_set_t));
			CHECK_MEM(temp);
			temp->block = iter->block;
			temp->next = head;
			head = temp;
		}
	}

	return head;
}

/* Take the set difference of a cache line and a memory block */
acs_p Difference(acs_p acs, mem_blk_set_t* mem_blk) {
	mem_blk_set_t* iter;
	acs_p ret;

	if (!acs)
		return NULL;

	ret = (acs_p) malloc(sizeof(acs_s));
	CHECK_MEM(ret);
	ret->mem_blk_h = NULL;

	for (iter = acs->mem_blk_h; iter; iter = iter->next) {
		if (iter->block != mem_blk->block) {
			mem_blk_set_t* temp = (mem_blk_set_t *) malloc(
					sizeof(mem_blk_set_t));
			CHECK_MEM(temp);
			temp->block = iter->block;
			temp->next = ret->mem_blk_h;
			ret->mem_blk_h = temp;
		}
	}

	return ret;
}

/* Copy an abstract cache state */
acs_p* copy_cache(acs_p* acs) {
	int i;
	acs_p* dest = NULL;

	if (!acs)
		return NULL;

	/* Allocate memory for the copying destination */
	dest = makeCacheSet();

	for (i = 0; i <= CACHE_SET_SIZE; i++) {
		dest[i] = makeCopy(acs[i]);
	}

	return dest;
}

/* abstract cache set update for a singleton memory block */
acs_p* update_singleton(acs_p* acs, mem_blk_set_t* mem_blk_set) {
	int line = 0;
	acs_p* ret;
	acs_p cur;
	int i;
	mem_blk_set_t* temp = NULL;

	temp = (mem_blk_set_t *) malloc(sizeof(mem_blk_set_t));
	CHECK_MEM(temp);
	temp->block = mem_blk_set->block;
	temp->next = NULL;

	ret = makeCacheSet();

	for (line = 0; line < CACHE_SET_SIZE; line++) {
		/* block is not present in the cache line */
		if (!acs) {
			line = CACHE_SET_SIZE;
			break;
		}
		/* block is present in the cache line */
		if (acs[line] && isResident(acs[line]->mem_blk_h, temp))
			break;
	}

	/* The memory block is present in the cache */
	if (line < CACHE_SET_SIZE)
	{
		for (i = 1; i < line; i++)
			ret[i] = makeCopy(acs[i - 1]);
		if (line > 0) {
			cur = Difference(acs[line], temp);
			ret[line] = Union(cur, acs[line - 1]);
#ifdef MEM_FREE
			freeCacheLine(cur);
			cur = NULL;
#endif
		}
		for (i = line + 1; i < CACHE_SET_SIZE; i++)
			ret[i] = makeCopy(acs[i]);
		ret[0] = makeCacheBlock(temp);

		/* For May analysis */
		if (line == 0 && acs[0]) {
			cur = Difference(acs[0], temp);
			ret[1] = Union(cur, ret[1]);
#ifdef MEM_FREE
			freeCacheLine(cur);
			cur = NULL;
#endif
		}
	}

	/* The memory block is not present in the cache */
	else {
		if (acs) {
			for (i = 1; i < CACHE_SET_SIZE; i++)
				ret[i] = makeCopy(acs[i - 1]);
		}
		ret[0] = makeCacheBlock(temp);
		if (acs) {
			/* For persistence analysis collect the victim cache 
			 * blocks */
			ret[PSEUDO] = Union(acs[PSEUDO], acs[CACHE_SET_SIZE - 1]);
		}
	}

#ifdef MEM_FREE
	free(temp);
#endif

	return ret;
}

/* Must join of cache analysis */
acs_p* joinCacheMust(acs_p* acs1, acs_p* arg) {
	acs_p temp = NULL;
	acs_p val = NULL;
	acs_p val2 = NULL;
	int i, j;
	acs_p* acs;

	if (!acs1)
		return copy_cache(arg);

	acs = makeCacheSet();

	/* Do cache join for all the abstract cache sets of a cache */
	for (i = 0; i < CACHE_SET_SIZE; i++) {
		temp = NULL;
		val = NULL;

		/* If one memory block is present in more than one cache
		 * block take the cache block which is older in age. 
		 * Following code take care of this in case of must 
		 * analysis. */
		for (j = i; j >= 0; j--) {
			val = temp;
			val2 = Intersect(acs1[i], arg[j]);
			temp = Union(temp, val2);
#ifdef MEM_FREE
			freeCacheLine(val);
			freeCacheLine(val2);
			val = NULL;
#endif
		}

		for (j = i; j >= 0; j--) {
			val = temp;
			val2 = Intersect(acs1[i], arg[j]);
			temp = Union(temp, val2);
#ifdef MEM_FREE
			freeCacheLine(val);
			freeCacheLine(val2);
			val = NULL;
#endif
		}

		acs[i] = temp;
	}

	return acs;
}

/* May join of cache analysis */
acs_p* joinCacheMay(acs_p* acs1, acs_p* arg) {
	acs_p temp = NULL;
	acs_p val = NULL;
	int i, j;
	acs_p* acs;
	mem_blk_set_t* iter;

	if (!acs1)
		return copy_cache(arg);

	acs = makeCacheSet();

	for (i = 0; i < CACHE_SET_SIZE; i++) {
		temp = NULL;
		val = NULL;

		/* PRESENT in ACS-0 but not in ACS-1 */
		if (acs1[i]) {
			for (iter = acs1[i]->mem_blk_h; iter; iter = iter->next) {
				for (j = i - 1; j >= 0; j--) {
					if (arg[j] && isResident(arg[j]->mem_blk_h, iter)) {
						break;
					}
				}
				if (j < 0) {
					mem_blk_set_t* cur = (mem_blk_set_t *) malloc(
							sizeof(mem_blk_set_t));
					cur->block = iter->block;
					cur->next = NULL;
					val = temp;
					temp = UnionCacheMem(temp, cur);
#ifdef MEM_FREE
					freeCacheLine(val);
					free(cur);
					cur = NULL;
					val = NULL;
#endif
				}
			}
		}
		/* PRESENT in ACS-1 but not in ACS-0 */
		if (arg[i]) {
			for (iter = arg[i]->mem_blk_h; iter; iter = iter->next) {
				for (j = i - 1; j >= 0; j--) {
					if (acs1[j] && isResident(acs1[j]->mem_blk_h, iter)) {
						break;
					}
				}
				if (j < 0) {
					mem_blk_set_t* cur = (mem_blk_set_t *) malloc(
							sizeof(mem_blk_set_t));
					cur->block = iter->block;
					cur->next = NULL;
					val = temp;
					temp = UnionCacheMem(temp, cur);
#ifdef MEM_FREE
					freeCacheLine(val);
					free(cur);
					val = NULL;
					cur = NULL;
#endif
				}
			}
		}
		acs[i] = temp;
	}

	return acs;
}

/* Persistence join of cache analysis */
acs_p* joinCachePS(acs_p* acs1, acs_p* arg) {
	acs_p temp = NULL;
	acs_p val = NULL;
	int i, j;
	acs_p* acs;
	mem_blk_set_t* iter;

	if (!acs1)
		return copy_cache(arg);

	acs = makeCacheSet();

	for (i = 0; i <= CACHE_SET_SIZE; i++) {
		temp = NULL;
		val = NULL;

		if (acs1[i]) {
			for (iter = acs1[i]->mem_blk_h; iter; iter = iter->next) {
				for (j = i + 1; j <= CACHE_SET_SIZE; j++) {
					if (arg[j] && isResident(arg[j]->mem_blk_h, iter)) {
						break;
					}
				}
				if (j > CACHE_SET_SIZE)
				{
					mem_blk_set_t* cur = (mem_blk_set_t *) malloc(
							sizeof(mem_blk_set_t));
					cur->block = iter->block;
					cur->next = NULL;
					val = temp;
					temp = UnionCacheMem(temp, cur);
#ifdef MEM_FREE
					freeCacheLine(val);
					free(cur);
					val = NULL;
					cur = NULL;
#endif
				}
			}
		}
		if (arg[i]) {
			for (iter = arg[i]->mem_blk_h; iter; iter = iter->next) {
				for (j = i + 1; j <= CACHE_SET_SIZE; j++) {
					if (acs1[j] && isResident(acs1[j]->mem_blk_h, iter)) {
						break;
					}
				}
				if (j > CACHE_SET_SIZE)
				{
					mem_blk_set_t* cur = (mem_blk_set_t *) malloc(
							sizeof(mem_blk_set_t));
					cur->block = iter->block;
					cur->next = NULL;
					val = temp;
					temp = UnionCacheMem(temp, cur);
#ifdef MEM_FREE
					freeCacheLine(val);
					free(cur);
					val = NULL;
					cur = NULL;
#endif
				}
			}
		}
		acs[i] = temp;
	}

	return acs;
}

/* Join function during data cache update. Depends on the
 * direction of analysis (Must, May and Persistence) */
acs_p* joinCache(acs_p* acs1, acs_p* arg, ANALYSIS_T type) {
	/* Join operation for for must cache analysis */
	if (type == MUST) {
		return joinCacheMust(acs1, arg);
	}

	/* Join function for MAY analysis */
	else if (type == MAY) {
		return joinCacheMay(acs1, arg);
	}

	/* Join function for persistence analysis */
	else if (type == PERSISTENCE) {
		return joinCachePS(acs1, arg);
	}

	return NULL;
}

/* Instruction cache update function */
acs_p** update_abs_inst(acs_p** acs_in, unsigned addr) {
	mem_blk_set_t mem_blk;
	acs_p* temp;
	acs_p* cur;
	acs_p** acs_out;
	int set, i;

	mem_blk.block = GET_MEM(addr);
	mem_blk.next = NULL;

	acs_out = (acs_p **) malloc(MAX_CACHE_SET * sizeof(acs_p *));
	memset(acs_out, 0, MAX_CACHE_SET * sizeof(acs_p *));

	if (acs_in) {
		for (i = 0; i < MAX_CACHE_SET; i++)
			acs_out[i] = copy_cache(acs_in[i]);
	}

	/* Each instruction corresponds to two addresses. Update
	 * the instruction cache state accordingly */
	set = GET_SET(mem_blk.block);
	if (acs_in)
		temp = update_singleton(acs_in[set], &mem_blk);
	else
		temp = update_singleton(NULL, &mem_blk);
	mem_blk.block = GET_MEM(addr + SIZE_OF_WORD);
	set = GET_SET(mem_blk.block);
	cur = acs_out[set];
	acs_out[set] = update_singleton(temp, &mem_blk);

	/* free up memory */
#ifdef MEM_FREE
	freeCacheSet(temp);
	freeCacheSet(cur);
	temp = cur = NULL;
#endif

	return acs_out;
}

/* Check whether two abstract cache blocks are same or not */
int is_same_cache_block(acs_p acs1, acs_p acs2) {
	mem_blk_set_t* iter;

	if (!acs1 && !acs2)
		return 1;
	if (!acs1 || !acs2)
		return 0;

	for (iter = acs1->mem_blk_h; iter; iter = iter->next) {
		if (!isResident(acs2->mem_blk_h, iter))
			return 0;
	}

	if (getCardinality(acs1->mem_blk_h) == getCardinality(acs2->mem_blk_h))
		return 1;

	return 0;
}

/* Check whether two abstract cache states are identical */
int checkEquality(acs_p* acs1, acs_p* acs2) {
	int i;

	if (!acs1 && !acs2)
		return 1;
	if (!acs1 || !acs2)
		return 0;
	for (i = 0; i <= CACHE_SET_SIZE; i++) {
		if (!acs1[i] && !acs2[i])
			continue;
		else if (!acs1[i] || !acs2[i])
			return 0;
		else if (!is_same_cache_block(acs1[i], acs2[i]))
			return 0;
	}

	return 1;
}

/* Transfer/update function for l2 instruction abstract cache */
void transforml2InstCacheState(tcfg_node_t* bbi, int* change_flag,
		ANALYSIS_T type, int iteration_count) {
	de_inst_t* inst;
	int n_inst;
	acs_p** acs_out = NULL;
	acs_p** cur_acs = NULL;
	acs_p** prev_acs;
	acs_p* cur_acs_set;
	int k;

	assert(bbi);
	assert(bbi->bb);
	inst = bbi->bb->code;

	/* save a copy to check the change in abstract cache states */
	acs_out = (acs_p **) malloc(MAX_CACHE_SET * sizeof(acs_p *));
	CHECK_MEM(acs_out);
	memset(acs_out, 0, MAX_CACHE_SET * sizeof(acs_p *));

	if (!bbi->acs_out) {
		bbi->acs_out = (acs_p **) malloc(MAX_CACHE_SET * sizeof(acs_p *));
		CHECK_MEM(bbi->acs_out);
		memset(bbi->acs_out, 0, MAX_CACHE_SET * sizeof(acs_p *));
	}

	for (k = 0; k < MAX_CACHE_SET; k++) {
		acs_out[k] = copy_cache(bbi->acs_out[k]);

		if (!bbi->acs_out[k])
			bbi->acs_out[k] = makeCacheSet();
	}
#if 0
	/* cleekee: account for cache changes by mispredicted instructions */
	if (bpred_scheme != NO_BPRED) {
		acs_spec = (acs_p **) malloc(MAX_CACHE_SET * sizeof(acs_p *));
		CHECK_MEM(acs_spec);
		memset(acs_spec, 0, MAX_CACHE_SET * sizeof(acs_p *));

		CHECK_MEM(num_mp_insts);
		CHECK_MEM(mp_insts);

		bbi_in_p = bbi->in;

		/* iterate through every incoming edge*/
		while (bbi_in_p != NULL) {
			/* sudiptac: check whether first iteration, skip the speculation 
			 * through back edge in that case */
			is_backedge =
					((loop_map[bbi->id] == loop_map[bbi_in_p->src->id])
							&& (bbi == loop_map[bbi->id]->head)) ? 1 : 0;
			if (iteration_count == 0 && is_backedge) {
				bbi_in_p = bbi_in_p->next_in;
				continue;
			}

			/*ipdate incoming ACS with mispredicated instructions */
			for (n_inst = 0; n_inst < num_mp_insts[bbi_in_p->id]; n_inst++) {
				bbi_n_inst = 0;

				/* identify tcfg node that contains mp_insts */
				if (!n_inst) {
					if (bbi_in_p == bbi_in_p->src->out)
						bbi_spec = bbi_in_p->next_out->dst;
					else
						bbi_spec = bbi_in_p->src->out->dst;
				}

				/* point bbi_spec to next tcfg node containing mp_insts */
				if (bbi_n_inst >= bbi_spec->bb->num_inst) {
					bbi_spec = bbi_spec->out->dst;
					bbi_n_inst = 0;
				}

				/* Use cache access classification method */
				if (inst_chmc_l1[bbi_spec->id][bbi_n_inst] == ALL_MISS) {
					if (!n_inst)
						cur_acs = update_abs_inst(bbi_in_p->src->acs_out,
								mp_insts[bbi_in_p->id][n_inst]->addr);
					else
						cur_acs = update_abs_inst(cur_acs,
								mp_insts[bbi_in_p->id][n_inst]->addr);
				} else if (inst_chmc_l1[bbi_spec->id][bbi_n_inst]
						== NOT_CLASSIFIED
						|| inst_chmc_l1[bbi_spec->id][bbi_n_inst] == PS) {
					if (!n_inst) {
						prev_acs = bbi_in_p->src->acs_out;
						cur_acs = update_abs_inst(bbi_in_p->src->acs_out,
								mp_insts[bbi_in_p->id][n_inst]->addr);
					} else {
						prev_acs = cur_acs;
						cur_acs = update_abs_inst(cur_acs,
								mp_insts[bbi_in_p->id][n_inst]->addr);
					}

					for (k = 0; k < MAX_CACHE_SET; k++) {
						cur_acs_set = cur_acs[k];
						cur_acs[k] = joinCache(prev_acs[k], cur_acs[k], type);
#ifdef MEM_FREE
						freeCacheSet(cur_acs_set);
						cur_acs_set = NULL;
#endif
					}
				}

				bbi_n_inst++;
			}

			/* join all incoming ACS as speculated ACS */
			if (cur_acs && num_mp_insts[bbi_in_p->id] > 0) {
				for (k = 0; k < MAX_CACHE_SET; k++) {
					cur_acs_set = acs_spec[k];

					acs_spec[k] = joinCache(acs_spec[k], cur_acs[k], type);
#ifdef MEM_FREE
					freeCacheSet(cur_acs_set);
					cur_acs_set = NULL;
#endif
				}
			}
#ifdef MEM_FREE
			freeCacheState(cur_acs);
			cur_acs = NULL;
#endif
			bbi_in_p = bbi_in_p->next_in;
		}

		/* join speculated ACS with ACS without branch prediction */
		for (k = 0; k < MAX_CACHE_SET; k++) {
			if (!bbi->acs_in || !bbi->acs_in[k])
				continue;

			cur_acs_set = bbi->acs_out[k];

			bbi->acs_out[k] = joinCache(acs_spec[k], bbi->acs_in[k], type);
#ifdef MEM_FREE
			freeCacheSet(cur_acs_set);
			cur_acs_set = NULL;
#endif
		}
#ifdef MEM_FREE
		freeCacheState(acs_spec);
		acs_spec = NULL;
#endif
	}
#endif
	for (n_inst = 0; n_inst < bbi->bb->num_inst; n_inst++) {
#if 0
		isa_name = isa[inst->op_enum].name;

		/* Save a copy to check the equality between the 
		 * previous state and the updated state. This is 
		 * important for the iterative computaion */
		acs_out = (acs_p **) malloc(MAX_CACHE_SET * sizeof(acs_p *));
		memset(acs_out, 0, MAX_CACHE_SET * sizeof(acs_p *));

		if(!inst->acs_out)
		{
			inst->acs_out = (acs_p **) malloc(MAX_CACHE_SET * sizeof(acs_p *));
			memset(inst->acs_out, 0, MAX_CACHE_SET * sizeof(acs_p *));
		}

		for(k = 0; k < MAX_CACHE_SET; k++)
		{
			acs_out[k] = copy_cache(inst->acs_out[k]);

			if(!inst->acs_out[k])
			{
				inst->acs_out[k] = makeCacheSet();
			}
		}
#endif

		/* Use cache access classification method */
		if (inst_chmc_l1[bbi->id][n_inst] == ALL_MISS) {
#if 0
			cur_acs = inst->acs_out;
			inst->acs_out = update_abs_inst(inst->acs_in, inst->addr);
#endif

			cur_acs = bbi->acs_out;

			/* cleekee: bbi->acs_out is already updated if bpred is enabled */
			if (!n_inst && bpred_scheme == NO_BPRED)
				bbi->acs_out = update_abs_inst(bbi->acs_in, inst->addr);
			else
				bbi->acs_out = update_abs_inst(bbi->acs_out, inst->addr);

#ifdef MEM_FREE
			freeCacheState(cur_acs);
			cur_acs = NULL;
#endif
		} else if (inst_chmc_l1[bbi->id][n_inst] == NOT_CLASSIFIED
				|| inst_chmc_l1[bbi->id][n_inst] == PS) {
#if 0
			cur_acs = inst->acs_out;
			inst->acs_out = update_abs_inst(inst->acs_in, inst->addr);
#endif
			cur_acs = bbi->acs_out;

			/* cleekee: bbi->acs_out is already updated if bpred is enabled */
			if (!n_inst && bpred_scheme == NO_BPRED) {
				prev_acs = bbi->acs_in;
				bbi->acs_out = update_abs_inst(bbi->acs_in, inst->addr);
			} else {
				prev_acs = bbi->acs_out;
				bbi->acs_out = update_abs_inst(bbi->acs_out, inst->addr);
			}

#if 0
			for(k = 0; k < MAX_CACHE_SET; k++) {
				cur_acs_set = inst->acs_out[k];
				inst->acs_out[k] = joinCache(inst->acs_in[k], inst->acs_out[k], type);
#ifdef MEM_FREE
				freeCacheSet(cur_acs_set);
				cur_acs_set = NULL;
#endif
			}
#endif

			for (k = 0; k < MAX_CACHE_SET; k++) {
				cur_acs_set = bbi->acs_out[k];
				bbi->acs_out[k] = joinCache(prev_acs[k], bbi->acs_out[k], type);
#ifdef MEM_FREE
				freeCacheSet(cur_acs_set);
				cur_acs_set = NULL;
#endif
			}

#ifdef MEM_FREE
			freeCacheState(cur_acs);
			cur_acs = NULL;
#endif
		}
		/* L2 cache is not accessed at all. So no change in abstract cache state, 
		 * just copy the incoming abstract cache state */
		else {
			if (!n_inst) {
				for (k = 0; k < MAX_CACHE_SET; k++) {
					cur_acs_set = bbi->acs_out[k];
					bbi->acs_out[k] = copy_cache(bbi->acs_in[k]);
#ifdef MEM_FREE
					freeCacheSet(cur_acs_set);
					cur_acs_set = NULL;
#endif
				}
			} else {
				/* Do nothing */
			}
		}
#if 0
		else
		{
			for(k = 0; k < MAX_CACHE_SET; k++) {
				cur_acs_set = inst->acs_out[k];
				inst->acs_out[k] = copy_cache(inst->acs_in[k]);
#ifdef MEM_FREE
				freeCacheSet(cur_acs_set);
				cur_acs_set = NULL;
#endif
			}
		}
		/* check whether the abstract cache states change or not */
		for(k = 0; k < MAX_CACHE_SET; k++)
		*change_flag |= !checkEquality(inst->acs_out[k], acs_out[k]);

		/* Linking incoming and outgoing abstract cache states of two 
		 * consecutive basic blocks */
		if(n_inst < bbi->bb->num_inst - 1)
		{
			de_inst_t* next_inst = inst + 1;
			for(k = 0; k < MAX_CACHE_SET; k++)
			next_inst->acs_in[k] = inst->acs_out[k];
			inst++;
		}
#endif
		inst++;
	}

	/* check whether abstract cache states change or not at the end of basic 
	 * block "bbi" */
	for (k = 0; k < MAX_CACHE_SET; k++)
		*change_flag |= !checkEquality(bbi->acs_out[k], acs_out[k]);

	/* sudiptac : free running acs_out */
	freeCacheState(acs_out);
}

/* Transfer/update function for instruction abstract cache */
void transformInstCacheState(tcfg_node_t* bbi, int* change_flag,
		ANALYSIS_T type, int iteration_count) {
	de_inst_t* inst;
	int n_inst;
	acs_p** acs_out;
	acs_p** cur_acs;
	acs_p** acs_spec;
	acs_p* cur_acs_set;
	tcfg_edge_t* bbi_in_p;
	int k;
	char is_backedge = 0;

	assert(bbi);
	assert(bbi->bb);
	inst = bbi->bb->code;

	/* save a copy to check changes in abstract state value */
	acs_out = (acs_p **) malloc(MAX_CACHE_SET * sizeof(acs_p *));
	CHECK_MEM(acs_out);
	memset(acs_out, 0, MAX_CACHE_SET * sizeof(acs_p *));

	if (!bbi->acs_out) {
		bbi->acs_out = (acs_p **) malloc(MAX_CACHE_SET * sizeof(acs_p *));
		CHECK_MEM(bbi->acs_out);
		memset(bbi->acs_out, 0, MAX_CACHE_SET * sizeof(acs_p *));
	}

	for (k = 0; k < MAX_CACHE_SET; k++) {
		acs_out[k] = copy_cache(bbi->acs_out[k]);

		if (!bbi->acs_out[k]) {
			bbi->acs_out[k] = makeCacheSet();
		}
	}

	/* cleekee: account for cache changes by mispredicted instructions */
	if (bpred_scheme != NO_BPRED) {
		acs_spec = (acs_p **) malloc(MAX_CACHE_SET * sizeof(acs_p *));
		CHECK_MEM(acs_spec);
		memset(acs_spec, 0, MAX_CACHE_SET * sizeof(acs_p *));

		CHECK_MEM(num_mp_insts);
		CHECK_MEM(mp_insts);

		bbi_in_p = bbi->in;

		/* iterate through every incoming edge */
		while (bbi_in_p != NULL) {
			/* sudiptac: check whether first iteration, skip the speculation 
			 * through back edge in that case */
			is_backedge =
					((loop_map[bbi->id] == loop_map[bbi_in_p->src->id])
							&& (bbi == loop_map[bbi->id]->head)) ? 1 : 0;
			if (iteration_count == 0 && is_backedge) {
				bbi_in_p = bbi_in_p->next_in;
				continue;
			}
			/* update incoming ACS with mispredicted instructions */
			for (n_inst = 0; n_inst < num_mp_insts[bbi_in_p->id]; n_inst++) {
				if (!n_inst)
					cur_acs = update_abs_inst(bbi_in_p->src->acs_out,
							mp_insts[bbi_in_p->id][n_inst]->addr);
				else
					cur_acs = update_abs_inst(cur_acs,
							mp_insts[bbi_in_p->id][n_inst]->addr);
			}

			/* join all incoming ACS as speculated ACS */
			if (num_mp_insts[bbi_in_p->id] > 0) {
				for (k = 0; k < MAX_CACHE_SET; k++) {
					cur_acs_set = acs_spec[k];

					/* sudiptac: sanity check required ? */
					if (!cur_acs || !cur_acs[k])
						continue;

					acs_spec[k] = joinCache(acs_spec[k], cur_acs[k], type);
#ifdef MEM_FREE
					freeCacheSet(cur_acs_set);
					cur_acs_set = NULL;
#endif
				}
			}
#ifdef MEM_FREE
			freeCacheState(cur_acs);
			cur_acs = NULL;
#endif
			bbi_in_p = bbi_in_p->next_in;
		}

		/* join speculated ACS with ACS without branch prediction */
		for (k = 0; k < MAX_CACHE_SET; k++) {
			if (!bbi->acs_in || !bbi->acs_in[k])
				continue;

			cur_acs_set = bbi->acs_out[k];

			bbi->acs_out[k] = joinCache(acs_spec[k], bbi->acs_in[k], type);
#ifdef MEM_FREE
			freeCacheSet(cur_acs_set);
			cur_acs_set = NULL;
#endif
		}
#ifdef MEM_FREE
		freeCacheState(acs_spec);
		acs_spec = NULL;
#endif
	}

	for (n_inst = 0; n_inst < bbi->bb->num_inst; n_inst++) {
		/* updating cache states through each instruction */
		cur_acs = bbi->acs_out;

		/* cleekee: bbi->acs_out is already updated if bpred is enabled */
		if (!n_inst && (bpred_scheme == NO_BPRED))
			bbi->acs_out = update_abs_inst(bbi->acs_in, inst->addr);
		else
			bbi->acs_out = update_abs_inst(bbi->acs_out, inst->addr);
#ifdef MEM_FREE
		freeCacheState(cur_acs);
		cur_acs = NULL;
#endif
		inst++;
	}

	/* checking equality between two abstract cache states for this 
	 * basic block */
	for (k = 0; k < MAX_CACHE_SET; k++)
		*change_flag |= !checkEquality(bbi->acs_out[k], acs_out[k]);

	/* free running acs_out */
	freeCacheState(acs_out);
}

/* Perform join operation on two abstract cache states */
/* Join operation depends on the direction of cache analysis 
 * (may, must, persistence). This direction of cache analysis 
 * is provided through the argument "type" */
void JoinCacheState(tcfg_node_t* pred, tcfg_node_t* bbi, int type) {
	acs_p* free_p = NULL;
	int i;

	if (!pred)
		return;

#if 0
	/* First instruction of this basic block */
	f_inst = bbi->bb->code;

	/* Last instruction of predecessor basic block */
	l_inst = pred->bb->code + pred->bb->num_inst - 1;
#endif

	/* Get the abstract cache state at the exit point of the last
	 * instruction of the predecessor basic block */
	for (i = 0; i < MAX_CACHE_SET; i++) {
#if 0
		/* no cache state out of the last instruction of an input basic 
		 * block */
		if(!l_inst->acs_out[i])
		continue;
		free_p = f_inst->acs_in[i];
		f_inst->acs_in[i] = joinCache(f_inst->acs_in[i], l_inst->acs_out[i], type);
#endif

		if (!pred->acs_out || !pred->acs_out[i])
			continue;

		free_p = bbi->acs_in[i];
		bbi->acs_in[i] = joinCache(bbi->acs_in[i], pred->acs_out[i], type);

		/* Free the old abstract cache state */
#ifdef MEM_FREE
		freeCacheSet(free_p);
		free_p = NULL;
#endif
	}
}

/* This procedure is called before doing each cache analysis. Cache 
 * analysis is initialized with allocating memory for abstract cache 
 * states. After finishing one analysis and before starting a next 
 * one, this allocated memory should be reclaimed for better memory 
 * management. "cleanupCache" procedure is used for this purpose 
 */
void initializeCache(tcfg_node_t* bbi) {

	bbi->acs_in = (acs_p **) malloc(MAX_CACHE_SET * sizeof(acs_p *));
	CHECK_MEM(bbi->acs_in);
	memset(bbi->acs_in, 0, MAX_CACHE_SET * sizeof(acs_p *));
	bbi->acs_out = (acs_p **) malloc(MAX_CACHE_SET * sizeof(acs_p *));
	CHECK_MEM(bbi->acs_out);
	memset(bbi->acs_out, 0, MAX_CACHE_SET * sizeof(acs_p *));

	//for (i = 0; i < MAX_CACHE_SET; i++)
	//bbi->acs_in[i] = makeCacheSet();
#if 0		  
	assert(inst);

	for(j = 0; j < bbi->bb->num_inst; j++)
	{
		inst->acs_in = (acs_p **)malloc(MAX_CACHE_SET * sizeof(acs_p *));
		memset(inst->acs_in, 0, MAX_CACHE_SET * sizeof(acs_p *));
		inst->acs_out = (acs_p **)malloc(MAX_CACHE_SET * sizeof(acs_p *));
		memset(inst->acs_out, 0, MAX_CACHE_SET * sizeof(acs_p *));
		inst++;
	}
	inst = bbi->bb->code;
	for(i = 0; i < MAX_CACHE_SET; i++)
	{
		inst->acs_in[i] = makeCacheSet();
	}
#endif

}

/* Allocate memory for storing CHMC information of an instruction */
/* inst_chmc_l1[i][j] = CHMC in L1 cache of j-th instruction at i-th tcfg block */
/* inst_chmc_l2[i][j] = CHMC in L2 cache of j-th instruction at i-th tcfg block */
/* also record the age of the memory block in the abstract must cache. This will 
 * later be used for CRPD analysis and the shared cache conflict analysis */
void initialize_CHMC(void) {
	int i, j;

	inst_chmc_l1 = (char **) malloc(num_tcfg_nodes * sizeof(char *));
	CHECK_MEM(inst_chmc_l1);
	inst_age_l1 = (char **) malloc(num_tcfg_nodes * sizeof(char *));
	CHECK_MEM(inst_age_l1);
	inst_chmc_l2 = (char **) malloc(num_tcfg_nodes * sizeof(char *));
	CHECK_MEM(inst_chmc_l2);
	inst_age_l2 = (char **) malloc(num_tcfg_nodes * sizeof(char *));
	CHECK_MEM(inst_age_l2);

	for (i = 0; i < num_tcfg_nodes; i++) {
		inst_chmc_l1[i] = (char *) malloc(tcfg[i]->bb->num_inst * sizeof(char));
		CHECK_MEM(inst_chmc_l1[i]);
		inst_age_l1[i] = (char *) malloc(tcfg[i]->bb->num_inst * sizeof(char));
		CHECK_MEM(inst_age_l1[i]);
		inst_chmc_l2[i] = (char *) malloc(tcfg[i]->bb->num_inst * sizeof(char));
		CHECK_MEM(inst_chmc_l2[i]);
		inst_age_l2[i] = (char *) malloc(tcfg[i]->bb->num_inst * sizeof(char));
		CHECK_MEM(inst_age_l2[i]);

		for (j = 0; j < tcfg[i]->bb->num_inst; j++) {
			//inst_chmc_l1[i][j] = NOT_CLASSIFIED;
			//inst_chmc_l2[i][j] = NOT_CLASSIFIED;
			inst_chmc_l1[i][j] = CINFTY;
			inst_chmc_l2[i][j] = CINFTY;
			inst_age_l1[i][j] = CINFTY;
			inst_age_l2[i][j] = CINFTY;
		}
	}
}

/* For a given instruction addresse classify it as persistence
 * or non-classified (L2 cache) */
void categorize_l2_inst_X_PS_NC(tcfg_node_t* bbi, de_inst_t* inst,
		int inst_id) {
	mem_blk_set_t temp;
	int h1, h2;

	temp.block = GET_MEM(inst->addr);
	temp.next = NULL;

#if 0
	h1 = checkForVictim(inst->acs_in, &temp);
	temp.block = GET_MEM(inst->addr + SIZE_OF_WORD);
	h2 = checkForVictim(inst->acs_in, &temp);
#endif
	h1 = checkForVictim(bbi->acs_in, &temp);
	temp.block = GET_MEM(inst->addr + SIZE_OF_WORD);
	h2 = checkForVictim(bbi->acs_in, &temp);

	if (inst_chmc_l1[bbi->id][inst_id] == ALL_HIT) {
		inst_chmc_l2[bbi->id][inst_id] = ALL_X;
	} else if ((!h1 && !h2)
			&& inst_chmc_l2[bbi->id][inst_id] == NOT_CLASSIFIED) {
		inst_chmc_l2[bbi->id][inst_id] = PS;
	}
	/* Rest are already L2 classified or L2 not classified */
}

/* For a given instruction addresse classify it as all hit
 * or non-classified (L2 cache) */
void categorize_l2_inst_X_AH_NC(tcfg_node_t* bbi, de_inst_t* inst,
		int inst_id) {
	mem_blk_set_t temp;
	int h1, h2;
	int hc1, hc2;
	int conflicts = 0;

	temp.block = GET_MEM(inst->addr);
	temp.next = NULL;

#if 0
	h1 = checkForPresence(inst->acs_in, &temp);
	temp.block = GET_MEM(inst->addr + SIZE_OF_WORD);
	h2 = checkForPresence(inst->acs_in, &temp);
#endif

	h1 = checkForPresence(bbi->acs_in, &temp);
	hc1 = checkForConflicts(bbi, inst, h1, 1, &conflicts);
	temp.block = GET_MEM(inst->addr + SIZE_OF_WORD);
	h2 = checkForPresence(bbi->acs_in, &temp);
	hc2 = checkForConflicts(bbi, inst, h2, 0, &conflicts);

	if (inst_chmc_l1[bbi->id][inst_id] == ALL_HIT) {
		inst_chmc_l2[bbi->id][inst_id] = ALL_X;

		if (hc1 && hc2)
			inst_age_l2[bbi->id][inst_id] = conflicts;
		else
			inst_age_l2[bbi->id][inst_id] = CINFTY;

	} else if (hc1 && hc2) {
		inst_chmc_l2[bbi->id][inst_id] = ALL_HIT;
		inst_age_l2[bbi->id][inst_id] = conflicts;
	} else {
		inst_chmc_l2[bbi->id][inst_id] = NOT_CLASSIFIED;
		inst_age_l2[bbi->id][inst_id] = CINFTY;
	}
}

/* For a given instruction address classify it as all miss
 * or non-classified (L2 cache) */
void categorize_l2_inst_X_AM_NC(tcfg_node_t* bbi, de_inst_t* inst,
		int inst_id) {
	mem_blk_set_t temp;
	int h1, h2;
	int hc1, hc2;
	int conflicts = 0;

	temp.block = GET_MEM(inst->addr);
	temp.next = NULL;

#if 0
	h1 = checkForPresence(inst->acs_in, &temp);
	temp.block = GET_MEM(inst->addr + SIZE_OF_WORD);
	h2 = checkForPresence(inst->acs_in, &temp);
#endif

	h1 = checkForPresence(bbi->acs_in, &temp);
	hc1 = checkForConflicts(bbi, inst, h1, 1, &conflicts);
	temp.block = GET_MEM(inst->addr + SIZE_OF_WORD);
	h2 = checkForPresence(bbi->acs_in, &temp);
	hc2 = checkForConflicts(bbi, inst, h2, 0, &conflicts);

	if (inst_chmc_l1[bbi->id][inst_id] == ALL_HIT) {
		inst_chmc_l2[bbi->id][inst_id] = ALL_X;
	} else if ((!hc1 || !hc2)
			&& inst_chmc_l2[bbi->id][inst_id] == NOT_CLASSIFIED) {
		inst_chmc_l2[bbi->id][inst_id] = ALL_MISS;
	}
	/* Rest are already classified or kept non-classified */
}

/* For a given instruction addresse classify it as all hit
 * or non-classified (L1 cache) */
void categorize_inst_AH_NC(tcfg_node_t* bbi, de_inst_t* inst,
		int inst_id) {
	mem_blk_set_t temp;
	int h1, h2;
	int hc1, hc2;
	int conflicts = 0;

	temp.block = GET_MEM(inst->addr);
	temp.next = NULL;

#if 0
	h1 = checkForPresence(inst->acs_in, &temp);
	temp.block = GET_MEM(inst->addr + SIZE_OF_WORD);
	h2 = checkForPresence(inst->acs_in, &temp);
#endif

	h1 = checkForPresence(bbi->acs_in, &temp);
	hc1 = checkForConflicts(bbi, inst, h1, 1, &conflicts);
	temp.block = GET_MEM(inst->addr + SIZE_OF_WORD);
	h2 = checkForPresence(bbi->acs_in, &temp);
	hc2 = checkForConflicts(bbi, inst, h2, 0, &conflicts);

	if (hc1 && hc2) {
		inst_chmc_l1[bbi->id][inst_id] = ALL_HIT;
		inst_age_l1[bbi->id][inst_id] = conflicts;
	} else {
		inst_chmc_l1[bbi->id][inst_id] = NOT_CLASSIFIED;
		inst_age_l1[bbi->id][inst_id] = CINFTY;
	}
	/* Rest are already non-classified */
}

/* For a given instruction address classify it as persistence
 * or non-classified (L1 cache) */
void categorize_inst_PS_NC(tcfg_node_t* bbi, de_inst_t* inst,
		int inst_id) {
	mem_blk_set_t temp;
	int h1, h2;

	temp.block = GET_MEM(inst->addr);
	temp.next = NULL;

#if 0
	h1 = checkForVictim(inst->acs_in, &temp);
	temp.block = GET_MEM(inst->addr + SIZE_OF_WORD);
	h2 = checkForVictim(inst->acs_in, &temp);
#endif		  
	h1 = checkForVictim(bbi->acs_in, &temp);
	temp.block = GET_MEM(inst->addr + SIZE_OF_WORD);
	h2 = checkForVictim(bbi->acs_in, &temp);

	if (!h1 && !h2 && inst_chmc_l1[bbi->id][inst_id] == NOT_CLASSIFIED) {
		inst_chmc_l1[bbi->id][inst_id] = PS;
	}

	/* Rest are already L1 classified or kept non-classified */
}

/* For a given instruction address classify it as all miss
 * or non-classified (L1 cache) */
void categorize_inst_AM_NC(tcfg_node_t* bbi, de_inst_t* inst,
		int inst_id) {
	mem_blk_set_t temp;
	int h1, h2;
	int hc1, hc2;
	int conflicts = 0;

	temp.block = GET_MEM(inst->addr);
	temp.next = NULL;

#if 0
	h1 = checkForPresence(inst->acs_in, &temp);
	temp.block = GET_MEM(inst->addr + SIZE_OF_WORD);
	h2 = checkForPresence(inst->acs_in, &temp);
#endif

	h1 = checkForPresence(bbi->acs_in, &temp);
	hc1 = checkForConflicts(bbi, inst, h1, 1, &conflicts);
	temp.block = GET_MEM(inst->addr + SIZE_OF_WORD);
	h2 = checkForPresence(bbi->acs_in, &temp);
	hc2 = checkForConflicts(bbi, inst, h2, 0, &conflicts);

	if ((!hc1 || !hc2) && inst_chmc_l1[bbi->id][inst_id] == NOT_CLASSIFIED) {
		inst_chmc_l1[bbi->id][inst_id] = ALL_MISS;
	}
	/* Rest are already L1 classified or kept L1 non-classified */
}

/* Categorize instruction at L2 cache after analysis */
void categorize_L2(int type) {
	de_inst_t* inst;
	int i, j;

	for (i = 0; i < num_tcfg_nodes; i++) {
		inst = tcfg[i]->bb->code;

		for (j = 0; j < tcfg[i]->bb->num_inst; j++) {
			switch (type) {
			case MUST:
				categorize_l2_inst_X_AH_NC(tcfg[i], inst, j);
				break;
			case MAY:
				categorize_l2_inst_X_AM_NC(tcfg[i], inst, j);
				break;
			case PERSISTENCE:
				categorize_l2_inst_X_PS_NC(tcfg[i], inst, j);
				/* set the latency for instruction cache miss */
				/* if (inst->l2_inst_access == NOT_CLASSIFIED && (inst->inst_access == NOT_CLASSIFIED ||
				 inst->inst_access == ALL_MISS))
				 tcfg[i]->inst_cache_delay += L2_MISS_PENALTY; */
				/* Increment number of persistence memory blocks in L2 instruction cache */
				/* else if (inst->l2_inst_access == PS || inst->inst_access == PS)
				 tcfg[i]->n_l2_persistence += 1;	*/
				break;
			default:
				prerr("Unknown analysis type");
			};

			inst++;
		}
	}
}

/* Categorize instruction access patterns. For must analysis :: all hits 
 * or non-classified */
void categorize_L1(int type) {
	de_inst_t* inst;
	int i, j;

	for (i = 0; i < num_tcfg_nodes; i++) {
		inst = tcfg[i]->bb->code;

		for (j = 0; j < tcfg[i]->bb->num_inst; j++) {
			switch (type) {
			case MUST:
				categorize_inst_AH_NC(tcfg[i], inst, j);
				break;
			case MAY:
				categorize_inst_AM_NC(tcfg[i], inst, j);
				/* if(inst->inst_access == ALL_MISS)
				 tcfg[i]->inst_cache_delay += L1_MISS_PENALTY; */
				break;
			case PERSISTENCE:
				categorize_inst_PS_NC(tcfg[i], inst, j);
				/* set the latency for instruction cache miss */
				/* if(inst->inst_access == NOT_CLASSIFIED)
				 tcfg[i]->inst_cache_delay += L1_MISS_PENALTY; */
				/* Increase the no. of persistence instructions by one */
				/* else if(inst->inst_access == PS)
				 tcfg[i]->n_persistence += 1; */
				break;
			default:
				prerr("Unknown analysis type");
			};

			inst++;
		}

	}
}

/* clean up the cache, this section is called before starting 
 * a new cache analysis */
void cleanupCache(void) {
	int i;

	for (i = 0; i < num_tcfg_nodes; i++) {
#if 0
		inst = tcfg[i]->bb->code;
		prev_inst = NULL;
#endif

#ifdef MEM_FREE
		freeCacheState(tcfg[i]->acs_in);
		freeCacheState(tcfg[i]->acs_out);
#endif

#if 0
		for(j = 0; j < tcfg[i]->bb->num_inst; j++)
		{
#ifdef MEM_FREE
			freeCacheState(inst->acs_out);
#endif
			inst->acs_out = NULL;
			/* CAUTION :::: since the input abstract cache state of previous 
			 * instruction and the output abstract cache state of this 
			 * instruction are connected, there is no need to do a double 
			 * memory free */
			if (prev_inst)
			prev_inst->acs_in = NULL;
			prev_inst = inst;
			inst++;
		}
#endif
	}
}

/* Analysis of l2 instruction cache */
void analyze_abs_l2_instr_cache(int type) {
	int change_flag = 1;
	tcfg_edge_t* edge;
	int i, topoidx;
	int iter = 0;

	/* Initialize the abstract cache at the entry of the 
	 * program */
	for (i = 0; i < num_tcfg_nodes; i++)
		initializeCache(tcfg[i]);

	while (change_flag) {
		change_flag = 0;

		for (i = 0; i < num_tcfg_nodes; i++) {
			/* sudiptac: get the topological index */
			topoidx = topo_tcfg[i];

			/* Join cache states from predecessor basic 
			 * blocks */
			for (edge = tcfg[topoidx]->in; edge; edge = edge->next_in) {
				JoinCacheState(edge->src, tcfg[topoidx], type);
			}
			transforml2InstCacheState(tcfg[topoidx], &change_flag, type, iter);
		}
		iter++;
	}

	/* Dump the cache state at end of each basic block */
#ifdef _DEBUG_CRPD
	dumpInstCache();
	printf("L2 Iteration count = %d\n", iter);
#endif

	/* CHMC classification of instructions after analysis */
	categorize_L2(type);

	/* Clean up the cache before the analysis starts */
	cleanupCache();
}

/* Analysis of l1 instruction cache */
void analyze_abs_instr_cache(int type) {
	int change_flag = 1;
	tcfg_edge_t* edge;
	int i, topoidx;
	int iter = 0;

	/* Initialize the abstract cache at the entry of the 
	 * program */
	for (i = 0; i < num_tcfg_nodes; i++)
		initializeCache(tcfg[i]);

	while (change_flag) {
		change_flag = 0;

		for (i = 0; i < num_tcfg_nodes; i++) {
			/* sudiptac: get the topological index */
			topoidx = topo_tcfg[i];
#if 0
			/* cleekee: previous acs_in should be cleared first*/
			/* sudiptac: what about loops ? */
			for(j = 0; j < MAX_CACHE_SET; j++) {
#ifdef   MEM_FREE
				freeCacheSet(tcfg[i]->acs_in[j]);
#endif
				tcfg[i]->acs_in[j]=NULL;
			}
#endif
#ifdef _DEBUG_CRPD
			fprintf(stdout, "computing cache states of bbi %d (%d.%d)\n", topoidx, tcfg[topoidx]->bb->proc->id, \
					tcfg[topoidx]->bb->id);
#endif
			/* Join cache states from predecessor basic 
			 * blocks */
			for (edge = tcfg[topoidx]->in; edge; edge = edge->next_in) {
#ifdef _DEBUG_CRPD
				fprintf(stdout, "join cache states from bbi %d (%d.%d)\n", edge->src->id,
						tcfg[edge->src->id]->bb->proc->id, tcfg[edge->src->id]->bb->id);
#endif
				JoinCacheState(edge->src, tcfg[topoidx], type);
			}
			transformInstCacheState(tcfg[topoidx], &change_flag, type, iter);
		}
		iter++;
#ifdef _DEBUG_WCET
		fprintf(stdout, "iteration count = %d\n", iter);
#endif
	}

	/* Dump the cache state at end of each basic block */
#ifdef _DEBUG_CRPD
	dumpInstCache();
	fprintf(stdout, "Iteration count = %d\n", iter);
#endif	

	/* CHMC classification of instructions after analysis */
	categorize_L1(type);

	/* Clean up the cache before another analysis */
	cleanupCache();
}

/* abstract interpretation based analysis for instruction cache */
void analyze_abs_instr_cache_all() {
	/* set advanced L1 cache features */
	set_cache();
	/* Set L1 cache parameters */
	X = assoc;
	Y = nsets;
	B = bsize;
	/* initialize hit-miss classification */
	initialize_CHMC();

	/* Do must analysis in instruction cache */
	analyze_abs_instr_cache(MUST);
	/* Do may analysis in instruction cache */
	analyze_abs_instr_cache(MAY);
	/* Do persistence analysis for instruction cache */
	//analyze_abs_instr_cache(PERSISTENCE);
	if (enable_il2cache) {
		/* set advanced L2 cache features */
		set_cache_l2();
		/* Set L2 cache parameters */
		X = assoc_l2;
		Y = nsets_l2;
		B = bsize_l2;
		/* Do must analysis in L2 instruction cache */
		analyze_abs_l2_instr_cache(MUST);
		/* Do may analysis in L2 instruction cache */
		analyze_abs_l2_instr_cache(MAY);
		/* Do persistence analysis in L2 instruction cache */
		//analyze_abs_l2_instr_cache(PERSISTENCE);
	}

#if 0
	/* Print categorization of all instructions */
	print_classification();
#endif
}

