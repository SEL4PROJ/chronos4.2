#ifndef __MPA_CACHE_H_
#define __MPA_CACHE_H_
#include "isa.h"
#include "pipeline.h"
#include "scp_address.h"

/*** SCOPED CACHE ANALYSIS ***/

#define L1_DCACHE_ANALYSIS 1
#define L2_DCACHE_ANALYSIS 2
#define UNIFIED_CACHE_ANALYSIS 3
//int current_analysis;
#define SBLK_FREE 3
#define SBLK_DONE 4
#define ACS_IDENTICAL 0
#define ACS_NOT_IDENTICAL 1
#define UNKNOWN_AGE     -1

#define EVICTED     (X+1)
#define MAX_A       4       /*MAX_CACHE_ASSOCIATIVITY*/
struct scope_block { 
    saddr_p     m;          /*scope address of this scoped block*/
    mem_blk_set_t* inst_block;/* address of instruction memory block */
#if 0
    int         age;        /*relative age of this scoped block*/
    saddr_p     ys[MAX_A];  /*younger set*/
#endif
    int         flag;
    int         scp_age; /*scp_age = |yes_set| + |inst_ys_set| + 1*/
    worklist_p  ys_set; /* contains temporal-scopes*/
    worklist_p  inst_ys_set;/* contains instruction memory blocks*/
};
typedef struct scope_block  sblk_s;
typedef struct scope_block* sblk_p;

/*ACS structure: scp_acs[i]=cacheSet[i], addr in increasing order*/
#define scp_acs worklist_p* 

/****** SCOPED PERSISTENCE ANALYSIS FUNCTION *******/
#define WRITE_THRU  1
#define AVOID_ONE_ACCESS_MULTIPLE_AGING 1
/*fdct not converge if AVOID_MULTIPLE_AGING*/
#define AGED        0x1

/****** estimate cache miss of PS blks in loop L ******/

void scp_recalculate_temporal_scope(int* unrolled_loop_map, int* old_loop_bound);
void scp_pre_address_analysis(char* fName, worklist_p**** input_addrset);
loop_t* scp_psloop_dl(mas_inst_t* inst, int level);
int analyze_unpred_access(dat_inst_t *d_inst, inf_node_t* ib);
void scp_store_address_set(void);
void mpaex_datacache(int analysis);
int getIbLB(inf_node_t *ib);

void categorize_ul2_inst_PS_NC(int bbi_id, scp_acs mpa_acs_in, int inst_id,
                de_inst_t* inst, loop_t*lp);
void scp_data_update(scp_acs acs, worklist_p addr_in, loop_t*lp);
char** inst_psnc_ul2;
loop_t*** inst_ps_loop_ul2;
int get_mblk_hitmiss_ul2(tcfg_node_t*, int, loop_t*, int);
int loop_dist(loop_t* lp1, loop_t* lp2);
int scp_addrINacs(saddr_p maddr, scp_acs acs,loop_t*lp);
int scp_cmp_saddr(saddr_p dst, saddr_p src, loop_t* lp);
sblk_p scp_join_search(saddr_p mblk, worklist_p cacheset, loop_t*lp);
sblk_p scp_join_search_inst(mem_blk_set_t* iblock, worklist_p cacheset);
int scp_compareACS(scp_acs acs_a, scp_acs acs_b, loop_t*lp);
int scp_addrINacs(saddr_p maddr, scp_acs acs, loop_t*lp);
loop_t* scp_inner_ps_loop(worklist_p addrset);
void scp_update_Sblk_age(sblk_p sblk);
void uni_update_inst(scp_acs acs, unsigned inst_block);
void scp_test_cache_miss(void);
void scp_compare_sorted_ACSs(loop_t*lp);

#endif
