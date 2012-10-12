#include "scp_cache.h"
#include "arch_funcs.h"

FILE *dbgMpa;

extern int          USE_SEGMENT_SIZE;   /*flag: use segment size for unpred.A*/

extern int	        num_tcfg_loops;
extern loop_t       **loops;      /*array of loops*/
extern loop_t       **loop_s;   /*sping tbid -> loop*/

extern prog_t	    prog;
extern int	        num_tcfg_nodes;
extern tcfg_node_t  **tcfg;
extern int	        num_tcfg_edges;
extern tcfg_edge_t  **tcfg_edges;

extern int          X,Y,B,l1,l2;//X: cache-assoc, Y: # cache-set; B: block-size

scp_acs             *lpOut_acs; //summarized & recomputed acs of inner loops
scp_acs             *lpPersIn;  //lpPersIn[id] = PS blocks of lp->id
worklist_p          *lpReqPS;   //PS.blk needed in loop->id
worklist_p          *prvAcsNode;

int                 lp_coldms[36]; //lp_coldms[id] = number of cold miss in lp id
int                 *visited;   //flag whether this node is visited first time

/*for experiment statistic*/
int totalDataExec, totalPersMiss, totalNPersMiss;

extern int enable_scp_dcache;
extern int enable_scp_dl2cache;
extern int enable_ul2cache;
extern cache_t cache_l2;

#define absInt(x) (x>0?x:-x)

#if 0
static void printCacheSet(FILE*fp, worklist_p set);
static loop_t* bbi_lp(tcfg_node_t *bbi);
static int bbi_lpId(tcfg_node_t *bbi);
static int cpyACS(scp_acs dst, scp_acs src);
static void flushCache(saddr_p mAcc, scp_acs acs_out);
static int singletonAccQuick(dat_inst_t*  d_inst, int lpId);
static int singletonAcc(worklist_p *addrList, saddr_p tsM, dat_inst_t* d_inst, int lpId);
static void PS_data_update(scp_acs acs_out, dat_inst_t *d_inst, loop_t *lp);
static int PS_join (scp_acs dst, scp_acs src, loop_t* lp);
static void transform_bbi_dcache(tcfg_node_t *bbi, loop_t* lp,int type);
static void analyze_loop_ps(loop_t *lp);
static void getOuterPS(loop_t *lp);
static void estLpMissPS(loop_t *lp);
static void estNodeAllMiss(tcfg_node_t* bbi);
static void init_mem(void);
static void free_mem(void);

/****** CACHE ANALYSIS *******/
static void printCacheSet(FILE*fp, worklist_p set) {
    worklist_p blkNode;
    sblk_p  blk;
    for (blkNode = set; blkNode; blkNode= blkNode->next) {
        blk = (sblk_p)(blkNode->data); 
        fprintf(fp," %x:%d",blk->m->blkAddr,blk->age);
        printTSset(fp,blk->m->tsList);
    }
    fflush(fp);
}
#endif

#if 0
static loop_t* bbi_lp(tcfg_node_t *bbi) {
    int dbg = 0;
    loop_t *lp;
    if (dbg) fprintf(dbgMpa,"\nBB %d inf_lp->id %d ",bbi->bb->id, bbi->loop_id);
    if (bbi->loop_id==-1) return loops[0]; //not in loop
    lp = loops[inf_loops[bbi->loop_id].loop_id]; 
    if (dbg) {fprintf(dbgMpa," -> lp->id %d", lp->id);fflush(dbgMpa);}
    return lp;
}

static int bbi_lpId(tcfg_node_t *bbi) {
    int lpId = bbi_lp(bbi)->id;
    return lpId;
}

/*add saddr m to set strNode after prvNode, keep strNode an increasing set*/
static void addToIncSet(saddr_p m,worklist_p *prvNode,
                worklist_p *strNode, loop_t *lp) {
    worklist_p  curNode;
    saddr_p    curBlk;

    if ( (*prvNode)==NULL ) curNode = *strNode;
    else curNode = (*prvNode)->next;

    for ( ; curNode; curNode = curNode->next) {
        curBlk = (saddr_p)(curNode->data);
        if (curBlk->blkAddr < m->blkAddr) {
            *prvNode = curNode;
        }
        else if (curBlk->blkAddr == m->blkAddr) {
            if (cmpTSset(curBlk->tsList,m->tsList,lp->id)==0) {
                return;//already added
            }
            else {
                *prvNode = curNode;
            }
        }
        else {//prvBlk->blkAddr < m->blkAddr < curBlk->blkAddr
            addAfterNode(m,prvNode,strNode); 
            return;
        }
    }
    //prvBlk->blkAddr < m->blkAddr; curBlk = NULL
    addAfterNode(m,prvNode,strNode);
}

static void cpySBlk(sblk_p dst, sblk_p src) {
    int i;
    dst->age    = src->age;
    dst->m      = src->m;
    for (i=0; i<src->age-1; i++) {
        dst->ys[i]     = src->ys[i];
    }
    dst->flag   = src->flag;
}

static sblk_p createSBlk(saddr_p addrBlk) {
    sblk_p tmpBlk;
    tmpBlk          = malloc(sizeof(sblk_s));
    tmpBlk->m       = addrBlk;
    tmpBlk->age     = 1;
    tmpBlk->flag    = 0;
    return tmpBlk;
}

static int cmpSBlk(sblk_p sblk1, sblk_p sblk2) {
    if (sblk1->age != sblk2->age) return 1;
    if (sblk1->ys != sblk2->ys) return 1;
    return 0;
}

/*Make dst similar to src*/ 
static int cpyACS(scp_acs dst, scp_acs src) {
    int dbg = 0;
    int i;
    int change;
    worklist_p sNode, dNode, prvNode;
    sblk_p sBlk, dBlk, tmpBlk;
    if (dbg) {
        fprintf(dbgMpa,"\nAcs copy");
        for (i=0; i<MAX_CACHE_SET; i++) {
            fprintf(dbgMpa,"\nS[%d]: ",i);printCacheSet(dbgMpa,src[i]);
            fprintf(dbgMpa,"\nD[%d]: ",i);printCacheSet(dbgMpa,dst[i]);
        }
    }
    change = 0;//no change
    for (i=0; i<MAX_CACHE_SET; i++) {
        sNode = src[i];
        dNode = dst[i]; prvNode = NULL;
        while (sNode) {
            sBlk = (sblk_p)(sNode->data); 
            if (dNode==NULL) {//src still has, dst already short
                //fprintf(dbgMpa," f1");
                dBlk = malloc(sizeof(sblk_s));
                cpySBlk(dBlk,sBlk);
                addAfterNode(dBlk,&prvNode, &(dst[i]));
                sNode = sNode->next;
                continue;
            }
            //dNode != NULL
            dBlk = dNode->data;
            if (sBlk->m->blkAddr > dBlk->m->blkAddr) {
                //skip, cannot add sMem at this position
                prvNode = dNode;
                dNode = dNode->next;
            }
            if (sBlk->m->blkAddr==dBlk->m->blkAddr) {
                if (cmpSBlk(sBlk,dBlk)!=0) {
                    change = 1;
                    cpySBlk(dBlk, sBlk);
                }
                sNode = sNode->next;
                prvNode = dNode;
                dNode = dNode->next;
            }
            else {//prvBlk->m->addr < sBlk->m->blkAddr < dBlk->m->blkAddr
                change = 1;
                tmpBlk = malloc(sizeof(sblk_s)); 
                cpySBlk(tmpBlk, sBlk);
                addAfterNode(tmpBlk, &prvNode, &(dst[i]));
                sNode = sNode->next;
            }
        }
    }
    if (dbg) {
        for (i=0; i<MAX_CACHE_SET; i++) {
            fprintf(dbgMpa,"\n--> c:%d D[%d]: ",change,i);
            printCacheSet(dbgMpa,dst[i]);
        }
    }
    return change;
}

//add scoped address mAcc to younger set of scoped cache block acsBlk
static int addToYS(sblk_p acsBlk, saddr_p mAcc) {
    int i;
    int ysSize;
    if (acsBlk->age == EVICTED) return 0;
    ysSize = acsBlk->age - 1;
    for (i=0; i<ysSize; i++) {
        if (acsBlk->ys[i]->blkAddr==mAcc->blkAddr) return 0;
    }
    if (mAcc && mAcc != -1) {
        acsBlk->ys[ysSize] = mAcc;
        acsBlk->age++;
        return 1;
    }
    return 0;
}

static int clearYS(sblk_p acsBlk) {
    acsBlk->age = 1;
    return 1;
}

/* union younger set from src to dst */
static int unionYS(sblk_p dst, sblk_p src) {
    int     i;
    int     ysSizeSrc;
    int     changed;

    changed = 0;
    ysSizeSrc = src->age - 1;
    for (i=0; i<ysSizeSrc; i++) {
        if (dst->age == EVICTED) return changed;
        if (src->ys[i])
            changed |= addToYS(dst,src->ys[i]);
    }
    return changed;   
}

//flush all cache blks aged by unpredictable access
static void flushCache(saddr_p mAcc, scp_acs acs_out) {
    int i;
    sblk_p      acsBlk;
    worklist_p  curNode;
    for (i=0; i<MAX_CACHE_SET; i++) {
        for(curNode = acs_out[i]; curNode; curNode = curNode->next) {
            acsBlk = (sblk_p)(curNode->data); 
            acsBlk->age = EVICTED;
        }
    }
}

/* quick way to check if data ref. D accesses a single memory block only
 * We could determine if D renews m in loop L by checking access pattern of D if
 * (i)  D is loop-affine access 
 * (ii) addr stride of D in each iteration of L is less than block size 
 */
static int singletonAccQuick(dat_inst_t*  d_inst, int lpId) {//quick check, not formally proven, same result
    int     i;
    expr_p  exp;

    exp = (expr_p)(&(d_inst->addrExpr));
    
    if (exp->varNum==0) return 1;   //D is scalar access
    if (lpId==0) return 0;          //L_id is the outermost loop
    for (i=0; i<exp->varNum-1; i++) {
        if (exp->value[i].t!=VALUE_CONST) return 0; //D is not loop-affine access
    }

    i = exp->varNum-1; //induction variable of the inner most loop
    if (exp->value[i].t == VALUE_CONST && exp->value[i].val>=lpId) {
        if (exp->coef[i] < SIZE_OF_BLOCK) return 1;
    }
    return 0;
}

/* check if the access in temporal scope m is singleton (one single memory block only, no overlap)*/
static int singletonAcc(worklist_p *addrList, saddr_p tsM, dat_inst_t* d_inst, int lpId) {
    worklist_p  addrNode;
    saddr_p     mAcc;
    int         cmp;

    freeList(addrList);  
    for (addrNode = (d_inst->addr_set); addrNode; addrNode = addrNode->next) {
        mAcc = (saddr_p)(addrNode->data);
        cmp = cmpSAddr(tsM, mAcc, lpId); 
        switch (cmp) {
            case EQUAL_TS:
            case SEP_TS:
                break;
            default: //OLAP_TS
                return 0;//not singleton access
                //addToWorkList(addrList, mAcc);
        }
    }
    return 1;//is singleton access
}

/* scope-aware update PS, update acs after accessing d_inst in loop lp*/
static void PS_data_update(scp_acs acs_out, dat_inst_t *d_inst, loop_t *lp) {
    int         dbg = 0;
    int         i, s;
    int         cmp, found;
    int         singleton;
    worklist_p  sblkNode,addrNode,prvNode,agedNode,addr_set,addrList;
    saddr_p     mAcc;
    sblk_p      acsBlk, tmpBlk;
    worklist_p  Xf[MAX_CACHE_SET];          
    worklist_p  newBlk[MAX_CACHE_SET];
    worklist_p  addPos[MAX_CACHE_SET];

    agedNode = NULL; addrList = NULL;
    for (i=0; i<MAX_CACHE_SET; i++) {
        newBlk[i] = NULL; addPos[i] = NULL; Xf[i] = NULL;
    }

    /*divide addr_set into different cache set (X_{f_i})*/
    addr_set = d_inst->addr_set;
    singleton = singletonAccQuick(d_inst, lp->id);
    for (addrNode = addr_set; addrNode; addrNode = addrNode->next) {
        mAcc = (saddr_p)(addrNode->data);
        if (mAcc->blkAddr == UNKNOWN_ADDR) {
            flushCache(mAcc,acs_out);
            continue;
        }
        s = GET_SET(mAcc->blkAddr);
        addAfterNode(mAcc, &(addPos[s]), &(Xf[s]));
    }
    for (i=0; i<MAX_CACHE_SET; i++) addPos[i]=NULL;

    if (dbg) {fprintf(dbgMpa," canRenew: %d", singleton);}
    if (dbg) {
        #if 0
        fprintf(dbgMpa,"\n\nAddrSet: ");printSAddrSet(dbgMpa,addr_set,0);
        for (i=0; i<MAX_CACHE_SET; i++) {
            fprintf(dbgMpa,"\nXf[%d] ",i);printSAddrSet(dbgMpa,Xf[i],0);
        }
        #endif
    }

    /*add newly accessed scoped blks to younger set if overlap*/
    for (i=0; i<MAX_CACHE_SET; i++) {
        for (addrNode = Xf[i]; addrNode; addrNode=addrNode->next) {
            mAcc = (saddr_p)(addrNode->data);
            found = 0;
            prvNode = NULL;
            for (sblkNode = acs_out[i]; sblkNode; sblkNode=sblkNode->next) {
                acsBlk = (sblk_p)(sblkNode->data); 
                if (acsBlk->m->blkAddr <= mAcc->blkAddr) prvNode = sblkNode;
                if (acsBlk->age==EVICTED && acsBlk->m->blkAddr!=mAcc->blkAddr){
                    //acsBlk is evicted -> no need to age it further
                    continue;
                }
                cmp = cmpSAddr(acsBlk->m,mAcc,lp->id);
                switch (cmp) {
                    case EQUAL_TS:          //acsBlk is identical with mAcc
                        found = 1;
                        //remember the position of accessed addr in the cache
                        addToWorkList(&(newBlk[i]),mAcc);
                        addToWorkList(&(addPos[i]),sblkNode);
                        break;

                    case OLAP_TS:           //acsBlk is overlap with mAcc
                        if (0) {
                            fprintf(dbgMpa,"\nOverlap: ");
                            printSAddr(dbgMpa,acsBlk->m,1);
                            fprintf(dbgMpa," - ");
                            printSAddr(dbgMpa,mAcc,1);
                        }
#if AVOID_ONE_ACCESS_MULTIPLE_AGING 
                        if ( acsBlk->flag == AGED) break;//already aged
#endif
                        addToYS(acsBlk,mAcc);
                        acsBlk->flag = AGED;
                        addToWorkList(&agedNode,acsBlk);
                        break;
                    case SEP_TS:            //separated TS -> no interaction
                        //do nothing
                        break;
                    default:
                        printf("\n Panic, unknown cmp %d",cmp); exit(1);
                }
            }//finish for acs_out[i]
            if (!found) {                   //mAcc is a new scoped block
                addToWorkList(&(newBlk[i]),mAcc);
                addToWorkList(&(addPos[i]),prvNode);
            }
        }//finish X_f_i
        while (!isEmpty(newBlk[i])) {
            mAcc    = removeOneFromWorkList(&(newBlk[i]));
            prvNode = removeOneFromWorkList(&(addPos[i]));
            if (prvNode == NULL) goto ADD_NEW_BLK;
            acsBlk  = prvNode->data;
            if (acsBlk->m->blkAddr==mAcc->blkAddr) {
                cmp = cmpSAddr(acsBlk->m,mAcc,lp->id);
                if (cmp == EQUAL_TS) {
                    if (singletonAcc(&addrList,acsBlk->m,d_inst,lp->id)==1) {//formally proven approach
                        clearYS(acsBlk);
                    }
                    #if 0  
                    if (singleton==1) { //quicker way, not formally proven, same result
                        clearYS(acsBlk);
                    }
                    #endif
                }
                else if (cmp!=EQUAL_TS) {
                    goto ADD_NEW_BLK;
                }
            }
            else {//mAcc is a new scoped block in this acs
                if (acsBlk->m->blkAddr<mAcc->blkAddr) {
                ADD_NEW_BLK:
                    tmpBlk  = createSBlk(mAcc); 
                    addAfterNode(tmpBlk,&prvNode, &(acs_out[i]));
                }
                //else not new scp_blk -> do nothing
            }
        }

    }//finish MAX_CACHE_SET
    
    /*reset aged mark*/
    while (!isEmpty(agedNode)) {
        tmpBlk = removeOneFromWorkList(&agedNode);
        tmpBlk->flag = 0;
    }
    if (dbg) {
        for (i=0; i<1; i++) {
            fprintf(dbgMpa,"\nD[%d] ",i);printCacheSet(dbgMpa,acs_out[i]);
        }
    }
}

/* scope-aware join PS, join src to dst */
static int PS_join (scp_acs dst, scp_acs src, loop_t* lp) {
    int         dbg = 0;
    int         i;
    int         changed;
    worklist_p  sNode, dNode, prvNode;
    sblk_p      sBlk, dBlk, tmpBlk;

    if (dbg) {
        //fprintf(dbgMpa,"\nJoin 2 ACS");
        for (i=0; i<1; i++) {
            fprintf(dbgMpa,"\nS[%d] ",i);printCacheSet(dbgMpa,src[i]);
            fprintf(dbgMpa,"\nD[%d] ",i);printCacheSet(dbgMpa,dst[i]);
        }
    }

    changed = 0;
    for (i=0; i<MAX_CACHE_SET; i++) {
        sNode   = src[i];
        dNode   = dst[i];
        prvNode = NULL;
        while (sNode) {
            sBlk = (sblk_p)(sNode->data);
            if (dNode) {
                dBlk = (sblk_p)(dNode->data);
                if (sBlk->m->blkAddr == dBlk->m->blkAddr) {
                    if (eqTSset(sBlk->m->tsList, dBlk->m->tsList, lp->id)) {
                        changed |= unionYS(dBlk,sBlk);
                        prvNode = dNode;
                        sNode   = sNode->next;
                        dNode   = dNode->next;
                    }
                    else goto NEXT_SRC_NODE;        //same addr, diff TS
                }
                else if (dBlk->m->blkAddr < sBlk->m->blkAddr) {
NEXT_SRC_NODE:
                    prvNode = dNode;
                    dNode   = dNode->next;
                }
                else {//prvBlk->blkAddr < sBlk->blkAddr < dBlk->blkAddr
                    goto ADD_NEW_BLK;
                }
            }
            else {//dNode==NULL                     //add new dNode for sNode
ADD_NEW_BLK:
                if (0) {
                    fprintf(dbgMpa,"\nAdd ");
                    printSAddr(dbgMpa,sBlk->m,1);
                    fprintf(dbgMpa," after ");
                    if (prvNode) {
                        tmpBlk = prvNode->data;
                        printSAddr(dbgMpa,tmpBlk->m,1);
                    }
                    else {
                        fprintf(dbgMpa," D[%d] head",i);
                    }
                }
                tmpBlk  = malloc(sizeof(sblk_s));
                cpySBlk(tmpBlk, sBlk);
                addAfterNode(tmpBlk, &prvNode, &(dst[i]));
                sNode   = sNode->next;
                changed = 1;
            }
        }//end while sNode
    }//end for cache_set

    if (dbg && changed) {
        for (i=0; i<MAX_CACHE_SET; i++) {
            fprintf(dbgMpa,"\nS[%d] ",i);printCacheSet(dbgMpa,src[i]);
            fprintf(dbgMpa,"\n-->D[%d] ",i);printCacheSet(dbgMpa,dst[i]);
        }
    }
    return changed;
}

/*** Pers. analysis within a basic block ***/
static void transform_bbi_dcache(tcfg_node_t *bbi, loop_t* lp,int type) {
    int dbg = 0;
    dat_inst_t*     d_inst;
    de_inst_t*      insn;
    int             n_inst;
    
    cpyACS(bbi->acs_out, bbi->acs_in); 
    for (n_inst = 0; n_inst < bbi->bb->num_d_inst; n_inst++) {
        d_inst  = (dat_inst_t*)(bbi->bb->d_instlist);
        d_inst  = d_inst + n_inst;
        insn    = d_inst->insn;

        if (!isMemAccess(insn->op_enum)) {
            printf("\nErr: not ld/st inst: ");
            printInstr(insn);
            continue;
        }
        if (type != PERSISTENCE) {
            printf("\nErr: not implemented");fflush(stdout);
            exit(1);
        }
        if (dbg) {
            fprintf(dbgMpa,"\n\nDataRef ");fprintInstr(dbgMpa,insn);
        }

#if WRITE_THRU 
        if (isLoadInst(insn->op_enum)) {
            PS_data_update(bbi->acs_out,d_inst, lp); 
        }
        else {//write-through no allocate policy
            if (dbg) {
                fprintf(dbgMpa,"write inst, do nothing");
            }
            //write inst -> do nothing
            continue;
        }
#else
        PS_update(bbi->acs_out,d_inst, renewFlag, lp); 
#endif
    }
}

/*** Analyze ps within a loop, according to mpa algorithm ***/
static void analyze_loop_ps(loop_t *lp) {
    int         dbg = 0;
    int         i,j;
    int         hdLpId, blkLpId;
    tcfg_node_t *lpHead, *lpTail, *curNode; 
    tcfg_edge_t *in_edge, *out_edge;
    int         changed,flag;
    int         iterCount;

    P_Queue *pQueue;    //priority queue of node to process


    if (dbg){fprintf(dbgMpa,"\n\n=== Analyze L%d ",lp->id);fflush(dbgMpa);}

    /*check if this lp has been analyzed*/
    if (lp->flags == LOOP_ANALYZED){fprintf(dbgMpa," : lp analyzed");return;}
    else lp->flags = LOOP_ANALYZED; //mark analyzed

    hdLpId = lp->id;

    pQueue = NULL;
    lpHead = lp->head;
    lpTail = lp->tail;  /*NOTE: Vivy assume lp has 1 lpTail -> true?*/
    if (lpTail==NULL) lpTail = tcfg[num_tcfg_nodes-1];
    if (dbg) {fprintf(dbgMpa," [%d,%d]",lpHead->id, lpTail->id);fflush(dbgMpa);}

    /*Reinitialize ACS before analyzing this loop*/
    for (i=lpHead->id; i<=lpTail->id; i++) {
        curNode = tcfg[i];
        visited[i] = 0;
        for (j=0; j<MAX_CACHE_SET; j++) {
            curNode->acs_in[j] = NULL;
            curNode->acs_out[j] = NULL;
        }
    }
    
    iterCount = 0;
    p_enqueue(&pQueue,lpHead,lpHead->id);
    while (!p_queue_empty(&pQueue)) {
        curNode = (tcfg_node_t*) p_dequeue(&pQueue);
        if (curNode==lpHead) iterCount++;
        blkLpId = bbi_lpId(curNode);

        /*ignore blks belong to outer lp*/
        if (cmpLpOrder(hdLpId,blkLpId)==-1) continue;

        if (dbg) {
            fprintf(dbgMpa,"\n\nAnalyze bbi (%d,%d), L%d",
                    bbi_pid(curNode),bbi_bid(curNode),blkLpId);fflush(dbgMpa);
        }
        // merge ACS of incoming edges
        changed = 0;
        for (in_edge=curNode->in; in_edge!=NULL; in_edge=in_edge->next_in) {
            if (cmpLpOrder(hdLpId,bbi_lpId(in_edge->src))>=0) {
                flag = PS_join(curNode->acs_in, in_edge->src->acs_out, lp);
                if (dbg) {
                    fprintf(dbgMpa,"\nJoin (%d->%d) : changed %d",
                            in_edge->src->id,curNode->id, flag); 
                }
                if (flag==1) changed=1;
            }
        }
        if (visited[curNode->id]==0) {changed=1; visited[curNode->id]=1;}

        if (changed) {
            // perform abs.int within the block
            transform_bbi_dcache(curNode,lp,PERSISTENCE);
            //enqueue outgoing bbi
            for (out_edge=curNode->out; out_edge; out_edge=out_edge->next_out){
                p_enqueue(&pQueue,out_edge->dst, out_edge->dst->id); 
            }
        }
    }//finish analyze this lp
    if (1) {printf("\nFinish analysis L%d in %d rounds",lp->id,iterCount);}
}

/****** COMPUTE CACHE MISSES FROM ANALYSIS RESULT ******/

/* collect scoped blks persistence entering lp */
static void getOuterPS(loop_t *lp) {
    /* For each loop, collect PS.blk when entering the loop -> lpPersIn
    * Collect PS.blk needed inside the loop -> lpReqPS
    * if m in lpReqPS & m notin lpPersIn -> m need 1 cold miss each entering lp*/
    int dbg = 0;
    int i;
    tcfg_node_t     *head, *src;
    tcfg_edge_t     *in_e;
    worklist_p      setNode,prvNode;
    sblk_p          setBlk;
    scp_acs         lpIn;
    
    head = lp->head;                        //structured loop -> 1 lp head
    lpIn = lpPersIn[lp->id];                //persistence blks entering loop lp
    if (dbg) fprintf(dbgMpa,"\nPers.blk when entering L%d",lp->id);

    for (in_e = head->in; in_e; in_e = in_e->next_in) {
       src = in_e->src; 
       if (bbi_lp(src)->id==lp->id) continue;
       for (i=0; i<MAX_CACHE_SET; i++) {
            prvNode = NULL;
            for (setNode = src->acs_out[i]; setNode; setNode = setNode->next) {
                setBlk = (sblk_p)(setNode->data);
                if (setBlk->age < PSEUDO) {//PS
                    addAfterNode(setBlk,&prvNode,&(lpIn[i])); 
                }
            }
       }
       if (dbg) {
            fprintf(dbgMpa,"\nEnter L%d from (%d,%d)",
                lp->id,bbi_pid(src),bbi_bid(src));
            for (i=0; i<MAX_CACHE_SET; i++) {
                fprintf(dbgMpa,"\nS[%d] ",i);
                printCacheSet(dbgMpa,src->acs_out[i]);
                fprintf(dbgMpa,"\nList of PS blks ");
                fprintf(dbgMpa,"\n->S[%d] ",i);printCacheSet(dbgMpa,lpIn[i]);
            }
       }
    }
}

/* estimate cold miss of persistent blks each time entering lp*/
static void estLpMissPS(loop_t *lp) {
    int         dbg = 0;
    int         i, s;
    worklist_p  inNode, reqNode, prvNode;
    saddr_p     reqBlk;
    sblk_p      inBlk;
    worklist_p  *prvInNode;
    worklist_p  prvReqNode;
    int         found, lpMiss;
    int         lpEntry;

    if (dbg) {
        fprintf(dbgMpa,"\n\nEst cold miss in L%d",lp->id);
        fprintf(dbgMpa,"\n LPS set:");
        printSAddrSet(dbgMpa,lpReqPS[lp->id],0);
        fprintf(dbgMpa,"\n lpPS_in set");
        for (i=0; i<MAX_CACHE_SET; i++) {
            fprintf(dbgMpa,"\n S[%d]: ",i);
            printCacheSet(dbgMpa,lpPersIn[lp->id][i]);
        }
        fprintf(dbgMpa,"\n Miss est: ");
    }
    prvReqNode = NULL;
    prvInNode = calloc(MAX_CACHE_SET,sizeof(worklist_p));

    lp_coldms[lp->id] = 0; 
    for (reqNode = lpReqPS[lp->id]; reqNode; reqNode = reqNode->next) {
        reqBlk = (saddr_p)(reqNode->data);     
        //fprintf(dbgMpa," R:%x ",reqBlk->blkAddr);
        found = 0;

        s = GET_SET(reqBlk->blkAddr);
        prvNode = prvInNode[s];
        if (prvNode) inNode = prvNode->next;
        else inNode = lpPersIn[lp->id][s];

        for (  ; inNode; inNode = inNode->next ) {
            inBlk = (sblk_p)(inNode->data);
            if (inBlk->m->blkAddr < reqBlk->blkAddr) {
                prvNode = inNode; 
            }
            else if (inBlk->m->blkAddr == reqBlk->blkAddr && lp->parent) {
                if (cmpSAddr(inBlk->m, reqBlk,lp->id)==0) {
                    //regBlk PS in lp InACS -> no cold miss needed
                    found = 1;
                addToIncSet(reqBlk,&prvReqNode,&(lpReqPS[lp->parent->id]),lp);
                    if (dbg) {fprintf(dbgMpa," U:%x ",reqBlk->blkAddr);}
                    break; 
                }
                else {
                    prvNode = inNode;
                }
            }
            else {//prvBlk->blkAddr < reqBlk->blkAddr < inBlk->blkAddr
                //regBlk not PS in lp InACS -> need 1 cold ms each enter
                found = 1;
                if (lp->parent) 
                    lpMiss=estScopeSize(reqBlk->tsList,lp->parent->id); 
                else lpMiss = 1;
                lp_coldms[lp->id]+=lpMiss;
                if (dbg) {fprintf(dbgMpa," C:%x:%d ",reqBlk->blkAddr, lpMiss);}
                break;
            }
        }
        if (!found) {
            if (lp->parent) lpMiss=estScopeSize(reqBlk->tsList,lp->parent->id); 
            else lpMiss = 1;
            lp_coldms[lp->id]+=lpMiss;
            if (dbg) {fprintf(dbgMpa," C:%x:%d ",reqBlk->blkAddr,lpMiss);}
        }
        prvInNode[s] = prvNode;
    }
    free(prvInNode);

    if (lp->parent) lpEntry = lp->parent->exec;
    else lpEntry = 1;

    totalPersMiss += lp_coldms[lp->id];

    if (dbg) {
        fprintf(dbgMpa,"\nCold miss in L%d: %d",lp->id, lp_coldms[lp->id]);}
    if (1) {
        printf("\nIn L%d, Cold miss %d, Entry %d, Exec %d",
                lp->id,lp_coldms[lp->id],lpEntry, lp->exec);
        fflush(stdout);
    }
}

static void estNodeAllMiss(tcfg_node_t* bbi) {
    int dbg = 0;
    dat_inst_t*     d_inst;
    de_inst_t*      insn;
    int             n_inst,cs;
    int             num_PS, max_miss, max_exec; 
    
    worklist_p      PS_set, miss_set, LPS_req;
    worklist_p      addrNode, setNode, prvReqNode, prvNode;
    saddr_p         addrBlk;
    sblk_p          setBlk;

    loop_t          *lp;

    bbi->max_miss = 0;
    bbi->dcache_delay = 0;
    lp = bbi_lp(bbi);
    max_exec = lp->exec;
    cpyACS(bbi->acs_out, bbi->acs_in); 
    if (dbg) {
        fprintf(dbgMpa,"\n\nEst non-PS miss in bbi (%d,%d), L%d, ME: %d",
                bbi_pid(bbi),bbi_bid(bbi),bbi_lp(bbi)->id, max_exec);
    }
    for (n_inst = 0; n_inst < bbi->bb->num_d_inst; n_inst++) {
        d_inst = (dat_inst_t*)(bbi->bb->d_instlist);
        d_inst = d_inst + n_inst;
        insn = d_inst->insn;
        max_miss = 0; num_PS = 0; 
        prvNode = NULL; LPS_req = NULL;
        if (dbg){miss_set = NULL; PS_set = NULL;}
        d_inst->max_exec = max_exec;
        totalDataExec +=max_exec;
        #if WRITE_THRU
        if (isStoreInst(insn->op_enum)) {
            d_inst->max_miss = max_exec; 
            totalNPersMiss += d_inst->max_miss;
            if (1) {
                printf("\n\nDataRef: ");printInstr(d_inst->insn);
                printf("maxPS: %d, maxMs: %d, maxExec: %d",
                        num_PS, d_inst->max_miss, max_exec);
                fflush(stdout);
            }
            continue;
        }
        #endif 

        for (addrNode = d_inst->addr_set; addrNode; addrNode = addrNode->next) {
            addrBlk = (saddr_p)(addrNode->data);
            if (addrBlk->blkAddr==UNKNOWN_ADDR) goto ALL_MISS;
            cs = GET_SET(addrBlk->blkAddr);
            if (cs<0 || cs >= MAX_CACHE_SET) {
                printf("\nPanic: unknown cache set %d",cs);
                exit(1);
            }
            for (setNode=bbi->acs_out[cs]; setNode; setNode = setNode->next) {
                setBlk = (sblk_p)(setNode->data);
                if (addrBlk->blkAddr > setBlk->m->blkAddr) continue;
                if (addrBlk->blkAddr == setBlk->m->blkAddr) {
                    if (cmpSAddr(addrBlk,setBlk->m,lp->id)==0) {
                        if (setBlk->age==EVICTED) {//non-PS
                            //max_miss+=estConfScope(setBlk->m,bbi->acs_out[cs],lp);
                            max_miss+=estScopeSize(setBlk->m->tsList,lp->id);
                            if (dbg) addToWorkList(&miss_set, addrBlk);
                        }
                        else {//PS
                            addAfterNode(addrBlk,&prvNode,&LPS_req);
                            num_PS++; 
                        }
                        break;
                    }
                    else continue;
                }
                else {//prvBlk->blkAddr < addrBlk->blkAddr < setBlk->blkAddr
                    //not yet loaded to acs -> PS
                    addAfterNode(addrBlk,&prvNode, &LPS_req);
                    num_PS++; 
                    break;
                }
            }
        }

        if (max_miss  < max_exec) {
            d_inst->max_miss = max_miss;
            prvReqNode = NULL;
            for (setNode = LPS_req; setNode; setNode=setNode->next) {
                addrBlk = (saddr_p)(setNode->data); 
                addToIncSet(addrBlk,&prvReqNode,&(lpReqPS[lp->id]),lp);
                if (dbg) addToWorkList(&PS_set, addrBlk);
            }
            while(!isEmpty(LPS_req)) removeOneFromWorkList(&LPS_req);
        }
        else {//just all miss 
            ALL_MISS:
            max_miss = max_exec;
            d_inst->max_miss = max_miss;
        }

        bbi->max_miss += d_inst->max_miss;
        totalNPersMiss += d_inst->max_miss;

        if (dbg) {
            fprintf(dbgMpa,"\n\nDataRef: ");
            fprintInstr(dbgMpa,d_inst->insn);
            fprintf(dbgMpa,"\n#PS: %d, max_miss: %d, max_exec: %d",
                        num_PS, d_inst->max_miss, max_exec);
            fprintf(dbgMpa,"\nList of miss.blk :");
            printSAddrSet(dbgMpa,miss_set,0);
            #if 0
            fprintf(dbgMpa,"\nList of PS.req :");
            printSAddrSet(dbgMpa,PS_set,0);
            #endif
            while(!isEmpty(PS_set)) removeOneFromWorkList(&PS_set);
            while(!isEmpty(miss_set)) removeOneFromWorkList(&miss_set);
        }

        
        if (1) {
            printf("\n\nDataRef: ");printInstr(d_inst->insn);
            printf("\nmaxPS: %d, maxMs: %d, maxExec: %d",
                        num_PS, d_inst->max_miss, max_exec);
            fflush(stdout);
        }
        PS_data_update(bbi->acs_out,d_inst, lp); 
    }
}

/****** OTHER ROUTINES *******/

static void init_mem(void) {
    int i,j;
    dbgMpa = fopen("dbg_mpa.dbg","w");
    visited = calloc(num_tcfg_nodes,sizeof(int));
    for (i=0; i<num_tcfg_nodes; i++) {
        tcfg[i]->acs_in = calloc(MAX_CACHE_SET,sizeof(worklist_p));
        tcfg[i]->acs_out = calloc(MAX_CACHE_SET,sizeof(worklist_p));
        for (j=0; j<MAX_CACHE_SET; j++) {
            tcfg[i]->acs_in[j] = NULL;
            tcfg[i]->acs_out[j] = NULL;
        }
    }
    lpOut_acs = calloc(num_tcfg_loops,sizeof(worklist_p*));
    lpPersIn = calloc(num_tcfg_loops,sizeof(worklist_p*));
    lpReqPS = calloc(num_tcfg_loops,sizeof(worklist_p));
    lp_coldms = calloc(num_tcfg_loops, sizeof(int));
    for (i=0; i<num_tcfg_loops; i++) {
        lpReqPS[i] = NULL;
        lpOut_acs[i] = calloc(MAX_CACHE_SET,sizeof(worklist_p));
        lpPersIn[i] = calloc(MAX_CACHE_SET,sizeof(worklist_p));
    }
    prvAcsNode = calloc(MAX_CACHE_SET,sizeof(worklist_p));
}

static void free_mem(void) {
    int i;
    for (i=0; i<num_tcfg_nodes; i++) {
        free(tcfg[i]->acs_in);
        free(tcfg[i]->acs_out);
    }
    for (i=0; i<num_tcfg_loops; i++) {
        free(lpOut_acs[i]);
        free(lpPersIn[i]);
    }
    free(prvAcsNode);
    free(lpOut_acs);
    free(lpPersIn);
    free(lpReqPS);
    free(visited);
    fclose(dbgMpa);
}

/***  Multi-level PSistence analysis of data cache, general handle ***/
void mpa_datacache() {
    int i;
    inf_node_t *ib;
    tcfg_node_t *bbi;

    init_mem();
    for (i=0; i<num_tcfg_nodes; i++) {
        bbi = tcfg[i];
        ib = &(inf_procs[bbi_pid(bbi)].inf_cfg[bbi_bid(bbi)]);
        bbi->loop_id = ib->loop_id;
    }

    /*PS analysis from outer-most loop to inner loop*/
    analyze_loop_ps(loops[0]);    
    for (i=num_tcfg_loops-1; i>0; i--) analyze_loop_ps(loops[i]);

    #if 1
    /*collect PS blk of incoming edge of each lp*/
    for (i=0; i<num_tcfg_loops; i++) getOuterPS(loops[i]);      
    
    /*deriving cache miss for each data reference*/
    totalDataExec = 0;
    totalPersMiss = 0;
    totalNPersMiss = 0;
    for (i=0; i<num_tcfg_nodes; i++) estNodeAllMiss(tcfg[i]);
    /*eliminate duplicated cold miss of identical memScp*/
    for (i=1; i<num_tcfg_loops; i++) estLpMissPS(loops[i]);      
    estLpMissPS(loops[0]);      

    if (1) {
        printf("\nTotal data ref %d",totalDataExec);
        printf("\nTotal PS. miss %d",totalPersMiss);
        printf("\nTotal non-PS. miss %d",totalNPersMiss);
    }
    #endif
    
    free_mem();
}
#endif

/***************************************************************************/
worklist_p*** scp_addrset_l1;
worklist_p*** scp_addrset_l2;
void scp_pre_address_analysis(char* fName, worklist_p**** input_addrset) {
        worklist_p*** scp_addrset = calloc(prog.num_procs, sizeof(worklist_p**));
        int proc_id;
        for (proc_id = 0; proc_id < prog.num_procs; proc_id++) {
                proc_t* proc = &(prog.procs[proc_id]);
                scp_addrset[proc_id] = calloc(proc->num_bb, sizeof(worklist_p*));
                int bb_id;
                for (bb_id = 0; bb_id < proc->num_bb; bb_id++) {
                        cfg_node_t* bb = &(proc->cfg[bb_id]);
                        scp_addrset[proc_id][bb_id] = calloc(bb->num_d_inst,
                                        sizeof(worklist_p));
                }
        }
        /*****************************************************/
        classified_address_analysis(fName);
        for (proc_id = 0; proc_id < prog.num_procs; proc_id++) {
                proc_t* proc = &(prog.procs[proc_id]);
                int bb_id;
                for (bb_id = 0; bb_id < proc->num_bb; bb_id++) {
                        cfg_node_t* bb = &(proc->cfg[bb_id]);
                        int i;
                        for (i = 0; i < bb->num_d_inst; i++) {
                                dat_inst_t* dat = bb->d_instlist;
                                dat = dat + i;
                                scp_addrset[proc_id][bb_id][i] = dat->addr_set;
                        }
                }
        }
        /*****************************************************/
        *input_addrset = scp_addrset;
        /*****************************************************/
        return;
        for (proc_id = 0; proc_id < prog.num_procs; proc_id++) {
                proc_t* proc = &(prog.procs[proc_id]);
                int bb_id;
                for (bb_id = 0; bb_id < proc->num_bb; bb_id++) {
                        cfg_node_t* bb = &(proc->cfg[bb_id]);
                        if (bb->num_d_inst == 0)
                                continue;
                        printf("\n********************************************\nbb:%d\n",
                                        bb->id);
                        int i;
                        for (i = 0; i < bb->num_d_inst; i++) {
                                dat_inst_t* dat = bb->d_instlist;
                                dat = dat + i;
                                de_inst_t* insn = dat->insn;
                                printDataRef(stdout, dat);
                                printf("\t");
                                if (isStoreInst(insn->op_enum))
                                        printf("[STORE] ");
                                else
                                        printf("[LOAD] ");
                                printf("\n");
                                worklist_p addrset = dat->addr_set;
                                for (; addrset != NULL; addrset = addrset->next) {
                                        saddr_p saddr = addrset->data;
                                        printf("0x%x ", saddr->blkAddr);
                                }
                                printf("\n");
                        }
                }
        }
}
void scp_store_address_set() {
//      extern int enable_scp_dcache;
//      extern int enable_scp_dl2cache;
//      extern int enable_ul2cache;
        if (enable_scp_dcache == 1) {
                int i;
                for (i = 0; i < num_tcfg_nodes; i++) {
                        tcfg_node_t* bbi = tcfg[i];
                        if (bbi->bb->num_d_inst == 0)
                                continue;
                        cfg_node_t* bb = bbi->bb;
                        bbi->addrset_l1 = calloc(bbi->bb->num_d_inst, sizeof(worklist_p));
                        if (enable_scp_dl2cache || enable_ul2cache) {
                                bbi->addrset_l2 = calloc(bbi->bb->num_d_inst,
                                                sizeof(worklist_p));
                        }
                        int j;
                        for (j = 0; j < bb->num_d_inst; j++) {
                                bbi->addrset_l1[j] = scp_addrset_l1[bb->proc->id][bb->id][j];
                                if (enable_scp_dl2cache || enable_ul2cache) {
                                        bbi->addrset_l2[j] =
                                                        scp_addrset_l2[bb->proc->id][bb->id][j];
                                }
                        }
                }
        }
}
void scp_add2List(worklist_p* head, worklist_p* tail, void* data) {
        worklist_p temp = (worklist_p) malloc(sizeof(worklist_s));
        temp->next = NULL;
        temp->data = data;
        if (*head == NULL) {
                *head = temp;
                *tail = temp;
        } else {
                (*tail)->next = temp;
                *tail = temp;
        }
}
worklist_p scp_unrolled_temporal_scope(worklist_p addrset, loop_t*innerLoop,
                int* unrolled_loop_map, int* old_loop_bound) {
        worklist_p ans = NULL, ansTail = NULL;
        worklist_p node = addrset;
        for (; node != NULL; node = node->next) {
                saddr_p saddr = node->data;
                //      printf("address:0x%x lp:%d\n", saddr->blkAddr, innerLoop->id);
                /*********************************************/
                worklist_p tsNode = saddr->tsList;
                worklist_p newTsList = NULL, newTsTail = NULL;
                int flag = 1;
                for (; tsNode != NULL; tsNode = tsNode->next) {
                        ts_p tS = tsNode->data;
                        loop_t*lp = innerLoop;
                        int lw = 0, up = 0;
                        while (lp != NULL) {
                                if (unrolled_loop_map[lp->id] == tS->loop_id) {
                                        up = old_loop_bound[tS->loop_id] - 1;
                                        lw = (up >= 1 ? 1 : up);
                                        break;
                                }
                                lp = lp->parent;
                        }
#if 0
                        if (lp == NULL) {
                                scp_print_ts(saddr->tsList);
                                printf("\n");
                                printf("current ts:%d",tS->loop_id);
                                printf("\n");
                                int k;
                                for (k = 0; k < num_tcfg_loops; k++) {
                                        printf("new loop id %d: %d", loops[k]->id,
                                                        unrolled_loop_map[loops[k]->id]);
                                        if (loops[k]->parent!=NULL) {
                                                printf(" parent:%d",loops[k]->parent->id);
                                        }
                                        printf("\n");
                                }
                                printf("UNROLLED BUG\n");
                                exit(1);
                        }
#endif
                        if (!(tS->up < lw || tS->lw > up)) {
                                if (lp != NULL) {
                                        ts_p newTs = malloc(sizeof(ts_s));
                                        newTs->loop_id = lp->id;
                                        newTs->lw = (tS->lw > lw ? tS->lw : lw);
                                        newTs->up = (tS->up < up ? tS->up : up);
                                        if (lp->id != 0) {
                                                newTs->lw--;
                                                newTs->up--;
                                        }
                                        scp_add2List(&newTsList, &newTsTail, newTs);
                                }
                        } else {
                                flag = 0;
                                break;
                        }
                }
                /*******************************************/
                if (flag == 1) {
                        saddr_p new_saddr = malloc(sizeof(saddr_s));
                        new_saddr->blkAddr = saddr->blkAddr;
                        new_saddr->instAddr = saddr->instAddr;
                        new_saddr->flag = saddr->flag;
                        new_saddr->psLoop = saddr->psLoop;
                        new_saddr->tsList = newTsList;
                        scp_add2List(&ans, &ansTail, new_saddr);
                }
        }
        return ans;
}
void scp_recalculate_temporal_scope(int* unrolled_loop_map, int* old_loop_bound) {
        int i;

        for (i = 0; i < num_tcfg_nodes; i++) {
                tcfg_node_t* bbi = tcfg[i];
                if (bbi->bb->num_d_inst == 0)
                        continue;
                cfg_node_t* bb = bbi->bb;
                bbi->addrset_l1 = calloc(bbi->bb->num_d_inst, sizeof(worklist_p));
                if (enable_scp_dl2cache || enable_ul2cache) {
                        bbi->addrset_l2 = calloc(bbi->bb->num_d_inst, sizeof(worklist_p));
                }
                int j;
                for (j = 0; j < bbi->bb->num_d_inst; j++) {
                        bbi->addrset_l1[j] = scp_unrolled_temporal_scope(
                                        scp_addrset_l1[bb->proc->id][bb->id][j], loop_map[bbi->id],
                                        unrolled_loop_map, old_loop_bound);
                        if (enable_scp_dl2cache || enable_ul2cache) {
                                bbi->addrset_l2[j] = scp_unrolled_temporal_scope(
                                                scp_addrset_l2[bb->proc->id][bb->id][j],
                                                loop_map[bbi->id], unrolled_loop_map, old_loop_bound);
                        }
                }
        }
}
loop_t* scp_mostOuterLoop(worklist_p lparr);
void scp_dump_address(void) {
        int i;
        printf("DUMP address\n");
        for (i = 0; i < num_tcfg_nodes; i++) {
                if (enable_scp_dcache == 0)
                        continue;
                tcfg_node_t* bbi = tcfg[i];
                if (bbi->bb->num_d_inst == 0)
                        continue;
                printf("Basic block %d\n", bbi->id);
                int j;
                for (j = 0; j < bbi->bb->num_d_inst; j++) {
                        dat_inst_t* dat = bbi->bb->d_instlist;
                        dat = dat + j;
                        de_inst_t* insn = dat->insn;
                        printf("\n\tinstr %x ", insn->addr);
                        if (isStoreInst(insn->op_enum))
                                printf("[STORE]");
                        else
                                printf("[LOAD]");
                        printf("\n");
                        worklist_p node;
                        for (node = bbi->addrset_l1[j]; node != NULL; node = node->next) {
                                saddr_p saddr = node->data;
                                int cacheset = GET_SET(saddr->blkAddr);
                                printf("\t\t0x%x (%d)", saddr->blkAddr, cacheset);
                                worklist_p tsnode = saddr->tsList;
                                while (tsnode != NULL) {
                                        ts_p tS = tsnode->data;
                                        printf(" l%d[%d,%d]", tS->loop_id, tS->lw, tS->up);
                                        tsnode = tsnode->next;
                                }
#if 1
                                printf(" \tPS in:");
                                worklist_p lpans = saddr->psLoop;
                                if (lpans != NULL) {
                                        worklist_p temp = lpans;
                                        while (temp != NULL) {
                                                loop_t* tlp = temp->data;
                                                printf(" l%d", tlp->id);
                                                temp = temp->next;
                                        }
                                        loop_t* tlp = scp_mostOuterLoop(lpans);
                                        printf(" outerLp:%d ", tlp->id);
                                }
#endif
                                printf("\n");
                        } //
                        if (enable_scp_dl2cache || enable_ul2cache) {
                                printf("\tL2 cache\n");
                                for (node = bbi->addrset_l2[j]; node != NULL;
                                                node = node->next) {
                                        saddr_p saddr = node->data;
                                        int cacheset = GET_SET(saddr->blkAddr);
                                        printf("\t\t0x%x (%d)", saddr->blkAddr, cacheset);
                                        worklist_p tsnode = saddr->tsList;
                                        while (tsnode != NULL) {
                                                ts_p tS = tsnode->data;
                                                printf(" l%d[%d,%d]", tS->loop_id, tS->lw, tS->up);
                                                tsnode = tsnode->next;
                                        }
#if 1
                                        printf(" \tPS in:");
                                        worklist_p lpans = saddr->psLoop;
                                        if (lpans != NULL) {
                                                worklist_p temp = lpans;
                                                while (temp != NULL) {
                                                        loop_t* tlp = temp->data;
                                                        printf(" l%d", tlp->id);
                                                        temp = temp->next;
                                                }
                                                loop_t* tlp = scp_mostOuterLoop(lpans);
                                                printf(" outerLp:%d ", tlp->id);
                                        }
#endif
                                        printf("\n");
                                }
                        }
                }
        }
}
void scp_dump_instruction(void) {
        int i;
        extern int enable_icache;
        if (enable_icache) {
                printf("DUMP instruction address\n");
                for (i = 0; i < num_tcfg_nodes; i++) {
                        tcfg_node_t* bbi = tcfg[i];
                        cfg_node_t* bb = bbi->bb;
                        int j;
                        printf("basic block %d\n", bbi->id);
                        for (j = 0; j < bb->num_inst; j++) {
                                de_inst_t* inst = &(bb->code[j]);
                                //unsigned first_word = GET_MEM(inst->addr);
                                //unsigned second_word = GET_MEM(inst->addr + SIZE_OF_WORD);
//                              printf("inst 0x%x: %x(%d) %x(%d)\n", inst->addr, first_word,
//                                              GET_SET(first_word), second_word, GET_SET(second_word));
                                printf("\tinst 0x%x:", inst->addr);
                                if (inst_chmc_l1[bbi->id][j] == ALL_HIT)
                                        printf("\tL1:ALL_HIT");
                                else if (inst_chmc_l1[bbi->id][j] == ALL_MISS)
                                        printf("\tL1:ALL_MISS");
                                else
                                        printf("\tL1:NOT_CLASSIFIED");
                                extern int enable_il2cache;
                                if (enable_il2cache) {
                                        if (inst_chmc_l2[bbi->id][j] == ALL_HIT)
                                                printf("\tL2:ALL_HIT");
                                        else if (inst_chmc_l2[bbi->id][j] == ALL_MISS)
                                                printf("\tL2:ALL_MISS");
                                        else if (inst_chmc_l2[bbi->id][j] == ALL_X) {
                                                printf("\tL2:ALL_X");
                                        } else {
                                                printf("\tL2:NOT_CLASSIFIED");
                                        }
                                }
                                extern int enable_ul2cache;
                                if (enable_ul2cache) {
                                        if (inst_psnc_ul2[bbi->id][j] == PS) {
                                                printf("\tL2:PS lp:%d",
                                                                inst_ps_loop_ul2[bbi->id][j]->id);
                                        } else if (inst_psnc_ul2[bbi->id][j] == NOT_CLASSIFIED)
                                                printf("\tL2:NOT_CLASSIFIED");
                                        else if (inst_psnc_ul2[bbi->id][j] == ALL_X)
                                                printf("\tL2:ALL_X");
                                        else
                                                printf("\tL2:");
                                }
                                printf("\n");
                        }
                }
        }
        if (enable_scp_dcache) {
                printf("Dump LOAD/STORE instruction\n");
                for (i = 0; i < num_tcfg_nodes; i++) {
                        tcfg_node_t* bbi = tcfg[i];
                        cfg_node_t* bb = bbi->bb;
                        printf("basic block %d\n", bbi->id);
                        int j;
                        for (j = 0; j < bb->num_d_inst; j++) {
                                dat_inst_t* dat = bb->d_instlist;
                                dat = dat + j;
                                de_inst_t* insn = dat->insn;
                                printf("\t0x%x ", insn->addr);
                                if (isStoreInst(insn->op_enum)) {
                                        printf("[STORE]");
                                } else {
                                        printf("[LOAD]");
                                        loop_t* ps_lp1 = scp_inner_ps_loop(bbi->addrset_l1[j]);
                                        printf("\tL1:");
                                        if (ps_lp1 == NULL) {
                                                printf("n");
                                        } else {
                                                printf("%d", ps_lp1->id);
                                        }
                                        if (enable_scp_dl2cache || enable_ul2cache) {
                                                loop_t* ps_lp2 = scp_inner_ps_loop(bbi->addrset_l2[j]);
                                                printf("\tL2:");
                                                if (ps_lp2 == NULL) {
                                                        printf("n");
                                                } else {
                                                        printf("%d", ps_lp2->id);
                                                }
                                        }
                                }
                                printf("\n");
                        }
                }
        }
}
//void scp_copy_address() {
//      int i;
//      for (i = 0; i < num_tcfg_nodes; i++) {
//              tcfg_node_t* bbi = tcfg[i];
//              if (bbi->bb->num_d_inst == 0)
//                      continue;
//              cfg_node_t* bb = bbi->bb;
//              if (current_analysis == L1_DCACHE_ANALYSIS) {
//                      bbi->addrset_l1 = calloc(bbi->bb->num_d_inst, sizeof(worklist_p));
//              } else if (current_analysis == L2_DCACHE_ANALYSIS) {
//                      bbi->addrset_l2 = calloc(bbi->bb->num_d_inst, sizeof(worklist_p));
//              }
//              int j;
//              for (j = 0; j < bbi->bb->num_d_inst; j++) {
//                      bbi->addrset_l1[j] = scp_addrset_l1[bb->proc->id][bb->id][j];
//              }
//      }
//}
void scp_enqueue(void* data, worklist_p* head, worklist_p* tail) {
        worklist_p node = malloc(sizeof(worklist_s));
        node->data = data;
        node->next = NULL;
        if (*head == NULL) {
                *head = node;
                *tail = *head;
        } else {
                worklist_p temp = *tail;
                temp->next = node;
                *tail = node;
        }
}

void* scp_dequeue(worklist_p* head, worklist_p* tail) {
        worklist_p node = *head;
        *head = node->next;
        if (*head == NULL
        )
                *tail = *head;
        void* ans = node->data;
        free(node);
        return ans;
}

int scp_empty_queue(worklist_p head, worklist_p tail) {
        if (head == NULL
        )
                return 1;
        else
                return 0;
}

scp_acs scp_createEmptyACS(void) {
        scp_acs acs = NULL;
        acs = calloc(MAX_CACHE_SET, sizeof(worklist_p));
        int i = 0;
        for (i = 0; i < MAX_CACHE_SET; i++) {
                acs[i] = NULL;
        }
        return acs;
}
ts_p scp_ts(worklist_p tslst, loop_t*lp) {
        for (; tslst != NULL; tslst = tslst->next) {
                ts_p ts = tslst->data;
                if (ts->loop_id == lp->id) {
                        return ts;
                }
        }
        return NULL;
}
int scp_overlap(saddr_p ma, saddr_p mb, loop_t*lp) {
        if (ma->blkAddr == mb->blkAddr)
                return 0;
        while (lp != NULL) {
                ts_p tsa = scp_ts(ma->tsList, lp);
                ts_p tsb = scp_ts(mb->tsList, lp);
                if (tsa != NULL && tsb != NULL) {
                        if (tsa->up < tsb->lw || tsa->lw > tsb->up) {
                                return 0;
                        }
                } else if (tsa == NULL && tsb == NULL) {
                        /*
                         * TODO: check the address analysis
                         */
#if 0
                        return 0;
#endif
                } else {
#if 0
                        return 0;
#endif
                }
                lp = lp->parent;
        }
        return 1;
}
/**
 * return a copy of blk
 */
sblk_p scp_cpySBlk(sblk_p blk) {
        sblk_p ans = malloc(sizeof(sblk_s));
        ans->scp_age = blk->scp_age;
        ans->m = blk->m;

        // copy inst block list
        ans->inst_block = NULL;
        mem_blk_set_t *p = blk->inst_block;
        while (p) {
            mem_blk_set_t *q = malloc(sizeof(mem_blk_set_t));
            q->block = p->block;
            q->next = ans->inst_block;
            ans->inst_block = q;
            p = p->next;
        }
        ans->ys_set = NULL;
        worklist_p node = blk->ys_set;
        for (; node != NULL; node = node->next) {
                addToWorkList(&ans->ys_set, node->data);
        }
        ans->inst_ys_set = NULL;
        node = blk->inst_ys_set;
        for (; node != NULL; node = node->next) {
                addToWorkList_inst_ys(&ans->inst_ys_set, node->data);
        }
        return ans;
}

void scp_discardWorkList(worklist_p* wl) {
        worklist_p p = *wl;
        while (p != NULL) {
                worklist_p t = p->next;
                free(p);
                p = t;
        }
        *wl = NULL;
}

void scp_discardWorkList_inst_ys(worklist_p* wl) {
        worklist_p p = *wl;
        while (p != NULL) {
                worklist_p t = p->next;
                mem_blk_set_t *p1, *p2;
                p1 = p->data;
                while (p1) {
                    p2 = p1->next;
                    free(p1);
                    p1 = p2;
                }
                free(p);
                p = t;
        }
        *wl = NULL;
}

void scp_totally_discardWorkList(worklist_p* wl) {
        worklist_p p = *wl;
        while (p != NULL) {
                mem_blk_set_t *p1, *p2;
                worklist_p t = p->next;
                sblk_p s = (sblk_p)(p->data);
                scp_discardWorkList(&s->ys_set);
                scp_discardWorkList_inst_ys(&s->inst_ys_set);
                p1 = s->inst_block;
                while (p1) {
                    p2 = p1->next;
                    free(p1);
                    p1 = p2;
                }
                free(p->data);
                free(p);
                p = t;
        }
        *wl = NULL;
}

/*
 * copy src to dst
 */
void scp_cpyACS(scp_acs dst, scp_acs src) {
        if (dst == NULL) {
                printf("scp_cpyACS:NULL\n");
        }
        int cacheset;
        for (cacheset = 0; cacheset < MAX_CACHE_SET; cacheset++) {
                worklist_p src_cs = src[cacheset];
                scp_totally_discardWorkList(&dst[cacheset]);
                dst[cacheset] = NULL;
                for (; src_cs != NULL; src_cs = src_cs->next) {
                        sblk_p blk = src_cs->data;
                        addToWorkList(&dst[cacheset], scp_cpySBlk(blk));
                }
        }
}

sblk_p scp_createSBlk(saddr_p addr) {
        sblk_p ans = malloc(sizeof(sblk_s));
        ans->scp_age = 1;
        ans->ys_set = NULL;
        ans->inst_ys_set = NULL;
        ans->m = addr;
        ans->inst_block = NULL;
        return ans;
}
sblk_p scp_createSBlk_inst(unsigned block) {
        sblk_p ans = malloc(sizeof(sblk_s));
        ans->scp_age = 1;
        ans->ys_set = NULL;
        ans->inst_ys_set = NULL;
        ans->m = NULL;
        ans->inst_block = malloc(sizeof(mem_blk_set_t));
        ans->inst_block->block = block;
        ans->inst_block->next = NULL;
        return ans;
}
/**
 * return length of a linked list
 */
int scp_length(worklist_p wk) {
        int ans = 0;
        for (; wk != NULL; wk = wk->next) {
                ans++;
        }
        return ans;
}
/**
 * - compare 2 data memory blocks with their temporal-scopes
 * - return 0: not equal, 1: equal
 * - NOTE:2 temporal-scopes of same memory block
 *  could be considered to be equal if they share the same accessed intervals
 *  in outer loops of lp (ignore the differences in nested loops of lp)
 *  - if lp is NULL then all loop levels are compared
 */
int scp_cmp_saddr(saddr_p dst, saddr_p src, loop_t* lp) {
        if (dst->blkAddr != src->blkAddr)
                return 0;

        /*if (lp!=NULL) */
        if (lp != NULL) {
                while (lp != NULL) {
                        ts_p ts_dst = scp_ts(dst->tsList, lp);
                        ts_p ts_src = scp_ts(src->tsList, lp);
                        if (ts_dst != NULL && ts_src != NULL) {
                                if (ts_dst->lw == ts_src->lw && ts_dst->up == ts_src->up) {
                                        /*do nothing*/
                                } else {
                                        /*not equal*/
                                        return 0;
                                }
                        } else if (ts_dst == NULL && ts_src == NULL) {
                                /*do nothing*/
                        } else {
                                /* not equal */
                                /*
                                 * NOTE: address should be fixed
                                 *
                                 */
                                return 0;
                        }
                        lp = lp->parent;
                }
                return 1;
        } else {/*lp == NULL*/

                if (scp_length(dst->tsList) != scp_length(src->tsList))
                        return 0;
                worklist_p dstnode = dst->tsList;
                for (; dstnode != NULL; dstnode = dstnode->next) {
                        ts_p ts = dstnode->data;
                        worklist_p srcnode = src->tsList;
                        int found = 0;
                        for (; srcnode != NULL; srcnode = srcnode->next) {
                                ts_p tssrc = srcnode->data;
                                if (ts->loop_id == tssrc->loop_id && ts->lw == tssrc->lw
                                                && ts->up == tssrc->up) {
                                        found = 1;
                                        break;
                                }
                        }
                        if (found == 0)
                                return 0;
                }
                return 1;
        }
}
sblk_p scp_join_search(saddr_p mblk, worklist_p cacheset, loop_t*lp) {
        for (; cacheset != NULL; cacheset = cacheset->next) {
                sblk_p ablk = cacheset->data;
                /*duy: make sure that this scope-block contains a data memory block*/
                if (ablk->m == NULL
                )
                        continue;
                if (scp_cmp_saddr(ablk->m, mblk, lp) == 1) {
                        return ablk;
                }
        }
        return NULL;
}
/*isResident*/
sblk_p scp_join_search_inst(mem_blk_set_t* iblock, worklist_p cacheset) {
        for (; cacheset != NULL; cacheset = cacheset->next) {
                sblk_p ablk = cacheset->data;
                if (ablk->inst_block == NULL
                )
                        continue;
                if (ablk->inst_block->block == iblock->block)
                        return ablk;
        }
        return NULL;
}
void scp_add2YS(worklist_p* ys, saddr_p address) {
        worklist_p node = *ys;
        int found = 0;
        while (node != NULL) {
                saddr_p addr = node->data;
                if (scp_cmp_saddr(addr, address, NULL) == 1) { //NOTE: all levels are checked
                        found = 1;
                        break;
                }
                node = node->next;
        }
        if (found == 0) {
                addToWorkList(ys, address);
        }
}

void scp_add2instYS(worklist_p* inst_ys, unsigned iblock) {

        worklist_p node = *inst_ys;
        int found = 0;
        while (node != NULL) {
                mem_blk_set_t* nblock = node->data;
                if (nblock->block == iblock) {
                        found = 1;
                        break;
                }
                node = node->next;
        }
        if (found == 0) {
                mem_blk_set_t* temp = malloc(sizeof(mem_blk_set_t));
                temp->block = iblock;
                temp->next = NULL;
                addToWorkList_inst_ys(inst_ys, temp);
                free(temp);
        }
}

void scp_unionYS(sblk_p dst, sblk_p src) {
        if (dst->scp_age >= EVICTED) {
                return;
        }
        worklist_p node = src->ys_set;
        for (; node != NULL; node = node->next) {
                saddr_p saddr = node->data;
                int found = 0;

                worklist_p dnode = dst->ys_set;
                for (; dnode != NULL; dnode = dnode->next) {
                        saddr_p daddr = dnode->data;
                        if (scp_cmp_saddr(daddr, saddr, NULL) == 1) {
                                found = 1;
                                break;
                        }
                }

                if (found == 0) {
                        addToWorkList(&dst->ys_set, saddr);
                }
        }
}
void scp_union_instYS(sblk_p dst, sblk_p src) {
        if (dst->scp_age >= EVICTED) {
                return;
        }
        worklist_p node = src->inst_ys_set;
        for (; node != NULL; node = node->next) {
                mem_blk_set_t* s_iblock = node->data;
                int found = 0;

                worklist_p dnode = dst->inst_ys_set;
                for (; dnode != NULL; dnode = dnode->next) {
                        mem_blk_set_t* d_iblock = dnode->data;
                        if (s_iblock->block == d_iblock->block) {
                                found = 1;
                                break;
                        }
                }
                if (found == 0) {
                        addToWorkList_inst_ys(&dst->inst_ys_set, s_iblock);
                }
        }
}
void scp_print_ts(worklist_p tslist) {
        for (; tslist != NULL; tslist = tslist->next) {
                ts_p ts = tslist->data;
                printf(" l%d[%d,%d]", ts->loop_id, ts->lw, ts->up);
        }
//printf("\n");
}
int scp_address_set_cardinality(worklist_p addr_set) {
        worklist_p p;
        int ans = 0;
        for (p = addr_set; p != NULL; p = p->next) {
                saddr_p addr_mem = p->data;
                worklist_p node;
                int flag = 0;
                for (node = p->next; node != NULL; node = node->next) {
                        saddr_p addr_node = node->data;
                        if (addr_node->blkAddr == addr_mem->blkAddr) {
                                flag = 1;
                                break;
                        }
                }
                if (flag == 0) {
                        ans++;
                }
        }
        return ans;
}
int scp_instr_set_cardinality(worklist_p instr_set) {
        return scp_length(instr_set);
}
void scp_update_Sblk_age(sblk_p sblk) {
#if 0
        sblk->scp_age = scp_length(sblk->ys_set) + scp_length(sblk->inst_ys_set)
        + 1;
#endif
        sblk->scp_age = scp_address_set_cardinality(sblk->ys_set)
                        + scp_instr_set_cardinality(sblk->inst_ys_set) + 1;
        if (sblk->scp_age >= EVICTED) {
                sblk->scp_age = EVICTED;
        }
}
/*
void scp_discardACS(scp_acs acs) {
        int i;
        for (i = 0; i < MAX_CACHE_SET; i++) {
                scp_discardWorkList(&acs[i]);
        }
        free(acs);
}
*/
void scp_totally_discardACS(scp_acs* p_acs) {
        scp_acs acs = *p_acs;
        int i;
        for (i = 0; i < MAX_CACHE_SET; i++) {
                worklist_p node = acs[i];
                while (node != NULL) {
                        mem_blk_set_t *p1, *p2;
                        worklist_p temp = node->next;
                        sblk_p s = (sblk_p)(node->data);
                        scp_discardWorkList(&s->ys_set);
                        scp_discardWorkList_inst_ys(&s->inst_ys_set);
                        
                        p1 = s->inst_block;
                        while (p1) {
                            p2 = p1->next;
                            free(p1);
                            p1 = p2;
                        }

                        free(node->data);
                        free(node);
                        node = temp;
                }
        }
        free(acs);
        *p_acs = NULL;
}
void scp_join(worklist_p* acs_dst, worklist_p* acs_src, loop_t*lp) {
        int cacheset;
        for (cacheset = 0; cacheset < MAX_CACHE_SET; cacheset++) {
                worklist_p dst_cs = acs_dst[cacheset];
                worklist_p src_cs = acs_src[cacheset];
                worklist_p srcnode;
                for (srcnode = src_cs; srcnode != NULL; srcnode = srcnode->next) {
                        sblk_p src_blk = srcnode->data;
                        sblk_p dst_blk = scp_join_search(src_blk->m, dst_cs, lp);
                        if (dst_blk == NULL) {
                                addToWorkList(&acs_dst[cacheset], scp_cpySBlk(src_blk));
                        } else {
                                scp_unionYS(dst_blk, src_blk);
                                scp_update_Sblk_age(dst_blk);
                        }
                }
        }
}
void uni_join(worklist_p* acs_dst, worklist_p* acs_src, loop_t*lp) {
        int cacheset;
        for (cacheset = 0; cacheset < MAX_CACHE_SET; cacheset++) {
                worklist_p dst_cs = acs_dst[cacheset];
                worklist_p src_cs = acs_src[cacheset];
                worklist_p srcnode;
                for (srcnode = src_cs; srcnode != NULL; srcnode = srcnode->next) {
                        sblk_p src_blk = srcnode->data;
                        sblk_p dst_blk = NULL;
                        if (src_blk->m != NULL) {
                                /*TODO:*/
                                dst_blk = scp_join_search(src_blk->m, dst_cs, lp);
                        } else if (src_blk->inst_block != NULL) {
                                /*TODO:*/
                                dst_blk = scp_join_search_inst(src_blk->inst_block, dst_cs);
                        } else {
                                printf("BUG IN SCOPED_BLOCK\n");
                                exit(1);
                        }
                        if (dst_blk == NULL) {
                                addToWorkList(&acs_dst[cacheset], scp_cpySBlk(src_blk));
                        } else {
                                scp_unionYS(dst_blk, src_blk);
                                scp_union_instYS(dst_blk, src_blk);
                                scp_update_Sblk_age(dst_blk);
                        }
                }
        }
}
void uni_update_inst(scp_acs acs, unsigned inst_block) {
        /*note: inst_block is the address of instruction memory block,
         * not of the instruction*/
        int cacheset = GET_SET(inst_block);
        worklist_p node;
        for (node = acs[cacheset]; node != NULL; node = node->next) {
                sblk_p sblk = node->data;
                sblk->flag = SBLK_FREE;
        }
        mem_blk_set_t iblk;
        iblk.block = inst_block;
        iblk.next = NULL;

        sblk_p inst_sblk = scp_join_search_inst(&iblk, acs[cacheset]);
        if (inst_sblk == NULL) {
                /*inst_block 's not in ACS*/
                inst_sblk = scp_createSBlk_inst(iblk.block);
                addToWorkList(&acs[cacheset], inst_sblk);
                inst_sblk->flag = SBLK_DONE;
        } else {
                /*instblock 's already in ACS*/
                /*renew scoped block: reset younger set*/
                scp_discardWorkList(&(inst_sblk->ys_set));
                scp_discardWorkList_inst_ys(&(inst_sblk->inst_ys_set));

                inst_sblk->ys_set = NULL;
                inst_sblk->inst_ys_set = NULL;
                inst_sblk->scp_age = 1;
                inst_sblk->flag = SBLK_DONE;
        }
        for (node = acs[cacheset]; node != NULL; node = node->next) {
                sblk_p sblk = node->data;
                if (sblk->flag == SBLK_DONE) {
                        continue;
                }
                scp_add2instYS(&sblk->inst_ys_set, iblk.block);
                scp_update_Sblk_age(sblk);
                sblk->flag = SBLK_DONE;
        }

}

void uni_update_data(scp_acs acs, worklist_p addrset, loop_t*lp) {
        scp_acs temp_acs = scp_createEmptyACS();
        scp_cpyACS(temp_acs, acs);
        scp_data_update(acs, addrset, lp);
        uni_join(acs, temp_acs, lp);
        //scp_discardACS(temp_acs);
        scp_totally_discardACS(&temp_acs);
}
void uni_inst_filter_function(int bbi_id, scp_acs mpa_acs_out, de_inst_t* inst,
                int inst_id, loop_t*lp) {

        /* Each instruction corresponds to two addresses. Update
         * the instruction cache state accordingly */
        if (inst_chmc_l1[bbi_id][inst_id] == ALL_MISS) {
                /*CAC: A - always access to ul2 cache*/
                uni_update_inst(mpa_acs_out, GET_MEM(inst->addr));
                uni_update_inst(mpa_acs_out, GET_MEM(inst->addr+SIZE_OF_WORD));
        } else if (inst_chmc_l1[bbi_id][inst_id] == NOT_CLASSIFIED
                        || inst_chmc_l1[bbi_id][inst_id] == PS) {
                /*CAC: U - uncertainly access to ul2 cache*/
                /*first part*/
                scp_acs temp_acs = scp_createEmptyACS();
                scp_cpyACS(temp_acs, mpa_acs_out);
                uni_update_inst(mpa_acs_out, GET_MEM(inst->addr));
                uni_join(mpa_acs_out, temp_acs, lp);
                //scp_discardACS(temp_acs);
                scp_totally_discardACS(&temp_acs);
                /*second part*/
                temp_acs = scp_createEmptyACS();
                scp_cpyACS(temp_acs, mpa_acs_out);
                uni_update_inst(mpa_acs_out, GET_MEM(inst->addr+SIZE_OF_WORD));
                uni_join(mpa_acs_out, temp_acs, lp);
                //scp_discardACS(temp_acs);
                scp_totally_discardACS(&temp_acs);
        } else {/*CAC: N - never access to ul2 cache*/
                /*do nothing*/
        }
}
void uni_transform_ul2acs(tcfg_node_t* bbi, loop_t*lp) {
        /*note: bbi->mpa_acs_out must be a copy of bbi->mpa_acs_in before entering this procedure */
        int inst_id;
        for (inst_id = 0; inst_id < bbi->bb->num_inst; inst_id++) {
                de_inst_t* inst = &(bbi->bb->code[inst_id]);
                /********************************************************/
                /*filter function for instruction memory block in unified cache analysis*/
                uni_inst_filter_function(bbi->id, bbi->mpa_acs_out, inst, inst_id, lp);
                /********************************************************/

                int iType = inst_type(inst);
                /* load/store instruction */
                if (iType == INST_LOAD || iType == INST_STORE) {
                        int ls_index = -1;
                        /***************************************************/
                        /*search for the index of inst in d_instlist*/
                        for (ls_index = 0; ls_index < bbi->bb->num_d_inst; ls_index++) {
                                dat_inst_t* dat = bbi->bb->d_instlist;
                                dat = dat + ls_index;
                                de_inst_t* insn = dat->insn;
                                addr_t addr = insn->addr;
                                if (addr == inst->addr)
                                        break;
                        }
                        if (ls_index >= bbi->bb->num_d_inst) {
                                printf("NO INSTRUCTION!\n");
                                exit(1);
                        }
                        /***************************************************/
                        worklist_p addrset = bbi->address_set[ls_index];
                        /*update unified cache for data memory block*/
                        uni_update_data(bbi->mpa_acs_out, addrset, lp);
                }
        }
}
void scp_data_update(scp_acs acs, worklist_p addr_in, loop_t*lp) {
        int cacheset;
        for (cacheset = 0; cacheset < MAX_CACHE_SET; cacheset++) {
                worklist_p addrset;
                for (addrset = acs[cacheset]; addrset != NULL;
                                addrset = addrset->next) {
                        sblk_p sblk = addrset->data;
                        sblk->flag = SBLK_FREE;
                }
                worklist_p xf = NULL;
                for (addrset = addr_in; addrset != NULL; addrset = addrset->next) {
                        saddr_p saddr = addrset->data;
                        if (GET_SET(saddr->blkAddr) == cacheset) {
                                addToWorkList(&xf, saddr); //TODO: discard xf
                        }
                }

                for (addrset = xf; addrset != NULL; addrset = addrset->next) {
                        saddr_p maddr = addrset->data;
                        sblk_p iblk = scp_join_search(maddr, acs[cacheset], lp);

                        if (iblk == NULL) {
                                iblk = scp_createSBlk(maddr);
                                addToWorkList(&acs[cacheset], iblk); //not in s_in
                                iblk->flag = SBLK_DONE;
                        } else {
                                worklist_p node = addr_in;
                                int overlap = 0;
                                for (; node != NULL; node = node->next) {
                                        saddr_p address = node->data;
                                        if (scp_overlap(maddr, address, lp) == 1) {
                                                overlap = 1;
                                                break;
                                        }
                                }
                                if (overlap == 0) {
                                        scp_discardWorkList(&(iblk->ys_set));
                                        scp_discardWorkList_inst_ys(&(iblk->inst_ys_set));
                                        /*reset younger set*/
                                        iblk->scp_age = 1;
                                        iblk->ys_set = NULL; // not overlap with any data reference -> renew
                                        iblk->inst_ys_set = NULL;
                                } else {
                                        node = xf;
                                        for (; node != NULL; node = node->next) {
                                                saddr_p address = node->data;
                                                if (scp_overlap(maddr, address, lp) == 1) { //TODO: try to replace maddr with iblk->m and check the result
                                                        //addToWorkList(&iblk->ys_set, address); //otherwise
                                                        scp_add2YS(&(iblk->ys_set), address);
                                                }
                                        }
                                        scp_update_Sblk_age(iblk);
                                }
                                iblk->flag = SBLK_DONE;
                        }
                }

                for (addrset = acs[cacheset]; addrset != NULL;
                                addrset = addrset->next) {
                        sblk_p sblk = addrset->data;
                        if (sblk->flag == SBLK_DONE) {
                                continue;
                        }
                        if (sblk->m != NULL) {
                                /* data memory block */
                                worklist_p node = xf;
                                for (; node != NULL; node = node->next) {
                                        saddr_p address = node->data;
                                        if (scp_overlap(sblk->m, address, lp) == 1) {
                                                //addToWorkList(&sblk->ys_set, address);
                                                scp_add2YS(&(sblk->ys_set), address); //otherwise
                                        }
                                }
                                scp_update_Sblk_age(sblk);
                                sblk->flag = SBLK_DONE;
                        } else if (sblk->inst_block != NULL) {
                                /* instruction memory block */
                                worklist_p node = xf;
                                for (; node != NULL; node = node->next) {
                                        saddr_p address = node->data;
                                        scp_add2YS(&(sblk->ys_set), address);
                                }
                                scp_update_Sblk_age(sblk);
                                sblk->flag = SBLK_DONE;
                        }
                }
                /*discard xf*/
                scp_discardWorkList(&xf);
        }
}

void scp_print_ACS(scp_acs acs, loop_t*lp) {
        int i;
        for (i = 0; i < MAX_CACHE_SET; i++) {
#if 1
                if (i != 30)
                        continue;
#endif
                printf("\tcacheset %d(lp:%d):\n", i, lp->id);
                worklist_p node;
                for (node = acs[i]; node != NULL; node = node->next) {
                        sblk_p sblk = node->data;
#if 0
                        if (sblk->scp_age >= EVICTED)
                        continue;
#endif
                        printf("\t0x%x[%d]D", sblk->m->blkAddr, sblk->scp_age);
                        if (sblk->scp_age >= EVICTED
                        )
                                printf("[x]");
                        scp_print_ts(sblk->m->tsList);
                        printf("\n");
                        worklist_p p = sblk->ys_set;
                        while (p != NULL) {
                                saddr_p addr = p->data;
                                printf("\t\t%xD", addr->blkAddr);
                                scp_print_ts(addr->tsList);
                                printf("\n");
                                p = p->next;
                        }
                }
                printf("\n");
        }
}
void uni_print_ACS(scp_acs acs, loop_t*lp) {
        int i;
        for (i = 0; i < MAX_CACHE_SET; i++) {
                printf("\tcacheset %d(lp:%d):\n", i, lp->id);
                worklist_p node;
                for (node = acs[i]; node != NULL; node = node->next) {
                        sblk_p sblk = node->data;
#if 0
                        if (sblk->scp_age >= EVICTED)
                        continue;
#endif
                        if (sblk->m != NULL) {
                                /*data memory block*/
                                printf("\t\t0x%x[%d]D", sblk->m->blkAddr, sblk->scp_age);
                                scp_print_ts(sblk->m->tsList);
                        } else if (sblk->inst_block != NULL) {
                                /*instruction memory block*/
                                printf("\t\t0x%x[%d]I", sblk->inst_block->block, sblk->scp_age);
                        }
                        printf("\n");
                        //              printf("\t\tdata_ys:\n");
                        worklist_p p = sblk->ys_set;
                        while (p != NULL) {
                                saddr_p addr = p->data;
                                printf("\t\t\t%xD", addr->blkAddr);
                                scp_print_ts(addr->tsList);
                                printf("\n");
                                p = p->next;
                        }
//                      printf("\t\tinst_ys:\n");
                        p = sblk->inst_ys_set;
                        while (p != NULL) {
                                mem_blk_set_t* temp = p->data;
                                printf("\t\t\t%xI", temp->block);
                                printf("\n");
                                p = p->next;
                        }
                }
                printf("\n");
        }
}
int scp_compareACS(scp_acs acs_a, scp_acs acs_b, loop_t*lp) {
        int i;
        for (i = 0; i < MAX_CACHE_SET; i++) {
                worklist_p cs_a = acs_a[i];
                worklist_p cs_b = acs_b[i];
                worklist_p node;
                for (node = cs_a; node != NULL; node = node->next) {
                        sblk_p blk_a = node->data;
                        if (blk_a->m != NULL) {/*data memory block*/
                                sblk_p blk_b = scp_join_search(blk_a->m, cs_b, lp);
                                if (blk_b != NULL && blk_a->scp_age == blk_b->scp_age) {
                                        continue;
                                }
                                return ACS_NOT_IDENTICAL;
                        } else if (blk_a->inst_block != NULL) {/*instruction memory block*/
                                sblk_p blk_b = scp_join_search_inst(blk_a->inst_block, cs_b);
                                if (blk_b != NULL && blk_a->scp_age == blk_b->scp_age) {
                                        continue;
                                }
                                return ACS_NOT_IDENTICAL;
                        }
                }
        }
        return ACS_IDENTICAL;
}
void scp_datal2_update(scp_acs acs, worklist_p addr_in, loop_t*lp) {
        scp_acs acs_in = scp_createEmptyACS();
        scp_cpyACS(acs_in, acs);
        scp_data_update(acs, addr_in, lp);
        scp_join(acs, acs_in, lp);
        //scp_discardACS(acs_in);
        scp_totally_discardACS(&acs_in);
}
void scp_analyze_loop_ps(loop_t* lp, int analysis) {

        tcfg_node_t* head = lp->head;
        int i;
        for (i = 0; i < num_tcfg_nodes; i++) {
                tcfg_node_t* bbi = tcfg[i];
                loop_t* innerLp = loop_map[bbi->id];
                if (innerLp == NULL || isInner(innerLp->id, lp->id) == 0)
                        continue;
                int j = 0;
                if (bbi->mpa_acs_in) 
                    scp_totally_discardACS(&bbi->mpa_acs_in);
                if (bbi->mpa_acs_out)
                    scp_totally_discardACS(&bbi->mpa_acs_out);
                bbi->mpa_acs_in = scp_createEmptyACS();
                bbi->mpa_acs_out = scp_createEmptyACS();
                for (j = 0; j < MAX_CACHE_SET; j++) {
                        bbi->mpa_acs_in[j] = NULL;
                        bbi->mpa_acs_out[j] = NULL;
                }

        }
        int firstvisited[num_tcfg_nodes];
        for (i = 0; i < num_tcfg_nodes; i++) {
                firstvisited[i] = 1;
        }
        worklist_p qHead, qTail;
        qHead = qTail = NULL;
        scp_enqueue(head, &qHead, &qTail);
        int changed = 0;
        while (scp_empty_queue(qHead, qTail) == 0) {
                tcfg_node_t* curnode = scp_dequeue(&qHead, &qTail);
                scp_acs acs_in = scp_createEmptyACS();
                tcfg_edge_t* in_e;
                for (in_e = curnode->in; in_e != NULL; in_e = in_e->next_in) {
                        loop_t *in_e_loop = loop_map[in_e->src->id];
                        if (in_e_loop && scp_cmpLpOrder(lp->id, in_e_loop->id) >= 0) { //TODO: change here
                                if (analysis == L1_DCACHE_ANALYSIS
                                                || analysis == L2_DCACHE_ANALYSIS) {
                                        scp_join(acs_in, in_e->src->mpa_acs_out, lp);
                                } else if (analysis == UNIFIED_CACHE_ANALYSIS) {
                                        uni_join(acs_in, in_e->src->mpa_acs_out, lp);
                                }
                        }
                }

                changed = scp_compareACS(acs_in, curnode->mpa_acs_in, lp);
                if (firstvisited[curnode->id] == 0 && changed == ACS_IDENTICAL) {
                        //scp_discardACS(acs_in);
                        scp_totally_discardACS(&acs_in);
                        continue;
                }
                if (firstvisited[curnode->id] == 1)
                        firstvisited[curnode->id] = 0;
                //scp_discardACS(curnode->mpa_acs_in);
                //scp_totally_discardACS(&curnode->mpa_acs_in);
                //curnode->mpa_acs_in = acs_in;
                scp_cpyACS(curnode->mpa_acs_in, acs_in);
                scp_totally_discardACS(&acs_in);
                scp_cpyACS(curnode->mpa_acs_out, curnode->mpa_acs_in);
                int i;
                if (analysis == L1_DCACHE_ANALYSIS || analysis == L2_DCACHE_ANALYSIS) {
                        for (i = 0; i < curnode->bb->num_d_inst; i++) {
                                if (analysis == L1_DCACHE_ANALYSIS) {
                                        scp_data_update(curnode->mpa_acs_out,
                                                        curnode->address_set[i], lp);
                                } else if (analysis == L2_DCACHE_ANALYSIS) {
                                        scp_datal2_update(curnode->mpa_acs_out,
                                                        curnode->address_set[i], lp);
                                }
                        }
                } else if (analysis == UNIFIED_CACHE_ANALYSIS) {
                        /*mpa_acs_out 's already a copy of mpa_acs_in*/
                        uni_transform_ul2acs(curnode, lp);
                }

                tcfg_edge_t* out_e;
                for (out_e = curnode->out; out_e != NULL; out_e = out_e->next_out) {
                        loop_t *out_e_loop = loop_map[out_e->dst->id];
                        if (out_e_loop == NULL || isInner(out_e_loop->id, lp->id) == 0)
                            continue;
                        if (out_e_loop && scp_cmpLpOrder(lp->id, out_e_loop->id) >= 0) { //TODO: change here
                                scp_enqueue(out_e->dst, &qHead, &qTail);
                        }
                }
        }

        for (i = 0; i < num_tcfg_nodes; i++) {
                tcfg_node_t* bbi = tcfg[i];
                loop_t* innerLp = loop_map[bbi->id];
                if (innerLp == NULL || isInner(innerLp->id, lp->id) == 0) //TODO: change here
                        continue;
                int inst_index = 0;
                int dat_inst_index = 0;
                scp_acs acs_it = scp_createEmptyACS();
                scp_cpyACS(acs_it, bbi->mpa_acs_in);
                for (inst_index = 0; inst_index < bbi->bb->num_inst; inst_index++) {
                        de_inst_t* inst = &(bbi->bb->code[inst_index]);
                        int iType = inst_type(inst);
                        if (iType == INST_LOAD || iType == INST_STORE) {
                                /*
                                 * (hit/miss) access pattern classification for data memory block
                                 */
                                if (dat_inst_index >= bbi->bb->num_d_inst) {
                                        printf(
                                                        "panic: too manry load/store instructions (%d>=%d) -\n",
                                                        dat_inst_index, bbi->bb->num_d_inst);
                                        exit(1);
                                }
                                worklist_p node;
                                for (node = bbi->address_set[dat_inst_index]; node != NULL;
                                                node = node->next) {
                                        saddr_p addr = node->data;
                                        if (scp_addrINacs(addr, acs_it, lp) == 1) {
                                                addToWorkList(&(addr->psLoop), lp);
                                        }
                                }
                        }
                        /*
                         * hit/miss classification for instruction memory block
                         */
                        if (analysis == UNIFIED_CACHE_ANALYSIS) {
                                categorize_ul2_inst_PS_NC(bbi->id, acs_it, inst_index, inst,
                                                lp);
                        }
                        /****************** update ACS ***********************/
                        if (analysis == UNIFIED_CACHE_ANALYSIS) {
                                /*
                                 * update instruction memory block
                                 * just calling filter function for instruction memory block
                                 */
                                uni_inst_filter_function(bbi->id, acs_it, inst, inst_index, lp);
                        }

                        if (iType == INST_LOAD || iType == INST_STORE) {
                                /*
                                 * update data memory block
                                 */
                                if (dat_inst_index >= bbi->bb->num_d_inst) {
                                        printf(
                                                        "panic: too manry load/store instructions (%d>=%d)\n",
                                                        dat_inst_index, bbi->bb->num_d_inst);
                                        exit(1);
                                }
                                worklist_p addrset = bbi->address_set[dat_inst_index];
                                if (analysis == L1_DCACHE_ANALYSIS) {
                                        scp_data_update(acs_it, addrset, lp);
                                } else if (analysis == L2_DCACHE_ANALYSIS) {
                                        scp_datal2_update(acs_it, addrset, lp);
                                } else if (analysis == UNIFIED_CACHE_ANALYSIS) {
                                        uni_update_data(acs_it, addrset, lp);
                                }
                                dat_inst_index++; //NOTE: be carefull
                        }
                }
                //scp_discardACS(acs_it);
                scp_totally_discardACS(&acs_it);
        }

        /*****************************************************************/
        /*
         * discard ACS to free memory
         */
        for (i = 0; i < num_tcfg_nodes; i++) {
                tcfg_node_t* bbi = tcfg[i];
                loop_t* innerLp = loop_map[bbi->id];
                if (innerLp == NULL || isInner(innerLp->id, lp->id) == 0)
                        continue;
                scp_totally_discardACS(&bbi->mpa_acs_in);
                scp_totally_discardACS(&bbi->mpa_acs_out);
        }
}
int scp_addrINacs(saddr_p maddr, scp_acs acs, loop_t*lp) {
        int cacheset = GET_SET(maddr->blkAddr);
        worklist_p node;
        if (cacheset < 0)
            return 0;
        for (node = acs[cacheset]; node != NULL; node = node->next) {
                //printf("address:0x%x cacheset:%d mem:%x\n", node,cacheset,maddr->blkAddr);
                sblk_p sblk = (sblk_p) node->data;
                if (sblk->m == NULL
                )
                        continue;
                if (scp_cmp_saddr(maddr, sblk->m, lp) == 1) {
                        if (sblk->scp_age < EVICTED) {
                                return 1;
                        } else {
                                return 0;
                        }
                }
        }
        return 0;
}
int scp_instINacs(mem_blk_set_t* iblock, scp_acs acs) {
        int cacheset = GET_SET(iblock->block);
        worklist_p node;
        for (node = acs[cacheset]; node != NULL; node = node->next) {
                sblk_p sblk = node->data;
                if (sblk->inst_block == NULL
                )
                        continue;
                if (sblk->inst_block->block == iblock->block) {
                        if (sblk->scp_age < EVICTED
                        )
                                return 1;
                        else
                                return 0;
                }
        }
        return 0;
}
void categorize_ul2_inst_PS_NC(int bbi_id, scp_acs mpa_acs_in, int inst_id,
                de_inst_t* inst, loop_t*lp) {
#if 0
        de_inst_t* inst = &bbi->bb->code[inst_id];
#endif
        mem_blk_set_t temp;
        int h1, h2;
        temp.block = GET_MEM(inst->addr);
        temp.next = NULL;
#if 0
        h1 = scp_instINacs(&temp, bbi->mpa_acs_in);
#endif
        h1 = scp_instINacs(&temp, mpa_acs_in);
        temp.block = GET_MEM(inst->addr + SIZE_OF_WORD);
#if 0
        h2 = scp_instINacs(&temp, bbi->mpa_acs_in);
#endif
        h2 = scp_instINacs(&temp, mpa_acs_in); //NOTE: be carefull
        if (inst_chmc_l1[bbi_id][inst_id] == ALL_HIT) {
                inst_psnc_ul2[bbi_id][inst_id] = ALL_X;
        } else if ((h1 && h2) && inst_psnc_ul2[bbi_id][inst_id] == NOT_CLASSIFIED) {
                inst_psnc_ul2[bbi_id][inst_id] = PS;
                if (inst_ps_loop_ul2[bbi_id][inst_id] == NULL) {
                        inst_ps_loop_ul2[bbi_id][inst_id] = lp;
                }
                /*ignore this if the algorithm visits the most outer loop first*/
                else if (scp_cmpLpOrder(inst_ps_loop_ul2[bbi_id][inst_id]->id, lp->id)
                                < 0) { //TODO: change here
                        inst_ps_loop_ul2[bbi_id][inst_id] = lp;
                }
        }
}
int scp_est_ts_size(worklist_p tslist, loop_t* lpPS) {
        int ans = 1;
        if (lpPS == NULL
        )
                return ans;
        while (lpPS != NULL) {
                worklist_p node = tslist;
                ts_p ts = NULL;
                while (node != NULL) {
                        ts = node->data;
                        if (ts->loop_id == lpPS->id)
                                break;
                        node = node->next;
                }
                ans = ans * (ts->up - ts->lw + 1);
                lpPS = lpPS->parent;
        }
        return ans;
}
loop_t* scp_mostOuterLoop(worklist_p lparr) {
        loop_t* ans;
        if (lparr == NULL
        )
                return NULL;
        ans = lparr->data;
        lparr = lparr->next;
        while (lparr != NULL) {
                loop_t* lp = lparr->data;
                if (scp_cmpLpOrder(ans->id, lp->id) < 0) //TODO: change here
                        ans = lp;
                lparr = lparr->next;
        }
        return ans;
}

#if 0
void scp_cal_cachemiss() {
        int i;
        for (i = 0; i < num_tcfg_nodes; i++) {
                tcfg_node_t* bbi = tcfg[i];
                if (bbi->bb->num_d_inst > 0) {
                        printf("\nBasic Block %d lp:%d\n", bbi->id, loop_map[bbi->id]);
                        int max_l1 = 0;
                        int max_l2 = 0;
                        int j = 0;
                        for (j = 0; j < bbi->bb->num_d_inst; j++) {
                                dat_inst_t* dat = bbi->bb->d_instlist;
                                dat = dat + j;
                                insn_t* insn = dat->insn;
                                printf(".DataRef 0x%s ", insn->addr);
                                if (isStoreInst(insn->op))
                                printf("[STORE]");
                                else
                                printf("[LOAD]");
                                printf("\n");
                                int max_miss_l1 = 0;
                                int max_miss_l2 = 0;
                                worklist_p node;
                                for (node = bbi->addrset_l1[j]; node != NULL;
                                                node = node->next) {
                                        saddr_p maddr = node->data;
                                        printf("\t0x%x (%d)", maddr->blkAddr,
                                                        GET_SET(maddr->blkAddr));
                                        scp_print_ts(maddr->tsList);
                                        worklist_p lpans = maddr->psLoop;
                                        int miss = 1;
                                        if (lpans != NULL) {
                                                worklist_p temp = lpans;
                                                while (temp != NULL) {
                                                        loop_t* tlp = temp->data;
                                                        printf(" l%d ", tlp->id);
                                                        temp = temp->next;
                                                }
                                                loop_t* tlp = scp_mostOuterLoop(lpans);
                                                printf(" outerLp:%d ", tlp->id);
                                                miss = scp_est_ts_size(maddr->tsList, tlp->parent);
                                        } else {
                                                miss = scp_est_ts_size(maddr->tsList,
                                                                loop_map[bbi->id]);
                                        }
                                        printf(" miss:%d", miss);
                                        printf("\n");
                                        max_miss_l1 += miss;
                                }
                                if (enable_scp_dl2cache == 1) {
                                        //worklist_p node;
                                        printf("L2 data cache\n");
                                        for (node = bbi->addrset_l2[j]; node != NULL;
                                                        node = node->next) {
                                                saddr_p maddr = node->data;
                                                printf("\t0x%x (%d)", maddr->blkAddr,
                                                                GET_SET(maddr->blkAddr));
                                                scp_print_ts(maddr->tsList);
                                                worklist_p lpans = maddr->psLoop;
                                                int miss = 1;
                                                if (lpans != NULL) {
                                                        worklist_p temp = lpans;
                                                        while (temp != NULL) {
                                                                loop_t* tlp = temp->data;
                                                                printf(" l%d", tlp->id);
                                                                temp = temp->next;
                                                        }
                                                        loop_t* tlp = scp_mostOuterLoop(lpans);
                                                        printf(" outerLp:%d ", tlp->id);
                                                        miss = scp_est_ts_size(maddr->tsList, tlp->parent);
                                                } else {
                                                        miss = scp_est_ts_size(maddr->tsList,
                                                                        loop_map[bbi->id]);
                                                }
                                                printf(" miss:%d", miss);
                                                printf("\n");
                                                max_miss_l2 += miss;
                                        }
                                }
                                loop_t* lp = loop_map[bbi->id];
                                int max_exec = lp->exec;
                                if (max_miss_l1 > max_exec)
                                max_miss_l1 = max_exec;
                                if (max_miss_l2 > max_exec)
                                max_miss_l2 = max_exec;
                                max_l1 += max_miss_l1;
                                max_l2 += max_miss_l2;
                                printf(" maxMiss in L1:%d", max_miss_l1);
                                if (enable_scp_dl2cache == 1) {
                                        printf(" L2:%d", max_miss_l2);
                                }
                                printf("\t");
                                printf("ps in L1: ");
                                lp = scp_inner_ps_loop(bbi->addrset_l1[j]);
                                if (lp == NULL
                                )
                                printf("NULL");
                                else
                                printf("%d", lp->id);
                                if (enable_scp_dl2cache) {
                                        printf(" L2:");
                                        lp = scp_inner_ps_loop(bbi->addrset_l2[j]);
                                        if (lp == NULL
                                        )
                                        printf("NULL");
                                        else
                                        printf("%d", lp->id);
                                }
                                printf("\n");
                        }
                        printf("Basic block %d maxMs in L1: %d L2:%d\n", bbi->id, max_l1,
                                        max_l2);
//                      printf("dump in_ACS\n");
//                      worklist_p node_lp = bbi->mpa_lp_in;
//                      worklist_p acs_node = bbi->mpa_acsin_arr;
//                      while (node_lp != NULL) {
//                              loop_t* lp = node_lp->data;
//                              printf("ACS in lp %d\n", lp->id);
//                              scp_acs acs = acs_node->data;
//                              scp_print_ACS(acs);
//
//                              node_lp = node_lp->next;
//                              acs_node = acs_node->next;
//                      }
                        printf("\n");
                }
        }
}
#endif
int scp_loadstore_index(mas_inst_t* inst) {
        tcfg_node_t* bbi = tcfg[inst->bbi_id];
        if (bbi->bb->num_d_inst == 0)
                return -1;
        int i = 0;
        for (i = 0; i < bbi->bb->num_d_inst; i++) {
                dat_inst_t* dat = bbi->bb->d_instlist;
                dat = dat + i;
                de_inst_t* insn = dat->insn;
                addr_t addr = insn->addr;
                if (addr == inst->inst->addr) {
                        break;
                }
        }
        if (i >= bbi->bb->num_d_inst)
                return -1;
        else
                return i;
}
loop_t* scp_inner_ps_loop(worklist_p addrset) {
        int flag = 0;
        loop_t* lpans = NULL;
        worklist_p node = addrset;
        for (; node != NULL; node = node->next) {
                saddr_p addr = node->data;
                loop_t* tlp = scp_mostOuterLoop(addr->psLoop);
                if (flag == 0) {
                        flag = 1;
                        lpans = tlp;
                } else {
                        if (lpans != NULL && tlp != NULL) {
                                if (scp_cmpLpOrder(lpans->id, tlp->id) > 0) //TODO: change here
                                        lpans = tlp;
                        } else
                                lpans = NULL;
                }
        }
        return lpans;
}
loop_t* scp_psloop_dl(mas_inst_t* inst, int level) {
        int index = scp_loadstore_index(inst);
        if (index < 0)
                return NULL;
        tcfg_node_t* bbi = tcfg[inst->bbi_id];
        if (bbi->bb->num_d_inst == 0)
                return NULL;
        dat_inst_t* dat = bbi->bb->d_instlist;
        dat = dat + index;
        worklist_p addrset;
        if (level == 1)
                addrset = bbi->addrset_l1[index];
        else if (level == 2)
                addrset = bbi->addrset_l2[index];
        loop_t* lpans = scp_inner_ps_loop(addrset);
        return lpans;
}
void mpaex_datacache(int analysis) {
        /************* init **************/
        int i;
        for (i = 0; i < num_tcfg_nodes; i++) {
                tcfg_node_t* bbi = tcfg[i];
                inf_node_t* ib = &(inf_procs[bbi_pid(bbi)].inf_cfg[bbi_bid(bbi)]);
                bbi->loop_id = ib->loop_id;
                if (analysis == L1_DCACHE_ANALYSIS) {
                        bbi->address_set = bbi->addrset_l1;
                } else if (analysis == L2_DCACHE_ANALYSIS
                                || analysis == UNIFIED_CACHE_ANALYSIS) {
                        bbi->address_set = bbi->addrset_l2;
                }
                int j = 0;
                for (; j < bbi->bb->num_d_inst; j++) {
                        worklist_p node = bbi->address_set[j];
                        for (; node != NULL; node = node->next) {
                                saddr_p addr = node->data;
                                addr->psLoop = NULL;
                        }
                }
        }
        /*************************************/
        if (analysis == UNIFIED_CACHE_ANALYSIS) {
                inst_psnc_ul2 = calloc(num_tcfg_nodes, sizeof(char*));
                inst_ps_loop_ul2 = calloc(num_tcfg_nodes, sizeof(loop_t**));
                int i;
                for (i = 0; i < num_tcfg_nodes; i++) {
                        tcfg_node_t* bbi = tcfg[i];
                        inst_psnc_ul2[i] = calloc(bbi->bb->num_inst, sizeof(char));
                        inst_ps_loop_ul2[i] = calloc(bbi->bb->num_inst, sizeof(loop_t*));
                        int j;
                        for (j = 0; j < bbi->bb->num_inst; j++) {
                                inst_psnc_ul2[i][j] = NOT_CLASSIFIED;
                                inst_ps_loop_ul2[i][j] = NULL;
                        }
                }
        }
        /*************************************/
        scp_analyze_loop_ps(loops[0], analysis);
        for (i = num_tcfg_loops - 1; i >= 1; i--) {
                scp_analyze_loop_ps(loops[i], analysis);
        }
#if 1
        scp_test_cache_miss();
#endif

}
int loop_dist(loop_t* lp1, loop_t* lp2) {
        if (lp1 == NULL || lp2 == NULL
        )
                return -1;
        int ans = 0;
        if (scp_cmpLpOrder(lp1->id, lp2->id) > 0) { //TODO:change here
                loop_t* t = lp1;
                lp1 = lp2;
                lp2 = t;
        }
        while (lp1 != NULL) {
                ans++;
                if (lp1->id == lp2->id)
                        return ans;
                lp1 = lp1->parent;
        }
        return -100;
}
/*TODO: implement this*/
int get_mblk_hitmiss_ul2(tcfg_node_t* bbi, int mblk_id, loop_t* lp,
                int contextMask) {
        lp = loop_map[bbi->id];
        de_inst_t* inst;
        int i;
        inst = bbi->bb->code;
        for (i = 0; i < bbi->bb->num_inst; i++) {
                int mblk = MBLK_ID_L2(bbi->bb->sa, inst->addr);
                if (mblk == mblk_id) {
                        if (inst_psnc_ul2[bbi->id][i] == PS) {
                                loop_t* ps_lp = inst_ps_loop_ul2[bbi->id][i];
                                int lp_dist = loop_dist(ps_lp, lp);/*TODO: */
                                int ps_ctx = contextMask & ((1 << lp_dist) - 1);
                                if (ps_ctx == 0)
                                        return IC_MISS;
                                else
                                        return IC_HIT;
                        } else if (inst_psnc_ul2[bbi->id][i] == NOT_CLASSIFIED) {
                                return IC_UNCLEAR;
                        } else if (inst_psnc_ul2[bbi->id][i] == ALL_X) {
                                return IC_HIT;
                        }
                }
                inst++;
        }
        printf("BUGS in get_mblk_hitmiss_ul2\n");
        exit(1);
        return IC_MISS;
}
/********************************************************************/
void scp_test_cache_miss() {
        FILE* fdbg = fopen("dbg.txt", "w");
        int final_miss = 0;
        int i;
        for (i = 0; i < num_tcfg_nodes; i++) {
                tcfg_node_t* bbi = tcfg[i];
                if (bbi->bb->num_d_inst == 0)
                        continue;
                fprintf(fdbg, "Basic block %d\n", bbi->id);
                int j;
                for (j = 0; j < bbi->bb->num_d_inst; j++) {
                        dat_inst_t* dat = bbi->bb->d_instlist;
                        dat = dat + j;
                        de_inst_t* insn = dat->insn;
                        if (isStoreInst(insn->op_enum) == 1)
                                continue;
                        worklist_p addrnode;
                        int cachemiss = 0;
                        for (addrnode = bbi->address_set[j]; addrnode != NULL; addrnode =
                                        addrnode->next) {
                                saddr_p saddr = addrnode->data;
                                fprintf(fdbg, "\t0x%x(%d)", saddr->blkAddr,
                                                GET_SET(saddr->blkAddr));

                                worklist_p tsNode = saddr->tsList;
                                while (tsNode != NULL) {
                                        ts_p tscope = tsNode->data;
                                        fprintf(fdbg, " l%d[%d,%d]", tscope->loop_id, tscope->lw,
                                                        tscope->up);
                                        tsNode = tsNode->next;
                                }

                                loop_t* psLp = scp_mostOuterLoop(saddr->psLoop);
                                if (psLp == NULL) {
                                        fprintf(fdbg, " ps:NULL");
                                        psLp = loop_map[i];
                                } else {
                                        fprintf(fdbg, " ps:%d", psLp->id);
                                        worklist_p temp_wp = saddr->psLoop;
                                        while (temp_wp != NULL) {
                                                loop_t* t = temp_wp->data;
                                                fprintf(fdbg, " _%d ", t->id);
                                                temp_wp = temp_wp->next;
                                        }
                                        psLp = psLp->parent;
                                }
                                int total = 0;
                                if (psLp == NULL) {
                                        total = 1;
                                } else {
                                        total = 1;
                                        while (psLp != NULL) {
                                                worklist_p tsNode = saddr->tsList;
                                                for (; tsNode != NULL; tsNode = tsNode->next) {
                                                        ts_p tscp = tsNode->data;
                                                        if (tscp->loop_id == psLp->id) {
                                                                total *= (tscp->up - tscp->lw + 1);
                                                                break;
                                                        }
                                                }
                                                psLp = psLp->parent;
                                        }
                                }
                                cachemiss += total;
                                fprintf(fdbg, " miss:%d", total);
                                fprintf(fdbg, "\n");
                        }
                        final_miss += cachemiss;
                        fprintf(fdbg, "inst:0x%x bb:%d cache_miss:%d lp:%d\n", insn->addr,
                                        bbi->id, cachemiss, loop_map[bbi->id]?loop_map[bbi->id]->id:0);
                }
        }
        fprintf(fdbg, "total: %d\n", final_miss);
        fclose(fdbg);
}
#if 0
void scp_fprintf_ACS(FILE* fout, scp_acs acs) {
        int i;
        for (i=0;i<MAX_CACHE_SET;i++) {
                worklist_p node = acs[i];
                fprintf("\tcacheset:%d\n",i);
                for (;node!=NULL;node=node->next) {
                        sblk_p scp_blk= node->data;
                        fprintf(fout,"\t\t0x%x[%d]",scp_blk->m->blkAddr,scp_blk->scp_age);
                        worklist_p ts_node;
                        //for (ts_node=scp_blk->m->)
                }
        }
}
void scp_compare_sorted_ACSs(loop_t*lp) {
        FILE* fout = fopen("ACS_dbg.txt", "w");
        int i;
        for (i = 0; i < num_tcfg_nodes; i++) {
                tcfg_node_t* bbi = tcfg[i];
                if (scp_cmpLpOrder(loop_map[bbi->id]->id, lp->id) > 0)
                continue;
                /*
                 * TODO: sort ACS
                 */
                fprintf(fout, "Basic block %d (lp:%d) for lp:%d\n", bbi->id,
                                loop_map[bbi->id]->id, lp->id);
                fprintf(fout, "ACS_IN:\n");
                scp_fprintf_ACS(fout,bbi->mpa_acs_in);
                fprintf(fout, "ACS_OUT:\n");
                scp_fprintf_ACS(fout,bbi->mpa_acs_out);
                fprintf(fout, "\n");

        }
        fclose(fout);
}

#endif

