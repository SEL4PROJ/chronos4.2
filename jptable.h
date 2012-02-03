#ifndef __JPTABLE_H__
#define __JPTABLE_H__

#include "address.h"

typedef struct jptb {
        addr_t adr;
        int    ntarget;
        addr_t *ptarget;
        int    index;
} jptb;

extern jptb * pjptb;
extern int    bjptb;
extern int    njp;

int lookup_jptable(addr_t adr);
void get_jptable(addr_t src,int index, addr_t * target);
int get_jptable_static(addr_t src, addr_t * target);
void read_injp(char * objfile);


#endif /* __JPTABLE_H__ */

