#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include "jptable.h"

jptb * pjptb;
int    bjptb = 0;
int    njp;

int lookup_jptable(addr_t adr){
    int i;
    int num = 0;
    for(i = 0; i < njp; i++){
        if(pjptb[i].adr == adr ){
           num = pjptb[i].ntarget;
        }
    }
    return num;        
}

void get_jptable(addr_t src,int index, addr_t * target){
     int i;
     for(i = 0; i < njp; i++){
         if(pjptb[i].adr == src){
             *target = pjptb[i].ptarget[index];
             break;
          }
     } 
     assert(i < njp);
}

int get_jptable_static(addr_t src, addr_t * target){
     int i,j;
     int tail = -1;
     for(i = 0; i < njp; i++){
         if(pjptb[i].adr == src){
             j = pjptb[i].index;
             *target = pjptb[i].ptarget[j];
             pjptb[i].index++;
             if(pjptb[i].index == pjptb[i].ntarget)
                   tail = 0;
             else  
                   tail = 1;
             break;
          }
     } 
     //assert(i < njp);
     return tail;
}


void read_injp(char * objfile){
     int  tablesize,i,j;
     char file[100];
     FILE *ftable;
     sprintf(file,"%s.jtable",objfile);
     ftable = fopen(file,"r");
     if(!ftable){
        // no indirect jump
        bjptb = 0;
     }else{
        bjptb = 1;
        fscanf(ftable,"%d",&tablesize);
        njp = tablesize;
        pjptb = (jptb *)calloc(tablesize, sizeof(jptb));
        for(i = 0; i < tablesize; i++){
            fscanf(ftable,"%08x",&pjptb[i].adr);
            fscanf(ftable,"%d",&pjptb[i].ntarget);
            pjptb[i].index = 0;
            pjptb[i].ptarget = (addr_t *)calloc(pjptb[i].ntarget, sizeof(addr_t));
            for(j = 0; j < pjptb[i].ntarget; j++)
               fscanf(ftable,"%08x",&pjptb[i].ptarget[j]);
        }
        fclose(ftable);
     }
     //printf("bool: %d\n",bjptb);
}

