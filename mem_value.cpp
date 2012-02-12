#include "mem_value.h"
#include <stdio.h>
#include <hash_map>
#include <hash_set>

using __gnu_cxx::hash_map;
using __gnu_cxx::hash_set;

hash_map <unsigned, long> global_memory;
hash_map <unsigned, long> local_memory;
hash_set <unsigned> cache_hit_memory;

void global_memory_init(void) {
    global_memory.clear();
}

void local_memory_init(void) {
    local_memory.clear();
}

void global_memory_add(unsigned addr, long value) {
    global_memory[addr] = value;
}

void local_memory_add(unsigned addr, long value) {
    local_memory[addr] = value;
}

int global_memory_query(unsigned addr, long *value) {
    if (global_memory.find(addr) == global_memory.end())
        return 0;
    *value = global_memory[addr];
    return 1;
}

int local_memory_query(unsigned addr, long *value) {
    if (local_memory.find(addr) == local_memory.end())
        return 0;
    *value = local_memory[addr];
    return 1;
}

int cache_hit_p(unsigned addr) {
    return cache_hit_memory.find(addr) == cache_hit_memory.end() ? 0:1;
}

void init_cache_hit_list(void) {
    unsigned addr;
    int ret;
    FILE *fp;
    cache_hit_memory.clear();
    fp = fopen(CACHE_HIT_LIST_FILENAME, "r");
    if (fp == NULL) {
        printf("The file that contains always cache hit addresses is not found.\n");
        return;
    }
    while (!feof(fp)) {
        ret = fscanf(fp, "%x", &addr);
        if (ret > 0)
            cache_hit_memory.insert(addr);
    }
    fclose(fp);
}
