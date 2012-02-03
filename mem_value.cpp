#include "mem_value.h"
#include <hash_map>

using __gnu_cxx::hash_map;

hash_map <unsigned, long> global_memory;
hash_map <unsigned, long> local_memory;

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


