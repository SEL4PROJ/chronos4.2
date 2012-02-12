#ifdef __cplusplus

#define CACHE_HIT_LIST_FILENAME "cache_hit"

extern "C" {
#endif

    void global_memory_init(void);

    void local_memory_init(void);

    void global_memory_add(unsigned addr, long value);

    void local_memory_add(unsigned addr, long value);

    int global_memory_query(unsigned addr, long *value);

    int local_memory_query(unsigned addr, long *value);

    int cache_hit_p(unsigned addr);

    void init_cache_hit_list(void);

#ifdef __cplusplus
}
#endif
