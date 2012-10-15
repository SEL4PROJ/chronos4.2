#ifdef __cplusplus

#define L1_CACHE_HIT_LIST_FILENAME "cache_hit_l1.txt"
#define L2_CACHE_HIT_LIST_FILENAME "cache_hit_l2.txt"

extern "C" {
#endif

    void global_memory_init(void);

    void local_memory_init(void);

    void global_memory_add(unsigned addr, long value);

    void local_memory_add(unsigned addr, long value);

    int global_memory_query(unsigned addr, long *value);

    int local_memory_query(unsigned addr, long *value);

    int cache_hit_p(unsigned addr);

    int l2_cache_hit_p(unsigned addr);

    void init_cache_hit_list(void);

#ifdef __cplusplus
}
#endif
