#ifdef __cplusplus
extern "C" {
#endif

    void global_memory_init(void);

    void local_memory_init(void);

    void global_memory_add(unsigned addr, long value);

    void local_memory_add(unsigned addr, long value);

    int global_memory_query(unsigned addr, long *value);

    int local_memory_query(unsigned addr, long *value);

#ifdef __cplusplus
}
#endif
