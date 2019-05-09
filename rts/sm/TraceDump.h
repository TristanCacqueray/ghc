void trace_dump_start_gc(void);
void trace_dump_end_gc(void);
void trace_dump_set_source(const char *c);
void trace_dump_set_source_closure(StgClosure *c);
void trace_dump_edge(StgClosure *tgt);

