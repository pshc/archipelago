#ifndef ARCHIPELAGO_H
#define ARCHIPELAGO_H

/* TEMP */
typedef void * func_t;

typedef void *tuple_t;
extern tuple_t *tuple(unsigned int, ...);

struct List;
extern struct List *list(unsigned int, ...);

extern void test_success(void);
extern void test_failure(const char *, const char *, const char *,
		unsigned int);

#define CHECK(cond, msg) do { if (cond) test_success(); else \
		test_failure(#cond, msg, __FILE__, __LINE__); } while (0)

#endif /* ARCHIPELAGO_H */
