#ifndef UTIL_H
#define UTIL_H

#define CHECK(cond, ...) do { if (!(cond)) fail(__VA_ARGS__ ); } while (0)

#ifdef __GNUC__
void fail(const char *, ...) __printflike(1, 2) __dead2;
void error_out(const char *) __dead2;
#else
void fail(const char *, ...);
void error_out(const char *);
#endif

struct list {
	void *val;
	struct list *next;
};

struct list *nil(void);
struct list *cons(void *, struct list *);

#define IS_CONS(x) ((x)->next)
#define IS_NIL(x) (!(IS_CONS(x)))

struct map;

struct map *new_map(void *compare_func);
void map_set(struct map *, void *, void *);
int map_has(struct map *, const void *);
void *map_get(struct map *, const void *);

#endif /* UTIL_H */
