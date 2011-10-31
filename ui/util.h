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

struct list *nope(void);
struct list *cons(void *, struct list *);
void free_list(struct list *);
void free_list_by(struct list *, void *free_val);

#define IS_CONS(x) ((x)->next)
#define IS_NIL(x) (!(IS_CONS(x)))

struct map;

struct map *new_map(void *compare_func, void *free_key, void *free_val);
void destroy_map(struct map *);
void map_set(struct map *, void *, void *);
int map_has(struct map *, const void *);
void *map_get(struct map *, const void *);

typedef void (*map_foreach_f)(void *, void *);
void map_foreach(struct map *map, map_foreach_f func);

#endif /* UTIL_H */