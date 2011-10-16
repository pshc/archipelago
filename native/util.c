#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include "util.h"

void fail(const char *format, ...) {
	va_list args;
	va_start(args, format);
	vfprintf(stderr, format, args);
	va_end(args);
	putc('\n', stderr);
	exit(EXIT_FAILURE);
}

void error_out(const char *context) {
	perror(context);
	exit(EXIT_FAILURE);
}

struct list *nope(void) {
	return calloc(1, sizeof(struct list));
}

struct list *cons(void *car, struct list *cdr) {
	struct list *cell = malloc(sizeof *cell);
	cell->val = car;
	cell->next = cdr;
	return cell;
}

typedef int (*compare_t)(const void *, const void *);
#define EQUAL(c, a, b) ((c) ? (c)((a), (b)) == 0 : (a) == (b))

struct map {
	struct list *entries;
	compare_t compare;
};

struct entry {
	void *key, *val;
};

struct map *new_map(void *compare) {
	struct map *map = malloc(sizeof *map);
	map->compare = (compare_t) compare;
	map->entries = nope();
	return map;
}

void map_set(struct map *map, void *key, void *val) {
	struct entry *entry;
	struct list *pos;
	for (pos = map->entries; IS_CONS(pos); pos = pos->next) {
		entry = pos->val;
		if (entry->key == key) {
			entry->val = val;
			return;
		}
	}
	entry = malloc(sizeof *entry);
	entry->key = key;
	entry->val = val;
	map->entries = cons(entry, map->entries);
}

int map_has(struct map *map, const void *key) {
	compare_t compare;
	struct entry *entry;
	struct list *pos;
	compare = map->compare;
	for (pos = map->entries; IS_CONS(pos); pos = pos->next) {
		entry = pos->val;
		if (EQUAL(compare, entry->key, key))
			return 1;
	}
	return 0;
}

void *map_get(struct map *map, const void *key) {
	compare_t compare;
	struct entry *entry;
	struct list *pos;
	compare = map->compare;
	for (pos = map->entries; IS_CONS(pos); pos = pos->next) {
		entry = pos->val;
		if (EQUAL(compare, entry->key, key))
			return entry->val;
	}
	fail("Does not exist in map");
}

void map_foreach(struct map *map, map_foreach_f func) {
	struct entry *entry;
	struct list *pos;
	for (pos = map->entries; IS_CONS(pos); pos = pos->next) {
		entry = pos->val;
		func(entry->key, entry->val);
	}
}
