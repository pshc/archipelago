#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include "util.h"

typedef void (*free_t)(void *);

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

void free_list(struct list *list) {
	free_list_by(list, NULL);
}

void free_list_by(struct list *pos, void *free_val) {
	struct list *next;
	for (; IS_CONS(pos); pos = next) {
		if (free_val)
			((free_t) free_val)(pos->val);
		next = pos->next;
		free(pos);
	}
	free(pos);
}

typedef int (*compare_t)(const void *, const void *);
#define EQUAL(c, a, b) ((c) ? (c)((a), (b)) == 0 : (a) == (b))

struct map {
	struct list *entries;
	compare_t compare;
	free_t free_key, free_val;
};

struct entry {
	void *key, *val;
};

struct map *new_map(void *compare, void *free_key, void *free_val) {
	struct map *map = malloc(sizeof *map);
	map->entries = nope();
	map->compare = (compare_t) compare;
	map->free_key = free_key;
	map->free_val = free_val;
	return map;
}

void destroy_map(struct map *map) {
	struct entry *entry;
	struct list *pos, *next;
	free_t free_key, free_val;
	free_key = map->free_key;
	free_val = map->free_val;
	for (pos = map->entries; IS_CONS(pos); pos = next) {
		entry = pos->val;
		next = pos->next;
		free(pos);
		if (free_key)
			free_key(entry->key);
		if (free_val)
			free_val(entry->val);
		free(entry);
	}
	free(pos);
	free(map);
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
