#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

struct nom_atom {
	intptr_t *extrs;
	uint32_t gc_flags;
	uint32_t discrim;
};

#define TABLE_COUNT(table) ((table)[0])
#define SLOT_KEY(table, index) ((table)[1 + (index)*2])
#define SLOT_VALUE(table, index) ((table)[2 + (index)*2])

__dead2 void fail(const char *err) {
	fputs(err, stderr);
	fputc('\n', stderr);
	exit(1);
}

__dead2 void match_fail(void) {
	fputs("Match failure.\n", stderr);
	exit(1);
}

static int table_index(intptr_t *table, intptr_t count, intptr_t key) {
	int i;
	for (i = 0; i < count; i++)
		if (SLOT_KEY(table, i) == key)
			return i;
	return -1;
}

/* ENVS */

typedef intptr_t env_id;
typedef intptr_t stack_entry, env_entry;

static env_entry *resize_env_table(env_entry *table, intptr_t count) {
	intptr_t *new_table;
	new_table = realloc(table, (1 + count*2) * sizeof *table);
	if (!new_table) {
		if (table)
			free(table);
		fail("No memory to extend env table");
	}
	TABLE_COUNT(new_table) = count;
	return new_table;
}

static stack_entry *resize_env_stack(intptr_t *pstack, stack_entry *stack,
			intptr_t count) {
	stack_entry *new_stack;
	new_stack = realloc(stack, (1 + count) * sizeof *stack);
	if (!new_stack) {
		if (stack)
			free(stack);
		fail("No memory to extend env stack");
	}
	TABLE_COUNT(new_stack) = count;
	if (new_stack != stack)
		*pstack = (intptr_t) new_stack;
	return new_stack;
}

intptr_t _getenv(env_id env, env_entry *table) {
	int i;
	stack_entry *stack;

	if (!table)
		fail("Env not present (null context)");
	i = table_index(table, TABLE_COUNT(table), env);
	if (i == -1)
		fail("Env not present");
	stack = (stack_entry *) SLOT_VALUE(table, i);
	return stack[TABLE_COUNT(stack)];
}

int _haveenv(env_id env, env_entry *table) {
	return table && table_index(table, TABLE_COUNT(table), env) != -1;
}

env_entry *_pushenv(env_id env, env_entry *table, intptr_t val) {
	int i;
	intptr_t table_len, stack_len;
	stack_entry *stack;

	table_len = table ? TABLE_COUNT(table) : 0;
	i = table_index(table, table_len, env);
	if (i == -1) {
		i = table_len;
		table = resize_env_table(table, table_len+1);
		SLOT_KEY(table, i) = env;
		stack = NULL;
		stack_len = 1;
	}
	else {
		stack = (stack_entry *) SLOT_VALUE(table, i);
		stack_len = TABLE_COUNT(stack) + 1;
	}

	stack = resize_env_stack(&SLOT_VALUE(table, i), stack, stack_len);

	/* One-based due to length prefix */
	stack[stack_len] = val;

	return table;
}

env_entry *_popenv(env_id env, env_entry *table) {
	int i;
	intptr_t table_len, stack_len;
	stack_entry *stack;

	if (!table)
		fail("Empty env table?!");
	table_len = TABLE_COUNT(table);
	i = table_index(table, table_len, env);
	if (i == -1)
		fail("Env missing?!");

	stack = (stack_entry *) SLOT_VALUE(table, i);
	stack_len = TABLE_COUNT(stack) - 1;

	if (stack_len) {
		stack = resize_env_stack(&SLOT_VALUE(table, i), stack,
				stack_len);
	}
	else {
		SLOT_VALUE(table, i) = 0;
		free(stack);
		/* ought to remove this id from the env table altogether */
	}

	return table;
}

/* EXTRINSICS */

static intptr_t *resize_atom_table(struct nom_atom *atom, intptr_t* table,
                                   intptr_t count) {
	intptr_t *new_table;
	new_table = realloc(table, (1 + count*2) * sizeof *table);
	if (!new_table) {
		free(table);
		fail("No memory to extend extrinsic table");
	}
	if (new_table != table)
		atom->extrs = new_table;
	TABLE_COUNT(new_table) = count;
	return new_table;
}

void _addextrinsic(intptr_t extr, struct nom_atom *atom, intptr_t val) {
	intptr_t count, *table;

	table = atom->extrs;
	count = table ? TABLE_COUNT(table) : 0;

	if (table_index(table, count, extr) != -1)
		fail("Extrinsic already present");

	table = resize_atom_table(atom, table, count+1);
	SLOT_KEY(table, count) = extr;
	SLOT_VALUE(table, count) = val;
}

void _updateextrinsic(intptr_t extr, struct nom_atom *atom, intptr_t val) {
	int index;
	intptr_t *table;

	table = atom->extrs;
	if (!table)
		fail("Extrinsic not already present (empty table)");

	index = table_index(table, TABLE_COUNT(table), extr);
	if (index == -1)
		fail("Extrinsic not already present");

	SLOT_VALUE(table, index) = val;
}

intptr_t _getextrinsic(intptr_t extr, struct nom_atom *atom) {
	int index;
	intptr_t *table;

	table = atom->extrs;
	if (!table)
		fail("Extrinsic not found (empty table)");

	index = table_index(table, TABLE_COUNT(table), extr);
	if (index == -1)
		fail("Extrinsic not found");

	return SLOT_VALUE(table, index);
}

int _hasextrinsic(intptr_t extr, struct nom_atom *atom) {
	intptr_t *table;
	table = atom->extrs;
	if (!table)
		return 0;
	return table_index(table, TABLE_COUNT(table), extr) != -1;
}

/* GC */

#define GC_PUTS(s) do {} while (0)
#define GC_PUTCHAR(c) do {} while (0)
#define GC_PRINTF(...) do {} while (0)

struct frame_map {
	uint32_t num_roots, num_meta;
	/* const void *meta[0]; */
};

struct shadow_stack {
	struct shadow_stack *next;
	const struct frame_map *map;
	void *roots;
};

extern struct shadow_stack *llvm_gc_root_chain;

static void *heap[64];
static uint32_t heap_count = 0;

static void push_heap_ptr(void *ptr) {
	if (heap_count >= sizeof heap / sizeof *heap)
		fail("Out of GC heap entries"); /* pffft */
	heap[heap_count++] = ptr;
}

static void pop_heap_ptr(uint32_t i) {
	if (!heap_count)
		fail("Popping empty heap");
	if (i >= heap_count)
		fail("Bad GC heap pop");
	for (heap_count--; i < heap_count; i++)
		heap[i] = heap[i + 1];
}

static void visit_gc_root(void **root) {
	struct nom_atom *atom;
	uint8_t *c;
	int i;

	GC_PRINTF("   root %016lx ", (intptr_t) root);
	atom = *root;
	if (!atom) {
		GC_PUTS("is null");
		return;
	}
	GC_PRINTF("is 0x%016lx: ", (intptr_t) atom);

	c = (uint8_t *) atom;
	for (i = 0; i < 16; i++) {
		GC_PRINTF("%02x ", c[i]);
		if (i % 4 == 3)
			GC_PUTCHAR(' ');
	}
	GC_PUTCHAR('\n');

	atom->gc_flags = 0xaabbccdd;
}

void gc_collect(void) {
	struct shadow_stack *r;
	uint32_t i, n;
	void **roots;
	struct nom_atom *atom;

	GC_PUTS("=== marking...");
	for (r = llvm_gc_root_chain; r; r = r->next) {
		if (r->map->num_meta)
			fail("Unexpected meta entries in stack roots");
		GC_PRINTF(" stack frame %lx\n", (intptr_t) r);
		i = 0;
		n = r->map->num_roots;
		roots = (void **) &r->roots;
		for (i = 0; i < n; i++)
			visit_gc_root(&roots[i]);
	}

	GC_PUTS("=== sweeping...");
	/* heap_count may decrease due to pop_heap_ptr(); watch out! */
	for (i = 0; i < heap_count; i++) {
		atom = heap[i];
		GC_PRINTF(" 0x%016lx is ", (intptr_t) atom);
		if (atom->gc_flags == 0xaabbccdd) {
			atom->gc_flags = 0;
			GC_PUTS("live");
		}
		else {
			GC_PRINTF("dead. ");
			/* this heap entry will disappear, so decrement i */
			pop_heap_ptr(i--);
			free(atom);
			GC_PUTS("freed.");
		}
	}

	GC_PUTS("=== done collection.");
}

void *gc_alloc(size_t size) {
	void *p;

	gc_collect();
	p = malloc(size);
	if (!p)
		fail("OOM");
	push_heap_ptr(p);
	GC_PRINTF("Allocated 0x%016lx.\n", (intptr_t) p);
	return p;
}

/* TEMP */

void _print_str(const char *s) {
	fputs(s, stdout);
}
void _print_int(intptr_t n) {
	printf("%d", (int) n);
}
void _newline(void) {
	putchar('\n');
}
