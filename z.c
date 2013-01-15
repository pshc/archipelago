#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

struct nom_atom {
	intptr_t gc;
	intptr_t *extrs;
	uint32_t discrim;
};

#define TABLE_COUNT(table) ((table)[0])
#define SLOT_KEY(table, index) ((table)[1 + (index)*2])
#define SLOT_VALUE(table, index) ((table)[2 + (index)*2])

#define GC_MARK ((intptr_t) 1)

__dead2 void fail(const char *);
static __dead2 void oom(void);
static int table_index(intptr_t *table, intptr_t count, intptr_t key);

/* ENVS */

typedef intptr_t env_id;
typedef intptr_t stack_entry, env_entry;

static env_entry *resize_env_table(env_entry *table, intptr_t count) {
	intptr_t *new_table = realloc(table, (1 + count*2) * sizeof *table);
	if (!new_table) {
		if (table)
			free(table);
		oom();
	}
	TABLE_COUNT(new_table) = count;
	return new_table;
}

static stack_entry *resize_env_stack(intptr_t *pstack, stack_entry *stack,
			intptr_t count) {
	stack_entry *new_stack = realloc(stack, (1 + count) * sizeof *stack);
	if (!new_stack) {
		if (stack)
			free(stack);
		oom();
	}
	TABLE_COUNT(new_stack) = count;
	if (new_stack != stack)
		*pstack = (intptr_t) new_stack;
	return new_stack;
}

intptr_t _getenv(env_id env, env_entry *table) {
	if (!table)
		fail("Env not present (null context)");
	int i = table_index(table, TABLE_COUNT(table), env);
	if (i == -1)
		fail("Env not present");
	stack_entry *stack = (stack_entry *) SLOT_VALUE(table, i);
	return stack[TABLE_COUNT(stack)];
}

int _haveenv(env_id env, env_entry *table) {
	return table && table_index(table, TABLE_COUNT(table), env) != -1;
}

env_entry *_pushenv(env_id env, env_entry *table, intptr_t val) {
	stack_entry *stack = NULL;
	intptr_t stack_len = 1;

	intptr_t table_len = table ? TABLE_COUNT(table) : 0;
	int i = table_index(table, table_len, env);
	if (i == -1) {
		i = table_len;
		table = resize_env_table(table, table_len+1);
		SLOT_KEY(table, i) = env;
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
	if (!table)
		fail("Empty env table?!");
	intptr_t table_len = TABLE_COUNT(table);
	int i = table_index(table, table_len, env);
	if (i == -1)
		fail("Env missing?!");

	stack_entry *stack = (stack_entry *) SLOT_VALUE(table, i);
	intptr_t stack_len = TABLE_COUNT(stack) - 1;

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
	intptr_t *new_table = realloc(table, (1 + count*2) * sizeof *table);
	if (!new_table) {
		free(table);
		oom();
	}
	if (new_table != table)
		atom->extrs = new_table;
	TABLE_COUNT(new_table) = count;
	return new_table;
}

void _addextrinsic(intptr_t extr, struct nom_atom *atom, intptr_t val) {
	intptr_t *table = atom->extrs;
	intptr_t count = table ? TABLE_COUNT(table) : 0;

	if (table_index(table, count, extr) != -1)
		fail("Extrinsic already present");

	table = resize_atom_table(atom, table, count+1);
	SLOT_KEY(table, count) = extr;
	SLOT_VALUE(table, count) = val;
}

void _updateextrinsic(intptr_t extr, struct nom_atom *atom, intptr_t val) {
	intptr_t *table = atom->extrs;
	if (!table)
		fail("Extrinsic not already present (empty table)");

	int index = table_index(table, TABLE_COUNT(table), extr);
	if (index == -1)
		fail("Extrinsic not already present");

	SLOT_VALUE(table, index) = val;
}

intptr_t _getextrinsic(intptr_t extr, struct nom_atom *atom) {
	intptr_t *table = atom->extrs;
	if (!table)
		fail("Extrinsic not found (empty table)");

	int index = table_index(table, TABLE_COUNT(table), extr);
	if (index == -1)
		fail("Extrinsic not found");

	return SLOT_VALUE(table, index);
}

int _hasextrinsic(intptr_t extr, struct nom_atom *atom) {
	intptr_t *table = atom->extrs;
	if (!table)
		return 0;
	return table_index(table, TABLE_COUNT(table), extr) != -1;
}

/* GC */

#ifdef LOGGC
# define GC_PUTS(s) puts(s)
# define GC_PUTCHAR(c) putchar(c)
# define GC_PRINTF(...) printf(__VA_ARGS__)
#else
# define GC_PUTS(s) do {} while (0)
# define GC_PUTCHAR(c) do {} while (0)
# define GC_PRINTF(...) do {} while (0)
#endif

struct frame_map {
	uint32_t num_roots, num_meta;
	const void *meta[1]; /* variable-length really */
};

struct shadow_stack {
	struct shadow_stack *next;
	const struct frame_map *map;
	void *roots;
};

extern struct shadow_stack *llvm_gc_root_chain;

static void *heap[64] = {0};
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
	heap_count--;
	/* move last heap entry into this now-vacant slot */
	heap[i] = heap[heap_count];
	heap[heap_count] = NULL;
}

union packed_ptr {
	char *bytes[sizeof(intptr_t)];
	void *ptr;
};

static void mark_gc_atom(struct nom_atom *);

#ifdef LOGGC
static const char *read_gc_spec_name(const uint8_t *spec, unsigned int n) {
	const uint8_t *name = spec + n * (1 + sizeof(intptr_t));
	for (unsigned int i = 0; name[i]; i++) {
		if (name[i] < '0' || name[i] > 'z')
			fail("Suspicious unusual ctor name char");
		if (i > 30)
			fail("Ctor name is suspiciously long");
	}
	return (const char *) name;
}
#endif /* LOGGC */

static void read_atom_spec(struct nom_atom *atom, const uint8_t *spec) {
	GC_PRINTF("    spec at %016lx ", (intptr_t) spec);
	unsigned int n = *spec++;
	if (!n)
		return;
	if (n > 20)
		fail("Suspicious field count");

	/* ctor name at end */
	GC_PRINTF("is a %s.\n", read_gc_spec_name(spec, n));

	for (unsigned int i = 0; i < n; i++) {
		unsigned int offset = *spec++;

		/* unaligned load */
		union packed_ptr tbl_ptr;
		memcpy(tbl_ptr.bytes, spec, sizeof tbl_ptr.bytes);
		intptr_t *tbl = *(intptr_t **) tbl_ptr.ptr;
		spec += sizeof tbl;

		/* TODO: use tbl to typecheck */

		/* recurse into atom pointed by field */
		struct nom_atom *ref_atom = *(struct nom_atom **)
				((char *)atom + offset);

		GC_PRINTF("     field at %d points to atom %016lx\n", offset,
				(intptr_t) ref_atom);

		if (ref_atom)
			mark_gc_atom(ref_atom);
	}
}

static void visit_gc_root(void **root, const void *metadata) {
	(void) metadata;

	GC_PRINTF("   root %016lx ", (intptr_t) root);
	struct nom_atom *atom = *root;
	if (!atom) {
		GC_PUTS("is null");
		return;
	}
	GC_PRINTF("is 0x%016lx: ", (intptr_t) atom);

	mark_gc_atom(atom);
}

static void mark_gc_atom(struct nom_atom *atom) {
	if (atom->gc & GC_MARK) {
		GC_PUTS("(already marked)");
		return;
	}

	GC_PRINTF("   ");
	for (int i = 0; i < 16; i++) {
		GC_PRINTF("%02x ", ((uint8_t *) atom)[i]);
		if (i % 4 == 3)
			GC_PUTCHAR(' ');
	}
	GC_PUTCHAR('\n');

	intptr_t spec = atom->gc;
	/* mark before recursing into fields */
	atom->gc |= GC_MARK;

	if (spec)
		read_atom_spec(atom, (const uint8_t *) spec);
}

void gc_collect(void) {
	GC_PUTS("=== marking...");
	for (struct shadow_stack *r = llvm_gc_root_chain; r; r = r->next) {
		GC_PRINTF(" stack frame %lx\n", (intptr_t) r);
		uint32_t i = 0;
		/* first, roots with metadata */
		void **roots = (void **) &r->roots;
		for (uint32_t n = r->map->num_meta; i < n; i++)
			visit_gc_root(&roots[i], r->map->meta[i]);
		/* then roots without */
		for (uint32_t n = r->map->num_roots; i < n; i++)
			visit_gc_root(&roots[i], NULL);
	}

	GC_PUTS("=== sweeping...");
	/* heap_count may decrease due to pop_heap_ptr(); watch out! */
	for (unsigned int i = 0; i < heap_count; i++) {
		struct nom_atom *atom = heap[i];
		GC_PRINTF(" 0x%016lx is ", (intptr_t) atom);
		if (atom->gc & GC_MARK) {
			atom->gc &= ~GC_MARK;
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
	gc_collect();
	void *p = malloc(size);
	if (!p)
		oom();
	push_heap_ptr(p);
	GC_PRINTF("Allocated 0x%016lx.\n", (intptr_t) p);
	return p;
}

/* ERROR HANDLING */

__dead2 void fail(const char *err) {
	fputs(err, stderr);
	fputc('\n', stderr);
	exit(1);
}

__dead2 void match_fail(void) {
	fputs("Match failure.\n", stderr);
	exit(1);
}

static __dead2 void oom(void) {
	fputs("OOM.\n", stderr);
	exit(1);
}

/* HELPERS */

static int table_index(intptr_t *table, intptr_t count, intptr_t key) {
	for (int i = 0; i < count; i++)
		if (SLOT_KEY(table, i) == key)
			return i;
	return -1;
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
