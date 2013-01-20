#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

struct nom_atom {
	uintptr_t gc;
	uintptr_t *extrs;
	uint32_t discrim;
};

#define TABLE_COUNT(table) ((table)[0])
#define SLOT_KEY(table, index) ((table)[1 + (index)*2])
#define SLOT_VALUE(table, index) ((table)[2 + (index)*2])

__dead2 void fail(const char *);
__dead2 void oom(void);
static ssize_t table_index(uintptr_t *table, uintptr_t count, uintptr_t key);

/* ENVS */

typedef uintptr_t env_id;
typedef uintptr_t stack_entry, env_entry;

static env_entry *resize_env_table(env_entry *table, uintptr_t count) {
	uintptr_t *new_table = realloc(table, (1 + count*2) * sizeof *table);
	if (!new_table) {
		if (table)
			free(table);
		oom();
	}
	TABLE_COUNT(new_table) = count;
	return new_table;
}

static stack_entry *resize_env_stack(uintptr_t *pstack, stack_entry *stack,
			uintptr_t count) {
	stack_entry *new_stack = realloc(stack, (1 + count) * sizeof *stack);
	if (!new_stack) {
		if (stack)
			free(stack);
		oom();
	}
	TABLE_COUNT(new_stack) = count;
	if (new_stack != stack)
		*pstack = (uintptr_t) new_stack;
	return new_stack;
}

uintptr_t _getenv(env_id env, env_entry *table) {
	if (!table)
		fail("Env not present (null context)");
	ssize_t i = table_index(table, TABLE_COUNT(table), env);
	if (i == -1)
		fail("Env not present");
	stack_entry *stack = (stack_entry *) SLOT_VALUE(table, i);
	return stack[TABLE_COUNT(stack)];
}

int _haveenv(env_id env, env_entry *table) {
	return table && table_index(table, TABLE_COUNT(table), env) != -1;
}

env_entry *_pushenv(env_id env, env_entry *table, uintptr_t val) {
	stack_entry *stack = NULL;
	uintptr_t stack_len = 1;

	uintptr_t table_len = table ? TABLE_COUNT(table) : 0;
	ssize_t i = table_index(table, table_len, env);
	if (i == -1) {
		i = (ssize_t) table_len;
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
	ssize_t i = table_index(table, TABLE_COUNT(table), env);
	if (i == -1)
		fail("Env missing?!");

	stack_entry *stack = (stack_entry *) SLOT_VALUE(table, i);
	uintptr_t stack_len = TABLE_COUNT(stack) - 1;

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

static uintptr_t *resize_atom_table(struct nom_atom *atom, uintptr_t* table,
			uintptr_t count) {
	uintptr_t *new_table = realloc(table, (1 + count*2) * sizeof *table);
	if (!new_table) {
		free(table);
		oom();
	}
	if (new_table != table)
		atom->extrs = new_table;
	TABLE_COUNT(new_table) = count;
	return new_table;
}

void _addextrinsic(uintptr_t extr, struct nom_atom *atom, uintptr_t val) {
	uintptr_t *table = atom->extrs;
	uintptr_t count = table ? TABLE_COUNT(table) : 0;

	if (table_index(table, count, extr) != -1)
		fail("Extrinsic already present");

	table = resize_atom_table(atom, table, count+1);
	SLOT_KEY(table, count) = extr;
	SLOT_VALUE(table, count) = val;
}

void _updateextrinsic(uintptr_t extr, struct nom_atom *atom, uintptr_t val) {
	uintptr_t *table = atom->extrs;
	if (!table)
		fail("Extrinsic not already present (empty table)");

	ssize_t index = table_index(table, TABLE_COUNT(table), extr);
	if (index == -1)
		fail("Extrinsic not already present");

	SLOT_VALUE(table, index) = val;
}

uintptr_t _getextrinsic(uintptr_t extr, struct nom_atom *atom) {
	uintptr_t *table = atom->extrs;
	if (!table)
		fail("Extrinsic not found (empty table)");

	ssize_t index = table_index(table, TABLE_COUNT(table), extr);
	if (index == -1)
		fail("Extrinsic not found");

	return SLOT_VALUE(table, index);
}

int _hasextrinsic(uintptr_t extr, struct nom_atom *atom) {
	uintptr_t *table = atom->extrs;
	if (!table)
		return 0;
	return table_index(table, TABLE_COUNT(table), extr) != -1;
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

__dead2 void oom(void) {
	fputs("OOM.\n", stderr);
	exit(1);
}

/* HELPERS */

static ssize_t table_index(uintptr_t *table, uintptr_t count, uintptr_t key) {
	if (count > 20)
		fail("Suspiciously large env/extr table");
	for (uintptr_t i = 0; i < count; i++)
		if (SLOT_KEY(table, i) == key)
			return (ssize_t) i;
	return -1;
}

/* TEMP */

void _print_str(const char *s) {
	fputs(s, stdout);
}
void _print_int(int32_t n) {
	printf("%d", (int) n);
}
void _newline(void) {
	putchar('\n');
}
