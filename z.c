#include <stdio.h>
#include <stdlib.h>

#define ATOM_TABLE(atom) ((atom)[0])
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
		free(table);
		fail("No memory to extend env table");
	}
	TABLE_COUNT(new_table) = count;
	return new_table;
}

static stack_entry *resize_env_stack(stack_entry *stack, intptr_t count) {
	stack_entry *new_stack;
	new_stack = realloc(stack, (1 + count) * sizeof *stack);
	if (!new_stack) {
		free(stack);
		fail("No memory to extend env stack");
	}
	TABLE_COUNT(new_stack) = count;
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
	stack_entry *stack, *new_stack;

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

	new_stack = resize_env_stack(stack, stack_len);
	/* TODO: move this thing into the resize_env_stack helper */
	if (new_stack != stack) {
		SLOT_VALUE(table, i) = (intptr_t) new_stack;
		stack = new_stack;
	}

	/* One-based due to length prefix */
	stack[stack_len] = val;

	return table;
}

env_entry *_popenv(env_id env, env_entry *table) {
	int i;
	intptr_t table_len, stack_len;
	stack_entry *stack, *new_stack;

	if (!table)
		fail("Empty env table?!");
	table_len = TABLE_COUNT(table);
	i = table_index(table, table_len, env);
	if (i == -1)
		fail("Env missing?!");

	stack = (stack_entry *) SLOT_VALUE(table, i);
	stack_len = TABLE_COUNT(stack) - 1;

	if (stack_len) {
		new_stack = resize_env_stack(stack, stack_len);
		if (new_stack != stack)
			SLOT_VALUE(table, i) = (intptr_t) new_stack;
	}
	else {
		SLOT_VALUE(table, i) = 0;
		free(stack);
		/* ought to remove this id from the env table altogether */
	}

	return table;
}

/* EXTRINSICS */

static intptr_t *resize_atom_table(intptr_t **atom, intptr_t* table,
                                   intptr_t count) {
	intptr_t *new_table;
	new_table = realloc(table, (1 + count*2) * sizeof *table);
	if (!new_table) {
		free(table);
		fail("No memory to extend extrinsic table");
	}
	if (new_table != table)
		ATOM_TABLE(atom) = new_table;
	TABLE_COUNT(new_table) = count;
	return new_table;
}

void _addextrinsic(intptr_t extr, intptr_t **atom, intptr_t val) {
	intptr_t count, *table;

	table = ATOM_TABLE(atom);
	count = table ? TABLE_COUNT(table) : 0;

	if (table_index(table, count, extr) != -1)
		fail("Extrinsic already present");

	table = resize_atom_table(atom, table, count+1);
	SLOT_KEY(table, count) = extr;
	SLOT_VALUE(table, count) = val;
}

void _updateextrinsic(intptr_t extr, intptr_t **atom, intptr_t val) {
	int index;
	intptr_t *table;

	table = ATOM_TABLE(atom);
	if (!table)
		fail("Extrinsic not already present (empty table)");

	index = table_index(table, TABLE_COUNT(table), extr);
	if (index == -1)
		fail("Extrinsic not already present");

	SLOT_VALUE(table, index) = val;
}

intptr_t _getextrinsic(intptr_t extr, intptr_t **atom) {
	int index;
	intptr_t *table;

	table = ATOM_TABLE(atom);
	if (!table)
		fail("Extrinsic not found (empty table)");

	index = table_index(table, TABLE_COUNT(table), extr);
	if (index == -1)
		fail("Extrinsic not found");

	return SLOT_VALUE(table, index);
}

int _hasextrinsic(intptr_t extr, intptr_t **atom) {
	intptr_t *table;
	table = ATOM_TABLE(atom);
	if (!table)
		return 0;
	return table_index(table, TABLE_COUNT(table), extr) != -1;
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
