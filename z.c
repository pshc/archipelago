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

__dead2 void match_fail() {
	fputs("Match failure.\n", stderr);
	exit(1);
}

static int table_index(intptr_t *table, intptr_t count, intptr_t key) {
	intptr_t i;
	for (i = 0; i < count; i++)
		if (SLOT_KEY(table, i) == key)
			return i;
	return -1;
}

/* ENVS */

static intptr_t *resize_env_table(intptr_t* table, intptr_t count) {
	intptr_t *new_table;
	new_table = realloc(table, (1 + count*2) * sizeof *table);
	if (!new_table) {
		free(table);
		fail("No memory to extend env table");
	}
	TABLE_COUNT(new_table) = count;
	return new_table;
}


intptr_t _getenv(intptr_t env, intptr_t *ctx) {
	intptr_t i;
	if (!ctx)
		fail("Env not present (null context)");
	i = table_index(ctx, TABLE_COUNT(ctx), env);
	if (i == -1)
		fail("Env not present");
	return SLOT_VALUE(ctx, i);
}

int _haveenv(intptr_t env, intptr_t *ctx) {
	return ctx && table_index(ctx, TABLE_COUNT(ctx), env) != -1;
}

intptr_t _pushenv(intptr_t env, intptr_t **pctx, intptr_t val) {
	intptr_t index, count, old, *ctx;
	ctx = *pctx;
	count = ctx ? TABLE_COUNT(ctx) : 0;
	index = table_index(ctx, count, env);
	if (index == -1) {
		index = count;
		ctx = *pctx = resize_env_table(ctx, count+1);
		SLOT_KEY(ctx, index) = env;
		old = 0;
	}
	else {
		old = SLOT_VALUE(ctx, index);
	}
	SLOT_VALUE(ctx, index) = val;
	return old;
}

void _popenv(intptr_t env, intptr_t *ctx, intptr_t oldVal) {
	intptr_t index;
	/* TODO: shrink table if stack empty (we don't even know currently) */
	if (!ctx)
		fail("Empty env table?!");
	index = table_index(ctx, TABLE_COUNT(ctx), env);
	if (index == -1)
		fail("Env missing?!");
	SLOT_VALUE(ctx, index) = oldVal;
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
	intptr_t index, *table;

	table = ATOM_TABLE(atom);
	if (!table)
		fail("Extrinsic not already present (empty table)");

	index = table_index(table, TABLE_COUNT(table), extr);
	if (index == -1)
		fail("Extrinsic not already present");

	SLOT_VALUE(table, index) = val;
}

intptr_t _getextrinsic(intptr_t extr, intptr_t **atom) {
	intptr_t index, *table;

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
