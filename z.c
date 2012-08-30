#include <stdio.h>
#include <stdlib.h>

#define ATOM_TABLE(atom) ((atom)[0])
#define TABLE_COUNT(table) ((table)[0])
#define SLOT_EXTR(table, index) ((table)[1 + (index)*2])
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

static int extrinsic_index(intptr_t *table, intptr_t count, intptr_t extr) {
	intptr_t i;
	for (i = 0; i < count; i++)
		if (SLOT_EXTR(table, i) == extr)
			return i;
	return -1;
}

static intptr_t *resize_atom_table(intptr_t **atom, intptr_t* table,
                                   intptr_t count) {
	intptr_t *new_table;
	new_table = realloc(table, (1 + count*2) * sizeof *table);
	if (!new_table)
		fail("No memory to extend extrinsic table");
	if (new_table != table)
		ATOM_TABLE(atom) = new_table;
	TABLE_COUNT(new_table) = count;
	return new_table;
}

void _addextrinsic(intptr_t extr, intptr_t **atom, intptr_t val) {
	intptr_t count, *table;

	table = ATOM_TABLE(atom);
	count = table ? TABLE_COUNT(table) : 0;

	if (extrinsic_index(table, count, extr) != -1)
		fail("Extrinsic already present");

	count++;
	table = resize_atom_table(atom, table, count);
	SLOT_EXTR(table, count-1) = extr;
	SLOT_VALUE(table, count-1) = val;
}

void _updateextrinsic(intptr_t extr, intptr_t **atom, intptr_t val) {
	intptr_t index, *table;

	table = ATOM_TABLE(atom);
	if (!table)
		fail("Extrinsic not already present (empty table)");

	index = extrinsic_index(table, TABLE_COUNT(table), extr);
	if (index == -1)
		fail("Extrinsic not already present");

	SLOT_VALUE(table, index) = val;
}

intptr_t _getextrinsic(intptr_t extr, intptr_t **atom) {
	intptr_t index, *table;

	table = ATOM_TABLE(atom);
	if (!table)
		fail("Extrinsic not found (empty table)");

	index = extrinsic_index(table, TABLE_COUNT(table), extr);
	if (index == -1)
		fail("Extrinsic not found");

	return SLOT_VALUE(table, index);
}

int _hasextrinsic(intptr_t extr, intptr_t **atom) {
	intptr_t *table;
	table = ATOM_TABLE(atom);
	if (!table)
		return 0;
	return extrinsic_index(table, TABLE_COUNT(table), extr) != -1;
}

void _print_str(const char *s) {
	fputs(s, stdout);
}
void _print_int(intptr_t n) {
	printf("%d", (int) n);
}
void _newline(void) {
	putchar('\n');
}
