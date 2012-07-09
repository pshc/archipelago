#include <stdio.h>
#include <stdlib.h>

__dead2 void fail(const char *err) {
	fputs(err, stderr);
	fputc('\n', stderr);
	exit(1);
}

void _addextrinsic(intptr_t extr, intptr_t **atom, intptr_t val) {
	intptr_t *table, *new_table;
	intptr_t i, count, table_size;

	table = atom[0];
	count = table ? table[0] : 0;

	/* Check that it isn't already in the list */
	for (i = 0; i < count; i++)
		if (table[1 + i*2] == extr)
			fail("Extrinsic already present");

	/* Append this extrinsic/value pair */
	count++;
	table_size = 1 + count*2;
	new_table = realloc(table, table_size * sizeof *table);
	if (!new_table)
		fail("No memory to extend extrinsic table");
	if (new_table != table)
		atom[0] = new_table;
	new_table[0] = count;
	new_table[table_size-2] = extr;
	new_table[table_size-1] = val;
}

intptr_t _getextrinsic(intptr_t extr, intptr_t **atom) {
	intptr_t *table;
	intptr_t i, count;

	table = atom[0];
	if (!table)
		fail("Extrinsic not found (empty table)");

	count = table[0];
	for (i = 0; i < count; i++)
		if (table[1 + i*2] == extr)
			return table[2 + i*2];
	fail("Extrinsic not found");
}
