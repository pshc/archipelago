#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include "serial.h"
#include "util.h"

struct adt *AST, *Var;
struct map *loaded_modules;

static char *base_dir = NULL;
static FILE *f = NULL;

static void *read_node(type_t type);

type_t intT(void) {
	type_t type = malloc(sizeof *type);
	type->kind = KIND_INT;
	type->adt = NULL;
	return type;
}

type_t adtT(struct adt *adt) {
	type_t type = malloc(sizeof *type);
	type->kind = KIND_ADT;
	type->adt = adt;
	return type;
}

type_t weak(type_t t) {
	type_t wrapper = malloc(sizeof *wrapper);
	wrapper->kind = KIND_WEAK;
	wrapper->ref = t;
	return wrapper;
}

struct ctor *Ctor(char *name, size_t field_count, ...) {
	struct ctor *ctor;
	va_list field_list;
	struct field *field, **fields;
	size_t i;
	fields = malloc(field_count * sizeof fields);
	va_start(field_list, field_count);
	for (i = 0; i < field_count; i++) {
		field = malloc(sizeof(struct field));
		field->name = va_arg(field_list, char *);
		field->type = va_arg(field_list, type_t);
		fields[i] = field;
	}
	va_end(field_list);
	ctor = malloc(sizeof *ctor);
	ctor->name = name;
	ctor->field_count = field_count;
	ctor->fields = fields;
	return ctor;
}

struct adt *ADT(char *name) {
	struct adt *adt = malloc(sizeof *adt);
	adt->name = name;
	adt->ctor_count = 0;
	adt->ctors = NULL;
	return adt;
}

void ADT_ctors(struct adt *adt, size_t ctor_count, ...) {
	va_list ctor_list;
	struct ctor **ctors;
	size_t i;
	CHECK(adt->ctors == NULL, "ADT %s already has ctors", adt->name);
	ctors = malloc(ctor_count * sizeof ctors);
	va_start(ctor_list, ctor_count);
	for (i = 0; i < ctor_count; i++)
		ctors[i] = va_arg(ctor_list, struct ctor *);
	va_end(ctor_list);
	adt->ctor_count = ctor_count;
	adt->ctors = ctors;
}

void setup_serial(const char *dir) {
	Var = ADT("Var");
	ADT_ctors(Var, 1,
		Ctor("Var", 0)
	);
	AST = ADT("AST");
	ADT_ctors(AST, 5,
		Ctor("Num", 1, "int", intT()),
		Ctor("Bind", 1, "var", weak(adtT(Var))),
		Ctor("Plus", 2, "a", adtT(AST), "b", adtT(AST)),
		Ctor("Lam", 2, "param", adtT(Var), "expr", adtT(AST)),
		Ctor("App", 2, "func", adtT(AST), "arg", adtT(AST))
	);

	base_dir = strdup(dir);
	loaded_modules = new_map(&strcmp);
}

static int read_char() {
	int c = fgetc(f);
	if (c == EOF) {
		perror("fgetc");
		exit(EXIT_FAILURE);
	}
	return c;
}

static int read_int() {
	int a = read_char(), b, c, d;
	if (a <= 0x7f)
		return a;
	CHECK(a > 0xbf, "Invalid extension char");
	b = read_char() & 0x3f;
	if (a <= 0xdf) {
		a &= 0x1f;
		a = (a << 6) | b;
		CHECK(a > 0x7f, "Two-byte literal underflow");
		return a;
	}
	c = read_char() & 0x3f;
	if (a <= 0xef) {
		a &= 0x0f;
		a = (a << 12) | (b << 6) | c;
		CHECK(a > 0x7ff, "Three-byte literal underflow");
		return a;
	}
	CHECK(a <= 0xf7, "TODO");
	a &= 0x07;
	d = read_char() & 0x3f;
	a = (a << 18) | (b << 12) | (c << 6) | d;
	CHECK(a > 0xffff, "Four-byte literal underflow");
	return a;
}

static char *read_str() {
	int len = read_int();
	char *str = malloc(len+1);
	size_t count = fread(str, len, 1, f);
	CHECK(count == 1, "String overflow");
	str[len] = '\0';
	return str;
}

static void *read_adt(struct adt *adt) {
	struct ctor *ctor;
	intptr_t *dest, *inst;
	size_t field_count, i;
	int ix;
	struct field **src;

	ix = read_int();
	CHECK(ix < adt->ctor_count, "ADT %s index overflow (%d>%d)", adt->name, ix, (int) adt->ctor_count);
	ctor = adt->ctors[ix];
	field_count = ctor->field_count;

	inst = malloc((field_count+1) * sizeof(intptr_t));
	inst[0] = ix;
	src = ctor->fields;
	dest = inst + 1;
	for (i = 0; i < field_count; i++)
		*dest++ = (intptr_t) read_node((*src++)->type);
	return inst;
}

static void *read_weak(type_t type) {
	size_t atom_ix, mod_ix;
	mod_ix = read_int();
	atom_ix = read_int();
	return NULL;
}

static void *read_node(type_t type) {
	switch (type->kind) {
		case KIND_INT:
			return (void *)(intptr_t)read_int();

		case KIND_STR:
			return read_str();

		case KIND_ADT:
			return read_adt(type->adt);

		case KIND_WEAK:
			return read_weak(type->ref);
	}
	fail("Bad kind %d", type->kind);
}

char *module_hash_by_name(const char *name) {
	char *full = alloca(strlen(base_dir) + strlen(name) + 6);
	strcpy(full, base_dir);
	strcat(full, "mods/");
	strcat(full, name);
	char *hash = malloc(65);
	ssize_t read = readlink(full, hash, 64);
	if (read < 0) {
		perror(full);
		fail("Couldn't find hash for module '%s'.", name);
	}
	hash[read] = '\0';
	CHECK(read == 64, "Bad hash: %s", hash);
	return hash;
}

struct module *load_module(const char *hash, type_t root_type) {
	char *full;
	int dep_count, i;
	char dep[64];
	size_t count;
	void *root;
	struct module *module;
	FILE *saved;

	if (map_has(loaded_modules, hash))
		return map_get(loaded_modules, hash);

 	full = alloca(strlen(base_dir) + strlen(hash) + 6);
	strcpy(full, base_dir);
	strcat(full, "mods/");
	strcat(full, hash);
	f = fopen(full, "rb");
	if (!f)
		error_out(full);

	dep_count = read_int();
	printf("%s has %d dep(s).\n", hash, dep_count);

	/* Loading deps will change f. Preserve it. */
	saved = f;
	for (i = 0; i < dep_count; i++) {
		count = fread(dep, sizeof dep, 1, saved);
		if (!count)
			error_out(full);
		/* TODO: Where do we get the dep root type? */
		load_module(dep, root_type);
	}

	f = saved;
	root = read_node(root_type);

	CHECK(fgetc(f) == EOF && feof(f), "Trailing data");
	fclose(f);
	f = NULL;

	module = malloc(sizeof *module);
	module->root_type = root_type;
	module->root = root;
	map_set(loaded_modules, strdup(hash), module);

	return module;
}

#ifdef STANDALONE
int main(void) {
	setup_serial("");

	char *hash = module_hash_by_name("test");
	load_module(hash, adtT(AST));

	CHECK(map_has(loaded_modules, hash), "Not loaded?");
	CHECK(!map_has(loaded_modules, "fgsfds"), "Bogus hash");

	free(hash);

	return 0;
}
#endif /* STANDALONE */
