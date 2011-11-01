#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include "serial.h"
#include "util.h"

struct adt *Type, *TypeVar, *FieldForm, *CtorForm, *DtForm, *DtList;
struct map *loaded_modules;

static char *base_dir = NULL;
static char *mod_dir = "../mods/";

/* Deserialization context */
static FILE *f = NULL;
static intptr_t node_ctr;
static struct map *own_map, *forward_refs;
static intptr_t *cur_field;

static void *read_node(type_t type);
static void destroy_module(struct module *);

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

type_t arrayT(type_t elem) {
	type_t type = malloc(sizeof *type);
	type->kind = KIND_ARRAY;
	type->ref = elem;
	return type;
}

type_t weak(type_t t) {
	type_t wrapper = malloc(sizeof *wrapper);
	wrapper->kind = KIND_WEAK;
	wrapper->ref = t;
	return wrapper;
}

type_t copy_type(type_t t) {
	type_t copy = malloc(sizeof *t);
	memcpy(copy, t, sizeof *t);
	return copy;
}

void destroy_type(type_t t) {
	switch (t->kind) {
		case KIND_INT:
		case KIND_STR:
		case KIND_ADT:
			break;
		case KIND_ARRAY:
		case KIND_WEAK:
			destroy_type(t->ref);
			break;
	}
	free(t);
}

struct ctor *Ctor(const char *name, size_t field_count, ...) {
	struct ctor *ctor;
	va_list field_list;
	struct field *field, **fields;
	size_t i;
	fields = malloc(field_count * sizeof fields);
	va_start(field_list, field_count);
	for (i = 0; i < field_count; i++) {
		field = malloc(sizeof(struct field));
		field->name = strdup(va_arg(field_list, char *));
		/* Take ownership of the types */
		field->type = va_arg(field_list, type_t);
		fields[i] = field;
	}
	va_end(field_list);
	ctor = malloc(sizeof *ctor);
	ctor->name = strdup(name);
	ctor->field_count = field_count;
	ctor->fields = fields;
	return ctor;
}

static void destroy_ctor(struct ctor *ctor) {
	size_t i, count;
	struct field *field;
	for (i = 0, count = ctor->field_count; i < count; i++) {
		field = ctor->fields[i];
		free(field->name);
		destroy_type(field->type);
		free(field);
	}
	free(ctor->fields);
	free(ctor->name);
	free(ctor);
}

struct adt *ADT(const char *name) {
	struct adt *adt = malloc(sizeof *adt);
	adt->name = strdup(name);
	adt->ctor_count = 0;
	adt->ctors = NULL;
	return adt;
}

void ADT_ctors(struct adt *adt, size_t ctor_count, ...) {
	va_list ctor_list;
	struct ctor **ctors;
	size_t i;
	CHECK(adt->ctors == NULL, "ADT %s already has ctors", adt->name);
	CHECK(ctor_count > 0, "No phantom types");
	va_start(ctor_list, ctor_count);
	if (ctor_count) {
		ctors = malloc(ctor_count * sizeof ctors);
		for (i = 0; i < ctor_count; i++)
			ctors[i] = va_arg(ctor_list, struct ctor *);
		adt->ctors = ctors;
	}
	va_end(ctor_list);
	adt->ctor_count = ctor_count;
}

static void destroy_ADT(struct adt *adt) {
	size_t i, count;
	for (i = 0, count = adt->ctor_count; i < count; i++)
		destroy_ctor(adt->ctors[i]);
	free(adt->ctors);
	free(adt->name);
	free(adt);
}

void setup_serial(const char *dir) {
	Type = ADT("Type");
	TypeVar = ADT("TypeVar");
	ADT_ctors(TypeVar, 1, Ctor("TypeVar", 0));
	FieldForm = ADT("FieldForm");
	ADT_ctors(FieldForm, 1, Ctor("FieldForm", 1,
		"type", adtT(Type)));
	CtorForm = ADT("CtorForm");
	ADT_ctors(CtorForm, 1, Ctor("CtorForm", 1,
		"fields", arrayT(adtT(FieldForm))));
	DtForm = ADT("DtForm");
	ADT_ctors(DtForm, 1, Ctor("DtForm", 2,
		"ctors", arrayT(adtT(CtorForm)),
		"tvars", arrayT(adtT(TypeVar))));
	ADT_ctors(Type, 13,
		Ctor("TVar", 1, "typeVar", weak(adtT(TypeVar))),
		Ctor("TMeta", 0), /* XXX */
		Ctor("TInt", 0),
		Ctor("TStr", 0),
		Ctor("TChar", 0),
		Ctor("TBool", 0),
		Ctor("TVoid", 0),
		Ctor("TTuple", 1, "tupleTypes", arrayT(adtT(Type))),
		Ctor("TAnyTuple", 0),
		Ctor("TFunc", 2, "funcArgs", arrayT(adtT(Type)),
				"funcRet", adtT(Type)),
		Ctor("TData", 1, "data", weak(adtT(DtForm))),
		Ctor("TApply", 2, "appType", adtT(Type),
				"appVars", arrayT(adtT(Type))),
		Ctor("TWeak", 1, "refType", adtT(Type)));
	DtList = ADT("DtList");
	ADT_ctors(DtList, 1, Ctor("DtList", 1, "dts", arrayT(adtT(DtForm))));

	base_dir = strdup(dir);
	loaded_modules = new_map(&strcmp, &free, &destroy_module);
}

void cleanup_serial(void) {
	destroy_map(loaded_modules);
	free(base_dir);
	destroy_ADT(Type);
	destroy_ADT(TypeVar);
	destroy_ADT(FieldForm);
	destroy_ADT(CtorForm);
	destroy_ADT(DtForm);
	destroy_ADT(DtList);
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

static struct array *read_array(type_t elem_type) {
	int i, len;
	len = read_int();
	struct array *array = malloc(sizeof array->len
			+ sizeof array->elems[0] * len);
	array->len = (size_t) len;
	for (i = 0; i < len; i++)
		array->elems[i] = read_node(elem_type);
	return array;
}

static void *read_adt(struct adt *adt) {
	struct ctor *ctor;
	intptr_t *dest, *inst;
	size_t field_count, i;
	int ix;
	struct field **src;

	if (adt->ctor_count > 1) {
		ix = read_int();
		CHECK(ix < adt->ctor_count, "ADT %s index overflow (%d>%d)", adt->name, ix, (int) adt->ctor_count);
	}
	else {
		CHECK(adt->ctor_count == 1, "Phantom type?!");
		ix = 0;
	}
	ctor = adt->ctors[ix];
	field_count = ctor->field_count;

	inst = malloc((field_count+1) * sizeof(intptr_t));
	inst[0] = ix;
	src = ctor->fields;
	dest = inst + 1;
	for (i = 0; i < field_count; i++) {
		/* Provide context for forward refs */
		cur_field = dest;

		*dest++ = (intptr_t) read_node((*src++)->type);
	}
	return inst;
}

static void *read_weak(type_t type) {
	size_t atom_ix, mod_ix;
	void *dest = NULL;
	void *key;
	struct list *refs;
	mod_ix = read_int();
	atom_ix = read_int();
	if (mod_ix == 0) {
		/* XXX: Should be able to get a cheaper check for this? */
		if (map_has(own_map, (void *) atom_ix)) {
			dest = map_get(own_map, (void *) atom_ix);
		}
		else {
			key = (void *) atom_ix;
			if (map_has(forward_refs, key))
				refs = map_get(forward_refs, key);
			else
				refs = nope();
			refs = cons(cur_field, refs);
			map_set(forward_refs, key, refs);
			dest = (void *) 0xaaaaaaaa;
		}
	}
	else {
		/* TODO */
	}
	return dest;
}

static void *read_node(type_t type) {
	intptr_t ix;
	void *node;
	switch (type->kind) {
		case KIND_INT:
			return (void *)(intptr_t)read_int();

		case KIND_STR:
			return read_str();

		case KIND_ARRAY:
			return read_array(type->ref);

		case KIND_ADT:
			ix = node_ctr++;
			node = read_adt(type->adt);
			map_set(own_map, (void *) ix, node);
			return node;

		case KIND_WEAK:
			return read_weak(type->ref);
	}
	fail("Bad kind %d", type->kind);
}

char *module_hash_by_name(const char *name) {
	char *full = alloca(strlen(base_dir) + strlen(mod_dir) + strlen(name));
	strcpy(full, base_dir);
	strcat(full, mod_dir);
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

static void resolve_forward_refs(void *ix, struct list *refs) {
	intptr_t dest, *field;
	dest = (intptr_t) map_get(own_map, ix);
	for (; IS_CONS(refs); refs = refs->next) {
		field = refs->val;
		*field = dest;
	}
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

	full = alloca(strlen(base_dir) + strlen(mod_dir) + strlen(hash));
	strcpy(full, base_dir);
	strcat(full, mod_dir);
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
	node_ctr = 0;
	cur_field = NULL;
	own_map = new_map(NULL, NULL, NULL);
	forward_refs = new_map(NULL, NULL, &free_list);
	root = read_node(root_type);

	map_foreach(forward_refs, (map_foreach_f) &resolve_forward_refs);
	destroy_map(forward_refs);
	destroy_map(own_map);

	CHECK(fgetc(f) == EOF && feof(f), "Trailing data");
	fclose(f);
	f = NULL;

	module = malloc(sizeof *module);
	module->root_type = copy_type(root_type);
	module->root = root;
	map_set(loaded_modules, strdup(hash), module);

	return module;
}

static void free_str(char *str) {
	free(str);
}
static void free_array(struct array *array) {
	free(array);
}
static void free_obj(intptr_t *obj) {
	free(obj);
}

static void destroy_module(struct module *module) {
	struct walker walker = {NULL, &free_str, &free_array, NULL, &free_obj,
			NULL};
	walk_object(module->root, module->root_type, &walker);
	destroy_type(module->root_type);
	free(module);
}

void walk_object(intptr_t *obj, type_t type, struct walker *walker) {
	struct adt *adt;
	intptr_t ix;
	struct ctor *ctor;
	struct array *array;
	size_t i, len;
	switch (type->kind) {
	case KIND_INT:
		if (walker->walk_int)
			walker->walk_int((int)(intptr_t) obj);
		break;

	case KIND_STR:
		if (walker->walk_str)
			walker->walk_str((char *) obj);
		break;

	case KIND_ARRAY:
		array = (struct array *) obj;
		for (i = 0, len = array->len; i < len; i++)
			walk_object((intptr_t *) array->elems[i], type->ref,
					walker);
		/* Walking after for now due to cleanup needs */
		if (walker->walk_array)
			walker->walk_array(array);
		break;

	case KIND_ADT:
		adt = type->adt;
		ix = *obj;
		CHECK(ix < adt->ctor_count, "%d >= %d on %s", (int) ix,
			(int) adt->ctor_count, adt->name);
		ctor = adt->ctors[ix];
		if (walker->walk_open)
			walker->walk_open(obj, adt, ctor);
		len = ctor->field_count;
		for (i = 0; i < len; i++)
			walk_object((intptr_t *) obj[i + 1],
					ctor->fields[i]->type, walker);
		if (walker->walk_close)
			walker->walk_close(obj);
		break;

	case KIND_WEAK:
		if (walker->walk_ref)
			walker->walk_ref(obj);
		break;

	default:
		fail("Invalid object kind %d", (int) type->kind);
	}
}

#ifdef STANDALONE
int main(void) {
	setup_serial("");

	char *hash = module_hash_by_name("forms");
	type_t ast_type = adtT(DtList);
	load_module(hash, ast_type);

	CHECK(map_has(loaded_modules, hash), "Not loaded?");
	CHECK(!map_has(loaded_modules, "fgsfds"), "Bogus hash");

	destroy_type(ast_type);
	free(hash);

	cleanup_serial();
	return 0;
}
#endif /* STANDALONE */
