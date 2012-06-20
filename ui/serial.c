#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include "platform.h"
#include "serial.h"
#include "util.h"

struct adt *Type, *TypeVar, *PrimType;
struct adt *FieldForm, *CtorForm, *DtForm, *DtList;
struct adt *Overlay, *Entry;
struct map *loaded_modules;
/* Map of array listings, keyed by module pointer */
struct map *loaded_atoms;
struct map *atom_names, *named_dts, *form_dts;
struct module *forms_module;

/* Deserialization context */
static FILE *f = NULL;
static intptr_t node_ctr;
static struct map *own_map, *forward_refs;
static void ***dep_listing;
static intptr_t *cur_field;

static void *read_node(type_t type);
static void destroy_module(struct module *);
static void read_forms_module(void);

type_t intT(void) {
	type_t type = malloc(sizeof *type);
	type->kind = KIND_INT;
	type->adt = NULL;
	type->n = 0;
	return type;
}

type_t strT(void) {
	type_t type = malloc(sizeof *type);
	type->kind = KIND_STR;
	type->adt = NULL;
	type->n = 0;
	return type;
}

type_t boolT(void) {
	type_t type = malloc(sizeof *type);
	type->kind = KIND_BOOL;
	type->adt = NULL;
	type->n = 0;
	return type;
}

type_t voidT(void) {
	type_t type = malloc(sizeof *type);
	type->kind = KIND_VOID;
	type->adt = NULL;
	type->n = 0;
	return type;
}

type_t tvarT(struct tvar *tvar) {
	type_t type = malloc(sizeof *type);
	type->kind = KIND_VOID;
	type->tvar = tvar;
	type->n = 0;
	return type;
}

type_t adtT(struct adt *adt) {
	type_t type = malloc(sizeof *type);
	type->kind = KIND_ADT;
	type->adt = adt;
	type->n = 0;
	return type;
}

type_t arrayT(type_t elem) {
	type_t type = malloc(sizeof *type);
	type->kind = KIND_ARRAY;
	type->ref = elem;
	type->n = 0;
	return type;
}

type_t weak(type_t t) {
	type_t wrapper = malloc(sizeof *wrapper);
	wrapper->kind = KIND_WEAK;
	wrapper->ref = t;
	wrapper->n = 0;
	return wrapper;
}

type_t copy_type(type_t t) {
	type_t copy = malloc(sizeof *t);
	memcpy(copy, t, sizeof *t);
	return copy;
}

void destroy_type(type_t t) {
	size_t i, n;
	switch (t->kind) {
		case KIND_INT:
		case KIND_STR:
		case KIND_BOOL:
		case KIND_VOID:
		case KIND_TVAR:
		case KIND_ADT:
			break;
		case KIND_FUNC:
		case KIND_TUPLE:
			for (i = 0, n = t->n; i < n; i++)
				destroy_type(t->types[i]);
			free(t->types);
			break;
		case KIND_ARRAY:
		case KIND_WEAK:
			destroy_type(t->ref);
			break;
	}
	free(t);
}

static struct field *make_field(const char *name, type_t type) {
	struct field *field = malloc(sizeof *field);
	field->name = strdup(name);
	field->type = type;
	return field;
}

static struct ctor *make_ctor(const char *name, size_t field_count,
			struct field **fields) {
	struct ctor *ctor = malloc(sizeof *ctor);
	ctor->name = strdup(name);
	ctor->field_count = field_count;
	ctor->fields = fields;
	return ctor;
}

static void set_adt_ctors(struct adt *adt, size_t ctor_count,
			struct ctor **ctors) {
	CHECK(adt->ctors == NULL, "ADT %s already has ctors", adt->name);
	CHECK(ctor_count > 0, "No phantom types");
	adt->ctor_count = ctor_count;
	adt->ctors = ctors;
}

struct ctor *Ctor(const char *name, size_t field_count, ...) {
	va_list field_list;
	struct field **fields;
	const char *field_name;
	size_t i;
	fields = malloc(field_count * sizeof fields);
	va_start(field_list, field_count);
	for (i = 0; i < field_count; i++) {
		field_name = va_arg(field_list, const char *);
		/* Take ownership of the types */
		fields[i] = make_field(name, va_arg(field_list, type_t));
	}
	va_end(field_list);
	return make_ctor(name, field_count, fields);
}

static void destroy_ctor(struct ctor *ctor) {
	size_t i, count;
	struct field *field;
	for (i = 0, count = ctor->field_count; i < count; i++) {
		field = ctor->fields[i];
		/* TEMP */
		if (!field)
			continue;
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
	if (ctor_count) {
		va_start(ctor_list, ctor_count);
		ctors = malloc(ctor_count * sizeof *ctors);
		for (i = 0; i < ctor_count; i++)
			ctors[i] = va_arg(ctor_list, struct ctor *);
		va_end(ctor_list);
	}
	set_adt_ctors(adt, ctor_count, ctors);
}

static void destroy_ADT(struct adt *adt) {
	size_t i, count;
	for (i = 0, count = adt->ctor_count; i < count; i++)
		destroy_ctor(adt->ctors[i]);
	free(adt->ctors);
	free(adt->name);
	free(adt);
}

void setup_serial(void) {
    setup_platform();
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
	PrimType = ADT("PrimType");
	ADT_ctors(PrimType, 4, Ctor("PInt", 0), Ctor("PStr", 0),
		Ctor("PChar", 0), Ctor("PBool", 0));
	ADT_ctors(Type, 14,
		Ctor("TVar", 1, "typeVar", weak(adtT(TypeVar))),
		Ctor("TPrim", 1, "primType", adtT(PrimType)),
		Ctor("TVoid", 0),
		Ctor("TTuple", 1, "tupleTypes", arrayT(adtT(Type))),
		Ctor("TAnyTuple", 0),
		Ctor("TFunc", 2, "funcArgs", arrayT(adtT(Type)),
				"funcRet", adtT(Type)),
		Ctor("TData", 1, "data", weak(adtT(DtForm))),
		Ctor("TApply", 3, "appTarget", adtT(Type),
				"appVar", weak(adtT(TypeVar)),
				"appArg", adtT(Type)),
		Ctor("TArray", 1, "elemType", adtT(Type)),
		Ctor("TWeak", 1, "refType", adtT(Type)));
	DtList = ADT("DtList");
	ADT_ctors(DtList, 1, Ctor("DtList", 1, "dts", arrayT(adtT(DtForm))));

	Entry = ADT("Entry");
	ADT_ctors(Entry, 1, Ctor("Entry", 2,
		"key", weak(NULL), /* TEMP */
		"value", strT()));
	Overlay = ADT("Overlay");
	ADT_ctors(Overlay, 1, Ctor("Overlay", 1,
		"entries", arrayT(adtT(Entry))));

	form_dts = new_map(NULL, NULL, &destroy_ADT);
	named_dts = new_map(&strcmp, &free, NULL);
	loaded_atoms = new_map(NULL, NULL, &free);
	atom_names = new_map(NULL, NULL, &free);
	loaded_modules = new_map(&strcmp, &free, &destroy_module);

	read_forms_module();
}

void cleanup_serial(void) {
	destroy_map(loaded_modules);
	destroy_map(atom_names);
	destroy_map(loaded_atoms);
	destroy_map(named_dts);
	destroy_map(form_dts);
	destroy_ADT(Type);
	destroy_ADT(TypeVar);
	destroy_ADT(PrimType);
	destroy_ADT(FieldForm);
	destroy_ADT(CtorForm);
	destroy_ADT(DtForm);
	destroy_ADT(DtList);
    cleanup_platform();
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

static void *read_tuple(size_t n, type_t *types) {
	size_t i;
	intptr_t *entries;
	entries = malloc(sizeof *types * n);
	for (i = 0; i < n; i++)
		entries[i] = (intptr_t) read_node(types[i]);
	return entries;
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
	size_t ctor_count, field_count, i, ix;
	struct field **src;

	ctor_count = adt->ctor_count;
	if (ctor_count > 1) {
		ix = (size_t) read_int();
		CHECK(ix < ctor_count, "ADT %s index overflow (%d>%d)", adt->name, (int) ix, (int) ctor_count);
	}
	else {
		CHECK(ctor_count == 1, "Phantom type?!");
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
		dest = dep_listing[mod_ix - 1][atom_ix];
	}
	/* TODO: typecheck the referenced atom */
	(void) type;
	return dest;
}

static void *read_node(type_t type) {
	intptr_t ix;
	void *node;
	switch (type->kind) {
		case KIND_INT:
		case KIND_BOOL:
			return (void *)(intptr_t)read_int();

		case KIND_STR:
			return read_str();

		case KIND_VOID:
			fail("No void literals");

		case KIND_TVAR:
			fail("No tvar literals");

		case KIND_FUNC:
			fail("No func literals");

		case KIND_TUPLE:
			return read_tuple(type->n, type->types);

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
    char *full = module_path("mods", name);
    char *hash = malloc(65);
	ssize_t read = readlink(full, hash, 64);
	if (read < 0) {
		perror(full);
        free(full);
		fail("Couldn't find hash for module '%s'.", name);
	}
    free(full);
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

static void **own_listing;

static void populate_own_listing(void *key, void *value) {
	own_listing[(int)(intptr_t) key] = value;
}

struct module *load_module(const char *hash, type_t root_type) {
	char *full, *combined;
	int atom_count, dep_count, i;
	char dep[65];
	size_t count;
	void *root;
	struct module *module, *dep_mod;
	FILE *saved;
	void ***saved_dep_listing = NULL;

	if (map_has(loaded_modules, hash))
		return map_get(loaded_modules, hash);

	/* Get the node count for ease of loading */
    combined = alloca(strlen(hash) + 7);
	strcpy(combined, hash);
	strcat(combined, "_count");
    full = module_path("opt", combined);
	f = fopen(full, "rb");
    free(full);
	if (!f)
		error_out(combined);

	atom_count = read_int();
	CHECK(atom_count > 0, "Empty mod or bad metadata");
	CHECK(fgetc(f) == EOF && feof(f), "Trailing metadata");
	fclose(f);
	printf("%s has %d atom(s).\n", hash, atom_count);

	full = module_path("mods", hash);
	f = fopen(full, "rb");
    free(full);
    full = NULL;
	if (!f)
		error_out(hash);

	dep_count = read_int();
	printf("%s has %d dep(s).\n", hash, dep_count);
	if (dep_count > 0)
		saved_dep_listing = malloc(sizeof *dep_listing * dep_count);

	/* Loading deps will overwrite context. Preserve it. */
	saved = f;
	for (i = 0; i < dep_count; i++) {
		count = fread(dep, sizeof dep - 1, 1, saved);
		if (!count)
			error_out(hash);
		dep[sizeof dep - 1] = '\0';
		/* TODO: Where do we get the dep root type? */
		dep_mod = load_module(dep, root_type);
		saved_dep_listing[i] = map_get(loaded_atoms, dep_mod);
	}

	f = saved;
	dep_listing = saved_dep_listing;
	node_ctr = 0;
	cur_field = NULL;
	own_map = new_map(NULL, NULL, NULL);
	forward_refs = new_map(NULL, NULL, &free_list);
	root = read_node(root_type);

	CHECK(node_ctr == atom_count, "Inconsistent atom count");

	if (dep_count > 0)
		free(saved_dep_listing);

	map_foreach(forward_refs, (map_foreach_f) &resolve_forward_refs);
	destroy_map(forward_refs);

	CHECK(fgetc(f) == EOF && feof(f), "Trailing data");
	fclose(f);
	f = NULL;

	module = malloc(sizeof *module);
	module->root_type = copy_type(root_type);
	module->root = root;
	map_set(loaded_modules, strdup(hash), module);

	own_listing = malloc(sizeof *own_listing * atom_count);
	/* TODO: Don't even bother with the map */
	map_foreach(own_map, &populate_own_listing);
	map_set(loaded_atoms, module, own_listing);
	own_listing = NULL;
	destroy_map(own_map);

	return module;
}

static void map_name(void *node, char *name) {
	map_set(atom_names, node, strdup(name));
}

static void map_names(struct array *entries) {
	size_t i;
	for (i = 0; i < entries->len; i++)
		match(entries->elems[i], Entry, "Entry", &map_name, NULL);
}

struct module *load_named_module(const char *name, struct adt *root_adt) {
	char *hash, *names_name;
	type_t root_type, overlay_type;
	struct module *mod, *names_mod;

	root_type = adtT(root_adt);
	overlay_type = adtT(Overlay);

	hash = module_hash_by_name(name);
	mod = load_module(hash, root_type);
	free(hash);

	names_name = alloca(strlen(name) + 6);
	strcpy(names_name, name);
	strcat(names_name, "_Name");
	hash = module_hash_by_name(names_name);
	names_mod = load_module(hash, overlay_type);
	free(hash);

	match(names_mod->root, Overlay, "Overlay", map_names, NULL);

	destroy_type(overlay_type);
	destroy_type(root_type);

	return mod;
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
	struct ctor *ctor;
	struct array *array;
	size_t i, len, ix;
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

static void *dispatch_match_self(void *func, intptr_t *obj, size_t n) {
	switch (n) {
	case 0:
		return ( (void *(*)(intptr_t *)) func )(obj);
	case 1:
		return ( (void *(*)(intptr_t *, intptr_t)) func )(obj, obj[1]);
	case 2:
		return ( (void *(*)(intptr_t *, intptr_t, intptr_t)) func )(obj, obj[1], obj[2]);
	case 3:
		return ( (void *(*)(intptr_t *, intptr_t, intptr_t, intptr_t)) func )(obj, obj[1], obj[2], obj[3]);
	default:
		fail("%d fields not supported", (int) n);
	}
}

static void *dispatch_match(void *func, intptr_t *obj, size_t n) {
	switch (n) {
	case 0:
		return ( (void *(*)()) func )();
	case 1:
		return ( (void *(*)(intptr_t)) func )(obj[1]);
	case 2:
		return ( (void *(*)(intptr_t, intptr_t)) func )(obj[1], obj[2]);
	case 3:
		return ( (void *(*)(intptr_t, intptr_t, intptr_t)) func )(obj[1], obj[2], obj[3]);
	default:
		fail("%d fields not supported", (int) n);
	}
}

void *match(intptr_t *obj, struct adt *adt, ...) {
	va_list case_list;
	struct ctor *ctor;
	const char *ctor_name;
	void *func, *result;
	size_t i, n, nctors;
	int include_self;
	nctors = adt->ctor_count;
	CHECK(nctors > 0, "Phantom type?");
	va_start(case_list, adt);
	while ((ctor_name = va_arg(case_list, const char *))) {
		include_self = ctor_name[0] == '@';
		if (include_self)
			ctor_name++;
		for (i = 0; i < nctors; i++) {
			ctor = adt->ctors[i];
			if (strcmp(ctor->name, ctor_name) == 0) {
				ctor = adt->ctors[i];
				break;
			}
		}
		CHECK(i < adt->ctor_count, "No %s.%s", adt->name, ctor_name);
		func = va_arg(case_list, void *);
		if (i == (size_t) obj[0]) {
			n = ctor->field_count;
			if (include_self)
				result = dispatch_match_self(func, obj, n);
			else
				result = dispatch_match(func, obj, n);
			break;
		}
	}
	if (ctor_name == NULL)
		fail("Match failed.");
	va_end(case_list);
	return result;
}

const char *get_name(void *atom) {
	return map_has(atom_names, atom) ? map_get(atom_names, atom) : "<no name>";
}

#ifdef STANDALONE
#define SLOG(...) printf(__VA_ARGS__);
#else
#define SLOG(...)
#endif

static type_t read_type(intptr_t *);

static void *read_tvar(void *tvar) {
	return tvarT(tvar);
}

static void *read_tprim(void *prim) {
	return match(prim, PrimType,
		"PInt", intT,
		"PStr", strT,
		"PBool", boolT,
		NULL);
}

static void *read_ttuple(struct array *subs) {
	size_t i, len;
	struct type *type, **types;
	len = subs->len;
	CHECK(len > 0, "Zero-length tuple?");
	type = malloc(sizeof *type);
	type->kind = KIND_TUPLE;
	type->n = len;
	types = malloc(len * sizeof *types);
	type->types = types;
	for (i = 0; i < len; i++)
		types[i] = read_type(subs->elems[i]);
	return type;
}

static void *read_tfunc(struct array *args, void *ret) {
	size_t i, len;
	struct type *type, **types;
	len = args->len;
	type = malloc(sizeof *type);
	type->kind = KIND_FUNC;
	type->n = len + 1;
	types = malloc(type->n * sizeof *types);
	type->types = types;
	for (i = 0; i < len; i++)
		types[i] = read_type(args->elems[i]);
	types[len] = read_type(ret);
	return type;
}

static void *read_tdata(void *tdata) {
	return adtT(map_get(form_dts, tdata));
}

static void *read_tapply(void *target, void *tvar, void *arg) {
	(void) tvar;
	(void) arg;
	return read_type(target); /* TODO */
}

static void *read_tarray(void *type) {
	return arrayT(read_type(type));
}

static void *read_tweak(void *type) {
	return weak(read_type(type));
}

static type_t read_type(intptr_t *type) {
	return match(type, Type,
		"TVar", read_tvar,
		"TPrim", read_tprim,
		"TVoid", voidT,
		"TTuple", read_ttuple,
		"TAnyTuple", voidT,
		"TFunc", read_tfunc,
		"TData", read_tdata,
		"TApply", read_tapply,
		"TArray", read_tarray,
		"TWeak", read_tweak,
		NULL);
}

static struct ctor *read_ctor(struct ctor *ctor, struct array *field_forms) {
	size_t i, len;
	struct field *field, **fields = NULL;
	void *field_form;
	const char *name;

	name = get_name(ctor);
	len = field_forms->len;
	SLOG("  %s has %d field(s).\n", name, (int) len);
	if (len) {
		fields = malloc(len * sizeof *fields);
		for (i = 0; i < len; i++) {
			field_form = field_forms->elems[i];
			field = malloc(sizeof *field);
			field->name = strdup(get_name(field_form));
			SLOG("   %s\n", field->name);
			field->type = match(field_form, FieldForm,
					"FieldForm", &read_type, NULL);
			fields[i] = field;
		}
	}
	return make_ctor(name, len, fields);
}

static void read_dt(intptr_t *dt, struct array *ctor_forms,
			struct array *tvars) {
	size_t i, len;
	struct ctor **ctors;
	(void) tvars;
	len = ctor_forms->len;
	SLOG(" %s has %d ctor(s).\n", get_name(dt), (int) len);
	if (len) {
		ctors = malloc(len * sizeof *ctors);
		for (i = 0; i < len; i++)
			ctors[i] = match(ctor_forms->elems[i], CtorForm,
					"@CtorForm", &read_ctor, NULL);
	}
	set_adt_ctors(map_get(form_dts, dt), len, ctors);
}

static void read_forms(struct array *forms) {
	size_t i, len;
	for (i = 0, len = forms->len; i < len; i++)
		match(forms->elems[i], DtForm, "@DtForm", &read_dt, NULL);
}

static void scan_dt(intptr_t *dt, struct array *ctor_forms,
			struct array *tvars) {
	struct adt *adt;
	const char *name;
	(void) ctor_forms;
	(void) tvars;
	name = get_name(dt);
	adt = ADT(name);
	map_set(form_dts, dt, adt);
	map_set(named_dts, strdup(name), adt);
}

static void scan_forms(struct array *forms) {
	size_t i, len;
	len = forms->len;
	SLOG("%d form(s).\n", (int) len);
	for (i = 0; i < len; i++)
		match(forms->elems[i], DtForm, "@DtForm", &scan_dt, NULL);
}

static void read_forms_module(void) {
	forms_module = load_named_module("forms", DtList);
	match(forms_module->root, DtList, "DtList", &scan_forms, NULL);
	match(forms_module->root, DtList, "DtList", &read_forms, NULL);
}

#ifdef STANDALONE
int main(void) {
	setup_serial();
	cleanup_serial();
	return 0;
}
#endif /* STANDALONE */
