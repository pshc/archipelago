#ifndef SERIAL_H
#define SERIAL_H

struct adt;

struct type {
	enum { KIND_INT, KIND_STR, KIND_ARRAY, KIND_ADT, KIND_WEAK } kind;
	union {
		struct adt *adt;
		struct type *ref;
	};
};
typedef struct type *type_t;

struct array {
	size_t len;
	void *elems[0];
};

struct field {
	char *name;
	type_t type;
};

struct ctor {
	char *name;
	size_t field_count;
	struct field **fields;
};

struct adt {
	char *name;
	size_t ctor_count;
	struct ctor **ctors;
};

extern struct adt *Type, *TypeVar, *FieldForm, *CtorForm, *DtForm, *DtList;

type_t intT(void);
type_t strT(void);
type_t adtT(struct adt *);
type_t arrayT(type_t);
type_t weak(type_t);
type_t copy_type(type_t);
void destroy_type(type_t);

struct ctor *Ctor(const char *name, size_t field_count, ...);
struct adt *ADT(const char *name);
void ADT_ctors(struct adt *adt, size_t ctor_count, ...);

void setup_serial(const char *base_dir);
void cleanup_serial(void);

struct module {
	type_t root_type;
	void *root;
};

struct map;

extern struct map *loaded_modules, *loaded_atoms;
extern struct map *atom_names;

char *module_hash_by_name(const char *name);
struct module *load_module(const char *hash, type_t root_type);

struct walker {
	void (*walk_int)(int);
	void (*walk_str)(char *);
	void (*walk_array)(struct array *);
	void (*walk_open)(intptr_t *, struct adt *, struct ctor *);
	void (*walk_close)(intptr_t *);
	void (*walk_ref)(intptr_t *);
};

void walk_object(intptr_t *, type_t, struct walker *);

#endif /* SERIAL_H */
