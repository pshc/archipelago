#ifndef SERIAL_H
#define SERIAL_H

struct adt;

struct type {
	enum { KIND_INT, KIND_STR, KIND_ADT, KIND_WEAK } kind;
	union {
		struct adt *adt;
		struct type *ref;
	};
};
typedef struct type *type_t;

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

extern struct adt *AST, *Var;

type_t intT(void);
type_t adtT(struct adt *adt);
type_t weak(type_t t);
struct ctor *Ctor(char *name, size_t field_count, ...);
struct adt *ADT(char *name);
void ADT_ctors(struct adt *adt, size_t ctor_count, ...);

void setup_serial(const char *base_dir);

struct module {
	type_t root_type;
	void *root;
};

struct map;

extern struct map *loaded_modules;

char *module_hash_by_name(const char *name);
struct module *load_module(const char *hash, type_t root_type);

#endif /* SERIAL_H */
