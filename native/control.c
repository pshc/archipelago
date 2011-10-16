#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include "control.h"
#include "serial.h"
#include "util.h"

struct module *test_module;

static void walk_ast(void *node, type_t type) {
    intptr_t *obj = node;
    if (type->kind == KIND_ADT) {
        struct adt *adt = type->adt;
        intptr_t ix = *obj;
        CHECK(ix < adt->ctor_count, "%d >= %d on %s", (int) ix, (int) adt->ctor_count, adt->name);
        struct ctor *ctor = adt->ctors[ix];
        printf("Walk %s @ 0x%x\n", ctor->name, (unsigned int) obj);
        size_t i, len = ctor->field_count;
        for (i = 0; i < len; i++)
            walk_ast((void *) obj[i + 1], ctor->fields[i]->type);
    }
    else if (type->kind == KIND_INT) {
        printf("Walk %d\n", (int) obj);
    }
    else if (type->kind == KIND_WEAK) {
        printf("Walk weak -> 0x%x\n", (unsigned int) obj);
    }
}

void control_setup(void) {
    char *dir = strdup(__FILE__);
    *(strrchr(dir, '/') + 1) = '\0';
    setup_serial(dir);
    free(dir);

    char *hash = module_hash_by_name("test");
    test_module = load_module(hash, adtT(AST));
    walk_ast(test_module->root, test_module->root_type);
}

void control_shutdown(void) {
    printf("Shutting down.\n");
}