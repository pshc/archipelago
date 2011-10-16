#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include "control.h"
#include "serial.h"
#include "util.h"

struct module *test_module;

static void print_int(int i) {
    printf("Walk %d\n", i);
}
static void print_str(char *str) {
    printf("Walk \"%s\"\n", str);
}
static void print_obj(intptr_t *obj, struct adt *adt, struct ctor *ctor) {
    printf("Walk %s @ 0x%x\n", ctor->name, (unsigned int) obj);
}
static void print_ref(intptr_t *obj) {
    printf("Walk ->0x%x\n", (unsigned int) obj);
}

void control_setup(void) {
    char *dir = strdup(__FILE__);
    *(strrchr(dir, '/') + 1) = '\0';
    setup_serial(dir);
    free(dir);

    char *hash = module_hash_by_name("test");
    test_module = load_module(hash, adtT(AST));

    struct walker walker = {&print_int, &print_str, &print_obj, &print_ref};
    walk_object(test_module->root, test_module->root_type, &walker);
}

void control_shutdown(void) {
    printf("Shutting down.\n");
}