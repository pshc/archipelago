#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include "control.h"
#include "edit.h"
#include "serial.h"

void control_setup(void) {
    char *dir = strdup(__FILE__);
    *(strrchr(dir, '/') + 1) = '\0';
    setup_serial(dir);
    free(dir);

    char *hash = module_hash_by_name("forms");
    type_t ast_type = adtT(DtList);
    struct module *test_module = load_module(hash, ast_type);
    editor_set_module(test_module);
    destroy_type(ast_type);
    free(hash);
}

void control_shutdown(void) {
    printf("Shutting down.\n");
}