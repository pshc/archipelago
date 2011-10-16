#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include "control.h"
#include "serial.h"
#include "util.h"

static struct module *test_module;

void control_setup(void) {
    char *dir = strdup(__FILE__);
    *(strrchr(dir, '/') + 1) = '\0';
    setup_serial(dir);
    free(dir);

    char *hash = module_hash_by_name("test");
    test_module = load_module(hash, adtT(AST));
}

void control_shutdown(void) {
    printf("Shutting down.\n");
}