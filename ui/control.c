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

    struct module *forms_mod = load_named_module("forms", DtList);
    editor_set_module(forms_mod);
}

void control_shutdown(void) {
    cleanup_serial();
}