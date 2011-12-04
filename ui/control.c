#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include "control.h"
#include "edit.h"
#include "serial.h"
#include "util.h"

void control_setup(void) {
    char *dir = strdup(__FILE__);
    *(strrchr(dir, '/') + 1) = '\0';
    setup_serial(dir);
    free(dir);

    struct adt *body_dt = map_get(named_dts, "Body");
    struct module *bedrock_mod = load_named_module("bedrock", body_dt);
    editor_set_module(bedrock_mod);
}

void control_shutdown(void) {
    cleanup_serial();
}