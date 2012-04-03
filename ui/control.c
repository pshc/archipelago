#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include "control.h"
#include "edit.h"
#include "serial.h"
#include "util.h"

void control_setup(void) {
    setup_serial();

    struct adt *body_dt = map_get(named_dts, "CompilationUnit");
    struct module *bedrock_mod = load_named_module("bedrock", body_dt);
    editor_set_module(bedrock_mod);
}

void control_shutdown(void) {
    cleanup_serial();
}