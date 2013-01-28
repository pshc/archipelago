TESTS := $(wildcard tests/*.py)
TEST_TARGETS := $(TESTS:tests/%.py=%)
DIRS = bin ir mods opt views
OPTS = --color
CODEGEN = time ./construct.py $(OPTS)
CC = cc
CFLAGS = -g -std=c99 -pedantic -W -Wall -Werror -fstrict-aliasing

ifdef DEBUG
  CODEGEN = time ipdb construct.py $(OPTS)
endif
ifdef PROFILE
  CODEGEN = time python -m cProfile -s time construct.py $(OPTS)
endif
ifdef VIEW
  OPTS := --views $(OPTS)
endif

all: test

debug: CODEGEN = time ipdb construct.py $(OPTS)
debug: remake_tests

editor:
	@$(MAKE) -C Editor

profile: CODEGEN = time python -m cProfile -s time construct.py $(OPTS)
profile: remake_tests

setup: $(DIRS) ir/Makefile gc/bluefin.so
$(DIRS):
	@mkdir $@
ir/Makefile: .irMakefile
	@cp $< $@
gc/bluefin.so: gc/bluefin.cc
	@$(MAKE) -C gc bluefin.so

bin/%: tests/%.py setup runtime
	@$(CODEGEN) --test -- $< && $@ || echo $@ returned $$?.

$(TEST_TARGETS):
	@$(MAKE) bin/$@

Editor/x86/Editor_%.ll.o: Editor/%.py setup runtime
	@$(CODEGEN) --c-header -o Editor/x86/ $<

Editor/arm/Editor_%.ll.o: Editor/%.py setup
	@$(CODEGEN) --arm --c-header -o Editor/arm/ $<

# host runtime only
runtime: ir/gc_runtime.o ir/z.o
ir/gc_runtime.o: gc/runtime.c ir
	@echo Building GC runtime.
	@$(CC) $(CFLAGS) -c -o $@ $<
ir/z.o: z.c ir
	@echo Building runtime.
	@$(CC) $(CFLAGS) -c -o $@ $<

remake_tests: setup runtime
	@$(CODEGEN) --test -- $(TESTS)

test: remake_tests
	@echo Running tests...
	@for target in $(TEST_TARGETS); do \
	  bin/$$target || echo $$target returned $$?.; \
	done
	@echo
	@echo Done.

.PHONY: all clean debug editor remake_tests runtime setup test

clean:
	@rm -rf -- $(DIRS) *.pyc
	@$(MAKE) -C Editor clean
	@$(MAKE) -C gc clean
