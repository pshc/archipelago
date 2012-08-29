TESTS := $(wildcard tests/*.py)
TEST_BINS := $(TESTS:tests/%.py=bin/%)
DIRS = bin ir mods opt views
OPTS = --color -q
CODEGEN = ./construct.py $(OPTS)
CC = cc
CFLAGS = -ansi -pedantic -W -Wall -Werror

ifdef DEBUG
  CODEGEN = ipdb construct.py $(OPTS)
endif

all: test

debug: CODEGEN = ipdb construct.py $(OPTS)
debug: remake_tests

setup: dirs mach/__init__.py ir/Makefile
dirs: $(DIRS)
$(DIRS):
	mkdir $@
mach/__init__.py:
	@$(MAKE) -C mach __init__.py
ir/Makefile: .irMakefile
	@cp $< $@

ir/z.o: z.c
	$(CC) $(CFLAGS) -c -o $@ $^

bin/%: tests/%.py setup
	$(CODEGEN) $<

Editor/obj/Editor_%.ll.o: Editor/%.py $(DIRS) prop.py expand.py llvm.py
	$(CODEGEN) --c-header -o Editor/obj/ $<

remake_tests: setup ir/z.o
	$(CODEGEN) --test -- $(TESTS)

test: remake_tests
	@echo Running tests...
	@for bin in $(TEST_BINS); do \
	  $$bin || echo $$bin returned $$?.; \
	done
	@echo
	@echo Done.

.PHONY: all clean debug dirs remake_tests setup test

clean:
	rm -rf -- $(DIRS) *.pyc
	@$(MAKE) -C Editor clean
	@$(MAKE) -C mach clean
