TESTS := $(wildcard tests/*.py)
TEST_TARGETS := $(TESTS:tests/%.py=%)
DIRS = bin ir mods opt views
OPTS = --color
CODEGEN = ./construct.py $(OPTS)
CC = cc
CFLAGS = -g -std=c99 -pedantic -W -Wall -Werror

ifdef DEBUG
  CODEGEN = ipdb construct.py $(OPTS)
endif
ifdef PROFILE
  CODEGEN = python -m cProfile -s time construct.py $(OPTS)
endif
ifdef VIEW
  OPTS := -v $(OPTS)
endif

all: test

debug: CODEGEN = ipdb construct.py $(OPTS)
debug: remake_tests

editor:
	@$(MAKE) -C Editor

profile: CODEGEN = python -m cProfile -s time construct.py $(OPTS)
profile: remake_tests

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

bin/%: tests/%.py setup ir/z.o
	$(CODEGEN) --test -- $< && $@ || echo $@ returned $$?.

$(TEST_TARGETS):
	@$(MAKE) bin/$@

Editor/obj/Editor_%.ll.o: Editor/%.py $(DIRS) prop.py expand.py llvm.py
	$(CODEGEN) --c-header -o Editor/obj/ $<

remake_tests: setup ir/z.o
	$(CODEGEN) --test -- $(TESTS)

test: remake_tests
	@echo Running tests...
	@for target in $(TEST_TARGETS); do \
	  bin/$$target || echo $$target returned $$?.; \
	done
	@echo
	@echo Done.

.PHONY: all clean debug dirs editor remake_tests setup test

clean:
	rm -rf -- $(DIRS) *.pyc
	@$(MAKE) -C Editor clean
	@$(MAKE) -C mach clean
