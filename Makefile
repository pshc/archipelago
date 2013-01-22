TESTS := $(wildcard tests/*.py)
TEST_TARGETS := $(TESTS:tests/%.py=%)
DIRS = bin ir mods opt views
OPTS = --color
CODEGEN = ./construct.py $(OPTS)
CC = cc
CFLAGS = -g -std=c99 -pedantic -W -Wall -Werror
RUNTIME = gc/runtime.c z.c
RUNTIME_OBJS := ir/gc_runtime.o ir/z.o

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

setup: dirs ir/Makefile
dirs: $(DIRS)
$(DIRS):
	mkdir $@
ir/Makefile: .irMakefile
	@cp $< $@

bin/%: tests/%.py setup runtime
	$(CODEGEN) --test -- $< && $@ || echo $@ returned $$?.

$(TEST_TARGETS):
	@$(MAKE) bin/$@

Editor/x86/Editor_%.ll.o: Editor/%.py $(DIRS) expand.py flatten.py llvm.py
	@$(CODEGEN) --c-header -o Editor/x86/ $<

Editor/arm/Editor_%.ll.o: Editor/%.py $(DIRS) expand.py flatten.py llvm.py
	@$(CODEGEN) --arm --c-header -o Editor/arm/ $<

runtime: $(RUNTIME_OBJS)

ir/gc_runtime.o: gc/runtime.c ir
	$(CC) $(CFLAGS) -c -o $@ $<
ir/z.o: z.c ir
	$(CC) $(CFLAGS) -c -o $@ $<

remake_tests: setup runtime
	$(CODEGEN) --test -- $(TESTS)

test: remake_tests
	@echo Running tests...
	@for target in $(TEST_TARGETS); do \
	  bin/$$target || echo $$target returned $$?.; \
	done
	@echo
	@echo Done.

.PHONY: all clean debug dirs editor remake_tests runtime setup test

clean:
	rm -rf -- $(DIRS) *.pyc
	@$(MAKE) -C Editor clean
