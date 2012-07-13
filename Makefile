TESTS := $(wildcard tests/*.py)
TEST_BINS := $(TESTS:tests/%.py=bin/%)
DIRS = bin ir mods opt views
OPTS = --color -q -i
CODEGEN = ./construct.py $(OPTS) --
CC = cc
CFLAGS = -ansi -pedantic -W -Wall -Werror

all: test

debug: CODEGEN = ipdb construct.py $(OPTS) --
debug: remake_tests

dirs: $(DIRS) ir/Makefile
$(DIRS):
	mkdir $@
ir/Makefile: .irMakefile
	@cp $< $@

ir/z.o: z.c
	$(CC) $(CFLAGS) -c -o $@ $^

bin/%: tests/%.py dirs
	$(CODEGEN) $<

remake_tests: dirs ir/z.o
	$(CODEGEN) $(TESTS)

test: remake_tests
	@echo Running tests...
	@for bin in $(TEST_BINS); do \
	  $$bin || echo $$bin returned $$?.; \
	done
	@echo
	@echo Done.

.PHONY: all clean debug dirs remake_tests test

clean:
	rm -rf -- $(DIRS) *.pyc
