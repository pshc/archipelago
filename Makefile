TESTS := $(wildcard tests/*.py)
TEST_BINS := $(TESTS:tests/%.py=bin/tests_%)
DIRS = bin ir mods opt views
OPTS = --color -q
CODEGEN = ./construct.py $(OPTS) --

all: test

debug: CODEGEN = ipdb construct.py $(OPTS) --
debug: remake_tests

dirs: $(DIRS)
$(DIRS):
	mkdir $@

ir/z.o: z.c
	cc -c -o $@ $^

views/tests_%: tests/%.py dirs
	$(CODEGEN) $<

remake_tests: dirs ir/z.o
	$(CODEGEN) $(TESTS)

test: remake_tests
	@echo -n Running tests
	@for bin in $(TEST_BINS); do $$bin; done
	@echo
	@echo Done.

.PHONY: all clean debug dirs remake_tests test

clean:
	rm -rf -- $(DIRS) *.pyc
