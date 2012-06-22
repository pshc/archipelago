TESTS := $(wildcard tests/*.py)
TEST_BINS := $(TESTS:tests/%.py=bin/tests_%)
OPTS = --color -t
CODEGEN = ./construct.py $(OPTS) --

all: test

debug: CODEGEN = ipdb construct.py $(OPTS) --
debug: remake_tests

llvm: dirs
	@./llvm.py | tee hello.ll
	@llvm-as < hello.ll | opt -mem2reg | lli || echo Exited with code $$?

as: dirs
	@llvm-as < hello.ll | opt -mem2reg | llvm-dis

dirs: bin ir mods opt views
bin:
	mkdir $@
ir:
	mkdir $@
mods:
	mkdir $@
opt:
	mkdir $@
views:
	mkdir $@

views/tests_%: tests/%.py dirs
	$(CODEGEN) $<

remake_tests: dirs
	$(CODEGEN) $(TESTS)

test: remake_tests
	@echo -n Running tests
	@for bin in $(TEST_BINS); do $$bin; done
	@echo
	@echo Done.

.PHONY: all clean debug dirs llvm remake_tests test

clean:
	rm -rf -- bin/ ir/ mods/ opt/ views/ *.pyc *.bc hello a.out
