TESTS := $(wildcard tests/*.py)
TEST_BINS := $(TESTS:tests/%.py=views/tests_%)
CODEGEN = ./construct.py -q --

all: test

debug: CODEGEN = ipdb construct.py -q --
debug: remake_tests

llvm: dirs
	@./llvm.py | tee hello.ll
	@llvm-as < hello.ll | opt -mem2reg | lli || echo Exited with code $$?

as: dirs
	@llvm-as < hello.ll | opt -mem2reg | llvm-dis

dirs: mods opt views
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
	rm -f -- mods/* opt/* views/* *.pyc *.bc *.ll hello a.out
