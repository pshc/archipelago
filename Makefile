TESTS := $(wildcard tests/*.py)
TEST_BINS := $(TESTS:tests/%.py=views/tests_%)

all: test

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
	./llvm.py $<

remake_tests: dirs
	./llvm.py $(TESTS)

test: remake_tests
	@echo -n Running tests
	@for bin in $(TEST_BINS); do $$bin; done
	@echo
	@echo Done.

.PHONY: all clean dirs llvm remake_tests test

clean:
	rm -f -- mods/* opt/* views/* *.pyc *.bc *.ll hello a.out
