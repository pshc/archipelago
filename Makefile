TESTS := $(wildcard tests/*.py)
TEST_BINS := $(TESTS:tests/%.py=views/tests_%)

all: test

llvm:
	@./llvm.py | tee hello.ll
	@llvm-as < hello.ll | opt -mem2reg | lli || echo Exited with code $$?

as:
	@llvm-as < hello.ll | opt -mem2reg | llvm-dis

tada: opt mods views
	./llvm.py short.py

demo:
	./demo.py

mods:
	mkdir $@
opt:
	mkdir $@
views:
	mkdir $@

views/tests_%: tests/%.py
	./llvm.py $<

remake_tests:
	./llvm.py $(TESTS)

#test: $(TEST_BINS)
test: remake_tests
	@echo -n Running tests
	@for bin in $(TEST_BINS); do $$bin; done
	@echo
	@echo Done.

.PHONY: all clean llvm remake_tests tada test

clean:
	rm -f -- mods/* opt/* views/* *.pyc *.bc *.ll hello a.out
