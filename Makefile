TESTS := $(wildcard tests/*.py)
TEST_BINS := $(TESTS:tests/%.py=views/tests_%)

all: llvm

llvm:
	@./llvm.py

tada: opt mods views
	./c.py short.py

demo:
	./demo.py

mods:
	mkdir $@
opt:
	mkdir $@
views:
	mkdir $@

views/tests_%: tests/%.py
	./c.py $<

remake_tests:
	./c.py $(TESTS)

#test: $(TEST_BINS)
test: remake_tests
	@echo -n Running tests
	@for bin in $(TEST_BINS); do $$bin; done
	@echo
	@echo Done.

.PHONY: all clean llvm remake_tests tada test

clean:
	rm -f -- mods/* opt/* views/* *.pyc a.out
