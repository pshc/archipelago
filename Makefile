TESTS := $(wildcard tests/*.py)
TEST_BINS := $(TESTS:tests/%.py=views/tests_%)

all: tada

tada: mods views
	./c.py short.py

mods:
	mkdir $@
views:
	mkdir $@

views/tests_%:tests/%.py
	./c.py $<

test: $(TEST_BINS)
	@echo -n Running tests
	@for bin in $(TEST_BINS); do $$bin; done
	@echo
	@echo Done.

.PHONY: all clean test

clean:
	rm -f -- mods/* views/* *.pyc a.out
