SCRIPTS = ptrsize

__init__.py: $(SCRIPTS)
	@./ptrsize; echo PTRSIZE = $$? > $@

clean:
	rm -f -- __init__.py $(SCRIPTS)

.PHONY: clean
