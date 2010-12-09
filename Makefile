all: tada

tada: mods views
	./c.py short.py

mods:
	mkdir $@
views:
	mkdir $@

clean:
	rm -f -- mods/* views/* *.pyc a.out
