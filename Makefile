all: tada

tada: mods views
	./c.py

mods:
	mkdir $@
views:
	mkdir $@

clean:
	rm -f -- mods/* views/* *.pyc a.out
