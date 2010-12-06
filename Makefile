all: tada

tada: mods
	./c.py

test: mods
	./interpret.py test.py

mods:
	mkdir mods

clean:
	rm -f -- konnichiwa gutentag.c hello world.c mods/*
