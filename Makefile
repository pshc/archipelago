all: tada

tada: mods
	./c.py

serialize: mods
	./interpret.py serialize.py

test: mods
	./interpret.py test.py

mods:
	mkdir mods

clean:
	rm -f -- konnichiwa hello world.c mods/*
