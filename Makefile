all: tada

tada:
	./c.py

serialize:
	./interpret.py serialize.py

test:
	./interpret.py test.py

clean:
	rm -f -- konnichiwa hello world.c mods/*
