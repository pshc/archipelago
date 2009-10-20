all: tada

tada:
	./c.py

serialize:
	./interpret.py serialize.py

test:
	./interpret.py test.py
