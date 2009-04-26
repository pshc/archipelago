all: tada

tada:
	./interpret.py serialize.py

test:
	./interpret.py test.py
