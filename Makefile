all: tada

tada:
	./hm.py

serialize:
	./interpret.py serialize.py

test:
	./interpret.py test.py
