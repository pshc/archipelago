all: tada

tada:
	./mogrify.py

serialize:
	./interpret.py serialize.py

test:
	./interpret.py test.py
