CFLAGS = -Wall -DSTANDALONE

all: mods serial
	./serial
	@#python native.py

mods:
	mkdir mods

serial: serial.c util.c
