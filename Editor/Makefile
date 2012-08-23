OBJS = Editor/obj/Editor_visual.ll.o

all: gl.py include obj
	@$(MAKE) -C .. --no-print-directory $(OBJS)

include:
	@mkdir include
obj:
	@mkdir obj

gl.py: ../importer/import.py spec.py
	python $^  > $@

.PHONY: all clean

clean:
	rm -rf -- gl.py include obj
