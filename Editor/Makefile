OBJS = Editor/obj/Editor_gl.ll.o

all: include obj
	@$(MAKE) -C .. --no-print-directory $(OBJS)

include:
	@mkdir include
obj:
	@mkdir obj

.PHONY: all clean

clean:
	rm -rf -- include obj
