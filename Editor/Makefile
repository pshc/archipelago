OBJS = Editor/obj/Editor_gl.ll.o

all: include obj
	@$(MAKE) -C .. --no-print-directory $(OBJS)

obj:
	@mkdir obj

.PHONY: all clean

clean:
	rm -rf -- obj
