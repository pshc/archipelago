OBJS = obj/Editor_visual.ll.o
ABS_OBJS := $(OBJS:%=Editor/%)
DIRS = include obj
MAKE_PARENT := $(MAKE) -C .. --no-print-directory

all: gl.py $(DIRS)
	@$(MAKE_PARENT) runtime $(ABS_OBJS)

debug: rebuild $(DIRS)
	@DEBUG=true $(MAKE_PARENT) runtime $(ABS_OBJS)

profile: rebuild $(DIRS)
	@PROFILE=true $(MAKE_PARENT)  runtime $(ABS_OBJS)

include:
	@mkdir include
obj:
	@mkdir obj

gl.py: ../importer/import.py spec.py
	python $^  > $@

.PHONY: all clean debug profile rebuild

rebuild:
	@rm -f -- $(OBJS)

clean:
	@rm -rf -- gl.py $(DIRS)
