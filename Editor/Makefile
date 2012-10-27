OBJS = obj/Editor_visual.ll.o
ABS_OBJS := $(OBJS:%=Editor/%)
DIRS = include obj

all: gl.py $(DIRS)
	@$(MAKE) -C .. --no-print-directory $(ABS_OBJS)

debug: rebuild $(DIRS)
	@DEBUG=true $(MAKE) -C .. --no-print-directory $(ABS_OBJS)

profile: rebuild $(DIRS)
	@PROFILE=true $(MAKE) -C .. --no-print-directory $(ABS_OBJS)

include:
	@mkdir include
obj:
	@mkdir obj

gl.py: ../importer/import.py spec.py
	python $^  > $@

.PHONY: all clean rebuild

rebuild:
	@rm -f -- $(OBJS)

clean:
	@rm -rf -- gl.py $(DIRS)
