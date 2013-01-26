OBJS = x86/Editor_visual.ll.o arm/Editor_visual.ll.o
ABS_OBJS := $(OBJS:%=Editor/%)
DIRS = arm include x86
MAKE_PARENT := $(MAKE) -C .. --no-print-directory

all: gl.py $(DIRS)
	@$(MAKE_PARENT) $(ABS_OBJS)

debug: rebuild $(DIRS)
	@DEBUG=true $(MAKE_PARENT) $(ABS_OBJS)

profile: rebuild $(DIRS)
	@PROFILE=true $(MAKE_PARENT) $(ABS_OBJS)

arm:
	@mkdir arm
include:
	@mkdir include
x86:
	@mkdir x86


gl.py: ../importer/import.py spec.py
	python $^  > $@

.PHONY: all clean debug profile rebuild

rebuild:
	@rm -f -- $(OBJS)

clean:
	@rm -rf -- gl.py $(DIRS)
