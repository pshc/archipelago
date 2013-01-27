TARGETS = x86/Editor_visual.ll.o arm/Editor_visual.ll.o
ABS_TARGETS := $(TARGETS:%=Editor/%)

OBJS = obj/Editor_visual.ll.o obj/bedrock.ll.o

DIRS = arm include obj x86
MAKE_PARENT := $(MAKE) -C .. --no-print-directory

all: gl.py $(DIRS)
	@$(MAKE_PARENT) $(ABS_TARGETS)
	@$(MAKE) $(OBJS)

debug: rebuild $(DIRS)
	@DEBUG=true $(MAKE_PARENT) $(ABS_TARGETS)

profile: rebuild $(DIRS)
	@PROFILE=true $(MAKE_PARENT) $(ABS_TARGETS)

obj/%.o: arm/%.o x86/%.o
	@lipo -create $^ -output $@

$(DIRS):
	@mkdir $@

gl.py: ../importer/import.py spec.py
	python $^  > $@

.PHONY: all clean debug profile rebuild

rebuild:
	@rm -f -- $(OBJS)

clean:
	@rm -rf -- gl.py $(DIRS)
