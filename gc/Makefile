# Do shell calls by-need for now
CXXFLAGS = -W -Wall -Wno-unused-parameter -dynamiclib \
           $(shell llvm-config --cxxflags)
LDFLAGS = -L$(shell llvm-config --libdir)
LIBS = $(shell llvm-config --libs codegen)

all: bluefin.so test.s

bluefin.so: bluefin.cc
	@echo Building bluefin GC plugin...
	@$(CXX) $(CXXFLAGS) $(LDFLAGS) -o $@ $^ $(LIBS)

editor: bluefin.so
	@$(MAKE) -C ../Editor

test.s: bluefin.so ../ir/cond.ll
	llc -load=bluefin.so ../ir/cond.ll -o test.s

clean:
	@rm -f -- bluefin.so test.s

.PHONY: all clean editor
