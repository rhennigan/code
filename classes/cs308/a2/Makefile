# Automatically Generated Makefile by EDE.
# For use with: make
# Relative File Name: Makefile
#
# DO NOT MODIFY THIS FILE OR YOUR CHANGES MAY BE LOST.
# EDE is the Emacs Development Environment.
# http://cedet.sourceforge.net/ede.shtml
#

top="$(CURDIR)"/

sort_test_SOURCES=sort_test.c
sort_test_OBJ= sort_test.o
CC=gcc
C_COMPILE=$(CC) $(DEFS) $(INCLUDES) $(CPPFLAGS) $(CFLAGS)
C_DEPENDENCIES=-Wp,-MD,.deps/$(*F).P
C_LINK=$(CC) $(CFLAGS) $(LDFLAGS) -L.
grep_test_SOURCES=grep_test.c
grep_test_OBJ= grep_test.o
VERSION=1.0
DISTDIR=$(top)HW2-$(VERSION)
top_builddir = 

DEP_FILES=.deps/sort_test.P .deps/grep_test.P

all: sort_test grep_test

DEPS_MAGIC := $(shell mkdir .deps > /dev/null 2>&1 || :)
-include $(DEP_FILES)

%.o: %.c
	@echo '$(C_COMPILE) -c $<'; \
	$(C_COMPILE) $(C_DEPENDENCIES) -o $@ -c $<

sort_test: $(sort_test_OBJ)
	$(C_LINK) -o $@ $^ $(LDDEPS)

grep_test: $(grep_test_OBJ)
	$(C_LINK) -o $@ $^ $(LDDEPS)

tags: 


clean:
	rm -f *.mod *.o *.obj .deps/*.P .lo

.PHONY: dist

dist:
	rm -rf $(DISTDIR)
	mkdir $(DISTDIR)
	cp $(sort_test_SOURCES) $(grep_test_SOURCES) $(DISTDIR)
	tar -cvzf $(DISTDIR).tar.gz $(DISTDIR)
	rm -rf $(DISTDIR)

# End of Makefile
