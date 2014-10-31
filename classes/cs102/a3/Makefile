# Automatically Generated Makefile by EDE.
# For use with: make
# Relative File Name: Makefile
#
# DO NOT MODIFY THIS FILE OR YOUR CHANGES MAY BE LOST.
# EDE is the Emacs Development Environment.
# http://cedet.sourceforge.net/ede.shtml
#

top="$(CURDIR)"/

main_SOURCES=main.c
main_OBJ= main.o
CC=gcc
C_COMPILE=$(CC) $(DEFS) $(INCLUDES) $(CPPFLAGS) $(CFLAGS)
C_DEPENDENCIES=-Wp,-MD,.deps/$(*F).P
C_LINK=$(CC) $(CFLAGS) $(LDFLAGS) -L.
VERSION=1.0
DISTDIR=$(top)HW3-$(VERSION)
top_builddir = 

DEP_FILES=.deps/main.P

all: main

DEPS_MAGIC := $(shell mkdir .deps > /dev/null 2>&1 || :)
-include $(DEP_FILES)

%.o: %.c
	@echo '$(C_COMPILE) -c $<'; \
	$(C_COMPILE) $(C_DEPENDENCIES) -o $@ -c $<

main: $(main_OBJ)
	$(C_LINK) -o $@ $^ $(LDDEPS)

tags: 


clean:
	rm -f *.mod *.o *.obj .deps/*.P .lo

.PHONY: dist

dist:
	rm -rf $(DISTDIR)
	mkdir $(DISTDIR)
	cp $(main_SOURCES) $(ede_FILES) $(DISTDIR)
	tar -cvzf $(DISTDIR).tar.gz $(DISTDIR)
	rm -rf $(DISTDIR)


# End of Makefile
