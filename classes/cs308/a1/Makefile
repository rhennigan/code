#*****************************************************************************/
#* Richard Hennigan                                                          */
#* cs308_hw1: Makefile                                                       */
#* 2014-09-18                                                                */
#* Richard_Hennigan@student.uml.edu                                          */
#*****************************************************************************/


# Automatically Generated Makefile by EDE.
# For use with: make
# Relative File Name: Makefile
#
# DO NOT MODIFY THIS FILE OR YOUR CHANGES MAY BE LOST.
# EDE is the Emacs Development Environment.
# http://cedet.sourceforge.net/ede.shtml
#

top="$(CURDIR)"/

prof_prog_SOURCES=prof_prog.c
prof_prog_OBJ= prof_prog.o
CC=gcc
C_COMPILE=$(CC) $(DEFS) $(INCLUDES) $(CPPFLAGS) $(CFLAGS)
C_DEPENDENCIES=-Wp,-MD,.deps/$(*F).P
C_LINK=$(CC) $(CFLAGS) $(LDFLAGS) -L.
assignment1_SOURCES=main.c
assignment1_OBJ= main.o
VERSION=1.0
DISTDIR=$(top)cs308_assignment_1-$(VERSION)
top_builddir = 

DEP_FILES=.deps/prof_prog.P .deps/main.P

all: prof_prog assignment1

DEPS_MAGIC := $(shell mkdir .deps > /dev/null 2>&1 || :)
-include $(DEP_FILES)

%.o: %.c
	@echo '$(C_COMPILE) -c $<'; \
	$(C_COMPILE) $(C_DEPENDENCIES) -o $@ -c $<

prof_prog: $(prof_prog_OBJ)
	$(C_LINK) -o $@ $^ $(LDDEPS)

assignment1: $(assignment1_OBJ)
	$(C_LINK) -o $@ $^ $(LDDEPS)

tags: 


clean:
	rm -f *.mod *.o *.obj .deps/*.P .lo

.PHONY: dist

dist:
	rm -rf $(DISTDIR)
	mkdir $(DISTDIR)
	cp $(prof_prog_SOURCES) $(assignment1_SOURCES) $(DISTDIR)
	tar -cvzf $(DISTDIR).tar.gz $(DISTDIR)
	rm -rf $(DISTDIR)



# End of Makefile
