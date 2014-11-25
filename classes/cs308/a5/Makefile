CC=gcc
CFLAGS=-std=c99 -g -c
LDFLAGS=-std=c99 -g
BUILD=list
EXECUTABLE=main

SOURCES=$(BUILD:%=src/%.c)
OBJECTS=$(BUILD:%=build/%.o)
HEADERS=$(BUILD:%=lib/%.h)

all: $(SOURCES) $(EXECUTABLE)

$(EXECUTABLE): $(OBJECTS) $(EXECUTABLE).c
	$(CC) $(LDFLAGS) $(OBJECTS) $(EXECUTABLE).c -o $@

build/%.o: src/%.c lib/%.h
	@echo "building "$@" from "$<
	mkdir -p build/
	$(CC) $(CFLAGS) $< -o $@
	@echo " "

clean:
	rm build/*.o
