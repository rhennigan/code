CC=gcc
CFLAGS=-std=gnu99 -c -Wall
LDFLAGS=-std=gnu99 -Wall
BUILD=list
EXECUTABLE=test

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
