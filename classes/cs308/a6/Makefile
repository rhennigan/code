CC=gcc
CFLAGS=-std=gnu99 -g -c -Wall -D_USE_COLOR_TERM -D_FILE_OFFSET_BITS=64
LDFLAGS=-std=gnu99 -g -Wall -D_FILE_OFFSET_BITS=64
BUILD=util list
EXECUTABLE=rfsd

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
