CC=gcc
CFLAGS=-std=c99 -g -c
LDFLAGS=-g
SOURCES=src/list.c src/hash.c src/user_input.c src/util.c test.c
OBJECTS=$(SOURCES:.c=.o)
EXECUTABLE=test

all: $(SOURCES) $(EXECUTABLE)

$(EXECUTABLE): $(OBJECTS)
	$(CC) $(LDFLAGS) $(OBJECTS) -o $@

.c.o:
	$(CC) $(CFLAGS) $< -o $@

# test: util.o hash.o user_input.o list.o
# 	$(CC) -o test $(CFLAGS) test.c build/*.o

# util.o: lib/util.h src/util.c prep
# 	$(CC) -o build/util.o $(CFLAGS) -c src/util.c

# list.o: lib/list.h src/list.c prep
# 	$(CC) -o build/list.o $(CFLAGS) -c src/list.c

# hash.o: lib/hash.h src/hash.c prep
# 	$(CC) -o build/hash.o $(CFLAGS) -c src/hash.c

# user_input.o: lib/user_input.h src/user_input.c prep
# 	$(CC) -o build/user_input.o $(CFLAGS) -c src/user_input.c

# prep: 
# 	mkdir -p build/

# clean:
# 	rm build/*.o
