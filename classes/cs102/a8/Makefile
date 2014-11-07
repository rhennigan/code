prep: 
	mkdir -p build/

test: hash.o
	gcc -o test test.c build/hash.o

hash.o: lib/hash.h src/hash.c
	gcc -o build/hash.o src/hash.c
