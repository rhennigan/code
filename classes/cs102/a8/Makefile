test: hash.o
	gcc -o test test.c build/hash.o

hash.o: lib/hash.h src/hash.c prep
	gcc -o build/hash.o -c src/hash.c

prep: 
	mkdir -p build/
