GCC_OPTS="-std=c99 -g"

test: util.o hash.o user_input.o list.o
	gcc -o test $GCC_OPTS test.c build/*.o

util.o: lib/util.h src/util.c prep
	gcc -o build/util.o $GCC_OPTS -c src/util.c

list.o: lib/list.h src/list.c prep
	gcc -o build/list.o $GCC_OPTS -c src/list.c

hash.o: lib/hash.h src/hash.c prep
	gcc -o build/hash.o $GCC_OPTS -c src/hash.c

user_input.o: lib/user_input.h src/user_input.c prep
	gcc -o build/user_input.o $GCC_OPTS -c src/user_input.c

prep: 
	mkdir -p build/

clean:
	rm build/*.o
