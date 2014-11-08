CFLAGS="-std=c99 -g"

test: util.o hash.o user_input.o list.o
	gcc -o test $(CFLAGS) test.c build/*.o

util.o: lib/util.h src/util.c prep
	gcc -o build/util.o $(CFLAGS) -c src/util.c

list.o: lib/list.h src/list.c prep
	gcc -o build/list.o $(CFLAGS) -c src/list.c

hash.o: lib/hash.h src/hash.c prep
	gcc -o build/hash.o $(CFLAGS) -c src/hash.c

user_input.o: lib/user_input.h src/user_input.c prep
	gcc -o build/user_input.o $(CFLAGS) -c src/user_input.c

prep: 
	mkdir -p build/

clean:
	rm build/*.o
