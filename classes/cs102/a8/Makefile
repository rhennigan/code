test: hash.o user_input.o
	gcc -o test test.c build/hash.o build/user_input.o

hash.o: lib/hash.h src/hash.c build/list.o prep
	gcc -o build/hash.o -c src/hash.c build/list.o

list.o: lib/list.h src/list.c prep
	gcc -o build/list.o -c src/list.c

user_input.o: lib/user_input.h src/user_input.c prep
	gcc -o build/user_input.o -c src/user_input.c

prep: 
	mkdir -p build/

clean:
	rm build/*.o
