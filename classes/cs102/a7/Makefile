test: test.c pq.o list.o
	mkdir -p build/
	cc -o build/test -g test.c build/pq.o build/list.o

pq.o: src/pq.c lib/pq.h list.o
	mkdir -p build/
	cc -o build/pq.o -c -g src/pq.c

list.o: src/list.c lib/list.h
	mkdir -p build/
	cc -o build/list.o -c -g src/list.c
