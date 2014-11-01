assignment_log: src/assignment_log.c pq.o list.o user_input.o
	mkdir -p build/
	cc -o build/assignment_log -g src/assignment_log.c build/pq.o build/list.o build/user_input.o

user_input.o: src/user_input.c lib/user_input.h
	mkdir -p build/
	cc -o build/user_input.o -c -g src/user_input.c

pq.o: src/pq.c lib/pq.h list.o
	mkdir -p build/
	cc -o build/pq.o -c -g src/pq.c

list.o: src/list.c lib/list.h
	mkdir -p build/
	cc -o build/list.o -c -g src/list.c
