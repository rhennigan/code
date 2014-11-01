all: assignment_log assignment_log_heap

assignment_log: src/assignment_log.c pq.o list.o user_input.o
	mkdir -p build/
	cc -o build/assignment_log -g src/assignment_log.c build/pq.o build/list.o build/user_input.o

assignment_log_heap: src/assignment_log.c pq_heap.o list.o user_input.o
	mkdir -p build/
	cc -o build/assignment_log_heap -g src/assignment_log.c build/pq_heap.o build/list.o build/user_input.o

user_input.o: src/user_input.c lib/user_input.h
	mkdir -p build/
	cc -o build/user_input.o -c -g src/user_input.c

pq_heap.o: src/pq_heap.c lib/pq_heap.h
	mkdir -p build/
	cc -o build/pq_heap.o -c -g src/pq_heap.c

pq.o: src/pq.c lib/pq.h list.o
	mkdir -p build/
	cc -o build/pq.o -c -g src/pq.c

list.o: src/list.c lib/list.h
	mkdir -p build/
	cc -o build/list.o -c -g src/list.c

clean:
	rm -rf build/
