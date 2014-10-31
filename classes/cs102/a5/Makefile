airport: src/airport.c queue.o list.o user_input.o
	cc -o airport -g src/airport.c queue.o list.o user_input.o
queue_test: src/queue_test.c queue.o list.o
	cc -o queue_test -g src/queue_test.c queue.o list.o
queue.o: src/queue.c lib/queue.h list.o
	cc -c -g src/queue.c
list.o: src/list.c lib/list.h
	cc -c -g src/list.c
user_input.o: src/user_input.c lib/user_input.h
	cc -c -g src/user_input.c
clean:
	rm *.o
