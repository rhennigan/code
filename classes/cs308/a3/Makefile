deadlock_test: donuts.h proddonuts consdonuts deadlock_test.c
	cc -o deadlock_test deadlock_test.c
proddonuts consdonuts: donuts.h proddonuts.o consdonuts.o utilities.o
	cc -o proddonuts proddonuts.o utilities.o
	cc -o consdonuts consdonuts.o utilities.o
consdonuts.o: donuts.h consdonuts.c
	cc -c consdonuts.c
proddonuts.o: donuts.h proddonuts.c
	cc -c proddonuts.c
utilities.o:  utilities.c
	cc -c utilities.c
clean:
	rm *.o proddonuts consdonuts deadlock_test .conslk .prodlk log/* *~
