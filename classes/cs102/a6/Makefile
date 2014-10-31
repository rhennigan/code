stock_ledger: src/stock_ledger.c deque.o user_input.o
	cc -o stock_ledger -g src/stock_ledger.c -lcurl -lm deque.o list.o user_input.o

user_input.o: src/user_input.c lib/user_input.h
	cc -c -g src/user_input.c

list.o: src/list.c lib/list.h
	cc -c -g src/list.c

deque.o: src/deque.c lib/deque.h list.o
	cc -c -g src/deque.c

clean:
	rm *.o *.csv
