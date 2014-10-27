vec_test: vec_test.c vectors.o utils.o
	mkdir -p build/
	cc -o build/vec_test vec_test.c build/vectors.o build/utils.o -lm

vectors.o: vectors.c vectors.h utils.o
	mkdir -p build/
	cc -o build/vectors.o -c -g vectors.c -lm

utils.o: utils.c utils.h
	mkdir -p build/
	cc -o build/utils.o -c -g utils.c

clean:
	rm build/*.o
