vec_test: vec_test.c vectors.o
	mkdir -p build/
	cc -o build/vec_test vec_test.c build/vectors.o -lm

vectors.o: vectors.c vectors.h
	mkdir -p build/
	cc -o build/vectors.o -c -g vectors.c -lm

