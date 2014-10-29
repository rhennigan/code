mat_test: mat_test.c math/matrices.o math/vectors.o math/utils.o
	mkdir -p build/
	cc -std=gnu99 -o build/mat_test mat_test.c build/math/matrices.o build/math/vectors.o build/math/utils.o -lm

vec_test: vec_test.c math/vectors.o math/utils.o
	mkdir -p build/
	cc -o build/vec_test vec_test.c build/math/vectors.o build/math/utils.o -lm

math/matrices.o: math/matrices.c math/matrices.h math/vectors.o
	mkdir -p build/math/
	cc -std=gnu99 -o build/math/matrices.o -c -g math/matrices.c -lm

math/vectors.o: math/vectors.c math/vectors.h math/utils.o
	mkdir -p build/math/
	cc -o build/math/vectors.o -c -g math/vectors.c -lm

math/utils.o: math/utils.c math/utils.h
	mkdir -p build/math/
	cc -o build/math/utils.o -c -g math/utils.c

clean:
	rm build/*.o
	rm build/math/*.o

reset:
	rm -rf build/
	rm *~
