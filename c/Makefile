CC = gcc
BINARY = critbit-tests

critbit-tests: critbit.h critbit-struct.h critbit.c critbit-debug.h critbit-debug.c tests.c
	$(CC) critbit.c critbit-debug.c tests.c -g -O3 -Wall -Wextra -o $(BINARY)
