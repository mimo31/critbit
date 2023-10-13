CC = gcc
BINARY = critbit-tests

critbit-tests: critbit.h critbit-struct.h critbit.c critbit-print.h critbit-print.c tests.c
	$(CC) critbit.c critbit-print.c tests.c -g -fsanitize=address -Wall -Wextra -o $(BINARY)
