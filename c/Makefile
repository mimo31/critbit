CC = gcc
BINARY = critbit-tests

critbit-tests: critbit.h critbit.c tests.c
	$(CC) critbit.c tests.c -g -fsanitize=address -Wall -Wextra -o $(BINARY)
