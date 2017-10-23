CC = gcc
FLAGS = -m32 -nostdlib -s -static -Wl,--build-id=none
CFLAGS = -c $(FLAGS)

fac : fac.s stubstart.s
	$(CC) $(FLAGS) $^ -o $@

.PHONY: clean

clean : 
	rm fac
