CFLAGS=-std=gnu99 -pedantic -g -w

sslsniff: sslsniff.o
	gcc $(CFLAGS) -o sslsniff sslsniff.o -lpcap

sslsniff.o: sslsniff.c
	gcc $(CFLAGS) -c -o sslsniff.o sslsniff.c
	
clean:
	rm -f sslsniff.o
