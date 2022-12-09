#
# Makefile for Proxy Lab 
#
# You may modify this file any way you like (except for the handin
# rule). Autolab will execute the command "make" on your specific 
# Makefile to build your proxy from sources.
#
CC = gcc
CFLAGS = -g -Wall -O3
LDFLAGS = -lpthread

all: proxy

csapp.o: csapp.c csapp.h
	$(CC) $(CFLAGS) -c csapp.c

parser.o: parser.c parser.h
	$(CC) $(CFLAGS) -c parser.c

cache.o: cache.c cache.h csapp.h
	$(CC) $(CFLAGS) -c cache.c

proxy.o: proxy.c csapp.h parser.h
	$(CC) $(CFLAGS) -c proxy.c

proxy: proxy.o csapp.o parser.o cache.o
	$(CC) $(CFLAGS) proxy.o csapp.o parser.o cache.o -o proxy $(LDFLAGS)

parser_test: parser_test.c parser.o
	$(CC) $(CFLAGS) parser_test.c parser.o -o parser_test $(LDFLAGS)

# Creates a tarball in ../proxylab-handin.tar that you should then
# hand in to Autolab. DO NOT MODIFY THIS!
handin:
	(make clean; cd ..; tar czvf proxylab-handin.tar.gz proxylab-handout)

clean:
	rm -f *~ *.o proxy core *.tar *.zip *.gzip *.bzip *.gz


