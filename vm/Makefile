all: macc

%.o: CFLAGS+= -Wall -pedantic -g
macc: LDLIBS +=-lgc

clean:
	rm -f *.o macc

.PHONY: clean all
