all: macc macc8

CFLAGS += -Wall -pedantic -g -Os
LDLIBS += -lgc

macc: macc.o
macc8: macc8.o

clean:
	rm -f *.o macc macc8

.PHONY: clean all
