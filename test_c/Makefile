LEVEL = ..
MP3=1
TESTS	= $(wildcard *.c)
test:	$(TESTS:%.c=%.test)

all-exe: $(TESTS:.c=.exe)

%.ll: %.c
	clang -emit-llvm -S $< -o $*.ll -Xclang -disable-O0-optnone 

%.exe: %.s
	$(CC) -g $+ -o $@

include ../Makefile.common

.PHONY: test %.test clean realclean %.run project
