LEVEL = ..
MP3=1
TESTS	= $(wildcard *.cl)
test:	$(TESTS:%.cl=%.test)

all-exe: $(TESTS:.cl=.exe)

.PHONY: test %.test clean realclean %.run project

include ../Makefile.common