LEVEL = ..
MP3=1
TESTS	= $(wildcard *.c)
test:	$(TESTS:%.c=%.test)

all-exe: $(TESTS:.c=.exe)

OPTFLAGS = -load-pass-plugin=$(UNIT_PORJECT) -passes="function(mem2reg,instcombine,simplifycfg,adce),inline,globaldce,function(sroa,early-cse,unit-sccp,jump-threading,correlated-propagation,simplifycfg,instcombine,simplifycfg,reassociate,unit-licm,adce,simplifycfg,instcombine),globaldce" 
# OPTFLAGS = -load-pass-plugin=$(UNIT_PORJECT) -passes="function(mem2reg,instcombine,simplifycfg,adce,unit-sccp)" 
OPTREFFLAGS = -load-pass-plugin=$(UNIT_PORJECT) -passes="function(mem2reg,instcombine,simplifycfg,adce)" 
# OPTREFFLAGS = -passes="sccp"
OPT0FLAGS = -passes="function(mem2reg,instcombine,simplifycfg,adce),inline,globaldce"
# OPT0FLAGS = -passes="function(mem2reg)"
# OPTREFFLAGS = -passes="function(mem2reg,instcombine,simplifycfg,adce),inline,globaldce,function(sroa,early-cse,unit-sccp,jump-threading,correlated-propagation,simplifycfg,instcombine,simplifycfg,reassociate,unit-licm,adce,simplifycfg,instcombine),globaldce"

%.ll: %.c
	clang -emit-llvm -S $< -o $*.ll -Xclang -disable-O0-optnone 

%.exe: %.s
	$(CC) -g $+ -o $@

include ../Makefile.common

.PHONY: test %.test clean realclean %.run project
