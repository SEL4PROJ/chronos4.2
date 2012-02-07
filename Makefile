CC=gcc
CFLAGS=-g -O2 -DMEM_FREE -Wall -Wstrict-prototypes
#CFLAGS=-g -D_DEBUG -DMEM_FREE 
#CFLAGS=-g -DMEM_FREE
#CFLAGS=-g -O2 -U_FORTIFY_SOURCE
#CFLAGS=-pg

SS_SRC=$(wildcard imm/*.c)
SRC=main.c common.c isa.c readfile.c cfg.c tcfg.c loops.c options.c \
pipeline.c exegraph.c estimate.c cache.c bpred.c ilp.c \
scp_tscope.c scp_address.c scp_cache.c jptable.c\
infeasible.c reg.c symexec.c conflicts.c infdump.c address.c unicache.c $(SS_SRC)
CPP_SRC=mem_value.cpp
OBJ=$(SRC:.c=.o) $(CPP_SRC:.cpp=.o)

all: est

est: $(OBJ)
	$(CC) $(CFLAGS) -lstdc++ $^ -o $@

clean:
	rm -rf .deps/
	rm -f est *.o imm/*.o

### Dependency generation from http://mad-scientist.net/make/autodep.html
DEPDIR = .deps
df = $(DEPDIR)/$(*)
%.o: %.c
	$(COMPILE.c) -MD -o $@ $<
	@mkdir -p `dirname $(df).P`; \
		cp $*.d $(df).P; \
		sed -e 's/#.*//;s/^[^:]*://;s/\\$$//;s/ *$$//;s/^ *//;/^$$/d;s/$$/:/' < $*.d >> $(df).P; \
		rm -f $*.d
-include $(SRC:%.c=$(DEPDIR)/%.P)
### End dependency generation magic.
