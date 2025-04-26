CC = gcc
KLEE_CC = clang
CFLAGS = -g -O0 -Wall -Wextra
KLEE_CFLAGS = -g -O0 -emit-llvm -Wall -Wextra

KLEE_TARGETS = raft_klee_test.bc

.PHONY: all clean klee

all: klee

klee: $(KLEE_TARGETS)

raft_klee_test.bc: raft_klee_test.c
	$(KLEE_CC) $(KLEE_CFLAGS) -c -o $@ $<

clean:
	rm -f $(KLEE_TARGETS) *.o
	rm -rf klee-out-*

run-klee: raft_klee_test.bc
	klee --libc=uclibc --posix-runtime $< 