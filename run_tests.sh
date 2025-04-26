#!/bin/bash

# Script to run Raft tests with and without KLEE

echo "======================================================="
echo "  Running Raft Tests                                   "
echo "======================================================="

# Change to test_harness directory
cd test_harness || { echo "Could not find test_harness directory"; exit 1; }

# Clean any previous builds
echo "Cleaning previous builds..."
make clean

# Build and run regular test
echo -e "\n======================================================="
echo "  Building and running regular Raft test                 "
echo "======================================================="
make all
echo -e "\nRunning regular test:"
./raft_test

# Build and run KLEE test if KLEE is available
echo -e "\n======================================================="
echo "  Building and running KLEE symbolic test                "
echo "======================================================="

# Check if KLEE is available directly
if command -v klee &> /dev/null; then
    echo "KLEE found in system path, running directly..."
    make klee
    make run-klee
# Check if Docker is available
elif command -v docker &> /dev/null; then
    echo "KLEE not found in path, attempting to run via Docker..."
    echo "Building KLEE bytecode..."
    docker run --rm -v "$(pwd):/workdir" klee/klee:latest bash -c "cd /workdir && clang -I /klee/include -emit-llvm -c -g -O0 -Wno-everything raft_klee_test.c -o raft_klee_test.bc"
    
    echo "Running KLEE symbolic execution..."
    docker run --rm -v "$(pwd):/workdir" klee/klee:latest bash -c "cd /workdir && klee --libc=uclibc --posix-runtime raft_klee_test.bc"
else
    echo "Error: Neither KLEE nor Docker found. Cannot run symbolic tests."
    exit 1
fi

# Check results
echo -e "\n======================================================="
echo "  Test Results                                          "
echo "======================================================="

if [ -d "klee-out-0" ]; then
    echo "KLEE tests completed. Results in klee-out-* directories."
    echo "Number of test cases: $(ls klee-out-*/test*.ktest 2>/dev/null | wc -l)"
    echo "Number of errors found: $(ls klee-out-*/test*.err 2>/dev/null | wc -l)"
    
    # Check for specific assertion failures
    if grep -q "assertion failed" klee-out-*/warnings.txt 2>/dev/null; then
        echo -e "\nWarning: Some assertions failed. Check klee-out-*/warnings.txt for details."
    fi
else
    echo "No KLEE test results found."
fi

echo -e "\nAll tests completed." 