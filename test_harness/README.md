# Raft KLEE Symbolic Test Harness

This directory contains symbolic testing files for the Raft consensus algorithm using KLEE.

## Files

- `raft_klee_test.c` - KLEE symbolic test harness for Raft
- `Makefile` - Compilation instructions for KLEE
- `analyze_klee_results.py` - Python script to analyze KLEE test results

## Building and Running

### KLEE Symbolic Test

To build and run the KLEE symbolic test:

```
make klee
make run-klee
```

Alternatively, you can use the provided Docker script:

```
./run_docker.bat  # Windows
./run_docker.sh   # Linux/Mac (if available)
```

This will generate KLEE test cases in the `klee-out-*` directory.

## Test Coverage

The symbolic test harness tests for:

1. **Leader Election Safety**: Ensures no more than one leader exists in the same term
2. **Leader Election Liveness**: Ensures a leader is eventually elected
3. **Message Processing**: Tests handling of various message types
4. **Log Replication**: Verifies log consistency across the cluster

## Key Properties Verified

- Leader Uniqueness: No more than one leader in the same term
- Multiple Rounds: Tests multiple rounds of message processing and leader election
- Symbolic Network: Uses symbolic delays and drop probabilities to model network issues
- Log Consistency: Ensures all logs are consistent across nodes

## Interpreting Results

- If KLEE reports violations, it means potential bugs have been found in the Raft implementation
- Review the generated test cases in the `klee-out-*` directory to understand failure conditions
- Counterexamples are provided whenever an assertion fails 