# Evaluation of Raft Algorithm using KLEE Symbolic Execution

This document outlines how the evaluation criteria from the COMP_790 Proposal have been implemented using KLEE symbolic execution.

## Phase 1 Evaluation Implementation

The evaluation implements the research questions specified in the proposal:

### 1. Safety Properties

**Research Question**: Does Raft maintain leader uniqueness under adversarial delay scenarios?

**Implementation**:
- The safety property of leader uniqueness (at most one leader per term) is implemented in the `verify_safety_properties` function.
- This function checks each term and asserts that there is at most one leader per term using `klee_assert(leaders_in_term <= 1)`.
- Split-brain scenarios are tracked using the `split_brain_detected` field in the metrics structure.

### 2. Liveness Properties

**Research Question**: Does Raft guarantee that a leader is eventually elected under adversarial conditions?

**Implementation**:
- The liveness property is implemented in the `verify_liveness_properties` function.
- It asserts that after a reasonable number of rounds, at least one node should be in the leader state.
- This is checked with `klee_assert(has_leader || "No leader elected - liveness property violation")`.
- Election success rate is tracked using the metrics structure.

## Symbolic Variables

As specified in the proposal, the following symbolic variables have been integrated:

1. **Election Timeout**:
   ```c
   node->electionTimeout = klee_range(150, 300, "electionTimeout");
   ```

2. **Heartbeat Interval**:
   ```c
   node->heartbeatTimeout = klee_range(50, 200, "heartbeatTimeout");
   ```

3. **Network Delays**:
   ```c
   network.message_delay[i][j] = klee_range(0, 100, "message_delay");
   ```

4. **Message Drops**:
   ```c
   network.message_drop[i][j] = klee_range(0, 1, "message_drop");
   ```

## Attack Scenarios

Two adversarial scenarios have been implemented:

1. **Delayed Heartbeats**:
   - Implemented by adding a symbolic heartbeat delay parameter:
   ```c
   if (use_delayed_heartbeats) {
       heartbeat_delay = klee_range(0, 3 * max_heartbeat_timeout, "heartbeat_delay");
   }
   ```
   - The delay is applied in the `process_append_entries` function.

2. **Randomized Election Timeouts**:
   - Implemented by randomizing the election timeout values:
   ```c
   if (use_randomized_timeouts) {
       for (int i = 0; i < NUM_NODES; i++) {
           int base_timeout = nodes[i].electionTimeout;
           nodes[i].electionTimeout = klee_range(base_timeout, 2 * base_timeout, "randomized_timeout");
       }
   }
   ```

## Metrics Collection

The following metrics are collected during execution:

1. **Election Success Rate**:
   - Tracked using `election_success_count` and `election_attempt_count`
   - Reported in the analysis output

2. **Leader Election Time**:
   - Tracked using `election_rounds_elapsed` when a leader is elected
   - Stored in `leader_election_time`

3. **Split Brain Detection**:
   - Tracked when multiple leaders are detected in the same term
   - Stored in `split_brain_detected`

## Running the Evaluation

To run the evaluation:

1. Execute the `run_docker.bat` script, which will:
   - Compile and run the standard Raft test
   - Compile and run the KLEE symbolic test
   - Analyze the results using the Python analysis script

2. The results will be written to `klee_analysis_report.txt` with metrics on:
   - Safety property violations
   - Liveness property violations
   - Election success rate
   - Time taken to elect a leader

## Extended Evaluation

This implementation satisfies the Phase 1 evaluation requirements. The final evaluation would extend to include log replication under adversarial delays, which would be implemented in a similar fashion with additional assertions for log consistency across a majority of nodes. 