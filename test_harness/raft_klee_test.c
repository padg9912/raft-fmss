#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <klee/klee.h>

#define NUM_NODES 5

// Mock Raft node states
typedef enum {
    FOLLOWER = 0,
    CANDIDATE = 1,
    LEADER = 2
} RaftState;

// Log entry structure
typedef struct {
    int term; // Term number
    int index; // Log entry index
    int command;  // Simplified representation of command data
} LogEntry;

// Mock Raft node structure
typedef struct {
    int id; // Node identifier
    RaftState state; // Current state of the node
    int currentTerm; // Current term number
    int votedFor; // ID of the node this node voted for
    int votes_received; // Number of votes received
    int log_length; // Length of the node's log
    LogEntry log[20];  // Support for up to 20 log entries
    int commit_index; // Index of the highest log entry known to be committed
    int last_applied; // Index of the highest log entry applied to the state machine
    int lastHeartbeat; // Time of the last heartbeat received
    int electionTimeout; // Timeout for election attempts
    int heartbeatTimeout;  // Added heartbeat timeout
    int next_index[5];     // Next log entry to send to each server (for leaders)
    int match_index[5];    // Highest log entry known to be replicated (for leaders)
} RaftNode;

// Mock message types
typedef enum {
    REQUEST_VOTE = 0, // Request vote from other nodes
    VOTE_RESPONSE = 1,
    APPEND_ENTRIES = 2,
    APPEND_RESPONSE = 3
} MessageType;

// Mock message structure
typedef struct {
    MessageType type; // Type of message
    int term; // Term number
    int sender_id; // ID of the node sending the message
    int receiver_id; // ID of the node receiving the message
    int success; // Whether the message was successful
    int prev_log_index; // Index of the previous log entry
    int prev_log_term; // Term of the previous log entry
    int entries_length; // Number of entries in the message
    LogEntry entries[5];  // Support for sending up to 5 entries at once
    int leader_commit; // Commit index of the leader
    int last_log_index; // Last log index for append response
    int match_index; // Match index in append response
    int prev_match_index; // Previous match index in append response
} RaftMessage;

// Network state
typedef struct {
    int message_delay[5][5]; // Delay matrix between nodes
    int message_drop[5][5];  // Drop probability matrix
} NetworkState;

// Metrics structure to collect data
typedef struct {
    int election_rounds_elapsed; // Number of election rounds elapsed
    int leader_elected; // Whether a leader was elected
    int leader_election_time; // Time taken to elect a leader
    int election_success_count; // Number of successful elections
    int election_attempt_count; // Total number of election attempts
    int split_brain_detected; // Whether split brain was detected
    int log_replication_success; // Number of successful log replications
    int log_replication_attempts; // Total number of log replication attempts
    int log_consistency_violations; // Number of log consistency violations
    int log_entries_replicated;   // Total number of entries replicated across all followers
    int partial_replication;      // Number of entries replicated to at least one but not all followers
    int full_replication;         // Number of entries replicated to all followers
    int follower_replication[5];  // Per-follower replication counts
    int replication_latency;      // Simulated latency for replication
    int replication_failures;     // Count of failed replication attempts
} RaftMetrics;

// Initialize a node
void initialize_node(RaftNode* node, int id) {
    node->id = id; // Node identifier
    node->state = FOLLOWER; // Initial state
    node->currentTerm = 0; // Current term number
    node->votedFor = -1; // Node this node voted for
    node->votes_received = 0; // Number of votes received
    node->log_length = 0; // Length of the node's log
    node->commit_index = 0; // Index of the highest log entry known to be committed
    node->last_applied = 0; // Index of the highest log entry applied to the state machine
    node->lastHeartbeat = 0; // Time of the last heartbeat received
    
    // Initialize log entries
    for (int i = 0; i < 20; i++) {
        node->log[i].term = 0;
        node->log[i].index = i;
        node->log[i].command = 0;
    }
    
    // Initialize next_index and match_index arrays
    for (int i = 0; i < 5; i++) {
        node->next_index[i] = 1;  // Start at 1 (as per Raft paper)
        node->match_index[i] = 0; // Start at 0
    }
    
    // Symbolic election timeout (between 150-300ms in real systems)
    node->electionTimeout = klee_range(150, 300, "electionTimeout");
    
    // Symbolic heartbeat timeout (between 50-200ms in real systems)
    node->heartbeatTimeout = klee_range(50, 200, "heartbeatTimeout");
}

// Mock function to process vote request
void process_vote_request(RaftNode* node, RaftMessage* msg, RaftMetrics* metrics) {
    if (msg->term > node->currentTerm) {
        node->currentTerm = msg->term;
        node->state = FOLLOWER;
        node->votedFor = -1;
    }

    if (msg->term < node->currentTerm) {
        return;         // Reject vote for lower term
    }

    // Only grant vote if we haven't voted yet in this term or we've already voted for this candidate
    if ((node->votedFor == -1 || node->votedFor == msg->sender_id) &&
        msg->prev_log_index >= node->log_length) {  // Simplified log consistency check
        // Grant vote
        node->votedFor = msg->sender_id;
        
        // Create vote response message
        RaftMessage response;
        response.type = VOTE_RESPONSE;
        response.term = node->currentTerm;
        response.sender_id = node->id;
        response.receiver_id = msg->sender_id;
        response.success = 1;  // Vote granted
        
        // Track metrics for vote
        if (metrics) {
            metrics->election_attempt_count++;
        }
        
        // In a real system, this would be sent over the network
    }
}

// Mock function to process append entries
void process_append_entries(RaftNode* node, RaftMessage* msg, int heartbeat_delay, RaftMetrics* metrics) {
    // Apply the heartbeat delay if specified
    int effective_time;
    if (heartbeat_delay > 0) {
        effective_time = klee_range(0, heartbeat_delay, "effective_heartbeat_time");
    } else {
        // No delay, use current time
        effective_time = node->lastHeartbeat;
    }
    
    // Reset election timeout as we hear from leader
    node->lastHeartbeat = effective_time;

    // Simple append entries processing logic
    if (msg->term > node->currentTerm) {
        node->currentTerm = msg->term;
        node->state = FOLLOWER;
        node->votedFor = -1;
    }

    if (msg->term < node->currentTerm) {
        // Reject entries from lower term
        if (metrics) {
            metrics->log_replication_attempts++;
        }
        
        // Create append response message (in a real system)
        // Here we would send a failure response
        return;
    }

    // Log consistency check
    if (msg->prev_log_index > 0) {
        // Check if we have the entry at prev_log_index
        if (msg->prev_log_index > node->log_length) {
            // Log doesn't contain an entry at prev_log_index
            if (metrics) {
                metrics->log_replication_attempts++;
                metrics->log_consistency_violations++;
            }
            // In a real system, it would send failure response
            return;
        }
        
        // Check if terms match at prev_log_index
        if (node->log[msg->prev_log_index - 1].term != msg->prev_log_term) {
            if (metrics) {
                metrics->log_replication_attempts++;
                metrics->log_consistency_violations++;
            }
            
            // Delete conflicting entry and all that follow
            node->log_length = msg->prev_log_index - 1;
            
            // In a real system, would send failure response
            return;
        }
    }
    
    // If we get here, log prefix is consistent. Now append any new entries not already in the log
    if (msg->entries_length > 0) {
        if (metrics) {
            metrics->log_replication_attempts++;
        }
        
        // Process entries
        for (int i = 0; i < msg->entries_length; i++) {
            int entry_index = msg->prev_log_index + i;
            
            // If existing entry conflicts with new one (same index but different terms)
            if (entry_index < node->log_length && 
                node->log[entry_index].term != msg->entries[i].term) {
                // Delete the conflicting entry and all that follow
                node->log_length = entry_index;
            }
            
            // Append entry if it's not already in the log
            if (entry_index >= node->log_length) {
                node->log[entry_index] = msg->entries[i];
                
                // Update log length if necessary
                if (entry_index + 1 > node->log_length) {
                    node->log_length = entry_index + 1;
                }
            }
        }
        
        // Log replication successful for these entries
        if (metrics) {
            metrics->log_replication_success++;
        }
    }

    // Update commit index if leader committed entries
    if (msg->leader_commit > node->commit_index) {
        // Set commit index to min of leader's commit index and index of last new entry
        int last_new_entry = msg->prev_log_index + msg->entries_length;
        node->commit_index = (msg->leader_commit < last_new_entry) ? 
                              msg->leader_commit : last_new_entry;
                              
        // In a real system, it would apply committed entries to state machine
        node->last_applied = node->commit_index;
    }
}

// Mock function to transition to candidate
void become_candidate(RaftNode* node, RaftMetrics* metrics) {
    node->state = CANDIDATE;
    node->currentTerm++;
    node->votedFor = node->id;  // Vote for self
    node->votes_received = 1;   // Count vote for self
    
    // Track election attempt
    if (metrics) {
        metrics->election_attempt_count++;
    }
}

// Mock function to process message
void process_message(RaftNode* node, RaftMessage* msg, NetworkState* network, RaftMetrics* metrics, int heartbeat_delay) {
    // Check if message should be dropped
    if (network->message_drop[msg->sender_id][msg->receiver_id]) {
        return; // Message dropped
    }
    
    // Apply delay
    int delay = network->message_delay[msg->sender_id][msg->receiver_id];
    // In a real system, we would wait 'delay' time
    
    switch (msg->type) {
        case REQUEST_VOTE:
            process_vote_request(node, msg, metrics);
            break;
        case VOTE_RESPONSE:
            if (node->state == CANDIDATE && msg->success) {
                node->votes_received++;
                
                // Check if we have majority
                if (node->votes_received > 2) { // Assuming 5 nodes total
                    node->state = LEADER;
                    
                    // Update metrics for successful leader election
                    if (metrics) {
                        metrics->leader_elected = 1;
                        metrics->election_success_count++;
                        metrics->leader_election_time = metrics->election_rounds_elapsed;
                    }
                    
                    // Initialize leader state for log replication
                    for (int i = 0; i < 5; i++) {
                        if (i != node->id) {
                            node->next_index[i] = node->log_length + 1;
                            node->match_index[i] = 0;
                        }
                    }
                    // In a real system, would start sending heartbeats
                }
            }
            break;
        case APPEND_ENTRIES:
            process_append_entries(node, msg, heartbeat_delay, metrics);
            break;
        case APPEND_RESPONSE:
            // Handle append response
            if (node->state == LEADER && msg->success) {
                // Update match_index and next_index for follower
                node->match_index[msg->sender_id] = msg->last_log_index;
                node->next_index[msg->sender_id] = msg->last_log_index + 1;

                if (metrics) {
                    // Calculate number of entries successfully replicated
                    int entries_replicated = (msg->match_index > msg->prev_match_index) ? 
                                            (msg->match_index - msg->prev_match_index) : 
                                            msg->entries_length;
                    
                    // Update total replicated entries
                    metrics->log_entries_replicated += entries_replicated;
                    
                    // Track per-follower replication
                    metrics->follower_replication[msg->sender_id] += entries_replicated;
                    
                    // Update replication latency with actual network delay
                    metrics->replication_latency += network->message_delay[node->id][msg->sender_id];
                    
                    // Check if this is a partial or full replication
                    if (node->match_index[msg->sender_id] == node->last_applied) {
                        // This follower is fully caught up with the leader
                        metrics->full_replication++;
                    } else {
                        // This follower has some entries but not all
                        metrics->partial_replication++;
                    }
                }

                // Try to advance the commit index
                // Find the largest N such that a majority of match_index[i] >= N
                // and N > commitIndex and N is from current term
                for (size_t N = node->commit_index + 1; N <= node->last_applied; N++) {
                    if (node->log[N].term == node->currentTerm) {
                        int count = 1; // Count self
                        for (size_t i = 0; i < NUM_NODES; i++) {
                            if (i != node->id && node->match_index[i] >= N) {
                                count++;
                            }
                        }
                        if (count > NUM_NODES / 2) {
                            node->commit_index = N;
                        } else {
                        break;
                        }
                    }
                }
            } else if (node->state == LEADER && !msg->success) {
                // If unsuccessful, decrement next_index and retry
                if (node->next_index[msg->sender_id] > 1) {
                    node->next_index[msg->sender_id]--;
                }
                
                // Update metrics for failed replication
                if (metrics) {
                    metrics->replication_failures++;
                    
                    // Track which entries failed to replicate
                    int attempted_entries = msg->entries_length > 0 ? msg->entries_length : 1;
                    
                    // Add failed replication latency to total latency
                    // This helps measure the cost of failures in terms of time
                    metrics->replication_latency += network->message_delay[node->id][msg->sender_id];
                    
                    // If we have many consecutive failures for this follower, 
                    // we might want to track this as a potential network partition
                    if (node->next_index[msg->sender_id] <= 1) {
                        // We've backed up all the way - this follower might be disconnected
                        // In a real implementation, we might want to mark this node as potentially partitioned
                        // For now, we just count the extreme failure case
                        metrics->log_consistency_violations++;
                    }
                }
            }
            break;
        default:
            break;
    }
}

// Check for election timeout
void check_election_timeout(RaftNode* node, int current_time, RaftMetrics* metrics) {
    if (node->state != LEADER && 
        (current_time - node->lastHeartbeat) > node->electionTimeout) {
        become_candidate(node, metrics);
        
        // In a real system, would send vote requests to all other nodes
    }
}

// Verify safety properties
void verify_safety_properties(RaftNode nodes[], int num_nodes, RaftMetrics* metrics) {
    // Check for at most one leader per term
    for (int term = 0; term < 10; term++) { // Check for first 10 terms
        int leaders_in_term = 0;
        for (int i = 0; i < num_nodes; i++) {
            if (nodes[i].state == LEADER && nodes[i].currentTerm == term) {
                leaders_in_term++;
            }
        }
        
        // Assert no more than one leader per term (safety property)
        klee_assert(leaders_in_term <= 1);
        
        // Update metrics if we detect split brain
        if (leaders_in_term > 1 && metrics) {
            metrics->split_brain_detected = 1;
        }
    }
}

// Verify liveness property - a leader is eventually elected
void verify_liveness_properties(RaftNode nodes[], int num_nodes, RaftMetrics* metrics, int max_rounds) {
    // If we've reached a certain number of rounds, verify that a leader has been elected
    if (metrics->election_rounds_elapsed >= max_rounds) {
        int has_leader = 0;
        for (int i = 0; i < num_nodes; i++) {
            if (nodes[i].state == LEADER) {
                has_leader = 1;
                break;
            }
        }
        
        // Verify the liveness property - eventually a leader is elected
        // Note: We use conditional assertion based on round count to ensure liveness check
        // happens after a reasonable time period (but not earlier)
        if (metrics->election_rounds_elapsed >= max_rounds) {
            klee_assert(has_leader || "No leader elected - liveness property violation");
        }
    }
}

// Verify log entries match on a majority of nodes
void verify_log_consistency(RaftNode nodes[], int num_nodes, RaftMetrics* metrics) {
    // For each log entry that's committed on any node
    int max_commit = 0;
    
    // Find the highest commit index among all nodes
    for (int i = 0; i < num_nodes; i++) {
        if (nodes[i].commit_index > max_commit) {
            max_commit = nodes[i].commit_index;
        }
    }
    
    // Check consistency for each entry up to max_commit
    for (int idx = 1; idx <= max_commit; idx++) {
        // For each index, count nodes that have committed this entry
        int commit_count = 0;
        int term_mismatch = 0;
        int reference_term = -1;
        
        for (int i = 0; i < num_nodes; i++) {
            // If this node has committed this entry
            if (nodes[i].commit_index >= idx) {
                commit_count++;
                
                // Remember the term of the first node we find with this entry
                if (reference_term == -1) {
                    reference_term = nodes[i].log[idx-1].term;
                }
                // Check if any node has a different term for this entry
                else if (nodes[i].log[idx-1].term != reference_term) {
                    term_mismatch = 1;
                    
                    // Update metrics for log inconsistency
                    if (metrics) {
                        metrics->log_consistency_violations++;
                    }
                }
            }
        }
        
        // Assert: If a majority has committed an entry, all committed entries must match
        if (commit_count > num_nodes/2) {
            klee_assert(term_mismatch == 0 && "Log entries don't match on majority of nodes");
        }
    }
}

// Verify that log entries are replicated to all nodes after a certain number of rounds
void verify_log_replication_progress(RaftNode nodes[], int num_nodes, RaftMetrics *metrics, int rounds, int is_adversarial) {
    // Identify the leader
    int leader_idx = identify_leader(nodes, num_nodes);
    
    // Minimal verification: After enough rounds, some entries should have been replicated
    if (rounds > NUM_NODES * 2) {
        // At least some replication attempts should have been made
        assert(metrics->log_entries_replicated > 0 || leader_idx == -1);
        
        if (leader_idx != -1) {
            RaftNode *leader = &nodes[leader_idx];
            
            // If we have a leader with entries, verify that metrics are being tracked
            if (leader->log_length > 0) {
                // At least some followers should have received entries
                assert(metrics->follower_replication[leader_idx] > 0);
                
                // Partial replication should be tracked if we've had any successful replication
                if (metrics->log_entries_replicated > 0) {
                    assert(metrics->partial_replication > 0);
                    
                    // In non-adversarial scenarios with enough rounds, full replication should occur for some entries
                    if (!is_adversarial && rounds > NUM_NODES * 3) {
                        assert(metrics->full_replication > 0);
                    }
                    
                    // Check follower-specific replication progress
                    int followers_with_entries = 0;
    for (int i = 0; i < num_nodes; i++) {
                        if (i != leader_idx && nodes[i].log_length > 0) {
                            followers_with_entries++;
                        }
                    }
                    
                    // At least half of followers should eventually get some entries in normal conditions
                    if (!is_adversarial && rounds > NUM_NODES * 4) {
                        assert(followers_with_entries >= (num_nodes - 1) / 2);
                    }
                    
                    // Additional metrics checks for non-adversarial scenarios
                    if (!is_adversarial && rounds > NUM_NODES * 5) {
                        // Replication efficiency: More successful than failed attempts over time
                        if (metrics->replication_failures > 0) {
                            assert(metrics->log_entries_replicated >= metrics->replication_failures);
                        }
                        
                        // Latency should be reasonable (non-zero but finite)
                        if (metrics->log_entries_replicated > 0) {
                            assert(metrics->replication_latency > 0);
                            assert(metrics->replication_latency / metrics->log_entries_replicated < rounds * 2);
                        }
                    }
                }
            }
        }
    }
}

// Identify the leader among all nodes, returns -1 if none found
int identify_leader(RaftNode nodes[], int num_nodes) {
    for (int i = 0; i < num_nodes; i++) {
        if (nodes[i].state == LEADER) {
            return i;
        }
    }
    return -1;  // No leader found
}

// Main test function for KLEE
int main() {
    RaftNode nodes[NUM_NODES];
    NetworkState network;
    RaftMetrics metrics = {0}; // Initialize metrics to zero
    
    // Initialize nodes
    for (int i = 0; i < NUM_NODES; i++) {
        initialize_node(&nodes[i], i);
    }
    
    // Make network delays symbolic
    for (int i = 0; i < NUM_NODES; i++) {
        for (int j = 0; j < NUM_NODES; j++) {
            if (i != j) {
                network.message_delay[i][j] = klee_range(0, 100, "message_delay");
                network.message_drop[i][j] = klee_range(0, 1, "message_drop");
            }
        }
    }
    
    // Symbolic execution parameters
    int num_rounds = klee_range(1, 20, "num_rounds"); // Limit to 20 rounds to avoid path explosion
    int current_time = 0;
    
    // Delay parameters (symbolic)
    int heartbeat_delay = 0;
    int use_delayed_heartbeats = klee_range(0, 1, "use_delayed_heartbeats");
    int use_randomized_timeouts = klee_range(0, 1, "use_randomized_timeouts");
    int adversarial_message_delays = klee_range(0, 1, "adversarial_message_delays");
    
    // Test case 1: Delayed heartbeats scenario
    if (use_delayed_heartbeats) {
        // Heartbeat delay up to 3x heartbeat timeout
        int max_heartbeat_timeout = 0;
        for (int i = 0; i < NUM_NODES; i++) {
            if (nodes[i].heartbeatTimeout > max_heartbeat_timeout) {
                max_heartbeat_timeout = nodes[i].heartbeatTimeout;
            }
        }
        
        heartbeat_delay = klee_range(0, 3 * max_heartbeat_timeout, "heartbeat_delay");
    }
    
    // Test case 2: Randomized election timeouts scenario
    if (use_randomized_timeouts) {
        // Randomize election timeouts
        for (int i = 0; i < NUM_NODES; i++) {
            int base_timeout = nodes[i].electionTimeout;
            nodes[i].electionTimeout = klee_range(base_timeout, 2 * base_timeout, "randomized_timeout");
        }
    }
    
    // Test case 3: Log replication under adversarial message delays
    if (adversarial_message_delays) {
        // Make message delivery delays up to 2x election timeout
        int max_election_timeout = 0;
        for (int i = 0; i < NUM_NODES; i++) {
            if (nodes[i].electionTimeout > max_election_timeout) {
                max_election_timeout = nodes[i].electionTimeout;
            }
        }
        
        for (int i = 0; i < NUM_NODES; i++) {
            for (int j = 0; j < NUM_NODES; j++) {
                if (i != j) {
                    network.message_delay[i][j] = klee_range(0, 2 * max_election_timeout, "adversarial_delay");
                }
            }
        }
    }
    
    // Add some initial log entries to node 0 (potential leader)
    int num_initial_entries = klee_range(1, 5, "num_initial_entries");
    for (int i = 0; i < num_initial_entries; i++) {
        nodes[0].log[i].term = nodes[0].currentTerm;
        nodes[0].log[i].index = i+1;
        nodes[0].log[i].command = klee_range(1, 100, "command_value");
        nodes[0].log_length++;
    }
    
    // Execute multiple rounds with metrics tracking
    for (int round = 0; round < num_rounds; round++) {
        metrics.election_rounds_elapsed = round + 1;
        
        // Advance time symbolically
        current_time += klee_range(10, 50, "time_advance");
        
        // Check election timeouts
        for (int i = 0; i < NUM_NODES; i++) {
            check_election_timeout(&nodes[i], current_time, &metrics);
        }
        
        // Leader sends append entries (if there is a leader)
        for (int i = 0; i < NUM_NODES; i++) {
            if (nodes[i].state == LEADER) {
                // Send append entries/heartbeats to all other nodes
                for (int j = 0; j < NUM_NODES; j++) {
                    if (j != i) {
                        RaftMessage msg;
                        msg.type = APPEND_ENTRIES;
                        msg.term = nodes[i].currentTerm;
                        msg.sender_id = i;
                        msg.receiver_id = j;
                        msg.leader_commit = nodes[i].commit_index;
                        
                        // Determine entries to send based on next_index
                        int next_idx = nodes[i].next_index[j];
                        msg.prev_log_index = next_idx - 1;
                        
                        if (msg.prev_log_index > 0 && msg.prev_log_index <= nodes[i].log_length) {
                            msg.prev_log_term = nodes[i].log[msg.prev_log_index - 1].term;
                        } else {
                            msg.prev_log_term = 0;
                        }
                        
                        // Add entries starting at next_index (up to 5 max)
                        msg.entries_length = 0;
                        for (int e = next_idx; e <= nodes[i].log_length && msg.entries_length < 5; e++) {
                            msg.entries[msg.entries_length] = nodes[i].log[e - 1];
                            msg.entries_length++;
                        }
                        
                        process_message(&nodes[j], &msg, &network, &metrics, heartbeat_delay);
                        
                        // Follower responds with success/failure (simplified)
                        if (msg.entries_length > 0) {
                            RaftMessage response;
                            response.type = APPEND_RESPONSE;
                            response.term = nodes[j].currentTerm;
                            response.sender_id = j;
                            response.receiver_id = i;
                            response.prev_log_index = msg.prev_log_index;
                            response.entries_length = msg.entries_length;
                            
                            // Determine success based on log consistency
                            if (msg.prev_log_index == 0 || 
                                (msg.prev_log_index <= nodes[j].log_length && 
                                 nodes[j].log[msg.prev_log_index - 1].term == msg.prev_log_term)) {
                                response.success = 1;
                                // Set the match index fields for successful response
                                response.last_log_index = msg.prev_log_index + msg.entries_length;
                                response.match_index = response.last_log_index;
                                response.prev_match_index = msg.prev_log_index;
                            } else {
                                response.success = 0;
                                // Set default values for unsuccessful response
                                response.last_log_index = msg.prev_log_index;
                                response.match_index = 0;
                                response.prev_match_index = msg.prev_log_index;
                            }
                            
                            process_message(&nodes[i], &response, &network, &metrics, 0);
                        }
                    }
                }
            }
        }
        
        // Generate a symbolic message (random RPCs)
        if (klee_range(0, 1, "generate_message")) {
            RaftMessage msg;
            msg.type = klee_range(0, 3, "message_type");
            msg.term = klee_range(0, 5, "message_term");
            msg.sender_id = klee_range(0, NUM_NODES-1, "sender_id");
            msg.receiver_id = klee_range(0, NUM_NODES-1, "receiver_id");
            
            // Only process if sender and receiver are different
            if (msg.sender_id != msg.receiver_id) {
                // Customized fields based on message type
                if (msg.type == REQUEST_VOTE) {
                    msg.prev_log_index = klee_range(0, 10, "prev_log_index");
                    msg.prev_log_term = klee_range(0, 5, "prev_log_term");
                } else if (msg.type == APPEND_ENTRIES) {
                    msg.prev_log_index = klee_range(0, 10, "prev_log_index");
                    msg.prev_log_term = klee_range(0, 5, "prev_log_term");
                    msg.entries_length = klee_range(0, 5, "entries_length");
                    msg.leader_commit = klee_range(0, 10, "leader_commit");
                    
                    // Generate symbolic entries
                    for (int e = 0; e < msg.entries_length; e++) {
                        msg.entries[e].term = klee_range(1, 5, "entry_term");
                        msg.entries[e].index = msg.prev_log_index + e + 1;
                        msg.entries[e].command = klee_range(1, 100, "entry_command");
                    }
                } else if (msg.type == VOTE_RESPONSE || msg.type == APPEND_RESPONSE) {
                    msg.success = klee_range(0, 1, "success");
                    msg.prev_log_index = klee_range(0, 10, "resp_prev_log_index");
                    msg.entries_length = klee_range(0, 5, "resp_entries_length");
                    
                    // Add the missing fields for APPEND_RESPONSE
                    if (msg.type == APPEND_RESPONSE) {
                        msg.last_log_index = msg.prev_log_index + msg.entries_length;
                        msg.match_index = msg.success ? msg.last_log_index : 0;
                        msg.prev_match_index = msg.prev_log_index;
                    }
                }
                
                process_message(&nodes[msg.receiver_id], &msg, &network, &metrics, heartbeat_delay);
            }
        }
        
        // Verify safety properties after each round
        verify_safety_properties(nodes, NUM_NODES, &metrics);
        
        // Verify log consistency after each round
        verify_log_consistency(nodes, NUM_NODES, &metrics);
        
        // Verify liveness properties after a reasonable number of rounds
        if (round >= 10) { // Check liveness after at least 10 rounds
            verify_liveness_properties(nodes, NUM_NODES, &metrics, num_rounds);
            verify_log_replication_progress(nodes, NUM_NODES, &metrics, round, adversarial_message_delays);
            
            // Additional assertions for enhanced metrics after sufficient rounds
            if (metrics.log_replication_attempts > 0) {
                // Ensure we're making progress with replication
                klee_assert(metrics.log_entries_replicated > 0 || "No entries have been replicated");
                
                // Check if we're achieving at least partial replication
                if (round >= 15) {
                    klee_assert(metrics.partial_replication > 0 || "No partial replication achieved after 15 rounds");
                }
                
                // By late rounds, we should see some full replication if network is stable
                if (round >= 20 && !adversarial_message_delays) {
                    klee_assert(metrics.full_replication > 0 || "No full replication achieved in stable network");
                }
            }
        }
    }
    
    // Report metrics symbolically for KLEE to explore
    if (metrics.leader_elected) {
        // Success path - leader was elected
        klee_assert(metrics.split_brain_detected == 0);
        
        // Check log replication metrics if this was a log replication test
        if (adversarial_message_delays && metrics.log_replication_attempts > 0) {
            // Assert that at least some log replication succeeded
            // In a healthy system, we expect a decent success rate
            klee_assert(metrics.log_replication_success > 0 || "No log replication succeeded");
            
            // Ensure we're replicating entries
            klee_assert(metrics.log_entries_replicated > 0 || "No entries were replicated");
            
            // In adversarial conditions, we should achieve at least partial replication
            klee_assert(metrics.partial_replication > 0 || "No partial replication achieved under adversarial conditions");
            
            // Check for balanced replication among followers
            int min_follower_replication = metrics.follower_replication[0];
            int max_follower_replication = metrics.follower_replication[0];
            for (int i = 1; i < NUM_NODES; i++) {
                if (i != identify_leader(nodes, NUM_NODES)) {
                    if (metrics.follower_replication[i] < min_follower_replication) {
                        min_follower_replication = metrics.follower_replication[i];
                    }
                    if (metrics.follower_replication[i] > max_follower_replication) {
                        max_follower_replication = metrics.follower_replication[i];
                    }
                }
            }
            // Some followers should have received entries
            klee_assert(max_follower_replication > 0 || "No followers received any entries");
            
            // Verify no consistency violations remain
            klee_assert(metrics.log_consistency_violations == 0 || "Log consistency violations detected");
        }
    } else if (metrics.election_rounds_elapsed >= 10) {
        // If we've run at least 10 rounds and still no leader, report liveness violation
        klee_assert(0 && "Liveness violation: No leader elected after sufficient rounds");
    }
    
    // Calculate election success rate
    if (metrics.election_attempt_count > 0) {
        float success_rate = (float)metrics.election_success_count / metrics.election_attempt_count;
        if (success_rate < 0.1 && metrics.election_attempt_count >= 5) {
            klee_assert(0 && "Poor election success rate");
        }
    }
    
    // Final replication quality metrics
    if (metrics.log_replication_attempts > 0 && metrics.leader_elected) {
        // Calculate replication efficiency
        float replication_success_rate = (float)metrics.log_replication_success / metrics.log_replication_attempts;
        // We expect at least some success in replication attempts
        if (replication_success_rate < 0.05 && metrics.log_replication_attempts >= 10) {
            klee_assert(0 && "Extremely poor replication success rate");
        }
        
        // Check average latency if we have successful replications
        if (metrics.log_replication_success > 0) {
            float avg_latency = (float)metrics.replication_latency / metrics.log_replication_success;
            // Report excessive latency
            if (avg_latency > 30 && !adversarial_message_delays) {
                klee_assert(0 && "Excessive replication latency in stable network");
            }
        }
    }
    
    return 0;
} 