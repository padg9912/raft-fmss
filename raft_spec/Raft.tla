--------------------------------- MODULE Raft ---------------------------------

(* This is the formal specification for the Raft consensus algorithm,
   extended with adversarial delay parameters for security analysis.

   Copyright 2014 Diego Ongaro.
   This work is licensed under the Creative Commons Attribution-4.0
   International License https://creativecommons.org/licenses/by/4.0/

   Modified in 2025 to include adversarial timing parameters.
*)

EXTENDS Naturals, FiniteSets, Sequences, TLC

\* The set of server IDs
CONSTANTS Server

\* The set of requests that can go into the log
CONSTANTS Value

\* Server states.
CONSTANTS Follower, Candidate, Leader

\* A reserved value.
CONSTANTS Nil

\* Message types:
CONSTANTS RequestVoteRequest, RequestVoteResponse,
          AppendEntriesRequest, AppendEntriesResponse

\* Adversarial parameters
CONSTANTS
  MaxElectionTimeout,       \* Maximum election timeout value
  MinElectionTimeout,       \* Minimum election timeout value
  HeartbeatTimeout,         \* Heartbeat timeout (how often leaders send heartbeats)
  MaxHeartbeatDelay,        \* Maximum delay an adversary can impose on heartbeats
  MaxMessageDelay,          \* Maximum delay of any message 
  MaxNetworkPartition,      \* Maximum number of nodes that can be partitioned (0=no partition)
  MessageDropProb           \* Probability a message is dropped (0=none, N=1 in N)

----
\* Global variables

\* A bag of records representing requests and responses sent from one server
\* to another. TLAPS doesn't support the Bags module, so this is a function
\* mapping Message to Nat.
VARIABLE messages

\* A history variable used in the proof. This would not be present in an
\* implementation.
\* Keeps track of successful elections, including the initial logs of the
\* leader and voters' logs. Set of functions containing various things about
\* successful elections (see BecomeLeader).
VARIABLE elections

\* A history variable used in the proof. This would not be present in an
\* implementation.
\* Keeps track of every log ever in the system (set of logs).
VARIABLE allLogs

\* Adversarial variables
VARIABLE 
  \* Stores the election timeout for each server (can be manipulated by adversary)
  electionTimeouts,
  \* Tracks the time of the next heartbeat for each server
  nextHeartbeatTime,
  \* For each message, tracks the additional adversarial delay
  messageDelays,
  \* Current logical time of the system
  currentTime,
  \* Tracks whether a server is partitioned from the network
  partitioned

----
\* The following variables are all per server (functions with domain Server).
\* The server's term number.
VARIABLE currentTerm
\* The server's state (Follower, Candidate, or Leader).
VARIABLE state
\* The candidate the server voted for in its current term, or
\* Nil if it hasn't voted for any.
VARIABLE votedFor
serverVars == <<currentTerm, state, votedFor>>

\* A Sequence of log entries. The index into this sequence is the index of the
\* log entry. Unfortunately, the Sequence module defines Head(s) as the entry
\* with index 1, so be careful not to use that!
VARIABLE log
\* The index of the latest entry in the log the state machine may apply.
VARIABLE commitIndex
logVars == <<log, commitIndex>>

\* The following variables are used only on candidates:
\* The set of servers from which the candidate has received a RequestVote
\* response in its currentTerm.
VARIABLE votesResponded
\* The set of servers from which the candidate has received a vote in its
\* currentTerm.
VARIABLE votesGranted
\* A history variable used in the proof. This would not be present in an
\* implementation.
\* Function from each server that voted for this candidate in its currentTerm
\* to that voter's log.
VARIABLE voterLog
candidateVars == <<votesResponded, votesGranted, voterLog>>

\* The following variables are used only on leaders:
\* The next entry to send to each follower.
VARIABLE nextIndex
\* The latest entry that each follower has acknowledged is the same as the
\* leader's. This is used to calculate commitIndex on the leader.
VARIABLE matchIndex
leaderVars == <<nextIndex, matchIndex, elections>>

\* End of per server variables.
----

\* All variables; used for stuttering (asserting state hasn't changed).
vars == <<messages, allLogs, serverVars, candidateVars, leaderVars, logVars,
         electionTimeouts, nextHeartbeatTime, messageDelays, currentTime, partitioned>>

----
\* Helpers

\* The set of all quorums. This just calculates simple majorities, but the only
\* important property is that every quorum overlaps with every other.
Quorum == {i \in SUBSET(Server) : Cardinality(i) * 2 > Cardinality(Server)}

\* The term of the last entry in a log, or 0 if the log is empty.
LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)].term

\* Helper for Send and Reply. Given a message m and bag of messages, return a
\* new bag of messages with one more m in it.
WithMessage(m, msgs) ==
    IF m \in DOMAIN msgs THEN
        [msgs EXCEPT ![m] = msgs[m] + 1]
    ELSE
        msgs @@ (m :> 1)

\* Helper for Discard and Reply. Given a message m and bag of messages, return
\* a new bag of messages with one less m in it.
WithoutMessage(m, msgs) ==
    IF m \in DOMAIN msgs THEN
        IF msgs[m] <= 1 THEN
            [i \in DOMAIN msgs \ {m} |-> msgs[i]]
        ELSE
            [msgs EXCEPT ![m] = msgs[m] - 1]
    ELSE
        msgs

\* Add a message to the bag of messages with possible adversarial delay.
\* The adversary can choose any delay up to MaxMessageDelay for any message.
Send(m) == 
    /\ messages' = WithMessage(m, messages)
    /\ messageDelays' = messageDelays @@ (m :> (CHOOSE delay \in 0..MaxMessageDelay : TRUE))
    /\ UNCHANGED <<currentTime, electionTimeouts, nextHeartbeatTime, partitioned>>

\* Remove a message from the bag of messages. Used when a server is done
\* processing a message.
Discard(m) == 
    /\ messages' = WithoutMessage(m, messages)
    /\ UNCHANGED <<messageDelays, currentTime, electionTimeouts, nextHeartbeatTime, partitioned>>

\* Combination of Send and Discard
Reply(response, request) ==
    /\ messages' = WithoutMessage(request, WithMessage(response, messages))
    /\ messageDelays' = messageDelays @@ (response :> (CHOOSE delay \in 0..MaxMessageDelay : TRUE))
    /\ UNCHANGED <<currentTime, electionTimeouts, nextHeartbeatTime, partitioned>>

\* Return the minimum value from a set, or undefined if the set is empty.
Min(s) == CHOOSE x \in s : \A y \in s : x <= y

\* Return the maximum value from a set, or undefined if the set is empty.
Max(s) == CHOOSE x \in s : \A y \in s : x >= y

----
\* Determine if a message can be delivered based on delays and partitioning.
CanDeliver(m) ==
    /\ m \in DOMAIN messages  \* Message exists
    /\ messages[m] > 0        \* At least one copy of the message
    /\ m \in DOMAIN messageDelays  \* It has a delay assigned
    /\ currentTime >= messageDelays[m]  \* The delay has passed
    /\ \/ partitioned[m.msource] = FALSE  \* Source is not partitioned
       \/ partitioned[m.mdest] = FALSE    \* Destination is not partitioned

\* Determine if a server can send heartbeats based on timing and partitioning.
CanSendHeartbeat(i) ==
    /\ state[i] = Leader
    /\ currentTime >= nextHeartbeatTime[i]
    /\ partitioned[i] = FALSE

\* Determine if a server can timeout and become a candidate.
CanTimeout(i) ==
    /\ state[i] \in {Follower, Candidate}
    /\ currentTime >= electionTimeouts[i]
    /\ partitioned[i] = FALSE

----
\* Define initial values for all variables

InitHistoryVars == /\ elections = {}
                  /\ allLogs = {}
                  /\ voterLog = [i \in Server |-> [j \in {} |-> <<>>]]

InitServerVars == /\ currentTerm = [i \in Server |-> 1]
                 /\ state = [i \in Server |-> Follower]
                 /\ votedFor = [i \in Server |-> Nil]

InitCandidateVars == /\ votesResponded = [i \in Server |-> {}]
                    /\ votesGranted = [i \in Server |-> {}]

\* The values nextIndex[i][i] and matchIndex[i][i] are never read, since the
\* leader does not send itself messages. It's still easier to include these
\* in the functions.
InitLeaderVars == /\ nextIndex = [i \in Server |-> [j \in Server |-> 1]]
                 /\ matchIndex = [i \in Server |-> [j \in Server |-> 0]]

InitLogVars == /\ log = [i \in Server |-> << >>]
              /\ commitIndex = [i \in Server |-> 0]

\* Initialize adversarial variables
InitAdversarialVars == 
    /\ electionTimeouts = [i \in Server |-> 
                            CHOOSE timeout \in MinElectionTimeout..MaxElectionTimeout : TRUE]
    /\ nextHeartbeatTime = [i \in Server |-> 0]  \* Start with immediate heartbeats
    /\ messageDelays = [m \in {} |-> 0]  \* Empty initial message delays
    /\ currentTime = 0                  \* Start at time 0
    /\ partitioned = [i \in Server |-> FALSE]  \* Initially no partitions

Init == /\ messages = [m \in {} |-> 0]
       /\ InitHistoryVars
       /\ InitServerVars
       /\ InitCandidateVars
       /\ InitLeaderVars
       /\ InitLogVars
       /\ InitAdversarialVars

----
\* Adversarial actions

\* The adversary manipulates election timeouts to disrupt leader election.
AdversaryManipulatesElectionTimeout ==
    /\ \E i \in Server : 
        /\ electionTimeouts' = [electionTimeouts EXCEPT ![i] = 
                                CHOOSE timeout \in MinElectionTimeout..MaxElectionTimeout : TRUE]
    /\ UNCHANGED <<messages, allLogs, serverVars, candidateVars, leaderVars, 
                   logVars, messageDelays, nextHeartbeatTime, currentTime, partitioned>>

\* The adversary delays heartbeats to cause unnecessary elections.
AdversaryDelaysHeartbeat ==
    /\ \E i \in Server : 
        /\ state[i] = Leader
        /\ nextHeartbeatTime' = [nextHeartbeatTime EXCEPT ![i] = 
                                  currentTime + CHOOSE delay \in 1..MaxHeartbeatDelay : TRUE]
    /\ UNCHANGED <<messages, allLogs, serverVars, candidateVars, leaderVars, 
                   logVars, messageDelays, electionTimeouts, currentTime, partitioned>>

\* The adversary creates a network partition
AdversaryCreatesPartition ==
    /\ LET partitionSize == CHOOSE size \in 0..MaxNetworkPartition : TRUE
       IN
          /\ partitionSize > 0  \* Only if we can actually partition nodes
          /\ \E nodes \in SUBSET Server :
              /\ Cardinality(nodes) = partitionSize
              /\ partitioned' = [i \in Server |-> IF i \in nodes THEN TRUE ELSE FALSE]
    /\ UNCHANGED <<messages, allLogs, serverVars, candidateVars, leaderVars, 
                   logVars, messageDelays, electionTimeouts, nextHeartbeatTime, currentTime>>

\* The adversary heals a network partition
AdversaryHealsPartition ==
    /\ \E i \in Server : partitioned[i] = TRUE
    /\ partitioned' = [i \in Server |-> FALSE]
    /\ UNCHANGED <<messages, allLogs, serverVars, candidateVars, leaderVars, 
                   logVars, messageDelays, electionTimeouts, nextHeartbeatTime, currentTime>>

\* The adversary drops a message (implements MessageDropProb)
AdversaryDropsMessage ==
    /\ MessageDropProb > 0
    /\ \E m \in DOMAIN messages :
        /\ messages[m] > 0
        /\ m \in DOMAIN messageDelays
        /\ Discard(m)
    /\ UNCHANGED <<allLogs, serverVars, candidateVars, leaderVars, logVars, 
                   electionTimeouts, nextHeartbeatTime, currentTime, partitioned>>

----
\* Define state transitions

\* Time advances.
AdvanceTime ==
    /\ currentTime' = currentTime + 1
    /\ UNCHANGED <<messages, messageDelays, electionTimeouts, nextHeartbeatTime, 
                   partitioned, allLogs, serverVars, candidateVars, leaderVars, logVars>>

\* Server i restarts from stable storage.
\* It loses everything but its currentTerm, votedFor, and log.
Restart(i) ==
    /\ state' = [state EXCEPT ![i] = Follower]
    /\ votesResponded' = [votesResponded EXCEPT ![i] = {}]
    /\ votesGranted' = [votesGranted EXCEPT ![i] = {}]
    /\ voterLog' = [voterLog EXCEPT ![i] = [j \in {} |-> <<>>]]
    /\ nextIndex' = [nextIndex EXCEPT ![i] = [j \in Server |-> 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![i] = [j \in Server |-> 0]]
    /\ commitIndex' = [commitIndex EXCEPT ![i] = 0]
    /\ electionTimeouts' = [electionTimeouts EXCEPT ![i] = 
                             currentTime + CHOOSE timeout \in MinElectionTimeout..MaxElectionTimeout : TRUE]
    /\ UNCHANGED <<messages, messageDelays, nextHeartbeatTime, currentTime, partitioned, 
                   currentTerm, votedFor, log, elections, allLogs>>

\* Server i times out and starts a new election.
Timeout(i) ==
    /\ CanTimeout(i)
    /\ state' = [state EXCEPT ![i] = Candidate]
    /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[i] + 1]
    \* Most implementations would probably just set the local vote
    \* atomically, but messaging localhost for it is weaker.
    /\ votedFor' = [votedFor EXCEPT ![i] = Nil]
    /\ votesResponded' = [votesResponded EXCEPT ![i] = {}]
    /\ votesGranted' = [votesGranted EXCEPT ![i] = {}]
    /\ voterLog' = [voterLog EXCEPT ![i] = [j \in {} |-> <<>>]]
    /\ electionTimeouts' = [electionTimeouts EXCEPT ![i] = 
                             currentTime + CHOOSE timeout \in MinElectionTimeout..MaxElectionTimeout : TRUE]
    /\ UNCHANGED <<messages, messageDelays, nextHeartbeatTime, currentTime, partitioned, 
                   leaderVars, logVars, allLogs>>

\* Candidate i sends j a RequestVote request.
RequestVote(i, j) ==
    /\ state[i] = Candidate
    /\ j \notin votesResponded[i]
    /\ Send([mtype |-> RequestVoteRequest,
             mterm |-> currentTerm[i],
             mlastLogTerm |-> LastTerm(log[i]),
             mlastLogIndex |-> Len(log[i]),
             msource |-> i,
             mdest |-> j])
    /\ UNCHANGED <<allLogs, serverVars, candidateVars, leaderVars, logVars, allLogs>>

\* Leader i sends j an AppendEntries request containing up to 1 entry.
\* While implementations may want to send more than 1 at a time, this spec uses
\* just 1 because it minimizes atomic regions without loss of generality.
AppendEntries(i, j) ==
    /\ i /= j
    /\ state[i] = Leader
    /\ LET prevLogIndex == nextIndex[i][j] - 1
           prevLogTerm == IF prevLogIndex > 0 THEN
                              log[i][prevLogIndex].term
                          ELSE
                              0
           \* Send up to 1 entry, constrained by the end of the log.
           lastEntry == Min({Len(log[i]), nextIndex[i][j]})
           entries == SubSeq(log[i], nextIndex[i][j], lastEntry)
       IN Send([mtype |-> AppendEntriesRequest,
                mterm |-> currentTerm[i],
                mprevLogIndex |-> prevLogIndex,
                mprevLogTerm |-> prevLogTerm,
                mentries |-> entries,
                \* mlog is used as a history variable for the proof.
                \* It would not exist in a real implementation.
                mlog |-> log[i],
                mcommitIndex |-> Min({commitIndex[i], lastEntry}),
                msource |-> i,
                mdest |-> j])
    /\ UNCHANGED <<allLogs, serverVars, candidateVars, leaderVars, logVars, allLogs>>

\* Leader i sends heartbeats to all servers.
SendHeartbeats(i) ==
    /\ CanSendHeartbeat(i)
    /\ nextHeartbeatTime' = [nextHeartbeatTime EXCEPT ![i] = currentTime + HeartbeatTimeout]
    /\ \A j \in Server \ {i} :
         Send([mtype |-> AppendEntriesRequest,
               mterm |-> currentTerm[i],
               mprevLogIndex |-> nextIndex[i][j] - 1,
               mprevLogTerm |-> IF nextIndex[i][j] - 1 > 0 
                                 THEN log[i][nextIndex[i][j] - 1].term 
                                 ELSE 0,
               mentries |-> <<>>,  \* Empty for heartbeats
               mlog |-> log[i],    \* History variable
               mcommitIndex |-> commitIndex[i],
               msource |-> i,
               mdest |-> j])
    /\ UNCHANGED <<allLogs, serverVars, candidateVars, leaderVars, logVars, allLogs>>

\* Candidate i transitions to leader.
BecomeLeader(i) ==
    /\ state[i] = Candidate
    /\ votesGranted[i] \in Quorum
    /\ state' = [state EXCEPT ![i] = Leader]
    /\ nextIndex' = [nextIndex EXCEPT ![i] =
                        [j \in Server |-> Len(log[i]) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![i] =
                         [j \in Server |-> 0]]
    /\ nextHeartbeatTime' = [nextHeartbeatTime EXCEPT ![i] = currentTime]  \* Send heartbeats immediately
    /\ elections' = elections \cup
                      {[eterm |-> currentTerm[i],
                        eleader |-> i,
                        elog |-> log[i],
                        evotes |-> votesGranted[i],
                        evoterLog |-> voterLog[i]]}
    /\ UNCHANGED <<messages, messageDelays, currentTime, partitioned, allLogs, 
                   currentTerm, votedFor, candidateVars, logVars, electionTimeouts, allLogs>>

\* Leader i receives a client request to add v to the log.
ClientRequest(i, v) ==
    /\ state[i] = Leader
    /\ LET entry == [term |-> currentTerm[i],
                     value |-> v]
           newLog == Append(log[i], entry)
       IN log' = [log EXCEPT ![i] = newLog]
    /\ UNCHANGED <<messages, messageDelays, electionTimeouts, nextHeartbeatTime, currentTime, 
                   partitioned, allLogs, serverVars, candidateVars, leaderVars, commitIndex>>

\* Leader i advances its commitIndex.
\* This is done as a separate step from handling AppendEntries responses,
\* in part to minimize atomic regions, and in part so that leaders of
\* single-server clusters are able to mark entries committed.
AdvanceCommitIndex(i) ==
    /\ state[i] = Leader
    /\ LET \* The set of servers that agree up through index.
           Agree(index) == {i} \cup {k \in Server :
                                         matchIndex[i][k] >= index}
           \* The maximum indexes for which a quorum agrees
           agreeIndexes == {index \in 1..Len(log[i]) :
                                Agree(index) \in Quorum}
           \* New value for commitIndex'[i]
           newCommitIndex ==
              IF /\ agreeIndexes /= {}
                 /\ log[i][Max(agreeIndexes)].term = currentTerm[i]
              THEN
                  Max(agreeIndexes)
              ELSE
                  commitIndex[i]
       IN commitIndex' = [commitIndex EXCEPT ![i] = newCommitIndex]
    /\ UNCHANGED <<messages, messageDelays, electionTimeouts, nextHeartbeatTime, currentTime, 
                   partitioned, allLogs, serverVars, candidateVars, leaderVars, log, allLogs>>

----
\* Message handlers
\* i = recipient, j = sender, m = message

\* Server i receives a RequestVote request from server j with
\* m.mterm <= currentTerm[i].
HandleRequestVoteRequest(i, j, m) ==
    LET logOk == \/ m.mlastLogTerm > LastTerm(log[i])
                 \/ /\ m.mlastLogTerm = LastTerm(log[i])
                    /\ m.mlastLogIndex >= Len(log[i])
        grant == /\ m.mterm = currentTerm[i]
                /\ logOk
                /\ votedFor[i] \in {Nil, j}
    IN /\ m.mterm <= currentTerm[i]
       /\ \/ grant  /\ votedFor' = [votedFor EXCEPT ![i] = j]
          \/ ~grant /\ UNCHANGED votedFor
       /\ Reply([mtype |-> RequestVoteResponse,
                 mterm |-> currentTerm[i],
                 mvoteGranted |-> grant,
                 \* mlog is used just for the `elections' history variable for
                 \* the proof. It would not exist in a real implementation.
                 mlog |-> log[i],
                 msource |-> i,
                 mdest |-> j],
                 m)
       /\ UNCHANGED <<electionTimeouts, currentTime, partitioned, state, currentTerm, 
                      candidateVars, leaderVars, logVars, allLogs>>

\* Server i receives a RequestVote response from server j with
\* m.mterm = currentTerm[i].
HandleRequestVoteResponse(i, j, m) ==
    \* This tallies votes even when the current state is not Candidate, but
    \* they won't be looked at, so it doesn't matter.
    /\ m.mterm = currentTerm[i]
    /\ votesResponded' = [votesResponded EXCEPT ![i] =
                              votesResponded[i] \cup {j}]
    /\ \/ /\ m.mvoteGranted
          /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                  votesGranted[i] \cup {j}]
          /\ voterLog' = [voterLog EXCEPT ![i] =
                              voterLog[i] @@ (j :> m.mlog)]
       \/ /\ ~m.mvoteGranted
          /\ UNCHANGED <<votesGranted, voterLog>>
    /\ Discard(m)
    /\ UNCHANGED <<electionTimeouts, nextHeartbeatTime, currentTime, partitioned, 
                   allLogs, serverVars, votedFor, leaderVars, logVars>>

\* Server i receives an AppendEntries request from server j with
\* m.mterm <= currentTerm[i]. This just handles m.entries of length 0 or 1, but
\* implementations could safely accept more by treating them the same as
\* multiple independent requests of 1 entry.
HandleAppendEntriesRequest(i, j, m) ==
    LET logOk == \/ m.mprevLogIndex = 0
                 \/ /\ m.mprevLogIndex > 0
                    /\ m.mprevLogIndex <= Len(log[i])
                    /\ m.mprevLogTerm = log[i][m.mprevLogIndex].term
    IN /\ m.mterm <= currentTerm[i]
       /\ \/ /\ \* reject request
                \/ m.mterm < currentTerm[i]
                \/ /\ m.mterm = currentTerm[i]
                   /\ state[i] = Follower
                   /\ \lnot logOk
             /\ Reply([mtype |-> AppendEntriesResponse,
                       mterm |-> currentTerm[i],
                       msuccess |-> FALSE,
                       mmatchIndex |-> 0,
                       msource |-> i,
                       mdest |-> j],
                       m)
             /\ UNCHANGED <<electionTimeouts, state, logVars, allLogs>>
          \/ \* return to follower state
             /\ m.mterm = currentTerm[i]
             /\ state[i] = Candidate
             /\ state' = [state EXCEPT ![i] = Follower]
             /\ electionTimeouts' = [electionTimeouts EXCEPT ![i] = 
                              currentTime + CHOOSE timeout \in MinElectionTimeout..MaxElectionTimeout : TRUE]
             /\ UNCHANGED <<currentTerm, votedFor, logVars, messages, messageDelays, 
                            nextHeartbeatTime, currentTime, partitioned, allLogs>>
          \/ \* accept request
             /\ m.mterm = currentTerm[i]
             /\ state[i] = Follower
             /\ logOk
             /\ LET index == m.mprevLogIndex + 1
                IN \/ \* already done with request
                      /\ \/ m.mentries = << >>
                         \/ /\ m.mentries /= << >>
                            /\ Len(log[i]) >= index
                            /\ log[i][index].term = m.mentries[1].term
                      \* This could make our commitIndex decrease (for
                      \* example if we process an old, duplicated request),
                      \* but that doesn't really affect anything.
                      /\ commitIndex' = [commitIndex EXCEPT ![i] =
                                             m.mcommitIndex]
                      /\ electionTimeouts' = [electionTimeouts EXCEPT ![i] = 
                                             currentTime + CHOOSE timeout \in MinElectionTimeout..MaxElectionTimeout : TRUE]
                      /\ Reply([mtype |-> AppendEntriesResponse,
                               mterm |-> currentTerm[i],
                               msuccess |-> TRUE,
                               mmatchIndex |-> m.mprevLogIndex +
                                               Len(m.mentries),
                               msource |-> i,
                               mdest |-> j],
                               m)
                      /\ UNCHANGED <<state, log, allLogs>>
                   \/ \* conflict: remove 1 entry
                      /\ m.mentries /= << >>
                      /\ Len(log[i]) >= index
                      /\ log[i][index].term /= m.mentries[1].term
                      /\ LET new == [index2 \in 1..(Len(log[i]) - 1) |->
                                          log[i][index2]]
                         IN log' = [log EXCEPT ![i] = new]
                      /\ electionTimeouts' = [electionTimeouts EXCEPT ![i] = 
                                             currentTime + CHOOSE timeout \in MinElectionTimeout..MaxElectionTimeout : TRUE]
                      /\ UNCHANGED <<state, commitIndex, messages, messageDelays, 
                                     nextHeartbeatTime, currentTime, partitioned, allLogs>>
                   \/ \* no conflict: append entry
                      /\ m.mentries /= << >>
                      /\ Len(log[i]) = m.mprevLogIndex
                      /\ log' = [log EXCEPT ![i] =
                                      Append(log[i], m.mentries[1])]
                      /\ electionTimeouts' = [electionTimeouts EXCEPT ![i] = 
                                             currentTime + CHOOSE timeout \in MinElectionTimeout..MaxElectionTimeout : TRUE]
                      /\ UNCHANGED <<state, commitIndex, messages, messageDelays, 
                                     nextHeartbeatTime, currentTime, partitioned, allLogs>>
       /\ UNCHANGED <<candidateVars, leaderVars>>

\* Server i receives an AppendEntries response from server j with
\* m.mterm = currentTerm[i].
HandleAppendEntriesResponse(i, j, m) ==
    /\ m.mterm = currentTerm[i]
    /\ \/ /\ m.msuccess \* successful
          /\ nextIndex' = [nextIndex EXCEPT ![i][j] = m.mmatchIndex + 1]
          /\ matchIndex' = [matchIndex EXCEPT ![i][j] = m.mmatchIndex]
       \/ /\ \lnot m.msuccess \* not successful
          /\ nextIndex' = [nextIndex EXCEPT ![i][j] =
                               Max({nextIndex[i][j] - 1, 1})]
          /\ UNCHANGED <<matchIndex>>
    /\ Discard(m)
    /\ UNCHANGED <<electionTimeouts, nextHeartbeatTime, currentTime, partitioned, 
                   allLogs, serverVars, candidateVars, logVars, elections>>

\* Any RPC with a newer term causes the recipient to advance its term first.
UpdateTerm(i, j, m) ==
    /\ m.mterm > currentTerm[i]
    /\ currentTerm' = [currentTerm EXCEPT ![i] = m.mterm]
    /\ state' = [state EXCEPT ![i] = Follower]
    /\ votedFor' = [votedFor EXCEPT ![i] = Nil]
    /\ electionTimeouts' = [electionTimeouts EXCEPT ![i] = currentTime + CHOOSE timeout \in MinElectionTimeout..MaxElectionTimeout : TRUE]
    /\ Reply([mtype |-> m.mtype,
             mterm |-> m.mterm,
             msuccess |-> FALSE,
             mmatchIndex |-> 0,
             msource |-> i,
             mdest |-> j],
             m)
    /\ UNCHANGED <<allLogs, candidateVars, leaderVars, logVars>>

\* Message m is processed by recipient i at time currentTime.
HandleMessage(i, m) ==
    /\ CanDeliver(m)
    /\ LET j == m.msource
           t == m.mterm
       IN \/ /\ m.mtype = RequestVoteRequest
             /\ HandleRequestVoteRequest(i, j, m)
          \/ /\ m.mtype = RequestVoteResponse
             /\ HandleRequestVoteResponse(i, j, m)
          \/ /\ m.mtype = AppendEntriesRequest
             /\ HandleAppendEntriesRequest(i, j, m)
          \/ /\ m.mtype = AppendEntriesResponse
             /\ HandleAppendEntriesResponse(i, j, m)
    /\ UNCHANGED <<allLogs>>

\* End of message handlers.
----
\* Network state constraints.

\* The values that go into the log have the form [term, value].
LogEntry == [term: Nat, value: Value]

\* The set of all possible log values for all servers.
LogEntries == UNION {[1..Len(log[i]) -> LogEntry] : i \in Server}

----
\* Defines how the variables may transition.
Next == \/ \E m \in DOMAIN messages : 
            \E i \in Server :
                /\ HandleMessage(i, m)
        \/ \E i \in Server : Timeout(i)
        \/ \E i,v \in Server : ClientRequest(i, v)
        \/ \E i \in Server : BecomeLeader(i)
        \/ \E i \in Server : AdvanceCommitIndex(i)
        \/ \E i,j \in Server : RequestVote(i, j)
        \/ \E i,j \in Server : AppendEntries(i, j)
        \/ \E i \in Server : SendHeartbeats(i)
        \/ \E i \in Server : Restart(i)
        \/ AdversaryManipulatesElectionTimeout
        \/ AdversaryDelaysHeartbeat
        \/ AdversaryCreatesPartition
        \/ AdversaryHealsPartition
        \/ AdversaryDropsMessage
        \/ AdvanceTime

\* The specification must start with the initial state and transition according
\* to Next.
Fairness ==
    /\ \A i \in Server : WF_vars(Timeout(i))
    /\ \A i,j \in Server : WF_vars(RequestVote(i, j))
    /\ WF_vars(\E m \in DOMAIN messages : \E i \in Server : HandleMessage(i, m))
    /\ \A i \in Server : WF_vars(BecomeLeader(i))
    /\ \A i \in Server : WF_vars(SendHeartbeats(i))
    /\ WF_vars(AdvanceTime)
    \* Add other critical actions that should be fair

Spec == Init /\ [][Next]_vars /\ Fairness

\* The following are helper operators for use in properties.

\* True when a majority of servers have the given log entry.
CommittedAt(index) ==
    LET entriesMatchingAtIndex(s) == 
        {i \in Server : 
            /\ Len(log[i]) >= index
            /\ log[i][index].term = log[s][index].term}
    IN \E s \in Server : 
        /\ Len(log[s]) >= index
        /\ entriesMatchingAtIndex(s) \in Quorum

\* The set of committed entries.
committed == {i \in 1..Len(log[1]) : CommittedAt(i)}

----
\* Safety properties and invariants.

\* Election Safety: At most one leader can be elected in a given term.
ElectionSafety ==
    \A i, j \in Server :
        (/\ state[i] = Leader
         /\ state[j] = Leader
         /\ currentTerm[i] = currentTerm[j]) => i = j

\* Leader Completeness: If a log entry is committed in a given term, 
\* then that entry will be present in the logs of the leaders for all higher terms.
LeaderCompleteness ==
    \A i \in Server :
        state[i] = Leader =>
            \A j \in 1..commitIndex[i] :
                \E k \in Server :
                    /\ Len(log[k]) >= j
                    /\ log[k][j].term <= currentTerm[i]

\* Log Matching: If two logs contain an entry with the same index and term, 
\* then the logs are identical in all entries up through the given index.
LogMatching ==
    \A i, j \in Server :
        \A idx \in 1..Min({Len(log[i]), Len(log[j])}) :
            log[i][idx].term = log[j][idx].term =>
                SubSeq(log[i], 1, idx) = SubSeq(log[j], 1, idx)

\* State Machine Safety: If a server has applied a log entry at a given index,
\* no other server will ever apply a different log entry for the same index.
StateMachineSafety ==
    \A i, j \in Server :
        \A idx \in 1..Min({commitIndex[i], commitIndex[j]}) :
            log[i][idx] = log[j][idx]

\* Leader Append-Only: Leaders never delete or overwrite entries in their logs,
\* they only append new entries.
LeaderAppendOnly ==
    \A i \in Server :
        state[i] = Leader =>
            \A j \in 1..Len(log[i]) :
                UNCHANGED (log[i][j])

\* Properties under adversarial conditions:

\* Despite adversarial delays, the system will eventually make progress 
\* when the network is stable long enough.
EventualProgress ==
    []<>((\A i \in Server : partitioned[i] = FALSE) => 
          \E i \in Server : state[i] = Leader)

\* Even with adversarial partitions, the system will never violate safety properties.
SafetyUnderPartitions ==
    (\E i, j \in Server : partitioned[i] /= partitioned[j]) => 
        /\ ElectionSafety
        /\ LogMatching
        /\ StateMachineSafety

\* State constraint to limit model checking
StateConstraint ==
    /\ \A i \in Server : Len(log[i]) <= 3
    /\ \A i \in Server : currentTerm[i] <= 5
    /\ currentTime <= 20

====