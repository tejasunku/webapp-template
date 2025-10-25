------------------------ MODULE NonNativeTransitions ------------------------
(* @spec: non-native-transitions *)
(* @feature: State Machine with Non-Native Transitions (T-001) *)
(* @version: v0.0.0 *)
(* @author: TLA+ Models Agent *)

(* TLA+ specification demonstrating state machines with non-native transitions *)
(* Models complex recovery protocols, temporal logic, and concurrency patterns *)
(* This is where TLA+ adds unique value beyond Alloy's structural analysis *)

EXTENDS Naturals, Sequences, FiniteSets, TLC

(* Constants representing system bounds *)
CONSTANT
    MaxFactories,           (* Maximum number of factories *)
    MaxClients,             (* Maximum number of clients per factory *)
    RecoveryTimeoutValue,   (* Timeout for recovery operations *)
    ClientTypes             (* Set of possible client types: Database, Cache, Queue, ExternalAPI *)

(* Variables representing system state *)
VARIABLE
    factories,              (* Set of factory instances *)
    clients,                (* Set of client instances with states *)
    network,                (* Network state modeling partition/failure *)
    recovery_ops,           (* Active recovery operations *)
    step_counter            (* Global step counter for temporal reasoning *)

(* Type invariant ensuring well-formed state *)
TypeOK ==
    /\ factories \subseteq ClientTypes
    /\ clients \subseteq (0..(MaxFactories * MaxClients)) \X ClientTypes \X (0..MaxFactories) \X (0..MaxClients)
    /\ network \subseteq {"healthy", "partitioned", "failed"}
    /\ recovery_ops \subseteq (0..MaxFactories) \X (0..(MaxFactories * MaxClients))  (* (factory_id, client_id) pairs *)
    /\ step_counter \in (0..RecoveryTimeoutValue)

(* Initial state - system starts healthy *)
Init ==
    /\ factories = {0, 1}  (* Start with 2 factories using 0-based indexing *)
    /\ clients = {}         (* No clients initially *)
    /\ network = "healthy"  (* Network is healthy *)
    /\ recovery_ops = {}    (* No recovery operations *)
    /\ step_counter = 0

(* Helper functions *)

(* Get clients for a specific factory *)
GetFactoryClients(fid) ==
    {<<cid, ctype, owner_fid, state>> \in clients : owner_fid = fid}

(* Get clients in a specific state *)
GetClientsInState(state) ==
    {<<cid, ctype, fid, s>> \in clients : s = state}

(* Check if factory exists and is operational *)
FactoryOperational(fid) ==
    fid \in factories

(* Network failure modeling *)
NetworkPartition ==
    /\ network = "healthy"
    /\ network' = "partitioned"
    /\ UNCHANGED <<factories, clients, recovery_ops, step_counter>>

NetworkRecovery ==
    /\ network = "partitioned"
    /\ network' = "healthy"
    /\ UNCHANGED <<factories, clients, recovery_ops, step_counter>>

(* Client lifecycle operations *)

(* Initialize new client - NATIVE transition *)
InitializeClient(fid, ctype) ==
    /\ FactoryOperational(fid)
    /\ Cardinality(GetFactoryClients(fid)) < MaxClients
    /\ LET new_cid == Cardinality(clients) + 1
           IN clients' = clients \cup {<<new_cid, ctype, fid, "init">>}
    /\ UNCHANGED <<factories, network, recovery_ops, step_counter>>

(* Client ready transition - NATIVE transition *)
ClientReady(cid, ctype, fid) ==
    /\ <<cid, ctype, fid, "init">> \in clients
    /\ clients' = (clients \ {<<cid, ctype, fid, "init">>}) \cup {<<cid, ctype, fid, "ready">>}
    /\ UNCHANGED <<factories, network, recovery_ops, step_counter>>

(* Client failure due to network partition - NON-NATIVE transition *)
ClientFailFromPartition(cid, ctype, fid) ==
    /\ network = "partitioned"
    /\ <<cid, ctype, fid, "ready">> \in clients
    /\ clients' = (clients \ {<<cid, ctype, fid, "ready">>}) \cup {<<cid, ctype, fid, "failed">>}
    /\ UNCHANGED <<factories, network, recovery_ops, step_counter>>

(* Start recovery operation - NON-NATIVE transition triggered by external event *)
StartRecovery(cid, ctype, fid) ==
    /\ <<cid, ctype, fid, "failed">> \in clients
    /\ <<fid, cid>> \notin recovery_ops
    /\ recovery_ops' = recovery_ops \cup {<<fid, cid>>}
    /\ clients' = (clients \ {<<cid, ctype, fid, "failed">>}) \cup {<<cid, ctype, fid, "recovering">>}
    /\ UNCHANGED <<factories, network, step_counter>>

(* Complete recovery operation - COMPLEX NON-NATIVE transition *)
CompleteRecovery(cid, ctype, fid) ==
    /\ <<fid, cid>> \in recovery_ops
    /\ <<cid, ctype, fid, "recovering">> \in clients
    /\ network = "healthy"  (* Can only recover when network is healthy *)
    /\ recovery_ops' = recovery_ops \ {<<fid, cid>>}
    /\ clients' = (clients \ {<<cid, ctype, fid, "recovering">>}) \cup {<<cid, ctype, fid, "ready">>}
    /\ UNCHANGED <<factories, network, step_counter>>

(* Recovery timeout - NON-NATIVE transition based on temporal constraint *)
RecoveryTimeoutTransition(cid, ctype, fid) ==
    /\ <<fid, cid>> \in recovery_ops
    /\ <<cid, ctype, fid, "recovering">> \in clients
    /\ step_counter >= RecoveryTimeoutValue
    /\ recovery_ops' = recovery_ops \ {<<fid, cid>>}
    /\ clients' = (clients \ {<<cid, ctype, fid, "recovering">>}) \cup {<<cid, ctype, fid, "terminated">>}
    /\ UNCHANGED <<factories, network, step_counter>>

(* Terminate client - NATIVE transition *)
TerminateClient(cid, ctype, fid) ==
    /\ <<cid, ctype, fid, "ready">> \in clients
    /\ clients' = clients \ {<<cid, ctype, fid, "ready">>}
    /\ UNCHANGED <<factories, network, recovery_ops, step_counter>>

(* Step counter increment *)
IncrementStep ==
    /\ step_counter' = step_counter + 1
    /\ UNCHANGED <<factories, clients, network, recovery_ops>>

(* Define variable tuple for fairness specifications *)
vars == <<factories, clients, network, recovery_ops, step_counter>>

(* Next state relation - combines all possible transitions *)
Next ==
    \/ NetworkPartition
    \/ NetworkRecovery
    \/ \E fid \in factories, ctype \in ClientTypes : InitializeClient(fid, ctype)
    \/ \E cid, ctype, fid : ClientReady(cid, ctype, fid)
    \/ \E cid, ctype, fid : ClientFailFromPartition(cid, ctype, fid)
    \/ \E cid, ctype, fid : StartRecovery(cid, ctype, fid)
    \/ \E cid, ctype, fid : CompleteRecovery(cid, ctype, fid)
    \/ \E cid, ctype, fid : RecoveryTimeoutTransition(cid, ctype, fid)
    \/ \E cid, ctype, fid : TerminateClient(cid, ctype, fid)
    \/ IncrementStep

(* Specification definition with fairness constraints *)
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

(* TEMPORAL PROPERTIES - The unique value TLA+ provides *)

(* SAFETY: No two factories manage the same client ID *)
ClientUniqueness ==
    \A cid1, cid2, ctype1, ctype2, fid1, fid2, state1, state2 :
        /\ <<cid1, ctype1, fid1, state1>> \in clients
        /\ <<cid2, ctype2, fid2, state2>> \in clients
        /\ cid1 = cid2
        => (fid1 = fid2 /\ ctype1 = ctype2)

(* SAFETY: Recovery operations only exist for failed/recovering clients *)
RecoveryConsistency ==
    \A fid, cid \in recovery_ops :
        \E ctype \in ClientTypes, state \in {"failed", "recovering"} :
            <<cid, ctype, fid, state>> \in clients

(* LIVENESS: Eventually all network partitions are healed *)
NetworkHealing ==
    <>(network = "healthy")

(* LIVENESS: Clients that fail eventually either recover or terminate *)
ClientEventualResolution ==
    \A cid, ctype, fid :
        (<<cid, ctype, fid, "failed">> \in clients) => <>(<<cid, ctype, fid, "ready">> \in clients)

(* FAIRNESS: Recovery operations get a chance to complete *)
RecoveryFairness ==
    WF_vars(<<Next>>)

(* TEMPORAL INVARIANTS - Properties that must hold over time *)

(* Invariants that must always be true *)
Inv1 == TypeOK
Inv2 == Cardinality(factories) <= MaxFactories
Inv3 == \A fid \in factories : Cardinality(GetFactoryClients(fid)) <= MaxClients
Inv4 == ClientUniqueness
Inv5 == RecoveryConsistency

(* THEOREMS: Prove that the specification maintains invariants *)

THEOREM Spec => []Inv1
THEOREM Spec => []Inv2
THEOREM Spec => []Inv3
THEOREM Spec => []Inv4
THEOREM Spec => []Inv5

(* LIVENESS THEOREMS: Prove temporal properties *)

THEOREM Spec => NetworkHealing
THEOREM Spec => []ClientEventualResolution

================================================================