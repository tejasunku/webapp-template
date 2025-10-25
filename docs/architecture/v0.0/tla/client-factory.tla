------------------------ MODULE ClientFactory ------------------------
(* @spec: client-factory-dynamics *)
(* @feature: Shared Adapter Factory Pattern (F-001) *)
(* @version: v0.0.0 *)
(* @author: TLA+ Models Agent *)

(* TLA+ specification for client factory dynamic behavior *)
(* Models state transitions, temporal properties, and concurrency *)

EXTENDS Naturals, Sequences, FiniteSets, TLC

(* Constants *)
CONSTANT
    MaxProcesses,           (* Maximum number of processes *)
    MaxThreads,             (* Maximum number of threads per process *)
    MaxClients,             (* Maximum number of client instances *)
    ClientTypes             (* Set of possible client types *)

(* Variables *)
VARIABLE
    processes,              (* Set of active processes *)
    threads,                (* Set of active threads *)
    clients,                (* Set of active clients *)
    factories,              (* Set of client factories *)
    clientCount             (* Counter for unique client IDs *)

(* Type definitions *)
TypeOK ==
    /\ processes \subseteq SUBSET Nat
    /\ threads \subseteq SUBSET (Nat \X Nat)  (* (pid, tid) pairs *)
    /\ clients \subseteq SUBSET (Nat \X ClientTypes \X Nat \X Nat)  (* (id, type, pid, tid) *)
    /\ factories \subseteq SUBSET ClientTypes
    /\ clientCount \in Nat

(* Initial state predicate *)
Init ==
    /\ processes = {}
    /\ threads = {}
    /\ clients = {}
    /\ factories = ClientTypes
    /\ clientCount = 0

(* Helper functions *)

GetProcessClients(pid, ttype) ==
    {<<id, ctype, p, t>> \in clients : p = pid /\ ctype = ttype}

GetThreadClients(pid, tid, ttype) ==
    {<<id, ctype, p, t>> \in clients : p = pid /\ t = tid /\ ctype = ttype}

ClientExists(pid, tid, ttype) ==
    \E <<id, ctype, p, t>> \in clients : p = pid /\ t = tid /\ ctype = ttype

(* State transitions *)

(* New process creation *)
CreateProcess(pid) ==
    /\ pid \notin processes
    /\ Cardinality(processes) < MaxProcesses
    /\ processes' = processes \cup {pid}
    /\ UNCHANGED <<threads, clients, factories, clientCount>>

(* New thread creation within process *)
CreateThread(pid, tid) ==
    /\ pid \in processes
    /\ <<pid, tid>> \notin threads
    /\ Cardinality({<<p, t>> \in threads : p = pid}) < MaxThreads
    /\ threads' = threads \cup {<<pid, tid>>}
    /\ UNCHANGED <<processes, clients, factories, clientCount>>

(* Client initialization *)
InitClient(pid, tid, ctype) ==
    /\ pid \in processes
    /\ <<pid, tid>> \in threads
    /\ ctype \in factories
    /\ ~ClientExists(pid, tid, ctype)
    /\ clientCount < MaxClients
    /\ LET newClients == clients \cup {<<clientCount, ctype, pid, tid>>}
           IN clients' = newClients
    /\ clientCount' = clientCount + 1
    /\ UNCHANGED <<processes, threads, factories>>

(* Client reuse (same process, same thread, same type) *)
ReuseClient(pid, tid, ctype) ==
    /\ ClientExists(pid, tid, ctype)
    /\ UNCHANGED <<processes, threads, clients, factories, clientCount>>

(* Next state relation *)
Next ==
    \/ \E pid \in Nat : CreateProcess(pid)
    \/ \E pid \in processes, tid \in Nat : CreateThread(pid, tid)
    \/ \E pid \in processes, tid \in Nat, ctype \in ClientTypes :
           /\ ~ClientExists(pid, tid, ctype)
           /\ InitClient(pid, tid, ctype)
    \/ \E pid, tid \in Nat, ctype \in ClientTypes :
           /\ ClientExists(pid, tid, ctype)
           /\ ReuseClient(pid, tid, ctype)

(* Temporal properties *)

(* SAFETY: No two clients of same type in different processes/threads *)
TypeSafety ==
    \A pid1, tid1, pid2, tid2 \in Nat, ctype \in ClientTypes :
        /\ <<pid1, tid1>> \in threads
        /\ <<pid2, tid2>> \in threads
        /\ ClientExists(pid1, tid1, ctype)
        /\ ClientExists(pid2, tid2, ctype)
        => (pid1 = pid2 /\ tid1 = tid2)

(* LIVENESS: Every request for client eventually gets a client *)
ClientLiveness ==
    \A pid \in processes, tid \in Nat, ctype \in ClientTypes :
        /\ <<pid, tid>> \in threads
        => <>\/ClientExists(pid, tid, ctype)

(* INVARIANTS *)
Inv1 == TypeOK
Inv2 == Cardinality(processes) <= MaxProcesses
Inv3 == \A pid \in processes : Cardinality({<<p, t>> \in threads : p = pid}) <= MaxThreads
Inv4 == Cardinality(clients) <= MaxClients

(* THEOREM: System maintains invariants *)
THEOREM Spec => []Inv1
THEOREM Spec => []Inv2
THEOREM Spec => []Inv3
THEOREM Spec => []Inv4

(* Specification *)
Spec == Init /\ [][Next]_<<processes, threads, clients, factories, clientCount>>

================================================================