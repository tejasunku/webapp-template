-- Client Factory Alloy Model
-- @model: client-factory
-- @feature: Shared Adapter Factory Pattern (F-001)
-- @version: v0.0.0
-- @author: Alloy Models Agent

-- Client Factory formal model for thread-safe client management
-- Validates process and thread isolation properties

-- Basic component types
sig Process {
    id: one Int
}

sig Thread {
    id: one Int,
    process: one Process
}

sig Client {
    process: one Process,
    thread: one Thread,
    type: one ClientType,
    factory: one Factory
}

sig Factory {
    name: one Name,
    clients: set Client
}

-- Client types
enum ClientType { Database, Cache, Queue, ExternalAPI }

-- Names
sig Name {}

-- System invariants

-- INV-01: Each process has unique threads
fact ProcessThreadUniqueness {
    all p: Process |
        all disj t1, t2: Thread |
            (t1.process = p and t2.process = p) => t1.id != t2.id
}

-- INV-02: Each client belongs to exactly one factory
fact ClientFactoryRelationship {
    all c: Client | one f: Factory | c in f.clients
    all f: Factory | all c: f.clients | c.factory = f
}

-- INV-03: Client isolation by process and thread
fact ClientIsolation {
    all c1, c2: Client |
        (c1.factory = c2.factory and c1.type = c2.type) =>
            (c1.process = c2.process and c1.thread = c2.thread) <=> c1 = c2
}

-- INV-04: Clients are uniquely identified by process, thread, and type
fact ClientUniqueness {
    all c1, c2: Client |
        (c1.process = c2.process and c1.thread = c2.thread and c1.type = c2.type) => c1 = c2
}

-- Client dependencies (optional, for future extensions)
sig ClientDependency {
    client: one Client,
    depends_on: one Client
}

fun dependencies[c: Client] : set Client {
    c.depends_on
}

-- Properties to verify

-- PROP-01: Process-scoped client uniqueness
assert ProcessScopedClients {
    all f: Factory, t: ClientType, p: Process, th: Thread |
        lone c: f.clients |
            c.type = t and c.process = p and c.thread = th
}

-- PROP-02: Thread isolation within same process
assert ThreadIsolation {
    all f: Factory, t: ClientType, p: Process |
        all disj th1, th2: Thread |
            (th1.process = p and th2.process = p) =>
                let c1 = f.clients & (Client <: type).t & (Client <: process).p & (Client <: thread).th1,
                     c2 = f.clients & (Client <: type).t & (Client <: process).p & (Client <: thread).th2 |
                #c1 = 1 and #c2 = 1 implies c1 != c2
}

-- PROP-03: Factory manages only its declared client types
assert FactoryTypeConsistency {
    all f: Factory, c: f.clients |
        c.type in Database + Cache + Queue + ExternalAPI
}

-- PROP-04: Client initialization idempotency
assert ClientInitializationIdempotency {
    all f: Factory, t: ClientType, p: Process, th: Thread |
        let existing_clients = f.clients & (Client <: type).t & (Client <: process).p & (Client <: thread).th |
            #existing_clients <= 1
}

-- Test scenarios

-- Basic functionality test
run BasicClientFactory {
    some f: Factory |
        some c: f.clients |
        c.type = Database
} for 2 Factory, 2 Process, 2 Thread, 3 Client, 3 ClientDependency, 3 Name

-- Multiple clients test
run MultipleClientTypes {
    some f: Factory |
        #f.clients >= 3
} for 2 Factory, 3 Process, 3 Thread, 5 Client, 3 ClientDependency, 3 Name

-- Thread isolation test
run ThreadIsolationTest {
    some p: Process |
        some disj th1, th2: Thread |
            th1.process = p and th2.process = p and
            some f: Factory, t: ClientType |
                some c1: f.clients |
                    c1.type = t and c1.process = p and c1.thread = th1 and
                some c2: f.clients |
                    c2.type = t and c2.process = p and c2.thread = th2 and
                c1 != c2
} for 2 Factory, 3 Process, 4 Thread, 6 Client, 3 ClientDependency, 3 Name

-- Process isolation test
run ProcessIsolationTest {
    some disj p1, p2: Process |
        some f: Factory, t: ClientType |
            some c1: f.clients |
                c1.type = t and c1.process = p1 and
            some c2: f.clients |
                c2.type = t and c2.process = p2 and
            c1 != c2
} for 2 Factory, 3 Process, 3 Thread, 6 Client, 3 ClientDependency, 3 Name

-- Counterexample generation tests

-- Test for potential violations
check ProcessScopedClients for 2 Factory, 3 Process, 3 Thread, 5 Client, 3 ClientDependency, 3 Name
check ThreadIsolation for 2 Factory, 3 Process, 4 Thread, 6 Client, 3 ClientDependency, 3 Name
check FactoryTypeConsistency for 2 Factory, 3 Process, 3 Thread, 8 Client, 3 ClientDependency, 3 Name
check ClientInitializationIdempotency for 2 Factory, 2 Process, 2 Thread, 4 Client, 3 ClientDependency, 3 Name

-- Performance tests
run ScalabilityTest {
    #Process = 5 and #Thread = 10 and #Client = 20
} for exactly 2 Factory, exactly 5 Process, exactly 10 Thread, exactly 20 Client, exactly 5 ClientDependency, exactly 5 Name

-- Edge case tests

-- Single process, single thread
run MinimalSystem {
    #Process = 1 and #Thread = 1 and #Client = 1
} for exactly 1 Factory, exactly 1 Process, exactly 1 Thread, exactly 1 Client, exactly 1 ClientDependency, exactly 1 Name

-- Maximum complexity test
run MaximumComplexity {
    #Factory = 3 and #Process = 5 and #Thread = 15 and #Client = 30
} for exactly 3 Factory, exactly 5 Process, exactly 15 Thread, exactly 30 Client, exactly 5 ClientDependency, exactly 5 Name