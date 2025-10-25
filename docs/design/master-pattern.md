# 🌒 The Teja Pattern — v1.0

*A formal, idempotent, milestone-driven development loop for composable systems*

---

## 1 · Core Philosophy

Every piece of software has two truths:

* the **conceptual truth** (intent, models, behaviors), and
* the **executable truth** (code, data, runtime).

The Teja Pattern binds them through explicit, testable artifacts.
Each artifact exists in one layer of the loop and must have a single responsibility.
No knowledge is implicit, no test is purposeless, and no code exists without provenance.

---

## 2 · The Development Loop

```
Intent
 ↓
Milestone (Business Requirements)
 ↓
Clarify existing Resources
 ↓
Division of Responsibility (update Milestone with specifications learned here)
 ↺ (Loop back if design changes needed)
 ↓
[Formal Models Decision - See /docs/design/formal-model-flow.md]
 ↓
Behavior (Gherkin) (Readable engineer implementation guide. Should always match milestones, but be less intent focused and cohesive. More comprehensive)
 ↺ (Update Milestone if behavior reveals new requirements)
 ↓
Schemas
 ↓
Tests
 ↓
Implementation (Domain / SDK / App / Tests)
 ↓
Versioning & Governance
 ↺ (Loop back to refine any stage based on implementation experience)
```

### Key Feedback Loops

1. **Milestone ↔ Division of Responsibility**: Specifications learned during responsibility division update milestone requirements
2. **Formal Models → Milestone**: Edge cases and constraints discovered update milestone specifications
3. **Gherkin → Milestone**: Behavior specifications may reveal missing requirements
4. **Implementation → Any Stage**: Implementation experience may require refining any previous stage

**Formal Models Usage**: See `/docs/design/formal-model-flow.md` for detailed decision criteria on when to use Alloy and/or TLA+ models.

Each stage produces structured outputs that the next consumes.
Iteration happens through **milestones** — discrete, versioned snapshots of truth.

---

## 2.1 · Formal Model Integration

### Decision-Driven Formal Verification

Formal models are **conditional tools** used only when specific concerns exist:

**Use Alloy for:**
- Schema/interface/data stability problems
- Data consistency and safety concerns
- Complex structural relationships
- Resource sharing and isolation validation

**Use TLA+ for:**
- State machines with non-native transitions (e.g., custom router edge cases)
- Performance guarantees that must be proven
- Race conditions and concurrency concerns
- Complex temporal behavior that isn't natively supported

**Simple behavior goes directly to Gherkin** - native browser events, standard CRUD operations, well-understood patterns.

### Formal Model → Milestone Integration

When formal models are used:
1. **Analyze the concern** using appropriate formal method
2. **Document findings** including edge cases and constraints
3. **Update Milestone** with discovered requirements
4. **Assess acceptability** - are the constraints acceptable or is design refinement needed?
5. **Proceed to Gherkin** with updated understanding

**TLA+ Requirement**: All TLA+ models must be backed by Alloy types, even if the Alloy model is mostly boilerplate for type definitions.

### When Formal Models Are Not Used

Most features proceed directly from **Division of Responsibility → Gherkin** when:
- No data safety concerns exist
- Behavior is simple and well-understood
- No performance guarantees are required
- No race conditions or complex state management

---

## 3 · Layer Responsibilities

| Layer                          | Description                                               | Artifact                               |
| ------------------------------ | --------------------------------------------------------- | -------------------------------------- |
| **Intent**                     | Defines purpose, goals, and constraints.                  | `/docs/intent.md`                      |
| **Milestone**                  | Business requirements and success criteria.               | `/docs/milestones/vX.Y.Z.yaml`        |
| **Resources**                  | Lists external systems and dependencies.                  | `/docs/architecture/vX.Y/resources.yaml` |
| **Division of Responsibility** | Splits responsibilities across services and contexts.     | `/docs/architecture/vX.Y/responsibilities.yaml` |
| **Formal Models**              | Conditional validation for specific concerns.             | `/docs/architecture/vX.Y/alloy/`, `/docs/architecture/vX.Y/tla/` (if needed) |
| **Behavior**                   | Human-readable expected behavior (BDD).                   | `/docs/architecture/vX.Y/*.feature`   |
| **Schemas**                    | Executable data contracts.                                | `/shared/schemas/`                     |
| **Tests**                      | Enforce invariants, behaviors, and regressions.           | `/tests/`                              |
| **Implementation**             | Realized code: domain logic, SDK adapters, apps, and tests. | `/domain/`, `/sdk/`, `/app/`, `/tests/`      |
| **Governance**                 | Policies, automation, CI, and milestone management.       | `/ai/manifest.yaml`, `/docs/milestones/`    |

---

## 4 · Implementation Architecture

### Folder Layout

```
/apps/
  backend/
    elysiajs/        ← Example app following the pattern
      app/           ← Application orchestration and entry points
      domain/        ← Pure business logic and invariants
      sdk/           ← External service adapters and clients
      tests/         ← Test suite for this app
    cache/           ← Cache service implementation
    db/              ← Database service implementation
    queue/           ← Queue service implementation
  frontend/
    <frontend-app>/  ← Future frontend applications
/shared/
  schemas/          ← Shared data contracts and types
  utils/            ← Shared utilities and helpers
  sdk/              ← Shared SDK adapters and client factory
    adapters/
    clientFactory.ts
/docs/
  architecture/
    v0.0/
      resources.yaml
      responsibilities.yaml
      alloy/
      tla/
      *.feature
    v0.1/
      resources.yaml
      responsibilities.yaml
      alloy/
      tla/
      *.feature
  design/
    dev-protocol.md
    master-pattern.md
  intent.md
  milestones/
    v0.0.yaml
    v0.1.yaml
/ai/
  manifest.yaml
  agents/
  policies/
/tests/              ← Global/integration tests
```

All applications (like `elysiajs`) follow the same internal structure with `/app`, `/domain`, `/sdk`, and `/tests` buckets.

---

## 5 · Adapter & SDK Pattern

Adapters represent external resources.
They must follow the **Shared Adapter Protocol (SAP):**

```ts
// @shared/sdk/clientFactory.ts
export function makeScopedClient<T>(init: () => T): () => T {
  let pid = -1, tid = -1;
  let client: T | null = null;
  return () => {
    const newPid = process.pid;
    const newTid = (require("worker_threads") as any)?.threadId ?? 0;
    if (!client || newPid !== pid || newTid !== tid) {
      pid = newPid; tid = newTid;
      client = init();
    }
    return client;
  };
}
```

Each adapter uses this factory to guarantee:

* one client per process/thread,
* automatic re-init on fork/thread change,
* no top-level side effects,
* full idempotency.

**Adapters never export client instances.**
They export *pure async functions* that wrap SDK calls.

---

## 6 · Testing Philosophy

### 6.1 Global vs Local

| Layer         | Purpose                                                                             | Typical Tests                       |
| ------------- | ----------------------------------------------------------------------------------- | ----------------------------------- |
| **Global**    | Integration + behavioral coverage for all features (Gherkin → use-case → adapters). | Feature specs                       |
| **Domain**    | Pure logic / invariant enforcement.                                                 | Invariant or regression tests       |
| **SDK**       | Non-trivial wrapping logic around SDKs (e.g., retries, normalization).              | Mocked retry or normalization tests |
| **App**       | Branching orchestration.                                                            | Edge-condition tests                |
| **Shared**    | Schema round-trip validation.                                                       | Serialization tests                 |

### 6.2 Gherkin Documentation Requirements

**All Gherkin features must include labels for traceability:**

```gherkin
@feature: Feature Name
  @id: F-XXX
  Feature description...

  @scenario: SC-XXX
  Scenario: Scenario description
    Given ...
    When ...
    Then ...
```

**Required Labels:**
- `@feature: Feature Name` - Feature identification
- `@id: F-XXX` - Unique feature identifier
- `@scenario: SC-XXX` - Unique scenario identifier for test mapping

**Test Mapping:**
- Tests must reference Gherkin scenario IDs in their descriptions
- Each test should map 1:1 to a Gherkin scenario
- Test files must include `@scenario: SC-XXX` labels in test descriptions

> **If behavior is tested globally, you do not need a local SDK test.**
> Local tests only exist for nontrivial logic that can't be observed through end-to-end integration.

### 6.2 "Direct I/O" Rule

If a function deterministically maps input → output and has no internal state:

* verify via integration tests,
* rely on TypeScript + schemas for safety,
* no dedicated test required.

### 6.3 Regression Scope

When a bug appears:

1. Add a test where the bug lived (domain, sdk, app).
2. Patch the code.
3. Increment **patch version** for that module.
4. Keep global tests unchanged unless behavior changed.

---

## 7 · Versioning Semantics

| Type      | Trigger                               | Effect                                    |
| --------- | ------------------------------------- | ----------------------------------------- |
| **Patch** | Bug fix or stability improvement.     | Add regression tests.                     |
| **Minor** | New feature or non-breaking behavior. | Add new feature tests.                    |
| **Major** | Backward-incompatible change.         | Update relevant Gherkin + schema + tests. |

Each service or library versions **independently**, while the overall monorepo milestone tracks global coherence.

---

## 8 · Governance and CI

### Manifest Rules (`/ai/manifest.yaml`)

```yaml
sdk_policy:
  - "All adapters must use makeScopedClient()."
  - "No SDK initialized at import time."
  - "Clients reinitialize when PID/thread changes."

test_policy:
  - "Global tests for each Gherkin feature."
  - "Domain tests only for invariants."
  - "SDK tests only for nontrivial transformations or retry logic."
  - "Regression tests live beside their origin module."

doc_policy:
  - "Single canonical /docs/design/master-pattern.md per monorepo."
  - "Local READMEs reference the canonical design doc."

version_policy:
  - "Patch = bug fix, Minor = new feature, Major = breaking change."
```

### CI Loop

1. Type + lint
2. Alloy / TLA⁺ verification
3. Schema generation
4. Test suite
5. Manifest compliance
6. PR summarization + milestone update

---

## 9 · Milestone Workflow

### 9.1 Milestone Philosophy

**Small, frequent, implementable milestones** are the core of the Teja Pattern. Each milestone should be achievable within 1-2 days and provide immediate value.

### 9.2 Milestone Characteristics

**v0.0.0 - The "Hello World" Milestone**
- Duration: ~1 day
- Goal: Validate basic project setup and workflow
- Example: Simple text input with submit button that saves to backend
- Purpose: Prove the development loop works end-to-end

**Incremental Milestones**
- Duration: 1-2 days each
- Goal: Add specific, testable functionality
- Value: Each milestone delivers working features
- Feedback: Implementation experience refines future milestones

### 9.3 Milestone Requirements

**Every milestone must:**
1. **Be Implementable** - Can be completed within 1-2 days
2. **Provide Value** - Delivers working, demonstrable functionality
3. **Be Testable** - Has comprehensive test coverage
4. **Be Documented** - Updated architecture and intent as needed
5. **Be Deployable** - Can be deployed and used immediately

### 9.4 Milestone Workflow

1. **Define Milestone** - Create specific, achievable scope
2. **Implement** - Build functionality using Teja Pattern
3. **Test** - Ensure comprehensive coverage
4. **Validate** - Confirm milestone meets requirements
5. **Deploy** - Release working milestone
6. **Refine** - Update intent and future milestones based on implementation experience

### 9.5 Milestone Artifacts

Each milestone generates:
- Working code implementation
- Comprehensive test suite
- Updated documentation
- Deployment artifacts
- Lessons learned for next milestone

### 9.6 Milestone Files

- `/docs/milestones/vX.Y.Z.yaml` - Milestone definition and requirements
- Implementation code in appropriate service directories
- Test coverage for all new functionality
- Updated architecture documentation

---

## 10 · Scaling & Exports

When extracting a service or library:

1. Copy `/shared/sdk/` and `/docs/design/master-pattern.md`.
2. Include only relevant `/domain`, `/app`.
3. Retain tests and schemas.
4. Create new `/ai/manifest.yaml` for version tracking.

This keeps exported modules autonomous yet philosophically identical.

---

## 11 · Principles Summary

1. **Every artifact serves a neighbor.**
   Intent feeds models; models feed behaviors; behaviors feed tests; tests feed code.
2. **Never test what you don't own.**
   SDKs are assumed correct; wrappers are not.
3. **One client per process.**
   No shared global state.
4. **Behavior is contract; schema is law.**
5. **Documentation is centralized; implementation is local.**
6. **Milestones freeze truth; versions describe motion.**

---

## 12 · Canonical Pattern Summary

| Category       | Rule                                                         |
| -------------- | ------------------------------------------------------------ |
| **Structure**  | `/apps/backend/*`, `/apps/frontend/*`, `/shared/sdk`, `/shared/schemas`, `/docs`, `/ai` |
| **Adapters**   | Pure async functions, one client per process                 |
| **Tests**      | Global > Local > Regression                                  |
| **Docs**       | One canonical design doc per monorepo                        |
| **Versioning** | Patch = fix, Minor = feature, Major = break                  |
| **Governance** | Manifest defines all policies                                |
| **Goal**       | Iterative, provable, idempotent systems                      |

---

## 13 · Final Statement

> **The Teja Pattern** is a closed, living system of design.
> Every artifact mirrors another: behavior implies structure, structure implies law, law implies code.
>
> It replaces heroics with harmony — a development philosophy where correctness emerges from care and iteration, not control.
>
> **Implementation is not improvisation.** It is the final movement of a verified composition.