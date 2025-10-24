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
Resources
 ↓
Division of Responsibility
 ↓
Formal Models (Alloy / TLA⁺)
 ↓
Behavior (Gherkin)
 ↓
Schemas
 ↓
Tests
 ↓
Implementation (Domain / SDK / App / Tests)
 ↓
Versioning & Governance
 ↺
```

Each stage produces structured outputs that the next consumes.
Iteration happens through **milestones** — discrete, versioned snapshots of truth.

---

## 3 · Layer Responsibilities

| Layer                          | Description                                               | Artifact                               |
| ------------------------------ | --------------------------------------------------------- | -------------------------------------- |
| **Intent**                     | Defines purpose, goals, and constraints.                  | `/docs/intent.md`                      |
| **Resources**                  | Lists external systems and dependencies.                  | `/docs/architecture/vX.Y/resources.yaml` |
| **Division of Responsibility** | Splits responsibilities across services and contexts.     | `/docs/architecture/vX.Y/responsibilities.yaml` |
| **Formal Models**              | Validates static (Alloy) and dynamic (TLA⁺) consistency.  | `/docs/architecture/vX.Y/alloy/`, `/docs/architecture/vX.Y/tla/` |
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

Each milestone represents a verified, stable state of the system.

* Snapshot models, schemas, and tests.
* Increment milestone when feature set or contracts change.
* Use `/docs/milestones/vX.yaml` to define version dependencies across libraries.

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