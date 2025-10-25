# **Tech Stack Configuration**

This document outlines the technologies and conventions used a general purpose web app like this.
It serves as a reference for both implementation and onboarding.

---

## 🧱 Frontend Stack

### Core Framework

* **React (18)** — primary UI library. It remains the most widely adopted, has deep ecosystem support, and meets our performance goals.
* **TypeScript** — adds static typing for better data safety and predictable behavior; the compile overhead is worthwhile for stability.
* **Vite (≥ 5)** — frontend bundler and dev server. Provides instant hot-reloads and extremely fast local builds compared to Webpack.

### Routing & State

* **TanStack Router (v1)** — SPA router that maps URL changes (e.g. `/home → /app`) to React components, enabling fast, type-safe navigation.
* **TanStack Query (v4)** — manages *server state* by handling fetch, cache, and synchronization logic automatically.
* **Zustand** — will manage *client-only* state shared across components (e.g., user-configurable settings).

### Styling

* **Tailwind CSS** — utility-first styling framework.
* **Tailwind Forms** — improves default form controls and layout consistency.
  *(Radix UI or Headless UI may be added later for accessible components.)*

### Package Manager

* **pnpm** — fast, disk-efficient Node package manager.
  Bundling and dev serving are handled by **Vite**, not by pnpm itself.

### Testing

* **Vitest** — Vite-native test runner for fast logic and component tests; integrates cleanly with React Testing Library.
* **Playwright** — end-to-end browser automation for UI and functional testing.

### Logging & Telemetry

* **Grafana Faro** — frontend telemetry SDK for capturing anonymized performance and error data.
  → Logs flow through **Grafana Alloy → Loki** for centralized analysis.
  → Minimal PII capture; manual instrumentation discouraged.

---

## ⚙️ Backend Stack

### Core Framework

* **TypeScript** — keeps schema parity with the frontend and edge functions.
* **ElysiaJS (≥ 1.0)** — lightweight REST framework offering high performance, strong typing, and automatic OpenAPI documentation.
* **Bun (≥ 1.1)** — runtime + toolchain + bundler + package manager. Much faster than Node .js and widely supported.

### Database & ORM

* **PostgreSQL** — primary relational database.
* **Drizzle ORM (v0.30+)** — type-safe query builder eliminating manual SQL mappings.
* **drizzle-kit** — CLI for generating and running SQL migrations; helps prevent data loss.
* **postgres.js** — Bun-compatible PostgreSQL driver, integrates seamlessly with Drizzle.

### Data Validation

* **Valibot** — faster, smaller alternative to Zod with equivalent schema ergonomics.
  Schemas can export to JSON Schema for API docs or LLM function calling.

### AI Integration

* **Vercel AI SDK (@ai-sdk)** — unified interface for OpenAI-compatible models (via OpenRouter).
  Handles prompt calls, streaming, and structured responses validated with Valibot.

### Observability & Logging

* **Logfire-JS** — simple OpenTelemetry-compatible logger for spans and traces.
* **Grafana Alloy** — unified collector/agent that redacts and forwards logs, metrics, and traces.
* **Grafana Cloud Stack** — managed backends for telemetry:

  * **Loki**  → logs
  * **Prometheus** → metrics
  * **Tempo**  → traces
    Using the **Grafana Cloud Free Tier** initially (≈ 50 GB logs / 14-day retention).
    Self-hosting may follow once we move full-time.

### Caching and Queues:
* **Redis** — caching expensive operations and idempotency checks
* **Redis Streams** (>5.0) — Advanced functionality for queues. 
---

## 🧩 Version & Compatibility Notes

| Library                | Key Version / Usage                                              |
| ---------------------- | ---------------------------------------------------------------- |
| **TanStack Query v4**  | Use `useQuery({ queryKey, queryFn })`, *not* `useQuery(key, fn)` |
| **TanStack Router v1** | Object-based route definitions                                   |
| **React 18**           | Use `createRoot()` (not `ReactDOM.render()`)                     |
| **ElysiaJS ≥ 1.0**     | New plugin API                                                   |
| **Bun ≥ 1.1**          | Stable ESM + fetch APIs                                          |
| **Drizzle ORM ≥ 0.30** | Stable schema inference                                          |


---

## 🧩 Deployment, Authentication & Security

### Deployment & Environment
- **Deployment Targets:**  
  Render (for backend services) and Supabase (for database and authentication).
- **CI/CD:**  
  Managed via **GitHub Actions** for automated builds, testing, and deployments.
- **Environment Variables:**  
  Stored in `.env.*` files. All required variables must be validated at startup using **Valibot** to guarantee correctness before runtime.  
- **CDN:**  
  Supabase CDN may be introduced later when edge delivery or caching is needed.

### Authentication
- **Supabase Auth** — handles authentication, authorization, and user management.  
  Integrates directly with PostgreSQL and frontend SDKs to simplify session handling.

### Security
- **Secrets Management:**  
  All secrets must be provided through environment variables and never stored in code or version control.  
- **Telemetry & Logs:**  
  All logs, traces, and telemetry must be redacted or anonymized before leaving the system.

*(Monorepo structure, environment setup, and architecture decision records (ADRs) will be documented separately in the main repository README and `/docs` folder.)*

---

## ⛘️ Forbidden Libraries / Patterns

* **No Redux** — TanStack Query handles server state.
* **No Axios** — use native `fetch`.
* **No class components** — React function components only.
* **No implicit `any` or unchecked JSON** — validate all inbound/outbound data with Valibot.
* **Don’t over-optimize** — choose the simplest correct solution.
  If a TS component becomes performance-critical, implement that portion in Rust.

---

## 🧠 Guiding Principles

1. **Type safety first** — all data crossing service boundaries must be schema-validated.
2. **Observability by default** — all services emit metrics/logs/traces via Alloy.
3. **Minimal lock-in** — all major components (ORM, LLM API, telemetry) are provider-agnostic.
4. **Simplicity > Cleverness** — prefer clear, documented patterns over exotic optimizations.

---

**AI Instruction:**
Always use these exact versions and libraries unless there’s a compelling reason not to.
If suggesting an alternative, explicitly explain *why* it’s superior and what trade-offs it introduces.