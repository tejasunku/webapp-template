# Claude Code Configuration - Teja Pattern Development Environment

## =€ CRITICAL: CONCURRENT EXECUTION & FILE MANAGEMENT

**ABSOLUTE RULES**:
1. ALL operations MUST be concurrent/parallel in a single message
2. **NEVER save working files, text/mds and tests to the root folder**
3. ALWAYS organize files in appropriate subdirectories
4. **USE CLAUDE CODE'S TASK TOOL** for spawning agents concurrently, not just MCP

### ¡ GOLDEN RULE: "1 MESSAGE = ALL RELATED OPERATIONS"

**MANDATORY PATTERNS**:
- **TodoWrite**: ALWAYS batch ALL todos in ONE call (5-10+ todos minimum)
- **Task tool (Claude Code)**: ALWAYS spawn ALL agents in ONE message with full instructions
- **File operations**: ALWAYS batch ALL reads/writes/edits in ONE message
- **Bash commands**: ALWAYS batch ALL terminal operations in ONE message
- **Memory operations**: ALWAYS batch ALL memory store/retrieve in ONE message

### <¯ CRITICAL: Claude Code Task Tool for Agent Execution

**Claude Code's Task tool is the PRIMARY way to spawn agents:**
```javascript
//  CORRECT: Use Claude Code's Task tool for parallel agent execution
[Single Message]:
  Task("Research agent", "Analyze requirements and patterns...", "researcher")
  Task("Coder agent", "Implement core features...", "coder")
  Task("Tester agent", "Create comprehensive tests...", "tester")
  Task("Reviewer agent", "Review code quality...", "reviewer")
  Task("Architect agent", "Design system architecture...", "system-architect")
```

**MCP tools are ONLY for coordination setup:**
- `mcp__claude-flow__swarm_init` - Initialize coordination topology
- `mcp__claude-flow__agent_spawn` - Define agent types for coordination
- `mcp__claude-flow__task_orchestrate` - Orchestrate high-level workflows

### =Á File Organization Rules

**NEVER save to root folder. Use these directories:**
- `/src` - Source code files
- `/tests` - Test files
- `/docs` - Documentation and markdown files
- `/config` - Configuration files
- `/scripts` - Utility scripts
- `/examples` - Example code

## <× Teja Pattern Development Workflow

### Core Development Philosophy

This project follows the **Teja Pattern** - a systematic development methodology that binds conceptual truth to executable truth through explicit, testable artifacts.

**Development Loop:**
```
Intent ’ Resources ’ Responsibilities ’ Formal Models ’ Behavior ’ Schemas ’ Tests ’ Implementation
```

### <¯ Milestone-Driven Development with Red-Green-Refactor

#### Milestone Testing Strategy

For every milestone, we follow a disciplined **Red-Green-Refactor** cycle:

1. **Test Generation**: Create comprehensive tests from Gherkin specifications
2. **Test Classification**: Identify which tests should pass vs fail
3. **Implementation**: Implement code to make failing tests pass one by one

#### Test Expectations by Category:

** Expected to Pass Initially:**
- Interface tests for existing behavior
- Tests on current working functionality
- Shared schema validation for existing contracts
- Basic service connectivity tests

**L Expected to Fail Initially (Focus Areas):**
- New feature behavior tests
- Domain logic for new business rules
- Integration tests for new service interactions
- Edge case and error handling tests

#### Implementation Strategy:

```javascript
// Milestone Development Workflow
const milestoneWorkflow = {
  1: "Generate comprehensive tests from Gherkin specifications",
  2: "Run all tests and classify results (passing vs failing)",
  3: "Prioritize failing tests by business value and dependencies",
  4: "Implement code to make highest priority failing test pass",
  5: "Re-run tests - ensure previous passes still pass",
  6: "Move to next failing test - repeat until all pass",
  7: "Run full test suite - validate milestone completion"
};
```

#### Practical Implementation Pattern:

```bash
# For any milestone development:
make agent-behavior    # Generate Gherkin from formal models
make agent-schemas     # Create shared and internal schemas
make agent-test        # Generate comprehensive test suite

# Initial test run - see what passes/fails
make test

# Focus on failing tests one by one:
# 1. Pick highest priority failing test
# 2. Implement minimal code to make it pass
# 3. Re-run tests to verify
# 4. Repeat until all tests pass

# Final validation
make validate-testing  # Complete testing strategy validation
```

## > Available AI Agents (54 Total)

### Core Development
`coder`, `reviewer`, `tester`, `planner`, `researcher`

### Swarm Coordination
`hierarchical-coordinator`, `mesh-coordinator`, `adaptive-coordinator`, `collective-intelligence-coordinator`, `swarm-memory-manager`

### Consensus & Distributed
`byzantine-coordinator`, `raft-manager`, `gossip-coordinator`, `consensus-builder`, `crdt-synchronizer`, `quorum-manager`, `security-manager`

### Performance & Optimization
`perf-analyzer`, `performance-benchmarker`, `task-orchestrator`, `memory-coordinator`, `smart-agent`

### GitHub & Repository
`github-modes`, `pr-manager`, `code-review-swarm`, `issue-tracker`, `release-manager`, `workflow-automation`, `project-board-sync`, `repo-architect`, `multi-repo-swarm`

### SPARC Methodology
`sparc-coord`, `sparc-coder`, `specification`, `pseudocode`, `architecture`, `refinement`

### Specialized Development
`backend-dev`, `mobile-dev`, `ml-developer`, `cicd-engineer`, `api-docs`, `system-architect`, `code-analyzer`, `base-template-generator`

### Testing & Validation
`tester`, `tdd-london-swarm`, `production-validator`

### Migration & Planning
`migration-planner`, `swarm-init`

## <¯ Claude Code vs MCP Tools

### Claude Code Handles ALL EXECUTION:
- **Task tool**: Spawn and run agents concurrently for actual work
- File operations (Read, Write, Edit, MultiEdit, Glob, Grep)
- Code generation and programming
- Bash commands and system operations
- Implementation work
- Project navigation and analysis
- TodoWrite and task management
- Git operations
- Package management
- Testing and debugging

### MCP Tools ONLY COORDINATE:
- Swarm initialization (topology setup)
- Agent type definitions (coordination patterns)
- Task orchestration (high-level planning)
- Memory management
- Neural features
- Performance tracking
- GitHub integration

**KEY**: MCP coordinates the strategy, Claude Code's Task tool executes with real agents.

## =€ Agent Execution Flow with Claude Code

### The Correct Pattern:

1. **Optional**: Use MCP tools to set up coordination topology
2. **REQUIRED**: Use Claude Code's Task tool to spawn agents that do actual work
3. **REQUIRED**: Each agent runs hooks for coordination
4. **REQUIRED**: Batch all operations in single messages

### Example Full-Stack Development:

```javascript
// Single message with all agent spawning via Claude Code's Task tool
[Parallel Agent Execution]:
  // Claude Code's Task tool spawns real agents concurrently
  Task("Backend Developer", "Build REST API with Express. Use hooks for coordination.", "backend-dev")
  Task("Frontend Developer", "Create React UI. Coordinate with backend via memory.", "coder")
  Task("Database Architect", "Design PostgreSQL schema. Store schema in memory.", "code-analyzer")
  Task("Test Engineer", "Write Jest tests. Check memory for API contracts.", "tester")
  Task("DevOps Engineer", "Setup Docker and CI/CD. Document in memory.", "cicd-engineer")
  Task("Security Auditor", "Review authentication. Report findings via hooks.", "reviewer")

  // All todos batched together
  TodoWrite { todos: [...8-10 todos...] }

  // All file operations together
  Bash "mkdir -p app/{src,tests,docs,config}"
  Write "backend/server.js"
  Write "frontend/App.jsx"
  Write "database/schema.sql"
```

## =Ë Agent Coordination Protocol

### Every Agent Spawned via Task Tool MUST:

**1ã BEFORE Work:**
```bash
npx claude-flow@alpha hooks pre-task --description "[task]"
npx claude-flow@alpha hooks session-restore --session-id "swarm-[id]"
```

**2ã DURING Work:**
```bash
npx claude-flow@alpha hooks post-edit --file "[file]" --memory-key "swarm/[agent]/[step]"
npx claude-flow@alpha hooks notify --message "[what was done]"
```

**3ã AFTER Work:**
```bash
npx claude-flow@alpha hooks post-task --task-id "[task]"
npx claude-flow@alpha hooks session-end --export-metrics true
```

## <¯ Milestone Development Commands

### Complete Development Workflow

```bash
# 1. Generate specifications and behavior
make workflow-formal        # Complete formal verification workflow
make workflow-behavior      # Behavior ’ Schemas workflow

# 2. Create comprehensive test suite
make agent-test             # Generate interface and domain tests

# 3. Initial test assessment
make test                   # Run all tests - see what passes/fails
make test-coverage-analysis # Analyze coverage gaps

# 4. Focused implementation (Red-Green-Refactor)
# Identify failing tests, then implement one by one:
make test-interface        # Test service interfaces (should mostly pass)
make test-domain          # Test domain logic (focus on failures here)

# 5. Implementation cycle:
# While tests are failing:
#   a. Pick highest priority failing test
#   b. Implement minimal code to make it pass
#   c. Re-run tests
#   d. Repeat until all pass

# 6. Final validation
make validate-testing      # Complete testing strategy validation
make test                  # Full test suite - should all pass
```

### Test Prioritization Strategy

**Priority 1 - Fix First:**
- New feature behavior tests
- Domain logic for new business rules
- Integration tests for new functionality
- Critical error handling tests

**Priority 2 - Fix Next:**
- Edge case scenarios
- Performance-related tests
- Security validation tests
- Complex workflow tests

**Priority 3 - Fix Last:**
- Minor UI improvements
- Nice-to-have features
- Optimization opportunities
- Documentation tests

## =' Testing Strategy Commands

### Interface vs Domain Testing

```bash
# Interface tests (service contracts) - should mostly pass
make test-interface         # Test shared schemas and service boundaries

# Domain tests (business logic) - focus of new implementation
make test-domain           # Test internal business rules and invariants

# Contract testing between services
make test-contracts        # Test service-to-service agreements

# Coverage analysis
make test-coverage-analysis # See what's covered vs missing

# Validate test mapping to requirements
make test-mapping          # Ensure every Gherkin scenario has tests
```

### Schema Validation

```bash
# Validate schema structure and classification
make schema-validate       # Ensure shared vs internal schemas are correct
make schema-coverage       # Analyze schema completeness

# Behavior validation
make gherkin-validate      # Check Gherkin syntax and completeness
make gherkin-coverage      # Analyze scenario coverage
```

## =€ Quick Start for New Milestone

```bash
# 1. Set up environment
make setup

# 2. Generate all artifacts from specifications
make workflow-behavior      # Generate behavior and schemas
make agent-test             # Generate comprehensive tests

# 3. Initial assessment
make test                   # See what passes vs fails

# 4. Focused implementation cycle
while [ $? -ne 0 ]; do
  echo "= Identify highest priority failing test"
  echo "=' Implement minimal code to make it pass"
  make test
done

# 5. Final validation
make validate-testing
echo " Milestone complete - all tests passing!"
```

## <¯ Success Criteria

### Milestone Completion Requirements:
-  **All Tests Pass**: Every generated test passes
-  **Behavior Coverage**: All Gherkin scenarios are tested
-  **Schema Validation**: All shared and internal schemas validated
-  **Interface Contracts**: All service interfaces working correctly
-  **Domain Logic**: All business rules implemented correctly
-  **Code Quality**: Passes linting, type checking, and formatting

### Quality Gates:
-  **Test Coverage**: Minimum 90% for critical paths
-  **Schema Compliance**: All data validated at boundaries
-  **Interface Consistency**: All service contracts honored
-  **Documentation**: All code and schemas properly documented

## =à Development Tools Integration

### Environment Setup
```bash
# Required MCP servers (Claude Flow required, others optional)
claude mcp add claude-flow npx claude-flow@alpha mcp start
claude mcp add ruv-swarm npx ruv-swarm mcp start  # Optional: Enhanced coordination
claude mcp add flow-nexus npx flow-nexus@latest mcp start  # Optional: Cloud features
```

### Development Environment
- **Runtime**: Bun (>= 1.1)
- **Package Manager**: pnpm with workspaces
- **Testing**: Vitest + Playwright
- **Validation**: Valibot schemas
- **Documentation**: Gherkin features

### Code Quality Tools
- **TypeScript**: Strict mode enabled
- **Linting**: ESLint + Prettier
- **Testing**: Vitest for unit/integration, Playwright for E2E
- **Validation**: Valibot for runtime schema validation

---

Remember: **Claude Flow coordinates, Claude Code creates!**

Focus on making failing tests pass one by one, following the Red-Green-Refactor cycle for systematic, test-driven development.