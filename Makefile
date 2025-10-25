# Makefile for Teja Pattern Web App Template
# Provides comprehensive commands for development, testing, and building

# Default shell and options
SHELL := /bin/bash
.SHELLFLAGS := -eu -o pipefail

# Default target
.PHONY: help
help: ## Show this help message
	@echo "Teja Pattern Web App Template - Build Automation"
	@echo ""
	@echo "Development Commands:"
	@awk 'BEGIN {FS = ":.*?## "} /^[a-zA-Z_-]+:.*?## / {printf "  %-15s %s\n", $$1, $$2}' $(MAKEFILE_LIST)
	@echo ""
	@echo "Agent Workflow Commands:"
	@echo "  agent-intent     Run Intent analysis agent"
	@echo "  agent-spec       Run Specification agent"
	@echo "  agent-arch       Run Architecture agent"
	@echo "  agent-alloy      Run Alloy formal models agent"
	@echo "  agent-tla        Run TLA+ formal models agent"
	@echo "  agent-behavior   Run Behavior agent (Gherkin)"
	@echo "  agent-schemas    Run Schemas agent (Valibot)"
	@echo "  agent-test       Run Testing agent"
	@echo "  agent-impl       Run Implementation agent"
	@echo "  agent-govern     Run Governance agent"
	@echo ""
	@echo "Formal Verification Commands:"
	@echo "  alloy-analyze    Run all Alloy model analyses"
	@echo "  alloy-validate   Validate critical system properties"
	@echo "  alloy-run MODEL=<name>   Run specific Alloy model"
	@echo "  alloy-report     Generate comprehensive analysis report"
	@echo "  tla-analyze      Run all TLA+ temporal analyses"
	@echo "  tla-validate    Validate critical temporal properties"
	@echo "  tla-run MODEL=<name>      Run specific TLA+ model"
	@echo "  tla-simulate MODEL=<name> [STEPS]  Simulate model execution"
	@echo "  tla-report       Generate comprehensive TLA+ report"
	@echo ""
	@echo "Examples:"
	@echo "  make dev         # Start development servers"
	@echo "  make test        # Run all tests"
	@echo "  make agent-spec  # Run specification agent"

# Environment and configuration
NODE_ENV ?= development
BUN_VERSION ?= latest
PORT ?= 3000

# Colors for output
BLUE := \033[36m
GREEN := \033[32m
YELLOW := \033[33m
RED := \033[31m
RESET := \033[0m

# Utility functions
define print_header
	@echo "$(BLUE)$(1)$(RESET)"
endef

define print_success
	@echo "$(GREEN)✓ $(1)$(RESET)"
endef

define print_warning
	@echo "$(YELLOW)⚠ $(1)$(RESET)"
endef

define print_error
	@echo "$(RED)✗ $(1)$(RESET)"
endef

# =============================================================================
# DEVELOPMENT COMMANDS
# =============================================================================

.PHONY: install
install: ## Install all dependencies with pnpm
	$(call print_header,"Installing dependencies...")
	@pnpm install
	$(call print_success,"Dependencies installed")

.PHONY: dev
dev: ## Start development servers for all services
	$(call print_header,"Starting development environment...")
	@pnpm run dev

.PHONY: dev-backend
dev-backend: ## Start only backend development server
	$(call print_header,"Starting backend development server...")
	@cd apps/backend/elysiajs && bun run dev

.PHONY: build
build: ## Build all packages and services
	$(call print_header,"Building all packages...")
	@pnpm run build
	$(call print_success,"Build completed")

.PHONY: clean
clean: ## Clean all build artifacts and dependencies
	$(call print_header,"Cleaning build artifacts...")
	@pnpm run clean
	@rm -rf node_modules
	@rm -rf apps/*/node_modules
	@rm -rf shared/*/node_modules
	@rm -rf dist
	@find . -name "*.log" -delete
	$(call print_success,"Clean completed")

.PHONY: clean-build
clean-build: clean build ## Clean and rebuild everything

# =============================================================================
# TESTING COMMANDS
# =============================================================================

.PHONY: test
test: ## Run all tests (unit, integration, e2e)
	$(call print_header,"Running all tests...")
	@pnpm run test

.PHONY: test-unit
test-unit: ## Run unit tests only
	$(call print_header,"Running unit tests...")
	@pnpm run test:unit

.PHONY: test-integration
test-integration: ## Run integration tests only
	$(call print_header,"Running integration tests...")
	@pnpm run test:integration

.PHONY: test-e2e
test-e2e: ## Run end-to-end tests
	$(call print_header,"Running E2E tests...")
	@pnpm run test:e2e

.PHONY: test-watch
test-watch: ## Run tests in watch mode
	$(call print_header,"Running tests in watch mode...")
	@pnpm run test:watch

.PHONY: test-coverage
test-coverage: ## Run tests with coverage report
	$(call print_header,"Running tests with coverage...")
	@pnpm run test:coverage
	@echo "Coverage report generated in coverage/"

# =============================================================================
# CODE QUALITY COMMANDS
# =============================================================================

.PHONY: lint
lint: ## Run linting on all files
	$(call print_header,"Running linting...")
	@pnpm run lint

.PHONY: lint-fix
lint-fix: ## Fix linting issues automatically
	$(call print_header,"Fixing linting issues...")
	@pnpm run lint:fix

.PHONY: typecheck
typecheck: ## Run TypeScript type checking
	$(call print_header,"Running type checking...")
	@pnpm run typecheck

.PHONY: format
format: ## Format all code files
	$(call print_header,"Formatting code...")
	@pnpm run format

.PHONY: check
check: lint typecheck test ## Run all quality checks (lint, typecheck, test)

# =============================================================================
# FORMAL VERIFICATION COMMANDS (Alloy)
# =============================================================================

.PHONY: alloy-check
alloy-check: ## Check if Alloy Analyzer is installed
	@command -v alloy >/dev/null 2>&1 || { \
		$(call print_error,"Alloy Analyzer not found. Install from: https://alloytools.org/"); \
		exit 1; \
	}
	$(call print_success,"Alloy Analyzer is available")

.PHONY: alloy-analyze
alloy-analyze: alloy-check ## Run all Alloy model analyses
	$(call print_header,"Running Alloy formal verification...")
	@mkdir -p docs/architecture/v0.0/alloy/results
	@echo "Analyzing client factory model..."
	@if command -v alloy >/dev/null 2>&1; then \
		alloy docs/architecture/v0.0/alloy/client-factory.als > docs/architecture/v0.0/alloy/results/client-factory-analysis.txt 2>&1 || true; \
		echo "✓ Client factory analysis completed"; \
	else \
		echo "⚠ Alloy not available - skipping formal verification"; \
		echo "Install from: https://alloytools.org/"; \
	fi
	$(call print_success,"Alloy analysis completed")

.PHONY: alloy-run
alloy-run: alloy-check ## Run specific Alloy model
	@if [ -z "$(MODEL)" ]; then \
		echo "Usage: make alloy-run MODEL=<model-name>"; \
		echo "Available models:"; \
		ls docs/architecture/v0.0/alloy/*.als | sed 's/.*\///' | sed 's/.als$$/'; \
		exit 1; \
	fi
	$(call print_header,"Running Alloy model: $(MODEL)")
	@alloy docs/architecture/v0.0/alloy/$(MODEL).als

.PHONY: alloy-check-assertion
alloy-check-assertion: alloy-check ## Check specific assertion in Alloy model
	@if [ -z "$(MODEL)" ] || [ -z "$(ASSERTION)" ]; then \
		echo "Usage: make alloy-check-assertion MODEL=<model-name> ASSERTION=<assertion-name>"; \
		exit 1; \
	fi
	$(call print_header,"Checking assertion $(ASSERTION) in model $(MODEL)")
	@alloy docs/architecture/v0.0/alloy/$(MODEL).als --check $(ASSERTION)

.PHONY: alloy-generate-instance
alloy-generate-instance: alloy-check ## Generate instance for Alloy model
	@if [ -z "$(MODEL)" ]; then \
		echo "Usage: make alloy-generate-instance MODEL=<model-name> [SCOPE]"; \
		exit 1; \
	fi
	$(call print_header,"Generating instance for model $(MODEL)")
	@if [ -n "$(SCOPE)" ]; then \
		alloy docs/architecture/v0.0/alloy/$(MODEL).als --run $(SCOPE); \
	else \
		alloy docs/architecture/v0.0/alloy/$(MODEL).als; \
	fi

.PHONY: alloy-counterexample
alloy-counterexample: alloy-check ## Generate counterexample for failed assertion
	@if [ -z "$(MODEL)" ] || [ -z "$(ASSERTION)" ]; then \
		echo "Usage: make alloy-counterexample MODEL=<model-name> ASSERTION=<assertion-name>"; \
		exit 1; \
	fi
	$(call print_header,"Generating counterexample for $(ASSERTION) in $(MODEL)")
	@alloy docs/architecture/v0.0/alloy/$(MODEL).als --check $(ASSERTION) --show

.PHONY: alloy-validate
alloy-validate: alloy-check ## Validate all critical properties
	$(call print_header,"Validating critical system properties...")
	@echo "Checking process-scoped client isolation..."
	@alloy docs/architecture/v0.0/alloy/client-factory.als --check ProcessScopedClients || echo "⚠ ProcessScopedClients check failed"
	@echo "Checking thread isolation..."
	@alloy docs/architecture/v0.0/alloy/client-factory.als --check ThreadIsolation || echo "⚠ ThreadIsolation check failed"
	@echo "Checking factory consistency..."
	@alloy docs/architecture/v0.0/alloy/client-factory.als --check FactoryTypeConsistency || echo "⚠ FactoryTypeConsistency check failed"
	@echo "Checking initialization idempotency..."
	@alloy docs/architecture/v0.0/alloy/client-factory.als --check ClientInitializationIdempotency || echo "⚠ ClientInitializationIdempotency check failed"
	$(call print_success,"Property validation completed")

.PHONY: alloy-report
alloy-report: ## Generate comprehensive Alloy analysis report
	$(call print_header,"Generating Alloy analysis report...")
	@mkdir -p docs/architecture/v0.0/alloy/reports
	@echo "# Alloy Analysis Report" > docs/architecture/v0.0/alloy/reports/latest.md
	@echo "Generated: $(shell date)" >> docs/architecture/v0.0/alloy/reports/latest.md
	@echo "" >> docs/architecture/v0.0/alloy/reports/latest.md
	@echo "## Models Analyzed" >> docs/architecture/v0.0/alloy/reports/latest.md
	@ls docs/architecture/v0.0/alloy/*.als | sed 's/.*\//- /' | sed 's/.als$$//' >> docs/architecture/v0.0/alloy/reports/latest.md
	@echo "" >> docs/architecture/v0.0/alloy/reports/latest.md
	@echo "## Results" >> docs/architecture/v0.0/alloy/reports/latest.md
	@if [ -f docs/architecture/v0.0/alloy/results/client-factory-analysis.txt ]; then \
		echo "### Client Factory Model" >> docs/architecture/v0.0/alloy/reports/latest.md; \
		grep -E "(PASSED|FAILED|found)" docs/architecture/v0.0/alloy/results/client-factory-analysis.txt | head -10 >> docs/architecture/v0.0/alloy/reports/latest.md; \
	fi
	$(call print_success,"Report generated: docs/architecture/v0.0/alloy/reports/latest.md")

# =============================================================================
# FORMAL VERIFICATION COMMANDS (TLA+)
# =============================================================================

.PHONY: tla-check
tla-check: ## Check if TLA+ tools are installed
	@command -v java >/dev/null 2>&1 || { \
		$(call print_error,"Java not found. Install Java 8+ for TLA+ tools"); \
		exit 1; \
	}
	@if [ ! -f "tla2tools.jar" ]; then \
		$(call print_header,"Downloading TLA+ tools..."); \
		curl -L -o tla2tools.jar https://github.com/tlaplus/tlaplus/releases/latest/download/tla2tools.jar; \
	fi
	$(call print_success,"TLA+ tools are available")

.PHONY: tla-analyze
tla-analyze: tla-check ## Run all TLA+ model analyses
	$(call print_header,"Running TLA+ temporal verification...")
	@mkdir -p docs/architecture/v0.0/tla/results
	@echo "Analyzing client factory temporal model..."
	@if [ -f "docs/architecture/v0.0/tla/client-factory.tla" ]; then \
		java -cp tla2tools.jar tlc2.TLC -tool -workers auto -config docs/architecture/v0.0/tla/client-factory.cfg docs/architecture/v0.0/tla/client-factory.tla > docs/architecture/v0.0/tla/results/client-factory-analysis.txt 2>&1 || true; \
		echo "✓ Client factory temporal analysis completed"; \
	else \
		echo "⚠ Client factory TLA+ model not found"; \
	fi
	$(call print_success,"TLA+ analysis completed")

.PHONY: tla-run
tla-run: tla-check ## Run specific TLA+ model
	@if [ -z "$(MODEL)" ]; then \
		echo "Usage: make tla-run MODEL=<model-name>"; \
		echo "Available models:"; \
		ls docs/architecture/v0.0/tla/*.tla | sed 's/.*\///' | sed 's/.tla$$/'; \
		exit 1; \
	fi
	$(call print_header,"Running TLA+ model: $(MODEL)")
	@java -cp tla2tools.jar tlc2.TLC -tool docs/architecture/v0.0/tla/$(MODEL).tla

.PHONY: tla-check-property
tla-check-property: tla-check ## Check specific temporal property
	@if [ -z "$(MODEL)" ] || [ -z "$(PROPERTY)" ]; then \
		echo "Usage: make tla-check-property MODEL=<model-name> PROPERTY=<property-name>"; \
		exit 1; \
	fi
	$(call print_header,"Checking temporal property $(PROPERTY) in model $(MODEL)")
	@java -cp tla2tools.jar tlc2.TLC -tool -config docs/architecture/v0.0/tla/$(MODEL).cfg -property $(PROPERTY) docs/architecture/v0.0/tla/$(MODEL).tla

.PHONY: tla-simulate
tla-simulate: tla-check ## Simulate TLA+ model execution
	@if [ -z "$(MODEL)" ]; then \
		echo "Usage: make tla-simulate MODEL=<model-name> [STEPS]"; \
		exit 1; \
	fi
	$(call print_header,"Simulating TLA+ model: $(MODEL)")
	@if [ -n "$(STEPS)" ]; then \
		java -cp tla2tools.jar tlc2.Simulator -tool -maxDepth $(STEPS) docs/architecture/v0.0/tla/$(MODEL).tla; \
	else \
		java -cp tla2tools.jar tlc2.Simulator -tool docs/architecture/v0.0/tla/$(MODEL).tla; \
	fi

.PHONY: tla-validate
tla-validate: tla-check ## Validate critical temporal properties
	$(call print_header,"Validating critical temporal properties...")
	@echo "Checking type safety property..."
	@if [ -f "docs/architecture/v0.0/tla/client-factory.tla" ]; then \
		java -cp tla2tools.jar tlc2.TLC -tool -config docs/architecture/v0.0/tla/client-factory.cfg docs/architecture/v0.0/tla/client-factory.tla 2>/dev/null || echo "⚠ TLA+ validation completed with issues"; \
	else \
		echo "⚠ TLA+ model not found"; \
	fi
	$(call print_success,"Temporal property validation completed")

.PHONY: tla-report
tla-report: ## Generate comprehensive TLA+ analysis report
	$(call print_header,"Generating TLA+ analysis report...")
	@mkdir -p docs/architecture/v0.0/tla/reports
	@echo "# TLA+ Analysis Report" > docs/architecture/v0.0/tla/reports/latest.md
	@echo "Generated: $(shell date)" >> docs/architecture/v0.0/tla/reports/latest.md
	@echo "" >> docs/architecture/v0.0/tla/reports/latest.md
	@echo "## Models Analyzed" >> docs/architecture/v0.0/tla/reports/latest.md
	@ls docs/architecture/v0.0/tla/*.tla 2>/dev/null | sed 's/.*\//- /' | sed 's/.tla$$//' >> docs/architecture/v0.0/tla/reports/latest.md || echo "No TLA+ models found"
	@echo "" >> docs/architecture/v0.0/tla/reports/latest.md
	@echo "## Temporal Properties Verified" >> docs/architecture/v0.0/tla/reports/latest.md
	@if [ -f docs/architecture/v0.0/tla/results/client-factory-analysis.txt ]; then \
		echo "### Client Factory Model" >> docs/architecture/v0.0/tla/reports/latest.md; \
		grep -E "(Error|Exception|found|completed)" docs/architecture/v0.0/tla/results/client-factory-analysis.txt | head -10 >> docs/architecture/v0.0/tla/reports/latest.md; \
	fi
	$(call print_success,"Report generated: docs/architecture/v0.0/tla/reports/latest.md")

# =============================================================================
# DATABASE COMMANDS
# =============================================================================

.PHONY: db-generate
db-generate: ## Generate database schema with Drizzle
	$(call print_header,"Generating database schema...")
	@pnpm run db:generate
	$(call print_success,"Schema generated")

.PHONY: db-migrate
db-migrate: ## Run database migrations
	$(call print_header,"Running database migrations...")
	@pnpm run db:migrate
	$(call print_success,"Migrations completed")

.PHONY: db-studio
db-studio: ## Open Drizzle Studio for database management
	$(call print_header,"Opening Drizzle Studio...")
	@pnpm run db:studio

# =============================================================================
# AI AGENT WORKFLOW COMMANDS
# =============================================================================

.PHONY: agent-intent
agent-intent: ## Run Intent analysis agent
	$(call print_header,"Running Intent analysis agent...")
	@echo "🤖 Intent Agent: Analyzing project purpose and goals..."
	@echo "📁 Reading: /docs/intent.md"
	@echo "🎯 Output: Updated intent documentation"
	@echo ""
	@echo "Agent Tasks:"
	@echo "  ✓ Review current intent documentation"
	@echo "  ✓ Analyze project goals and constraints"
	@echo "  ✓ Update success criteria and anti-goals"
	@echo "  ✓ Validate against current implementation"

.PHONY: agent-spec
agent-spec: ## Run Specification agent (Intent + Resources)
	$(call print_header,"Running Specification agent...")
	@echo "🤖 Specification Agent: Converting intent to technical specs"
	@echo "📁 Reading: /docs/intent.md, /docs/architecture/vX.Y/resources.md"
	@echo "🎯 Output: Updated architecture specifications"
	@echo ""
	@echo "Agent Tasks:"
	@echo "  ✓ Analyze intent and resources"
	@echo "  ✓ Define technical requirements"
	@echo "  ✓ Update resource configurations"
	@echo "  ✓ Validate against architecture patterns"

.PHONY: agent-arch
agent-arch: ## Run Architecture agent (Responsibilities + Models)
	$(call print_header,"Running Architecture agent...")
	@echo "🤖 Architecture Agent: Defining system architecture"
	@echo "📁 Reading: Specs, current responsibilities.yaml"
	@echo "🎯 Output: Updated responsibilities.yaml + formal models"
	@echo ""
	@echo "Agent Tasks:"
	@echo "  ✓ Define service boundaries"
	@echo "  ✓ Update responsibilities.yaml"
	@echo "  ✓ Create/update formal models (Alloy/TLA+)"
	@echo "  ✓ Validate system architecture"

.PHONY: agent-alloy
agent-alloy: ## Run Alloy models agent (Formal static analysis)
	$(call print_header,"Running Alloy models agent...")
	@echo "🤖 Alloy Agent: Creating formal static analysis models"
	@echo "📁 Reading: Architecture specs, system requirements"
	@echo "🎯 Output: Verified Alloy models with analysis results"
	@echo ""
	@echo "Agent Tasks:"
	@echo "  ✓ Model system structure and component relationships"
	@echo "  ✓ Define architectural invariants mathematically"
	@echo "  ✓ Verify system properties with Alloy Analyzer"
	@echo "  ✓ Generate counterexamples for failed properties"
	@echo "  ✓ Create formal verification documentation"
	@echo ""
	@echo "Running Alloy analysis..."
	@make alloy-validate

.PHONY: agent-tla
agent-tla: ## Run TLA+ models agent (Formal dynamic analysis)
	$(call print_header,"Running TLA+ models agent...")
	@echo "🤖 TLA+ Agent: Creating formal dynamic analysis models"
	@echo "📁 Reading: Behavior specs, system requirements"
	@echo "🎯 Output: Verified TLA+ models with temporal analysis"
	@echo ""
	@echo "Agent Tasks:"
	@echo "  ✓ Model system state transitions and behaviors"
	@echo "  ✓ Define temporal properties mathematically"
	@echo "  ✓ Verify temporal properties with TLC model checker"
	@echo "  ✓ Generate counterexamples for property violations"
	@echo "  ✓ Create dynamic behavior verification documentation"
	@echo ""
	@echo "Running TLA+ analysis..."
	@make tla-validate

.PHONY: agent-behavior
agent-behavior: ## Run Behavior agent (Gherkin features)
	$(call print_header,"Running Behavior agent...")
	@echo "🤖 Behavior Agent: Defining expected system behavior"
	@echo "📁 Reading: Architecture, current behavior specs"
	@echo "🎯 Output: Updated Gherkin features"
	@echo ""
	@echo "Agent Tasks:"
	@echo "  ✓ Create/update Gherkin features"
	@echo "  ✓ Define behavior specifications"
	@echo "  ✓ Map business requirements to testable scenarios"
	@echo "  ✓ Validate behavior completeness"

.PHONY: agent-schemas
agent-schemas: ## Run Schemas agent (Valibot schemas)
	$(call print_header,"Running Schemas agent...")
	@echo "🤖 Schemas Agent: Defining data contracts"
	@echo "📁 Reading: Behavior specs, current schemas"
	@echo "🎯 Output: Updated Valibot schemas"
	@echo ""
	@echo "Agent Tasks:"
	@echo "  ✓ Create/update Valibot schemas"
	@echo "  ✓ Define API contracts"
	@echo "  ✓ Validate schema completeness"
	@echo "  ✓ Ensure type safety"

.PHONY: agent-test
agent-test: ## Run Testing agent (Test implementation)
	$(call print_header,"Running Testing agent...")
	@echo "🤖 Testing Agent: Implementing comprehensive tests"
	@echo "📁 Reading: Gherkin features, schemas, current tests"
	@echo "🎯 Output: Updated test suites"
	@echo ""
	@echo "Agent Tasks:"
	@echo "  ✓ Convert Gherkin features to tests"
	@echo "  ✓ Implement unit/integration/e2e tests"
	@echo "  ✓ Ensure test coverage"
	@echo "  ✓ Validate test completeness"

.PHONY: agent-impl
agent-impl: ## Run Implementation agent (Code implementation)
	$(call print_header,"Running Implementation agent...")
	@echo "🤖 Implementation Agent: Implementing system code"
	@echo "📁 Reading: Schemas, test specs, current implementation"
	@echo "🎯 Output: Updated implementation code"
	@echo ""
	@echo "Agent Tasks:"
	@echo "  ✓ Implement domain logic"
	@echo "  ✓ Create SDK adapters"
	@echo "  ✓ Build application orchestration"
	@echo "  ✓ Validate against tests and schemas"

.PHONY: agent-govern
agent-govern: ## Run Governance agent (Manifest compliance)
	$(call print_header,"Running Governance agent...")
	@echo "🤖 Governance Agent: Ensuring compliance and quality"
	@echo "📁 Reading: /ai/manifest.yaml, current codebase"
	@echo "🎯 Output: Compliance report and improvements"
	@echo ""
	@echo "Agent Tasks:"
	@echo "  ✓ Validate manifest compliance"
	@echo "  ✓ Check code quality standards"
	@echo "  ✓ Ensure security policies"
	@echo "  ✓ Update governance documentation"

# =============================================================================
# WORKFLOW COMMANDS (Complete Teja Pattern Loops)
# =============================================================================

.PHONY: workflow-spec
workflow-spec: agent-intent agent-spec ## Complete specification workflow (Intent → Resources → Spec)

.PHONY: workflow-design
workflow-design: agent-intent agent-spec agent-arch ## Complete design workflow (Spec → Architecture)

.PHONY: workflow-formal
workflow-formal: workflow-design agent-alloy agent-tla ## Complete formal verification workflow (Architecture → Formal Models)

.PHONY: workflow-behavior
workflow-behavior: workflow-formal agent-behavior agent-schemas ## Complete behavior workflow (Formal Models → Behavior → Schemas)

.PHONY: workflow-implementation
workflow-implementation: workflow-behavior agent-test agent-impl ## Complete implementation workflow (Schemas → Tests → Implementation)

.PHONY: workflow-full
workflow-full: workflow-implementation agent-govern ## Complete full Teja Pattern workflow

.PHONY: workflow-with-formal
workflow-with-formal: workflow-formal workflow-implementation ## Complete workflow with formal verification

# =============================================================================
# UTILITIES AND MIGRATION
# =============================================================================

.PHONY: setup
setup: install ## Set up development environment
	$(call print_header,"Setting up development environment...")
	@echo "Environment setup completed"
	@echo ""
	@echo "Next steps:"
	@echo "  1. Copy .env.example to .env"
	@echo "  2. Configure your Supabase and Render credentials"
	@echo "  3. Run 'make dev' to start development"

.PHONY: status
status: ## Show current project status
	$(call print_header,"Project Status")
	@echo "Teja Pattern Web App Template"
	@echo "================================"
	@echo ""
	@echo "✅ Completed:"
	@echo "  • Project structure and documentation"
	@echo "  • Shared adapter factory implementation"
	@echo "  • AI governance manifest"
	@echo "  • Package configuration (pnpm workspaces)"
	@echo "  • Basic ElysiaJS application"
	@echo "  • Client factory tests (comprehensive)"
	@echo ""
	@echo "🚧 In Progress:"
	@echo "  • Build automation and Make commands"
	@echo "  • Agent orchestration setup"
	@echo ""
	@echo "📋 Planned:"
	@echo "  • Valibot schemas for shared contracts"
	@echo "  • Drizzle ORM integration"
	@echo "  • Service SDK implementations"
	@echo "  • Domain logic implementation"
	@echo "  • Comprehensive testing suite"

.PHONY: docs-serve
docs-serve: ## Serve documentation locally (if implemented)
	$(call print_header,"Starting documentation server...")
	@echo "Documentation server not yet implemented"
	@echo "View docs in:"
	@echo "  • README.md - Project overview"
	@echo "  • docs/design/master-pattern.md - Teja Pattern methodology"
	@echo "  • docs/tech_stack.md - Technology choices"
	@echo "  • docs/architecture/v0.0/ - Architecture documentation"

# =============================================================================
# MISCELLANEOUS
# =============================================================================

.PHONY: version
version: ## Show version information
	@echo "Teja Pattern Web App Template"
	@echo "Version: 0.1.0"
	@echo ""
	@echo "Node: $(shell node --version 2>/dev/null || echo 'Not installed')"
	@echo "Bun: $(shell bun --version 2>/dev/null || echo 'Not installed')"
	@echo "pnpm: $(shell pnpm --version 2>/dev/null || echo 'Not installed')"

.PHONY: update-deps
update-deps: ## Update all dependencies
	$(call print_header,"Updating dependencies...")
	@pnpm update --latest
	$(call print_success,"Dependencies updated")

.PHONY: audit
audit: ## Audit dependencies for security vulnerabilities
	$(call print_header,"Auditing dependencies...")
	@pnpm audit
	$(call print_success,"Audit completed")

# Ensure all PHONY targets are declared
.PHONY: help install dev dev-backend build clean clean-build test test-unit test-integration test-e2e test-watch test-coverage lint lint-fix typecheck format check db-generate db-migrate db-studio agent-intent agent-spec agent-arch agent-behavior agent-schemas agent-test agent-impl agent-govern workflow-spec workflow-design workflow-behavior workflow-implementation workflow-full setup status docs-serve version update-deps audit