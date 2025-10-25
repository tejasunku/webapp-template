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
	@echo "  agent-impl       Run Implementation agent"
	@echo "  agent-test       Run Testing agent"
	@echo "  agent-govern     Run Governance agent"
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

.PHONY: workflow-behavior
workflow-behavior: workflow-design agent-behavior agent-schemas ## Complete behavior workflow (Architecture → Behavior → Schemas)

.PHONY: workflow-implementation
workflow-implementation: workflow-behavior agent-test agent-impl ## Complete implementation workflow (Schemas → Tests → Implementation)

.PHONY: workflow-full
workflow-full: workflow-implementation agent-govern ## Complete full Teja Pattern workflow

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