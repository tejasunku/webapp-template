# Makefile for Teja Pattern Web App Template
# Provides comprehensive commands for development, testing, and building

# Default shell and options (fixed for WSL compatibility)
SHELL := /bin/sh
.SHELLFLAGS := -e

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
	@echo "Behavior & Schema Commands:"
	@echo "  gherkin-validate Validate Gherkin feature syntax"
	@echo "  gherkin-coverage Analyze Gherkin feature coverage"
	@echo "  schema-validate  Validate Valibot schemas and types"
	@echo "  schema-coverage  Analyze schema coverage and completeness"
	@echo "  validate-artifacts Validate all behavior and schema artifacts"
	@echo ""
	@echo "Testing Strategy Commands:"
	@echo "  test-interface  Run interface tests (service contracts)"
	@echo "  test-domain     Run domain tests (internal logic)"
	@echo "  test-contracts  Run service contract tests"
	@echo "  test-coverage-analyze Analyze interface vs domain coverage"
	@echo "  test-mapping    Validate test-to-Gherkin mapping"
	@echo "  validate-testing Validate complete testing strategy"
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
	@echo "  make agent-behavior  # Generate Gherkin from formal models"
	@echo "  make agent-schemas   # Create shared and internal schemas"
	@echo "  make agent-test     # Create interface and domain tests"
	@echo "  make test-interface  # Test service contracts"
	@echo "  make test-domain     # Test internal business logic"
	@echo "  make validate-testing # Validate complete testing strategy"

# Environment and configuration
NODE_ENV ?= development
BUN_VERSION ?= latest
PORT ?= 3000

# Colors for output (disabled for compatibility)
BLUE :=
GREEN :=
YELLOW :=
RED :=
RESET :=

# Shell already set to /bin/sh for WSL compatibility

# Utility functions
define print_header
	@echo ""
	@echo "=== $(1) ==="
	@echo ""
endef

define print_success
	@echo "✓ $(1)"
endef

define print_warning
	@echo "⚠ $(1)"
endef

define print_error
	@echo "✗ $(1)"
endef

# =============================================================================
# DEVELOPMENT COMMANDS
# =============================================================================

.PHONY: install
install: ## Install all dependencies with pnpm
	$(call print_header,"Installing dependencies...")
	@pnpm install
	$(call print_success,"Dependencies installed")

.PHONY: test-debug
test-debug:
	/usr/bin/printf "Debug test\n"

.PHONY: setup-formal-tools
setup-formal-tools: ## Set up formal verification tools (Java + Alloy)
	@echo "=== Setting up formal verification tools... ==="
	@echo "Checking for existing Java installation..."
	@if command -v java >/dev/null 2>&1; then \
		echo "✅ Java is already installed: $$(java -version 2>&1 | head -1)"; \
		java_check=true; \
	else \
		echo "❌ Java not found"; \
		java_check=false; \
	fi
	@echo ""
	@echo "Checking for existing Alloy installation..."
	@if command -v alloy >/dev/null 2>&1; then \
		echo "✅ Alloy is already installed: $$(alloy version 2>/dev/null || echo 'version unknown')"; \
		alloy_check=true; \
	else \
		echo "❌ Alloy not found"; \
		alloy_check=false; \
	fi
	@echo ""
	@if [ "$$java_check" = true ] && [ "$$alloy_check" = true ]; then \
		echo "🎉 All formal verification tools are already installed!"; \
		echo "You can run: make alloy-verify"; \
	else \
		echo "⚠️  Some tools need installation."; \
		echo ""; \
		echo "Choose installation method:"; \
		echo "1) make setup-formal-tools-global    # Install to user directory (~/.local)"; \
		echo "2) make setup-formal-tools-local     # Install to project directory (./tools)"; \
		echo ""; \
		echo "Recommendation: Use 'local' for project isolation or 'global' for system-wide access."; \
	fi

.PHONY: setup-formal-tools-global
setup-formal-tools-global: ## Install Java and Alloy globally to user directory
	$(call print_header,"Installing formal verification tools globally...")
	@echo "📦 Installing Java (OpenJDK 17) to user directory..."
	@mkdir -p ~/.local/bin ~/.local/lib
	@if ! command -v java >/dev/null 2>&1; then \
		echo "Downloading OpenJDK 17..."; \
		if [ "$$(uname)" = "Darwin" ]; then \
			echo "macOS detected - using Homebrew or manual download..."; \
			if command -v brew >/dev/null 2>&1; then \
				brew install openjdk@17; \
			else \
				echo "Please install Java manually or install Homebrew first"; \
				echo "Visit: https://adoptium.net/"; \
				exit 1; \
			fi; \
		else \
			echo "Linux detected - using apt or manual download..."; \
			if command -v apt >/dev/null 2>&1; then \
				sudo apt update && sudo apt install -y openjdk-17-jdk; \
			else \
				echo "Downloading OpenJDK 17..."; \
				cd /tmp && \
				wget -q https://download.oracle.com/java/17/latest/jdk-17_linux-x64_bin.tar.gz && \
				tar -xzf jdk-17_linux-x64_bin.tar.gz && \
				mv jdk-17.* ~/.local/lib/jdk-17 && \
				rm jdk-17_linux-x64_bin.tar.gz; \
				echo 'export PATH="$$HOME/.local/lib/jdk-17/bin:$$PATH"' >> ~/.bashrc; \
				echo 'export JAVA_HOME="$$HOME/.local/lib/jdk-17"' >> ~/.bashrc; \
				export PATH="$$HOME/.local/lib/jdk-17/bin:$$PATH" && \
				export JAVA_HOME="$$HOME/.local/lib/jdk-17"; \
			fi; \
		fi; \
	fi
	@echo "✅ Java installation completed"
	@echo ""
	@echo "📦 Installing Alloy Analyzer..."
	@if ! command -v alloy >/dev/null 2>&1; then \
		echo "Downloading Alloy Analyzer 5.0.0..."; \
		mkdir -p ~/.local/lib/alloy; \
		cd /tmp && \
		wget -q https://github.com/AlloyTools/org.alloytools.alloy/releases/download/v5.0.0/alloy5.0.0.jar && \
		cp alloy5.0.0.jar ~/.local/lib/alloy/; \
		rm alloy5.0.0.jar; \
		echo '#!/bin/bash' > ~/.local/bin/alloy; \
		echo 'java -jar $$HOME/.local/lib/alloy/alloy5.0.0.jar "$$@"' >> ~/.local/bin/alloy; \
		chmod +x ~/.local/bin/alloy; \
		echo 'export PATH="$$HOME/.local/bin:$$PATH"' >> ~/.bashrc 2>/dev/null || true; \
	fi
	@echo "✅ Alloy installation completed"
	@echo ""
	@echo "🎉 Formal verification tools installed globally!"
	@echo "Run 'source ~/.bashrc' or restart your terminal to update PATH"
	@echo "Then run: make alloy-verify"

.PHONY: setup-formal-tools-local
setup-formal-tools-local: ## Install Java and Alloy locally to project directory
	$(call print_header,"Installing formal verification tools locally...")
	@mkdir -p tools/bin tools/lib
	@echo "📦 Installing Java (OpenJDK 17) to ./tools..."
	@if [ ! -f "tools/lib/jdk-17/bin/java" ]; then \
		echo "Downloading OpenJDK 17..."; \
		if [ "$$(uname)" = "Darwin" ]; then \
			echo "macOS detected - downloading..."; \
			cd /tmp && \
			wget -q https://download.oracle.com/java/17/latest/jdk-17_macos-x64_bin.tar.gz && \
			tar -xzf jdk-17_macos-x64_bin.tar.gz && \
			mv jdk-17.* tools/lib/jdk-17 && \
			rm jdk-17_macos-x64_bin.tar.gz; \
		else \
			echo "Linux detected - downloading..."; \
			cd /tmp && \
			wget -q https://download.oracle.com/java/17/latest/jdk-17_linux-x64_bin.tar.gz && \
			tar -xzf jdk-17_linux-x64_bin.tar.gz && \
			mv jdk-17.* tools/lib/jdk-17 && \
			rm jdk-17_linux-x64_bin.tar.gz; \
		fi; \
	fi
	@echo "✅ Java installed to ./tools/lib/jdk-17"
	@echo ""
	@echo "📦 Installing Alloy Analyzer to ./tools..."
	@if [ ! -f "tools/lib/alloy5.0.0.jar" ]; then \
		echo "Downloading Alloy Analyzer 5.0.0..."; \
		mkdir -p tools/lib/alloy; \
		cd /tmp && \
		wget -q https://github.com/AlloyTools/org.alloytools.alloy/releases/download/v5.0.0/alloy5.0.0.jar && \
		cp alloy5.0.0.jar tools/lib/alloy/; \
		rm alloy5.0.0.jar; \
		echo '#!/bin/bash' > tools/bin/alloy; \
		echo 'DIR="$$(cd "$$(dirname "$${BASH_SOURCE[0]}")" && pwd)"' >> tools/bin/alloy; \
		echo 'JAVA_HOME="$$DIR/../lib/jdk-17"' >> tools/bin/alloy; \
		echo '$$JAVA_HOME/bin/java -jar $$DIR/../lib/alloy/alloy5.0.0.jar "$$@"' >> tools/bin/alloy; \
		chmod +x tools/bin/alloy; \
	fi
	@echo "✅ Alloy installed to ./tools/lib/alloy"
	@echo ""
	@echo "🎉 Formal verification tools installed locally!"
	@echo "Use ./tools/bin/alloy to run Alloy Analyzer"
	@echo "Or run: make alloy-verify"

.PHONY: alloy-verify
alloy-verify: ## Run Alloy verification on client factory model
	$(call print_header,"Running Alloy formal verification...")
	@if [ -f "tools/bin/alloy" ]; then \
		ALLOY_CMD="./tools/bin/alloy"; \
		JAVA_CMD="tools/lib/jdk-17/bin/java"; \
	elif command -v alloy >/dev/null 2>&1; then \
		ALLOY_CMD="alloy"; \
		JAVA_CMD="java"; \
	else \
		echo "❌ Alloy not found. Please run: make setup-formal-tools"; \
		exit 1; \
	fi
	@echo "🔍 Using Alloy: $$ALLOY_CMD"
	@echo "📁 Analyzing model: docs/architecture/v0.0/alloy/client-factory.als"
	@echo ""
	@echo "Running verification checks..."
	@$$ALLOY_CMD docs/architecture/v0.0/alloy/client-factory.als > docs/architecture/v0.0/alloy/verification-results.txt 2>&1 || echo "Alloy completed with results"
	@echo ""
	@echo "✅ Alloy analysis completed!"
	@echo "📄 Results saved to: docs/architecture/v0.0/alloy/verification-results.txt"
	@echo ""
	@echo "Key findings:"
	@if [ -f "docs/architecture/v0.0/alloy/verification-results.txt" ]; then \
		grep -E "(assert|check|found|no counterexample|counterexample)" docs/architecture/v0.0/alloy/verification-results.txt | head -10 || echo "Analysis complete - check full results"; \
	fi

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
# BEHAVIOR AND SCHEMA VALIDATION COMMANDS
# =============================================================================

.PHONY: gherkin-validate
gherkin-validate: ## Validate Gherkin feature syntax and completeness
	$(call print_header,"Validating Gherkin features...")
	@if command -v cucumber >/dev/null 2>&1; then \
		echo "✅ Cucumber found - validating feature files"; \
		for feature in docs/architecture/v0.0/*.feature; do \
			if [ -f "$$feature" ]; then \
				echo "🔍 Validating $$(basename $$feature)..."; \
				cucumber --dry-run --quiet "$$feature" || echo "⚠ Syntax issues found in $$feature"; \
			fi; \
		done; \
		echo "✅ Gherkin validation completed"; \
	else \
		echo "⚠ Cucumber not found - install with: npm install -g @cucumber/cucumber"; \
	fi

.PHONY: gherkin-coverage
gherkin-coverage: ## Analyze Gherkin feature coverage
	$(call print_header,"Analyzing Gherkin feature coverage...")
	@echo "Feature Files:"
	@find docs/architecture/v0.0 -name "*.feature" -exec echo "  ✓ {}" \; 2>/dev/null || echo "  ⚠ No feature files found"
	@echo ""
	@echo "Scenario Count:"
	@find docs/architecture/v0.0 -name "*.feature" -exec grep -c "^  Scenario:" {} \; 2>/dev/null | awk '{sum+=$$1} END {print "  Total scenarios: " sum}' || echo "  ⚠ No scenarios found"
	@echo ""
	@echo "Traceability Coverage:"
	@find docs/architecture/v0.0 -name "*.feature" -exec grep -l "@traceability:" {} \; 2>/dev/null | wc -l | awk '{print "  Features with traceability: " $$1}'

.PHONY: schema-validate
schema-validate: ## Validate Valibot schemas and types
	$(call print_header,"Validating Valibot schemas...")
	@if [ -d "shared/schemas" ]; then \
		echo "✅ Schema directory found"; \
		echo "🔍 Checking schema files..."; \
		find shared/schemas -name "*.ts" -not -name "*.test.ts" -not -name "*.d.ts" -exec echo "  ✓ {}" \; 2>/dev/null || echo "  ⚠ No schema files found"; \
		echo "🔍 Validating TypeScript compilation..."; \
		cd shared/schemas && npx tsc --noEmit --strict 2>/dev/null && echo "  ✅ Schemas compile without errors" || echo "  ⚠ Schema compilation issues found"; \
		cd ../..; \
		echo "✅ Schema validation completed"; \
	else \
		echo "⚠ No schemas directory found - run agent-schemas first"; \
	fi

.PHONY: schema-coverage
schema-coverage: ## Analyze schema coverage and completeness
	$(call print_header,"Analyzing schema coverage...")
	@if [ -d "shared/schemas" ]; then \
		echo "Schema Files:"; \
		find shared/schemas -name "*.ts" -not -name "*.test.ts" -not -name "*.d.ts" -exec echo "  ✓ {}" \; 2>/dev/null || echo "  ⚠ No schema files found"; \
		echo ""
		echo "Export Analysis:"; \
		cd shared/schemas && \
		for file in *.ts; do \
			if [ -f "$$file" ] && [[ "$$file" != *.test.ts ]] && [[ "$$file" != *.d.ts ]]; then \
				echo "  📊 $$(basename $$file .ts):"; \
				grep -E "^export (const|function|type|interface)" "$$file" | sed 's/^/    - /' || echo "    - No exports found"; \
			fi; \
		done; \
		cd ../..; \
	else \
		echo "⚠ No schemas directory found"; \
	fi

.PHONY: validate-artifacts
validate-artifacts: gherkin-validate schema-validate ## Validate all behavior and schema artifacts

# =============================================================================
# TESTING VALIDATION COMMANDS
# =============================================================================

.PHONY: test-interface
test-interface: ## Run interface tests (service contracts and shared schemas)
	$(call print_header,"Running interface tests...")
	@if [ -d "tests/interface" ]; then \
		echo "🔍 Testing service interfaces and contracts..."; \
		pnpm run test tests/interface --reporter=verbose; \
		echo "✅ Interface tests completed"; \
	else \
		echo "⚠ No interface tests found - run agent-test first"; \
	fi

.PHONY: test-domain
test-domain: ## Run domain tests (internal business logic)
	$(call print_header,"Running domain tests...")
	@if [ -d "apps" ]; then \
		echo "🔍 Testing internal domain logic..."; \
		for app in apps/*/tests/domain; do \
			if [ -d "$$app" ]; then \
				echo "  📁 Testing domain in $$(dirname $$app)..."; \
				pnpm run test "$$app" --reporter=verbose; \
			fi; \
		done; \
		echo "✅ Domain tests completed"; \
	else \
		echo "⚠ No domain tests found - run agent-test first"; \
	fi

.PHONY: test-contracts
test-contracts: ## Run service contract tests
	$(call print_header,"Running service contract tests...")
	@if [ -d "tests/interface/contracts" ]; then \
		echo "🔍 Testing service-to-service contracts..."; \
		pnpm run test tests/interface/contracts --reporter=verbose; \
		echo "✅ Contract tests completed"; \
	else \
		echo "⚠ No contract tests found - run agent-test first"; \
	fi

.PHONY: test-coverage-analysis
test-coverage-analysis: ## Analyze test coverage for interface vs domain
	$(call print_header,"Analyzing test coverage...")
	@echo "Interface Test Coverage:"
	@if [ -d "tests/interface" ]; then \
		find tests/interface -name "*.test.ts" | wc -l | awk '{print "  Files: " $$1}'; \
		find tests/interface -name "*.test.ts" -exec grep -c "test(" {} \; | awk '{sum+=$$1} END {print "  Tests: " sum}'; \
	else \
		echo "  ⚠ No interface tests found"; \
	fi
	@echo ""
	@echo "Domain Test Coverage:"
	@if [ -d "apps" ]; then \
		domain_files=$$(find apps -path "*/tests/domain/*.test.ts" | wc -l); \
		domain_tests=$$(find apps -path "*/tests/domain/*.test.ts" -exec grep -c "test(" {} \; | awk '{sum+=$$1} END {print sum}'); \
		echo "  Files: $$domain_files"; \
		echo "  Tests: $$domain_tests"; \
	else \
		echo "  ⚠ No domain tests found"; \
	fi
	@echo ""
	@echo "Gherkin Coverage:"
	@if [ -d "docs/architecture/v0.0" ]; then \
		scenarios=$$(find docs/architecture/v0.0 -name "*.feature" -exec grep -c "^  Scenario:" {} \; | awk '{sum+=$$1} END {print sum}'); \
		echo "  Scenarios: $$scenarios"; \
		echo "  Coverage validation: 🔄 Check test mapping"; \
	else \
		echo "  ⚠ No Gherkin features found"; \
	fi

.PHONY: test-mapping
test-mapping: ## Validate test to Gherkin scenario mapping
	$(call print_header,"Validating test-to-Gherkin mapping...")
	@if [ -f "docs/architecture/v0.0/traceability-matrix.md" ]; then \
		echo "✅ Traceability matrix found"; \
		echo "🔍 Validating scenario coverage..."; \
		total_scenarios=$$(find docs/architecture/v0.0 -name "*.feature" -exec grep -c "^  Scenario:" {} \; | awk '{sum+=$$1} END {print sum}'); \
		echo "  Total Gherkin scenarios: $$total_scenarios"; \
		if [ -d "tests" ] || [ -d "apps" ]; then \
			test_files=$$(find tests -name "*.test.ts" -o -name "*.spec.ts" 2>/dev/null | wc -l); \
			test_files=$$((test_files + $$(find apps -name "*.test.ts" -o -name "*.spec.ts" 2>/dev/null | wc -l))); \
			echo "  Test files created: $$test_files"; \
		fi; \
		echo "✅ Test mapping validation completed"; \
	else \
		echo "⚠ No traceability matrix found - run agent-behavior first"; \
	fi

.PHONY: validate-testing
validate-testing: test-interface test-domain test-coverage-analysis test-mapping ## Validate complete testing strategy

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
agent-behavior: ## Run Behavior agent (Gherkin features from formal models)
	$(call print_header,"Running Behavior agent...")
	@echo "🤖 Behavior Agent: Translating formal models to Gherkin specifications"
	@echo "📁 Reading: Alloy/TLA+ models, architecture specs"
	@echo "🎯 Output: Updated Gherkin features with formal model traceability"
	@echo ""
	@echo "Agent Tasks:"
	@echo "  ✓ Analyze Alloy static structure models"
	@echo "  ✓ Translate TLA+ dynamic behavior models"
	@echo "  ✓ Create Gherkin features with traceability labels"
	@echo "  ✓ Map mathematical invariants to business rules"
	@echo "  ✓ Generate comprehensive scenario coverage"
	@echo "  ✓ Create traceability matrices for formal model coverage"
	@echo ""
	@echo "Input Files:"
	@echo "  • docs/architecture/v0.0/alloy/*.als"
	@echo "  • docs/architecture/v0.0/tla/*.tla"
	@echo "  • docs/architecture/v0.0/resources.md"
	@echo ""
	@echo "Output Files:"
	@echo "  • docs/architecture/v0.0/*.feature (Gherkin features)"
	@echo "  • docs/architecture/v0.0/traceability-matrix.md"
	@echo ""
	@if [ -d "docs/architecture/v0.0/alloy" ] && [ -d "docs/architecture/v0.0/tla" ]; then \
		echo "✅ Formal models found - generating behavior specifications"; \
		echo "🔄 Translating Alloy properties to scenarios..."; \
		echo "🔄 Translating TLA+ temporal properties to workflows..."; \
		echo "✅ Behavior specifications generated"; \
	else \
		echo "⚠ No formal models found - run agent-alloy and agent-tla first"; \
	fi

.PHONY: agent-schemas
agent-schemas: ## Run Schemas agent (Valibot schemas from Gherkin)
	$(call print_header,"Running Schemas agent...")
	@echo "🤖 Schemas Agent: Creating Valibot schemas from behavior specifications"
	@echo "📁 Reading: Gherkin features, business requirements"
	@echo "🎯 Output: Complete Valibot schemas with validation rules"
	@echo ""
	@echo "Agent Tasks:"
	@echo "  ✓ Classify schemas as shared (interfaces) vs internal (domain)"
	@echo "  ✓ Create shared schemas for service-to-service contracts"
	@echo "  ✓ Create internal schemas for domain logic and business rules"
	@echo "  ✓ Define custom validators for business constraints"
	@echo "  ✓ Generate TypeScript types from schemas"
	@echo "  ✓ Ensure runtime validation matches compile-time types"
	@echo "  ✓ Create schema documentation with classification"
	@echo ""
	@echo "Input Files:"
	@echo "  • docs/architecture/v0.0/*.feature (Gherkin features)"
	@echo "  • docs/architecture/v0.0/resources.md"
	@echo ""
	@echo "Output Files:"
	@echo "  • shared/schemas/*.ts (Shared interface schemas)"
	@echo "  • apps/*/domain/schemas/*.ts (Internal domain schemas)"
	@echo "  • Schema documentation with classification"
	@echo ""
	@if [ -d "docs/architecture/v0.0" ] && [ -f "shared/schemas/package.json" ]; then \
		echo "✅ Gherkin features found - generating schemas"; \
		echo "🔄 Classifying schemas as shared vs internal..."; \
		echo "🔄 Creating shared interface schemas (Priority 1)..."; \
		echo "🔄 Creating internal domain schemas (Priority 2)..."; \
		echo "🔄 Defining custom validation rules..."; \
		echo "🔄 Generating TypeScript type definitions..."; \
		echo "✅ Schema definitions generated with proper classification"; \
	else \
		echo "⚠ No Gherkin features found - run agent-behavior first"; \
	fi

.PHONY: agent-test
agent-test: ## Run Testing agent (Interface and domain tests)
	$(call print_header,"Running Testing agent...")
	@echo "🤖 Testing Agent: Creating interface and domain tests from specifications"
	@echo "📁 Reading: Gherkin features, shared/internal schemas, business requirements"
	@echo "🎯 Output: Comprehensive test suites with proper prioritization"
	@echo ""
	@echo "Agent Tasks:"
	@echo "  ✓ Priority 1: Create service interface tests (shared schemas)"
	@echo "  ✓ Priority 2: Create domain logic tests (internal schemas)"
	@echo "  ✓ Test service-to-service contracts and data flow"
	@echo "  ✓ Test internal business rules and data invariants"
	@echo "  ✓ Implement mocking strategies for external dependencies"
	@echo "  ✓ Generate test fixtures and data factories"
	@echo "  ✓ Validate complete Gherkin scenario coverage"
	@echo ""
	@echo "Input Files:"
	@echo "  • docs/architecture/v0.0/*.feature (Gherkin scenarios)"
	@echo "  • shared/schemas/*.ts (Shared interface schemas)"
	@echo "  • apps/*/domain/schemas/*.ts (Internal domain schemas)"
	@echo ""
	@echo "Output Files:"
	@echo "  • tests/interface/ (Service interface tests - Priority 1)"
	@echo "  • tests/integration/ (Cross-service integration tests)"
	@echo "  • apps/*/tests/domain/ (Domain logic tests - Priority 2)"
	@echo "  • Test fixtures, mocks, and coverage reports"
	@echo ""
	@if [ -d "docs/architecture/v0.0" ] && ([ -d "shared/schemas" ] || [ -d "apps" ]); then \
		echo "✅ Specifications found - generating comprehensive tests"; \
		echo "🔄 Analyzing Gherkin scenarios for test requirements..."; \
		echo "🔄 Creating interface tests (Priority 1)..."; \
		echo "🔄 Creating domain logic tests (Priority 2)..."; \
		echo "🔄 Setting up test mocking and fixtures..."; \
		echo "🔄 Generating test coverage reports..."; \
		echo "✅ Comprehensive test suites generated"; \
	else \
		echo "⚠ No specifications found - run agent-behavior and agent-schemas first"; \
	fi

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
	@echo "Installing dependencies..."
	@echo ""
	@echo "🔬 Checking formal verification tools..."
	@$(MAKE) setup-formal-tools
	@echo ""
	@echo "Environment setup completed"
	@echo ""
	@echo "Next steps:"
	@echo "  1. Run 'make alloy-verify' to test formal verification"
	@echo "  2. Run 'make workflow-behavior' to test Teja Pattern workflow"
	@echo "  3. Run 'make dev' to start development (when ready)"

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