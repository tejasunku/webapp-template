# Architecture Documentation

This directory contains architectural specifications and design artifacts for the web application template.

## Structure

- `v0.0/` - Architecture artifacts for the current version
  - `resources.md` - External services and platform configurations
  - `responsibilities.yaml` - Service boundaries and responsibilities
  - `alloy/` - Formal Alloy models for static analysis
  - `tla/` - Formal TLA+ models for temporal behavior analysis
  - `*.feature` - Gherkin behavior specifications

## Purpose

These artifacts serve as the "source of truth" for system architecture and are used by:

1. **AI Agents** - As input for generating code, tests, and schemas
2. **Development** - As reference for implementation decisions
3. **Validation** - To ensure compliance with architectural constraints
4. **Documentation** - To communicate system design and constraints

## Usage

Architecture artifacts are consumed by the AI agent toolchain:

```bash
# Generate behavior from formal models
make agent-behavior

# Generate schemas from behavior
make agent-schemas

# Generate tests from behavior and schemas
make agent-test
```

## Versioning

Architecture artifacts are versioned alongside the software implementation. Each version (`vX.Y`) represents a stable architectural state that can be built upon.