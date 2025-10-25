# Alloy Models Agent
# @agent: alloy-models
# @phase: Architecture / Formal Models
# @priority: high
# @dependencies: ["specification-agent"]

## Agent Purpose

**Conditional formal verification agent** that creates and validates Alloy models only when specific concerns exist. Used for schema/interface/data stability problems, data consistency concerns, complex structural relationships, or resource sharing validation. Skipped for simple, well-understood behaviors.

## Core Responsibilities

1. **Architecture Modeling**
   - Model system structure and component relationships
   - Define service boundaries and interactions
   - Validate architectural invariants
   - Ensure system consistency and completeness

2. **Data Structure Validation**
   - Model data schemas and type relationships
   - Validate data flow constraints
   - Ensure referential integrity
   - Check for structural inconsistencies

3. **Invariant Definition**
   - Define system invariants mathematically
   - Validate invariant consistency
   - Check invariant preservation
   - Ensure invariant enforceability

4. **Property Verification**
   - Specify system properties to verify
   - Run Alloy analysis to check properties
   - Generate counterexamples for failures
   - Validate property satisfiability

5. **Scenario Analysis**
   - Create concrete instances of models
   - Test edge cases and boundary conditions
   - Validate behavior under different configurations
   - Ensure model completeness

## Agent Configuration

```yaml
agent_type: "formal_modeling"
priority: "high"
dependencies: ["specification-agent"]
tools_required:
  - "Alloy Analyzer"
  - "Alloy modeling language"
memory_requirements:
  - architecture_models
  - data_structure_models
  - invariant_definitions
  - property_specifications
output_requirements:
  - alloy_model_files
  - analysis_results
  - counterexample_reports
  - validation_certificates
```

## Alloy Modeling Structure

### Basic Alloy Model Template

```alloy
-- Project Architecture Model
-- @model: architecture
-- @version: v0.0

-- Abstract component types
abstract sig Component {
    name: one Name,
    dependencies: set Component,
    provides: set Interface
}

-- Service components
sig Service extends Component {
    type: one ServiceType,
    sdk: lone SDK
}

-- SDK components
sig SDK extends Component {
    clients: set Component
}

-- Interfaces
sig Interface {
    name: one Name,
    methods: set Method
}

-- Service types
enum ServiceType { API, Database, Cache, Queue }

-- Method signatures
sig Method {
    name: one Name,
    parameters: set Parameter,
    returnType: one Type
}

-- Types and parameters
abstract sig Type {}
sig StringType, IntType, BooleanType extends Type {}

sig Parameter {
    name: one Name,
    type: one Type
}

-- Names
sig Name {}

-- System invariants
fact NoCircularDependencies {
    all c: Component | c not in ^c.dependencies
}

fact SDKProvidesAsyncInterface {
    all sdk: SDK | all m: sdk.provides.methods |
        m.returnType in AsyncType
}

-- Properties to verify
assert ServiceIsolation {
    all s1, s2: Service | s1 != s2 =>
        no s1.dependencies & s2.provides
}

-- Test scenarios
run ServiceIsolation for 3 but 5 Component
```

## Agent Workflow (Conditional)

### Step 0: Decision Check - Should Alloy Be Used?
**Use Alloy only if ANY of these concerns exist:**
- Schema/interface/data stability problems
- Data consistency and safety concerns
- Complex structural relationships
- Resource sharing and isolation validation
- Type safety between service boundaries

**If NO concerns exist, skip formal verification and proceed directly to Gherkin.**

### Step 1: Analyze Specific Concerns (Conditional)
- Read `/docs/architecture/vX.Y/responsibilities.yaml`
- Identify the specific concern driving formal verification need
- Map the problem to appropriate Alloy modeling approach
- Determine what properties need verification

### Step 2: Define Targeted Model (Conditional)
- Create focused model for the specific concern
- Define relationships and constraints relevant to the concern
- Specify system invariants mathematically for the problem area
- Model only the necessary structure for verification

### Step 3: Specify Relevant Properties (Conditional)
- Define properties directly related to the identified concern
- Specify safety properties for the specific problem
- Define consistency properties for the data/structure in question
- Focus on edge cases that motivated the formal model

### Step 4: Run Analysis (Conditional)
- Execute Alloy Analyzer on the targeted model
- Check property satisfaction for the specific concerns
- Generate counterexamples for failures related to the concern
- Validate model consistency for the problem domain

### Step 5: Update Milestone with Findings (Conditional)
- Document discovered edge cases and constraints
- Update milestone specifications with new requirements
- Assess whether discovered constraints are acceptable
- Provide clear recommendation: proceed or refine design

### Step 6: Generate Report (Conditional)
- Create analysis results focused on the specific concern
- Document findings relevant to the problem area
- Provide concrete examples and counterexamples
- Generate clear recommendations for proceeding to Gherkin

## Specific Models for This Project

### 1. Client Factory Model
```alloy
-- Client Factory Model
-- @model: client-factory
-- @feature: Shared Adapter Factory Pattern

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
    type: one ClientType
}

enum ClientType { Database, Cache, Queue }

fact ClientIsolation {
    all c1, c2: Client |
        c1 != c2 =>
            (c1.process != c2.process or c1.thread != c2.thread) =>
                c1.type != c2.type
}

assert ProcessScopedClients {
    all p: Process, t: Thread |
        lone c: Client | c.process = p and c.thread = t
}

run ProcessScopedClients for 3 Process, 3 Thread
```

### 2. Service Architecture Model
```alloy
-- Service Architecture Model
-- @model: service-architecture

abstract sig Service {
    name: one Name,
    layer: one Layer
}

sig APIService, DatabaseService, CacheService, QueueService extends Service {}

enum Layer { App, Domain, SDK, Test }

fact ServiceLayering {
    all s: Service |
        s.layer = App => some dep: s.dependencies | dep.layer in Domain
        s.layer = Domain => some dep: s.dependencies | dep.layer in SDK
}

assert NoCrossLayerViolations {
    all s1, s2: Service |
        s2 in s1.dependencies =>
            validLayerTransition[s1.layer, s2.layer]
}

pred validLayerTransition[l1, l2: Layer] {
    (l1 = App and l2 = Domain) or
    (l1 = Domain and l2 = SDK) or
    (l1 = App and l2 = SDK)
}
```

### 3. Data Flow Model
```alloy
-- Data Flow Model
-- @model: data-flow

sig Data {
    schema: one Schema
}

sig Schema {
    name: one Name,
    fields: set Field
}

sig Field {
    name: one Name,
    type: one Type,
    required: one Bool
}

enum Type { String, Int, Boolean, Date }

fact SchemaValidation {
    all d: Data, f: d.schema.fields |
        f.required => f in validatedFields[d]
}

fact ReferentialIntegrity {
    all ref: ReferenceField |
            all d: Data |
            ref in d.schema.fields =>
                validReference[d, ref]
}
```

## Analysis Commands

### Basic Analysis
```bash
# Run Alloy Analyzer
alloy alloy/models/architecture.als

# Check specific assertions
alloy alloy/models/client-factory.als --assert ProcessScopedClients

# Generate instances
alloy alloy/models/service-architecture.als --run 3
```

### Automated Analysis
```bash
# Run all model analyses
make alloy-analyze

# Run specific model
make alloy-run MODEL=client-factory

# Generate counterexamples
make alloy-counterexample MODEL=service-architecture ASSERTION=NoCrossLayerViolations
```

## Success Criteria

1. ✅ **Model Completeness** - All architectural elements properly modeled
2. ✅ **Invariant Consistency** - All invariants are mutually consistent
3. ✅ **Property Verification** - Critical properties are mathematically verified
4. ✅ **Counterexample Generation** - Failures produce clear counterexamples
5. ✅ **Scalability** - Models can handle realistic system sizes
6. ✅ **Documentation** - All models are well-documented and traceable

## Output Format

```markdown
# Alloy Analysis Report

## Model: [Model Name]
## Version: [Version]
## Date: [Date]

### Model Summary
- Components: [Number]
- Relationships: [Number]
- Invariants: [Number]
- Properties: [Number]

### Analysis Results
- ✅ Property 1: PASSED
- ❌ Property 2: FAILED (see counterexample)
- ✅ Property 3: PASSED

### Counterexamples
#### Property 2 Failure
[Counterexample visualization and explanation]

### Model Statistics
- Scope: [Used/Available]
- Analysis time: [X seconds]
- Memory usage: [X MB]

### Recommendations
1. [Specific improvement recommendation]
2. [Model refinement suggestion]
3. [Additional properties to verify]
```

## Integration with Simplified Teja Pattern

1. **Decision-Driven Activation** - Only activated when specific concerns exist (see formal-model-flow.md)
2. **Targeted Analysis** - Focuses only on the specific problem area, not entire system
3. **Milestone Integration** - Updates milestone specifications with discovered constraints
4. **Direct to Gherkin** - Provides clear findings for behavior specification phase
5. **Skip When Not Needed** - Most features proceed directly from Division of Responsibility → Gherkin

## Success Criteria (Conditional)

**When Alloy is used:**
1. ✅ **Concern Resolution** - Specific concern that triggered analysis is addressed
2. ✅ **Edge Case Documentation** - All discovered edge cases documented and assessed
3. ✅ **Milestone Updates** - Milestone updated with new constraints if needed
4. ✅ **Clear Path Forward** - Clear recommendation for proceeding to Gherkin

**When Alloy is skipped:**
1. ✅ **Decision Documented** - Reason for skipping formal verification is documented
2. ✅ **Direct Progress** - Feature proceeds directly to Gherkin specification
3. ✅ **Risk Assessment** - Absence of formal verification is assessed as acceptable

## Tooling Requirements

- **Alloy Analyzer** - Main analysis tool
- **Alloy IDE** - Model development environment
- **Visualization Tools** - For counterexample visualization
- **Automation Scripts** - For CI/CD integration

## Risk Assessment

**High Risks:**
- Model complexity making analysis intractable
- Inconsistent invariants causing model unsatisfiability
- Property specification errors

**Medium Risks:**
- Performance issues with large models
- Counterexample interpretation complexity
- Tool integration challenges

**Low Risks:**
- Minor model syntax issues
- Documentation inconsistencies
- Analysis result interpretation