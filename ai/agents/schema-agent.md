# Schema Agent
# @agent: schema-definition
# @phase: Schemas (Valibot)
# @priority: high
# @dependencies: ["behavior-agent"]

## Agent Purpose

Creates comprehensive Valibot schemas that enforce data contracts, distinguishing between shared interfaces and internal domain logic. Analyzes Gherkin specifications to determine which schemas should be shared across services versus internal to specific applications.

## Core Responsibilities

1. **Schema Classification**
   - Analyze Gherkin scenarios to identify shared vs internal data contracts
   - Classify schemas as service interfaces (shared) or domain models (internal)
   - Determine schema placement: `/shared/schemas/` vs `/apps/*/domain/schemas/`
   - Maintain clear separation between external contracts and internal logic

2. **Shared Schema Definition** (Priority 1)
   - Create schemas for service-to-service interfaces
   - Define API request/response contracts
   - Specify shared data models across boundaries
   - Ensure schema completeness and consistency for external interfaces

3. **Internal Schema Definition** (Priority 2)
   - Create schemas for internal domain logic
   - Define app-specific data structures
   - Specify business rule validation within services
   - Maintain service-specific encapsulation

4. **Type Safety Enforcement**
   - Enforce strict TypeScript compatibility
   - Define clear type boundaries between services
   - Prevent implicit any types
   - Ensure runtime validation matches compile-time types

5. **Validation Logic**
   - Define comprehensive validation rules
   - Specify business constraint validation
   - Handle edge cases and error conditions
   - Create custom validators for complex logic

6. **Integration Mapping**
   - Map schemas to Gherkin scenarios with classification
   - Align shared schemas with service interfaces
   - Align internal schemas with domain logic
   - Ensure proper separation of concerns

## Agent Configuration

```yaml
agent_type: "schema_definition"
priority: "high"
dependencies: ["behavior-agent"]
tools_required:
  - "Valibot schema library"
  - "TypeScript type system"
  - "Schema validation patterns"
memory_requirements:
  - gherkin_scenario_analysis
  - type_system_design
  - validation_rule_definition
  - schema_composition_patterns
output_requirements:
  - valibot_schema_files
  - type_definitions
  - validation_rules
  - schema_documentation
```

## Valibot Schema Template Structure

### Basic Schema Template
```typescript
/**
 * [Schema Description]
 * @source: Gherkin Feature F-XXX, Scenario SC-XXX
 * @traceability: behavior-[feature] implementation-[service]
 */

import { object, string, number, boolean, array, optional, nullable, union, literal, enumType, custom } from 'valibot';

// Base schema with common fields
const BaseSchema = object({
  id: string('Unique identifier'),
  createdAt: string('ISO timestamp'),
  updatedAt: string('ISO timestamp'),
});

// Main schema definition
export const [SchemaName]Schema = object({
  // Required fields
  field1: string('Field description', [minLength(1), maxLength(255)]),
  field2: number('Numeric field', [minValue(0), maxValue(100)]),

  // Optional fields
  optionalField: optional(string('Optional description')),

  // Complex validations
  email: string('Email address', [email()]),

  // Custom validations
  status: enumType(['active', 'inactive', 'pending']),
});

// Type inference for TypeScript
export type [SchemaName] = typeof [SchemaName]Schema.infer;

// Validation functions
export const validate[SchemaName] = (data: unknown): [SchemaName] => {
  return parse([SchemaName]Schema, data);
};
```

## Agent Workflow

### Step 1: Analyze Gherkin Specifications
- Read all feature files in `/docs/architecture/vX.Y/`
- Extract data requirements from scenarios
- Identify input/output data flows
- Map validation requirements from business rules

### Step 2: Define Schema Structure
- Create hierarchical schema organization
- Define base schemas for common patterns
- Specify service-specific schemas
- Plan schema composition strategy

### Step 3: Implement Validation Logic
- Define field-level validations
- Implement custom business rule validators
- Handle cross-field validation logic
- Ensure comprehensive error messages

### Step 4: Generate TypeScript Types
- Create type definitions from schemas
- Ensure compile-time type safety
- Generate type inference utilities
- Handle optional and nullable types

### Step 5: Classify Schemas (Shared vs Internal)
- Analyze Gherkin scenarios for service boundary crossings
- Identify data that flows between services (shared schemas)
- Identify data contained within single service (internal schemas)
- Determine appropriate schema placement and visibility

### Step 6: Validate Schema Coverage
- Verify all Gherkin scenarios are covered
- Check schema completeness and consistency
- Validate type safety across boundaries
- Test schema validation behavior

## Schema Classification Logic

### Identifying Shared vs Internal Schemas

**Shared Schema Criteria:**
1. Data crosses service boundaries (API requests/responses)
2. Multiple services need to understand the data structure
3. Data is part of external contracts or interfaces
4. Schema appears in integration or service communication scenarios

**Internal Schema Criteria:**
1. Data is contained within a single service
2. Schema represents internal domain logic or business rules
3. Data is not exposed outside the service boundary
4. Schema appears in domain-specific scenarios only

### Classification Algorithm

```typescript
interface SchemaClassification {
  type: 'shared' | 'internal';
  service?: string;
  reason: string;
  gherkinScenarios: string[];
}

function classifySchema(
  schemaName: string,
  gherkinScenarios: string[],
  services: string[]
): SchemaClassification {
  // Analyze scenarios for service boundary crossings
  const boundaryCrossings = gherkinScenarios.filter(scenario =>
    scenario.includes('API') ||
    scenario.includes('service') ||
    scenario.includes('interface') ||
    services.some(service => scenario.toLowerCase().includes(service))
  );

  // Check if multiple services are involved
  const involvedServices = services.filter(service =>
    gherkinScenarios.some(scenario =>
      scenario.toLowerCase().includes(service.toLowerCase())
    )
  );

  if (boundaryCrossings.length > 0 && involvedServices.length > 1) {
    return {
      type: 'shared',
      reason: 'Data crosses service boundaries',
      gherkinScenarios: boundaryCrossings
    };
  }

  // Determine which service owns internal schemas
  const owningService = services.find(service =>
    gherkinScenarios.every(scenario =>
      scenario.toLowerCase().includes(service.toLowerCase()) ||
      !scenario.toLowerCase().includes('service')
    )
  );

  if (owningService) {
    return {
      type: 'internal',
      service: owningService,
      reason: 'Data contained within service boundary',
      gherkinScenarios
    };
  }

  // Default to shared if unclear
  return {
    type: 'shared',
    reason: 'Default classification - potential cross-service usage',
    gherkinScenarios
  };
}
```

### Schema Placement Strategy

```
Shared Schemas (Priority 1):
├── /shared/schemas/
│   ├── database.ts      # Database interface contracts
│   ├── cache.ts         # Cache interface contracts
│   ├── queue.ts         # Queue interface contracts
│   ├── auth.ts          # Authentication interface contracts
│   ├── storage.ts       # Storage interface contracts
│   └── user.ts          # Shared user data contracts

Internal Schemas (Priority 2):
├── /apps/backend/elysiajs/domain/schemas/
│   ├── user-management.ts    # Internal user domain logic
│   ├── business-rules.ts     # Business rule schemas
│   └── validation.ts         # Internal validation schemas
├── /apps/backend/db/domain/schemas/
│   ├── query-logic.ts        # Database query domain
│   ├── transaction-logic.ts  # Transaction management
│   └── data-consistency.ts   # Data consistency rules
└── /apps/backend/cache/domain/schemas/
    ├── cache-strategies.ts   # Internal cache strategies
    └── invalidation-rules.ts # Cache invalidation logic
```

## Schema Categories

### 1. API Request/Response Schemas

#### Database Service Schemas
```typescript
// /shared/schemas/database.ts

import { object, string, number, boolean, array, optional, custom } from 'valibot';

/**
 * Query request schema
 * @source: Database Service Feature F-002, Scenario SC-021
 */
export const QueryRequestSchema = object({
  table: string('Table name', [minLength(1)]),
  select: optional(array(string('Column names'))),
  where: optional(string('WHERE clause')),
  orderBy: optional(string('ORDER BY clause')),
  limit: optional(number('LIMIT value', [minValue(1), maxValue(1000)])),
  offset: optional(number('OFFSET value', [minValue(0)])),
});

/**
 * Query response schema
 * @source: Database Service Feature F-002, Scenario SC-021
 */
export const QueryResponseSchema = object({
  success: boolean('Query execution status'),
  data: array(object('Row data', {})), // Dynamic object structure
  count: number('Number of rows returned'),
  error: optional(string('Error message')),
});

/**
 * Transaction operation schema
 * @source: Database Service Feature F-002, Scenario SC-022
 */
export const TransactionOperationSchema = object({
  type: enumType(['INSERT', 'UPDATE', 'DELETE', 'SELECT']),
  table: string('Target table', [minLength(1)]),
  data: optional(object('Operation data', {})),
  where: optional(string('WHERE clause')),
});
```

#### Cache Service Schemas
```typescript
// /shared/schemas/cache.ts

import { object, string, number, optional, union } from 'valibot';

/**
 * Cache set operation schema
 * @source: Cache Service Feature F-003, Scenario SC-030
 */
export const CacheSetSchema = object({
  key: string('Cache key', [minLength(1), maxLength(255)]),
  value: union([string('String value'), number('Numeric value'), object('Object value')]),
  ttl: optional(number('Time to live in seconds', [minValue(1)])),
  namespace: optional(string('Cache namespace', [maxLength(100)])),
});

/**
 * Cache get operation schema
 * @source: Cache Service Feature F-003, Scenario SC-031
 */
export const CacheGetSchema = object({
  key: string('Cache key', [minLength(1)]),
  namespace: optional(string('Cache namespace')),
});

/**
 * Cache response schema
 * @source: Cache Service Feature F-003, Scenario SC-031
 */
export const CacheResponseSchema = object({
  found: boolean('Key existence status'),
  value: optional(union([string(), number(), object({})])),
  ttl: optional(number('Remaining TTL in seconds')),
});
```

### 2. Domain Entity Schemas

#### User Schema
```typescript
// /shared/schemas/user.ts

import { object, string, enumType, optional, email } from 'valibot';

/**
 * User creation schema
 * @source: Auth Service Feature F-005, Scenario SC-050
 */
export const CreateUserSchema = object({
  email: string('User email address', [email()]),
  name: string('User full name', [minLength(1), maxLength(255)]),
  role: enumType(['user', 'admin', 'moderator']),
  metadata: optional(object('Additional user data', {})),
});

/**
 * User profile schema
 * @source: Auth Service Feature F-005, Scenario SC-051
 */
export const UserProfileSchema = object({
  id: string('User ID'),
  email: string('User email'),
  name: string('User name'),
  role: enumType(['user', 'admin', 'moderator']),
  isActive: boolean('Account status'),
  lastLoginAt: optional(string('Last login timestamp')),
  createdAt: string('Account creation timestamp'),
  updatedAt: string('Profile update timestamp'),
});
```

### 3. Internal Domain Schemas

#### User Management Domain Schemas
```typescript
// /apps/backend/elysiajs/domain/schemas/user-management.ts

import { object, string, enumType, optional, custom } from 'valibot';

/**
 * Internal user creation schema with business rules
 * @source: Auth Service Feature F-005, Scenario SC-050 (Internal)
 * @classification: internal - service: elysiajs
 * @reason: Contains internal business logic for user creation
 */
export const CreateUserInternalSchema = object({
  // Basic user info (from shared schema)
  email: string('User email address', [email()]),
  name: string('User full name', [minLength(1), maxLength(255)]),
  role: enumType(['user', 'admin', 'moderator']),

  // Internal fields - not exposed externally
  source: enumType(['registration_form', 'admin_panel', 'api_import']),
  metadata: object('Internal creation metadata', {
    ipAddress: string('Creator IP address'),
    userAgent: optional(string('Creator user agent')),
    referralCode: optional(string('Referral code used')),
    campaignSource: optional(string('Marketing campaign source')),
  }),

  // Business rule fields
  approvalRequired: boolean('Whether admin approval is required'),
  trialEndDate: optional(string('Trial period end date')),
  onboardingSteps: array(enumType(['email_verified', 'profile_completed', 'preferences_set'])),
});

/**
 * Internal user profile with business logic
 * @source: Auth Service Feature F-005, Scenario SC-051 (Internal)
 * @classification: internal - service: elysiajs
 * @reason: Contains internal profile management logic
 */
export const UserProfileInternalSchema = object({
  // Shared profile fields
  ...UserProfileSchema.entries,

  // Internal business logic fields
  permissions: array(string('User permissions')),
  preferences: object('User preferences', {
    theme: enumType(['light', 'dark', 'auto']),
    notifications: object('Notification settings', {
      email: boolean('Email notifications'),
      push: boolean('Push notifications'),
      sms: boolean('SMS notifications'),
    }),
    privacy: object('Privacy settings', {
      profileVisibility: enumType(['public', 'friends', 'private']),
      showEmail: boolean('Show email in profile'),
    }),
  }),

  // Internal tracking fields
  loginCount: number('Total login count'),
  lastActiveAt: string('Last activity timestamp'),
  riskScore: number('Account risk score', [minValue(0), maxValue(100)]),

  // Business invariants
  updateHistory: array(object('Profile update history', {
    field: string('Updated field'),
    oldValue: optional(string('Previous value')),
    newValue: string('New value'),
    updatedAt: string('Update timestamp'),
    updatedBy: string('Who made the change'),
  })),
});

/**
 * Business rule validation for role assignment
 * @source: User Management Business Rules
 */
export const RoleAssignmentSchema = object({
  userId: string('Target user ID'),
  newRole: enumType(['user', 'admin', 'moderator']),
  assignedBy: string('Admin user ID assigning the role'),
  reason: string('Reason for role assignment', [minLength(10), maxLength(500)]),
  expiresAt: optional(string('Role expiration date')),
  conditions: optional(array(string('Conditions for role maintenance'))),
});
```

#### Database Domain Schemas
```typescript
// /apps/backend/db/domain/schemas/query-logic.ts

import { object, string, array, enumType, custom } from 'valibot';

/**
 * Internal query optimization schema
 * @source: Database Service Feature F-002, Scenario SC-025 (Internal)
 * @classification: internal - service: database
 * @reason: Contains internal query optimization logic
 */
export const QueryOptimizationSchema = object({
  originalQuery: string('Original SQL query'),
  optimizedQuery: string('Optimized SQL query'),
  optimizationStrategy: enumType(['index_hint', 'query_rewrite', 'join_reorder']),
  performanceGain: object('Performance metrics', {
    executionTimeMs: number('Execution time in milliseconds'),
    rowsScanned: number('Rows scanned'),
    indexUsage: string('Index used'),
  }),
  recommendations: array(string('Optimization recommendations')),
});

/**
 * Transaction management internal schema
 * @source: Database Service Feature F-002, Scenario SC-026 (Internal)
 * @classification: internal - service: database
 * @reason: Contains internal transaction management logic
 */
export const TransactionManagementSchema = object({
  transactionId: string('Unique transaction identifier'),
  operations: array(object('Transaction operations', {
    order: number('Operation order'),
    type: enumType(['INSERT', 'UPDATE', 'DELETE', 'SELECT']),
    table: string('Target table'),
    data: optional(object('Operation data')),
    where: optional(string('WHERE clause')),
  })),
  isolationLevel: enumType(['READ_COMMITTED', 'REPEATABLE_READ', 'SERIALIZABLE']),
  timeoutMs: number('Transaction timeout in milliseconds'),
  rollbackStrategy: enumType(['full_rollback', 'partial_rollback', 'retry']),
});
```

### 4. Internal Service Schemas

#### Client Configuration Schema
```typescript
// /shared/schemas/client-config.ts

import { object, string, number, enumType, optional } from 'valibot';

/**
 * Database client configuration
 * @source: Database Service Feature F-002, Scenario SC-020
 */
export const DatabaseConfigSchema = object({
  url: string('Database connection URL'),
  maxConnections: number('Maximum connection pool size', [minValue(1), maxValue(100)]),
  connectionTimeout: number('Connection timeout in milliseconds', [minValue(1000)]),
  idleTimeout: number('Idle connection timeout', [minValue(5000)]),
  ssl: optional(boolean('SSL connection requirement')),
});

/**
 * Redis client configuration
 * @source: Cache Service Feature F-003, Scenario SC-035
 */
export const RedisConfigSchema = object({
  host: string('Redis host', [minLength(1)]),
  port: number('Redis port', [minValue(1), maxValue(65535)]),
  password: optional(string('Redis password')),
  database: number('Redis database number', [minValue(0), maxValue(15)]),
  keyPrefix: optional(string('Key prefix for namespacing')),
});
```

### 4. Error Schema Definitions

```typescript
// /shared/schemas/errors.ts

import { object, string, enumType, optional, array } from 'valibot';

/**
 * Standard error response schema
 * @source: Multiple Features - Error handling scenarios
 */
export const ErrorResponseSchema = object({
  success: boolean('Operation success status'),
  error: object('Error details', {
    code: string('Error code'),
    message: string('Error message'),
    type: enumType(['VALIDATION', 'AUTHORIZATION', 'NOT_FOUND', 'INTERNAL', 'EXTERNAL']),
    details: optional(array(string('Additional error details'))),
    timestamp: string('Error timestamp'),
    requestId: optional(string('Request correlation ID')),
  }),
});

/**
 * Validation error details schema
 * @source: Schema validation requirements
 */
export const ValidationErrorSchema = object({
  field: string('Field that failed validation'),
  rule: string('Validation rule that failed'),
  value: optional(string('Invalid value')),
  message: string('Validation error message'),
});
```

## Custom Validation Functions

### Business Logic Validators
```typescript
// /shared/schemas/validators.ts

import { custom } from 'valibot';

/**
 * Validates ISO 8601 timestamp format
 */
export const isoTimestamp = custom<string>((input) => {
  const isoRegex = /^\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}(\.\d{3})?Z?$/;
  return isoRegex.test(input);
}, 'Must be a valid ISO 8601 timestamp');

/**
 * Validates email address format
 */
export const email = custom<string>((input) => {
  const emailRegex = /^[^\s@]+@[^\s@]+\.[^\s@]+$/;
  return emailRegex.test(input);
}, 'Must be a valid email address');

/**
 * Validates UUID format
 */
export const uuid = custom<string>((input) => {
  const uuidRegex = /^[0-9a-f]{8}-[0-9a-f]{4}-[1-5][0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}$/i;
  return uuidRegex.test(input);
}, 'Must be a valid UUID');

/**
 * Validates strong password
 */
export const strongPassword = custom<string>((input) => {
  // At least 8 characters, one uppercase, one lowercase, one number, one special character
  const passwordRegex = /^(?=.*[a-z])(?=.*[A-Z])(?=.*\d)(?=.*[@$!%*?&])[A-Za-z\d@$!%*?&]{8,}$/;
  return passwordRegex.test(input);
}, 'Password must be at least 8 characters with uppercase, lowercase, number, and special character');

/**
 * Validates cache key format
 */
export const cacheKey = custom<string>((input) => {
  // Alphanumeric with colons, dots, underscores, hyphens
  const keyRegex = /^[a-zA-Z0-9:._-]+$/;
  return keyRegex.test(input) && input.length <= 255;
}, 'Cache key must be alphanumeric with limited special characters');
```

## Schema Composition Patterns

### Base Schema Pattern
```typescript
// /shared/schemas/base.ts

import { object, string, optional } from 'valibot';

/**
 * Base schema with common audit fields
 */
export const BaseAuditSchema = {
  id: string('Unique identifier'),
  createdAt: string('Creation timestamp', [isoTimestamp]),
  updatedAt: string('Last update timestamp', [isoTimestamp]),
  createdBy: optional(string('Creator ID')),
  updatedBy: optional(string('Updater ID')),
};

/**
 * Base schema with soft delete
 */
export const SoftDeleteSchema = {
  ...BaseAuditSchema,
  deletedAt: optional(string('Deletion timestamp')),
  deletedBy: optional(string('Deleter ID')),
  isDeleted: boolean('Soft delete flag'),
};
```

### Extensible Schema Pattern
```typescript
// /shared/schemas/extensible.ts

import { object, string, record, optional } from 'valibot';

/**
 * Extensible schema with metadata support
 */
export const createExtensibleSchema = (baseSchema: object) => {
  return object({
    ...baseSchema.entries,
    metadata: optional(record(string('Metadata key'), string('Metadata value'))),
    tags: optional(array(string('Tag'))),
  });
};
```

## Integration Examples

### API Endpoint Integration
```typescript
// /apps/backend/elysiajs/app/routes/users.ts

import { Elysia, t } from 'elysia';
import { CreateUserSchema, UserProfileSchema } from 'shared/schemas/user';

export const userRoutes = new Elysia({ prefix: '/users' })
  .post('/',
    async ({ body }) => {
      // Implementation here
      return { success: true, user: createdUser };
    },
    {
      body: CreateUserSchema,
      response: {
        200: t.Object({
          success: t.Boolean(),
          user: UserProfileSchema,
        }),
        400: ErrorResponseSchema,
      },
    }
  )
  .get('/:id',
    async ({ params }) => {
      // Implementation here
      return { success: true, user };
    },
    {
      params: t.Object({ id: t.String() }),
      response: {
        200: t.Object({
          success: t.Boolean(),
          user: UserProfileSchema,
        }),
        404: ErrorResponseSchema,
      },
    }
  );
```

### Database Integration
```typescript
// /apps/backend/db/adapters/users.ts

import { drizzle } from 'drizzle-orm/postgres-js';
import { UserProfileSchema, CreateUserSchema } from 'shared/schemas/user';

export class UserAdapter {
  private db = drizzle(process.env.DATABASE_URL);

  async createUser(userData: typeof CreateUserSchema.infer): Promise<typeof UserProfileSchema.infer> {
    // Schema validation happens at boundary
    const validated = parse(CreateUserSchema, userData);

    // Database operation with typed results
    const result = await this.db.insert(usersTable).values(validated).returning();

    // Return with full schema validation
    return parse(UserProfileSchema, result[0]);
  }
}
```

## Success Criteria

1. ✅ **Schema Classification** - Clear separation between shared and internal schemas
2. ✅ **Shared Schema Priority** - All service interface schemas created first
3. ✅ **Internal Domain Coverage** - All internal domain logic has corresponding schemas
4. ✅ **Complete Gherkin Coverage** - All behavior scenarios have corresponding schemas
5. ✅ **Type Safety** - Full TypeScript compatibility with no implicit any
6. ✅ **Runtime Validation** - All data crossing boundaries is validated
7. ✅ **Business Rule Enforcement** - Custom validators for all business constraints
8. ✅ **Schema Consistency** - No conflicting or redundant schemas
9. ✅ **Documentation Completeness** - All schemas properly documented with classification

## Output Format

### File Structure
```
# Shared Schemas (Priority 1 - Service Interfaces)
/shared/schemas/
├── index.ts                    # Shared schema exports and utilities
├── base.ts                     # Base schemas and patterns
├── database.ts                 # Database service interface schemas
├── cache.ts                    # Cache service interface schemas
├── queue.ts                    # Queue service interface schemas
├── auth.ts                     # Authentication interface schemas
├── storage.ts                  # Storage service interface schemas
├── user.ts                     # Shared user data contracts
├── client-config.ts            # Shared configuration schemas
├── errors.ts                   # Shared error response schemas
├── validators.ts               # Shared custom validation functions
└── README.md                   # Shared schema documentation

# Internal Schemas (Priority 2 - Domain Logic)
/apps/backend/elysiajs/domain/schemas/
├── index.ts                    # Internal schema exports
├── user-management.ts          # User domain logic schemas
├── business-rules.ts           # Business rule validation schemas
├── validation.ts               # Internal validation schemas
└── README.md                   # Internal schema documentation

/apps/backend/db/domain/schemas/
├── index.ts                    # Database internal schema exports
├── query-logic.ts              # Query optimization schemas
├── transaction-logic.ts        # Transaction management schemas
├── data-consistency.ts         # Data consistency schemas
└── README.md                   # Database schema documentation

/apps/backend/cache/domain/schemas/
├── index.ts                    # Cache internal schema exports
├── cache-strategies.ts         # Internal cache strategy schemas
├── invalidation-rules.ts       # Cache invalidation schemas
└── README.md                   # Cache schema documentation
```

### Schema Documentation Format
```markdown
# Schema Documentation

## Database Service Schemas

### QueryRequestSchema
- **Purpose**: Validates database query requests
- **Source**: Gherkin Feature F-002, Scenario SC-021
- **Usage**: API request validation for database queries
- **Fields**: table, select, where, orderBy, limit, offset

### QueryResponseSchema
- **Purpose**: Validates database query responses
- **Source**: Gherkin Feature F-002, Scenario SC-021
- **Usage**: API response validation for query results
- **Fields**: success, data, count, error
```

## Integration with Teja Pattern

1. **Behavior Input** - Uses Gherkin scenarios as schema requirements
2. **Test Guidance** - Provides validation rules for test implementations
3. **Implementation Contract** - Defines strict contracts for services
4. **Type Safety** - Ensures compile-time and runtime type consistency
5. **Documentation** - Completes data contract documentation

## Tooling Requirements

- **Valibot Library** - Schema definition and validation
- **TypeScript** - Type system integration
- **Schema Generators** - Automated schema creation utilities
- **Validation Testers** - Schema validation test harness

## Risk Assessment

**High Risks:**
- Schema inconsistencies between services
- Performance impact of runtime validation
- Complex business rule validation logic

**Medium Risks:**
- Schema evolution and versioning challenges
- Type inference complexities
- Custom validation function maintenance

**Low Risks:**
- Minor syntax issues in schema definitions
- Documentation formatting inconsistencies
- Test coverage gaps for edge cases

## Quality Assurance

### Validation Checklist
- [ ] All Gherkin scenarios have corresponding schemas
- [ ] Schema validation covers all business rules
- [ ] TypeScript types are properly inferred
- [ ] Custom validators are thoroughly tested
- [ ] Error messages are clear and actionable
- [ ] Schema documentation is complete and accurate
- [ ] Cross-service schema consistency is maintained
- [ ] Performance impact of validation is acceptable