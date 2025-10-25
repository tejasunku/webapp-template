# Testing Agent
# @agent: testing-implementation
# @phase: Testing
# @priority: high
# @dependencies: ["schema-agent", "behavior-agent"]

## Agent Purpose

Creates comprehensive test suites by translating Gherkin behavior specifications and Valibot schemas into executable tests. Prioritizes service interface testing first, then creates domain-specific tests for internal service logic. Ensures complete test coverage of all specified behavior.

## Core Responsibilities

1. **Interface Testing (Priority 1)**
   - Create tests for all service-to-service interfaces
   - Test input/output contracts between services
   - Validate shared schema compliance across boundaries
   - Ensure API contract adherence and error handling

2. **Domain Testing (Priority 2)**
   - Create tests for internal service domain logic
   - Test data invariants within service boundaries
   - Validate business rules and constraints
   - Ensure internal schema compliance

3. **Test Structure Organization**
   - Organize tests by interface vs domain
   - Maintain clear test hierarchy and naming
   - Ensure test isolation and independence
   - Create comprehensive test suites

4. **Test Implementation Strategy**
   - Use appropriate testing frameworks for each layer
   - Create mocking strategies for external dependencies
   - Implement test data management
   - Ensure test performance and reliability

5. **Coverage Validation**
   - Verify complete Gherkin scenario coverage
   - Ensure all schema validations are tested
   - Validate test completeness and quality
   - Generate coverage reports

## Agent Configuration

```yaml
agent_type: "testing_implementation"
priority: "high"
dependencies: ["schema-agent", "behavior-agent"]
tools_required:
  - "Vitest (unit/integration tests)"
  - "Playwright (E2E tests)"
  - "Testing utilities and mocks"
  - "Coverage analysis tools"
memory_requirements:
  - gherkin_scenario_mapping
  - schema_validation_testing
  - interface_contract_testing
  - domain_logic_testing
output_requirements:
  - test_suite_files
  - test_coverage_reports
  - mocking_utilities
  - test_data_fixtures
```

## Test Organization Strategy

### Directory Structure
```
tests/
├── interface/                    # Service interface tests (Priority 1)
│   ├── shared/                   # Tests for shared schemas
│   │   ├── database.test.ts
│   │   ├── cache.test.ts
│   │   ├── queue.test.ts
│   │   ├── auth.test.ts
│   │   └── storage.test.ts
│   └── contracts/                # Service-to-service contracts
│       ├── api-to-database.test.ts
│       ├── api-to-cache.test.ts
│       └── worker-to-queue.test.ts
├── integration/                  # Cross-service integration tests
│   ├── api-endpoints.test.ts
│   ├── data-flow.test.ts
│   └── error-handling.test.ts
└── e2e/                         # End-to-end system tests
    ├── user-workflows.test.ts
    └── system-behavior.test.ts

apps/backend/elysiajs/tests/
├── domain/                       # Domain logic tests (Priority 2)
│   ├── user-management.test.ts
│   ├── data-validation.test.ts
│   └── business-rules.test.ts
└── app/                          # Application orchestration tests
    ├── routing.test.ts
    └── error-scenarios.test.ts

apps/backend/db/tests/
├── domain/                       # Database domain tests
│   ├── query-logic.test.ts
│   ├── transaction-management.test.ts
│   └── data-consistency.test.ts
└── sdk/                          # Database SDK tests
    └── connection-management.test.ts
```

## Agent Workflow

### Step 1: Analyze Gherkin and Schema Specifications
- Read all Gherkin features and identify interface vs domain scenarios
- Examine shared schemas from `/shared/schemas/`
- Review internal schemas from `/apps/*/domain/`
- Map test priorities and dependencies

### Step 2: Design Interface Test Strategy (Priority 1)
- Create tests for all shared schema boundaries
- Define service-to-service contract tests
- Plan integration test scenarios
- Design mocking strategies for external services

### Step 3: Implement Interface Tests
- Write comprehensive interface test suites
- Create test utilities and fixtures
- Implement proper mocking and stubbing
- Ensure contract validation and error handling

### Step 4: Design Domain Test Strategy (Priority 2)
- Identify internal domain logic scenarios
- Map business rules and data invariants
- Plan domain-specific test cases
- Design test data management

### Step 5: Implement Domain Tests
- Create domain logic test suites
- Test internal schema validations
- Validate business rule implementations
- Ensure data consistency and invariants

### Step 6: Validate Test Coverage
- Verify complete Gherkin scenario coverage
- Check shared vs internal schema testing
- Generate comprehensive coverage reports
- Validate test quality and effectiveness

## Interface Testing Templates

### Shared Schema Interface Tests
```typescript
// tests/interface/shared/database.test.ts

import { describe, test, expect, beforeEach, vi, afterEach } from 'vitest';
import {
  QueryRequestSchema,
  QueryResponseSchema,
  TransactionOperationSchema
} from 'shared/schemas/database';
import { makeScopedClient } from 'shared/utils/clientFactory';

describe('@feature: Database Service Interface (F-002)', () => {
  let mockDbAdapter: any;
  let getDbClient: () => any;

  beforeEach(() => {
    // Mock database adapter
    mockDbAdapter = {
      query: vi.fn(),
      transaction: vi.fn(),
      close: vi.fn(),
    };

    // Create scoped client
    getDbClient = makeScopedClient(() => mockDbAdapter);
    vi.clearAllMocks();
  });

  describe('@scenario: SC-021 - Query execution with proper error handling', () => {
    test('should execute valid SELECT query and return structured response', async () => {
      // Arrange
      const queryRequest = {
        table: 'users',
        select: ['id', 'name', 'email'],
        where: 'active = true',
        limit: 10
      };

      const mockResult = [
        { id: '1', name: 'John Doe', email: 'john@example.com' },
        { id: '2', name: 'Jane Smith', email: 'jane@example.com' }
      ];

      mockDbAdapter.query.mockResolvedValue(mockResult);
      const dbClient = getDbClient();

      // Act
      const result = await dbClient.query(queryRequest);

      // Assert
      expect(mockDbAdapter.query).toHaveBeenCalledWith(queryRequest);

      // Validate response schema
      const validatedResponse = QueryResponseSchema.parse(result);
      expect(validatedResponse.success).toBe(true);
      expect(validatedResponse.data).toEqual(mockResult);
      expect(validatedResponse.count).toBe(2);
    });

    test('should handle invalid SQL query with proper error response', async () => {
      // Arrange
      const invalidQuery = {
        table: 'nonexistent_table',
        select: ['*']
      };

      const dbError = new Error('Table "nonexistent_table" doesn\'t exist');
      mockDbAdapter.query.mockRejectedValue(dbError);
      const dbClient = getDbClient();

      // Act
      const result = await dbClient.query(invalidQuery);

      // Assert
      expect(mockDbAdapter.query).toHaveBeenCalledWith(invalidQuery);

      // Validate error response schema
      const validatedResponse = QueryResponseSchema.parse(result);
      expect(validatedResponse.success).toBe(false);
      expect(validatedResponse.error).toBeDefined();
      expect(validatedResponse.error).toContain('Table');
    });
  });

  describe('@scenario: SC-022 - Transaction management and rollback', () => {
    test('should execute all operations in transaction successfully', async () => {
      // Arrange
      const transactionOps = [
        {
          type: 'INSERT',
          table: 'users',
          data: { name: 'New User', email: 'new@example.com' }
        },
        {
          type: 'UPDATE',
          table: 'audit_log',
          data: { action: 'user_created', user_id: '123' },
          where: 'id = 1'
        }
      ];

      mockDbAdapter.transaction.mockResolvedValue({
        success: true,
        results: [{ id: '123' }, { rowsAffected: 1 }]
      });
      const dbClient = getDbClient();

      // Act
      const result = await dbClient.transaction(transactionOps);

      // Assert
      expect(mockDbAdapter.transaction).toHaveBeenCalledWith(transactionOps);
      expect(result.success).toBe(true);
      expect(result.results).toHaveLength(2);
    });

    test('should rollback transaction on operation failure', async () => {
      // Arrange
      const failingTransactionOps = [
        {
          type: 'INSERT',
          table: 'users',
          data: { name: 'User', email: 'invalid-email' } // Invalid email
        }
      ];

      const validationError = new Error('Invalid email format');
      mockDbAdapter.transaction.mockRejectedValue(validationError);
      const dbClient = getDbClient();

      // Act
      await expect(dbClient.transaction(failingTransactionOps))
        .rejects.toThrow('Invalid email format');

      // Assert
      expect(mockDbAdapter.transaction).toHaveBeenCalledWith(failingTransactionOps);
    });
  });
});
```

### Service-to-Service Contract Tests
```typescript
// tests/interface/contracts/api-to-database.test.ts

import { describe, test, expect, beforeEach, vi } from 'vitest';
import {
  CreateUserSchema,
  UserProfileSchema
} from 'shared/schemas/user';
import { makeScopedClient } from 'shared/utils/clientFactory';

describe('@feature: API-Database Service Contract', () => {
  let mockApiClient: any;
  let mockDbClient: any;
  let getApiClient: () => any;
  let getDbClient: () => any;

  beforeEach(() => {
    // Mock API client
    mockApiClient = {
      post: vi.fn(),
      get: vi.fn(),
      put: vi.fn(),
      delete: vi.fn(),
    };

    // Mock database client
    mockDbClient = {
      query: vi.fn(),
      transaction: vi.fn(),
    };

    getApiClient = makeScopedClient(() => mockApiClient);
    getDbClient = makeScopedClient(() => mockDbClient);
    vi.clearAllMocks();
  });

  describe('User Creation Contract', () => {
    test('should validate user creation data flow from API to database', async () => {
      // Arrange
      const userData = {
        email: 'test@example.com',
        name: 'Test User',
        role: 'user'
      };

      const createdUser = {
        id: '123',
        email: 'test@example.com',
        name: 'Test User',
        role: 'user',
        isActive: true,
        createdAt: '2024-01-01T00:00:00Z',
        updatedAt: '2024-01-01T00:00:00Z'
      };

      // API layer validation
      const apiClient = getApiClient();
      mockApiClient.post.mockResolvedValue({ success: true, user: createdUser });

      // Database layer validation
      const dbClient = getDbClient();
      mockDbClient.transaction.mockResolvedValue({
        success: true,
        results: [{ id: '123' }]
      });

      // Act & Assert - API layer validates input schema
      await expect(CreateUserSchema.parse(userData)).resolves.toBe(userData);

      // Act - API processes request
      const apiResult = await apiClient.post('/users', userData);

      // Assert - API validates output schema
      expect(UserProfileSchema.parse(apiResult.user)).toEqual(createdUser);

      // Assert - Database received properly formatted data
      expect(mockDbClient.transaction).toHaveBeenCalled();
    });
  });
});
```

## Domain Testing Templates

### Internal Domain Logic Tests
```typescript
// apps/backend/elysiajs/tests/domain/user-management.test.ts

import { describe, test, expect, beforeEach } from 'vitest';
import { UserDomainService } from '../domain/user';
import {
  CreateUserInternalSchema,
  UserProfileInternalSchema
} from '../domain/schemas/user';

describe('@feature: User Domain Management (Internal)', () => {
  let userDomain: UserDomainService;

  beforeEach(() => {
    userDomain = new UserDomainService();
  });

  describe('@scenario: SC-050 - User creation with business rules', () => {
    test('should enforce unique email constraint within domain', async () => {
      // Arrange
      const userData = {
        email: 'existing@example.com',
        name: 'Test User',
        role: 'user'
      };

      // Mock existing user check
      vi.spyOn(userDomain, 'emailExists').mockResolvedValue(true);

      // Act & Assert
      await expect(userDomain.createUser(userData))
        .rejects.toThrow('Email already exists');
    });

    test('should apply business rule for user role assignments', async () => {
      // Arrange
      const userData = {
        email: 'new@example.com',
        name: 'New User',
        role: 'admin' // Attempting to assign admin role
      };

      // Mock authorization check
      vi.spyOn(userDomain, 'canAssignRole').mockResolvedValue(false);

      // Act & Assert
      await expect(userDomain.createUser(userData))
        .rejects.toThrow('Insufficient permissions for admin role assignment');
    });

    test('should validate internal user data structure', async () => {
      // Arrange
      const userData = {
        email: 'valid@example.com',
        name: 'Valid User',
        role: 'user',
        internalFields: {
          source: 'registration_form',
          metadata: { referrer: 'google' }
        }
      };

      vi.spyOn(userDomain, 'emailExists').mockResolvedValue(false);
      vi.spyOn(userDomain, 'canAssignRole').mockResolvedValue(true);

      // Act
      const result = await userDomain.createUser(userData);

      // Assert - Validates internal schema
      expect(CreateUserInternalSchema.parse(userData)).toEqual(userData);
      expect(UserProfileInternalSchema.parse(result)).toBeDefined();
      expect(result.internalFields).toBeDefined();
    });
  });

  describe('@scenario: SC-051 - User profile data invariants', () => {
    test('should maintain profile update history invariant', async () => {
      // Arrange
      const userId = 'user123';
      const updateData = {
        name: 'Updated Name',
        preferences: { theme: 'dark' }
      };

      const currentProfile = {
        id: userId,
        name: 'Original Name',
        preferences: { theme: 'light' },
        updatedAt: '2024-01-01T00:00:00Z',
        updateCount: 0
      };

      vi.spyOn(userDomain, 'getProfile').mockResolvedValue(currentProfile);

      // Act
      const updatedProfile = await userDomain.updateProfile(userId, updateData);

      // Assert - Invariant: updateCount must increment
      expect(updatedProfile.updateCount).toBe(currentProfile.updateCount + 1);

      // Invariant: updatedAt must be newer
      expect(new Date(updatedProfile.updatedAt))
        .toBeGreaterThan(new Date(currentProfile.updatedAt));

      // Invariant: previous values must be preserved in history
      expect(updatedProfile.previousName).toBe(currentProfile.name);
    });
  });
});
```

## Test Data Management

### Test Fixtures and Factories
```typescript
// tests/fixtures/user-factory.ts

import { faker } from '@faker-js/faker';
import { CreateUserSchema, UserProfileSchema } from 'shared/schemas/user';

export class UserFactory {
  static createUserData(overrides = {}) {
    const userData = {
      email: faker.internet.email(),
      name: faker.person.fullName(),
      role: 'user',
      ...overrides
    };

    return CreateUserSchema.parse(userData);
  }

  static createProfileData(overrides = {}) {
    const profileData = {
      id: faker.string.uuid(),
      email: faker.internet.email(),
      name: faker.person.fullName(),
      role: faker.helpers.arrayElement(['user', 'admin', 'moderator']),
      isActive: true,
      createdAt: faker.date.past().toISOString(),
      updatedAt: faker.date.recent().toISOString(),
      ...overrides
    };

    return UserProfileSchema.parse(profileData);
  }

  static createMultipleProfiles(count: number, overrides = {}) {
    return Array.from({ length: count }, () =>
      this.createProfileData(overrides)
    );
  }
}
```

### Mock Utilities
```typescript
// tests/mocks/service-mocks.ts

import { vi } from 'vitest';
import { makeScopedClient } from 'shared/utils/clientFactory';

export class ServiceMockFactory {
  static createDatabaseMock() {
    const mockDb = {
      query: vi.fn(),
      transaction: vi.fn(),
      close: vi.fn(),
    };

    return {
      client: mockDb,
      getClient: () => mockDb,
      scopedClient: makeScopedClient(() => mockDb)
    };
  }

  static createCacheMock() {
    const mockCache = {
      get: vi.fn(),
      set: vi.fn(),
      del: vi.fn(),
      clear: vi.fn(),
    };

    return {
      client: mockCache,
      getClient: () => mockCache,
      scopedClient: makeScopedClient(() => mockCache)
    };
  }

  static createQueueMock() {
    const mockQueue = {
      enqueue: vi.fn(),
      dequeue: vi.fn(),
      ack: vi.fn(),
      nack: vi.fn(),
    };

    return {
      client: mockQueue,
      getClient: () => mockQueue,
      scopedClient: makeScopedClient(() => mockQueue)
    };
  }
}
```

## Integration Test Templates

### Cross-Service Integration Tests
```typescript
// tests/integration/data-flow.test.ts

import { describe, test, expect, beforeAll, afterAll } from 'vitest';
import {
  DatabaseService,
  CacheService,
  QueueService
} from '../services';

describe('@feature: Cross-Service Data Flow Integration', () => {
  let dbService: DatabaseService;
  let cacheService: CacheService;
  let queueService: QueueService;

  beforeAll(async () => {
    // Initialize real services for integration testing
    dbService = new DatabaseService(process.env.TEST_DB_URL);
    cacheService = new CacheService(process.env.TEST_CACHE_URL);
    queueService = new QueueService(process.env.TEST_QUEUE_URL);

    await dbService.connect();
    await cacheService.connect();
    await queueService.connect();
  });

  afterAll(async () => {
    // Cleanup
    await dbService.disconnect();
    await cacheService.disconnect();
    await queueService.disconnect();
  });

  test('should maintain data consistency across database, cache, and queue', async () => {
    // Arrange
    const userData = {
      id: 'test-user-123',
      email: 'integration@test.com',
      name: 'Integration Test User'
    };

    // Act - Create user in database
    await dbService.users.create(userData);

    // Cache user data
    await cacheService.set(`user:${userData.id}`, userData, 3600);

    // Enqueue notification
    await queueService.enqueue('user-notifications', {
      type: 'user_created',
      userId: userData.id,
      timestamp: new Date().toISOString()
    });

    // Assert - Verify data consistency
    const dbUser = await dbService.users.findById(userData.id);
    const cachedUser = await cacheService.get(`user:${userData.id}`);
    const queueMessage = await queueService.dequeue('user-notifications');

    expect(dbUser).toEqual(userData);
    expect(cachedUser).toEqual(userData);
    expect(queueMessage.userId).toBe(userData.id);
  });
});
```

## Coverage Validation

### Coverage Analysis
```typescript
// scripts/validate-test-coverage.ts

import { readFileSync, readdirSync } from 'fs';
import { parse } from 'gherkin';

interface CoverageReport {
  gherkinFeatures: string[];
  coveredScenarios: string[];
  sharedSchemas: string[];
  testedSchemas: string[];
  interfaceTests: string[];
  domainTests: string[];
}

export function validateTestCoverage(): CoverageReport {
  const report: CoverageReport = {
    gherkinFeatures: [],
    coveredScenarios: [],
    sharedSchemas: [],
    testedSchemas: [],
    interfaceTests: [],
    domainTests: []
  };

  // Analyze Gherkin features
  const featureFiles = readdirSync('docs/architecture/v0.0/')
    .filter(file => file.endsWith('.feature'));

  for (const featureFile of featureFiles) {
    const featureContent = readFileSync(`docs/architecture/v0.0/${featureFile}`, 'utf8');
    const gherkinDocument = parse(featureContent);

    report.gherkinFeatures.push(featureFile);

    gherkinDocument.feature?.children.forEach(child => {
      if (child.type === 'Scenario') {
        const scenarioName = child.name || 'Unknown Scenario';
        report.coveredScenarios.push(`${featureFile}:${scenarioName}`);
      }
    });
  }

  // Analyze test files
  const testFiles = [
    ...getFiles('tests/interface', '.test.ts'),
    ...getFiles('tests/integration', '.test.ts'),
    ...getFiles('apps/*/tests', '.test.ts')
  ];

  for (const testFile of testFiles) {
    if (testFile.includes('interface/')) {
      report.interfaceTests.push(testFile);
    } else if (testFile.includes('domain/')) {
      report.domainTests.push(testFile);
    }
  }

  return report;
}

function getFiles(dir: string, extension: string): string[] {
  // Implementation to recursively find files with given extension
  return [];
}
```

## Success Criteria

1. ✅ **Interface Test Priority** - All service interface tests created before domain tests
2. ✅ **Gherkin Coverage** - Every Gherkin scenario has corresponding test
3. ✅ **Schema Validation** - All schemas (shared and internal) are tested
4. ✅ **Test Organization** - Clear separation between interface and domain tests
5. ✅ **Mocking Strategy** - Proper mocking for external dependencies
6. ✅ **Coverage Reports** - Comprehensive coverage analysis and reporting

## Output Format

### Test File Organization
```
tests/
├── interface/                    # Priority 1: Service interface tests
│   ├── shared/                   # Shared schema tests
│   │   ├── database.test.ts      # ✅ Database interface
│   │   ├── cache.test.ts         # ✅ Cache interface
│   │   ├── queue.test.ts         # ✅ Queue interface
│   │   ├── auth.test.ts          # ✅ Auth interface
│   │   └── storage.test.ts       # ✅ Storage interface
│   └── contracts/                # Service contracts
│       ├── api-to-database.test.ts
│       ├── api-to-cache.test.ts
│       └── worker-to-queue.test.ts
├── integration/                  # Integration tests
│   ├── api-endpoints.test.ts
│   ├── data-flow.test.ts
│   └── error-handling.test.ts
└── e2e/                         # E2E tests
    ├── user-workflows.test.ts
    └── system-behavior.test.ts

apps/backend/elysiajs/tests/
├── domain/                       # Priority 2: Domain logic tests
│   ├── user-management.test.ts   # User domain invariants
│   ├── data-validation.test.ts   # Internal validation rules
│   └── business-rules.test.ts    # Business logic
└── app/                          # App orchestration tests
    ├── routing.test.ts
    └── error-scenarios.test.ts
```

## Integration with Teja Pattern

1. **Behavior Input** - Uses Gherkin scenarios as test requirements
2. **Schema Input** - Uses Valibot schemas for validation testing
3. **Interface Priority** - Tests service boundaries before internal logic
4. **Domain Focus** - Tests internal invariants specified in Gherkin
5. **Coverage Assurance** - Ensures complete behavior and schema testing

## Tooling Requirements

- **Vitest** - Unit and integration testing framework
- **Playwright** - End-to-end testing framework
- **Faker.js** - Test data generation
- **MSW/vi.mock** - Service mocking
- **Coverage tools** - Test coverage analysis

## Risk Assessment

**High Risks:**
- Incomplete interface test coverage
- Mock implementation drift from real services
- Test performance and reliability issues

**Medium Risks:**
- Complex test data management
- Test isolation and independence challenges
- Integration test environment setup

**Low Risks:**
- Minor test syntax issues
- Documentation inconsistencies
- Coverage report formatting

## Quality Assurance

### Test Quality Checklist
- [ ] All interface scenarios are tested before domain scenarios
- [ ] Every Gherkin scenario has corresponding test case
- [ ] All shared schemas have validation tests
- [ ] All internal schemas have domain tests
- [ ] Mocks accurately represent real service behavior
- [ ] Tests are isolated and independent
- [ ] Test data is properly managed
- [ ] Coverage meets quality standards
- [ ] Tests run reliably and perform well