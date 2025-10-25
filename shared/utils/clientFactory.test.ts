/**
 * Client Factory Tests
 *
 * Tests based on docs/architecture/v0.0/adapter-factory.feature
 * Test labels reference specific scenarios in the Gherkin file
 *
 * @feature: Shared Adapter Factory Pattern
 * @scenario: SC-01 - Client isolation across different processes
 * @scenario: SC-02 - Client isolation across different threads
 * @scenario: SC-03 - Client reuse within same process and thread
 * @scenario: SC-04 - Async interface for synchronous client methods
 * @scenario: SC-05 - Preserving async methods in async wrapper
 * @scenario: SC-06 - Scoped async client factory
 * @scenario: SC-07 - Process ID detection
 * @scenario: SC-08 - Thread ID detection in Node.js
 * @scenario: SC-09 - Thread ID detection fallback
 * @scenario: SC-10 - No top-level side effects
 * @scenario: SC-11 - Error handling in client initialization
 */

import { describe, test, expect, vi, beforeEach, afterEach } from 'vitest';
import type { MockedFunction } from 'vitest';
import {
  makeScopedClient,
  makeAsyncClient,
  makeScopedAsyncClient,
  getCurrentProcessId,
  getCurrentThreadId
} from './clientFactory';

// Test utilities for mocking process and thread environments
interface MockEnvironment {
  processId?: number;
  threadId?: number;
  noProcess?: boolean;
  noWorkerThreads?: boolean;
}

function createMockEnvironment(env: MockEnvironment = {}) {
  const originalProcess = globalThis.process;
  const originalRequire = require;

  // Mock process
  if (env.noProcess) {
    delete (globalThis as any).process;
  } else if (env.processId !== undefined) {
    (globalThis as any).process = { pid: env.processId };
  }

  // Mock worker_threads
  vi.mock('worker_threads', () => {
    if (env.noWorkerThreads) {
      throw new Error('worker_threads not available');
    }
    return { threadId: env.threadId ?? 0 };
  });

  return {
    restore: () => {
      (globalThis as any).process = originalProcess;
      vi.restoreAllMocks();
    }
  };
}

describe('@feature: Shared Adapter Factory Pattern', () => {
  beforeEach(() => {
    vi.resetModules();
    vi.clearAllMocks();
  });

  afterEach(() => {
    vi.restoreAllMocks();
  });

  describe('@scenario: SC-01 - Client isolation across different processes', () => {
    test('should initialize client in first process', () => {
      const mockEnv = createMockEnvironment({ processId: 123 });
      const init = vi.fn(() => ({
        id: 'client-123',
        connect: vi.fn()
      }));
      const getClient = makeScopedClient(init);

      const client = getClient();

      expect(init).toHaveBeenCalledTimes(1);
      expect(client.id).toBe('client-123');
      mockEnv.restore();
    });

    test('should reinitialize in different process', () => {
      // First process
      let mockEnv = createMockEnvironment({ processId: 123 });
      const init = vi.fn(() => ({
        id: 'client-123',
        connect: vi.fn()
      }));
      const getClient = makeScopedClient(init);

      const client1 = getClient();
      expect(init).toHaveBeenCalledTimes(1);
      mockEnv.restore();

      // Different process
      mockEnv = createMockEnvironment({ processId: 124 });
      const client2 = getClient();

      expect(init).toHaveBeenCalledTimes(2);
      expect(client2.id).toBe('client-123');
      expect(client1).not.toBe(client2);
      mockEnv.restore();
    });
  });

  describe('@scenario: SC-02 - Client isolation across different threads', () => {
    test('should initialize client in first thread', () => {
      const mockEnv = createMockEnvironment({ processId: 123, threadId: 0 });
      const init = vi.fn(() => ({
        id: 'client-thread-0',
        connect: vi.fn()
      }));
      const getClient = makeScopedClient(init);

      const client = getClient();

      expect(init).toHaveBeenCalledTimes(1);
      expect(client.id).toBe('client-thread-0');
      mockEnv.restore();
    });

    test('should reinitialize in different thread', () => {
      // First thread
      let mockEnv = createMockEnvironment({ processId: 123, threadId: 0 });
      const init = vi.fn(() => ({
        id: 'client-thread-0',
        connect: vi.fn()
      }));
      const getClient = makeScopedClient(init);

      const client1 = getClient();
      expect(init).toHaveBeenCalledTimes(1);
      mockEnv.restore();

      // Different thread
      mockEnv = createMockEnvironment({ processId: 123, threadId: 1 });
      const client2 = getClient();

      expect(init).toHaveBeenCalledTimes(2);
      expect(client2.id).toBe('client-thread-0');
      expect(client1).not.toBe(client2);
      mockEnv.restore();
    });
  });

  describe('@scenario: SC-03 - Client reuse within same process and thread', () => {
    test('should return same client instance on multiple calls', () => {
      const mockEnv = createMockEnvironment({ processId: 123, threadId: 0 });
      const init = vi.fn(() => ({
        id: 'reusable-client',
        connect: vi.fn()
      }));
      const getClient = makeScopedClient(init);

      const client1 = getClient();
      const client2 = getClient();
      const client3 = getClient();

      expect(init).toHaveBeenCalledTimes(1);
      expect(client1).toBe(client2);
      expect(client2).toBe(client3);
      expect(client1.id).toBe('reusable-client');
      mockEnv.restore();
    });

    test('should not call initialization multiple times', () => {
      const mockEnv = createMockEnvironment({ processId: 123, threadId: 0 });
      const init = vi.fn(() => ({ connect: vi.fn() }));
      const getClient = makeScopedClient(init);

      getClient();
      getClient();
      getClient();

      expect(init).toHaveBeenCalledTimes(1);
      mockEnv.restore();
    });
  });

  describe('@scenario: SC-04 - Async interface for synchronous client methods', () => {
    test('should wrap sync methods to return Promises', async () => {
      const syncClient = {
        getData: vi.fn(() => 'sync-data'),
        postData: vi.fn((data: string) => `processed-${data}`),
        validate: vi.fn((input: any) => input.isValid)
      };

      const asyncClient = makeAsyncClient(syncClient);

      // All methods should be async
      expect(asyncClient.getData()).toBeInstanceOf(Promise);
      expect(asyncClient.postData('test')).toBeInstanceOf(Promise);
      expect(asyncClient.validate({ isValid: true })).toBeInstanceOf(Promise);

      // Results should match original sync behavior
      await expect(asyncClient.getData()).resolves.toBe('sync-data');
      await expect(asyncClient.postData('test')).resolves.toBe('processed-test');
      await expect(asyncClient.validate({ isValid: true })).resolves.toBe(true);

      expect(syncClient.getData).toHaveBeenCalledTimes(1);
      expect(syncClient.postData).toHaveBeenCalledWith('test');
      expect(syncClient.validate).toHaveBeenCalledWith({ isValid: true });
    });

    test('should handle sync method errors as Promise rejection', async () => {
      const syncClient = {
        failingMethod: vi.fn(() => {
          throw new Error('Sync operation failed');
        })
      };

      const asyncClient = makeAsyncClient(syncClient);

      await expect(asyncClient.failingMethod()).rejects.toThrow('Sync operation failed');
      expect(syncClient.failingMethod).toHaveBeenCalledTimes(1);
    });
  });

  describe('@scenario: SC-05 - Preserving async methods in async wrapper', () => {
    test('should preserve async methods without changes', async () => {
      const asyncClient = {
        fetchData: vi.fn(async () => ({ id: 1, name: 'test' })),
        processData: vi.fn(async (data: any) => ({ ...data, processed: true }))
      };

      const wrappedClient = makeAsyncClient(asyncClient);

      // Should still return Promises
      expect(wrappedClient.fetchData()).toBeInstanceOf(Promise);
      expect(wrappedClient.processData({ id: 1 })).toBeInstanceOf(Promise);

      // Results should match original async behavior
      await expect(wrappedClient.fetchData()).resolves.toEqual({ id: 1, name: 'test' });
      await expect(wrappedClient.processData({ id: 1 })).resolves.toEqual({
        id: 1,
        processed: true
      });

      expect(asyncClient.fetchData).toHaveBeenCalledTimes(1);
      expect(asyncClient.processData).toHaveBeenCalledWith({ id: 1 });
    });

    test('should handle mixed sync and async clients', async () => {
      const mixedClient = {
        syncMethod: vi.fn(() => 'sync-result'),
        asyncMethod: vi.fn(async () => 'async-result'),
        property: 'unchanged',
        nested: {
          syncMethod: vi.fn(() => 'nested-sync')
        }
      };

      const wrappedClient = makeAsyncClient(mixedClient);

      // Sync methods should become async
      await expect(wrappedClient.syncMethod()).resolves.toBe('sync-result');
      await expect(wrappedClient.nested.syncMethod()).resolves.toBe('nested-sync');

      // Async methods should remain async
      await expect(wrappedClient.asyncMethod()).resolves.toBe('async-result');

      // Non-function properties should be unchanged
      expect(wrappedClient.property).toBe('unchanged');

      expect(mixedClient.syncMethod).toHaveBeenCalled();
      expect(mixedClient.asyncMethod).toHaveBeenCalled();
      expect(mixedClient.nested.syncMethod).toHaveBeenCalled();
    });
  });

  describe('@scenario: SC-06 - Scoped async client factory', () => {
    test('should combine scoping with async interface', async () => {
      const mockEnv = createMockEnvironment({ processId: 123, threadId: 0 });
      const init = vi.fn(() => ({
        syncMethod: vi.fn(() => 'data'),
        asyncMethod: vi.fn(async () => 'async-data')
      }));

      const getClient = makeScopedAsyncClient(init);
      const client = getClient();

      // Should initialize only once
      expect(init).toHaveBeenCalledTimes(1);

      // Should provide async interface
      expect(client.syncMethod()).toBeInstanceOf(Promise);
      expect(client.asyncMethod()).toBeInstanceOf(Promise);

      // Should work correctly
      await expect(client.syncMethod()).resolves.toBe('data');
      await expect(client.asyncMethod()).resolves.toBe('async-data');

      mockEnv.restore();
    });

    test('should reuse async client within same scope', async () => {
      const mockEnv = createMockEnvironment({ processId: 123, threadId: 0 });
      const init = vi.fn(() => ({
        method: vi.fn(() => 'data')
      }));

      const getClient = makeScopedAsyncClient(init);
      const client1 = getClient();
      const client2 = getClient();

      expect(init).toHaveBeenCalledTimes(1);
      expect(client1).toBe(client2);

      mockEnv.restore();
    });
  });

  describe('@scenario: SC-07 - Process ID detection', () => {
    test('should return current process ID', () => {
      const originalProcess = globalThis.process;
      (globalThis as any).process = { pid: 999 };

      expect(getCurrentProcessId()).toBe(999);

      (globalThis as any).process = originalProcess;
    });

    test('should return 0 when process unavailable', () => {
      const originalProcess = globalThis.process;
      delete (globalThis as any).process;

      expect(getCurrentProcessId()).toBe(0);

      (globalThis as any).process = originalProcess;
    });

    test('should be consistent across calls', () => {
      const originalProcess = globalThis.process;
      (globalThis as any).process = { pid: 777 };

      expect(getCurrentProcessId()).toBe(777);
      expect(getCurrentProcessId()).toBe(777);
      expect(getCurrentProcessId()).toBe(777);

      (globalThis as any).process = originalProcess;
    });
  });

  describe('@scenario: SC-08 - Thread ID detection in Node.js', () => {
    test('should return worker thread ID', () => {
      const mockEnv = createMockEnvironment({ processId: 123, threadId: 42 });

      expect(getCurrentThreadId()).toBe(42);

      mockEnv.restore();
    });

    test('should return 0 in main thread', () => {
      const mockEnv = createMockEnvironment({ processId: 123, threadId: 0 });

      expect(getCurrentThreadId()).toBe(0);

      mockEnv.restore();
    });
  });

  describe('@scenario: SC-09 - Thread ID detection fallback', () => {
    test('should return 0 when worker_threads not available', () => {
      const mockEnv = createMockEnvironment({
        processId: 123,
        noWorkerThreads: true
      });

      expect(getCurrentThreadId()).toBe(0);

      mockEnv.restore();
    });

    test('should not throw error when worker_threads missing', () => {
      const mockEnv = createMockEnvironment({
        processId: 123,
        noWorkerThreads: true
      });

      expect(() => getCurrentThreadId()).not.toThrow();

      mockEnv.restore();
    });
  });

  describe('@scenario: SC-10 - No top-level side effects', () => {
    test('should not initialize client on module import', () => {
      const init = vi.fn(() => ({ connect: vi.fn() }));

      // Import should not trigger initialization
      expect(init).not.toHaveBeenCalled();

      // Only factory creation should be safe
      const getClient = makeScopedClient(init);
      expect(init).not.toHaveBeenCalled();

      // Only first call should initialize
      getClient();
      expect(init).toHaveBeenCalledTimes(1);
    });

    test('should not establish connections on factory creation', () => {
      const mockConnect = vi.fn();
      const init = vi.fn(() => ({
        connect: mockConnect,
        disconnect: vi.fn()
      }));

      const getClient = makeScopedClient(init);

      // Factory creation shouldn't connect
      expect(mockConnect).not.toHaveBeenCalled();

      // Only first client call should connect
      getClient();
      expect(mockConnect).toHaveBeenCalledTimes(1);
    });
  });

  describe('@scenario: SC-11 - Error handling in client initialization', () => {
    test('should propagate initialization errors', () => {
      const init = vi.fn(() => {
        throw new Error('Database connection failed');
      });

      const getClient = makeScopedClient(init);

      expect(() => getClient()).toThrow('Database connection failed');
      expect(init).toHaveBeenCalledTimes(1);
    });

    test('should attempt reinitialization on subsequent calls after failure', () => {
      let attempts = 0;
      const init = vi.fn(() => {
        attempts++;
        if (attempts < 3) {
          throw new Error(`Initialization attempt ${attempts} failed`);
        }
        return { connect: vi.fn() };
      });

      const getClient = makeScopedClient(init);

      // First two calls should fail
      expect(() => getClient()).toThrow('Initialization attempt 1 failed');
      expect(() => getClient()).toThrow('Initialization attempt 2 failed');

      // Third call should succeed
      expect(() => getClient()).not.toThrow();
      expect(init).toHaveBeenCalledTimes(3);
    });

    test('should succeed after underlying issue is resolved', () => {
      let shouldFail = true;
      const init = vi.fn(() => {
        if (shouldFail) {
          throw new Error('Network unreachable');
        }
        return { connect: vi.fn() };
      });

      const getClient = makeScopedClient(init);

      // First call should fail
      expect(() => getClient()).toThrow('Network unreachable');

      // Simulate network recovery
      shouldFail = false;

      // Second call should succeed
      expect(() => getClient()).not.toThrow();
      expect(init).toHaveBeenCalledTimes(2);
    });
  });
});