/**
 * Shared Adapter Protocol (SAP) - Client Factory
 *
 * Backend-agnostic client factory that ensures thread safety and async interface.
 * Handles process forking and thread changes by re-initializing clients.
 */

export function makeScopedClient<T>(init: () => T): () => T {
  let pid = -1;
  let tid = -1;
  let client: T | null = null;

  return () => {
    // Get current process ID
    const newPid = typeof process !== 'undefined' ? process.pid : 0;

    // Get current thread ID (works in Node.js, Bun, browsers)
    let newTid = 0;
    try {
      // Try Node.js worker_threads first
      const workerThreads = require('worker_threads');
      newTid = workerThreads.threadId ?? 0;
    } catch {
      // Fallback: try other thread detection methods
      if (typeof globalThis !== 'undefined' && 'workerId' in globalThis) {
        newTid = (globalThis as any).workerId;
      }
    }

    // Re-initialize client if process/thread changed
    if (!client || newPid !== pid || newTid !== tid) {
      pid = newPid;
      tid = newTid;
      client = init();
    }

    return client;
  };
}

/**
 * Ensures async interface for any client method calls
 * Wraps sync methods to be async, leaves async methods untouched
 */
export function makeAsyncClient<T extends Record<string, any>>(client: T): T {
  const asyncClient = {} as T;

  for (const [key, value] of Object.entries(client)) {
    if (typeof value === 'function') {
      asyncClient[key as keyof T] = async (...args: any[]) => {
        const result = value.apply(client, args);
        // If result is already a Promise, return it
        // Otherwise, wrap the sync result in a resolved Promise
        return result instanceof Promise ? result : Promise.resolve(result);
      } as any;
    } else {
      asyncClient[key as keyof T] = value;
    }
  }

  return asyncClient;
}

/**
 * Creates a scoped client with guaranteed async interface
 */
export function makeScopedAsyncClient<T>(init: () => T): () => T {
  const scopedClient = makeScopedClient(init);

  return () => {
    const client = scopedClient();
    return makeAsyncClient(client);
  };
}

/**
 * Process ID detection utility
 */
export function getCurrentProcessId(): number {
  return typeof process !== 'undefined' ? process.pid : 0;
}

/**
 * Thread ID detection utility (backend-agnostic)
 */
export function getCurrentThreadId(): number {
  try {
    const workerThreads = require('worker_threads');
    return workerThreads.threadId ?? 0;
  } catch {
    // No worker threads available or not in a worker
    return 0;
  }
}