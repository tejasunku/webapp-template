@feature: Shared Adapter Factory Pattern
  @id: F-001
  To ensure thread-safe and async external service communication
  As a developer using Teja Pattern
  I want a client factory that manages process/thread scoped connections
  And provides guaranteed async interfaces

  Background:
    Given a shared adapter factory is imported from "shared/utils/clientFactory"
    And external service clients may have state or connection requirements
    And the application may run in multi-process or multi-threaded environments

  @scenario: SC-01
  Scenario: Client isolation across different processes
    Given a client factory is created with makeScopedClient()
    When the factory is called in process with ID 123
    Then it should initialize and return a client instance
    When the factory is called in process with ID 124 (different process)
    Then it should re-initialize and return a new client instance
    And the two client instances should be independent

  @scenario: SC-02
  Scenario: Client isolation across different threads
    Given a client factory is created with makeScopedClient()
    When the factory is called in thread with ID 0
    Then it should initialize and return a client instance
    When the factory is called in thread with ID 1 (different thread)
    Then it should re-initialize and return a new client instance
    And the two client instances should be independent

  @scenario: SC-03
  Scenario: Client reuse within same process and thread
    Given a client factory is created with makeScopedClient()
    When the factory is called multiple times in the same process/thread
    Then it should return the same client instance on subsequent calls
    And client initialization should only happen once

  @scenario: SC-04
  Scenario: Async interface for synchronous client methods
    Given a client with synchronous methods
    When wrapped with makeAsyncClient()
    Then all methods should return Promises
    When a synchronous method returns a value
    Then the async wrapper should resolve with the same value
    When a synchronous method throws an error
    Then the async wrapper should reject with the same error

  @scenario: SC-05
  Scenario: Preserving async methods in async wrapper
    Given a client with both sync and async methods
    When wrapped with makeAsyncClient()
    Then async methods should remain async
    And sync methods should become async
    And method signatures should be preserved

  @scenario: SC-06
  Scenario: Scoped async client factory
    Given a client factory is created with makeScopedAsyncClient()
    When the factory is called
    Then it should return a client with async interface
    And the client should be scoped to current process/thread
    And initialization should happen only once per process/thread

  @scenario: SC-07
  Scenario: Process ID detection
    When getCurrentProcessId() is called
    Then it should return the current process ID
    And the value should be consistent across calls in the same process

  @scenario: SC-08
  Scenario: Thread ID detection in Node.js
    When getCurrentThreadId() is called in Node.js worker thread
    Then it should return the worker thread ID
    And the value should be 0 in the main thread

  @scenario: SC-09
  Scenario: Thread ID detection fallback
    When getCurrentThreadId() is called without worker_threads support
    Then it should return 0 as fallback
    And should not throw an error

  @scenario: SC-10
  Scenario: No top-level side effects
    Given a client factory is imported
    When the module is loaded
    Then no external clients should be initialized
    And no network connections should be established
    And client initialization should only happen on first factory call

  @scenario: SC-11
  Scenario: Error handling in client initialization
    Given a client factory with failing initialization
    When the factory is called for the first time
    Then the initialization error should be propagated
    When the factory is called again in the same process/thread
    Then it should attempt re-initialization
    And should succeed if the underlying issue is resolved

  Examples of client factory usage:

  Scenario: Database adapter implementation
    Given a database client factory
    When multiple services need database access
    Then each service should get its own process-scoped client
    And client connections should be managed automatically
    And all database operations should be async

  Scenario: Cache adapter implementation
    Given a Redis client factory
    When multiple processes need cache access
    Then each process should get its own Redis client
    And cache operations should be thread-safe
    And get/set operations should return Promises

  Scenario: External API adapter implementation
    Given an HTTP client factory for external API
    When making API calls from different threads
    Then each thread should have its own client instance
    And rate limiting should be handled correctly
    And all API responses should be Promises