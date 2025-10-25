/**
 * Health Check Routes
 *
 * Basic health monitoring endpoints following Teja Pattern principles.
 * These routes provide system status information without exposing
 * sensitive implementation details.
 */

import { Elysia, t } from 'elysia';

export const healthRoutes = new Elysia({ prefix: '/health' })
  .get('/', () => ({
    status: 'healthy',
    timestamp: new Date().toISOString(),
    version: '0.1.0'
  }))
  .get('/ready', () => ({
    status: 'ready',
    timestamp: new Date().toISOString(),
    services: {
      // Will check actual service health when adapters are implemented
      database: 'checking',
      cache: 'checking',
      queue: 'checking'
    }
  }))
  .get('/live', () => ({
    status: 'alive',
    timestamp: new Date().toISOString()
  }));