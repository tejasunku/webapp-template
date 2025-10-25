/**
 * ElysiaJS Application Entry Point
 *
 * This is the main entry point for the ElysiaJS API service.
 * It follows the Teja Pattern with clear separation between:
 * - app/: Application orchestration and routing
 * - domain/: Pure business logic and invariants
 * - sdk/: External service adapters
 * - tests/: Comprehensive test suite
 */

import { Elysia, t } from 'elysia';
import { cors } from '@elysiajs/cors';

// Import routes
import { healthRoutes } from './app/routes/health';

const app = new Elysia({ prefix: '/api/v1' })
  .use(cors())
  .get('/', () => ({
    message: 'Teja Pattern Web App Template',
    version: '0.1.0',
    status: 'healthy'
  }))
  .use(healthRoutes)
  .listen(process.env.PORT || 3000);

console.log(`🚀 ElysiaJS server running at http://localhost:${app.server?.port}`);

export default app;