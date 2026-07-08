import { defineConfig } from 'vite';
import { resolve } from 'path';

export default defineConfig({
  base: process.env.BASE_PATH || '/',
  server: {
    port: 3000,
    proxy: {
      '/api': {
        target: 'http://localhost:5001',
        changeOrigin: true
      }
    }
  },
  build: {
    rollupOptions: {
      input: {
        index2: resolve(__dirname, 'index2.html')
      }
    }
  }
});
