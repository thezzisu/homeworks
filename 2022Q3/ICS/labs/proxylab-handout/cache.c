/**
 * ZProxy - a tiny HTTP proxy
 * @file   cache.c
 * @author Zisu Zhang <2100012732@stu.pku.edu.cn>
 * MIT License
 */
#include "cache.h"

#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "csapp.h"

/**
 * get_ticks: get the current ticks. no used in current implementation.
 */
static __always_inline u_int64_t get_ticks() {
  u_int32_t lo, hi;
  asm volatile("rdtsc" : "=a"(lo), "=d"(hi));
  return (u_int64_t)hi << 32 | lo;
}

/**
 * zp_cache_entry_free: free a cache entry
 */
void zp_cache_entry_free(struct zp_cache_entry *entry) {
  free(entry->key);
  free(entry->data);
  free(entry);
}

/**
 * zp_cache_remove: remove a cache entry from the cache
 */
static void zp_cache_remove(struct zp_cache *cache,
                            struct zp_cache_entry *entry) {
  if (entry->prev != NULL) {
    entry->prev->next = entry->next;
  } else {
    cache->head = entry->next;
  }
  if (entry->next != NULL) {
    entry->next->prev = entry->prev;
  } else {
    cache->tail = entry->prev;
  }
}

/**
 * zp_cache_trim: trim the cache to the max size
 */
static void zp_cache_trim(struct zp_cache *cache) {
  if (cache->tail->prev == cache->head) return;
  struct zp_cache_entry *entry = cache->tail->prev;
  zp_cache_remove(cache, entry);
  cache->size -= entry->size;
#ifdef DEBUG
  printf("Trimming cache entry %s\n", entry->key);
#endif
  zp_cache_entry_free(entry);
}

/**
 * zp_cache_init: initialize a cache
 */
void zp_cache_init(struct zp_cache *cache, size_t max_size) {
  Sem_init(&cache->sem, 0, 1);
  cache->head = malloc(sizeof(struct zp_cache_entry));
  cache->head->key = cache->head->data = NULL;
  cache->head->size = 0;
  cache->tail = malloc(sizeof(struct zp_cache_entry));
  cache->tail->key = cache->tail->data = NULL;
  cache->tail->size = 0;
  cache->head->next = cache->head->prev = cache->tail;
  cache->tail->next = cache->tail->prev = cache->head;
  cache->size = 0;
  cache->max_size = max_size;
}

/**
 * zp_cache_free: free a cache
 */
void zp_cache_free(struct zp_cache *cache) {
  struct zp_cache_entry *entry = cache->head->next;
  while (entry != cache->tail) {
    struct zp_cache_entry *next = entry->next;
    zp_cache_entry_free(entry);
    entry = next;
  }
  free(cache->head);
  free(cache->tail);
}

/**
 * zp_cache_put: put a cache entry into the cache
 */
void zp_cache_put(struct zp_cache *cache, const char *key, const char *data,
                  size_t size) {
  V(&cache->sem);
#ifdef DEBUG
  printf("cache %p put %s\n", cache, key);
#endif
  struct zp_cache_entry *entry = malloc(sizeof(struct zp_cache_entry));
  entry->key = strdup(key);
  entry->data = malloc(size);
  memcpy(entry->data, data, size);
  entry->size = size;
  entry->prev = cache->head;
  entry->next = cache->head->next;
  cache->head->next->prev = entry;
  cache->head->next = entry;
  cache->size += size;
  while (cache->size > cache->max_size) {
    zp_cache_trim(cache);
  }
  P(&cache->sem);
}

/**
 * zp_cache_get: get a cache entry from the cache
 */
char *zp_cache_get(struct zp_cache *cache, const char *key, size_t *size) {
  V(&cache->sem);
#ifdef DEBUG
  printf("cache %p get %s\n", cache, key);
#endif
  struct zp_cache_entry *entry = cache->head->next;
  while (entry != cache->tail) {
    if (strcmp(entry->key, key) == 0) {
      zp_cache_remove(cache, entry);
      entry->prev = cache->head;
      entry->next = cache->head->next;
      cache->head->next->prev = entry;
      cache->head->next = entry;
      char *data = malloc(entry->size);
      memcpy(data, entry->data, entry->size);
      *size = entry->size;
      P(&cache->sem);
      return data;
    }
    entry = entry->next;
  }
  P(&cache->sem);
  return NULL;
}