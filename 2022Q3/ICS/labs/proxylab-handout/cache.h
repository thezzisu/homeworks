/**
 * ZProxy - a tiny HTTP proxy
 * @file   cache.h
 * @author Zisu Zhang <2100012732@stu.pku.edu.cn>
 * MIT License
 */
#ifndef ZP_CACHE_H
#define ZP_CACHE_H

#include <semaphore.h>
#include <stdlib.h>

struct zp_cache_entry {
  char *key;
  char *data;
  u_int64_t lat, size;
  struct zp_cache_entry *prev, *next;
};

void zp_cache_entry_free(struct zp_cache_entry *entry);

struct zp_cache {
  struct zp_cache_entry *head;
  struct zp_cache_entry *tail;
  u_int64_t size, max_size;
  sem_t sem;
};

void zp_cache_init(struct zp_cache *cache, u_int64_t max_size);
void zp_cache_free(struct zp_cache *cache);
void zp_cache_put(struct zp_cache *cache, const char *key, const char *data,
                  size_t size);
char *zp_cache_get(struct zp_cache *cache, const char *key, size_t *size);

#endif