/**
 * csim.c - Simulator for the Cache Lab
 *
 * See Cache Lab Writeup for more details.
 *
 * Zisu Zhang
 * 2100012732
 * MIT License
 */
#include <ctype.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

#include "cachelab.h"

/**
 * Print usage information.
 * Strings are extracted from csim-ref binary
 */
void print_usage(char **argv) {
  printf("Usage: %s [-hv] -s <num> -E <num> -b <num> -t <file>\n", argv[0]);
  puts("Options:");
  puts("  -h         Print this help message.");
  puts("  -v         Optional verbose flag.");
  puts("  -s <num>   Number of set index bits.");
  puts("  -E <num>   Number of lines per set.");
  puts("  -b <num>   Number of block offset bits.");
  puts("  -t <file>  Trace file.");
  puts("");
  puts("Examples:");
  printf("  linux>  %s -s 4 -E 1 -b 4 -t traces/yi.trace\n", argv[0]);
  printf("  linux>  %s -v -s 8 -E 2 -b 4 -t traces/yi.trace\n", argv[0]);
}

void panic(char *reason) {
  puts(reason);
  exit(1);
}

/**
 * The result struct is used to store the results of a cache simulation.
 */
typedef struct result {
  int hit;
  int miss;
  int eviction;
} result;

/** Init a result struct */
result *init_result() {
  result *r = (result *)malloc(sizeof(result));
  if (r == NULL) panic("malloc failed");
  r->hit = r->miss = r->eviction = 0;
  return r;
}

/** Free a result struct */
void free_result(result *r) { free(r); }

/**
 * A cache line
 * The valid bit is used to indicate whether the line is valid (used),
 * and the tag is used to store the tag of the line.
 * The lat (last accessed at) field stores the last time when the line accessed.
 */
typedef struct cache_line {
  int valid;
  int lat;
  unsigned long long tag;
} cache_line;

/**
 * A cache set
 * The lines field is allocated dynamically at init according to E.
 */
typedef struct cache_set {
  cache_line *lines;
} cache_set;

/**
 * A cache
 * The sets field is allocated dynamically at init according to s.
 */
typedef struct cache {
  int s;
  int E;
  int b;
  cache_set *sets;
} cache;

cache *init_cache(int s, int E, int b) {
  cache *c = malloc(sizeof(cache));
  if (c == NULL) panic("malloc failed");
  c->s = s;
  c->E = E;
  c->b = b;
  c->sets = malloc(sizeof(cache_set) * (1 << s));
  if (c->sets == NULL) panic("malloc failed");
  for (int i = 0; i < (1 << s); i++) {
    c->sets[i].lines = malloc(sizeof(cache_line) * E);
    if (c->sets[i].lines == NULL) panic("malloc failed");
    for (int j = 0; j < E; j++) {
      c->sets[i].lines[j].valid = 0;
      c->sets[i].lines[j].tag = 0;
      c->sets[i].lines[j].lat = 0;
    }
  }
  return c;
}

void free_cache(cache *c) {
  for (int i = 0; i < (1 << c->s); i++) {
    free(c->sets[i].lines);
  }
  free(c->sets);
  free(c);
}

/**
 * Simulate one access to the cache.
 * Apart from the verbose output of the reference binary, we also print the
 * corresponding set and tag of each access for debug purpose.
 */
void access_cache(cache *c, unsigned long long addr, int clock, result *r,
                  int verbose) {
  unsigned tag = addr >> (c->s + c->b);
  unsigned set = (addr >> c->b) & ((1 << c->s) - 1);
  if (verbose) printf("set: %x, tag: %x ", set, tag);
  cache_line *lines = c->sets[set].lines;
  int min_lat_index = 0;
  for (int i = 0; i < c->E; i++) {
    if (lines[i].valid == 0) {
      lines[i].valid = 1;
      lines[i].tag = tag;
      lines[i].lat = clock;
      r->miss++;
      if (verbose) printf("miss ");
      return;
    }
    if (lines[i].tag == tag) {
      lines[i].lat = clock;
      r->hit++;
      if (verbose) printf("hit ");
      return;
    }
    if (lines[i].lat < lines[min_lat_index].lat) {
      min_lat_index = i;
    }
  }
  lines[min_lat_index].tag = tag;
  lines[min_lat_index].lat = clock;
  r->miss++;
  r->eviction++;
  if (verbose) printf("miss eviction ");
}

char buf[128];

/**
 * Simulate the whole cache according to the trace file.
 * A global clock is used to implement and simulate the LRU policy.
 */
void simulate(int s, int E, int b, char *trace_file, int verbose) {
  FILE *fp = fopen(trace_file, "r");
  cache *c = init_cache(s, E, b);
  result *r = init_result();
  int clock = 0;
  unsigned long long addr;
  while (fgets(buf, 128, fp) != NULL) {
    if (buf[0] == 'I') continue;
    sscanf(buf + 3, "%llx", &addr);
    if (verbose) printf("%c %llx,%d ", buf[1], addr, 1 << b);
    access_cache(c, addr, ++clock, r, verbose);
    if (buf[1] == 'M') {
      access_cache(c, addr, ++clock, r, verbose);
    }
    if (verbose) printf("\n");
  }
  printSummary(r->hit, r->miss, r->eviction);
  free_cache(c);
  free_result(r);
  fclose(fp);
}

/**
 * The main function
 */
int main(int argc, char **argv) {
  int flag_v = 0;           // Flags
  int arg_s, arg_E, arg_b;  // Arguments
  char *arg_file = NULL;
  char c;
  arg_s = arg_E = arg_b = 0;

  while ((c = getopt(argc, argv, "vs:E:b:t:")) != -1) {
    switch (c) {
      case 'v':
        flag_v = 1;
        break;
      case 's':
        arg_s = atoi(optarg);
        break;
      case 'E':
        arg_E = atoi(optarg);
        break;
      case 'b':
        arg_b = atoi(optarg);
        break;
      case 't':
        arg_file = optarg;
        break;
      default:
        print_usage(argv);
        return 0;
    }
  }
  if (arg_file == NULL || !arg_s || !arg_E || !arg_b) {
    printf("%s: Missing required command line argument\n", argv[0]);
    print_usage(argv);
    return 0;
  }
  simulate(arg_s, arg_E, arg_b, arg_file, flag_v);
  return 0;
}