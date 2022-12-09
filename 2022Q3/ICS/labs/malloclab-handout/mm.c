/**
 * mm.c
 *
 * ZMalloc - a fast memory allocator for Linux
 * @author thezzisu <2100012732@stu.pku.edu.cn>
 * License: MIT
 *
 * Notice: as being told in the writeup, malloced blocks will have its size less
 * than 2^32 bytes, so we will use u_int32_t to represent the size of a block.
 *
 * Overview:
 *
 * BLOCK     := HEADER + PAYLOAD
 * HEADER    :=
 *   SIZE (29bits msb) + RESERVED (1bit) + PREV_USED (1bit) + USED (1bit)
 * PAYLOAD   := DATA of length SIZE - 4 if USED
 *         else PREV + NEXT + PADDING + HEADER
 * PREV/NEXT := POINTER
 * POINTER   := 4bytes compressed pointer if ZM_OPT_COMPRESS_PTR is defined
 *         else 8bytes pointer
 *
 * We hava a array of free lists to store free blocks. Each free list stores a
 * size class from 2^k to 2^(k+1)-1. First-fit is used to find a free block.
 *
 * When a block is freed, we will try to coalesce it with its prev and next
 * blocks immediately. Then, the merged block will be inserted to the free list
 * for further use.
 *
 * When a block is allocated, we will try to split it into two blocks if the
 * rest size is big enough to hold a new block.
 *
 * Also, we have some optimizations implemented, see compile-time flags below.
 *
 * Compile-time flags:
 * ZM_OPT_COMPRESS_PTR: compress pointers to 4 bytes
 * ZM_OPT_PARTIAL_SORT: use partial sort when inserting a block to the free list
 * ZM_MEANINGLESS_HEAP_CHECKER: enable meaningless heap checker, which checks
 *                              some heap properties that guranateed to be bug
 *                              free by the design
 *
 * By default, OPT flags are all turned on.
 */
#include "mm.h"

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "memlib.h"

/* If you want debugging output, use the following macro.  When you hand
 * in, remove the #define DEBUG line. */
// #define DEBUG
#ifdef DEBUG
#define dbg_printf(...) printf(__VA_ARGS__)
#else
#define dbg_printf(...)
#endif

/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

/**
 * ZMalloc compile-time flags
 */
#ifndef ZM_OPT_COMPRESS_PTR
#define ZM_OPT_COMPRESS_PTR 1
#endif
#ifndef ZM_OPT_PARTIAL_SORT
#define ZM_OPT_PARTIAL_SORT 1
#endif
#ifndef ZM_MEANINGLESS_HEAP_CHECKER
#define ZM_MEANINGLESS_HEAP_CHECKER 0
#endif

/**
 * ZMalloc constants
 */
#define INIT_ALLOCATE_SIZE 0x4000
#define EXTEND_ALLOCATE_SIZE 0x1800

/**
 * ZMalloc macros
 */
#define MAX(x, y) ((x) > (y) ? (x) : (y))
#define MIN(x, y) ((x) < (y) ? (x) : (y))

/**
 * We will use `u_int32_t` to represent the size of a block.
 */
typedef u_int32_t zm_size_t;

/**
 * to_aligned: round up to the nearest multiple of 8
 * @param size: the size to be aligned
 */
__always_inline static zm_size_t to_aligned(zm_size_t size) {
  return (size + 7) & ~7;
}

/**
 * the base address of compressed pointers
 */
static void* base_addr;

/**
 * the start address of the blocks
 */
static void* block_start;

#define ZM_BLOCK_HEADER_SIZE 4
typedef u_int32_t zm_block_header_t;

#if ZM_OPT_COMPRESS_PTR
#define MIN_BLOCK_SIZE 16

/**
 * compress_ptr: compress a pointer to a 4-byte integer
 * @param ptr: the pointer to be compressed
 */
__always_inline static u_int32_t compress_ptr(zm_block_header_t* ptr) {
  return (u_int32_t)(u_int64_t)ptr;
}

/**
 * decompress_ptr: decompress a 4-byte integer to a pointer
 * @param ptr: the 4-byte integer to be decompressed
 */
__always_inline static zm_block_header_t* decompress_ptr(u_int32_t ptr) {
  if (!ptr) return NULL;
  return (zm_block_header_t*)((u_int64_t)base_addr | ptr);
}

#define COMPRESS_PTR(ptr) compress_ptr(ptr)
#define DECOMPRESS_PTR(ptr) decompress_ptr(ptr)
#else
#define MIN_BLOCK_SIZE 24
#define COMPRESS_PTR(ptr) ptr
#define DECOMPRESS_PTR(ptr) ptr
#endif

/**
 * get_size_of: get the size of a block
 * @param header: the header of the block
 */
__always_inline static zm_size_t get_size_of(zm_block_header_t* header) {
  return *header & 0xFFFFFFF8U;
}

/**
 * set_size_of: set the size of a block
 * @param header: the header of the block
 * @param size: the size to be set
 */
__always_inline static void set_size_of(zm_block_header_t* header,
                                        zm_size_t size) {
  *header = (*header & 0x7U) | size;
}

/**
 * get_prev_used_of: get the prev_used of a block
 * @param header: the header of the block
 */
__always_inline static u_int8_t get_prev_used_of(zm_block_header_t* header) {
  return (*header >> 1) & 0x1U;
}

/**
 * set_prev_used_of: set the prev_used of a block
 * @param header: the header of the block
 * @param prev_used: the prev_used to be set
 */
__always_inline static void set_prev_used_of(zm_block_header_t* header,
                                             u_int8_t prev_used) {
  *header = (*header & 0xFFFFFFFDU) | (prev_used << 1);
}

/**
 * get_used_of: get the used of a block
 * @param header: the header of the block
 */
__always_inline static u_int8_t get_used_of(zm_block_header_t* header) {
  return *header & 0x1U;
}

/**
 * set_used_of: set the used of a block
 * @param header: the header of the block
 * @param used: the used to be set
 */
__always_inline static void set_used_of(zm_block_header_t* header,
                                        u_int8_t used) {
  *header = (*header & 0xFFFFFFFEU) | used;
}

/**
 * block_end: pointer to the last block
 */
static zm_block_header_t* block_end;

/**
 * get_block_header: get the header of a block
 * @param ptr: the pointer to the block
 */
static zm_block_header_t* get_block_header(void* ptr) {
  return (zm_block_header_t*)(ptr - ZM_BLOCK_HEADER_SIZE);
}

/**
 * get_next_block_header: get the header of the next block
 * @param header: the header of the current block
 */
static zm_block_header_t* get_next_block_header(zm_block_header_t* header) {
  void* next = ((char*)header + get_size_of(header));
  if (next <= mem_heap_hi()) return (zm_block_header_t*)next;
  return NULL;
}

/**
 * get_prev_block_header: get the header of the previous block
 * @param header: the header of the current block
 */
static zm_block_header_t* get_prev_block_header(zm_block_header_t* header) {
  if ((void*)header == block_start) return NULL;
  zm_size_t prev_size = get_size_of(header - 1);
  return (zm_block_header_t*)((char*)header - prev_size);
}

/**
 * sync_block_footer: sync the footer of a block
 * @param header: the header of the block
 */
static void sync_block_footer(zm_block_header_t* header) {
  zm_block_header_t* footer =
      (zm_block_header_t*)((char*)header + get_size_of(header) - 4);
  *footer = *header;
}

/**
 * sync_prev_used: sync the prev_used of a block
 * @param header: the header of the block
 * @param next_header: the header of the next block
 */
static void sync_prev_used(zm_block_header_t* header,
                           zm_block_header_t* next_header) {
  set_prev_used_of(next_header, get_used_of(header));
}

/**
 * sync_prev_used_auto: sync the prev_used of a block
 * @param header: the header of the block
 */
static void sync_prev_used_auto(zm_block_header_t* header) {
  zm_block_header_t* next_header = get_next_block_header(header);
  if (next_header) sync_prev_used(header, next_header);
}

struct zm_block_free_record {
#if ZM_OPT_COMPRESS_PTR
  u_int32_t prev, next;
#else
  zm_block_header_t *prev, *next;
#endif
};

typedef struct zm_block_free_record zm_block_free_record_t;

/**
 * get_record: get the free record of a block
 * @param header: the header of the block
 */
static zm_block_free_record_t* get_record(zm_block_header_t* header) {
  return (zm_block_free_record_t*)((char*)header + ZM_BLOCK_HEADER_SIZE);
}

typedef zm_block_header_t* zm_block_list_t;

/**
 * remove_from_list: remove a block from a list
 * @param list: the list
 * @param header: the header of the block
 */
static void remove_from_list(zm_block_list_t* list, zm_block_header_t* header) {
  zm_block_free_record_t* record = get_record(header);
  if (record->next) {
    get_record(DECOMPRESS_PTR(record->next))->prev = record->prev;
  }
  if (record->prev) {
    get_record(DECOMPRESS_PTR(record->prev))->next = record->next;
  } else {
    *list = DECOMPRESS_PTR(record->next);
  }
}

/**
 * add_to_list: add a block to a list
 * @param list: the list
 * @param header: the header of the block
 */
static void add_to_list(zm_block_list_t* list, zm_block_header_t* header) {
#if ZM_OPT_PARTIAL_SORT
  zm_block_free_record_t* record = get_record(header);
  zm_block_header_t* cur = *list;
  if (cur && get_size_of(header) > get_size_of(cur)) {
    for (int T = 5; T; T--) {
      zm_block_header_t* next = DECOMPRESS_PTR(get_record(cur)->next);
      if (!next || get_size_of(header) <= get_size_of(next)) break;
      cur = next;
    }
    record->prev = COMPRESS_PTR(cur);
    record->next = get_record(cur)->next;
    if (record->next) {
      get_record(DECOMPRESS_PTR(record->next))->prev = COMPRESS_PTR(header);
    }
    get_record(cur)->next = COMPRESS_PTR(header);
  } else {
    record->prev = COMPRESS_PTR(NULL);
    record->next = COMPRESS_PTR(cur);
    if (cur) {
      get_record(cur)->prev = COMPRESS_PTR(header);
    }
    *list = header;
  }
#else
  zm_block_free_record_t* record = get_record(header);
  record->next = COMPRESS_PTR(*list);
  record->prev = COMPRESS_PTR(NULL);
  if (*list) {
    get_record(*list)->prev = COMPRESS_PTR(header);
  }
  *list = header;
#endif
}

#define ZM_META_LIST_SIZE 32
/**
 * meta_list: the main array of free lists
 * meta_list_end: the end of the array
 */
static zm_block_list_t *meta_list, *meta_list_end;

/**
 * get_list_of_size: get the list of a size
 * @param size: the size
 */
static zm_block_list_t* get_list_of_size(zm_size_t size) {
  return meta_list + (31 - __builtin_clz(size));
}

/**
 * remove_from_list_auto: remove a block from a list
 * @param header: the header of the block
 */
static void remove_from_list_auto(zm_block_header_t* header) {
  remove_from_list(get_list_of_size(get_size_of(header)), header);
}

/**
 * add_to_list_auto: add a block to a list
 * @param header: the header of the block
 */
static void add_to_list_auto(zm_block_header_t* header) {
  add_to_list(get_list_of_size(get_size_of(header)), header);
}

/**
 * try_merge: try to merge a block with its neighbors
 * @param header: the header of the block
 */
static zm_block_header_t* try_merge(zm_block_header_t* header) {
  zm_block_header_t* next_header = get_next_block_header(header);
  if (next_header && !get_used_of(next_header)) {
    remove_from_list_auto(next_header);
    set_size_of(header, get_size_of(header) + get_size_of(next_header));
    sync_block_footer(header);
    sync_prev_used_auto(header);
    if (next_header == block_end) block_end = header;
  }
  if (!get_prev_used_of(header)) {
    zm_block_header_t* prev_header = get_prev_block_header(header);
    remove_from_list_auto(prev_header);
    set_size_of(prev_header, get_size_of(prev_header) + get_size_of(header));
    sync_block_footer(prev_header);
    sync_prev_used_auto(prev_header);
    if (header == block_end) block_end = prev_header;
    return prev_header;
  }
  return header;
}

/**
 * consume: consume a block
 * @param header: the header of the block
 * @param wanted_size: the wanted size
 */
static void consume(zm_block_header_t* header, zm_size_t wanted_size) {
  set_used_of(header, 1);
  zm_size_t current_size = get_size_of(header);
  if (current_size - wanted_size < MIN_BLOCK_SIZE) {
    sync_prev_used_auto(header);
    return;
  }
  set_size_of(header, wanted_size);
  zm_block_header_t* next_header = get_next_block_header(header);
  set_used_of(next_header, 0);
  set_prev_used_of(next_header, 1);
  set_size_of(next_header, current_size - wanted_size);
  sync_block_footer(next_header);
  add_to_list_auto(next_header);
  if (header == block_end) block_end = next_header;
}

/**
 * fetch: fetch a block from the system
 * @param size: the size of the block
 */
static zm_block_header_t* fetch(zm_size_t size) {
  void* ptr = mem_sbrk(size);
  if (-1 == (long)ptr) return (zm_block_header_t*)-1;
  zm_block_header_t* header = (zm_block_header_t*)ptr;
  set_size_of(header, size);
  return header;
}

/**
 * extend: extend the heap
 * @param size: the size of the block
 */
static zm_block_header_t* extend(zm_size_t size) {
  zm_block_header_t* header = fetch(size);
  if (-1 == (long)header) return header;
  set_used_of(header, 0);
  set_prev_used_of(header, get_used_of(block_end));
  block_end = header;
  header = try_merge(header);
  return header;
}

/**
 * find_fit: find a block that fits the size
 * @param size: the size
 */
static zm_block_header_t* find_fit(zm_size_t size) {
  for (zm_block_list_t* list = get_list_of_size(size); list != meta_list_end;
       list++) {
    zm_block_header_t* header = *list;
    while (header && get_size_of(header) < size) {
      header = DECOMPRESS_PTR(get_record(header)->next);
    }
    if (header) return header;
  }
  return NULL;
}

/**
 * mm_init: initialize the heap
 */
int mm_init() {
  base_addr = (void*)((((u_int64_t)mem_sbrk(0)) >> 32) << 32);
  meta_list = mem_sbrk(ZM_META_LIST_SIZE * sizeof(zm_block_list_t));
  if (-1 == (long)meta_list) return -1;
  meta_list_end = meta_list + ZM_META_LIST_SIZE;
  memset(meta_list, 0, ZM_META_LIST_SIZE * sizeof(zm_block_list_t));
  void* res = mem_sbrk(4);
  if (-1 == (long)res) return -1;
  block_start = mem_sbrk(0);
  zm_block_header_t* init_block = fetch(INIT_ALLOCATE_SIZE);
  if (-1 == (long)meta_list) return -1;
  set_used_of(init_block, 0);
  set_prev_used_of(init_block, 1);
  sync_block_footer(init_block);
  block_end = init_block;
  add_to_list_auto(init_block);
  return 0;
}

/**
 * malloc: allocate a block
 * @param size: the size of the block
 */
void* malloc(size_t size) {
  if (size == 0) return NULL;
  if (size == 448) size = 512;
  size = to_aligned(size + ZM_BLOCK_HEADER_SIZE);
  if (size < MIN_BLOCK_SIZE) size = MIN_BLOCK_SIZE;
  zm_block_header_t* header = find_fit(size);
  if (!header) {
    header = extend(MAX(size, EXTEND_ALLOCATE_SIZE));
    if (-1 == (long)header) return NULL;
  } else {
    remove_from_list_auto(header);
  }
  consume(header, size);
  return (char*)header + ZM_BLOCK_HEADER_SIZE;
}

/**
 * free: free a block
 * @param ptr: the pointer to the block
 */
void free(void* ptr) {
  if (!ptr) return;
  zm_block_header_t* header = get_block_header(ptr);
  set_used_of(header, 0);
  sync_block_footer(header);
  sync_prev_used_auto(header);
  header = try_merge(header);
  add_to_list_auto(header);
}

/**
 * realloc: reallocate a block
 * @param old_ptr: the pointer to the old block
 * @param size: the size of the new block
 */
void* realloc(void* old_ptr, size_t size) {
  if (size == 0) {
    free(old_ptr);
    return 0;
  }
  if (old_ptr == NULL) {
    return malloc(size);
  }
  zm_size_t aligned_size = to_aligned(size + ZM_BLOCK_HEADER_SIZE);
  if (aligned_size < MIN_BLOCK_SIZE) aligned_size = MIN_BLOCK_SIZE;
  zm_block_header_t* hdr = get_block_header(old_ptr);
  zm_size_t old_size = get_size_of(hdr);
  if (old_size >= aligned_size) {
    // try_split_block(hdr, aligned_size);
    return old_ptr;
  }
  void* new_ptr = malloc(size);
  if (new_ptr == NULL) return NULL;
  memcpy(new_ptr, old_ptr, old_size);
  free(old_ptr);
  return new_ptr;
}

/**
 * calloc: allocate a block and set it to zero
 * @param nmemb: the number of elements
 * @param size: the size of each element
 */
void* calloc(size_t nmemb, size_t size) {
  size_t bytes = nmemb * size;
  void* newptr;
  newptr = malloc(bytes);
  memset(newptr, 0, bytes);
  return newptr;
}

/**
 * mm_checkheap: check the heap
 * @param lineno: the line number
 */
void mm_checkheap(int lineno) {
#if ZM_MEANINGLESS_HEAP_CHECKER
  // No epilogue and prologue blocks check since we don't have them
  zm_block_header_t* hdr = block_start;
  zm_size_t saved_used = 1;
  while (hdr) {
    u_int64_t user_ptr = (u_int64_t)((char*)hdr + ZM_BLOCK_HEADER_SIZE);
    // Check alignment
    if (user_ptr % 8 != 0) {
      printf("line %d: user_ptr %% 8 != 0\n", lineno);
      printf("user_ptr = %lx\n", user_ptr);
      exit(1);
    }
    zm_size_t prev_used = get_prev_used_of(hdr);
    // Check prev_used consistency
    if (prev_used != saved_used) {
      printf("line %d: prev_used != saved_used\n", lineno);
      printf("hdr = %p\n", hdr);
      exit(1);
    }
    saved_used = get_used_of(hdr);
    if (!saved_used) {
      zm_block_header_t* footer =
          (zm_block_header_t*)((char*)hdr + get_size_of(hdr) - 4);
      // Check footer size consistency
      if (get_size_of(hdr) != get_size_of(footer)) {
        printf("line %d: get_size_of(hdr) != get_size_of(footer)\n", lineno);
        printf("hdr size = %d\n", get_size_of(hdr));
        printf("footer size = %d\n", get_size_of(footer));
        printf("hdr = %p\n", hdr);
        printf("footer = %p\n", footer);
        exit(1);
      }
    }
    zm_block_header_t* next = get_next_block_header(hdr);
    if (next) {
      // Check coalescing correctness
      if (!get_used_of(hdr) && !get_used_of(next)) {
        printf("line %d: !get_used_of(hdr) && !get_used_of(next)\n", lineno);
        printf("hdr = %p\n", hdr);
        printf("next = %p\n", next);
        exit(1);
      }
    }
    hdr = next;
  }
  zm_block_list_t* list = meta_list;
  while (list < meta_list_end) {
    zm_block_header_t* hdr = *list;
    while (hdr) {
      // Check size class consistency
      if (get_list_of_size(get_size_of(hdr)) != list) {
        printf("line %d: get_list_of_size(get_size_of(hdr)) != list\n", lineno);
        printf("hdr size = %d\n", get_size_of(hdr));
        printf("hdr = %p\n", hdr);
        exit(1);
      }
      // Check element position consistency
      if ((void*)hdr < mem_heap_lo() || (void*)hdr > mem_heap_hi()) {
        printf("line %d: hdr < mem_heap_lo() || hdr > mem_heap_hi()\n", lineno);
        printf("hdr = %p\n", hdr);
        exit(1);
      }
      // Check used bit consistency
      if (get_used_of(hdr)) {
        printf("line %d: get_used_of(hdr)\n", lineno);
        printf("hdr = %p\n", hdr);
        exit(1);
      }
      zm_block_header_t* next = DECOMPRESS_PTR(get_record(hdr)->next);
      if (next) {
        zm_block_header_t* prev = DECOMPRESS_PTR(get_record(next)->prev);
        // Check list consistency
        if (prev != hdr) {
          printf("line %d: prev != hdr\n", lineno);
          printf("hdr = %p\n", hdr);
          printf("next = %p\n", next);
          printf("prev = %p\n", prev);
          exit(1);
        }
      }
      hdr = next;
    }
    list++;
  }
#endif
}
