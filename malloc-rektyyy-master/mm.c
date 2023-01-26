#include <assert.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <stddef.h>
#include <unistd.h>

#include "mm.h"
#include "memlib.h"

/* If you want debugging output, use the following macro.
 * When you hand in, remove the #define DEBUG line. */
#define DEBUG 0
#define DEBUG_REALLOC 0
#ifdef DEBUG
#define debug(fmt, ...) printf("%s: " fmt "\n", __func__, __VA_ARGS__)
#define msg(...) printf(__VA_ARGS__)
#else
#define debug(fmt, ...)
#define msg(...)
#endif

#define __unused __attribute__((unused))

/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* !DRIVER */

typedef int32_t word_t; /* Heap is bascially an array of 4-byte words. */

typedef enum {
  FREE = 0,     /* Block is free */
  USED = 1,     /* Block is used */
  PREVFREE = 2, /* Previous block is free (optimized boundary tags) */
} bt_flags;

static word_t *heap_start; /* Address of the first block */
static word_t *heap_end;   /* Address past last byte of last block */
static word_t *last;       /* Points at last block */
static word_t *list_start; /* Address of first free block*/
static word_t *list_end;   /* Address of last free block*/

/* --=[ boundary tag handling ]=-------------------------------------------- */

static inline word_t bt_size(word_t *bt) {
  return *bt & ~(USED | PREVFREE);
}

static inline int bt_used(word_t *bt) {
  return *bt & USED;
}

static inline int bt_free(word_t *bt) {
  return !(*bt & USED);
}

/* Given boundary tag address calculate it's buddy address. */
static inline word_t *bt_footer(word_t *bt) {
  return (void *)bt + bt_size(bt) - sizeof(word_t);
}

/* Given payload pointer returns an address of boundary tag. */
static inline word_t *bt_fromptr(void *ptr) {
  return (word_t *)ptr - 1;
}

/* Previous block free flag handling for optimized boundary tags. */
static inline bt_flags bt_get_prevfree(word_t *bt) {
  return *bt & PREVFREE;
}

static inline void bt_clr_prevfree(word_t *bt) {
  if (bt)
    *bt &= ~PREVFREE;
}

static inline void bt_set_prevfree(word_t *bt) {
  *bt |= PREVFREE;
}

/* Returns address of payload. */
static inline void *bt_payload(word_t *bt) {
  return bt + 1;
}

/* Returns address of next block or NULL. */
static inline word_t *bt_next(word_t *bt) {
  word_t *ptr = (void *)bt + bt_size(bt);
  if (ptr <= heap_end)
    return ptr;
  return NULL;
}

/* Returns address of previous block or NULL. */
static inline word_t *bt_prev(word_t *bt) {
  word_t *ptr = (void *)bt - bt_size(bt - 1);
  if (ptr >= heap_start)
    return ptr;
  return NULL;
}

/* Creates boundary tag(s) for given block. */
static inline void bt_make(word_t *bt, size_t size, bt_flags flags) {
  /* If the block is USED we need to make only header*/
  *bt = size | flags;
  bt_clr_prevfree(bt_next(bt));
  /* If the block is FREE we need to make header and footer*/
  if (bt_free(bt)) {
    *bt_footer(bt) = size | flags;
    bt_set_prevfree(bt_next(bt));
  }
}

/* --=[ list management
 * ]=---------------------------------------------------------- */

/* Returns address from size*/
static word_t *ptr_address(int toadd) {
  return (word_t *)(0x800000000 | toadd);
}

/* Returns size from address*/
static int ptr_size(word_t *bt) {
  return (unsigned long)bt - 0x800000000;
}

/* Returns address of next free block*/
static word_t *ptr_next(word_t *bt) {
  return ptr_address(*(bt + 1));
}

/* Returns address of prev free block*/
static word_t *ptr_prev(word_t *bt) {
  return ptr_address(*(bt + 2));
}

static void list_set_prev(word_t *block, word_t *val) {
  *(block + 2) = ptr_size(val);
}

static void list_set_next(word_t *block, word_t *val) {
  *(block + 1) = ptr_size(val);
}

static void list_clr_prev(word_t *block) {
  *(block + 2) = (unsigned long)NULL;
}

static void list_clr_next(word_t *block) {
  *(block + 1) = (unsigned long)NULL;
}

/* Add free block to list */
static void list_add(word_t *block) {
  /* If list is empty */
  if (list_start == NULL) {
    list_start = block;
    list_end = block;
    list_clr_next(list_start);
    list_clr_prev(list_end);
  } else {
    list_set_next(block, list_start);
    list_set_prev(list_start, block);
    list_clr_prev(block);
    list_start = block;
  }
}

/* Remove free block from list */
static void list_remove(word_t *block) {
  /* The only block in the list */
  if (list_start == block && list_end == block) {
    list_start = NULL;
    list_end = NULL;
  }
  /* Remove block from the start */
  else if (list_start == block) {
    list_start = ptr_next(list_start);
    list_clr_prev(list_start);

  }
  /* Remove block from the end*/
  else if (list_end == block) {
    list_end = ptr_prev(list_end);
    list_clr_next(list_end);
  }
  /* Remove block from the middle */
  else {
    word_t *prev = ptr_prev(block);
    word_t *next = ptr_next(block);
    list_set_next(prev, next);
    list_set_prev(next, prev);
  }
}

/* --=[ miscellanous procedures ]=------------------------------------------ */

/* Debugging function */
static void getblockinfo(word_t *bt) {
  if (bt_used(bt))
    msg("Block Address: %p Block Header Size: %d Block Header type: %d Block "
        "ends at: %p \n",
        bt, bt_size(bt), bt_used(bt) | bt_get_prevfree(bt), bt_next(bt));
  else
    msg("Block Address: %p Block Header Size: %d Block Header type: %d Block "
        "next: %p Block prev: %p Block "
        "ends at: %p Block Footer Type: %d\n",
        bt, bt_size(bt), bt_used(bt) | bt_get_prevfree(bt), ptr_next(bt),
        ptr_prev(bt), bt_next(bt), bt_used(bt_footer(bt)));
}

static size_t round_up(size_t size) {
  return (size + ALIGNMENT - 1) & -ALIGNMENT;
}

/* Calculates block size incl. header, footer & payload,
 * and aligns it to block boundary (ALIGNMENT). */
static inline size_t blksz(size_t size) {
  return round_up(size + sizeof(word_t));
}

/* Get more memory */
static void *morecore(size_t size) {
  void *ptr = mem_sbrk(size);
  last = heap_end;

  word_t epilogue = *heap_end;
  heap_end = (void *)heap_end + size;
  *heap_end = epilogue;
  if (ptr == (void *)-1)
    return NULL;
  return last;
}

/* --=[ mm_init ]=---------------------------------------------------------- */

int mm_init(void) {
  void *ptr = mem_sbrk(8 * sizeof(word_t));
  if (!ptr)
    return -1;

  bt_make(ptr + 3 * sizeof(word_t), 16, USED);
  heap_start = ptr + 7 * sizeof(word_t);
  heap_end = ptr + 7 * sizeof(word_t);
  *heap_end = (word_t)USED;
  list_start = NULL;
  list_end = NULL;

  last = NULL;
  return 0;
}
/* --=[ coalesce ]=--------------------------------------------------------- */

/* Join free blocks */
static void *coalesce(void *bt) {
  word_t *prev = bt_prev(bt);
  word_t *next = bt_next(bt);
  int nextcheck = bt_free(next);
  int prevcheck = bt_get_prevfree(bt);
  /* Both block are used */
  if (!prevcheck && !nextcheck) {
    list_add(bt);
    return bt;
  }
  /* Block on the right is free */
  else if (!prevcheck && nextcheck) {
    list_remove(next);
    bt_make(bt, bt_size(bt) + bt_size(next), FREE);
    list_add(bt);
    return bt;
  }
  /* Block on the left is free */
  else if (prevcheck && !nextcheck) {
    list_remove(prev);
    bt_make(prev, bt_size(prev) + bt_size(bt), FREE);
    list_add(prev);
    return prev;
  }
  /* Blocks on the right and left are free */
  else {
    list_remove(prev);
    bt_make(prev, bt_size(prev) + bt_size(bt) + bt_size(next), FREE);
    list_add(prev);
    list_remove(next);
    return prev;
  }
}

/* --=[ malloc ]=----------------------------------------------------------- */

#if 0
/* First fit startegy. */
static word_t *find_fit(size_t reqsz) { 
  if (!list_start)
    return NULL;
  for (word_t *ptr = list_start; ptr != (word_t *)0x800000000; ptr = ptr_next(ptr)) {
    if (bt_size(ptr) >= reqsz) {
      return ptr;
    }
  }
  return NULL;
}
#else
/* Best fit startegy. */
static word_t *find_fit(size_t reqsz) {
  if (!list_start)
    return NULL;
  word_t *best = NULL;
  for (word_t *ptr = list_start; ptr != (word_t *)0x800000000;
       ptr = ptr_next(ptr)) {
    word_t ptrsize = bt_size(ptr);
    if (ptrsize >= reqsz) {
      if (!best || ptrsize < bt_size(best)) {
        best = ptr;
      }
    }
  }
  return best;
}
#endif

void *malloc(size_t size) {
  size_t asize = blksz(size);
  word_t *ptr = find_fit(asize);
  if (ptr) {
    size_t blksize = bt_size(ptr);
    if (blksize - asize >= 16) {
      bt_make(ptr, asize, USED | bt_get_prevfree(ptr));
      word_t *next = bt_next(ptr);
      bt_make(next, blksize - asize, FREE);
      list_remove(ptr);
      coalesce(next);
    } else {
      bt_make(ptr, blksize, USED | bt_get_prevfree(ptr));
      list_remove(ptr);
    }
  } else {
    ptr = morecore(asize);
    bt_make(ptr, asize, USED | bt_get_prevfree(ptr));
  }
  return bt_payload(ptr);
}

/* --=[ free ]=------------------------------------------------------------- */

void free(void *ptr) {
  if (ptr != NULL) {
    word_t *block = bt_fromptr(ptr);
    bt_make(block, bt_size(block), FREE | bt_get_prevfree(block));
    coalesce(block);
  }
}

/* --=[ realloc ]=---------------------------------------------------------- */

void *realloc(void *old_ptr, size_t size) {
  if (old_ptr == NULL)
    return malloc(size);
  if (size == 0) {
    free(old_ptr);
    return NULL;
  }

  word_t *block = bt_fromptr(old_ptr);
  word_t blocksize = bt_size(block);
  word_t asize = blksz(size);

  /* jezeli nasz blok jest ma wiekszy size od wymaganego rozmiaru mozemy go
   * zmniejszyc*/
  if (asize <= blocksize) {
    word_t rest = blocksize - asize;
    if (rest >= 16) {
      bt_make(block, asize, USED | bt_get_prevfree(block));
      bt_make(bt_next(block), rest, FREE);
      coalesce(bt_next(block));
    }
    return old_ptr;
  }

  word_t *next = bt_next(block);
  /* jezeli nasz blok jest na samym koncu mozemy odrazu dac mu wiecej miejsca */
  if (next == heap_end) {
    morecore(asize - blocksize);
    bt_make(block, asize, USED | bt_get_prevfree(block));
    return old_ptr;
  }

  /* jezeli bloki z obu stron sa wolne*/
  if (bt_get_prevfree(block) && bt_free(next)) {
    if (DEBUG_REALLOC)
      msg("realloc oba");
    word_t *prev = bt_prev(block);
    word_t withboth = bt_size(prev) + blocksize + bt_size(next);
    if (withboth >= asize) {
      list_remove(next);
      list_remove(prev);
      memcpy(bt_payload(prev), old_ptr, size);
      if (withboth - asize >= 16) { // 2 * ALIGNMENT
        bt_make(prev, asize, USED);
        word_t *freeblock = bt_next(prev);
        bt_make(freeblock, withboth - asize, FREE);
        coalesce(freeblock);
      } else {
        bt_make(prev, withboth, USED);
      }
      return bt_payload(prev);
    }
  }

  /* jezeli blok po lewej stronie jest wolny*/
  if (bt_get_prevfree(block)) {
    if (DEBUG_REALLOC)
      msg("realloc lewo");
    word_t *prev = bt_prev(block);
    word_t withprev = blocksize + bt_size(prev);
    if (withprev >= asize) {
      list_remove(prev);
      memcpy(bt_payload(prev), old_ptr, size);
      if (withprev - asize >= 16) {
        bt_make(prev, asize, USED | bt_get_prevfree(block));
        word_t *prevnext = bt_next(prev);
        bt_make(prevnext, withprev - asize, FREE);
        coalesce(prevnext);
      } else {
        bt_make(prev, withprev, USED | bt_get_prevfree(block));
      }
      return bt_payload(prev);
    }
  }

  /* jezeli blok po prawej stronie jest wolny */
  if (bt_free(next)) {
    if (DEBUG_REALLOC)
      msg("realloc prawo");
    word_t withnext = blocksize + bt_size(next);
    if (withnext >= asize) {
      list_remove(next);
      if (withnext - asize >= 16) {
        bt_make(block, asize, USED | bt_get_prevfree(block));
        word_t *new = bt_next(block);
        bt_make(new, withnext - asize, FREE);
        coalesce(new);
      } else {
        bt_make(block, withnext, USED | bt_get_prevfree(block));
      }
      /* Remove block we used from free list */
      return old_ptr;
    }
  }

  /* ogolny przypadek */
  word_t *new_ptr = malloc(size);
  memcpy(new_ptr, old_ptr, size);
  free(old_ptr);
  if (DEBUG_REALLOC)
    msg("realloc");
  return new_ptr;
}

/* --=[ calloc ]=----------------------------------------------------------- */

void *calloc(size_t nmemb, size_t size) {
  size_t bytes = nmemb * size;
  void *new_ptr = malloc(bytes);
  if (new_ptr)
    memset(new_ptr, 0, bytes);
  return new_ptr;
}

/* --=[ mm_checkheap ]=----------------------------------------------------- */

void mm_checkheap(int verbose) {
  void *bt;
  msg("Check Heap \n");
  for (bt = heap_start; bt && bt_size(bt) > 0; bt = bt_next(bt)) {
    getblockinfo(bt);
  }
  msg("Heap start: %p Heap end: %p List start: %p List end: %p \n", heap_start,
      heap_end, list_start, list_end);
  msg("Check Heap End\n\n");
}
