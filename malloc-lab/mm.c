/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 *
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "team1",
    /* First member's full name */
    "Hyeonji Lee",
    /* First member's email address */
    "8976hylee@gmail.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};


/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

/* metadata size (bytes) */
typedef u_int32_t meta_t;

#define GET(ptr) (*(meta_t *)(ptr))
#define PUT(ptr, val) (*(meta_t *)(ptr) = (val))
#define PACK(size, palloc, alloc) ((size) | (palloc << 1) |(alloc))

#define MASK_BSIZE (~UINT32_C(0x7))
#define MASK_ALLOCATED (UINT32_C(0x1))
#define MASK_PALLOCATED (UINT32_C(1<<1))

/*ptr은 헤더나 푸터를 가리켜야 한다*/
#define GET_SIZE(ptr) ((MASK_BSIZE & GET(ptr)))
/*ptr은 헤더나 푸터를 가리켜야 한다*/
#define GET_ALLOC(ptr) (MASK_ALLOCATED & GET(ptr))
/*ptr은 헤더를 가리켜야 한다*/
#define GET_PALLOC(ptr) (MASK_PALLOCATED & GET(ptr))

/*ptr은 헤더나 푸터를 가리켜야 한다*/
#define SET_ALLOC(ptr, alloc) ((alloc) ? PUT((ptr), GET(ptr) | MASK_ALLOCATED) : PUT((ptr), GET(ptr) & ~MASK_ALLOCATED))
/*ptr은 헤더나 푸터를 가리켜야 한다*/
#define SET_PALLOC(ptr, palloc) ((palloc) ? PUT((ptr), GET(ptr) | MASK_PALLOCATED) : PUT((ptr), GET(ptr) & ~MASK_PALLOCATED))

#define GET_PRED(ptr) (((void **)(ptr))[0])  // (*(void **)ptr)
#define GET_SUCC(ptr) (((void **)(ptr))[1])  // (*((void **)ptr + 1))
#define SET_PRED(ptr, pred) (((void **)(ptr))[0] = (pred))
#define SET_SUCC(ptr, succ) (((void **)(ptr))[1] = (succ)) 

#define MSIZE (sizeof(meta_t))
#define CHUNKSIZE (1<<8)
#define MIN_BSIZE (ALIGN(MSIZE * 2 + sizeof(void *) * 2))
#define TO_BSIZE(size) ((size < sizeof(void *) * 2) ? MIN_BSIZE : ALIGN((size) + MSIZE))


#define HDRP(ptr) ((char *)(ptr) - MSIZE)
#define FTRP(ptr) ((char *)(ptr) + GET_SIZE(HDRP(ptr)) - 2 * MSIZE)
#define NEXT_HDRP(ptr) ((char *)(ptr) + GET_SIZE(HDRP(ptr)) - MSIZE)
#define PREV_FTRP(ptr) ((char *)(ptr) - 2 * MSIZE)
/*use only when !palloc*/
#define PREV_BLOCK(ptr) ((char *)(ptr) - GET_SIZE(PREV_FTRP(ptr)))
#define NEXT_BLOCK(ptr) ((char *)(ptr) + GET_SIZE(HDRP(ptr)))


static void *heap_base;
static void *free_head;
static void *last_search;

static void *find_fit(size_t requested);
static void *first_fit(size_t requested);
static void *next_fit(size_t requested);
static void *extend_heap(size_t size);
static void split(void *ptr, size_t requested);
static void *coalesce(void *ptr);
static inline void link_fb(void *ptr);
static inline void unlink_fb(void *ptr);


/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    void * allocated = mem_sbrk(MIN_BSIZE + 2 * MSIZE);
    if (allocated == (void *) -1) { return -1; }

    void *prologue = (char *)allocated + 2 * MSIZE;
    meta_t data = PACK(MIN_BSIZE, false, true);
    PUT(HDRP(prologue), data);

    void *epilogue = NEXT_BLOCK(prologue);
    PUT(HDRP(epilogue), PACK(0, true, true));

    heap_base = prologue;
    free_head = NULL;
    last_search = NULL;

    if (!extend_heap(0)) { return -1; }

    return 0;
}

/*
 * mm_malloc - Allocate a block placed in a free block if there are any available ones that can include the size
 *     else allocate by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    // 할 것 : 남은 힙 공간 있는지 탐색, sbrk 혹은 가용 리스트에서 배치 -> 정책에 따른 슬라이싱, 헤더 구성
    if (size <= 0) return NULL;

    size_t blocksize = TO_BSIZE(size);

    void *ptr = find_fit(blocksize);

    if (!ptr){
        ptr = extend_heap(blocksize);

        if (ptr == NULL)
          return NULL;
    }

    split(ptr, blocksize);

    return ptr;
}

static void *find_fit(size_t requested){
    return first_fit(requested);
}

static void *first_fit(size_t requested){
  void *cur = free_head;

  while(cur){
    if (GET_SIZE(HDRP(cur)) >= requested) return cur;

    cur = GET_SUCC(cur);
  }

  return NULL;
}

static void *next_fit(size_t requested){
  void *cur = last_search ? last_search : NEXT_BLOCK(heap_base);
  size_t size;
  do{
    size = GET_SIZE(HDRP(cur));
    if (size == 0){
      if (!last_search) return NULL;
      else cur = NEXT_BLOCK(heap_base);
      continue;
    }
    
    if (!GET_ALLOC(HDRP(cur)) && size >= requested){
      last_search = cur;
      return cur;
    }
    else
      cur = NEXT_BLOCK(cur);
  } while(cur != last_search);

  return NULL;
}

/* increase the brk pointer and return previous brk */
static void *extend_heap(size_t size)
{ 
  size_t min_size = (size > CHUNKSIZE) ? size : CHUNKSIZE;
  void *ptr = mem_sbrk(min_size);
  if (ptr == (void *)-1)
      return NULL;

  bool palloc = GET_PALLOC(HDRP(ptr));
  meta_t data = PACK(min_size, palloc, false);
  PUT(HDRP(ptr), data);
  PUT(FTRP(ptr), data);
  link_fb(ptr);

  // epilogue header
  PUT(NEXT_HDRP(ptr), PACK(0, false, true));

  return (ptr);
}

/* splites the block if the blocksize is big enough */
static void split(void *ptr, size_t requested)
{
    if (!GET_ALLOC(HDRP(ptr))) unlink_fb(ptr);

    // 블록 사이즈가 작으면 자르지 않고, 충분히 크면 자르기
    size_t blocksize = GET_SIZE(HDRP(ptr));
    bool palloc = GET_PALLOC(HDRP(ptr));

    if (blocksize < requested * 2){
      SET_ALLOC(HDRP(ptr), true);
      SET_PALLOC(NEXT_HDRP(ptr), true);
      return;
    }
    // if (blocksize < requested + MIN_BSIZE) {
    //   SET_ALLOC(HDRP(ptr), true);
    //   SET_PALLOC(NEXT_HDRP(ptr), true);
    //   return;
    // }


    meta_t data = PACK(requested, palloc, true);
    PUT(HDRP(ptr), data);

    size_t left = blocksize - requested;
    void *next = NEXT_BLOCK(ptr);
    data = PACK(left, true, false);
    PUT(HDRP(next), data);
    PUT(FTRP(next), data);

    link_fb(next);
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    if (GET_ALLOC(HDRP(ptr))){

      SET_PALLOC(NEXT_HDRP(ptr), false);
      coalesce(ptr);
    }
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    bool palloc = GET_PALLOC(HDRP(ptr));
    size_t cur_size = GET_SIZE(HDRP(ptr));
    size_t blocksize = TO_BSIZE(size);


    if (cur_size >= blocksize){
      return ptr;
    }

    if (!GET_ALLOC(NEXT_HDRP(ptr))){
      void *next = NEXT_BLOCK(ptr);
      unlink_fb(next);
      size_t next_size = GET_SIZE(HDRP(next));
      size_t sum = cur_size + next_size;
      

      while(!GET_ALLOC(NEXT_HDRP(next)) && sum < blocksize){
        next = NEXT_BLOCK(next);
        next_size = GET_SIZE(HDRP(next));
        sum += next_size;
        unlink_fb(next);
      }


      meta_t data = PACK(sum, palloc, true);
      PUT(HDRP(ptr), data);
      SET_PALLOC(NEXT_HDRP(ptr), true);

      if (sum >= blocksize){
        //split(ptr, blocksize);
        return ptr;
      }

    }
    else if (GET_SIZE(NEXT_HDRP(ptr)) == 0){
      void *next = extend_heap(blocksize - cur_size);
      //split(next, blocksize - cur_size);
      unlink_fb(next);

      meta_t data = PACK(GET_SIZE(HDRP(ptr)) + GET_SIZE(HDRP(next)), palloc, true);
      PUT(HDRP(ptr), data);
      SET_PALLOC(NEXT_HDRP(ptr), true);
      
      return ptr;
    }

    void *newptr = mm_malloc(size);
    if (newptr == NULL) { return NULL; }

    memcpy(newptr, ptr, cur_size - MSIZE);
    mm_free(ptr);

    return newptr;
}

static void *coalesce(void *ptr){
  void *block = ptr;
  size_t size = GET_SIZE(HDRP(ptr));
  
  if (!GET_ALLOC(NEXT_HDRP(ptr))){
    size += GET_SIZE(NEXT_HDRP(ptr));
    unlink_fb(NEXT_BLOCK(ptr));
  }

  bool palloc = GET_PALLOC(HDRP(ptr));
  if (!palloc){
    block = PREV_BLOCK(ptr);
    palloc = GET_PALLOC(HDRP(block));
    size += GET_SIZE(HDRP(block));
    unlink_fb(block);
  }

  // free 후 합친 블록
  meta_t data = PACK(size, palloc, false);
  PUT(HDRP(block), data);
  PUT(FTRP(block), data);
  link_fb(block);

  // 합친 다음 블록
  SET_PALLOC(NEXT_HDRP(block), false);

  return block;
}

static inline void link_fb(void *ptr){
  if (!ptr) return;

  if (free_head){
    SET_PRED(ptr, NULL);
    SET_SUCC(ptr, free_head);
    SET_PRED(free_head, ptr);      
  }
  else{
    SET_PRED(ptr, NULL);
    SET_SUCC(ptr, NULL);
  }

  free_head = ptr;
}

static inline void unlink_fb(void *ptr){
  if (!ptr) return;

  void *pred = GET_PRED(ptr);
  void *succ = GET_SUCC(ptr);
  if (pred){
    SET_SUCC(pred, succ);
  }
  else{
    free_head = succ;
  }

  if (succ){
    SET_PRED(succ, pred);
  }
}