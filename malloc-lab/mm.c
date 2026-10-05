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

#define MSIZE (sizeof(meta_t))
#define HEADER_PTR(ptr) ((char *)(ptr) - MSIZE)
#define FOOTER_PTR(ptr, size) ((char *)(ptr) + (size) - 2 * MSIZE)
#define NEXT_HEADER_PTR(ptr, size) ((char *)(ptr) + (size) - MSIZE)
#define PREV_FOOTER_PTR(ptr) ((char *)(ptr) - 2 * MSIZE)

#define CHUNKSIZE (1<<9)
#define MIN_BLOCK_SIZE (ALIGN(MSIZE))
#define MASK_BLOCK_SIZE (~UINT32_C(0x7))
#define MASK_ALLOCATED (0x1)
#define MASK_PALLOCATED (1<<1)

/*ptr은 헤더나 푸터를 가리켜야 한다*/
#define GET_SIZE(ptr) ((MASK_BLOCK_SIZE & GET(ptr)))
/*ptr은 헤더나 푸터를 가리켜야 한다*/
#define IS_ALLOCATED(ptr) (MASK_ALLOCATED & GET(ptr))
/*ptr은 헤더를 가리켜야 한다*/
#define IS_PALLOCATED(ptr) (MASK_PALLOCATED & GET(ptr))

#define BLOCK_SIZE(size) (ALIGN((size) + MSIZE))
/*use only when !palloc*/
#define PREV_BLOCK(ptr) ((char *)(ptr) - GET_SIZE(PREV_FOOTER_PTR(ptr)))
#define NEXT_BLOCK(ptr, size) ((char *)(ptr) + (size))

static void *heap_base;
static void *last_search;

static void *find_fit(size_t requested);
static void *first_fit(size_t requested);
static void *next_fit(size_t requested);
static void *extend_heap(size_t size);
static void split(void *ptr, size_t requested);
static void *coalesce(void *ptr);

/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    // 할 것 : 프롤로그와 에필로그 생성, 시작 포인터 저장
    void * allocated = mem_sbrk(16);
    if (allocated == (void *) -1) { return -1; }

    void *prologue = (char *)allocated + 2 * MSIZE;
    meta_t data = PACK(8, false, true);
    PUT(HEADER_PTR(prologue), data);

    void *epilogue = (char *)allocated + 4 * MSIZE;
    PUT(HEADER_PTR(epilogue), PACK(0, true, true));

    if (!extend_heap(0)) { return -1; }

    heap_base = prologue;
    last_search = NULL;
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

    size_t blocksize = BLOCK_SIZE(size);

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
    return next_fit(requested);
}

static void *first_fit(size_t requested){
  void *cur = heap_base;
  size_t size;

  do{
    size = GET_SIZE(HEADER_PTR(cur));

    if (!IS_ALLOCATED(HEADER_PTR(cur)) && size >= requested)
      return cur;
    else
      cur = NEXT_BLOCK(cur, size);
  } while (size > 0);

  return NULL;
}

static void *next_fit(size_t requested){
  void *cur = last_search ? last_search : NEXT_BLOCK(heap_base, 8);
  size_t size;
  do{
    size = GET_SIZE(HEADER_PTR(cur));
    if (size == 0){
      if (!last_search) return NULL;
      else cur = NEXT_BLOCK(heap_base, 8);
    }
    
    if (!IS_ALLOCATED(HEADER_PTR(cur)) && size >= requested){
      last_search = cur;
      return cur;
    }
    else
      cur = NEXT_BLOCK(cur, size);
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

  bool palloc = IS_PALLOCATED(HEADER_PTR(ptr));
  meta_t data = PACK(min_size, palloc, false);
  PUT(HEADER_PTR(ptr), data);
  PUT(FOOTER_PTR(ptr, min_size), data);

  // epilogue header
  PUT(NEXT_HEADER_PTR(ptr, min_size), PACK(0, false, true));

  return ptr;
}

/* splites the block if the blocksize is big enough */
static void split(void *ptr, size_t requested)
{
    // 블록 사이즈가 작으면 자르지 않고, 충분히 크면 자르기
    size_t blocksize = GET_SIZE(HEADER_PTR(ptr));
    bool palloc = IS_PALLOCATED(HEADER_PTR(ptr));
    if (blocksize < requested + MIN_BLOCK_SIZE) {
      PUT(HEADER_PTR(ptr), GET(HEADER_PTR(ptr)) | 1);

      void *next_hd = NEXT_HEADER_PTR(ptr, blocksize);
      PUT(next_hd, GET(next_hd) | (1<<1));
      return;
    }

    meta_t data = PACK(requested, palloc, true);
    PUT(HEADER_PTR(ptr), data);

    size_t left = blocksize - requested;
    void *next = NEXT_BLOCK(ptr, requested);
    data = PACK(left, true, false);
    PUT(HEADER_PTR(next), data);
    PUT(FOOTER_PTR(next, left), data);
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    if (IS_ALLOCATED(HEADER_PTR(ptr))){
      bool is_last_search = (last_search == ptr || last_search == NEXT_BLOCK(ptr, GET_SIZE(HEADER_PTR(ptr))));
      void *result = coalesce(ptr);

      if (is_last_search) last_search = result;
    }
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    bool palloc = IS_PALLOCATED(HEADER_PTR(ptr));
    size_t cur_size = GET_SIZE(HEADER_PTR(ptr));
    size_t blocksize = BLOCK_SIZE(size);


    if (cur_size >= blocksize){
      return ptr;
    }

    if (!IS_ALLOCATED(NEXT_HEADER_PTR(ptr, cur_size))){
      void *next = NEXT_BLOCK(ptr, cur_size);
      size_t next_size = GET_SIZE(HEADER_PTR(next));
      size_t sum = cur_size + next_size;
      bool is_last_search = next == last_search;
      while(!IS_ALLOCATED(NEXT_HEADER_PTR(next, next_size)) && sum < blocksize){
        next = NEXT_BLOCK(next, next_size);
        next_size = GET_SIZE(HEADER_PTR(next));
        sum += next_size;

        is_last_search = is_last_search || next == last_search;
      }

      if (sum >= blocksize){
        meta_t data = PACK(sum, palloc, true);
        PUT(HEADER_PTR(ptr), data);

        void *next_hd = NEXT_HEADER_PTR(ptr, sum);
        PUT(next_hd, GET(next_hd) | (1 << 1));

        if (is_last_search) last_search = NEXT_BLOCK(ptr, sum);

        split(ptr, blocksize);

        return ptr;
      }
    }
    else if (GET_SIZE(NEXT_HEADER_PTR(ptr, cur_size)) == 0){
      void *next = extend_heap(blocksize - cur_size);
      split(next, blocksize - cur_size);
      meta_t data = PACK(blocksize, palloc, true);
      PUT(HEADER_PTR(ptr), data);
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
  size_t size = GET_SIZE(HEADER_PTR(ptr));
  
  if (!IS_ALLOCATED(NEXT_HEADER_PTR(ptr, size))){
    size += GET_SIZE(NEXT_HEADER_PTR(ptr, size));
  }

  bool palloc = IS_PALLOCATED(HEADER_PTR(ptr));
  if (!palloc){
    block = PREV_BLOCK(ptr);
    palloc = IS_PALLOCATED(HEADER_PTR(block));
    size += GET_SIZE(HEADER_PTR(block));
  }

  // free 후 합친 블록
  meta_t data = PACK(size, palloc, false);
  PUT(HEADER_PTR(block), data);
  PUT(FOOTER_PTR(block, size), data);

  void *next_hd = NEXT_HEADER_PTR(block, size);
  PUT(next_hd, GET(next_hd) & ~(1<<1));

  return block;
}