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
#define PACK(size, alloc) ((size) | (alloc))

#define MSIZE (sizeof(meta_t))
#define HEADER_PTR(ptr) ((char *)(ptr) - MSIZE)
#define FOOTER_PTR(ptr, size) ((char *)(ptr) + (size) - 2 * MSIZE)
#define NEXT_HEADER_PTR(ptr, size) ((char *)(ptr) + (size) - MSIZE)
#define PREV_FOOTER_PTR(ptr) ((char *)(ptr) - 2 * MSIZE)

#define MIN_BLOCK_SIZE (MSIZE * 2 + ALIGNMENT)
#define MASK_BLOCK_SIZE (~UINT32_C(0x7))
#define MASK_ALLOCATED (0x1)

/*ptr은 헤더나 푸터를 가리켜야 한다*/
#define GET_SIZE(ptr) ((MASK_BLOCK_SIZE & *(meta_t *)ptr))
/*ptr은 헤더나 푸터를 가리켜야 한다*/
#define IS_ALLOCATED(ptr) (MASK_ALLOCATED & *(meta_t *)ptr)

#define BLOCK_SIZE(size) ((size) + 2 * MSIZE)
#define PREV_BLOCK(ptr) ((char *)(ptr) - GET_SIZE(PREV_FOOTER_PTR(ptr)))
#define NEXT_BLOCK(ptr, size) ((char *)(ptr) + (size))

static void *heap_base;
static void *first_fit(size_t block_size);
static void *extend_heap(size_t size);
static void split(void *ptr, size_t *requested);
static bool try_coalesce(void *ptr);


/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    // 할 것 : 프롤로그와 에필로그 생성, 시작 포인터 저장
    void * allocated = mem_sbrk(16);
    if (allocated == (void *) -1) { return -1; }

    void *prologue = (char *)allocated + 2 * MSIZE;
    meta_t data = PACK(8, true);
    PUT(HEADER_PTR(prologue), data);
    PUT(FOOTER_PTR(prologue, 8), data);

    void *epilogue = (char *)allocated + 4 * MSIZE;
    PUT(HEADER_PTR(epilogue), PACK(0, true));

    heap_base = prologue;
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

    size_t aligned = ALIGN(size);
    size_t blocksize = BLOCK_SIZE(aligned);

    void *ptr = first_fit(blocksize);

    if (!ptr){
        ptr = extend_heap(blocksize * 2);

        if (ptr == NULL)
          return NULL;
    }

    split(ptr, &blocksize);
    
    meta_t data = PACK(blocksize, true);
    PUT(HEADER_PTR(ptr), data);
    PUT(FOOTER_PTR(ptr, blocksize), data);

    return ptr;
}

static void *first_fit(size_t block_size){
  void *cur = heap_base;
  size_t size;

  do{
    size = GET_SIZE(HEADER_PTR(cur));

    if (!IS_ALLOCATED(HEADER_PTR(cur)) && size >= block_size)
      return cur;
    else
      cur = NEXT_BLOCK(cur, size);
  } while (size > 0);

  return NULL;
}

/* increase the brk pointer and return previous brk */
static void *extend_heap(size_t size)
{
  void *ptr = mem_sbrk(size);
  if (ptr == (void *)-1)
      return NULL;
  
  meta_t data = PACK(size, false);
  PUT(HEADER_PTR(ptr), data);
  PUT(FOOTER_PTR(ptr, size), data);

  // epilogue header
  PUT(NEXT_HEADER_PTR(ptr, size), PACK(0, true));

  return ptr;
}

/* splites the block if the blocksize is big enough */
static void split(void *ptr, size_t *requested)
{
    // 블록 사이즈가 작으면 자르지 않고, 충분히 크면 자르기
    size_t blocksize = GET_SIZE(HEADER_PTR(ptr));
    if (blocksize < *requested + MIN_BLOCK_SIZE) {
      *requested = blocksize;
      return;
    }

    meta_t data = PACK(*requested, false);
    PUT(HEADER_PTR(ptr), data);
    PUT(FOOTER_PTR(ptr, *requested), data);

    size_t left = blocksize - *requested;
    void *next = NEXT_BLOCK(ptr, *requested);
    data = PACK(left, false);
    PUT(HEADER_PTR(next), data);
    PUT(FOOTER_PTR(next, left), data);
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    // 할 것 : 들어온 ptr 유효성 검사
    size_t size = GET_SIZE(HEADER_PTR(ptr));
    meta_t data = PACK(size, false);
    PUT(HEADER_PTR(ptr), data);
    PUT(FOOTER_PTR(ptr, size), data);

    void *cur = PREV_BLOCK(ptr);
    if (IS_ALLOCATED(HEADER_PTR(cur))) cur = ptr;
    else if (!try_coalesce(cur)) cur = ptr;
    try_coalesce(cur);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    // 할 것 : 길이 비교. 다음 블록 활성 여부 확인, 새 블록 할당 여부 결정
    // 현재 길이 확인
    // 반복 : 병합. 현재 길이가 충분할 때까지 or 더이상 없을 때까지

    size_t copy_size = GET_SIZE(HEADER_PTR(ptr)) - 2 * MSIZE;

    size_t aligned = ALIGN(size);
    size_t blocksize = BLOCK_SIZE(aligned);

    while(GET_SIZE(HEADER_PTR(ptr)) < blocksize){
      if (!try_coalesce(ptr))

        break;
    }

    if (GET_SIZE(HEADER_PTR(ptr)) >= blocksize){
      size_t cur_size = GET_SIZE(HEADER_PTR(ptr));
      meta_t data = PACK(cur_size, true);
      PUT(HEADER_PTR(ptr), data);
      PUT(FOOTER_PTR(ptr, cur_size), data);
      return ptr;
    }
    else{
      size_t size = BLOCK_SIZE(copy_size);
      split(ptr, &size);
    }

    void *newptr = mm_malloc(size);
    

    if (newptr == NULL){
      size_t cur_size = GET_SIZE(HEADER_PTR(ptr));
      meta_t data = PACK(cur_size, true);
      PUT(HEADER_PTR(ptr), data);
      PUT(FOOTER_PTR(ptr, cur_size), data);
      return NULL;
    }

    memcpy(newptr, ptr, copy_size);
    mm_free(ptr);
    return newptr;
}

/* coalesce with the next block if it is free */
static bool try_coalesce(void *ptr){
  void *next = NEXT_BLOCK(ptr, GET_SIZE(HEADER_PTR(ptr)));
  if (IS_ALLOCATED(HEADER_PTR(next))) return false;

  size_t size = GET_SIZE(HEADER_PTR(ptr)) + GET_SIZE(HEADER_PTR(next));
  meta_t data = PACK(size, false);
  PUT(HEADER_PTR(ptr), data);
  PUT(FOOTER_PTR(ptr, size), data);

  return true;
}