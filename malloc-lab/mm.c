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
#define CHUNKSIZE (1<<9)
#define MIN_BSIZE (ALIGN(MSIZE * 2 + sizeof(void *) * 2)) 
#define TO_BSIZE(size) ((size < sizeof(void *) * 2) ? MIN_BSIZE : ALIGN(size + MSIZE))


#define HDRP(ptr) ((char *)(ptr) - MSIZE)
#define FTRP(ptr) ((char *)(ptr) + GET_SIZE(HDRP(ptr)) - 2 * MSIZE)
#define NEXT_HDRP(ptr) ((char *)(ptr) + GET_SIZE(HDRP(ptr)) - MSIZE)
#define PREV_FTRP(ptr) ((char *)(ptr) - 2 * MSIZE)
/*use only when !palloc*/
#define PREV_BLOCK(ptr) ((char *)(ptr) - GET_SIZE(PREV_FTRP(ptr)))
#define NEXT_BLOCK(ptr) ((char *)(ptr) + GET_SIZE(HDRP(ptr)))

#define MIN_SIZE_EXP 6
#define MAX_SIZE_EXP 13
#define CLASS_LEN (MAX_SIZE_EXP - MIN_SIZE_EXP + 2)
#define IND_TO_EXP(index) (index + 6)
#define EXP_TO_SIZE(exp) (1<< ((exp) - 1)) 
#define IND_TO_SIZE(index) (EXP_TO_SIZE(IND_TO_EXP(index)))

static void *heap_base;
static void *last_search;
static void *free_head;
static void *free_class[CLASS_LEN];

static void init_classes(void);
static void *find_fit(size_t requested);
static void *first_fit(size_t requested);
static void *next_fit(size_t requested);
static void *best_fit(size_t requested);
static void *extend_heap(size_t size);
static void *place(void *ptr, size_t requested);
static void *coalesce(void *ptr);
static inline void link_fb(void *ptr);
static inline void unlink_fb(void *ptr);
static inline unsigned int get_index(size_t size);
static inline size_t align_up(size_t size);


/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    init_classes();
    
    void * allocated = mem_sbrk(MIN_BSIZE + 2 * MSIZE);
    if (allocated == (void *) -1) { return -1; }

    void *prologue = (char *)allocated + 2 * MSIZE;
    meta_t data = PACK(MIN_BSIZE, false, true);
    PUT(HDRP(prologue), data);

    void *initial = mem_sbrk(64);
    if (initial == (void *) -1) return -1;

    // 작은 요청에 대비. 미리 확보하는 낭비를 너무 크게 하지는 않게
    data = PACK(64, true, false);
    PUT(HDRP(initial), data);
    PUT(FTRP(initial), data);
    link_fb(initial);

    PUT(NEXT_HDRP(initial), PACK(0, false, true));
  
    heap_base = prologue;
    free_head = NULL;
    last_search = NULL;

    return 0;
}

static void init_classes(void)
{
  for (int i = 0; i < CLASS_LEN; i++){
    free_class[i] = NULL;
  }
}

/*
 * mm_malloc - Allocate a block placed in a free block if there are any available ones that can include the size
 *     else allocate by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    if (size <= 0) return NULL;

    size_t blocksize = align_up(size);

    void *ptr = find_fit(blocksize);

    if (!ptr){
        ptr = extend_heap(blocksize);

        if (ptr == NULL)
          return NULL;
    }

    return place(ptr, blocksize);
}

static void *find_fit(size_t requested){
    return best_fit(requested);
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

static void *best_fit(size_t requested){
  void *best = NULL;
  unsigned int index = get_index(requested);
  void *cur = free_class[index];

  while(index < CLASS_LEN){
    if (!cur && best) return best; 

    // 대상 리스트 찾기
    while(!cur && index < CLASS_LEN - 1){
      cur = free_class[++index];
    }

    // 대상 리스트가 하나도 없을 때
    if (!cur) break;

    size_t size = GET_SIZE(HDRP(cur));
    if (size == requested) return cur;
    if (size > requested){
      if (!best) best = cur;
      else if (GET_SIZE(HDRP(best)) > size) best = cur;
    }

    cur = GET_SUCC(cur);
  }

  return best;
}

/* increase the brk pointer and return previous brk */
static void *extend_heap(size_t size)
{ 
  size_t min_size = (size > CHUNKSIZE) ? size : CHUNKSIZE;

  // 비슷한 요청이 반복될 때를 대비 -> 고정 길이 CHUNKSIZE로 할당하는 것보다 요청한 크기의 배수로 만들어두는 것이 효과적
  if (size > MIN_BSIZE && size <CHUNKSIZE){
    size_t batch_size = size * 8;
    if (batch_size > min_size) min_size = batch_size;
  }

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
static void *place(void *ptr, size_t requested)
{
    if (!GET_ALLOC(HDRP(ptr))) unlink_fb(ptr);

    // 블록 사이즈가 작으면 자르지 않고, 충분히 크면 자르기
    size_t blocksize = GET_SIZE(HDRP(ptr));  

    if (blocksize - requested <= MIN_BSIZE){
      SET_ALLOC(HDRP(ptr), true);
      SET_PALLOC(NEXT_HDRP(ptr), true);
      return ptr;
    }


    bool palloc = GET_PALLOC(HDRP(ptr));
    
    if (requested < blocksize / 2){
      meta_t data = PACK(requested, palloc, true);
      PUT(HDRP(ptr), data);
      
      void *next = NEXT_BLOCK(ptr);
      data = PACK(blocksize - requested, true, false);
      PUT(HDRP(next), data);
      PUT(FTRP(next), data);
      link_fb(next);

      return ptr;
    }
    else{
      meta_t data = PACK(blocksize - requested, palloc, false);
      PUT(HDRP(ptr), data);
      PUT(FTRP(ptr), data);
      link_fb(ptr);

      void *ret = NEXT_BLOCK(ptr);
      data = PACK(requested, false, true);
      PUT(HDRP(ret), data);
      SET_PALLOC(NEXT_HDRP(ret), true);

      return ret;
    }
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    if (GET_ALLOC(HDRP(ptr))){
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
    size_t blocksize = align_up(size);


    if (cur_size >= blocksize){
      return ptr;
    }

    if (!GET_ALLOC(NEXT_HDRP(ptr))){
      void *next = NEXT_BLOCK(ptr);
      unlink_fb(next);
      size_t next_size = GET_SIZE(HDRP(next));
      size_t sum = cur_size + next_size;

      meta_t data = PACK(sum, palloc, true);
      PUT(HDRP(ptr), data);
      SET_PALLOC(NEXT_HDRP(ptr), true);

      if (sum >= blocksize){
        return ptr;
      }

    }
    else if (GET_SIZE(NEXT_HDRP(ptr)) == 0){
      void *next = extend_heap(align_up((blocksize - cur_size)));
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

  void *head = free_class[get_index(GET_SIZE(HDRP(ptr)))];

  if (head){
    SET_PRED(ptr, NULL);
    SET_SUCC(ptr, head);
    SET_PRED(head, ptr);      
  }
  else{
    SET_PRED(ptr, NULL);
    SET_SUCC(ptr, NULL);
  }

  free_class[get_index(GET_SIZE(HDRP(ptr)))] = ptr;
}

static inline void unlink_fb(void *ptr){
  if (!ptr) return;

  void *pred = GET_PRED(ptr);
  void *succ = GET_SUCC(ptr);
  if (pred){
    SET_SUCC(pred, succ);
  }
  else{
    free_class[get_index(GET_SIZE(HDRP(ptr)))] = succ;
  }

  if (succ){
    SET_PRED(succ, pred);
  }
}

static inline unsigned int get_index(size_t size){
  size_t limit = EXP_TO_SIZE(MIN_SIZE_EXP);
  unsigned int index = 0;

  while(size > limit && index < CLASS_LEN - 1){
    limit <<= 1;
    ++index;
  }

  return index;
}

static inline size_t align_up(size_t size){
  if (size >= EXP_TO_SIZE(MIN_SIZE_EXP) && size < EXP_TO_SIZE(MAX_SIZE_EXP - 1)){
    size_t upper = EXP_TO_SIZE(MIN_SIZE_EXP);
    while (upper < size){
      upper <<= 1;
    }

    if (size >= upper - upper / 8){   // 조금 더 할당 -> 해제 후 조금 더 큰 요청에서도 사용할 수 있도록.
      return TO_BSIZE(upper);
    }  
  }

  return TO_BSIZE(size);  
}