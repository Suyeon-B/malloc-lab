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
    "Team 1",
    /* First member's full name */
    "Suyeon Bak",
    /* First member's email address */
    "tndus4243@naver.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};


/*
 * 기본 상수와 매크로
 */

/* 기본 단위 - word, double word, 새로 할당받는 힙의 크기 CHUNKSIZE, 최소 블록 크기 정의 */
#define WSIZE 4                 // 워드, 헤더/푸터 사이즈 (bytes)
#define DSIZE 8                 // 더블워드 사이즈 (bytes)
#define MINIMUM 16              // 최소 블록 크기 : Initial Prologue block, header, footer, PREC, SUCC
#define CHUNKSIZE (1 << 12)     // 힙 사이즈 확장 크기 기준 : 4,096bytes -> 4KB

#define MAX(x, y) ((x) > (y) ? (x) : (y))

/* header 및 footer 값(size + allocated) 리턴 */
#define PACK(size, alloc) ((size) | (alloc))

/* 주소 p에서의 word를 읽어오거나 쓰는 함수 */
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

/* 주소 p에 있는 header 또는 footer의 사이즈와 할당 비트를 리턴 */
#define GET_SIZE(p) (GET(p) & ~0x7)     // NOT 연산자로 SIZE만 뽑아오기 위해
#define GET_ALLOC(p) (GET(p) & 0x1)     // 0x1과 곱해서 끝 자리가 여전히 1이라면 allocated

/* 블록 포인터 bp를 인자로 받아 블록의 header와 footer의 주소 반환 */
#define HDRP(bp) ((char *)(bp)-WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* 블록 포인터 bp를 인자로 받아 이후, 이전 블록의 주소 리턴 */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp)-WSIZE))) // (char*)(bp) + GET_SIZE(지금 블록의 헤더값)
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp)-DSIZE)))   // (char*)(bp) - GET_SIZE(이전 블록의 풋터값)

/* Free List 상에서의 이전, 이후 블록의 포인터 리턴 */
#define PREC_FREEP(bp) (*(void **)(bp))         // 이전 블록의 bp
#define SUCC_FREEP(bp) (*(void **)(bp + WSIZE)) // 이후 블록의 bp

/* global variable & functions */
static char *heap_listp = NULL; 
static char *free_listp = NULL; // free list의 맨 첫 블록을 가리키는 포인터

static void *extend_heap(size_t);
static void *coalesce(void *);
static void *find_fit(size_t);
static void place(void *, size_t);

int mm_init(void);
void *mm_malloc(size_t);
void mm_free(void *);
void *mm_realloc(void *, size_t);
void removeBlock(void *);
void putFreeBlock(void *);


/*
 * mm_init : 6 words 사이즈의 free 리스트를 초기화하고, 초기 free 블록 생성
 */
int mm_init(void)
{
    // 6 words 사이즈의 빈 가용 리스트 초기화
    // 6 words 구성 : unused padding, prol_header, prol_footer, PREC, SUCC, epil_header
    if ((heap_listp = mem_sbrk(6 * WSIZE)) == (void *)-1)
        return -1;

    PUT(heap_listp, 0);                                 // unused padding
    PUT(heap_listp + (1 * WSIZE), PACK(MINIMUM, 1));    // prologue hdr
    PUT(heap_listp + (2 * WSIZE), NULL);                // prologue block안의 PRED 포인터 NULL로 초기화
    PUT(heap_listp + (3 * WSIZE), NULL);                // prologue block안의 SUCC 포인터 NULL로 초기화
    PUT(heap_listp + (4 * WSIZE), PACK(MINIMUM, 1));    // prologue ftr
    PUT(heap_listp + (5 * WSIZE), PACK(0, 1));          // epliogue hdr

    free_listp = heap_listp + 2 * WSIZE;                // free_listp는 PRED를 가리키게 한다.

    // 그 후 CHUNKSIZE만큼 힙을 확장해 초기 가용 블록 생성
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)         //실패하면 -1 리턴
    {
        return -1;
    }
    return 0;
}

/*
 * extend_heap(words) : 워드 단위 메모리를 인자로 받아, 새 가용 블록으로 힙을 확장한다.
 */
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    // 더블 워드 정렬에 따라 mem_sbrk함수로 추가 힙 메모리를 할당받는다.
    size = (words % 2) ? (words + 1) * WSIZE : (words)*WSIZE; 
    if ((long)(bp = mem_sbrk(size)) == -1)
    {   // brk 포인터에 size만큼 더해서 힙을 늘림. 실패시 -1
        return NULL;
    }
    // 가용 블록의 헤더와 풋터, 에필로그 헤더를 초기화
    PUT(HDRP(bp), PACK(size, 0));         // 가용 블록의 헤더 - 초기에는 할당 비트를 0(free)으로 준다.
    PUT(FTRP(bp), PACK(size, 0));         // 가용 블록의 풋터
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); // 새 에필로그 헤더 - 다음 sbrk 호출 시 새로운 가용블록의 헤더가 됨

    // 이전 블록이 가용하다면 coalesce
    return coalesce(bp);
}

/*
 * mm_malloc(size) : 요청 받은 메모리 사이즈를 인접한 8의 배수로 올려 할당한다.
 *                   만약 맞는 크기의 가용 블록이 없다면 추가 힙 메모리를 확장 & 할당한다.
 */
void *mm_malloc(size_t size)
{
    size_t asize;      // 할당할 메모리 사이즈
    size_t extendsize; // 맞는 크기의 free 블록이 없을 시 추가 요청할 메모리 사이즈
    char *bp;

    // 무의미한 malloc 요청 시
    if (size == 0)
    {
        return NULL;
    }
    // 요청한 size를 가까운 8의 배수로 round up
    asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);

    // 사이즈 맞는 가용 블록 찾기 (first fit)
    if ((bp = find_fit(asize)) != NULL)
    {                     
        place(bp, asize); 
        return bp;
    }

    
    // 맞는 가용 블록이 없을 때,
    // 힙을 새로운 가용 블록으로 확장하고,
    // 요청한 블록을 가용 블록에 배치한다.
    extendsize = MAX(asize, CHUNKSIZE); // 할당 요청 사이즈가 CHUNKSIZE보다 클 수 있어서, 둘 중 더 큰 값으로 사이즈를 정한다.
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}

/*
 * mm_realloc(ptr, size) - 요청한 사이즈만큼 재할당한다.
 */
void *mm_realloc(void *bp, size_t size)
{
    void *oldptr = bp;                          // 크기를 조절하고 싶은 힙의 시작 포인터
    void *newptr = mm_malloc(size);             // 크기 조절 뒤의 새 힙의 시작 포인터
    size_t copySize = GET_SIZE(HDRP(oldptr));   // 복사할 힙의 크기
    
    // 요청 사이즈 = 0 이면 free와 동일하다.
    if (size == 0)
    {
        mm_free(oldptr);
        return 0;
    }

    // 기존 메모리의 포인터가 아직 할당 전이면
    // malloc과 동일하다.
    if (oldptr == NULL)
    {
        return mm_malloc(size);
    }

    // 힙 사이즈가 충분하지 않아서 재할당이 불가능하면 NULL 반환
    if (newptr == NULL)
    {
        return NULL;
    }

    // 재할당 시작
    // 원래 메모리 크기보다 적은 크기를 realloc하면 크기에 맞는 메모리만 할당되고 나머지는 안 된다.
    if (size < copySize)                // 재할당할 size가 원래보다 더 작으면
    { 
        copySize = size;                // 이전 사이즈를 재할당할 사이즈로 줄임. 나머지는 free될 예정
    }
    memcpy(newptr, oldptr, copySize);   // newptr에 oldptr를 시작으로 copySize만큼의 메모리 값을 복사한다.
    mm_free(oldptr);                    // 기존의 힙을 반환한다.
    return newptr;
}

/*
 * find_fit(size) : 힙의 맨 처음부터 탐색, 제일 처음 발견된 요구하는 메모리 공간보다 큰 가용 블록의 주소를 반환한다.
 */
static void *find_fit(size_t asize)
{
   
    void *bp;

    // free list의 맨 뒤는 프롤로그 블록
    // Free list에서 유일하게 할당된 블록 - 종료 조건
    for (bp = free_listp; GET_ALLOC(HDRP(bp)) != 1; bp = SUCC_FREEP(bp))
    {   // first fit
        if (asize <= GET_SIZE(HDRP(bp))) 
        {
            return bp;
        }
    }

    // 못 찾으면 NULL을 리턴한다.
    return NULL;
}

/*
 * place(bp, size) : 할당할 수 있는 free 블록을 free list에서 없애준다.
 *   할당 후 남는 부분이 분할되었다면 새롭게 free list에 추가한다.
 */
static void place(void *bp, size_t asize)
{
    // 현재 할당할 수 있는 후보 가용 블록의 주소
    size_t csize = GET_SIZE(HDRP(bp));

    // 할당될 블록이므로 free list에서 제거
    removeBlock(bp);

    // 남는 부분이 가용블록이 될 수 있다면 분할한다.
    if ((csize - asize) >= (2 * DSIZE))
    {
        // 앞의 블록은 할당 블록으로
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        // 뒤의 블록은 가용 블록으로 분할한다.
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));

        // free list 첫번째에 분할된 블럭을 넣는다.
        putFreeBlock(bp);
    }
    // 남는 부분이 가용블록이 될 수 없다면 분할하지 않는다.
    else
    {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/*
 * mm_free(bp) - size와 할당 정보를 초기화한다.
 */
void mm_free(void *bp)
{
    // 해당 블록의 size를 알아내 header와 footer의 정보를 수정한다.
    size_t size = GET_SIZE(HDRP(bp));

    // header와 footer를 설정
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));

    // 4가지 case에 따라 coalescing을 진행
    coalesce(bp);
}

/*
 * coalesce(bp) : 현재 가용 블록을 앞뒤 가용 블록과 연결해서 free list에 반영
 */
static void *coalesce(void *bp)
{
    // 이전,다음 블록의 가용 여부에 따라 4가지 케이스로 나누어 coalesce를 진행한다.
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); // 직전 블록 가용 여부
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); // 직후 블록 가용 여부
    size_t size = GET_SIZE(HDRP(bp));

    // case 2 : 직전 allocated, 직후 free
    if (prev_alloc && !next_alloc)
    {
        // 직후 블록을 free list에서 제거한다. (합쳐진 free블록으로 다시 들어간다.)
        removeBlock(NEXT_BLKP(bp));     
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    // case 3 : 직전 free, 직후 allocated
    else if (!prev_alloc && next_alloc)
    {
        removeBlock(PREV_BLKP(bp));     
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        bp = PREV_BLKP(bp);
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    // case 4 : 직전, 직후 모두 free
    else if (!prev_alloc && !next_alloc)
    {
        removeBlock(PREV_BLKP(bp));
        removeBlock(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        bp = PREV_BLKP(bp);
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    // case 1 : 직전, 직후 모두 allocated -> 해당 블록만 free list에 넣어주면 된다.
    // 연결된 새 가용 블록을 free list에 추가한다.
    putFreeBlock(bp);
    return bp;
}

/*
 *   putFreeBlock(bp) : 새로운 free 블록을 free list의 첫 부분에 넣는다. (LIFO 순서)
 */
void putFreeBlock(void *bp)
{
    SUCC_FREEP(bp) = free_listp;
    PREC_FREEP(bp) = NULL;
    PREC_FREEP(free_listp) = bp;
    free_listp = bp;
}

/*
 *  removeBlock(bp) : 할당되거나 연결되는 가용 블록을 free list에서 없앤다.
 */
void removeBlock(void *bp)
{
    // free list의 첫번째 블록을 없앨 때
    if (bp == free_listp)
    {
        PREC_FREEP(SUCC_FREEP(bp)) = NULL;
        free_listp = SUCC_FREEP(bp);
    }
    // free list 안에서 없앨 때
    else
    {
        SUCC_FREEP(PREC_FREEP(bp)) = SUCC_FREEP(bp);
        PREC_FREEP(SUCC_FREEP(bp)) = PREC_FREEP(bp);
    }
}
