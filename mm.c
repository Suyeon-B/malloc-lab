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
    "Coding JJangJJang",
    /* First member's full name */
    "Kongal is cute",
    /* First member's email address */
    "><",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};

/* single word (4) or double word (8) alignment */
// #define ALIGNMENT 8

// /* rounds up to the nearest multiple of ALIGNMENT */
// #define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)
// DSIZE * ((sizeof(size_t) + (DSIZE) + (DSIZE - 1)) / DSIZE);

// #define SIZE_T_SIZE (DSIZE * ((sizeof(size_t) + (DSIZE) + (DSIZE - 1)) / DSIZE))

/*
 * 기본 상수와 매크로 (매크로가 뭔지 알아보기)
 */
#define WSIZE 4             /* 워드, 헤더/푸터 사이즈 (bytes) */
#define DSIZE 8             /* 더블워드 사이즈 (bytes) */
#define CHUNKSIZE (1 << 12) /* 힙 사이즈 CHUNK 만큼 확장 (bytes) 4GB(1<<32)를 최대 블록 크기로 두고,   */

#define MAX(x, y) ((x) > (y) ? (x) : (y)) /* 왜 괄호치는지 알아보기 */

/* 워드에 사이즈와 할당된 비트를 통합해서, header와 footer에 저장할 수 있는 값을 리턴 */
#define PACK(size, alloc) ((size) | (alloc))

/* p가 참조하는 워드를 읽어서 리턴 (여기서 캐스팅이 중요하다는데 왜인지 알아보기) */
#define GET(p) (*(unsigned int *)(p)) /* 문법 다시 보기 */
#define PUT(p, val) (*(unsigned int *)(p) = (val))

/* 주소 p에 있는 header 또는 footer의 사이즈와 할당 비트를 리턴 */
#define GET_SIZE(p) (GET(p) & ~0x7) /* NOT 연산자로 SIZE만 뽑아오기 위해 */
#define GET_ALLOC(p) (GET(p) & 0x1) /* 0x1과 곱해서 끝 자리가 여전히 1이라면 allocated */

/* 블록 포인터 bp가 주어지면,
 * HDRP와 FTRP매크로는 주소를 계산해서
 * 각각 블록 헤더와 풋터를 가리키는 포인터를 리턴한다.
 */
#define HDRP(bp) ((char *)(bp)-WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/*
 * 블록 포인터 bp가 주어지면,
 * 다음 혹은 이전 블록의 주소를 계산해서
 * 포인터를 리턴한다.
 */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp)-WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp)-GET_SIZE(((char *)(bp)-DSIZE)))

/* 처음에 쓸 가용 블록 힙 */
static char *heap_listp;

/* case 1~4의 경우에 따른 coalesce */
static void *coalesce(void *bp)
{
    /* 이전,다음 블록의 가용 여부에 따라 4가지 케이스로 나누어 coalesce를 진행한다. */
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    /* case 1 */
    if (prev_alloc && next_alloc)
    {
        return bp;
    }
    /* case 2 */
    else if (prev_alloc && !next_alloc)
    {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    /* case 3 */
    else if (!prev_alloc && next_alloc)
    {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0)); /* footer의 ptr를 구할 때 header포인터가 반영되므로 먼저 구함 */
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    /* case 4 */
    else
    {
        size += (GET_SIZE(FTRP(NEXT_BLKP(bp))) + GET_SIZE(HDRP(PREV_BLKP(bp))));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    return bp;
}

/*
 * 새 가용 블록으로 힙을 확장하는 함수
 */
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    /* 정렬 조건을 유지하기 위해 짝수 개의 워드만큼 할당한다. */
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
    { /* brk 포인터에 size만큼 더해서 힙을 늘리거나 줄임. 실패시 -1 */
        return NULL;
    }
    /* 가용 블록의 헤더와 풋터, 에필로그 헤더를 초기화 */
    PUT(HDRP(bp), PACK(size, 0));         /* 가용 블록의 헤더 - 초기에는 할당 비트를 0으로 준다. */
    PUT(FTRP(bp), PACK(size, 0));         /* 가용 블록의 풋터 */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* 새로운 에필로그 헤더, 다음 sbrk 호출 시 새로운 가용블록의 헤더가 됨 */

    /* 이전 블록이 가용하다면 Coalesce */
    return coalesce(bp);
}

/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    /* 초기 빈 힙 생성 */
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
    {
        return -1;
    }
    PUT(heap_listp, 0);                            /* alignment용 unused padding워드 */
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); /* 프롤로그 헤더 */
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); /* 프롤로그 풋터 */
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));     /* 에필로그 헤더 */
    heap_listp += (2 * WSIZE);

    /* CHUNKSIZE/WSIZE 만큼 빈 힙을 확장 */
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
    {
        return -1;
    }
    return 0;
}

/*
 * 할당할 사이즈에 맞는 가용 블록을 찾는 함수
 */
static void *find_fit(size_t asize)
{
    void *bp;
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
    {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
        {
            return bp;
        }
    }
    return NULL;
}

/*
 * 가용 블록에 할당해주는 함수.
 * 찾은 가용블록에 할당하고 남은 부분이
 * 또 다른 가용블록이 될 수 있을 때는 분할한다.
 */
static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));
    /* 남는 부분이 가용블록이 될 수 없다면 분할하지 않는다. */
    if ((csize - asize) < 2 * DSIZE)
    {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
    /* 남는 부분이 가용블록이 될 수 있다면 분할한다. */
    else
    {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
    }
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    /* 원래 있던 ver. */
    /* int newsize = ALIGN(size + SIZE_T_SIZE);
    void *p = mem_sbrk(newsize);
    if (p == (void *)-1)
    return NULL;
    else {
        *(size_t *)p = size;
        return (void *)((char *)p + SIZE_T_SIZE);
    } */

    size_t asize;      /* 할당된 블록 사이즈 */
    size_t extendsize; /* 맞는 블록이 없으면 힙에 추가로 요청할 사이즈 */
    char *bp;

    /* 의미 없는 malloc 요청 시 */
    if (size == 0)
    {
        return NULL;
    }

    /* 오버헤드와 정렬 조건을 고려해서,
     * 인접 8의 배수로 반올림하여
     * 필요한 블록 사이즈를 결정 */
    if (size <= DSIZE)
    {
        asize = 2 * DSIZE;
    }
    else
    {
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE); /* whyrano.. */
    }

    /* 맞는 가용 블록 찾기 */
    if ((bp = find_fit(asize)) != NULL)
    {
        place(bp, asize);
        return bp;
    }

    /* 맞는 가용 블록이 없을 때,
     * 힙을 새로운 가용 블록으로 확장하고,
     * 요청한 블록을 가용 블록에 배치한다. */
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
    { /* whywhywhy */
        return NULL;
    }
    place(bp, asize);
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));

    /* 헤더와 풋터에 payload가 없음을 나타냄 */
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *bp, size_t size)
{
    void *oldptr = bp;
    void *newptr = mm_malloc(size);
    size_t copySize = GET_SIZE(HDRP(oldptr));

    if (newptr == NULL)
    {
        return NULL;
    }
    if (size < copySize)
    {
        copySize = size;
    }
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;

    // void *oldptr = bp;

    // /* 요청 사이즈 <= 0 이면 반환을 해도 되니까 반환한다. */
    // if (size == 0) /* 이게 음수로 들어오는 경우는 왜? */
    // {
    //     mm_free(oldptr);
    //     return 0;
    // }
    // /* 기존 메모리의 포인터가 아직 할당 전이면
    //  * malloc과 동일하다. */
    // if (oldptr == NULL)
    // {
    //     return mm_malloc(size);
    // }

    // /* 힙 사이즈가 충분하지 않아서 재할당이 불가능하면 */
    // void *newptr = mm_malloc(size);
    // if (newptr == NULL)
    // {
    //     return 0;
    // }

    // /* 재할당 시작 */
    // size_t copySize = GET_SIZE(HDRP(oldptr));
    // if (size < copySize) /* 재할당할 size가 원래보다 더 작으면 */
    // {
    //     copySize = size; /* 이전 사이즈를 재할당할 사이즈로 줄임. 나머지는 free될 예정 */
    // }
    // /* memcpy(dest, source, num)
    //  * source의 메모리에 있는 값들을 num 길이만큼 dest에 복사해서 붙여넣는다. */
    // memcpy(newptr, oldptr, copySize);
    // mm_free(oldptr);
    // return newptr;
}
