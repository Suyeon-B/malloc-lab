#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

team_t team = {
    /* Team name */
    "team 9",
    /* First member's full name */
    "Kim Dokyung",
    /* First member's email address */
    "dkkim0122@gmail.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};

#define WSIZE sizeof(void *) // word, header, footer 사이즈(byte)
#define DSIZE (2 * WSIZE)    // double word 사이즈(byte)
#define CHUNKSIZE (1 << 12)  // heap 확장 사이즈(byte)
#define MINIMUM 24           // heap 확장 사이즈(byte)

#define MAX(x, y) ((x) > (y) ? (x) : (y))

#define PACK(size, alloc) ((size) | (alloc)) // 사이즈와 할당된 비트를 word로 압축

#define GET(p) (*(unsigned int *)(p))              // 해당 주소 안에 실제 값 불러오기
#define PUT(p, val) (*(unsigned int *)(p) = (val)) // 해당 주소 안의 실제 값 저장하기

#define GET_SIZE(p) (GET(p) & ~0x7) // '... 1111 1000'과 AND 연산하여 block의 사이즈 확인하기
#define GET_ALLOC(p) (GET(p) & 0x1) // '... 0000 0001'과 AND 연산하여 block의 할당 여부 확인하기

#define HDRP(bp) ((char *)(bp)-WSIZE)                        // block pointer를 받아 header 포인터 확인하기
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) // block pointer를 받아 footer 포인터 확인하기

#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp)-WSIZE))) // 다음 block의 block pointer로 이동하기
#define PREV_BLKP(bp) ((char *)(bp)-GET_SIZE(((char *)(bp)-DSIZE)))   // 이전 block의 block pointer로 이동하기

/* freeList의 이전 포인터와 다음 포인터 계산 */
#define NEXT_FLP(bp) (*((void **)(bp) + 1)) // 다음 free list 요소의 bp를 가져옴
#define PREV_FLP(bp) (*((char **)(bp)))     // 이전 free list 요소의 bp를 가져옴

static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static void add_free(void *bp);
static void del_free(void *bp);

static char *heap_listp; // 힙의 시작점을 나타내는 포인터
static char *free_listp; // free block들의 시작점을 나타내는 포인터

int mm_init(void)
{
    /* explicit 초기 힙은 6word */
    if ((heap_listp = mem_sbrk(6 * WSIZE)) == (void *)-1)
    {
        return -1;
    }

    PUT(heap_listp, 0);                              // 미사용 패딩
    PUT(heap_listp + (1 * WSIZE), PACK(MINIMUM, 1)); // prologue block hdr
    PUT(heap_listp + (2 * WSIZE), NULL);             // pred
    PUT(heap_listp + (3 * WSIZE), NULL);             // succ
    PUT(heap_listp + (4 * WSIZE), PACK(MINIMUM, 1)); // prologue block ftr
    PUT(heap_listp + (5 * WSIZE), PACK(0, 1));       // epilogue block hdr

    free_listp = heap_listp + (2 * WSIZE); // free listp의 탐색 시작점을 pred로 둔다.

    /* 초기 힙 설정 후 CHUNKSIZE/WSIZE 만큼 힙을 확장해 초기 가용 블록 생성 */
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
    {
        /* 실패 시 -1 */
        return -1;
    }
    return 0;
}

void *mm_malloc(size_t size)
{
    size_t adjust_size;
    size_t extend_size;
    char *bp;

    /* 의미 없는 size 요청 시 */
    if (size == 0)
    {
        return NULL;
    }

    /* 요청한 size를 가까운 8의 배수로 round up */
    if (size <= DSIZE)
    {
        adjust_size = 2 * DSIZE;
    }
    else
    {
        adjust_size = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);
    }

    /* 맞는 가용 블록 찾기 */
    if ((bp = find_fit(adjust_size)) != NULL)
    {
        place(bp, adjust_size);
        return bp;
    }

    /* 맞는 가용 블록이 없을 때,
     * 힙을 새로운 가용 블록으로 확장하고,
     * 요청한 블록을 가용 블록에 배치한다. */
    extend_size = MAX(adjust_size, CHUNKSIZE);
    if ((bp = extend_heap(extend_size / WSIZE)) == NULL)
    {
        return NULL;
    }
    place(bp, adjust_size);
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
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;

    newptr = mm_malloc(size);
    /* 의미 없는 요청 시 */
    if (newptr == NULL)
    {
        return NULL;
    }

    // 복사해 올 메모리 사이즈
    copySize = GET_SIZE(HDRP(oldptr));
    /* 원래 메모리 크기보다 작은 사이즈를 realloc하면 크기에 맞는 메모리만 할당되고 나머지는 안 된다. */
    if (size < copySize)
    {
        copySize = size;
    }
    memcpy(newptr, oldptr, copySize); // newptr에 oldptr를 시작으로 copySize만큼의 메모리 값을 복사한다.
    mm_free(oldptr);
    return newptr;
}

/*
 * 워드 단위 메모리를 인자로 받아 힙을 늘려준다.
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
    PUT(HDRP(bp), PACK(size, 0)); /* 가용 블록의 헤더 - 초기에는 할당 비트를 0으로 준다. */
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    return coalesce(bp);
}

static void *coalesce(void *bp)
{
    /* 직전/직후 블복의 가용 여부에 따라
     * case 1~4로 나누어 coalesce 진행 */
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); // 직전 블록 가용 여부
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); // 직후 블록 가용 여부
    size_t size = GET_SIZE(HDRP(bp));

    /* case 2 - 직전 allocated, 직후 free */
    if (prev_alloc && !next_alloc)
    {
        // free 상태였던 직후 블록을 free list에서 제거
        del_free(NEXT_BLKP(bp));

        // 현재 블록을 free 상태로 바꿈
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    /* case 3 - 직전 allocated, 직후 free */
    else if (!prev_alloc && next_alloc)
    {
        // free 상태였던 직후 블록을 free list에서 제거
        del_free(PREV_BLKP(bp));

        // 현재 블록을 free 상태로 바꿈
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    /* case 4 - 직전, 직후 모두 free */
    else if (!prev_alloc && !next_alloc)
    {
        del_free(PREV_BLKP(bp));
        del_free(NEXT_BLKP(bp));

        size += (GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp))));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    /* case 1 - 직전, 직후 블록 모두 allocated -> 해당 블록만 free list에 넣어준다. */
    add_free(bp);
    return bp;
}

static void *find_fit(size_t asize)
{
    /* first-fit */
    void *bp;

    /* free list의 맨 뒤는 prologue block
     * free list에서 유일하게 할당된 블록이므로,
     * 프롤로그 블록이 탐색의 종료 지점이다. */
    for (bp = free_listp; !GET_ALLOC(HDRP(bp)); bp = NEXT_FLP(bp))
    {
        if (asize <= GET_SIZE(HDRP(bp)))
        {
            return bp;
        }
    }
    return NULL;
}

/*
 * fit한 free 블록을 찾았을 때
 * 힙에 메모리를 할당해주는 함수
 */
static void place(void *bp, size_t asize)
{

    int cur_size = GET_SIZE(HDRP(bp)); // find fit으로 찾은 free 블록의 사이즈
    del_free(bp);                      // place함수를 통해 할당될 블록이므로 free list에서 없앤다.

    /* 남는 부분이 가용블록이 될 수 있다면 분할한다. */
    if (cur_size - asize >= MINIMUM)
    {
        /* 앞 부분은 할당 */
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        /* 뒷 부분은 분할해서 free로 둠 */
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(cur_size - asize, 0));
        PUT(FTRP(bp), PACK(cur_size - asize, 0));
        /* 새로 생긴 가용 블록을 free list에 추가 */
        add_free(bp);
    }
    /* 남는 부분이 가용블록이 될 수 없다면 분할하지 않는다. */
    else
    {
        PUT(HDRP(bp), PACK(cur_size, 1));
        PUT(FTRP(bp), PACK(cur_size, 1));
    }
}

static void add_free(void *bp)
{
    /* free_listp는 free list의 첫 주소를 가리키므로,
     * free_listp가 가리키는 free list 안의 블록과
     * PRED, SUCC 링크를 진행한다. */
    NEXT_FLP(bp) = free_listp; // 기존의 first free bp를 새로운 가용 블록의 다음 블록으로 연결한다.
    PREV_FLP(bp) = NULL;       // 새로운 가용 블록의 pred는 null
    PREV_FLP(free_listp) = bp; // 기존 블록의 앞에 새로운 가용 블록을 연결한다.
    free_listp = bp;
}

static void del_free(void *bp)
{
    /* first free block을 지우려고 할 때 */
    if (bp == free_listp)
    {
        // 다음 free block을 first로 바꿔준다.
        PREV_FLP(NEXT_FLP(bp)) = NULL;
        free_listp = NEXT_FLP(bp);
    }
    else
    {
        NEXT_FLP(PREV_FLP(bp)) = NEXT_FLP(bp);
        PREV_FLP(NEXT_FLP(bp)) = PREV_FLP(bp);
    }
}