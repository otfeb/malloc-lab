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
    "team 1",
    /* First member's full name */
    "HoSeok",
    /* First member's email address */
    "hs970216@naver.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* 기본 상수 정의 */
/* 워드와 헤더/풋터의 크기 (4 byte) */
#define WSIZE 4
/* 더블 워드의 크기 (8 byte) */
#define DSIZE 8
/* 초기 가용 블록과 힙 확장을 위한 기본 크기 단위 (2^12 = 4KB 분량) */
#define CHUNKSIZE (1 << 12)

/* 매크로 정의 */
/* 두 값을 비교하여 큰 값을 반환 */
#define MAX(x, y) (x > y ? x : y)
/* 크기와 할당 비트를 통합해서 헤더와 풋터에 저장할 수 있는 값을 반환 */
#define PACK(size, alloc) (size | alloc)
/* 인자 p가 참조하는 워드를 읽어서 반환 (포인터라서 직접 역참조 불가 -> 타입 변환) */
#define GET(p) (*(unsigned int *)(p))
/* 인자 p가 가리키는 워드에 val을 저장 */
#define PUT(p, val) (*(unsigned int *)(p) = (val))
/* 주소 p에 있는 헤더 또는 풋터의 크기를 반환 */
#define GET_SIZE(p) (GET(p) & ~0x7)
/* 주소 p에 있는 할당 비트를 반환 */
#define GET_ALLOC(p) (GET(p) & 0x1)
/* 블록 포인터 bp가 주어지면 블록 헤더를 가리키는 포인터를 반환 */
#define HDRP(bp) ((char *)(bp)-WSIZE)
/* 블록 포인터 bp가 주어지면 블록 풋터를 가리키는 포인터를 반환 */
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)
/* 다음 블록의 블록 포인터를 반환 */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp)-WSIZE)))
/* 이전 블록의 블록 포인터를 반환 */
#define PREV_BLKP(bp) ((char *)(bp)-GET_SIZE(((char *)(bp)-DSIZE)))

/* explicit list 용 매크로 */
/* 다음 가용 블록의 주소 */
#define GET_SUCC(bp) (*(void**)((char *)(bp) + WSIZE))
/* 이전 가용 블록 주소 */
#define GET_PRED(bp) (*(void**)(bp))

/* 헤더파일에 없는 메소드라서 전방 선언 */
static void *extend_heap(size_t words);
static void *coalaesce(void *bp);
static void *find_fit(size_t size);
static void place(void *bp, size_t asize);

static void splice_free_block(void *bp);
static void add_free_block(void *bp);

// static void *heap_currp;
static char *heap_listp;

int mm_init(void)
{
    /* 힙 초기화 , 8 word 크기 할당 , 할당 실패시 -1 반환 */
    if ((heap_listp = mem_sbrk(8 * WSIZE)) == (void *)-1)
        return -1;

    /* 더블 워드 정렬을 위한 미사용 패딩 */
    PUT(heap_listp, 0);
    /* 프롤로그 블록의 헤더 */
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1));
    /* 프롤로그 블록의 풋터 */
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1));
    /* 첫 가용 블록의 헤더 */
    PUT(heap_listp + (3 * WSIZE), PACK(4*WSIZE, 0));
    /* 이전 가용 블록 주소 */
    PUT(heap_listp + (4 * WSIZE), NULL);
    /* 다음 가용 블록 주소 */
    PUT(heap_listp + (5 * WSIZE), NULL);
    /* 첫 가용 블록의 풋터 */
    PUT(heap_listp + (6 * WSIZE), PACK(4*WSIZE, 0));
    /* 에필로그 블록의 헤더 */
    PUT(heap_listp + (7 * WSIZE), PACK(0, 1));

    /* 첫 번째 가용 블록의 bp */
    heap_listp += (4 * WSIZE);

    // heap_currp = heap_listp;

    /* 힙을 CHUNKSIZE 바이트로 확장 (4KB) */
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;
    return 0;
}

/* 힙 영역 확장 */
static void *extend_heap(size_t words){
    char *bp;
    size_t size;

    /* 정렬을 위해 짝수 개의 워드 할당 */
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    /* 가용 블럭의 헤더/풋터와 에필로그 헤더 초기화 */
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    /* 인접 블록이 가용 블록이면 합친다 */
    return coalaesce(bp);
}


/* 블록 합치기 */
static void *coalaesce(void *bp){
    /* 이전 블록(footer)이 할당인지 가용인지 체크 (prev_alloc 변수에는 0 or 1) */
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    /* 다음 블록(header)이 할당인지 가용인지 체크 (next_alloc 변수에는 0 or 1) */
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    /* 현재 블록(header)의 사이즈 */
    size_t size = GET_SIZE(HDRP(bp));

    /* Case 1. 인접 블록이 모두 할당일 때 */
    if(prev_alloc && next_alloc){
        add_free_block(bp);
        return bp;
    }
    /* Case 2. 이전 블록은 할당, 다음 블록은 가용일 때 */
    else if(prev_alloc && !next_alloc){
        splice_free_block(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    /* Case 3. 이전 블록은 가용, 다음 블록은 할당일 때 */
    else if(!prev_alloc && next_alloc){
        splice_free_block(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        /* case2 와 다르게 이전 블록과 합쳐졌으므로 bp를 이전 블록으로 이동 */
        bp = PREV_BLKP(bp);
    }
    /* Case 4. 인전 블록이 모두 가용일 때 */
    else{
        splice_free_block(PREV_BLKP(bp));
        splice_free_block(NEXT_BLKP(bp));
        /* 현재 블록의 사이즈와 두 인접 블록의 사이즈의 합 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    // heap_currp = bp;
    add_free_block(bp);
    return bp;
}

void *mm_malloc(size_t size)
{
    size_t asize;       // 조정된 블록 사이즈
    size_t extendsize;  // 확장할 사이즈
    char *bp;

    /* 잘못된 요청 처리 */
    if(size == 0)
        return NULL;

    /* 사이즈 조정 */
    if(size <= DSIZE)       // 8 byte 이하
        /* 최소 블록 크기 16바이트 할당 (헤더 4 + 풋터 4 + 데이터 8) */
        asize = 2 * DSIZE;
    else
        asize = DSIZE * ((size + DSIZE + DSIZE - 1) / DSIZE);

    /* 가용 블록 검색 */
    if((bp = find_fit(asize)) != NULL){
        place(bp, asize);      // 할당
        return bp;             // 새로 할당된 블록의 포인터 리턴
    }

    /* 적합한 블록이 없을 경우 힙 확장 */
    extendsize = MAX(asize, CHUNKSIZE);
    if((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;

    // int newsize = ALIGN(size + SIZE_T_SIZE);
    // void *p = mem_sbrk(newsize);
    // if (p == (void *)-1)
	// return NULL;
    // else {
    //     *(size_t *)p = size;
    //     return (void *)((char *)p + SIZE_T_SIZE);
    // }
}

static void *find_fit(size_t size){
    /* first fit 검색이므로 힙의 처음부터 가용 블록을 찾으며 인자값인 size보다 크거나 같은 가용 블록을 찾으면 그 가용 블록 bp주소를 반환 */
    void *bp = heap_listp;

    while(bp != NULL){
        if((size <= GET_SIZE(HDRP(bp)))){
            return bp;
        }
        bp = GET_SUCC(bp);
    }
    return NULL;
}

static void place(void *bp, size_t asize){
    splice_free_block(bp);

    size_t curr_size = GET_SIZE(HDRP(bp));  // 찾은 가용 블록 크기

    /* 둘의 차이가 최소 16보다 같거나 크면 분할 */
    if((curr_size - asize) >= (2 * DSIZE)){
        PUT(HDRP(bp), PACK(asize, 1));      // 현재 블록에서는 필요한 만큼만 할당
        PUT(FTRP(bp), PACK(asize, 1));

        PUT(HDRP(NEXT_BLKP(bp)), PACK((curr_size - asize), 0));     // 남은 크기는 가용 블록으로 설정
        PUT(FTRP(NEXT_BLKP(bp)), PACK((curr_size - asize), 0));
        add_free_block(NEXT_BLKP(bp));
    }
    else{
        PUT(HDRP(bp), PACK(curr_size, 1));       // 해당 블록 전부 할당
        PUT(FTRP(bp), PACK(curr_size, 1));
    }
}

static void splice_free_block(void *bp){
    if(bp == heap_listp){
        heap_listp = GET_SUCC(heap_listp);
        return;
    }
    GET_SUCC(GET_PRED(bp)) = GET_SUCC(bp);
    if(GET_SUCC(bp) != NULL)
        GET_PRED(GET_SUCC(bp)) = GET_PRED(bp);
}

static void add_free_block(void *bp){
    GET_SUCC(bp) = heap_listp;
    if(heap_listp != NULL)
        GET_PRED(heap_listp) = bp;
    heap_listp = bp;
}

/* 현재 ptr의 블록을 가용 상태로 만들고 인접 블록 중 가용 상태의 블록이 있는지 확인하고 있으면 합쳐준다 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalaesce(bp);
}

/* malloc과 free함수만을 이용하여 구현 */
void *mm_realloc(void *ptr, size_t size)
{

    if(ptr == NULL)         // 포인터가 null인 경우 할당만 수행
        return mm_malloc(size);
    if(size == 0){           // size가 0인 경우 블록 반환만 수행
        mm_free(ptr);
        return 0;
    }

    void *newptr = mm_malloc(size);     // 새로 할당한 블록의 포인터
    if(newptr == NULL)
        return NULL;

    size_t copySize = GET_SIZE(HDRP(ptr)) - DSIZE;      // 데이터 영역만 복사
    if(size < copySize)                                 // 기존 사이즈가 재할당 크기보다 크면
        copySize = size;                                // 기존 사이즈로 크기 변경 (기존 사이즈가 더 크면, 일부 데이터만 복사)

    memcpy(newptr, ptr, copySize);                  // 새 블록으로 데이터 복사
    mm_free(ptr);                                   // 기존 블록 반환
    
    return newptr;

    /* defualt 코드 */

    // void *oldptr = ptr;
    // void *newptr;
    // size_t copySize;

    // newptr = mm_malloc(size);
    // if (newptr == NULL)
    //     return NULL;
    // copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    // if (size < copySize)
    //     copySize = size;
    // memcpy(newptr, oldptr, copySize);
    // mm_free(oldptr);
    // return newptr;
}