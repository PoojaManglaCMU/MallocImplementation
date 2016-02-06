/*
 * mm.c
 *
 * Dynamic Storage Allocator
 * ========================
 *
 * Author : Pooja Mangla
 * ======
 * Andrew ID: pmangla
 * =========
 *
 * Block:
 * ======
 * Each block has a minimum size of 16 bytes: First 4 bytes for reserved for header
 * Last 4 bytes are reserved for footer. 
 * In case of free blocks, the 4 bytes next to header contain the last 4 bytes of the address
 * of the predecessor block in the free block list and next 4 bytes contain the last 4 bytes of   
 * of the address of the  successor block in the free block list.
 * In case of an allocated block, the 8 bytes contain payload if the size is more than or equal to
 * the minimum block size else they contain payload and padding. 
 *
 * Optimizations to implicit free list allocator provided in textbook code:
 * ========================================================================
 * The dynamic storage allocator used here uses free block lists i.e. segregated list technique.
 * Free block lists are stored in an array of linked list for different sizes of free blocks. 
 * There is no limit on size of these linked lists 
 * freeblocklist[0] contains free blocks of size <=16
 * freeblocklist[1] : size between 2^4 to 2^5
 * freeblocklist[2] : size between 2^5 - 2^6 
 * and so on
 *
 * This reduces the number of searched required for a free block as now the allocator will only search 
 * in a particular linked list based on size of the block required which further results in increase in 
 * throughput.
 *
 * Coalescing:
 * ==========
 * Coalescing is performed to coalesce adjacent free blocks which decreases external fragmentation further 
 * increasing memory utilization.
 *
 * Fit: 
 * ====
 * Memory allocation is done using first fit model. When a memory block is requested, first appropriate list
 * from the lists of free block lists is selected and then a free block of appropriate size is allocated from
 * that list.
 * 
 * Splitting
 * =========
 * If (size of free block - requested block size) >  MinBlockSize(16) we split the block and allocate. Also the 
 * remaining block is restored back in the appropriate free list.
 *
 * Free:
 * =====
 *Freeing a block is essentially changing the allocated bits to free bits
 * and add the block in appropriate free list.  
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "mm.h"
#include "memlib.h"

/* If you want debugging output, use the following macro.  When you hand
 * in, remove the #define DEBUG line. */
#define DEBUG
#ifdef DEBUG
# define dbg_printf(...) printf(__VA_ARGS__)
#else
# define dbg_printf(...)
#endif


/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(p) (((size_t)(p) + (ALIGNMENT-1)) & ~0x7)


/* Basic Constants/Macros */

#define WSIZE 4 /* Word and header/footer size (bytes) */
#define DSIZE 8 /* Double word size (bytes) */

#define CHUNKSIZE (1<<9)

#define SEGLIST 12// number of segregated free list
#define MINBLOCKSIZE 16

#define MAX(x, y) ((x) > (y)? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc))

 /* Read and write a word at address p */
#define GET(p) (*(unsigned *)(p))
#define PUT(p, val) (*(unsigned *)(p) = (intptr_t)(val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* from  bp, get previous and next free blocks addresses */
#define SUCC(bp)   ((char *) ((char*)(bp)))
#define PRED(bp)   ((char *) ((char*)(bp) + WSIZE))

/*Help Functions*/
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void insertseglist(void *ptr, size_t size);
static void deletefromseglist(void *ptr);
static void checkblock(void *bp);
static void *findvalidfit(size_t size, int index);
static long checkfreeblocks();
/*Global variables*/
char* heap_listp;
char *freelist;
char *head=(char *)0x800000000;

/*`
 * Initialize: return -1 on error, 0 on success.
 * Initializes the free list 
 * Sets prologue and epilogue blocks and gets some memory using mem_sbrk()
 */
int mm_init(void) {
	
	int i;
	char *bp;
	if((freelist = mem_sbrk(SEGLIST*WSIZE)) == NULL){
		return -1;
	} 
// initialize free list
	for(i=0; i<=SEGLIST; i++)
	{
		PUT(freelist+WSIZE*i, NULL);
	}

	// create initial empty heap
	if((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1){
		return -1;
	}
	
	PUT(heap_listp, 0);			   // Alignemnt padding
	PUT(heap_listp+(1*WSIZE), PACK(DSIZE,1));  // Prologue header
	PUT(heap_listp+(2*WSIZE), PACK(DSIZE,1));  // Prologue footer
	PUT(heap_listp+(3*WSIZE), PACK(0,1));	   // EPilogue header

	heap_listp += (2*WSIZE);

	/* Extend the empty heap with block of CHUNKSIze bytes*/
	bp =extend_heap(CHUNKSIZE/WSIZE);
	if(bp ==NULL){
		return -1;
	}
	// divide  the new memory into small sgments and put into app list
	
	//check_heap(4);	
	 return 0;
}

/*
 *This is invoked in two different circumstances: 
 * (1) when  the heap is initialized, and
 * (2) when mm_malloc is unable to find a suitable fit.
 */
static void *extend_heap(size_t words){
	char *bp;
	size_t size;

	// allocate even number of words to maintain alignment
	size = (words%2)?((words+1)*WSIZE):(words*WSIZE);
	if((long)(bp = mem_sbrk(size))== -1){
		return (void *)0;
	}
	
	// initialize free block header
	PUT(HDRP(bp), PACK(size,0));// free block header
	PUT(FTRP(bp), PACK(size,0));// free block foother
	PUT(HDRP(NEXT_BLKP(bp)), PACK(0,1));// new epilogue header
	//mm_checkheap(4);
	insertseglist(bp, size);
	return coalesce(bp);	
}

/**
 * Inserts the free block into appropriate index in free list
 * FreelIst[0] size <=16
 * list[1] = 2^4 - 2^5
 * and so on 2^n to 2^n+1
 */
static void insertseglist(void *bp, size_t size){
	int index=0;
	void *liststart=NULL;// address of pointer pointing to head of 
			     // list cprresponding to the size	
	char *headstart;

	while((index < SEGLIST) && (size >MINBLOCKSIZE)){
	
		size >>=1;
		index++;
	}
	liststart = freelist + WSIZE*index;
	headstart = head+GET(liststart);

	if(GET(liststart) != 0){
		
		/* set current free block next to prev list
 		*  and current free block's prev to NULL
 		*  Also set prev head's prev pointer to current free block
 		*/
		PUT(liststart,  bp);
		PUT(PRED(bp), NULL);
		PUT(SUCC(bp), headstart);

		PUT(PRED(headstart), bp);
	}else{
		// there are no blocks in this size currently	
		// set free blocks's next and prev as NULL
		PUT(liststart, bp);
		PUT(SUCC(bp), NULL);
		PUT(PRED(bp), NULL);
	}
}


/**
 *1. The previous and next blocks are both allocated.
2. The previous block is allocated and the next block is free.
3. The previous block is free and the next block is allocated.
4. The previous and next blocks are both free.
 */
static void *coalesce(void *bp){
	size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
	size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));

	size_t size = GET_SIZE(HDRP(bp));

	// if both next and prev are allocated just return
	if(prev_alloc && next_alloc){
		return bp;
	}

	/*if prev is alloc and next is free then combine
 	*current with next and put the resulting block
 	*in appropriate list
 	*/ 
	
	if(prev_alloc && !next_alloc){
		size+=GET_SIZE(HDRP(NEXT_BLKP(bp)));	
		deletefromseglist(bp);
		deletefromseglist(NEXT_BLKP(bp));
		PUT(HDRP(bp), PACK(size,0));
		PUT(FTRP(bp), PACK(size,0));
		insertseglist(bp, size);
		return bp;		
	}else if(!prev_alloc && next_alloc){// case 3

		size+=GET_SIZE(HDRP(PREV_BLKP(bp)));
		deletefromseglist(bp);
		deletefromseglist(PREV_BLKP(bp));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size,0));
		PUT(FTRP(bp), PACK(size,0));
		insertseglist(PREV_BLKP(bp), size);
		return PREV_BLKP(bp);
	} else {
		size+=GET_SIZE(HDRP(PREV_BLKP(bp)))+
			GET_SIZE(HDRP(NEXT_BLKP(bp)));
		deletefromseglist(bp);
		deletefromseglist(PREV_BLKP(bp));
		deletefromseglist(NEXT_BLKP(bp));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size,0));
		PUT(FTRP(NEXT_BLKP(bp)), PACK(size,0));
		bp = PREV_BLKP(bp);
		insertseglist(bp,size);
		return bp;
	}
	return bp;
	
}

/**
 * Removes the free block from the app free list 
 * and update header of the list, next and prev elements 
 */
static void deletefromseglist(void *bp){
	int index=0;
	size_t size= GET_SIZE(HDRP(bp));
 	char *nextadd=head+GET(SUCC(bp));
	char *prevadd =head+GET(PRED(bp));	
	//get the index where bp is in list
	while((index < SEGLIST) && (size>MINBLOCKSIZE)){
		size>>=1;
		index++;
	}
	
	/* 1. bp is between 2 blocks just need to update prev and next elements
	 * of Prev and Next blocks.
	 * 2. If only prev elemet is there, then update prev elements next to NULL
	 */
	if(GET(PRED(bp)) !=0) {
		if(GET(SUCC(bp)) == 0){
			PUT(SUCC(prevadd), NULL);
		}else{
			PUT(SUCC(prevadd), nextadd);
			PUT(PRED(nextadd), prevadd);
		}
	}else{
	/**3. bp has no prev and next, then list is empty update head to NULL
 	* 4. bp has no rev then update Head of list to next element of bp
 	*/ 
		if(GET(SUCC(bp)) == 0){
			PUT(freelist+index*WSIZE, NULL);	
		}else{
			PUT(PRED(nextadd), NULL);
			PUT(freelist+WSIZE*index, nextadd);
    			
		}
	}
	//PUT(NEXT(bp),NULL);
	//PUT(PREV(bp),NULL);
}
/*
 * malloc
 */
void *malloc (size_t size) {
	size_t asize; /* Adjusted block size */
	size_t extendsize; /* Amount to extend heap if no fit */
	char *bp;
	//mm_checkheap(334);
	if (size == 0){
		return NULL;
	}

	/* Adjust block size to include overhead and alignment reqs. */
	if (size <=  DSIZE){
		asize=MINBLOCKSIZE;
	}else{
		// round up to the nearest
		//multiple of 8
		asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);
	}
	
	/* Search the free list for a fit */
	if ((bp = find_fit(asize)) != NULL) {
		place(bp, asize);
		return bp;
	}

	/* No fit found. Get more memory and place the block */
	extendsize = MAX(asize,CHUNKSIZE);
	if ((bp = extend_heap(extendsize/WSIZE)) == NULL){
		return NULL;
	}
	place(bp, asize);
        return bp;
}

/*
 * Finds the appropriate free list from where block should be allocated
 * Ifthere is no free block in that list, we start looking at next higher 
 * size free list
 */
static void *find_fit(size_t size){
	void *bp=NULL;
	size_t asize=size;
	int index=0;
	while((index<SEGLIST) && (size>MINBLOCKSIZE)){
		index++;
		size>>=1;
	}
	while(bp == NULL && index <=SEGLIST){
		bp = findvalidfit(asize, index);
		index++;
	}
	return bp;
}

/*
 * Finds the block in the corresponding free list
 */
static void *findvalidfit(size_t asize, int index){
	char *bp=NULL;
	unsigned int temp;
	temp=GET(freelist+WSIZE*index);
        while(temp !=0)
        {
		bp=head+temp;
		if(asize <= GET_SIZE(HDRP(bp))){
			return bp;
		}
		temp =GET(SUCC(bp));
		}
		return NULL;
}


/*
 *Deletes the bp from its free list and aloocate the block either by:
 * 1. dividing and inserting the smaller block into appropriate free list or
 * 2. Allocating the entire block if block size - req size is lesser than
 * Min block size
 */
static void place(void *bp, size_t asize){
	size_t bsize=GET_SIZE(HDRP(bp));// get block size
	
	deletefromseglist(bp);

	/* if block size - reqsize > MIN BLock size then divide the block
 	* and add the new block to app list otherwise just allocate the 
 	* entire block
 	*/ 
	if(bsize-asize > MINBLOCKSIZE){
		PUT(HDRP(bp), PACK(asize,1));
		PUT(FTRP(bp), PACK(asize,1));
		bp = NEXT_BLKP(bp);
		PUT(HDRP(bp), PACK(bsize-asize, 0));
		PUT(FTRP(bp), PACK(bsize - asize,0));
		// add the new block into app list
		insertseglist(bp, bsize-asize);
	}else{
		PUT(HDRP(bp), PACK(bsize,1));
		PUT(FTRP(bp), PACK(bsize,1));
	}	
}
/*
 * free : frees the pointer from allocated block list
 * Insert the free block in appropriate free list and 
 * coalescing.
 */
void free (void *ptr) {
	if(ptr == NULL){
		return;
	}

	size_t size =GET_SIZE(HDRP(ptr));
	PUT(HDRP(ptr), PACK(size,0));
	PUT(FTRP(ptr), PACK(size,0));
//	coalesce(ptr);
	insertseglist(ptr,GET_SIZE(HDRP(ptr)));
	coalesce(ptr);		
}

/*
 * realloc - you may want to look at mm-naive.c
 */
void *realloc(void *oldptr, size_t size) {
       	  size_t oldsize;
	  void *newptr;

	  /* If size == 0 then this is just free, and we return NULL. */
	  if(size == 0) {
	 	  free(oldptr);
	  	  return 0;
	  }

	  /* If oldptr is NULL, then this is just malloc. */
	  if(oldptr == NULL) {
	          return malloc(size);
          }

	  newptr = malloc(size);

	  /* If realloc() fails the original block is left untouched  */
	  if(!newptr) {
	  	   return 0;
 	  }

	  /* Copy the old data. */
	  oldsize = GET_SIZE(HDRP(oldptr));
	  if(size < oldsize){
		 oldsize = size;
	  }
	  memcpy(newptr, oldptr, oldsize);

	  /* Free the old block. */
	  free(oldptr);

	  return newptr;

}

/*
 * calloc - you may want to look at mm-naive.c
 * This function is not tested by mdriver, but it is
 * needed to run the traces.
 */
void *calloc (size_t nmemb, size_t size) {
	 size_t bytes = nmemb * size;
	 void *newptr;

	 newptr = malloc(bytes);
	 memset(newptr, 0, bytes);

	 return newptr;

}


/*
 * Return whether the pointer is in the heap.
 * May be useful for debugging.
 */
static int in_heap(const void *p) {
    return p <= mem_heap_hi() && p >= mem_heap_lo();
}

/*
 * Return whether the pointer is aligned.
 * May be useful for debugging.
 */
static int aligned(const void *p) {
    return (size_t)ALIGN(p) == (size_t)p;
}

/*
 * mm_checkheap
 * Checking the heap segregate list:
 * 
 * 1.  epilogue and prologue blocks.
 * 2. each block’s address alignment.
 * 3. heap boundaries.
 * 4. each block’s header and footer: size (minimum size, 
 * alignment), previous/next allo-cate/free bit consistency, 
 * header and footer matching each other.
 * 5. coalescing: no two consecutive free blocks in the heap
 * 
 * Checking the free list (segregated list):
 * –
 * 1. All next/previous pointers are consistent (if A’s next 
 * pointer points to B, B’s previous pointer  should point to A).
 * –
 * 2. All free list pointers points between mem_heap_lo() 
 * and mem_heap_high()
 * 3. Count free blocks by iterating through every block and trave
 * rsing free list by pointers and see if they match.
 * 4. All blocks in each list bucket fall within bucket size range (
 * segregated list)
 */
void mm_checkheap(int lineno) {
	char *bp ;
	long freecount=0; // free block counter
	if(heap_listp == NULL){
		printf("Head list pointer is NULL, heap may not be initialized  properly\n");
		return ;
	}
	//checking prologue headers and footers
	if((GET_SIZE(heap_listp) != DSIZE) || (GET_ALLOC(heap_listp) !=1)){
		printf("Prlogue footer doesnt have proper value %d\n ", GET_SIZE(heap_listp));
	}
	
        if((GET_SIZE(heap_listp - WSIZE) != DSIZE) ||
                        (GET_ALLOC(heap_listp-WSIZE) !=1)){
                printf("Prologue header doesnt have proper value %d\n", GET_SIZE(heap_listp-WSIZE));
        }
	
	for(bp = heap_listp+DSIZE; GET_SIZE(HDRP(bp)) > 0 ; bp = NEXT_BLKP(bp)){
		checkblock(bp);
		if(!GET_ALLOC(HDRP(bp))){
			freecount++;
		

		/* Adjacent free blocks */
			if (!(GET_ALLOC(HDRP(NEXT_BLKP(bp))))){ 
				printf("Error: Free block pointer %p \
					and %p are adjacent\n", bp, NEXT_BLKP(bp));
			}
		
		}
	}
	long d;
	d=checkfreeblocks();
	if(freecount!=d){
		 printf("memcheck done for lineno = %d",lineno);
        	 printf("Free block count is not same =  \n");
	}
}

static long checkfreeblocks(){
	char *liststart=NULL;
	char *next = NULL;
	int index=0;
	//size_t prevsize=0;
	unsigned int temp;
	long freecount=0;
	for(index=0;index<=SEGLIST;index++){
		temp=GET(freelist+WSIZE*index);
		while(temp!=0){
			liststart=head+temp;
			if(!in_heap(liststart)){
		                printf("freelist pointer is not in heap \n");
		        }
  		        if(!aligned(liststart)){
          		        printf("freeelist pointer is not aligned %p\n",liststart);
        		}

		        if(GET(HDRP(liststart)) != GET(FTRP(liststart))){
                		printf("HEADER doesnt match footer for the freelist block %p\n", liststart);
       			 }

			//size check
		/*	if(!(GET_SIZE(liststart) <=((unsigned)1<<(4+index))) &&
				!(GET_SIZE(liststart)>prevsize)){
				printf("free block pointer's size is not in range\n");
			}*/
			if(GET_ALLOC(liststart)){
				printf("Free list has a pointer allocated\n");
			}
			freecount++;
	//		prevsize=GET_SIZE(liststart);
			temp=GET(SUCC(liststart));
			if(temp!=0){
				next=head+temp;
				if(liststart != (head+GET(PRED(next)))){
					printf("Next and prev of Next are not same in freelist corr to index =%d",index);
				}
			}
		}
	}
	return freecount;
}
static void checkblock(void *bp){
	if(!in_heap(bp)){
		printf("BP is not in heap \n");
	}
 	if(!aligned(bp)){
 		printf("BP is not aligned %p\n", bp);
	}
	
	if(GET(HDRP(bp)) != GET(FTRP(bp))){
		printf("HEADER doesnt match footer for the block %p\n", bp);
	}

	// min size 
	if(GET_SIZE(HDRP(bp)) < MINBLOCKSIZE){
		printf("Block size is lesser than min block size\n");
	}
}

