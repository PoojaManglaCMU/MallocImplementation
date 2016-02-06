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
 * Each block has a minimum size of 16 bytes: First 4 bytes for reserved for 
 * header. Last 4 bytes are reserved for footer. In case of free blocks, the 4 
 * bytes next to header contain the last 4 bytes of the address of the 
 * predecessor block in the free block list and next 4 bytes contain the last 4
 * bytes of the address of the  successor block in the free block list.
 * In case of an allocated block, the 8 bytes contain payload if the size is 
 * more than or equal to the minimum block size else they contain payload and 
 * padding. 
 *
 * Optimizations to implicit free list allocator provided in textbook code:
 * ========================================================================
 * The dynamic storage allocator used here uses free block lists i.e. 
 * segregated list technique. Free block lists are stored in an array of linked
 * list for different sizes of free blocks. There is no limit on size of these 
 * linked lists. 
 * freeblocklist[0] contains free blocks of size <=16
 * freeblocklist[1] : size between 2^4 to 2^5
 * freeblocklist[2] : size between 2^5 - 2^6 
 * and so on
 *
 * This reduces the number of searched required for a free block as now the 
 * allocator will only search in a particular linked list based on size of the 
 * block required which further results in increase in throughput.
 *
 * Coalescing:
 * ==========
 * Coalescing is performed to coalesce adjacent free blocks which decreases 
 * external fragmentation further increasing memory utilization.
 *
 * Fit: 
 * ====
 * Memory allocation is done using first fit model. When a memory block is 
 * requested, first appropriate list from the lists of free block lists is 
 * selected and then a free block of appropriate size is allocated from that 
 * list.
 * 
 * Splitting
 * =========
 * If (size of free block - requested block size) >  MinBlockSize(16) we split 
 * the block and allocate. Also the remaining block is restored back in the 
 * appropriate free list.
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

#define CHUNKSIZE (1<<8)

#define MAXLIST 12// number of segregated free list
#define MINLISTSIZE 24 // this is done to ensure that blocks 
                       // of size>16 and size<24 do not go 
                       // into the free list of size 32.  

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

/* Maximum size of free list of index n */
#define LIST_MAX_SIZE(n) (unsigned)(16*(1 << n))
#define LIST_MIN_SIZE(n) (unsigned)(16*(1 << (n-1)))

/* Settings for mm_checkheap */
#define CHECK         0 /* Kill bit: Set to 0 to disable checking
                           (Checking is currently disabled through comments) */
#define CHECK_MALLOC  1 /* Check allocation operations */
#define CHECK_FREE    1 /* Check free operations */
#define CHECK_REALLOC 1 /* Check reallocation operations */

/*Help Functions*/
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void insertnode(void *ptr, size_t size);
static void *find_valid_block(size_t size, int index);
static void deletenode(void *ptr);
static void checkblock(void *bp);
static long checkfreeblocks();

/*Global variables*/
char* heap_listp;
char *freeblocklist;
char *offset = (char *)0x800000000;
int line_count; // Running count of operations performed
int skip = 0;
#ifdef NEXT_FIT
static char *rover;           /* Next fit rover */
#endif

/*`
 * Initialize: return -1 on error, 0 on success.
 * Initializes the free list 
 * Sets prologue and epilogue blocks and gets some memory using mem_sbrk()
 */
int mm_init(void) {
	int i;
	char *bp;
	if((freeblocklist = mem_sbrk(MAXLIST*WSIZE)) == NULL){
		return -1;
	} 
	// Initialize free block lists
	for(i=0; i<=MAXLIST; i++)
	{
		PUT(freeblocklist+WSIZE*i, NULL);
	}

	// Create initial empty heap
	if((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1){
		return -1;
	}
	
	PUT(heap_listp, 0);			   // Alignment padding
	PUT(heap_listp+(1*WSIZE), PACK(DSIZE,1));  // Prologue header
	PUT(heap_listp+(2*WSIZE), PACK(DSIZE,1));  // Prologue footer
	PUT(heap_listp+(3*WSIZE), PACK(0,1));	   // EPilogue header

	heap_listp += (2*WSIZE);

#ifdef NEXT_FIT
	rover = heap_listp;
#endif
	
	/* Extend the empty heap with block of CHUNKSIZE bytes*/
	bp =extend_heap(CHUNKSIZE/WSIZE);
	if(bp == NULL){
		return -1;
	}
    if(CHECK) {
		mm_checkheap(199);	
    }
	 return 0;
}

/*
 * extend_heap(words)
 *
 * Extend heap by no. of bytes specified in the input parameter
 * This is invoked on two conditions: 
 * (1) when the heap is initialized, and
 * (2) when mm_malloc is unable to find a suitable fit.
 */
static void *extend_heap(size_t words){
	char *bp;
	size_t size;

	// allocate even number of words to maintain alignment
	size = (words % 2)?((words + 1)* WSIZE):(words * WSIZE);
	if((long)(bp = mem_sbrk(size)) == -1){
		return (void *)0;
	}
	
	// initialize free block header
	PUT(HDRP(bp), PACK(size,0));// free block header
	PUT(FTRP(bp), PACK(size,0));// free block foother
	PUT(HDRP(NEXT_BLKP(bp)), PACK(0,1));// new epilogue header
	insertnode(bp, size);
	return coalesce(bp);	
}

/**
 * Inserts the free block into appropriate index in free list
 * FreelIst[0] size <=16
 * list[1] = 2^4 - 2^5
 * and so on 2^n to 2^n+1
 */
static void insertnode(void *bp, size_t size){
	int index=0;
	void *freeblockhead = NULL; 
    char *header;

	while((index < MAXLIST) && (size > MINLISTSIZE)){
		size >>=1;
		index++;
	}
	freeblockhead = freeblocklist + (WSIZE * index);
	header = offset + GET(freeblockhead);

	if(GET(freeblockhead) != 0){
		/* set current free block next to prev list
 		*  and current free block's prev to NULL
 		*  Also set prev head's prev pointer to current free block
 		*/
		PUT(freeblockhead,  bp);
		PUT(PRED(bp), NULL);
		PUT(SUCC(bp), header);
		PUT(PRED(header), bp);
	}else{
		// there are no blocks in this size currently	
		// set free blocks's next and prev as NULL
		PUT(freeblockhead, bp);
		PUT(SUCC(bp), NULL);
		PUT(PRED(bp), NULL);
	}
}


/* Coalesce:
 *
 * Coalesces free blocks reducing external fragmentation. 
 * Handles below four cases:
 * 1. The previous and next blocks are both allocated: No coalescing done
 * 2. The previous block is allocated and the next block is free: Current 
 *    next block coalesced
 * 3. The previous block is free and the next block is allocated: Previous
 *    and current block coalesced.
 * 4. The previous and next blocks are both free: All three blocks colaesced
 *    into one. 
 */
static void *coalesce(void *bp){
	
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
	size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
	size_t size = GET_SIZE(HDRP(bp));
   
    //1st case
	if(prev_alloc && next_alloc){
		return bp;
	}

	if(prev_alloc && !next_alloc){ 
		// 2nd Case
		size += GET_SIZE(HDRP(NEXT_BLKP(bp)));	
		deletenode(bp);
		deletenode(NEXT_BLKP(bp));
		PUT(HDRP(bp), PACK(size,0));
		PUT(FTRP(bp), PACK(size,0));
	} else if(!prev_alloc && next_alloc){
        // 3rd Case
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
		deletenode(bp);
		deletenode(PREV_BLKP(bp));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size,0));
		PUT(FTRP(bp), PACK(size,0));
        bp = PREV_BLKP(bp);
	} else {
        // 4th Case
		size += GET_SIZE(HDRP(PREV_BLKP(bp)))+
			GET_SIZE(HDRP(NEXT_BLKP(bp)));
		deletenode(bp);
		deletenode(PREV_BLKP(bp));
		deletenode(NEXT_BLKP(bp));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size,0));
		PUT(FTRP(NEXT_BLKP(bp)), PACK(size,0));
		bp = PREV_BLKP(bp);
	}

#ifdef NEXT_FIT
    /* Make sure the rover isn't pointing into the free block */
    /* that we just coalesced */
	if ((rover > (char *)bp) && (rover < NEXT_BLKP(bp)))
        rover = bp;
#endif
    insertnode(bp, size);
	return bp;
}

/* deletenode(void *bp)
 *
 * Deletes a free node from the appropriate free block 
 * list when the block is allocated.
 *
 */
static void deletenode(void *bp){
	int index = 0;
	size_t size = GET_SIZE(HDRP(bp));
 	char *succ = offset + GET(SUCC(bp));
	char *pred = offset + GET(PRED(bp));	
	//get the index where bp is in list
	while((index < MAXLIST) && (size > MINLISTSIZE)){
		size>>=1;
		index++;
	}
	if(GET(PRED(bp)) != 0) {
		if(GET(SUCC(bp)) == 0) {
			PUT(SUCC(pred), NULL);
		} else {
			PUT(SUCC(pred), succ);
			PUT(PRED(succ), pred);
		}
	} else {
		if(GET(SUCC(bp)) == 0) {
			PUT(freeblocklist+index*WSIZE, NULL);	
		} else {
			PUT(PRED(succ), NULL);
			PUT(freeblocklist+WSIZE*index, succ);
		}
	}
}

/* MALLOC
 *
 * Allocates the requested block size from the heap. Minimum
 * block size allocated is 16 bytes. 
 * 
 * Input parameters: Size of the requested block
 * Return value: Pointer to the allocated block
 *
 */
void *malloc (size_t size) {
	size_t asize;      /* Adjusted block size */
	size_t extendsize; /* Amount to extend heap if no fit */
	char *bp;
	if (size == 0) {
		return NULL;
	}

	/* Adjust block size to include overhead and alignment reqs. */
	if (size <=  DSIZE) {
		asize= 2*DSIZE;
	} else {
		// round up to the nearest multiple of 8
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

/* find_fit(size)
 *
 * Finds the free block by first searching the list of free blocks of 
 * appropriate size and and then allocates the free block from that list
 *
 * Input: Size of block requested
 * Return value: Pointer to allocated block
 */
static void *find_fit(size_t size){
	void *bp = NULL;
	size_t asize = size;
	int index = 0;
    // Search for the free blocks list of appropriate size
	while((index < MAXLIST) && (size > MINLISTSIZE)){
		index++;
		size>>=1;
	}
	while(bp == NULL && index <= MAXLIST){
		bp = find_valid_block(asize, index);
		index++;
	}
	return bp;
}

/* find_valid_block(size, index)
 *
 * Finds the block in the corresponding free list.
 *
 * Input: 1) Size of the block requested
 *        2) Index of the free blocks list in the free 
 *           lists array
 *
 * Return Value: Pointer to allocated block 
 */
static void *find_valid_block(size_t asize, int index){
  	char *bp = NULL;
	unsigned int blk_addr;
	blk_addr = GET(freeblocklist + (WSIZE * index));
	while(blk_addr !=0)
	{
		bp = offset + blk_addr;
		if(asize <= GET_SIZE(HDRP(bp))){
            return bp;
		}
		blk_addr = GET(SUCC(bp));
	}
	return NULL;
}


/*
 * place(bp, size)
 *
 * Deletes the block from its free list and allocates the block.
 * If free block size - requested block size is greater than minimum
 * block size, split the free block and insert the remaining block into
 * free list. Allocates the entire block if difference is less than or 
 * equal to minimum block size.
 *
 * Input: Block pointer and size
 * Return value: Pointer to the block allocated 
 */
static void place(void *bp, size_t asize){

	size_t csize=GET_SIZE(HDRP(bp));// get block size
    size_t remainder = csize - asize;	
   
    // Delete node from the free list	
    deletenode(bp);
    
	if(remainder > MINLISTSIZE){
		PUT(HDRP(bp), PACK(asize,1));
		PUT(FTRP(bp), PACK(asize,1));
		bp = NEXT_BLKP(bp);
		PUT(HDRP(bp), PACK(remainder, 0));
		PUT(FTRP(bp), PACK(remainder,0));
		// add the new block into the list
		insertnode(bp, remainder);
	}else{
		PUT(HDRP(bp), PACK(csize,1));
		PUT(FTRP(bp), PACK(csize,1));
	}	
}

/* free(ptr)
 * Reset the allocated block for the freed block.
 * Insert the free block in appropriate free list and 
 * coalesce.
 *
 * Input: pointer of the block to be freed
 * Return value: None
 */
void free (void *ptr) {
	if(ptr == NULL){
		return;
	}
	size_t size = GET_SIZE(HDRP(ptr));
	PUT(HDRP(ptr), PACK(size,0));
	PUT(FTRP(ptr), PACK(size,0));
	insertnode(ptr, GET_SIZE(HDRP(ptr)));
	coalesce(ptr);	
    // Check heap for consistency
	line_count++;
	if (CHECK && CHECK_FREE) {
		mm_checkheap(515);
	}
}

/*
 * realloc - you may want to look at mm-naive.c
 */
void *realloc(void *ptr, size_t size) {
	size_t oldsize;
	void *newptr;
    size_t asize;
	if(size == 0) {
		free(ptr);
		return 0;
	}

	if(ptr == NULL) {
		return malloc(size);
	}
   
     /* Adjust block size to include overhead and alignment reqs. */
    if (size <=  DSIZE) {
        asize= 2*DSIZE;
    } else {
		// round up to the nearest multiple of 8
		asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);
	}
    oldsize = GET_SIZE(HDRP(ptr));
     
	if(asize == oldsize){
        return ptr;
    }
    
    if(asize <= oldsize){
		size = asize;
		/* If a new block couldn't fit in the remaining space, 
		 * return the pointer */
		if(oldsize - size <= 2*DSIZE)
			return ptr;
		PUT(HDRP(ptr), PACK(size, 1));
		PUT(FTRP(ptr), PACK(size, 1));
		PUT(HDRP(NEXT_BLKP(ptr)), PACK(oldsize-size, 1));
		free(NEXT_BLKP(ptr));
		return ptr;
    }

	newptr = malloc(size);

	if(!newptr) {
		return 0;
	}

	if(size < oldsize){
		oldsize = size;
	}
	memcpy(newptr, ptr, oldsize);

	free(ptr);

    // Check heap for consistency
    line_count++;
	if (CHECK && CHECK_REALLOC) {
		mm_checkheap(578);
	}
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
 * 1. Epilogue and prologue blocks.
 * 2. Each block’s address alignment.
 * 3. Heap boundaries.
 * 4. Each block’s header and footer: size (minimum size,
 * alignment), previous/next allo-cate/free bit consistency,
 * header and footer matching each other.
 * 5. Coalescing: no two consecutive free blocks in the heap
 *
 * Checking the free list (segregated list):
 * –
 * 1. All next/previous pointers are consistent (if A’s next
 * pointer points to B, B’s previous pointer  should point to A).
 * –
 * 2. All free list pointers points between mem_heap_lo()
 * and mem_heap_high()
 * 3. Count free blocks by iterating through every block and trave-
 *    -rsing free list by pointers and see if they match.
 * 4. All blocks in each list bucket fall within bucket size range (
 * segregated list)
 */
void mm_checkheap(int lineno) {
    char *ptr = heap_listp + DSIZE;
    long freeblockcount = 0; // free block counter

	if(heap_listp == NULL){
		printf("Head list pointer is NULL,heap is not initialized properly\n");
		return ;
	}
	//Checking prologue headers and footers
	if((GET_SIZE(heap_listp) != DSIZE) || (GET_ALLOC(heap_listp) != 1)){
		printf("Prologue footer does not have valid value %d\n ", 
                                                     GET_SIZE(heap_listp));
	}
    //Checking Epilogue header  
    if(GET(mem_heap_hi()-0x3) != PACK(0,1)) {
		printf("Epilogue header does not have valid value at lineno%d\n ",
															       lineno);
	}

	if((GET_SIZE(heap_listp - WSIZE) != DSIZE) ||
			(GET_ALLOC(heap_listp-WSIZE) != 1)){
		printf("Prologue header doesnt have valid value %d\n", 
                                                 GET_SIZE(heap_listp-WSIZE));
	}

	for(  ; GET_SIZE(HDRP(ptr)) > 0 ; ptr = NEXT_BLKP(ptr)){
		checkblock(ptr);
		if(!GET_ALLOC(HDRP(ptr))){
			freeblockcount++;

			/* Adjacent free blocks */
			if (!(GET_ALLOC(HDRP(NEXT_BLKP(ptr))))){
				printf("Error: Free block pointer %p \
						and %p are adjacent\n", ptr, NEXT_BLKP(ptr));
			}

		}
	}
	long d;
    d = checkfreeblocks();
    if(freeblockcount != d){
		printf("memcheck done for lineno = %d",lineno);
		printf("Free block count is not same while checking in free lists and \
                                                iterating through blocks \n");
    }
}

/*
 * Checks all blocks in free lists
 *
 */
static long checkfreeblocks(){
    char *liststart = NULL;
    char *next = NULL;
    int index = 0;
    unsigned int temp;
    long freecount = 0;
	unsigned size;
	unsigned alloc;

    for(index = 0; index <= MAXLIST; index++){
		temp = GET(freeblocklist + (WSIZE * index));
		while(temp != 0){
			liststart = offset + temp;
            if(!in_heap(liststart)){
                        printf("freelist pointer is not in heap \n");
                }
                if(!aligned(liststart)){
                        printf("freeelist pointer is not aligned %p\n", 
																liststart);
                }
   
				size = GET_SIZE(HDRP(liststart));
				alloc = GET_ALLOC(HDRP(liststart));

                if(GET(HDRP(liststart)) != GET(FTRP(liststart))){
                        printf("HEADER doesnt match footer for the freelist \
													block %p\n", liststart);
                 }
				 if (size != GET_SIZE(FTRP(liststart))) {
					 printf("%p: Header size of %u does not match footer size \
						 of %u\n", liststart, size, GET_SIZE(FTRP(liststart)));
				 }
				 if (alloc != GET_ALLOC(FTRP(liststart))) {
					 printf("%p: Header allocation of %u does not match footer \
										allocation of %u\n", liststart, alloc, 
													GET_ALLOC(FTRP(liststart)));
				 }

				 if(GET_ALLOC(liststart)){
					 printf("Free list has a pointer allocated\n");
				 }
				 freecount++;
				 temp = GET(SUCC(liststart));
				 if(temp != 0){
					 next = offset + temp;
					 if(liststart != (offset+GET(PRED(next)))){
						 printf("Next of Prev and Prev of Next are not same in \
								 freelist corr to index =%d", index);
					 }
				 }
		}
	}
	return freecount;
}

/*
 * Checks all blocks in the heap
 *
 */
static void checkblock(void *bp){
    unsigned size;
    unsigned alloc;

    if(!in_heap(bp)){
        printf("BP is not in heap \n");
    }
    if(!aligned(bp)){
        printf("BP is not aligned %p\n", bp);
    }

    size = GET_SIZE(HDRP(bp));
    alloc = GET_ALLOC(HDRP(bp));
    
    if(GET(HDRP(bp)) != GET(FTRP(bp))){
        printf("HEADER doesnt match footer for the block %p\n", bp);
    }
    if (size != GET_SIZE(FTRP(bp))) {
      printf("%p: Header size of %u does not match footer size of %u\n",
        bp, size, GET_SIZE(FTRP(bp)));
    }
    if (alloc != GET_ALLOC(FTRP(bp))) {
      printf("%p: Header allocation of %u does not match footer allocation "
        "of %u\n", bp, alloc, GET_ALLOC(FTRP(bp)));
    }
    // min size
    if(GET_SIZE(HDRP(bp)) < 2*DSIZE){
        printf("Block size is lesser than min block size\n");
    }
}       
