/* 
 * Simple, 32-bit and 64-bit clean allocator based on implicit free
 * lists, first-fit placement, and boundary tag coalescing, as described
 * in the CS:APP3e text. Blocks must be aligned to doubleword (8 byte) 
 * boundaries. Minimum block size is 16 bytes. 
 */
#include <stdio.h>
#include <string.h>
#include <stdlib.h>

#include "mm.h"
#include "memlib.h"

/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

/*
 * If NEXT_FIT defined use next fit search, else use first-fit search 
 */
#define NEXT_FITx

/* Basic constants and macros */
#define WSIZE       4       /* Word and header/footer size (bytes) */ 
#define DSIZE       8       /* Double word size (bytes) */
#define CHUNKSIZE  (1<<12)  /* Extend heap by this amount (bytes) */  

#define MAX(x, y) ((x) > (y)? (x) : (y))  

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc)) 

/* Read and write a word at address p */
#define GET(p)       (*(unsigned int *)(p))            
#define PUT(p, val)  (*(unsigned int *)(p) = (val))    

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)                   
#define GET_ALLOC(p) (GET(p) & 0x1)                    

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE)                      
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) 

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) 
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* Store predecessor or successor pointer for free blocks */
#define SET_PTR(p, ptr) (*(intptr_t *)(p) = (intptr_t)(ptr))
#define GET_SUCC_PTR(p) (*((intptr_t *)(p + DSIZE)))
#define GET_PRED_PTR(p) (*((intptr_t *)p))

// Address of free block's predecessor and successor entries
#define PRED_PTR(ptr) ((char *)(ptr))
#define SUCC_PTR(ptr) ((char *)(ptr) + DSIZE)

intptr_t *header = 0x800000000;

/* Value of free block's predecessor and successor entries on the list */
#define PRED(ptr) (*(char **)(PRED_PTR(ptr)))
#define SUCC(ptr) (*(char **)(SUCC_PTR(ptr)))
//#define SUCC(ptr) (header + GET(SUCC_PTR(ptr)))

/* Settings for mm_check */
#define CHECK         1 /* Kill bit: Set to 0 to disable checking
                           (Checking is currently disabled through comments) */
#define CHECK_MALLOC  1 /* Check allocation operations */
#define CHECK_FREE    1 /* Check free operations */
#define CHECK_REALLOC 1 /* Check reallocation operations */
#define DISPLAY_BLOCK 1 /* Describe blocks in heap after each check */
#define DISPLAY_LIST  1 /* Describe free blocks in lists after each check */
#define PAUSE         1 /* Pause after each check, also enables the function to
                           skip displaying mm_check messages*/

#define LINE_OFFSET   4 /* Line offset for referencing trace files */


/* Global variables */
static char *heap_listp = 0;  /* Pointer to first block */
static char *head = 0;
int line_count; // Running count of operations performed  
#ifdef NEXT_FIT
static char *rover;           /* Next fit rover */
#endif

/* Function prototypes for internal helper routines */
static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);
static void mm_check(char caller, void *ptr, int size);
static void delete_node(void *ptr);
static void insert_node(void *ptr, size_t size);

/* 
 * mm_init - Initialize the memory manager 
 */
int mm_init(void) 
{
    char *bp;
	 /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1) 
        return -1;
    PUT(heap_listp, 0);                          /* Alignment padding */
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); /* Prologue header */ 
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); /* Prologue footer */ 
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));     /* Epilogue header */
    heap_listp += (2*WSIZE);                     

#ifdef NEXT_FIT
    rover = heap_listp;
#endif

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if ((extend_heap(CHUNKSIZE/WSIZE)) == NULL) 
        return -1;
	/*PUT(PRED_PTR(bp),NULL);
    PUT(SUCC_PTR(bp),NULL);
    head = bp;*/

    line_count = LINE_OFFSET;
    mm_check('i', bp, (CHUNKSIZE/WSIZE)); 
    
    return 0;
}

/* 
 * malloc - Allocate a block with at least size bytes of payload 
 */
void *malloc(size_t size) 
{
    size_t asize;      /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    char *bp;      
    size_t checksize = size;
    if (heap_listp == 0){
        mm_init();
    }
    /* Ignore spurious requests */
    if (size == 0)
        return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE)                                          
        asize = 2*DSIZE;                                        
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE); 

    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {  
        place(bp, asize);
        line_count++;
		mm_check('a', bp, checksize);                  
        return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize,CHUNKSIZE);                 
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)  
        return NULL;                                  
    place(bp, asize);
    line_count++;   
    mm_check('a', bp, checksize);                              
    return bp;
} 

/* 
 * free - Free a block 
 */
void free(void *bp)
{
    if (bp == 0) 
        return;

    size_t size = GET_SIZE(HDRP(bp));
    if (heap_listp == 0){
        mm_init();
    }

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    insert_node(bp, size);
    coalesce(bp);
    line_count++;
    if (CHECK && CHECK_FREE) {
    mm_check('f', bp, size);
  }

}

/*
 * realloc - Naive implementation of realloc
 */
void *realloc(void *ptr, size_t size)
{
    size_t oldsize;
    void *newptr;

    /* If size == 0 then this is just free, and we return NULL. */
    if(size == 0) {
        mm_free(ptr);
        return 0;
    }

    /* If oldptr is NULL, then this is just malloc. */
    if(ptr == NULL) {
        return mm_malloc(size);
    }

    newptr = mm_malloc(size);

    /* If realloc() fails the original block is left untouched  */
    if(!newptr) {
        return 0;
    }

    /* Copy the old data. */
    oldsize = GET_SIZE(HDRP(ptr));
    if(size < oldsize) oldsize = size;
    memcpy(newptr, ptr, oldsize);

    /* Free the old block. */
    mm_free(ptr);
    line_count++;
	if (CHECK && CHECK_REALLOC) {
		mm_check('r', ptr, size);
	}

    return newptr;
}

/* 
 * mm_checkheap - Check the heap for correctness. Helpful hint: You
 *                can call this function using mm_checkheap(__LINE__);
 *                to identify the line number of the call site.
 */
void mm_check(char caller, void* caller_ptr, int caller_size)  
{ 
   // lineno = lineno; /* keep gcc happy */
   int size;  // Size of block
  int alloc; // Allocation bit
  char *ptr = heap_listp + DSIZE;
  int block_count = 1;
  int count_size;
  int count_list;
  int loc;   // Location of block relative to first block
  int caller_loc = (char *)caller_ptr - ptr;
  int list;
  char *scan_ptr;
  char skip_input;
  char *bp;
  int free_blocks;
 
  //if (!skip)
    printf("\n[%d] %c %d %d: Checking heap...\n",
      line_count, caller, caller_size, caller_loc);

  while (1) {
    loc = ptr - heap_listp - DSIZE;

    size = GET_SIZE(HDRP(ptr));
    if (size == 0)
      break;

    alloc = GET_ALLOC(HDRP(ptr));

    // Print block information
    //if (DISPLAY_BLOCK && !skip) {
      printf("%d: Block at location %d : %x has size %d and allocation bit %d is %s\n",
        block_count, loc, caller_loc, size, alloc, alloc?"allocated":"free");
     /* if (GET_TAG(HEAD(ptr))) {
        printf("%d: Block at location %d is tagged\n",
          block_count, loc);
      }*/
  //  }

    // Check consistency of size and allocation in header and footer
    if (size != GET_SIZE(FTRP(ptr))) {
      printf("%d: Header size of %d does not match footer size of %d\n",
        block_count, size, GET_SIZE(FTRP(ptr)));
    }
    if (alloc != GET_ALLOC(FTRP(ptr))) {
      printf("%d: Header allocation of %d does not match footer allocation "
        "of %d\n", block_count, alloc, GET_ALLOC(FTRP(ptr)));
    }
	ptr = NEXT_BLKP(ptr);
    block_count++;
   }
   printf("printing free block\n");
   bp = head;
   free_blocks = 0;
   if(bp == 0) { printf("free list is empty\n"); return; }
   while(bp != NULL)
   {
	   printf("Reached here.. \n");
	   size = GET_SIZE(HDRP(bp));
	   alloc = GET_ALLOC(HDRP(bp));
	   printf("%d: Free Block at location %x has size %d pred %x succ %x and allocation bit %d is %s\n",
			   block_count, bp, size, PRED(bp), SUCC(bp), alloc, alloc?"allocated":"free");
	   bp = SUCC(bp);
	   printf("bp is %x\n",bp);
    }
	return;

}

void mm_checkheap(int lineno) {
	lineno = lineno;
}

/* 
 * The remaining routines are internal helper routines 
 */

/* 
 * extend_heap - Extend heap with free block and return its block pointer
 */
static void *extend_heap(size_t words) 
{
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE; 
    if ((long)(bp = mem_sbrk(size)) == -1)  
        return NULL;                                        

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));         /* Free block header */   
    PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */   
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */
    insert_node(bp, size); 

    /* Coalesce if the previous block was free */
    return coalesce(bp);                                          
}

/*
 * coalesce - Boundary tag coalescing. Return ptr to coalesced block
 */
static void *coalesce(void *bp) 
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) {
        return bp;
    }

    else if (prev_alloc && !next_alloc) {
        delete_node(bp);
        delete_node(NEXT_BLKP(bp));      /* Case 2 */
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size,0));
    }

    else if (!prev_alloc && next_alloc) {      /* Case 3 */
        delete_node(bp);
        delete_node(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    else {
        delete_node(bp);
        delete_node(PREV_BLKP(bp));
        delete_node(NEXT_BLKP(bp));
                                                    /* Case 4 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + 
            GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
#ifdef NEXT_FIT
    /* Make sure the rover isn't pointing into the free block */
    /* that we just coalesced */
    if ((rover > (char *)bp) && (rover < NEXT_BLKP(bp))) 
        rover = bp;
#endif
    insert_node(bp, size);
    return bp;
}

/* 
 * place - Place block of asize bytes at start of free block bp 
 *         and split if remainder would be at least minimum block size
 */
static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp)); // size of free block 
    size_t remainder = csize - asize;
    /* Remove block from free list */
    delete_node(bp);
 

    if ((csize - asize) >= (2*DSIZE)) { 
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(remainder, 0));
        PUT(FTRP(bp), PACK(remainder, 0));
        insert_node(bp, remainder);
    }
    else { 
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

static void insert_node(void *ptr, size_t size) {
 // int list = 0;
  //void *search_ptr = ptr;
  //void *insert_ptr = NULL;
  char *bp;
  if ( head!= 0) {
	  bp = head;
	  SET_PTR(PRED_PTR(bp), ptr);
	  SET_PTR(SUCC_PTR(ptr), bp);      
	  SET_PTR(PRED_PTR(ptr), NULL);
      head = ptr; 
  } else {
	  head = ptr;
      SET_PTR(SUCC_PTR(ptr), NULL);
      SET_PTR(PRED_PTR(ptr), NULL);
      //(SUCC(ptr), NULL);
      //PUT(PRED(ptr), NULL);
	  //PUT(PRED_PTR(ptr),NULL);
	  //PUT(SUCC_PTR(ptr),NULL);
  }

      

  /* Select segregated list */
 /* while ((list < LISTS - 1) && (size > 1)) {
    size >>= 1;
    list++;
  }*/

  /* Select location on list to insert pointer while keeping list
     organized by byte size in ascending order. */
 /* search_ptr = free_lists[list];
  while ((search_ptr != NULL) && (size > GET_SIZE(HEAD(search_ptr)))) {
    insert_ptr = search_ptr;
    search_ptr = PRED(search_ptr);
  }

  // Set predecessor and successor 
  if (search_ptr != NULL) {
    if (insert_ptr != NULL) {
      SET_PTR(PRED_PTR(ptr), search_ptr);
      SET_PTR(SUCC_PTR(search_ptr), ptr);
      SET_PTR(SUCC_PTR(ptr), insert_ptr);
      SET_PTR(PRED_PTR(insert_ptr), ptr);
    } else {
      SET_PTR(PRED_PTR(ptr), search_ptr);
      SET_PTR(SUCC_PTR(search_ptr), ptr);
      SET_PTR(SUCC_PTR(ptr), NULL);

      // Add block to appropriate list 
      free_lists[list] = ptr;
    }
  } else {
    if (insert_ptr != NULL) {
      SET_PTR(PRED_PTR(ptr), NULL);
      SET_PTR(SUCC_PTR(ptr), insert_ptr);
      SET_PTR(PRED_PTR(insert_ptr), ptr);
    } else {
      SET_PTR(PRED_PTR(ptr), NULL);
      SET_PTR(SUCC_PTR(ptr), NULL);

      // Add block to appropriate list 
      free_lists[list] = ptr;
    }
  } */

  return;
}



/*
 * delete_node: Remove a free block pointer from a segregated list. If
 *              necessary, adjust pointers in predecessor and successor blocks
 *              or reset the list head.
 */
static void delete_node(void *ptr) {
  //int list = 0;
  size_t size = GET_SIZE(HDRP(ptr));

  /* Select segregated list */
 /* while ((list < LISTS - 1) && (size > 1)) {
    size >>= 1;
    list++;
  }*/
 
  if (PRED(ptr) != NULL) {
    if (SUCC(ptr) != NULL) {
      SET_PTR(SUCC_PTR(PRED(ptr)), SUCC(ptr));
      SET_PTR(PRED_PTR(SUCC(ptr)), PRED(ptr));
    } else {
      SET_PTR(SUCC_PTR(PRED(ptr)), NULL);
     // free_lists[list] = PRED(ptr);
    }
  } else {
    //intptr_t header1 = header + SUCC(ptr);
    if (SUCC(ptr) != NULL) {
      SET_PTR(PRED_PTR(SUCC(ptr)), NULL);
      head = SUCC(ptr);
    } else {
      head = 0;
     // free_lists[list] = NULL;
    }
  }

  return;
}


/* 
 * find_fit - Find a fit for a block with asize bytes 
 */
static void *find_fit(size_t asize)
{
#ifdef NEXT_FIT 
    /* Next fit search */
    char *oldrover = rover;

    /* Search from the rover to the end of list */
    for ( ; GET_SIZE(HDRP(rover)) > 0; rover = NEXT_BLKP(rover))
        if (!GET_ALLOC(HDRP(rover)) && (asize <= GET_SIZE(HDRP(rover))))
            return rover;

    /* search from start of list to old rover */
    for (rover = heap_listp; rover < oldrover; rover = NEXT_BLKP(rover))
        if (!GET_ALLOC(HDRP(rover)) && (asize <= GET_SIZE(HDRP(rover))))
            return rover;

    return NULL;  /* no fit found */
#else 
    /* First-fit search */
    void *bp;

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
            return bp;
        }
    }
    return NULL; /* No fit */
#endif
}

