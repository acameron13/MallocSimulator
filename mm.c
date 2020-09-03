/* Alison Cameron and Adam Nik
Carleton College
March 2020*/

/* We simulated malloc and free calls within the structure
 * of the heap by an explicit free list, implemented through
 * a doubly linked list. Each block of memory contains a header
 * and a footer, which indicate the size of the block and
 * whether it is currently allocated. Free blocks are stored
 * in the explicit free doubly linked list. Each free block
 * contains a pointer to its predecessor and succesor so that
 * the list can be traversed easily. When blocks are freed,
 * they are merged with other free blocks next to them in
 * contiguous memory. When the heap runs out of space, we
 * extend its size and add the new space to the explicit
 * free list. */

#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>
#include <stdbool.h>
#include <stdint.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "Backflippers!",
    /* First member's full name */
    "Alison Cameron",
    /* First member's email address */
    "camerona2@carleton.edu",
    /* Second member's full name (leave blank if none) */
    "Adam Nik",
    /* Second member's email address (leave blank if none) */
    "nika@carleton.edu"
};

/* Basic constants and macros */
#define WSIZE       8       /* word size (bytes) */
#define DSIZE       16      /* doubleword size (bytes) */
#define CHUNKSIZE  (1<<12)  /* initial heap size (bytes) */
#define OVERHEAD    16      /* overhead of header and footer (bytes) */
#define MINSIZE     32      /* minimum block size (bytes) */

/* NOTE: feel free to replace these macros with helper functions and/or
 * add new ones that will be useful for you. Just make sure you think
 * carefully about why these work the way they do
 */

/* Pack a size and allocated bit into a word */
/* Used to create headers and footers */
#define PACK(size, alloc)  ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)       (*(size_t *)(p))
#define PUT(p, val)  (*(size_t *)(p) = (val))

/* Perform unscaled pointer arithmetic */
/* Used to jump over blocks in the heap */
#define PADD(p, val) ((char *)(p) + (val))
#define PSUB(p, val) ((char *)(p) - (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0xf)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       (PSUB(bp, WSIZE))
#define FTRP(bp)       (PADD(bp, GET_SIZE(HDRP(bp)) - DSIZE))

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  (PADD(bp, GET_SIZE(HDRP(bp))))
#define PREV_BLKP(bp)  (PSUB(bp, GET_SIZE((PSUB(bp, DSIZE)))))

/* Get succesor and predecessor pointers of free block */
#define GET_SUCC(bp)                 (*(char **)((bp) + WSIZE))
#define GET_PRED(bp)                 (*(char **)(bp))

/* Function prototypes for internal helper routines */
static bool check_heap(int lineno);
static void print_heap();
static void print_block(void *bp);
static bool check_block(int lineno, void *bp);
static void *extend_heap(size_t size);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);
static void place(void *bp, size_t asize);
static size_t max(size_t x, size_t y);
static void insert_in_explicit_list(void *bp);
static void remove_from_explicit_list(void *bp);
static void print_free_list();

/* Global variables */
// Pointer to first block
static void *heap_start = NULL;
// Pointers to explicit free list head
static void *head;

/*
 * mm_init -- this function initializes the heap by aligning
              data and creating prologue and epilogue blocks.
              It then extends the heap to create space.
 * No arguments.
 * Returns -1 if it is unable to properly intialize the heap.
 * Ensures that the heap is aligned and the global variables
    point to the start of the heap and the start of the free
    list (which initially does not hold anything).
 */
int mm_init(void) {
    void *bp;
    /* create the initial empty heap */
    if ((heap_start = mem_sbrk(4 * WSIZE)) == NULL)
        return (-1);

    PUT(heap_start, 0);                        /* alignment padding */
    PUT(PADD(heap_start, WSIZE), PACK(OVERHEAD, 1));  /* prologue header */
    PUT(PADD(heap_start, DSIZE), PACK(OVERHEAD, 1));  /* prologue footer */
    PUT(PADD(heap_start, WSIZE + DSIZE), PACK(0, 1));   /* epilogue header */

    heap_start = PADD(heap_start, DSIZE); /* start the heap at the (size 0) payload of the prologue block */

    head = NULL;

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    bp = extend_heap(CHUNKSIZE / WSIZE);
    if (bp == NULL)
        return (-1);

    return (0);
}

/*
 * mm_malloc -- Finds a chunk of memory in the heap and
                returns a pointer to the start of the payload.
                Extends the size of the heap if there is not a
                free block large enough.
 * Arguments: the size of the requested payload
 * Returns a pointer to the start of the payload for newly
  allocated block.
 */
void *mm_malloc(size_t size) {
    size_t asize;      /* adjusted block size */
    size_t extendsize; /* amount to extend heap if no fit */
    void *bp; /* pointer to payload of block to be allocated */

    /* Ignore spurious requests */
    if (size <= 0)
        return (NULL);

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE) {
        asize = DSIZE + OVERHEAD;
    } else {
        /* Add overhead and then round up to nearest multiple of double-word alignment */
        asize = DSIZE * ((size + (OVERHEAD) + (DSIZE - 1)) / DSIZE);
    }

    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL){
        place(bp, asize);
        return (bp);
    }

    /* No fit found. Get more memory and place the block */
    extendsize = max(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return (NULL);

    place(bp, asize);
    return (bp);
}

/*
 * mm_free -- This function frees a previously allocated block,
              recreates correct boundary tags, coalesces with
              any surrounding free blocks. The coalescing will
              take care of the pointer and what it points to.
 * Takes in a block pointer
 * Returns nothing
 * mm_free should only be called on previously allocated blocks.
 * mm_free verifies that the block is combined with other free blocks.
 */
void mm_free(void *bp) {
    /* If the block pointer is already null, we do not need
     * to do anything. If not, we will free the allocated
     * block. */
    if (bp == NULL){
      return;
    }

    PUT(HDRP(bp), PACK(GET_SIZE(HDRP(bp)), 0));
    PUT(FTRP(bp), PACK(GET_SIZE(HDRP(bp)), 0));
    coalesce(bp);
}

/*
 * EXTRA CREDIT
 * mm_realloc -- <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
*/
void *mm_realloc(void *ptr, size_t size) {
    // TODO: implement this function for EXTRA CREDIT
    return (NULL);
}


/* The remaining routines are internal helper routines */


/*
 * place -- Place block of asize bytes at start of free block bp
 *          and split the free block into two parts of size
            asize and newsize. Newsize is the size of the
            new allocated block subtracted from the size of
            the whole free block. The boundary tags for each
            new block are then created.
 * Takes a pointer to a free block and the size of the requested new allocated
  block.
 * Returns nothing
 * place requires that asize is divisible by our double word size in order
 * to maintain a properly aligned heap. Place ensures that the
 * remaining free block is not smaller than the minimum block size.
 */
static void place(void *bp, size_t asize) {
    size_t newsize;
    size_t currsize;

    currsize = GET_SIZE(HDRP(bp));
    newsize = currsize - asize;

    /* If the current free block is either the correct size, or
     * the new free block is smaller than the minimum block size,
     * then we will allocate the entire free block. No splitting
     * occurs in these cases. Boundary tags are reset to indicate
     * that the block is allocated. The block is then removed
     * from the explicit free list. */
    if (asize == currsize || newsize < MINSIZE){
      PUT(HDRP(bp), PACK(currsize, 1));
      PUT(FTRP(bp), PACK(currsize, 1));
      remove_from_explicit_list(bp);
    }

    /* If the new split free block is large enough to be used
     * later, we will split the current free block into two
     * parts. We will then add boundary tags for each part.
     * The newly allocated block is then removed from the
     * explicit free list, and the new free block is
     * coalesced with others around it. */
    else{
      PUT(HDRP(bp), PACK(asize, 1));
      PUT(FTRP(bp), PACK(asize, 1));
      remove_from_explicit_list(bp);
      bp = NEXT_BLKP(bp);
      PUT(HDRP(bp), PACK(newsize, 0));
      PUT(FTRP(bp), PACK(newsize, 0));
      coalesce(bp);
    }

}

/*
 * coalesce -- Boundary tag coalescing.
 * Takes a pointer to a free block
 * Return ptr to coalesced block
 * Coalesce only deals 3 contiguous blocks in the heap.
 * We assume that the sizes in headers and footers match,
 * so that we are properly adding sizes together.
 * The original blocks are removed from the explicit free
 * list, and the new block is added.
 */
static void *coalesce(void *bp) {
    size_t prev_allocate;
    size_t next_allocate;
    size_t newsize;

    next_allocate = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    prev_allocate = GET_ALLOC(HDRP(PREV_BLKP(bp)));

    /* If the previous block is allocated, but the next one is free,
     * we will coalesce the current and next blocks. Boundary tags
     * are properly created. */
    if (prev_allocate == 1 && next_allocate == 0){
      newsize = GET_SIZE(HDRP(bp)) + GET_SIZE(HDRP(NEXT_BLKP(bp)));
      remove_from_explicit_list(NEXT_BLKP(bp));
      PUT(HDRP(bp), PACK(newsize, 0));
      PUT(FTRP(bp), PACK(newsize, 0));
    }
    /* If the previous block is free, but the next one is allocated,
     * we will coalesce the current and previous blocks. Boundary tags
     * are properly created. */
    else if (prev_allocate == 0 && next_allocate == 1){
      newsize = GET_SIZE(HDRP(bp)) + GET_SIZE(HDRP(PREV_BLKP(bp)));
      remove_from_explicit_list(PREV_BLKP(bp));
      PUT(FTRP(bp), PACK(newsize, 0));
      PUT(HDRP(PREV_BLKP(bp)), PACK(newsize, 0));
      bp = PREV_BLKP(bp);
    }

    /* When both the previous and next blocks are free, we will
     * coalesce all three together. Boundary tags are properly created. */
    else if (prev_allocate == 0 && next_allocate == 0){
      newsize = GET_SIZE(HDRP(bp)) + GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(HDRP(NEXT_BLKP(bp)));
      remove_from_explicit_list(PREV_BLKP(bp));
      remove_from_explicit_list(NEXT_BLKP(bp));
      bp = PREV_BLKP(bp);
      PUT(HDRP(bp), PACK(newsize, 0));
      PUT(FTRP(bp), PACK(newsize, 0));
    }

    insert_in_explicit_list(bp); //add newly coalesced block to the explicit list
    return (bp); //return a pointer to the beginning of the block
}


/*
 * find_fit - Find a fit for a block with asize bytes using first fit.
 * Arguments: the total size of requested block
 * Returns a pointer to the block of the correct size.
 * If no fit is found, returns null.
 */
static void *find_fit(size_t asize) {
    /* search from the start of the free list to the end */
    void* cur_block = head;
    while (cur_block != NULL){
        if (asize <= (size_t)GET_SIZE(HDRP(cur_block))){
          return cur_block; //return the first block large enough
        }
        cur_block = GET_SUCC(cur_block);
    }

    return NULL;
}

/*
 * extend_heap - Extend heap with free block and return its block pointer
 * Arguments: size of extension to the heap
 * Returns a pointer to the newly extended block
 * extend_heap ensures heap stays aligned
 */
static void *extend_heap(size_t words) {
    void *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = words * WSIZE;
    if (words % 2 == 1)
        size += WSIZE;
    if ((long)(bp = mem_sbrk(size)) < 0)
        return NULL;
    if (size < MINSIZE)
        size = MINSIZE;

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));         /* free block header */
    PUT(FTRP(bp), PACK(size, 0));         /* free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* new epilogue header */

    return (coalesce(bp));
}

/* Inserts the free block pointer at the start the explicit free list
 * Arguments: Pointer the block to insert in list
 * Returns nothing
 * bp must be a pointer to a free block
*/
static void insert_in_explicit_list(void *bp){
  GET_SUCC(bp) = head;
  if (head == NULL){ //list is empty
    head = bp;
  }
  else{
    GET_PRED(head) = bp;
  }
  GET_PRED(bp) = NULL;
  head = bp;
}

/* Removes the free block pointer in the explicit free list
 * Arguments: pointer to a block to be removed from List
 * Returns nothing
 * requires that block to be removed is in the list
*/
static void remove_from_explicit_list(void *bp){
  void *pred = GET_PRED(bp);
  void *succ = GET_SUCC(bp);
  if((pred == NULL && succ == NULL) || pred == succ){ //only one element in list
    if (head != NULL){
      head = NULL;
    }
  }
  else if (pred != NULL && succ == NULL){ //element being removed is tail
    GET_SUCC(pred) = NULL;
  }
  else if (pred == NULL && succ != NULL){ //element being removed is first element in list
    GET_PRED(succ) = NULL;
    head = succ;
  }
  else if (pred != NULL && succ != NULL){ //when there is both a predecessor and succesor
    GET_SUCC(pred) = succ;
    GET_PRED(succ) = pred;
  }
}

/*
 * check_heap -- Performs basic heap consistency checks for an implicit free list allocator
 * and prints out all blocks in the heap in memory order.
 * Checks include proper prologue and epilogue, alignment, and matching header and footer
 * Takes a line number (to give the output an identifying tag).
 */
static bool check_heap(int line) {
    char *bp;

    if ((GET_SIZE(HDRP(heap_start)) != DSIZE) || !GET_ALLOC(HDRP(heap_start))) {
        printf("(check_heap at line %d) Error: bad prologue header\n", line);
        return false;
    }

    for (bp = heap_start; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if (!check_block(line, bp)) {
            return false;
        }
    }

    if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp)))) {
        printf("(check_heap at line %d) Error: bad epilogue header\n", line);
        return false;
    }

    return true;
}

/*
 * check_block -- Checks a block for alignment and matching header and footer
 */
static bool check_block(int line, void *bp) {
    if ((size_t)bp % DSIZE) {
        printf("(check_heap at line %d) Error: %p is not double-word aligned\n", line, bp);
        return false;
    }
    if (GET(HDRP(bp)) != GET(FTRP(bp))) {
        printf("(check_heap at line %d) Error: header does not match footer\n", line);
        return false;
    }
    return true;
}

/*
 * print_heap -- Prints out the current state of the implicit free list
 */
static void print_heap() {
    char *bp;

    printf("Heap (%p):\n", heap_start);

    for (bp = heap_start; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        print_block(bp);
    }

    print_block(bp);
}

/*
 * print_block -- Prints out the current state of a block
 */
static void print_block(void *bp) {
    size_t hsize, halloc, fsize, falloc;

    hsize = GET_SIZE(HDRP(bp));
    halloc = GET_ALLOC(HDRP(bp));
    fsize = GET_SIZE(FTRP(bp));
    falloc = GET_ALLOC(FTRP(bp));

    if (hsize == 0) {
        printf("%p: End of free list\n", bp);
        return;
    }

    printf("%p: header: [%ld:%c] footer: [%ld:%c]\n", bp,
       hsize, (halloc ? 'a' : 'f'),
       fsize, (falloc ? 'a' : 'f'));
}

static void print_free_list(){
  printf("\nFree List: \n");
  printf("head : %p\n", head);
  void* cur_block = head;
  int i = 1;
  while (cur_block != NULL){
      printf("%d element: %p -> ", i, cur_block);
      cur_block = GET_SUCC(cur_block);
      i++;
  }
}

/*
 * max: returns x if x > y, and y otherwise.
 */
static size_t max(size_t x, size_t y) {
    return (x > y) ? x : y;
}
