/*
 ******************************************************************************
 *                               mm.c                                         *
 *           64-bit struct-based implicit free list memory allocator          *
 *                      without coalesce functionality                        *
 *                 CSE 361: Introduction to Computer Systems                  *
 *                                                                            *
 *  ************************************************************************  *
 *                     insert your documentation here. :)                     *
 *          In addition to the explicit list I implemented in the checkpoint  *
 *       version, I upgrade it to seg list which increases the throughput.    *
 *       I also implement features as remove footers and nth fit, which       *
 *       increase the util by around 3 percent each. Then at last I decrease  *
 *       the minimum_block_size into 16 bytes. This is done by squish the prev*
 *       pionter and status bits into 8 bytes. Decent challenges and huge     *
 *       amount of debugging work! But increase the util from ~60 to ~70!     *                                                       
 *  ************************************************************************  *
 *  ** ADVICE FOR STUDENTS. **                                                *
 *  Step 0: Please read the writeup!                                          *
 *  Step 1: Write your heap checker. Write. Heap. checker.                    *
 *  Step 2: Place your contracts / debugging assert statements.               *
 *  Good luck, and have fun!                                                  *
 *                                                                            *
 ******************************************************************************
 */

/* Do not change the following! */

#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <stdbool.h>
#include <stddef.h>
#include <assert.h>
#include <stddef.h>

#include "mm.h"
#include "memlib.h"

#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

/* You can change anything from here onward */

/*
 * If DEBUG is defined, enable printing on dbg_printf and contracts.
 * Debugging macros, with names beginning "dbg_" are allowed.
 * You may not define any other macros having arguments.
 */
//#define DEBUG // uncomment this line to enable debugging

#ifdef DEBUG
/* When debugging is enabled, these form aliases to useful functions */
#define dbg_printf(...) printf(__VA_ARGS__)
#define dbg_requires(...) assert(__VA_ARGS__)
#define dbg_assert(...) assert(__VA_ARGS__)
#define dbg_ensures(...) assert(__VA_ARGS__)
#else
/* When debugging is disnabled, no code gets generated for these */
#define dbg_printf(...)
#define dbg_requires(...)
#define dbg_assert(...)
#define dbg_ensures(...)
#endif

/* Basic constants */
typedef uint64_t word_t;
static const size_t wsize = sizeof(word_t);   // word and header size (bytes)
static const size_t dsize = 2*sizeof(word_t);      // double word size (bytes)
static const size_t min_block_size = 2*sizeof(word_t); // Minimum block size
static const size_t chunksize = (1 << 12);    // requires (chunksize % 16 == 0)
static const size_t nth_fit = 30;

static const word_t alloc_mask = 0x1;
static const word_t prev_alloc_mask = 0x2;
static const word_t is_tiny_mask = 0x4;
static const word_t size_mask = ~(word_t)0xF;
static const word_t special_mask = ~(word_t)0x7;
typedef struct block
{
    /* Header contains size + allocation flag */
    word_t header;
  
    /*
     * We don't know how big the payload will be.  Declaring it as an
     * array of size 0 allows computing its starting address using
     * pointer notation.
     */
     union{
    	
    	struct{
    		struct block* prev;
    		struct block* next;
    	};
    	char payload[0];
    	
    };
    /*
     * We can't declare the footer as part of the struct, since its starting
     * position is unknown
     */
     
} block_t;


/* Global variables */
/* Pointer to first block */
static block_t *heap_start = NULL;



bool mm_checkheap(int lineno);

/* Function prototypes for internal helper routines */
static block_t *extend_heap(size_t size);
static void place(block_t *block, size_t asize);
static block_t *find_fit(size_t asize);
static block_t *coalesce(block_t *block);

static size_t max(size_t x, size_t y);
static size_t round_up(size_t size, size_t n);

static word_t pack(size_t size, bool is_tiny, bool pre_alloc, bool alloc);
//static word_t pack(size_t size, bool alloc);

static size_t extract_size(word_t header);
static size_t get_size(block_t *block);
static size_t get_payload_size(block_t *block);

static bool extract_alloc(word_t header);
static bool get_alloc(block_t *block);
static bool get_prev_alloc(block_t *block);
static bool get_is_tiny(block_t *block);

static void write_header(block_t *block, size_t size,bool is_tiny,
 bool pre_alloc,bool alloc);
static void write_footer(block_t *block, size_t size,bool is_tiny,
 bool pre_alloc,bool alloc);

static block_t *payload_to_header(void *bp);
static void *header_to_payload(block_t *block);

static block_t *find_next(block_t *block);
static word_t *find_prev_footer(block_t *block);
static block_t *find_prev(block_t *block);


static void insert(block_t *block);
static void insert_helper(block_t * block,block_t * root, block_t * tail);
static void extract(block_t * block);
static block_t **seg_root(size_t size);
static block_t **seg_tail(size_t size);
//adding variables for mm_cheakheap

static block_t *root1;//16
static block_t *tail1;
static block_t *root2;//32-64
static block_t *tail2;
static block_t *root3;//64-128
static block_t *tail3;
static block_t *root4;//128-256
static block_t *tail4;
static block_t *root5;//256-512
static block_t *tail5;
static block_t *root6;//512-1024
static block_t *tail6;
static block_t *root7;//1024-4096
static block_t *tail7;
static block_t *root8;//4096-
static block_t *tail8;
//8*2*8=128 bytes total
/*
 * <what does mm_init do?>
 */
bool mm_init(void) 
{
    // Create the initial empty heap 
    word_t *start = (word_t *)(mem_sbrk(2*wsize));
    
  
    
    if (start == (void *)-1) 
    {
        return false;
    }
    start[0] = pack(0, false,true,true); // Prologue footer
    start[1] = pack(0, false,true,true); // Epilogue header
    // Heap starts with first "block header", currently the epilogue footer
    heap_start = (block_t *) &(start[1]);
    root1=NULL;
    tail1=NULL;
    root2=NULL;
    tail2=NULL;
    root3=NULL;
    tail3=NULL;
    root4=NULL;
    tail4=NULL;
    root5=NULL;
    tail5=NULL;
    root6=NULL;
    tail6=NULL;
    root7=NULL;
    tail7=NULL;
    root8=NULL;
    tail8=NULL;
    // Extend the empty heap with a free block of chunksize bytes
    if (extend_heap(chunksize) == NULL)
    {
        return false;
    }
    return true;
}

/*
 * <what does mmalloc do?>
 */
void *malloc(size_t size) 
{
    dbg_requires(mm_checkheap(__LINE__));
    size_t asize;      // Adjusted block size
    size_t extendsize; // Amount to extend heap if no fit is found
    block_t *block;
    void *bp = NULL;
    if (heap_start == NULL) // Initialize heap if it isn't initialized
    {
        mm_init();
    }
    if (size == 0) // Ignore spurious request
    {
        dbg_ensures(mm_checkheap(__LINE__));
        return bp;
    }
    //Adjust block size to include overhead and to meet alignment requirements
    //asize = round_up(size + dsize, dsize);
    asize = round_up(size + wsize, dsize);
    
    // Search the free list for a fit
   
    block = find_fit(asize);
	
    // If no fit is found, request more memory, and then and place the block
    if (block == NULL)
    {  
        extendsize = max(asize, chunksize);
        
        block = extend_heap(extendsize);
  
        if (block == NULL) // extend_heap returns an error
        {
            return bp;
        }

    }

    place(block, asize);
 
    bp = header_to_payload(block);
    dbg_printf("done malloc \n");
    dbg_ensures(mm_checkheap(__LINE__));
    
    return bp;
} 

/*
 * <what does free do?>
 * The free function will free the block by writing approprate header and 
 *footer. If the freed block's previous or next block is also free. Then 
 * the coalesce function will also be called to merge these blocks.
 */
void free(void *bp)
{
    if (bp == NULL)
    {
        return;
    }
    block_t *block = payload_to_header(bp);
    block_t *n_block = find_next(block);
    size_t size = get_size(block);//-wsize;
    bool is_tiny=get_is_tiny(block);
    bool is_ntiny=get_is_tiny(n_block);

    write_header(block, size,is_tiny, get_prev_alloc(block), false);
    write_footer(block, size,is_tiny, get_prev_alloc(block), false);
    
    if(is_ntiny){
    	write_header(n_block, special_mask&n_block->header,true,
    	false,get_alloc(n_block));
    }
    else{
    	write_header(n_block, get_size(n_block),false,
    	false,get_alloc(n_block));
    }
    coalesce(block);
   
}

/*
 * <what does realloc do?>
 * If the size is zero, realloc will work the same as free. If the pointer
 * offered is null, then it works the same as malloc. Else, adjust the block
 * that the ptr is currently pointing at and free the original block.
 */
void *realloc(void *ptr, size_t size)
{
    block_t *block = payload_to_header(ptr);
    size_t copysize;
    void *newptr;

    // If size == 0, then free block and return NULL
    if (size == 0)
    {
        free(ptr);
        return NULL;
    }

    // If ptr is NULL, then equivalent to malloc
    if (ptr == NULL)
    {
        return malloc(size);
    }

    // Otherwise, proceed with reallocation
    newptr = malloc(size);
    // If malloc fails, the original block is left untouched
    if (newptr == NULL)
    {
        return NULL;
    }

    // Copy the old data
    copysize = get_payload_size(block); // gets size of old payload
    if(size < copysize)
    {
        copysize = size;
    }
    memcpy(newptr, ptr, copysize);

    // Free the old block
    free(ptr);

    return newptr;
}

/*
 * <what does calloc do?>
 * The first part of calloc behave the same as malloc but set the payload 
 * to zero before adding data.
 */
void *calloc(size_t elements, size_t size)
{
    void *bp;
    size_t asize = elements * size;

    if (asize/elements != size)
    {    
        // Multiplication overflowed
        return NULL;
    }
    
    bp = malloc(asize);
    if (bp == NULL)
    {
        return NULL;
    }
    // Initialize all bits to 0
    memset(bp, 0, asize);

    return bp;
}

/******** The remaining content below are helper and debug routines ********/

/*
* return the appropriate root node of the seg list.
*/
static block_t **seg_root(size_t size){
	if(size==16) return &root1;
	else if (size<64) return &root2;
	else if (size<128) return &root3;
	else if (size<256) return &root4;
	else if (size<512) return &root5;
	else if (size<1024) return &root6;
	else if (size<4096) return &root7;
	else return &root8;

}


/*
* return the appropriate tail node of the seg list.
*/	
static block_t **seg_tail(size_t size){
	if(size==16) return &tail1;
	else if (size<64) return &tail2;
	else if (size<128) return &tail3;
	else if (size<256) return &tail4;
	else if (size<512) return &tail5;
	else if (size<1024) return &tail6;
	else if (size<4096) return &tail7;
	else return &tail8;

}



/*
 * extract is the helper function of the explicit list. It helps extract
 * existing free blocks in the linked list while maintain the structure.
 */
static void extract(block_t * block){
	dbg_printf("extract %p,%lx\n",block,block->header);
	bool is_tiny=get_is_tiny(block);
	block_t **root=is_tiny?&root1:seg_root(get_size(block));
	block_t **tail=is_tiny?&tail1:seg_tail(get_size(block));
	block_t *tiny_n;
	block_t *tiny_p;

	if(block==*root&&block==*tail){
		dbg_printf("extract case1\n");
	       *root = NULL;
	       *tail = NULL;
	}
	else if(block==*root){
		dbg_printf("extract case2\n");
	  	tiny_n=(block_t*)(special_mask&(word_t)block->prev);
	   	*root=is_tiny?tiny_n:block->next;
	   	if(is_tiny)
	   		write_header(*root,(size_t)NULL,true,true,false);
	   	else{
	   		
    			(*root)->prev=NULL;
	   	}

	}
	else if(block==*tail){
		dbg_printf("extract case3\n");
		tiny_p=(block_t*)(special_mask&(word_t)block->header);
		*tail=is_tiny?tiny_p:block->prev;
		if(is_tiny)
	   		write_footer(*tail,(size_t)NULL,true,true,false);
	   	else{
	   		(*tail)->next=NULL;	
	   	}
	}
	else{
	
		dbg_printf("extract case4\n");
		if(is_tiny){
			tiny_p=(block_t*)(special_mask&(word_t)block->header);
			tiny_n=(block_t*)(special_mask&(word_t)block->prev);
			write_footer(tiny_p, (size_t)tiny_n,true,true, false);
			write_header(tiny_n, (size_t)tiny_p,true,true, false);
		}
		else{
		
			block->prev->next=block->next;
			block->next->prev=block->prev;		
		}
	}

	dbg_printf("done extract\n");

}

/*
 * Another helper function of the explicit list. Insert helps inserting free 
 * blocks into the linked list. Usually called after coalecse.
 */
static void insert(block_t * block){

	dbg_printf("insert %p,%lx\n",block,block->header);
	block_t **root;
	block_t **tail;
	if(get_is_tiny(block)==true){
		root=seg_root(min_block_size);
		tail=seg_tail(min_block_size);
		if(*root==NULL&&*tail==NULL){
			dbg_printf("16insert1\n");
			*tail=block;
			*root=block;
			
			write_header(*root, (size_t)NULL,true,true,false);
			write_footer(*tail, (size_t)NULL,true,true, false);
			}
		else{
			dbg_printf("16insert2\n");
			write_header(*root, (size_t)block,true,true,false);
			write_header(block, (size_t)NULL,true,true,false);
			write_footer(block, (size_t)*root,true,true, false);
   	 		*root=block;
		
		}
	}
	else{
		root=seg_root(get_size(block));
		tail=seg_tail(get_size(block));
		if(*root==NULL&&*tail==NULL){
			dbg_printf("insert1\n");
			*tail=block;
			*root=block;
			(*tail)->next=NULL;
		}
		else{
			
			dbg_printf("insert2\n");
			(*root)->prev=block;
			block->next=*root;
			*root=block;
			block->prev=NULL;
		}
	
	}
    
}

/*
 * <what does extend_heap do?>
 * When no fit can be found, the extend_heap will be evoked to allocate 
 * more free space for the heap.
 */
static block_t *extend_heap(size_t size) 
{
    void *bp;
    
    // Allocate an even number of words to maintain alignment
    size = round_up(size, dsize);
    if ((bp = mem_sbrk(size)) == (void *)-1)
    {
        return NULL;
    }
    
    // Initialize free block header/footer 
    block_t *block = payload_to_header(bp);
    write_header(block, size,false,true, false);
    write_footer(block, size,false,true, false);
   
    // Create new epilogue header
    block_t *block_next = find_next(block);
    write_header(block_next, 0,false,false, true);
    // Coalesce in case the previous block was free
    return coalesce(block);
}

/*
 * <what does coalesce do?>
 * When there is a block being freed in the heap, the coalesce function
 * will be called to merge any consecutive free blocks to reduce the 
 * external space fragmentaion of the heap.
 */
static block_t *coalesce(block_t * block) 
{
	
	dbg_printf("coalesce  %p,%lx\n",block,block->header);
	
	bool tiny=get_is_tiny(block);
	bool p_alloc=get_prev_alloc(block);
	block_t *nblock=find_next(block);
	block_t *pblock=p_alloc? NULL:find_prev(block);
	bool n_alloc=extract_alloc(nblock->header);
	
	bool p_tiny= p_alloc? false:get_is_tiny(pblock);
	bool n_tiny=get_is_tiny(nblock);
	
	size_t size=tiny? min_block_size:get_size(block);
	size_t nsize=n_tiny? min_block_size:get_size(nblock);
	size_t psize;
	
	 if (n_alloc&&!p_alloc){
		dbg_printf("coalescse case 2\n");
		psize=p_tiny? min_block_size:get_size(pblock);
		psize+=size;
		extract(pblock);
   	 	write_header(pblock, psize,false, true,false);
   	 	write_footer(pblock, psize,false, true,false);
   	 	block=pblock;
	}
	else if(p_alloc&&!n_alloc){
		dbg_printf("coalescse case 3\n");
		extract(nblock);
		nsize+=size;
    		write_header(block, nsize, false,true,false);
    		write_footer(block, nsize, false,true,false);
	
	}
	else if(!p_alloc&&!n_alloc){
	dbg_printf("coalescse case 4\n");
	
		psize=p_tiny? min_block_size:get_size(pblock);
		psize+=size;
		psize+=nsize;
		extract(pblock);
		extract(nblock);
		write_header(pblock, psize,false,true, false);
   	 	write_footer(pblock, psize,false,true,false);
		block=pblock;
	}
	
	insert(block);
	dbg_printf("done coalecse\n");
    return block;
}

/*
 * <what does place do?>
 *Get the size of the current empty block first. If placing the block would 
 *result an unused block of size smaller than min_block_size, then use the 
 *csize as the size of this block. Otherwise use the provided asize to 
 *initialize the block. 
 *Then set up the remaining empty space as a new empty block.
 */
static void place(block_t *block, size_t asize)
{
    size_t csize = get_size(block);
    dbg_printf("start place %p,%lx\n",block,asize);
    block_t *block_next;
    bool is_tiny=false;
    extract(block);
    if ((csize - asize) >= min_block_size)
    {
    	if(asize==min_block_size)
    		is_tiny=true;
        write_header(block, asize,is_tiny,get_prev_alloc(block), true);
        dbg_printf(" block %p,header%lx\n"
    	    	 ,block,block->header);
        is_tiny=false;
        block_next = find_next(block);
	if(csize - asize==min_block_size)
		is_tiny=true;
        write_header(block_next, csize-asize,is_tiny,true, false);
        write_footer(block_next, csize-asize,is_tiny,true, false);
    	dbg_printf(" block_next %p,header%lx\n"
    	    	 ,block_next,block_next->header);
    		
        insert(block_next);
        
    }
    else{ 
    	block_next = find_next(block);
    	is_tiny=(csize==min_block_size)? true:false;
        write_header(block, csize,is_tiny,get_prev_alloc(block), true);
 	write_header(block_next, get_size(block_next),get_is_tiny(block_next)
 	,true, get_alloc(block_next));
    }
   
   }

/*
 * <what does find_fit do?>
 *iterate through the linked list until it find the appropriate unused 
 *block. return the block pointer if find one, null if doesn't.
 * currently use nth fit. 
 */
static block_t *find_fit(size_t asize)
{
    size_t count = 0;
    size_t temp_size = asize;
    block_t* block;
    block_t* best_fit = NULL;
    while (true) {
        for (block = *seg_root(temp_size); block != NULL; block = block->next)
        {
            if (asize <= get_size(block)) {

                if (asize == get_size(block)) {
                    return block;
                }

                if (!count) {//first found
                    best_fit = block;
                }
                else {
                    if (get_size(best_fit)>get_size(block)){//find a better one
                        best_fit = block;
                    }
                }
                count++;
                if (count >= nth_fit) {
                    return best_fit;
                }
            }

        }
        if (block->next == NULL || block == NULL) {//move to the next seg list
            if (temp_size >= chunksize) {//if we have searched all seg list
                break;
            }
            temp_size += temp_size;
        }
    }
    return best_fit;
}

/* 
 * <what does your heap checker do?>
 * Please keep modularity in mind when you're writing the heap checker!
 * First check the seglist1. Do all free blocks in list 1 all tiny blocks?
 * 
 * Then check the seglist 2-8 for the following:
 * It will check whether block->prev->next=block.
 * Are there any two consecctive empty blocks?(check coalesce)
 * Does each seg list only contain blocks with correct size?
 * Does the pre_alloc bit set correctly?
 * Does the alloc bit set correctly?
 * 
 * 
 * 
 */
bool mm_checkheap(int line)  
{ 

    block_t * temp=root1;//Check the seg list 1
    while(temp!=NULL){
     dbg_printf("print block %p,footer%lx,header%lx\n"
    	     ,temp,(word_t)temp->prev,temp->header);
    	if(get_is_tiny(temp)==false){
    	    dbg_printf("Error at %p,%lx, not a tiny block\n"
    	     ,temp,(word_t)temp->prev);
    	}
	
    	temp=(block_t*)(special_mask&(word_t)temp->prev);//temp=temp->next
    
    }
    block_t** root;
    block_t** tail;
    size_t temp_size=min_block_size<<1;
    while(true){
        root = seg_root(temp_size);//move to the next seg list
        tail= seg_tail(temp_size);
        for (block_t* temp =*root;temp!=NULL;temp=temp->next){
            dbg_printf("current size%lx\n", temp_size);
            dbg_printf("%p,%lx\n", temp, temp->header);
        if (temp != *tail) {//avoid seg fault
            if (temp->next->prev != temp) {
                dbg_printf("Error at %p,%lx,temp->next->prev!=temp\n",
                    temp, temp->header);
            }
           
        }
        if (get_alloc(temp) == get_alloc(find_next(temp))) {
            dbg_printf(
                "Error at %p,%lx, two consecutive empty block\n",
                temp, temp->header);
        }
        if (get_size(temp) > temp_size) {
            dbg_printf(
                "Error at %p,%lx, block size too big.\n"
                , temp, temp->header);

        }
        if (get_alloc(temp) != get_prev_alloc(find_next(temp))) {
            dbg_printf(
                "Error at %p,%lx,prev_alloc bit not approriately set.\n"
                , find_next(temp), find_next(temp)->header);
        }
        if (get_alloc(temp) == true) {
            dbg_printf(
                "Error at %p,%lx,alloc bit not approriately set.\n"
                , temp, temp->header);
        }
        }
	    if(temp->next==NULL){
		    if(temp_size>=chunksize){//we searched entire seg list
    			break;
    		}
		    temp_size+=temp_size;//double the temp_size 
	    }
    }

    return true;
}

/*
 * max: returns x if x > y, and y otherwise.
 */
static size_t max(size_t x, size_t y)
{
    return (x > y) ? x : y;
}

/*
 * round_up: Rounds size up to next multiple of n
 */
static size_t round_up(size_t size, size_t n)
{
    return (n * ((size + (n-1)) / n));
}

/*
 * pack: returns a header reflecting a specified size and its alloc status.
 * If the block is allocated, the lowest bit is set to 1, and 0 otherwise.
 * If the previous block is allocated, set 2nd lowset bit to 1, 0 otherwise.
 * If the block is tiny(16byte), set 3rd lowest bit to 1, 0 otherwise.
 */
static word_t pack(size_t size, bool is_tiny, bool pre_alloc,bool alloc)
{
     size=alloc ? (size | alloc_mask) : size;
     size=is_tiny ? (size | is_tiny_mask) : size;
     return pre_alloc ? (size | prev_alloc_mask) : size;
}


/*
 * extract_size: returns the size of a given header value based on the header
 *               specification above.
 */
static size_t extract_size(word_t word)
{
    return (word & size_mask);
}

/*
 * get_size: returns the size of a given block by clearing the lowest 4 bits
 *           (as the heap is 16-byte aligned).
 */
static size_t get_size(block_t *block)
{
    return get_is_tiny(block)? min_block_size:extract_size(block->header);
}

/*
 * get_payload_size: returns the payload size of a given block, equal to
 *                   the entire block size minus the header and footer sizes.
 */
static word_t get_payload_size(block_t *block)
{
    size_t asize = get_size(block);
    return asize - wsize;
}

/*
 * extract_alloc: returns the allocation status of a given header value based
 *                on the header specification above.
 */
static bool extract_alloc(word_t word)
{
    return (bool)(word & alloc_mask);
}
/*
 * get_prev_alloc: returns true when the previous block is allocated based on 
 * the block header's lowest bit, and false otherwise.
 */
static bool get_prev_alloc(block_t *block)
{
	return (bool)(block->header & prev_alloc_mask);
}

/*
 * get_is_tiny: returns true the block is marked as tiny(16 byte),
 * and false otherwise.
 */
static bool get_is_tiny(block_t *block)
{
	return (bool)(block->header & is_tiny_mask);
}
/*
 * get_alloc: returns true when the block is allocated based on the
 *            block header's lowest bit, and false otherwise.
 */
static bool get_alloc(block_t *block)
{
    return extract_alloc(block->header);
}

/*
 * write_header: given a block and its size and allocation status,
 *               writes an appropriate value to the block header.
 */
static void write_header(block_t *block, size_t size, bool is_tiny,
bool pre_alloc,bool alloc )
{
    block->header = pack(size,is_tiny, pre_alloc, alloc);
}


/*
 * write_footer: given a block and its size and allocation status,
 *               writes an appropriate value to the block footer by first
 *               computing the position of the footer.
 */
static void write_footer(block_t *block, size_t size, bool is_tiny, 
bool pre_alloc, bool alloc)
{
    word_t *footerp = (word_t *)((block->payload) + get_size(block)-dsize);
    *footerp = pack(size, is_tiny,pre_alloc, alloc);

}


/*
 * find_next: returns the next consecutive block on the heap by adding the
 *            size of the block.
 */
static block_t *find_next(block_t *block)
{
    dbg_requires(block != NULL);
    
    block_t *block_next = (block_t *)(((char *)block) + get_size(block));
    dbg_ensures(block_next != NULL);
    return block_next;
}

/*
 * find_prev_footer: returns the footer of the previous block.
 */
static word_t *find_prev_footer(block_t *block)
{
    // Compute previous footer position as one word before the header
  
    return (&(block->header)) - 1;
}

/*
 * find_prev: returns the previous block position by checking the previous
 *            block's footer and calculating the start of the previous block
 *            based on its size.
 */
static block_t *find_prev(block_t *block)
{
    word_t *footerp = find_prev_footer(block);
    size_t size =(*footerp&is_tiny_mask)?min_block_size:extract_size(*footerp);
    size=size ? size:8;//differentiate between epilogue footer and original 
    //footer
    return (block_t *)((char *)block - size);
}

/*
 * payload_to_header: given a payload pointer, returns a pointer to the
 *                    corresponding block.
 */
static block_t *payload_to_header(void *bp)
{
    return (block_t *)(((char *)bp) - offsetof(block_t, payload));
}

/*
 * header_to_payload: given a block pointer, returns a pointer to the
 *                    corresponding payload.
 */
static void *header_to_payload(block_t *block)
{
    return (void *)(block->payload);
}
