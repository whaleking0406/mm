/*
 * mm.c
 *
 * Name: Jingyu Wang   ID: jingyuw  Section: I
 * Util: 91%    KOPs: 15100   PERFINDEX: 98
 *
 * Overall Algorithm Description:
 * 
 * Major:
 * In this assignment, I used segregated free lists to hold the small
 * (block threshold = 40 bytes) free blocks, and used BSTs to hold 
 * larger free blocks.
 *
 * For each segregated list, every list keeps a fixed size free block,
 * and the entrances are places at the beginning of the heap, i.e, inside
 * the prologue block. The list are doubly linked, and ranges from [16-40].
 *
 * For each binary search tree, every tree node are different in size. If
 * we insert a block with same size, we doubly linked it to the tree node,
 * and then it can be regarded as a segregated free list with identical size.
 * The entrances of Seglist and BST are illustrated as following.
 *
 *
 * [padding][prologue H][Seglist 0]...[Seglist 3][BST 1][BST 2][prologue F]..
 *
 *
 * For smaller free blocks, they have the structure as:
 *
 * [Header][Next ptr][Prev ptr][Footer]
 *
 * And organized in doubly linked segregated list as (two lines together):
 * 
 * [block 1]->[block 2]->[block 2]....->NULL
 * [size t ]<-[size t ]<-[size t ]....
 * 
 * in which next ptr is the address of next same-size free block in doubly
 * list.
 *
 *
 *
 * For larger ones:
 * 
 * [Header][Next ptr][Prev ptr][Left ptr][Right ptr][Label][XXX][Footer]
 *
 * And organized in BST as:
 *
 *            ...[left  child]->[parent]<-[right child] ...
 *            ...[size c     ]<-[size a]->[size b     ] ...
 *                                ||
 *                             [block 2]
 *                             [size a ]
 *                                ||
 *                             [block 2]
 *                             [size a ]
 *                               ....
 *                                ||
 *                               NULL
 * 
 *
 * in which next is the same as above, prev is either the parent in tree or
 * the same-size block in list, left ptr is to the left child, label tag is
 * one of the four: Left, Right, Root or Segnode, indicating: this block is
 * a left child, right child, root of a tree, or a node in segregated list,
 * repectively.
 *
 *
 * Minor:
 * For allocated block, it doesn't have a footer, and I include the allocated
 * information in the header of the block next to it. More specifically, a
 * block's header's last bit indicates itself is allocated or not, second-to
 * last bit indicates the previous block is allocated or not. For this reason,
 * the minimum block size is 2 * DSIZE = 16 bytes.
 *
 * For the ptr shown above, it is actually an offset to the heap_listp, because
 * the heap never exceeds 2^32 so the offset is always a 4 bytes positive int. 
 *
 * If we find a same size block in BST, we prefer to return the same-size block
 * next to it in its following list, because it will save some unnecessary
 * linking jobs.
 *
 * 
 */

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <unistd.h>
#include "contracts.h"

#include "mm.h"
#include "memlib.h"


// Create aliases for driver tests
// DO NOT CHANGE THE FOLLOWING!
#ifdef DRIVER
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif

/*
 *  Logging Functions
 *  -----------------
 *  - dbg_printf acts like printf, but will not be run in a release build.
 *  - checkheap acts like mm_checkheap, but prints the line it failed 
 *  - on and exits if it fails.
 */

#ifndef NDEBUG
#define dbg_printf(...) printf(__VA_ARGS__)
#define checkheap(verbose) do {if (mm_checkheap(verbose)) {  \
                    printf("Checkheap failed on line %d\n", __LINE__);\
                    exit(-1);  \
                    }}while(0)
#else
#define dbg_printf(...)
#define checkheap(...)
#endif


#define WSIZE 4
#define DSIZE 8
#define CHUNKSIZE (1<<6) /* Chunk size that every time extend heap */
#define MAXCHUNK 0xFFFFFFFF /* Maximum allocated chunk size */
#define ROOT 0   /* Label Tag: A free block is root */
#define RIGHT 1  /* A free block is a left child */
#define LEFT 2  /* A free block is a right child */
#define SEGNODE 3 /* A free block is a seg node */

#define SEGNUM 3 /* Segregated list number */
#define MAXBINNUM 5 /* Total bin numer */
#define BLKTHRES 40 /* Block threshold */



char *heap_listp;
void *Root; /* pointer to the entrace of storage structure */


/*
 * ---------------------------------------
 *  Small Helper Functions start from here
 *  --------------------------------------
 */

static inline int Max(int x, int y){
    if(x > y) return x;
    return y;
}

/* Pack a size and allocated bit into a word */
static inline size_t Pack(size_t size, int alloc){
    return (size | alloc);
}

/* Read and write a word at address p */
static inline size_t Get(void *p){
    return (*(unsigned int *)(p));
}

static inline void Put(void *p, int val){
    (*(unsigned int *)(p)) = val;
}

/* Write a word at address p, while keeping the PrevAlloc bit */
static inline void PutLabel(void *p, int val){
    unsigned int temp = ((*(unsigned int *)(p)) & 0x2);
    (*(unsigned int *)(p)) = (val | temp);
}

/* Read the size from address p */
static inline size_t GetSize(void *p){
    return (Get(p) & ~0x7);
}

/* Given block ptr bp, compute address ofits header */
/* and footer, if it has any */
static inline void *HDRP(void *bp){
    return (void *)((char *)(bp) - WSIZE);
}

static inline void *FTRP(void *bp){
    return (void *)((char *)(bp) + GetSize(HDRP(bp)) - DSIZE);
}

/* Read the allocated fields from address p */
static inline int GetAlloc(void *p){
    return (Get(HDRP(p)) & 0x1);
}


/* Given block ptr bp, compute address of next and previous */
/* blocks. Note that it requres the block's footer */
static inline void *NextBlkp(void *bp){
    return (void *)((char *)(bp) + GetSize((char *)(bp) - WSIZE));
}

static inline void *PrevBlkp(void *bp){
    return (void *)((char *)(bp) - GetSize((char *)(bp) - DSIZE));
}

/* Given block ptr, decide whether the next/prev block is */
/* allocated */
static inline int GetNextAlloc(void *p){
    return (Get(HDRP(NextBlkp(p))) & 0x1);
}

static inline int GetPrevAlloc(void *p){
    return (Get(HDRP(p)) & 0x2) >> 1;
}


/* Given a pointer to a block, return the ptr to its Next field */
static inline void *NextPtr(void *bp){
    return bp;
}

/* Given a pointer to a block, return the ptr to its Label field */
static inline void *LabelPtr(void *bp){
    return (void *)((char *)(bp) + 4 * WSIZE);
}

/* Given a pointer to a block, return the ptr to its Prev field */
static inline void *PrevPtr(void *bp){
    return (void *)((char *)(bp) + 1 * WSIZE);
}

/* Given a pointer to a block, return the ptr to its Left field */
static inline void *LeftPtr(void *bp){
    return (void *)((char *)(bp) + 2 * WSIZE);
}

/* Given a pointer to a block, return the ptr to its Right field */
static inline void *RightPtr(void *bp){
    return (void *)((char *)(bp) + 3 * WSIZE);
}

/* Given a pointer, if it is NULL, return 0; if non-null */
/* return the offset to heap_listp, so that it is a 32 bit word */
static inline unsigned int PtrToInt(void *ptr){
    if(ptr == NULL) return 0;
    return (unsigned int)((unsigned long)ptr -
                          (unsigned long)heap_listp);
}


/* Given an unsigned int, if it is 0, return NULL; if non-zero */
/* return (offset + heap_listp), so that it is a 64 bit pointer */
static inline void *IntToPtr(unsigned int val){
    if(val == 0) return NULL;
    return (void *)((unsigned long)val + (unsigned long)heap_listp);
}


/* Given a pointer to a block, return the address of a freed */
/* block previous to it in a list or its parent in a tree */
static inline void *PrevFreed(void *bp){
    return IntToPtr(Get((PrevPtr(bp))));
}

/* Given a pointer to a block, return the address of a freed */
/* block next to it in a list */
static inline void *NextFreed(void *bp){
    return IntToPtr(Get((NextPtr(bp))));
}

/* Given a pointer to a block, return the address of its left */
/* free child */
static inline void *LeftFreed(void *bp){
    return IntToPtr(Get((LeftPtr(bp))));
}

/* Given a pointer to a block, return the address of its right */
/* free child */
static inline void *RightFreed(void *bp){
    return IntToPtr(Get((RightPtr(bp))));
}

/* The following two functions set the header of the next block */
/* Set the second-to-last LSB to 0 if next block is freed */
/* Set it to 1 if allocated */
static inline void ResetNextHDR(void *bp){
    Put(HDRP(NextBlkp(bp)), Get(HDRP(NextBlkp(bp))) & (~0x2));
}

static inline void SetNextHDR(void *bp){
    Put(HDRP(NextBlkp(bp)), Get(HDRP(NextBlkp(bp))) | (0x2));
}


/* Give the adjusted size of a block, return the bin index */
/* it belongs to */
static inline size_t GetBinInd(size_t asize){
    if(asize == 16) return 0;
    if(asize == 24) return 1;
    if(asize == 32) return 2;
    if(asize == 40) return 3;
    if(40 < asize && asize <= 64) return 4;
    return 5;
}

/* Give the bin index, get the address of the bin */
static inline void *GetBinAdd(size_t binNum){
    return (void *)((char *)Root + binNum * WSIZE);
}


/* The next two funcions re-link the block bp and */
/* its parent in BST, it will link the downward pointer */
/* to address given by (temp) */
static inline void ChangeLink(void *bp, void *temp){
    if(Get(LabelPtr(bp)) == LEFT){
        Put(LeftPtr(PrevFreed(bp)), PtrToInt(temp));
        Put(LabelPtr(temp), LEFT);
    }
    else if(Get(LabelPtr(bp)) == RIGHT){
        ENSURES(Get(LabelPtr(bp)) == RIGHT);
        Put(RightPtr(PrevFreed(bp)), PtrToInt(temp));
        Put(LabelPtr(temp), RIGHT);
    }
    else{
        ENSURES(Get(LabelPtr(bp)) == ROOT);
        Put(NextPtr(PrevFreed(bp)), PtrToInt(temp));
        Put(LabelPtr(temp), ROOT);
    }    
}

static inline void ChangeLinkToNull(void *bp){
    if(Get(LabelPtr(bp)) == LEFT){
        Put(LeftPtr(PrevFreed(bp)), PtrToInt(NULL));
    }
    else if(Get(LabelPtr(bp)) == RIGHT){
        Put(RightPtr(PrevFreed(bp)), PtrToInt(NULL));
    }
    else{
        ENSURES(Get(LabelPtr(bp)) == ROOT);
        Put(NextPtr(PrevFreed(bp)), PtrToInt(NULL));
    }    
}



/*
 * -----------------------------------
 *  Block Functions start from here
 *  ----------------------------------
 */



/* Helper function that insert a block in to doubly linked */
/* segregated list */
void DlistInsert(void *bp, size_t asize){
    dbg_printf("Doubly list insertion to binNum %zu\n", GetBinInd(asize));
    
    /* Determine which bin to insert to */
    size_t binNum = GetBinInd(asize);
    void *BinAdd = GetBinAdd(binNum);
    void *Entry = IntToPtr(Get(BinAdd));
    
    /* If currently there is no node in bin */
    if(Entry == NULL){
        dbg_printf("First element inserted to binNum %zu\n", binNum);
        Put(NextPtr(bp), PtrToInt(NULL));
        Put(PrevPtr(bp), PtrToInt(BinAdd));
        Put(NextPtr(BinAdd), PtrToInt(bp));
        ENSURES(IntToPtr(Get(BinAdd)) != NULL);
        ENSURES(NextFreed(IntToPtr(Get(BinAdd))) == NULL);
    }
    
    /* Elsewise, doubly link the node */
    else{
        dbg_printf("Inserting to binNum %zu\n", binNum);
        ENSURES(Entry != NULL);
        Put(NextPtr(bp), PtrToInt(Entry));
        Put(PrevPtr(Entry), PtrToInt(bp));
        Put(PrevPtr(bp), PtrToInt(BinAdd));
        Put(NextPtr(BinAdd), PtrToInt(bp));
    }    
}


/* Recursion helper function that insert a block into BST */
void TreeInsertRecur(void *bp, void *Entry){
    
    int diff = GetSize(HDRP(bp)) - GetSize(HDRP(Entry));
    
    /* Find the same size block, insert the segregated list */
    /* following it */
    if(diff == 0){
        ENSURES(Get(LabelPtr(Entry)) != SEGNODE);
        Put(NextPtr(bp), Get(NextPtr(Entry)));
        if(NextFreed(Entry) != NULL){
            ENSURES(Get(LabelPtr(NextFreed(Entry))) == SEGNODE);
            Put(PrevPtr(NextFreed(Entry)), PtrToInt(bp));
        }
        Put(NextPtr(Entry), PtrToInt(bp));
        Put(PrevPtr(bp), PtrToInt(Entry));
        Put(LabelPtr(bp), SEGNODE);
        return;
    }
    
    /* Go to right branch */
    if(diff > 0 && RightFreed(Entry) != NULL){
        TreeInsertRecur(bp, RightFreed(Entry));
    }
    
    /* Go to left branch */
    else if(diff < 0 && LeftFreed(Entry) != NULL){
        TreeInsertRecur(bp, LeftFreed(Entry));
    }
    
    /* Can not find a block with same size, insert tree node */
    else{
        Put(RightPtr(bp), PtrToInt(NULL));
        Put(LeftPtr(bp), PtrToInt(NULL));
        Put(NextPtr(bp), PtrToInt(NULL));
        Put(PrevPtr(bp), PtrToInt(Entry));
        
        if(diff > 0){
            /* Insert to right branch */
            ENSURES(RightFreed(Entry) == NULL);
            Put(RightPtr(Entry), PtrToInt(bp));
            Put(LabelPtr(bp), RIGHT);
        }
        else{
            /* Insert to left branch */
            ENSURES(diff < 0);
            ENSURES(LeftFreed(Entry) == NULL);
            Put(LeftPtr(Entry), PtrToInt(bp));
            Put(LabelPtr(bp), LEFT);
        }
    }    
}


/* Insert a freed block into a BST, it will call a recursion */
/* helper function to decide where to insert */
void TreeInsert(void *bp, size_t asize){
    dbg_printf("Tree insertion to binNum %zu\n", GetBinInd(asize));
    
    /* Determine which bin to insert to */
    size_t binNum = GetBinInd(asize);
    void *BinAdd = GetBinAdd(binNum);
    void *Entry = IntToPtr(Get(BinAdd));

    /* If currently there is no node in bin */
    if(Entry == NULL){
        Put(PrevPtr(bp), PtrToInt(BinAdd));
        Put(RightPtr(bp), PtrToInt(NULL));
        Put(LeftPtr(bp), PtrToInt(NULL));
        Put(NextPtr(bp), PtrToInt(NULL));
        Put(NextPtr(BinAdd), PtrToInt(bp));
        Put(LabelPtr(bp), ROOT);
        REQUIRES(IntToPtr(Get(BinAdd)) != NULL);
        dbg_printf("Inserting tree root\n");
    }
    
    /* Go to tree node insertion step */
    else TreeInsertRecur(bp, Entry);
    
}


/* Insert a freed block */
/* First it will decide whether to insert to segregated list */
/* or to BST, based on the adjusted size of the block, and then */
/* call different function to accomplish this task */
void InsertBlock(void *bp, size_t asize){
    dbg_printf("Inserting block with size %zu\n",
               GetSize(HDRP(bp)));

    if(asize <= BLKTHRES) DlistInsert(bp, asize);
    else TreeInsert(bp, asize);

}


/* Helper function that delete a block from doubly linked */
/* segregated list */
void DlistDelete(void *bp){
    dbg_printf("Doubly list deletion\n");
    
    /* If the node is the last one in this list */
    if(NextFreed(bp) == NULL){
        Put(NextPtr(PrevFreed(bp)), PtrToInt(NULL));
        dbg_printf("Deleting last node\n");
    }
    
    /* Elsewise, redirect the linkings */
    else{
        Put(NextPtr(PrevFreed(bp)), Get(NextPtr(bp)));
        Put(PrevPtr(NextFreed(bp)), Get(PrevPtr(bp)));
        dbg_printf("Deleting node\n");
    }    
}


/* Helper function that delete a block from BST: huge task */
/* If the given block is not a tree node, it is identical to */
/* doubly linked list deletion; elsewise, do tree node deletion */
void TreeDelete(void *bp){
    dbg_printf("Tree deletion---");
    
    void *temp;
    
    /* Deleting a node in segregated list in tree */
    /* Same as doubly list deletion */
    if(Get(LabelPtr(bp)) == SEGNODE){
        DlistDelete(bp);
    }
    
    /* Deleting a node in tree which has following list */
    /* Shift the following list */
    else if(NextFreed(bp) != NULL){
        temp = NextFreed(bp);
        ENSURES(Get(LabelPtr(bp)) != SEGNODE);
        if(RightFreed(bp) != NULL){
            Put(PrevPtr(RightFreed(bp)), Get(NextPtr(bp)));
        }
        if(LeftFreed(bp) != NULL){
            Put(PrevPtr(LeftFreed(bp)), Get(NextPtr(bp)));
        }
        Put(LeftPtr(temp), Get(LeftPtr(bp)));
        Put(RightPtr(temp), Get(RightPtr(bp)));
        Put(PrevPtr(temp), Get(PrevPtr(bp)));
        ChangeLink(bp, temp);
    }
    
    
    /* Deleting a node in tree that has no following list */
    /* Delete the whole node from BST */
    else if(LeftFreed(bp) != NULL && RightFreed(bp) != NULL){
        ENSURES(NextFreed(bp) == NULL);
        ENSURES(Get(LabelPtr(bp)) != SEGNODE);
        dbg_printf("This node has left and right---");
        temp = RightFreed(bp);
        ENSURES(temp != NULL);
        
        /* If right child doesn't have left child */
        if(LeftFreed(temp) == NULL){
            dbg_printf("This node's right have no left---");
            Put(PrevPtr(temp), Get(PrevPtr(bp)));
            Put(LeftPtr(temp), Get(LeftPtr(bp)));
            Put(PrevPtr(LeftFreed(bp)), Get(RightPtr(bp)));
            ChangeLink(bp, temp);
        }
        
        /* If right child has left child, find the leftmost node */
        /* to replace the deleted node */
        else{
            dbg_printf("This node's right have left---");
            while(LeftFreed(temp) != NULL){
                temp = LeftFreed(temp);
            }
            ENSURES(LeftFreed(temp) == NULL);
            
            if(RightFreed(temp) != NULL){
                REQUIRES(Get(LabelPtr(RightFreed(temp))) == RIGHT);
                Put(PrevPtr(RightFreed(temp)), Get(PrevPtr(temp)));
                Put(LabelPtr(RightFreed(temp)), LEFT);
            }
            Put(LeftPtr(PrevFreed(temp)), Get(RightPtr(temp)));
            Put(PrevPtr(temp), Get(PrevPtr(bp)));
            Put(LeftPtr(temp), Get(LeftPtr(bp)));
            Put(RightPtr(temp), Get(RightPtr(bp)));
            Put(PrevPtr(RightFreed(bp)), PtrToInt(temp));
            Put(PrevPtr(LeftFreed(bp)), PtrToInt(temp));
            ChangeLink(bp, temp);
        }
    }
    
    /* If the deleted node has only left child */
    else if(LeftFreed(bp) != NULL){
        dbg_printf("This node has only left---");
        temp = LeftFreed(bp);
        ChangeLink(bp, temp);
        Put(PrevPtr(temp), Get(PrevPtr(bp)));
    }
    
    /* If the deleted node has only right child */
    else if(RightFreed(bp) != NULL){
        dbg_printf("This node has only right---");
        temp = RightFreed(bp);
        ChangeLink(bp, temp);
        Put(PrevPtr(temp), Get(PrevPtr(bp)));        
    }
    
    /* The deleted node has no child */
    else{
        dbg_printf("This node has no child---");
        ChangeLinkToNull(bp);
    }
    dbg_printf("\n");
}


/* Delete a node from explicit list given a pointer to it */
/* If the size is less than block threshold, delete it in list */
/* else, delete it in BST */
void DeleteBlock(void *bp){
    dbg_printf("Deleting block with size %zu\n",
               GetSize(HDRP(bp)));
    
    size_t asize = GetSize(HDRP(bp));
    
    if(asize <= BLKTHRES) DlistDelete(bp);
    else TreeDelete(bp);

}


/* coalesce: Boundary tag coalescing. Return ptr to coalesced block */
static void *coalesce(void *bp){
    
    dbg_printf("Coalesce in:  ");
    
    size_t prev_alloc = GetPrevAlloc(bp);
    size_t next_alloc = GetNextAlloc(bp);
    size_t size = GetSize(HDRP(bp));
    
    if(prev_alloc && next_alloc){              /* case 1 */
        dbg_printf("Case 1\n");
        return bp;
    }
    
    else if(prev_alloc && !next_alloc){        /* case 2 */
        dbg_printf("Case 2\n");
        DeleteBlock(NextBlkp(bp));
        size += GetSize(HDRP(NextBlkp(bp)));
        PutLabel(HDRP(bp), Pack(size, 0));
        PutLabel(FTRP(bp), Pack(size, 0));
    }

    else if(!prev_alloc && next_alloc){        /* case 3 */
        dbg_printf("Case 3\n");
        DeleteBlock(PrevBlkp(bp));
        size += GetSize(HDRP(PrevBlkp(bp)));
        PutLabel(FTRP(bp), Pack(size, 0));
        PutLabel(HDRP(PrevBlkp(bp)), Pack(size, 0));
        bp = PrevBlkp(bp);
    }
    
    else{                                      /* case 4 */
        dbg_printf("Case 4\n");
        DeleteBlock(NextBlkp(bp));
        DeleteBlock(PrevBlkp(bp));
        size += GetSize(HDRP(PrevBlkp(bp))) +
                GetSize(FTRP(NextBlkp(bp)));
        PutLabel(HDRP(PrevBlkp(bp)), Pack(size, 0));
        PutLabel(FTRP(NextBlkp(bp)), Pack(size, 0));
        bp = PrevBlkp(bp);
    }
    
    return bp;
}


/* extend_heap: Extend heap with free block */
/* and return its block pointer */
static void *extend_heap(size_t words){
    
    char *bp;
    size_t size;
    
    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if((long)(bp = mem_sbrk(size)) == -1){
        return NULL;
    }
    
    dbg_printf("extend_heap by %d\n", (int)size);
    
    /* Initialize free block header/footer and the epilogue header */
    PutLabel(HDRP(bp), Pack(size, 0));         /* Free block header */ 
    PutLabel(FTRP(bp), Pack(size, 0));         /* Free block footer */ 
    PutLabel(HDRP(NextBlkp(bp)), Pack(0, 1));  /* New epilogue header */ 
    ResetNextHDR(bp);         /* Its predecessor must be a free block */
    
    /* if the previous block was free */
    return coalesce(bp);
}


/* FindFit: first it will decide search in segregated list or */
/* in BST based on asize. If cannot find in seglist, it will  */
/* proceed to BST. In BST, it wil find the block with exact the */
/* same size or the closest size larger than requirement */
static inline void *FindFit(size_t asize){
    
    /* Decide which bin to search */
    size_t binNum = GetBinInd(asize);
    void *BinAdd = GetBinAdd(binNum);
    void *bp = IntToPtr(Get(BinAdd));
    
    /* Used to record the closest size in BST */
    void *tempAdd;
    unsigned int tempSize;
    
    /* Segregated list searching */
    if(binNum <= SEGNUM){
        if(bp != NULL && asize == GetSize(HDRP(bp))){
            dbg_printf("Find asize in list = %zu\n", GetSize(HDRP(bp)));
            return bp;
        }
        /* Can not find a free block in segregated list */
        else binNum = SEGNUM + 1;   /* Go to BST */
    }
    
    /* BST searching */
    while(binNum <= MAXBINNUM){
        
        /* Keep searching */
        BinAdd = GetBinAdd(binNum);
        bp = IntToPtr(Get(BinAdd));
        
        tempAdd = NULL;
        tempSize = MAXCHUNK;
        
        binNum++;
        
        while(bp != NULL){
            if(asize < GetSize(HDRP(bp))){
                if(GetSize(HDRP(bp)) < tempSize){
                    /* Save the block that is larger */
                    tempSize = GetSize(HDRP(bp));
                    tempAdd = bp;
                }
                bp = LeftFreed(bp);
            }
            else if(asize > GetSize(HDRP(bp))){
                bp = RightFreed(bp);
            }
            else{
                ENSURES(asize == GetSize(HDRP(bp)));
                dbg_printf("Find asize in tree = %zu\n",
                           GetSize(HDRP(bp)));
                
                /* If the tree node has following segregated list */
                /* we prefer returning the node in list rather than */
                /* the tree node itself */
                /* It will save some re-linking jobs */
                if(NextFreed(bp) == NULL){
                    ENSURES(Get(LabelPtr(bp)) != SEGNODE);
                    return bp;
                }
                else{
                    ENSURES(GetSize(HDRP(bp)) ==
                            GetSize(HDRP(NextFreed(bp))));
                    return NextFreed(bp);
                }
            }
        }
        
        /* Can not find an exact same size block, considering to */
        /* return the closest one */
        if(tempAdd != NULL){
            dbg_printf("Find asize in other tree = %zu\n",
                       GetSize(HDRP(tempAdd)));
            
            /* Same trick as above */
            if(NextFreed(tempAdd) == NULL){
                ENSURES(Get(LabelPtr(tempAdd)) != SEGNODE);
                return tempAdd;
            }
            else{
                ENSURES(GetSize(HDRP(tempAdd)) ==
                        GetSize(HDRP(NextFreed(tempAdd))));
                return NextFreed(tempAdd);
            }
        }
    }
    
    return NULL;
}



/* place: Place block of asize bytes at start of free block bp */
/* and split if remainder would be at least minimum block size */
static inline void Place(void *bp, size_t asize){
    
    size_t csize = GetSize(HDRP(bp));
    void *newPtr;
    
    if((csize - asize) >= (2 * DSIZE)){
        
        PutLabel(HDRP(bp), Pack(asize, 1));
        PutLabel(FTRP(bp), Pack(asize, 1)); /* Overwitten later */
        SetNextHDR(bp);
        
        newPtr = NextBlkp(bp);
        PutLabel(HDRP(newPtr), Pack(csize-asize, 0)); 
        PutLabel(FTRP(newPtr), Pack(csize-asize, 0));
        ENSURES(GetPrevAlloc(NextBlkp(newPtr)) == 0);
        InsertBlock(newPtr, GetSize(HDRP(newPtr)));
    }
    else{
        PutLabel(HDRP(bp), Pack(csize, 1));
        PutLabel(FTRP(bp), Pack(csize, 1)); /* Overwitten later */
        SetNextHDR(bp);
    }
    
}
/*
 *  Malloc Implementation
 *  ---------------------
 *  The following functions deal with the user-facing
 *  malloc implementation.
 */

/*
 * Initialize: return -1 on error, 0 on success.
 */
int mm_init(void) {
    
    size_t structSize = (MAXBINNUM + 1) * WSIZE;
    heap_listp = (char *)mem_sbrk(4 * WSIZE + structSize);
    dbg_printf("mm_init\n");
    
    /* Unsuccessful initialization */
    if(heap_listp == (char *)(-1)){
        return -1;
    }
    
    /* Alignment padding */
    Put(heap_listp, 0);                      
    /* Prologue header, including the structure size */
    Put(heap_listp + (1 * WSIZE), Pack(DSIZE + structSize, 1)); 
    /* Prologue footer, including the structure size */
    Put(heap_listp + (2 * WSIZE + structSize),
        Pack(DSIZE + structSize, 1));
    
    /* Epilogue header, the one previous to it is allocated */
    /* Itself is also allocated */
    Put(heap_listp + (3 * WSIZE) + structSize, Pack(0, 0x3));
    
    /* Init all the pointers(offset) of structure to NULL */
    memset(heap_listp + (3 * WSIZE), 0, structSize);
    Root = heap_listp + 3 * WSIZE; /* Entrance of the structure */
    
    /* heap_listp is always at the beginning of prologue */
    heap_listp += 2 * WSIZE;
    
    return 0;
}

/*
 * malloc: same behavior as lib malloc
 */
void *malloc (size_t size) {
    checkheap(1);  /* Let's make sure the heap is ok! */
    
    size_t asize;  /* Adjusted size */
    size_t extendsize; 
    char *bp;
    
    if(size == 0){
        return NULL;
    }
    
    /* Adjust the size to asize based on 8-bytes alignment */
    if(size <= DSIZE + WSIZE){
        asize = 2 * DSIZE;
    }
    else{
        asize = DSIZE * ((size+WSIZE+(DSIZE-1))/DSIZE);
    }
    
    dbg_printf("malloc %zu, asize = %zu\n", size, asize);
    
    bp = FindFit(asize);
    if(bp != NULL){
        DeleteBlock(bp);
        Place(bp, asize);
        return bp;
    }
    
    /* We cannot find a block in list or BST */
    extendsize = Max(asize, CHUNKSIZE);
    if((bp = extend_heap(extendsize/WSIZE)) == NULL){
        return NULL;
    }
    else{
        Place(bp, asize);
    }
    return bp;
}

/*
 * free: same behavior as lib free
 */
void free(void *bp){
    
    void *newPtr;
    size_t size;
    
    /* free a NULL pointer */ 
    if(bp == NULL) return;
    
    size = GetSize(HDRP(bp));
    dbg_printf("free block size = %zu\n", size);
    dbg_printf("free address = 0x%lx\n", (unsigned long)bp);
    PutLabel(HDRP(bp), Pack(size, 0));
    PutLabel(FTRP(bp), Pack(size, 0));
    ResetNextHDR(bp);   /* Set the header of next block */
    
    newPtr = coalesce(bp);
    InsertBlock(newPtr, GetSize(HDRP(newPtr)));
}


/*
 * realloc: same behavior as lib realloc
 */
void *realloc(void *oldptr, size_t size)
{
    
    size_t oldsize;
    void *newptr;

    /* If size == 0 then this is just free, and we return NULL. */
    if(size == 0) {
	free(oldptr);
	return NULL;
    }

    /* If oldptr is NULL, then this is just malloc. */
    if(oldptr == NULL) {
	return malloc(size);
    }

    newptr = malloc(size);

    /* If realloc() fails the original block is left untouched  */
    if(newptr == NULL) {
	return NULL;
    }
    
    /* Copy the old data */
    oldsize = GetSize(HDRP(oldptr));
    if(size < oldsize) oldsize = size;
    memcpy(newptr, oldptr, oldsize);
    
    /* Free the old block */
    free(oldptr);
    
    return newptr;
}


/*
 * calloc: same behavior as lib calloc
 */
void *calloc (size_t nmemb, size_t size){
    
    size_t bytes = nmemb * size;
    void *newptr;

    newptr = malloc(bytes);
    memset(newptr, 0, bytes);

    return newptr;
}



/*
 * --------------------------------
 *  Check Functions start from here
 *  -------------------------------
 */



/* Return whether the pointer is in the heap */
int in_heap(void* p) {
    return p <= mem_heap_hi() && p >= mem_heap_lo();
}

/* Heap-checking helper function */
int IsAligned(void *bp){
    if((long)(bp) % DSIZE == 0) return 1;
    return 0;
}

/* Check every single block in heap */
void checkBlock(void *bp){
    
    REQUIRES(GetSize(HDRP(bp)) != 0);
    
    /* Address alignment */
    ENSURES(IsAligned(bp));
    
    /* Size alignment */
    ENSURES(GetSize(HDRP(bp)) % 8 == 0);
    
    /* Free block's footer and header consistency */
    if(!GetAlloc(bp)){
        ENSURES(GetSize(HDRP(bp)) == GetSize(FTRP(bp)));
    }
    
    /* Block header's next-alloc bit's consistency */
    ENSURES(GetAlloc(NextBlkp(bp)) == GetNextAlloc(bp));
    
    /* Size minimum */
    ENSURES(GetSize(HDRP(bp)) >= 2 * DSIZE);
    
    /* Pointer consistency */
    /* Only check when prev or next is freed */
    if(!GetPrevAlloc(bp)){
        ENSURES(NextBlkp(PrevBlkp(bp)) == bp);
    }
    if(!GetAlloc(bp)){
        ENSURES(PrevBlkp(NextBlkp(bp)) == bp);
    }
    
    /* Check coalescing */
    if(!GetAlloc(bp)){
        /* No two consecutive freed blocks */
        ENSURES(GetAlloc(NextBlkp(bp)));
    }
}

/* Check the segregated list data structure */
/* Return the num of free blocks in this list */
int checkList(size_t binNum){
    
    dbg_printf("Checking segregated list No. %zu\n", binNum);
    
    void *BinAdd = GetBinAdd(binNum);
    void *bp = IntToPtr(Get(BinAdd));
    size_t blockSize;
    int count = 0;
    
    /* Get block size in this bin */
    if(bp != NULL){
        blockSize = GetSize(HDRP(bp));
    }
    
    for(; bp != NULL; bp = NextFreed(bp)){
        
        /* Size consistency */
        ENSURES(GetSize(HDRP(bp)) == blockSize);
        
        /* Check for in heap */
        ENSURES(in_heap(bp));
        
        /* Counter */
        count++;
        
        /* Pointer consistency */
        if(PrevFreed(bp) != NULL){
            ENSURES(NextFreed(PrevFreed(bp)) == bp);
        }
        if(NextFreed(bp) != NULL){
            ENSURES(PrevFreed(NextFreed(bp)) == bp);
        }
    }
    
    return count;
}


/* Helper function that checks the BST structure recursively */
int checkTreeRecur(void *bp){
    
    void *head = bp;
    /* Used to count num in segregated list following this tree node*/
    int count = 0;
    
    if(head == NULL) return 0;
    
    else{
        
        /* Check for in_heap */
        ENSURES(in_heap(bp));
        
        /* check doubly linked list during counting */
        for(; bp != NULL; bp = NextFreed(bp)){
            if(PrevFreed(bp) != NULL && Get(LabelPtr(bp)) == SEGNODE){
                ENSURES(NextFreed(PrevFreed(bp)) == bp);
            }
            if(NextFreed(bp) != NULL){
                ENSURES(PrevFreed(NextFreed(bp)) == bp);
            }
            count++;
        }
        
        /* Check for tree structure */
        if(RightFreed(head) != NULL){
            ENSURES(PrevFreed(RightFreed(head)) == head);
            /* Check for size consistency */
            ENSURES(GetSize(HDRP(head)) < GetSize(HDRP(RightFreed(head))));
        }
        if(LeftFreed(head) != NULL){
            ENSURES(PrevFreed(LeftFreed(head)) == head);
            /* Check for size consistency */
            ENSURES(GetSize(HDRP(head)) > GetSize(HDRP(LeftFreed(head))));
        }
        if(PrevFreed(head) != NULL){
            if(Get(LabelPtr(head)) == LEFT){
                ENSURES(LeftFreed(PrevFreed(head)) == head);
            }
            if(Get(LabelPtr(head)) == RIGHT){
                ENSURES(RightFreed(PrevFreed(head)) == head);
            }
        }
        
        /* Counting of tree nodes */
        return (checkTreeRecur(RightFreed(head))
                + checkTreeRecur(LeftFreed(head)) + count);
    }
}



/* Check the binary search tree data structure */
/* Return the num of free blocks in this tree */
int checkTree(size_t binNum){
    
    dbg_printf("Checking BST No. %zu\n", binNum-SEGNUM-1);
    
    void *BinAdd = GetBinAdd(binNum);
    void *bp = IntToPtr(Get(BinAdd));
    
    return checkTreeRecur(bp);
    
}

/* Returns 0 if no errors were found, otherwise returns the error */
int mm_checkheap(int verbose) {
    
    void *bp;
    size_t i;
    size_t totalFreeNum = 0;
    size_t listFreeNum = 0;
    size_t treeFreeNum = 0;
    size_t structSize = (MAXBINNUM + 1) * WSIZE; 
    
    /* Step 1: Check the heap */
    dbg_printf("Step 1: Checking the heap...\n");
    /* 1.1 Check prologue block */
    dbg_printf("Checking prologue block...\n");
    ENSURES(GetSize(HDRP(heap_listp)) == DSIZE + structSize);
    ENSURES(GetAlloc(heap_listp));
    
    /* 1.2 Check each middle block */
    dbg_printf("Checking each middle block...\n");
    for(bp = NextBlkp(heap_listp); GetSize(HDRP(bp)) != 0;
        bp = NextBlkp(bp)){
        checkBlock(bp);
        if(!GetAlloc(bp)){
            totalFreeNum++;
        }
    }
    
    /* 1.3 Check epilogue block */
    dbg_printf("Checking epilogue block...\n");
    ENSURES(GetSize(HDRP(bp)) == 0);
    ENSURES(GetAlloc(bp));
    
    
    /* Step 2: Check the segregated free list */
    dbg_printf("Step 2: Checking segregated free list...\n");
    
    /* 2.1 Check segregated list */
    dbg_printf("Checking segregated list...\n");
    for(i = 0; i <= SEGNUM; i++){
        listFreeNum += checkList(i);
    }
    
    /* Step 3: Check the binary search tree */
    dbg_printf("Step 3: Checking binary search tree...\n");
    for(i = SEGNUM + 1; i <= MAXBINNUM; i++){
        treeFreeNum += checkTree(i);
    }
    
    /* Step 4: Check total free number consistency */
    dbg_printf("Step 4: Checking total free number...\n");
    ENSURES(totalFreeNum == treeFreeNum + listFreeNum);
    
    
    structSize = structSize;
    verbose = verbose;
    return 0;
}
