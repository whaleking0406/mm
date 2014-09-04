File description:

Author: Jingyu Wang
Date: 4/18/2014


1. Overview:

This mm.c file is the major and fundamental part of a course project: Carnegie Mellon University course "Intro. to Computer System" (15213)/MallocLab. In this project, we are required to implement the Dynamic Memory Allocator in C, i.e. the 'malloc' package, including functions like 'malloc', 'calloc', 'free' as well as 'realloc'.

As specified in handout, We are free to use any data structure and algorithm to finish this task. Besides, we have to keep the 'balance' of this implemented package, in the sense that, we need to take into consideration of both 'utilization' and 'speed'. These are the two key factors characterizing the performance of this project.

The word utilization here means how well we can take advantages of a given free block, and how to deal with it after it is freed or reallocated. For example, we can do a coalescing to merge two small adjacent block into a larger one. For the speed, it refers to the time (in Kops/sec) that we can find a target free block based on the requirement. For the detailed definition and measurement, please check it in CASPP wesite: http://csapp.cs.cmu.edu/public/malloclab.pdf or textbook.






2. Data Structure and Algorithm:

When a demand of a chunk of memory comes in, this implementation will first check in the free block pool to find a block of proper size (also need to consider alignment), and return the head address. If this kind of block does not exist, it will extend the heap by calling mem_sbrk to ask for a chunk of additional fixed memory.

There are many ways to deal with the storage and look-up of free blocks. Here I used segregated list and BST(binary search tree) to finish this task. For a block less than a specific size, I used doubly linked list to store those blocks, and for larger ones, I stored their addresses in a BST. 

For each segregated list, every list keeps a fixed size free block, and the entrances are places at the beginning of the heap, i.e, inside the prologue block. The list are doubly linked, and ranges from [16-40] bytes. For each binary search tree, every tree node is different in size. If we insert a block with same size, we doubly linked it to the tree node, and then it can be regarded as a segregated free list with identical size. Besides, additional information such as pointers, allocated bit, size info are needed and recorded inside a free block. Those are illustrated as following:


For list node:

[Header][Next ptr][Prev ptr][Footer]

For BST nodt:

[Header][Next ptr][Prev ptr][Left ptr][Right ptr][Label][XXX][Footer]

Each [] means a 4-bytes space.


