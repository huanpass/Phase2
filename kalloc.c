// Physical memory allocator, intended to allocate
// memory for user processes, kernel stacks, page table pages,
// and pipe buffers. Allocates 4096-byte pages.

#include "types.h"
#include "defs.h"
#include "param.h"
#include "memlayout.h"
#include "mmu.h"
#include "spinlock.h"

void freerange(void *vstart, void *vend);
extern char end[]; // first address after kernel loaded from ELF file
                   // defined by the kernel linker script in kernel.ld

struct run {
  struct run *next;
};

struct {
  struct spinlock lock;
  int use_lock;
  struct run *freelist;
  uint freepgs; // number of free pages, for cow testing
  uchar sharpgrefcount[PHYSTOP/PGSIZE]; // shared pg ref count
  // NOTE: accessed using sharpgrefcount[pa >> 12] bc log2(PGSIZE) = 12; shift faster than division
} kmem;

// Initialization happens in two phases.
// 1. main() calls kinit1() while still using entrypgdir to place just
// the pages mapped by entrypgdir on free list.
// 2. main() calls kinit2() with the rest of the physical pages
// after installing a full page table that maps them on all cores.
void
kinit1(void *vstart, void *vend)
{
  initlock(&kmem.lock, "kmem");
  kmem.use_lock = 0;
  kmem.freepgs = 0; // init num of free pgs to 0 
  freerange(vstart, vend);
}

void
kinit2(void *vstart, void *vend)
{
  freerange(vstart, vend);
  kmem.use_lock = 1;
}

void
freerange(void *vstart, void *vend)
{
  char *p;
  p = (char*)PGROUNDUP((uint)vstart);
  for(; p + PGSIZE <= (char*)vend; p += PGSIZE) {
    kmem.sharpgrefcount[V2P(p) >> 12] = 0; // initi ref count of each pg to 0
    kfree(p);
  }
}
//PAGEBREAK: 21
// Free the page of physical memory pointed at by v,
// which normally should have been returned by a
// call to kalloc().  (The exception is when
// initializing the allocator; see kinit above.)
void
kfree(char *v)
{
  struct run *r;

  if((uint)v % PGSIZE || v < end || V2P(v) >= PHYSTOP)
    panic("kfree");

  // Fill with junk to catch dangling refs.
  // memset(v, 1, PGSIZE);

  if(kmem.use_lock)
    acquire(&kmem.lock);
  r = (struct run*)v;

  // if page free but still referenced by another page, just decr the ref count
  if (kmem.sharpgrefcount[V2P(v) >> 12] > 0) {
    kmem.sharpgrefcount[V2P(v) >> 12] = kmem.sharpgrefcount[V2P(v) >> 12] - 1;
  }

  // if page no longer referenced by any pages, then we can return it to the free list
  if (kmem.sharpgrefcount[V2P(v) >> 12] == 0) {
    // Fill with junk to catch dangling refs.
    memset(v, 1, PGSIZE);
    kmem.freepgs = kmem.freepgs + 1; // increment number of free pages bc new node added to free list
    r->next = kmem.freelist;
    kmem.freelist = r;
  }

  if(kmem.use_lock)
    release(&kmem.lock);
}

// Allocate one 4096-byte page of physical memory.
// Returns a pointer that the kernel can use.
// Returns 0 if the memory cannot be allocated.
char*
kalloc(void)
{
  struct run *r;

  if(kmem.use_lock)
    acquire(&kmem.lock);
  r = kmem.freelist;
  if(r) {
    kmem.freelist = r->next;
    kmem.freepgs = kmem.freepgs - 1; // decrement number of free pages bc node removed from free list
    kmem.sharpgrefcount[V2P((char*)r) >> 12] = 1; // set ref count of pg to 1 when its alloc
  }
  if(kmem.use_lock)
    release(&kmem.lock);
  return (char*)r;
}

// get the number of free pages
int
numfreepgs(void) {
  // acquire lock for kmem if uses lock
  if (kmem.use_lock) {
    acquire(&kmem.lock);
  }

  // get num of free pgs from struct variable we added
  int numfp = kmem.freepgs;
  
  // if uses lock, release the lock again
  if (kmem.use_lock) {
    release(&kmem.lock);
  }

  // return the number of free pgs
  return numfp;
}

// incr the ref count of the page
void 
incrrefcount(uint pa) {

  // if phys addr out of range, panic
  // end = first address after kernel loaded from ELF file
  if (pa < (uint)V2P(end) || pa >= PHYSTOP) {
    panic("can't incr ref count");
  }

  // else, incr the ref count of the page
  acquire(&kmem.lock);
  kmem.sharpgrefcount[pa >> 12] = kmem.sharpgrefcount[pa >> 12] + 1;
  release(&kmem.lock);
}

// decr the ref count of the page
void 
decrrefcount(uint pa) {

  // if phys addr out of range, panic
  if (pa < (uint)V2P(end) || pa >= PHYSTOP) {
    panic("can't decr ref count");
  }

  // else, decr the ref count of the page
  acquire(&kmem.lock);
  kmem.sharpgrefcount[pa >> 12] = kmem.sharpgrefcount[pa >> 12] -1;
  release(&kmem.lock);
}

// get the ref count of the page -- used in page fault code
uchar
getrefcount(uint pa) {

  // if phys addr out of range, panic
  if (pa < (uint)V2P(end) || pa >= PHYSTOP) {
    panic("can't get ref count");
  }

  // get ref count of page at phys addr
  acquire(&kmem.lock);
  uchar count = kmem.sharpgrefcount[pa >> 12];
  release(&kmem.lock);

  return count;
}

