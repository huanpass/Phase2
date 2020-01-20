#include "param.h"
#include "types.h"
#include "defs.h"
#include "x86.h"
#include "memlayout.h"
#include "mmu.h"
#include "proc.h"
#include "elf.h"
#include "spinlock.h" // mutual exclusion spinlock, added for cow

extern char data[];  // defined by kernel.ld
pde_t *kpgdir;  // for use in scheduler()
// struct spinlock slock; // acquire mutual exclusion spinlock each time updating ref count array so other processes
                      // aren't trying to change it at the same time; don't want race condition
// uchar sharpgrefcount[PHYSTOP/PGSIZE]; // create an array to store the number of times each phys page of mem is being shared

// Set up CPU's kernel segment descriptors.
// Run once on entry on each CPU.
void
seginit(void)
{
  struct cpu *c;

  // Map "logical" addresses to virtual addresses using identity map.
  // Cannot share a CODE descriptor for both kernel and user
  // because it would have to have DPL_USR, but the CPU forbids
  // an interrupt from CPL=0 to DPL=3.
  c = &cpus[cpuid()];
  c->gdt[SEG_KCODE] = SEG(STA_X|STA_R, 0, 0xffffffff, 0);
  c->gdt[SEG_KDATA] = SEG(STA_W, 0, 0xffffffff, 0);
  c->gdt[SEG_UCODE] = SEG(STA_X|STA_R, 0, 0xffffffff, DPL_USER);
  c->gdt[SEG_UDATA] = SEG(STA_W, 0, 0xffffffff, DPL_USER);
  lgdt(c->gdt, sizeof(c->gdt));
}

// Return the address of the PTE in page table pgdir
// that corresponds to virtual address va.  If alloc!=0,
// create any required page table pages.
static pte_t *
walkpgdir(pde_t *pgdir, const void *va, int alloc)
{
  pde_t *pde;
  pte_t *pgtab;

  pde = &pgdir[PDX(va)];
  if(*pde & PTE_P){
    pgtab = (pte_t*)P2V(PTE_ADDR(*pde));
  } else {
    if(!alloc || (pgtab = (pte_t*)kalloc()) == 0)
      return 0;
    // Make sure all those PTE_P bits are zero.
    memset(pgtab, 0, PGSIZE);
    // The permissions here are overly generous, but they can
    // be further restricted by the permissions in the page table
    // entries, if necessary.
    *pde = V2P(pgtab) | PTE_P | PTE_W | PTE_U;
  }
  return &pgtab[PTX(va)];
}

// Create PTEs for virtual addresses starting at va that refer to
// physical addresses starting at pa. va and size might not
// be page-aligned.
static int
mappages(pde_t *pgdir, void *va, uint size, uint pa, int perm)
{
  char *a, *last;
  pte_t *pte;

  a = (char*)PGROUNDDOWN((uint)va);
  last = (char*)PGROUNDDOWN(((uint)va) + size - 1);
  for(;;){
    if((pte = walkpgdir(pgdir, a, 1)) == 0)
      return -1;
    if(*pte & PTE_P)
      panic("remap");
    *pte = pa | perm | PTE_P;
    if(a == last)
      break;
    a += PGSIZE;
    pa += PGSIZE;
  }
  return 0;
}

// There is one page table per process, plus one that's used when
// a CPU is not running any process (kpgdir). The kernel uses the
// current process's page table during system calls and interrupts;
// page protection bits prevent user code from using the kernel's
// mappings.
//
// setupkvm() and exec() set up every page table like this:
//
//   0..KERNBASE: user memory (text+data+stack+heap), mapped to
//                phys memory allocated by the kernel
//   KERNBASE..KERNBASE+EXTMEM: mapped to 0..EXTMEM (for I/O space)
//   KERNBASE+EXTMEM..data: mapped to EXTMEM..V2P(data)
//                for the kernel's instructions and r/o data
//   data..KERNBASE+PHYSTOP: mapped to V2P(data)..PHYSTOP,
//                                  rw data + free physical memory
//   0xfe000000..0: mapped direct (devices such as ioapic)
//
// The kernel allocates physical memory for its heap and for user memory
// between V2P(end) and the end of physical memory (PHYSTOP)
// (directly addressable from end..P2V(PHYSTOP)).

// This table defines the kernel's mappings, which are present in
// every process's page table.
static struct kmap {
  void *virt;
  uint phys_start;
  uint phys_end;
  int perm;
} kmap[] = {
 { (void*)KERNBASE, 0,             EXTMEM,    PTE_W}, // I/O space
 { (void*)KERNLINK, V2P(KERNLINK), V2P(data), 0},     // kern text+rodata
 { (void*)data,     V2P(data),     PHYSTOP,   PTE_W}, // kern data+memory
 { (void*)DEVSPACE, DEVSPACE,      0,         PTE_W}, // more devices
};

// Set up kernel part of a page table.
pde_t*
setupkvm(void)
{
  pde_t *pgdir;
  struct kmap *k;

  if((pgdir = (pde_t*)kalloc()) == 0)
    return 0;
  memset(pgdir, 0, PGSIZE);
  if (P2V(PHYSTOP) > (void*)DEVSPACE)
    panic("PHYSTOP too high");
  for(k = kmap; k < &kmap[NELEM(kmap)]; k++)
    if(mappages(pgdir, k->virt, k->phys_end - k->phys_start,
                (uint)k->phys_start, k->perm) < 0) {
      freevm(pgdir);
      return 0;
    }
  return pgdir;
}

// Allocate one page table for the machine for the kernel address
// space for scheduler processes.
void
kvmalloc(void)
{
  kpgdir = setupkvm();
  switchkvm();
}

// Switch h/w page table register to the kernel-only page table,
// for when no process is running.
void
switchkvm(void)
{
  lcr3(V2P(kpgdir));   // switch to the kernel page table
}

// Switch TSS and h/w page table to correspond to process p.
void
switchuvm(struct proc *p)
{
  if(p == 0)
    panic("switchuvm: no process");
  if(p->kstack == 0)
    panic("switchuvm: no kstack");
  if(p->pgdir == 0)
    panic("switchuvm: no pgdir");

  pushcli();
  mycpu()->gdt[SEG_TSS] = SEG16(STS_T32A, &mycpu()->ts,
                                sizeof(mycpu()->ts)-1, 0);
  mycpu()->gdt[SEG_TSS].s = 0;
  mycpu()->ts.ss0 = SEG_KDATA << 3;
  mycpu()->ts.esp0 = (uint)p->kstack + KSTACKSIZE;
  // setting IOPL=0 in eflags *and* iomb beyond the tss segment limit
  // forbids I/O instructions (e.g., inb and outb) from user space
  mycpu()->ts.iomb = (ushort) 0xFFFF;
  ltr(SEG_TSS << 3);
  lcr3(V2P(p->pgdir));  // switch to process's address space
  popcli();
}

// Load the initcode into address 0 of pgdir.
// sz must be less than a page.
void
inituvm(pde_t *pgdir, char *init, uint sz)
{
  char *mem;

  if(sz >= PGSIZE)
    panic("inituvm: more than a page");
  mem = kalloc();
  memset(mem, 0, PGSIZE);
  mappages(pgdir, 0, PGSIZE, V2P(mem), PTE_W|PTE_U);

  ///// added for cow
  // acquire(&slock);
  // // incr ref count for this initial page
  // sharpgrefcount[V2P(mem) >> 12] =  sharpgrefcount[V2P(mem) >> 12] + 1; // log2(pgsize) = 12 // faster than division
  // release(&slock);
  /////
  
  memmove(mem, init, sz);
}

// Load a program segment into pgdir.  addr must be page-aligned
// and the pages from addr to addr+sz must already be mapped.
int
loaduvm(pde_t *pgdir, char *addr, struct inode *ip, uint offset, uint sz)
{
  uint i, pa, n;
  pte_t *pte;

  if((uint) addr % PGSIZE != 0)
    panic("loaduvm: addr must be page aligned");
  for(i = 0; i < sz; i += PGSIZE){
    if((pte = walkpgdir(pgdir, addr+i, 0)) == 0)
      panic("loaduvm: address should exist");
    pa = PTE_ADDR(*pte);
    if(sz - i < PGSIZE)
      n = sz - i;
    else
      n = PGSIZE;
    if(readi(ip, P2V(pa), offset+i, n) != n)
      return -1;
  }
  return 0;
}

// Allocate page tables and physical memory to grow process from oldsz to
// newsz, which need not be page aligned.  Returns new size or 0 on error.
int
allocuvm(pde_t *pgdir, uint oldsz, uint newsz)
{
  char *mem;
  uint a;

  if(newsz >= KERNBASE)
    return 0;
  if(newsz < oldsz)
    return oldsz;

  a = PGROUNDUP(oldsz);
  if (!a) {
    a = PGSIZE;
    newsz += PGSIZE;
  }
  for(; a < newsz; a += PGSIZE){
    mem = kalloc();
    if(mem == 0){
      cprintf("allocuvm out of memory\n");
      deallocuvm(pgdir, newsz, oldsz);
      return 0;
    }
    memset(mem, 0, PGSIZE);
    if(mappages(pgdir, (char*)a, PGSIZE, V2P(mem), PTE_W|PTE_U) < 0){
      cprintf("allocuvm out of memory (2)\n");
      deallocuvm(pgdir, newsz, oldsz);
      kfree(mem);
      return 0;
    }

    ///// added for cow
    // acquire(&slock);
    // sharpgrefcount[V2P(mem) >> 12] = sharpgrefcount[V2P(mem) >> 12] + 1; // increment shared page ref count at this mem addr
    // release(&slock);
    /////

  }
  return newsz;
}

// Deallocate user pages to bring the process size from oldsz to
// newsz.  oldsz and newsz need not be page-aligned, nor does newsz
// need to be less than oldsz.  oldsz can be larger than the actual
// process size.  Returns the new process size.
int
deallocuvm(pde_t *pgdir, uint oldsz, uint newsz)
{
  pte_t *pte;
  uint a, pa;

  if(newsz >= oldsz)
    return oldsz;

  a = PGROUNDUP(newsz);
  for(; a  < oldsz; a += PGSIZE){
    pte = walkpgdir(pgdir, (char*)a, 0);
    if(!pte)
      a = PGADDR(PDX(a) + 1, 0, 0) - PGSIZE;
    else if((*pte & PTE_P) != 0){
      pa = PTE_ADDR(*pte);
      if(pa == 0)
        panic("kfree");
      
      ///// added for cow <--- now this is all taken care of in kalloc instead
      // acquire(&slock);
      // if ((sharpgrefcount[pa >> 12] - 1) == 0 || sharpgrefcount[pa >> 12] == 0) { // only remove pg if no other pg table pting to it
      char *v = P2V(pa);
      kfree(v);
      // }
      // release(&slock);
      /////

      *pte = 0;
    }
  }
  return newsz;
}

// Free a page table and all the physical memory pages
// in the user part.
void
freevm(pde_t *pgdir)
{
  uint i;

  if(pgdir == 0)
    panic("freevm: no pgdir");
  deallocuvm(pgdir, KERNBASE, 0);
  for(i = 0; i < NPDENTRIES; i++){
    if(pgdir[i] & PTE_P){
      char * v = P2V(PTE_ADDR(pgdir[i]));
      kfree(v);
    }
  }
  kfree((char*)pgdir);
}

// Clear PTE_U on a page. Used to create an inaccessible
// page beneath the user stack.
void
clearpteu(pde_t *pgdir, char *uva)
{
  pte_t *pte;

  pte = walkpgdir(pgdir, uva, 0);
  if(pte == 0)
    panic("clearpteu");
  *pte &= ~PTE_U;
}

// Given a parent process's page table, create a copy
// of it for a child.
pde_t*
copyuvm(pde_t *pgdir, uint sz)
{
  pde_t *d;
  pte_t *pte;
  uint pa, i, flags;
  // char *mem; // no need to alloc new memory since doing both parent and child will point to same addr in mem

  if((d = setupkvm()) == 0)
    return 0;
  for(i = PGSIZE; i < sz; i += PGSIZE){ // changed to i = PGSIZE
    if((pte = walkpgdir(pgdir, (void *) i, 0)) == 0)
      panic("copyuvm: pte should exist");
    if(!(*pte & PTE_P))
      panic("copyuvm: page not present");
    /////
    *pte &= ~PTE_W; // make permission for the parent page read-only
    /////
    pa = PTE_ADDR(*pte);
    flags = PTE_FLAGS(*pte);
    // don't need to alloc new page, commented out
    // if((mem = kalloc()) == 0)
    //   goto bad;
    // memmove(mem, (char*)P2V(pa), PGSIZE);
    // if(mappages(d, (void*)i, PGSIZE, V2P(mem), flags) < 0) {
    //   kfree(mem);
    //   goto bad;
    // }
    ///// added for cow
    // mapepages = Create PTEs for virtual addresses starting at va that refer to physical addresses starting at pa
    // if mappages unsuccessful, go to bad
    if (mappages(d, (void*)i, PGSIZE, pa, flags) < 0) { // map childs pgtable to same perm addr
      goto bad;
    }

    incrrefcount(pa); // increment ref count
    /////
  }
  ///// added for cow
  lcr3(V2P(pgdir)); // flush TLB
  /////
  return d;

bad:
  freevm(d);
  ///// added for cow
  lcr3(V2P(pgdir)); // failed to copy, but flush TLB bc entries in original proc pgttable changed
  /////
  return 0;
}

//PAGEBREAK!
// Map user virtual address to kernel address.
char*
uva2ka(pde_t *pgdir, char *uva)
{
  pte_t *pte;

  pte = walkpgdir(pgdir, uva, 0);
  if((*pte & PTE_P) == 0)
    return 0;
  if((*pte & PTE_U) == 0)
    return 0;
  return (char*)P2V(PTE_ADDR(*pte));
}

// Copy len bytes from p to user address va in page table pgdir.
// Most useful when pgdir is not the current page table.
// uva2ka ensures this only works for PTE_U pages.
int
copyout(pde_t *pgdir, uint va, void *p, uint len)
{
  char *buf, *pa0;
  uint n, va0;

  buf = (char*)p;
  while(len > 0){
    va0 = (uint)PGROUNDDOWN(va);
    pa0 = uva2ka(pgdir, (char*)va0);
    if(pa0 == 0)
      return -1;
    n = PGSIZE - (va - va0);
    if(n > len)
      n = len;
    memmove(pa0 + (va - va0), buf, n);
    len -= n;
    buf += n;
    va = va0 + PGSIZE;
  }
  return 0;
}

// pagefault fxn for cow
void
pagefault(uint err_code) {
  // cprintf("page fault\n";)
  uint va = rcr2(); // get faulting va from cr2 reg
  struct proc *proc = myproc(); // get the current proc

  // if va mapped to kernel code
  if (va >= KERNBASE) {
    // print err msg, kill proc, and return
    cprintf("illegal mem access on cpu bc va is mapped to kernel code: killing proc \n");
    proc->killed = 1;
    return;
  }

  pte_t *pte; // ptr to page table entry
  char *mem; // var to store mem addr

  // if va mapped to null pte
  // walkpgdir = Return the address of the PTE in page table pgdir that corresponds to virtual address va.
  if ((pte = walkpgdir(proc->pgdir, (void*)va, 0)) == 0) {
    // print err msg, kill proc, and return
    cprintf("illegal mem access bc va is mapped to null pte: killing proc \n");
    proc->killed = 1;
    return;
  }

  // if pte not present
  if (!(*pte & PTE_P)) {
    // print err msg, kill proc, and return
    cprintf("illegal mem access bc va mapped to pte which isn't present: killing proc \n");
    proc->killed = 1;
    return;
  }

  // if pte not user accessible
  if (!(*pte & PTE_U)) {
    // print err msg, kill proc, and return
    cprintf("illegal mem access bc va mapped to pte not user accessible: killing proc \n");
    proc->killed = 1;
    return;
  }

  // if curr page has write permissions enabled
  if (*pte & PTE_W) {
    panic("page fault already writeable \n");
  }

  // else if page not have write permission
  else {

    // get address in page table entry
    uint pa = PTE_ADDR(*pte);
    // get ref count of page
    uchar refcount = getrefcount(pa);

    // acquire(&slock);
    // if this the last proc that maps to this page, remove read-only restriction
    if (refcount == 1) {
      // release(&slock);
      *pte |= PTE_W;
    }

    // else check if >1 proc shares this page
    else {

      // if this proc the 1st one that tries to write to the page
      if (refcount > 1) {
        // release(&slock);

        // alloc a new mem page for this process
        mem = kalloc();
        // if mem cannot be allocated, kalloc() returns 0
        if (mem == 0) {
          // print err msg, kill proc, and return
          cprintf("mem cannot be alloc: killing proc \n");
          proc->killed = 1;
          return;
        }

        // copy contents from original mem page ptd to by va
        // from old copyuvm
        memmove(mem, (char*)P2V(pa), PGSIZE);
        decrrefcount(pa); // decr ref count

        // update shared page ref count of new and old page
        // acquire(&slock);
        // sharpgrefcount[pa >> 12] = sharpgrefcount[pa >> 12] - 1; // decr the ref count for old page
        // sharpgrefcount[V2P(mem) >> 12] = sharpgrefcount[V2P(mem) >> 12] + 1; // incr the ref count for new page
        // release(&slock);

        // similar syntax in walkpgdir but with pde
        *pte = V2P(mem) | PTE_P | PTE_W | PTE_U; // point pte to the new page

      // else shared page ref count < 1, which shouldn't happen, so panic
      } else {

        // release(&slock);
        panic("page fault bc ref count wrong \n");

      }
    }

    lcr3(V2P(proc->pgdir)); // flush TLB

  }
}

//PAGEBREAK!
// Blank page.
//PAGEBREAK!
// Blank page.
//PAGEBREAK!
// Blank page.

