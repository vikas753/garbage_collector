
#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>
#include <assert.h>
#include <string.h>

#include "gc.h"

#define CHUNK_SIZE (1024 * 1024)
#define ALLOC_UNIT 16
#define CELL_COUNT (CHUNK_SIZE / ALLOC_UNIT)

#define peq(aa, bb) (((intptr_t)aa) == ((intptr_t)bb))

// Max offset of a cell that can be possibly be on hold . 
#define MAX_INDEX ((1 << 16) - 1)

typedef uint16_t u16;
typedef uint8_t u8;

typedef struct cell {
    u16 size; // Size is in multiples of ALLOC_UNIT
    u16 next;
    u16 conf; // Serves as a confirmation that some location in
              // memory really is a cell. Stores (size * 7) % (2^16)
    u8  used;
    u8  mark;
} cell;

// We track both a free list and a used list. The used list is nessiary for the
// sweep phase of mark and sweep.
//
// Both lists are built with the cell structure above. Since allocated memory is
// on a list, there's no distinction between a list cell and a header for
// allocated memory.
static u16 free_list = 0;
static u16 used_list = 0;

// the bottom of the 1MB garbage collected heap
static void* chunk_base = 0;

// our best guess at the top of the stack
static intptr_t stack_top = 0;

// Stats
static size_t bytes_allocated = 0;
static size_t bytes_freed = 0;
static size_t blocks_allocated = 0;
static size_t blocks_freed = 0;


// enums to mark a cell
#define GC_MARK    2
#define GC_NO_MARK 0

// enums to define the state of booleans
#define TRUE   1
#define FALSE  0

cell*
o2p(u16 off)
{
    if (off == 0) {
        return 0;
    }
    intptr_t addr = (intptr_t)chunk_base;
    addr += off * ALLOC_UNIT;
    return (cell*) addr;
}

u16
p2o(cell* ptr)
{
    if (ptr == 0) {
        return 0;
    }
    intptr_t addr0 = (intptr_t)chunk_base;
    intptr_t addr1 = (intptr_t)ptr;
    intptr_t units = (addr1 - addr0) / ALLOC_UNIT;
    return (u16) units;
}

void
print_cell(cell* cc)
{
    if (cc) {
        printf(
            "cell %p +%d {size: %d, next: %d, conf: %d, used: %d, mark: %d}\n",
            cc, p2o(cc), cc->size, cc->next, cc->conf, cc->used, cc->mark
        );
    }
    else {
        printf("null cell\n");
    }
}

void
gc_print_info(void* addr)
{
    cell* cc = ((cell*)addr) - 1;
    print_cell(cc);
}

static
int
list_length(u16 off)
{
    if (off == 0) {
        return 0;
    }

    cell* item = o2p(off);
    return 1 + list_length(item->next);
}

static
long
list_total(u16 off)
{
    if (off == 0) {
        return 0;
    }

    cell* item = o2p(off);
    long rest = list_total(item->next);
    return rest + ALLOC_UNIT*item->size;
}


void
gc_print_stats()
{
    printf("== gc stats ==\n");
    printf("bytes allocated: %ld\n", bytes_allocated);
    printf("bytes freed: %ld\n", bytes_freed);
    printf("blocks allocated: %ld\n", blocks_allocated);
    printf("blocks freed: %ld\n", blocks_freed);
    printf("used_list length: %d\n", list_length(used_list));
    printf("free_list length: %d\n", list_length(free_list));
    printf("used space: %ld\n", list_total(used_list));
    printf("free space: %ld\n", list_total(free_list));
}

u16
insert_free(u16 coff, cell* item)
{
    assert(item != 0);

    bytes_freed = bytes_freed + ALLOC_UNIT * item->size;
    blocks_freed = blocks_freed + 1;
    u16 i_coff = p2o(item);

    u16 p_coff = free_list; 
    for (u16 c_coff = free_list; (p_coff != 0);)
    {
      cell* c_cell = o2p(c_coff);	      
      cell* p_cell = o2p(p_coff);
      cell* i_cell = o2p(i_coff);

      // Insertion should happen at node , just before the offset match . 
      if(i_coff <= c_coff)
      {
	// Check if the to be inserted node is before head
	// then handle the case accordingly as below
	if(p_coff == c_coff)
	{
          // Check for coalescence with free list node
	  // else somehow make an insertion
	  if((i_coff + i_cell->size) == c_coff)
	  {
            i_cell->size = i_cell->size + c_cell->size;
            i_cell->next = c_cell->next;	    
	  }
          else
	  {
	    i_cell->next = c_coff;	  
	  }
          free_list = i_coff;  
	}
	else
	{
	  // Check for coalescence with previous as well as current node
	  if(((p_coff + p_cell->size) == i_coff) && ((coff + i_cell->size) == c_coff))
	  {
            p_cell->size = p_cell->size + i_cell->size + c_cell->size;
            p_cell->next = c_cell->next;	    
	  } // Check for coalescence with previous node only
          else if((p_coff + p_cell->size) == i_coff) 
	  {
	    p_cell->size = p_cell->size + i_cell->size;
            p_cell->next = c_coff;	       	  
	  } // Check for coalescence with next node 
          else if((i_coff + i_cell->size) == c_coff)
	  {
	    p_cell->next = i_coff;	  
	    i_cell->size = i_cell->size + c_cell->size;
            i_cell->next = c_cell->next;	       	  	  
	  } // In case of no coalescence chip the node in between . 
          else
	  {
	    p_cell->next = i_coff;
            i_cell->next = c_coff;	    
	  }	  
	}
	return 0;	
      }
      p_coff = c_coff;
      c_coff = c_cell->next;
    }
    return -1;
}

// Scan the used list, to see if the pointer found on stack
// as any match in used list cells . If so fill up the cell offset
// and return .
int
find_ptr_gc_used_list(intptr_t address , u16* cell_offset)
{
  u16* pptr = &used_list;  
  for (cell* cc = o2p(used_list); cc; pptr = &(cc->next), cc = o2p(*pptr))
  {
    intptr_t address_bot = (intptr_t)cc + sizeof(cell);
    intptr_t address_top = address_bot + ALLOC_UNIT*cc->size - sizeof(cell);    
    if((address >= address_bot) & (address < address_top))
    {
      *cell_offset = p2o(cc);
      return TRUE;      
    }	    
  }
  return FALSE;  
}

static
void
insert_used(cell* item)
{
    assert(item);
    u16 ioff = p2o(item);
    item->used = 1;
    item->next = used_list;
    used_list = ioff;
}

void
gc_init(void* main_frame)
{
    intptr_t addr = (intptr_t)main_frame;
    intptr_t pages = addr / 4096 + 1;
    stack_top = pages * 4096;

    chunk_base = aligned_alloc(CHUNK_SIZE, CHUNK_SIZE);
    assert(chunk_base != 0);
    memset(chunk_base, 0, CHUNK_SIZE);

    cell* base_cell = (cell*) o2p(1);
    base_cell->size = CELL_COUNT - 1;
    base_cell->next = 0;

    free_list = 1;
}

static
int
div_round_up(int num, int den)
{
    int quo = num / den;
    return (num % den == 0) ? quo : quo + 1;
}

static
void*
gc_malloc1(size_t bytes)
{

    u16 units = (u16)div_round_up(bytes + sizeof(cell), ALLOC_UNIT);

    bytes_allocated += units * ALLOC_UNIT;
    blocks_allocated += 1;

    u16* pptr = &free_list;
    for (cell* cc = o2p(free_list); cc; pptr = &(cc->next), cc = o2p(*pptr)) {
        if (units <= cc->size) {

            cell* dd = 0;
            dd = cc;

	    u16 old_size = dd->size;
	    dd->size = units;
            dd->conf = 7*dd->size;
	    u16 new_size = old_size - units;

	    // Split cells , if left units of allocation are not zero . 
	    // If previous cell is a head of free list , then update the
	    // free list head . Else split and create a new cell and update
	    // it's position in the list as below . 
	    if(new_size != 0)
            {
	      *pptr = *pptr + units;
	      cell* new_cell_created = o2p(*pptr);
              new_cell_created->size = new_size;
	      new_cell_created->next = cc->next;
            }
            else
	    {
              *pptr = cc->next;	    
	    }

	    // Check for any out of bounds increment of block
	    // if there is any , then we need not perform 
	    // an allocation and perform a garbage collection 
	    // to avoid incorrect allocation . 
	    if(*pptr >= MAX_INDEX)
	    {
	      return 0;	    
	    }

	    dd->mark = GC_NO_MARK;
            insert_used(dd);
          
            void* addr = (void*)(dd + 1);
            memset(addr, 0x7F, bytes);

            assert(dd->size == units);
            assert(dd->conf == 7*dd->size);

            return addr;
        }
    }
    return 0;
}

void*
gc_malloc(size_t bytes)
{
    void* addr;

    addr = gc_malloc1(bytes);
    if (addr) {
        return addr;
    }

    // First attempt failed. Run gc and try once more.
    gc_collect();

    addr = gc_malloc1(bytes);
    if (addr) {
        return addr;
    }

    gc_print_stats();
    fflush(stdout);

    fprintf(stderr, "oom @ malloc(%ld)\n", bytes);
    fflush(stderr);
    abort();
}

static
void
mark_range(intptr_t bot, intptr_t top)
{


  // Scan the memory region as below and see if the 
  // scanned space contains any pointer to stack . 
  // If so then mark it to be used and recursively
  // scan the memory region of that page . 

  for(intptr_t i=bot;i<top;i=i+sizeof(intptr_t))
  {
    intptr_t* stack_address = (intptr_t*)i;
    intptr_t stack_addr_val = *stack_address;
    u16 cell_offset = 0;
    if(find_ptr_gc_used_list(stack_addr_val,&cell_offset) == TRUE)
    {
      cell* gc_cell_ptr = o2p(cell_offset);
      gc_cell_ptr->mark = gc_cell_ptr->mark | GC_MARK;
      intptr_t gc_cell_bot = (intptr_t)gc_cell_ptr + sizeof(cell);
      intptr_t gc_cell_top = (intptr_t)gc_cell_bot + ALLOC_UNIT*gc_cell_ptr->size - sizeof(cell);
     // Since a hit was found in the used list , perform a Depth First Search assuming it to be root
     // through the memory region of root .
      mark_range(gc_cell_bot,gc_cell_top);
    }
  }
}

static
void
mark()
{

  intptr_t stack_bot = 0;
  intptr_t bot = (intptr_t)&stack_bot;

  mark_range(bot, stack_top);
}

// Unmark each cell of used list , before performing
// mark and sweep of garbage collection
static
void 
init_gc_collect()
{
  for (cell* cc = o2p(used_list); cc; cc = o2p(cc->next)) 
  {
    cc->mark = GC_NO_MARK;	  
  }  	
}

static
void
sweep()
{
    // For each item on the used list, check if it's been
    // marked. If not, free it - probably by calling insert_free.
  u16* pptr = &used_list;  
  for (cell* cc = o2p(used_list); cc; cc = o2p(*pptr)) 
  {
    u16 next_cell = cc->next;	  
    if(cc->mark == GC_NO_MARK)
    {
      // If cell is marked , then remove it from used list as below
      // and insert it onto free_list . 	    
      cc->used = 0;
      if(insert_free(p2o(cc),cc) != 0)
      {
        printf(" Insert free fails !  , cell_ofs : %d \n" , p2o(cc));
        assert(0);	
      }      
    }
    else
    {
      pptr = &(cc->next);	    
    }
    *pptr = next_cell;
  }
}

void
gc_collect()
{
    init_gc_collect();	
    mark();
    sweep();
}
