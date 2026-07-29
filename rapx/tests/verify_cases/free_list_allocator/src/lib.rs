#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(unused)]
#![allow(unsafe_op_in_unsafe_fn)]

use std::alloc::Layout;
use std::mem;
use std::ptr::NonNull;

// ─── FreeBlock: a node in the free list ─────────────────────────────────────
// Each free block is laid out in memory as:
//
//   ┌───────────── FreeBlock ───────────────┐
//   │ size: usize  │ next: Option<NonNull<FreeBlock>> │
//   └───────────────────────────────────────┘
//   │←── sizeof(FreeBlock) = 16 bytes ────→│
//
// `size` covers the ENTIRE free region: header + usable space.
// `next` links to the next free block (or None).
//
// RAPx invariant on `next`: it is either Null, or points to a valid,
// aligned, allocated, and owned FreeBlock.
#[repr(C)]
#[rapx::invariant(any(Null(next), (Align(next.unwrap_some(), FreeBlock), Allocated(next.unwrap_some(), FreeBlock, 1), Typed(next.unwrap_some(), FreeBlock), Owning(next.unwrap_some()))))]
pub struct FreeBlock {
    /// Total size of this free region in bytes (header + usable space).
    size: usize,
    /// Pointer to the next free block in the list, or `None` if last.
    next: Option<NonNull<FreeBlock>>,
}

// ─── FreeListAllocator ──────────────────────────────────────────────────────
// A simple first-fit free-list allocator.
//
//   heap ──→ [ FreeBlock | ...free space... ]
//               ↑ head
//
// `heap` points to the backing buffer (wrapped in Vec, leaked).
// `head` is the first node of the free list.
//
// RAPx invariants:
//   - `heap` is allocated, aligned for FreeBlock, owned, and within bounds.
//   - `head` (if Some) points to a valid FreeBlock.
#[rapx::invariant(Allocated(heap, u8, size))]
#[rapx::invariant(Align(heap, FreeBlock))]
#[rapx::invariant(Owning(heap))]
#[rapx::invariant(InBound(heap, u8, size))]
#[rapx::invariant(Align(head.unwrap_some(), FreeBlock))]
#[rapx::invariant(Allocated(head.unwrap_some(), FreeBlock, 1))]
#[rapx::invariant(Typed(head.unwrap_some(), FreeBlock))]
#[rapx::invariant(Owning(head.unwrap_some()))]
pub struct FreeListAllocator {
    /// Backing buffer (leaked `Vec<u8>`), aligned to `FreeBlock`.
    heap: NonNull<u8>,
    /// Total capacity of the backing buffer in bytes.
    size: usize,
    /// Head of the singly-linked free list, or `None` if exhausted.
    head: Option<NonNull<FreeBlock>>,
}

impl FreeListAllocator {
    // ── new: initialize the allocator with one big free block ───────────
    #[rapx::verify]
    pub fn new(size: usize) -> Self {
        assert!(size >= mem::size_of::<FreeBlock>());

        let mut buf = vec![0u8; size];
        let heap = NonNull::new(buf.as_mut_ptr()).expect("non-null after vec alloc");
        std::mem::forget(buf);

        // The entire buffer starts as a single FreeBlock.
        let block = heap.as_ptr() as *mut FreeBlock;
        unsafe {
            block.write(FreeBlock { size, next: None });
        }

        Self {
            heap,
            size,
            head: Some(unsafe { NonNull::new_unchecked(block) }),
        }
    }

    // ── alloc: first-fit allocation (SOUND version) ─────────────────────
    //
    // Memory layout inside a free block when allocating `size` bytes with
    // caller-requested `align`:
    //
    //   block_start →
    //   ┌───────────────┬── padding ───┬─── user data ───┬─── remainder ────┐
    //   │ FreeBlock hdr │  (align_up)  │     `size`      │  split FreeBlock  │
    //   │   16 bytes    │              │     bytes        │   (if large nuff) │
    //   └───────────────┴──────────────┴─────────────────┴──────────────────┘
    //                    ↑ data_start                    ↑ new_block_addr
    //
    //   padding = align_up(block_start + sizeof(FreeBlock), align) - block_start
    //
    // Key fix over alloc_unsound: the split pointer `new_block_addr` is
    // explicitly aligned to `align_of::<FreeBlock>()` so that writing a
    // FreeBlock header there is always valid.
    #[rapx::verify]
    pub fn alloc(&mut self, layout: Layout) -> Option<NonNull<u8>> {
        // Minimum size of the user-data portion is one FreeBlock header.
        let size = layout.size().max(mem::size_of::<FreeBlock>());
        let align = layout.align();

        let mut prev: Option<NonNull<FreeBlock>> = None;
        let mut current = self.head;

        while let Some(block) = current {
            // SAFETY: block comes from the free list — invariants guarantee
            // it is allocated, aligned, and typed for FreeBlock.
            let block_ref = unsafe { block.as_ref() };
            let block_start = block.as_ptr() as usize;

            // Place user data after the header, aligned as the caller asked.
            let data_start = align_up(block_start + mem::size_of::<FreeBlock>(), align);
            let padding = data_start - block_start;

            if block_ref.size >= padding + size {
                // This block fits the request.
                unsafe {
                    // Unlink the block from the free list.
                    if let Some(mut p) = prev {
                        p.as_mut().next = block_ref.next;
                    } else {
                        self.head = block_ref.next;
                    }

                    let remain = block_ref.size - padding - size;
                    if remain > mem::size_of::<FreeBlock>() {
                        // The split-off remainder must be aligned for FreeBlock.
                        // `data_start + size` is NOT guaranteed to be FreeBlock-aligned
                        // because `size` is an arbitrary byte count (e.g. 17).
                        // We align it up explicitly and shrink `remain` accordingly.
                        let new_block_addr =
                            align_up(data_start + size, mem::align_of::<FreeBlock>());
                        let extra_padding = new_block_addr - (data_start + size);
                        let actual_remain = remain - extra_padding;
                        if actual_remain > mem::size_of::<FreeBlock>() {
                            let new_block = new_block_addr as *mut FreeBlock;
                            new_block.write(FreeBlock {
                                size: actual_remain,
                                next: self.head,
                            });
                            self.head = NonNull::new(new_block);
                        }
                    }

                    return Some(NonNull::new_unchecked(data_start as *mut u8));
                }
            }

            // This block didn't fit — move to the next one.
            prev = current;
            current = block_ref.next;
        }

        None
    }

    // ── alloc_unsound: UNSOUND version kept for comparison ──────────────
    //
    // BUG on line with "let new_block = (data_start + size) as *mut FreeBlock;"
    //
    // `data_start` is aligned to `layout.align()` (which may be e.g. 1, 2, 4)
    // but `size` is a raw byte count.  Their sum may NOT be aligned to
    // `align_of::<FreeBlock>()` (= 8 on 64-bit).
    //
    // Example triggering UB: layout.align()=1, layout.size()=17
    //   data_start = block_start + 16  (both 8‑aligned, so still 8‑aligned)
    //   new_block  = data_start + 17   →  ends on a non‑8‑aligned address
    //   new_block.write(FreeBlock{...}) → unaligned write → UNDEFINED BEHAVIOR
    //
    // Note: RAPx only flags the path where prev=None (first block matches
    // immediately) because extra loop iterations give the analysis more
    // symbolic knowledge.  The soundness bug exists on ALL paths.
    #[rapx::verify]
    pub fn alloc_unsound(&mut self, layout: Layout) -> Option<NonNull<u8>> {
        let size = layout.size().max(mem::size_of::<FreeBlock>());
        let align = layout.align();

        let mut prev: Option<NonNull<FreeBlock>> = None;
        let mut current = self.head;

        while let Some(block) = current {
            let block_ref = unsafe { block.as_ref() };
            let block_start = block.as_ptr() as usize;
            let data_start = align_up(block_start + mem::size_of::<FreeBlock>(), align);
            let padding = data_start - block_start;

            if block_ref.size >= padding + size {
                unsafe {
                    if let Some(mut p) = prev {
                        p.as_mut().next = block_ref.next;
                    } else {
                        self.head = block_ref.next;
                    }

                    let remain = block_ref.size - padding - size;
                    if remain > mem::size_of::<FreeBlock>() {
                        // BUG: `data_start + size` is not necessarily
                        // aligned to `align_of::<FreeBlock>()`.
                        let new_block = (data_start + size) as *mut FreeBlock;
                        new_block.write(FreeBlock {
                            size: remain,
                            next: self.head,
                        });
                        self.head = NonNull::new(new_block);
                    }

                    return Some(NonNull::new_unchecked(data_start as *mut u8));
                }
            }

            prev = current;
            current = block_ref.next;
        }

        None
    }

    // ── dealloc: return a block to the free list ────────────────────────
    //
    // The caller passes a pointer to where the FreeBlock header should
    // be written, and the original data_size (from the corresponding
    // `Layout::size()`).
    //
    // RAPx preconditions (`rapx::requires`) tell the verifier that
    // `block` is an allocated, aligned, bounds‑checked FreeBlock pointer.
    #[rapx::verify]
    #[rapx::requires(Allocated(block, FreeBlock, 1), kind = "precond")]
    #[rapx::requires(Align(block, FreeBlock), kind = "precond")]
    #[rapx::requires(InBound(block, FreeBlock, 1), kind = "precond")]
    pub unsafe fn dealloc(&mut self, block: *mut FreeBlock, data_size: usize) {
        // The free block's `size` covers header + data.
        block.write(FreeBlock {
            size: data_size + mem::size_of::<FreeBlock>(),
            next: self.head,
        });
        self.head = NonNull::new(block);
        self.merge();
    }

    // ── merge: coalesce adjacent free blocks ────────────────────────────
    //
    // Walks the free list and merges consecutive blocks whose combined
    // memory is contiguous (end of `block` == start of `next`).
    #[rapx::verify]
    unsafe fn merge(&mut self) {
        let mut current = self.head;
        while let Some(mut block) = current {
            let next = block.as_ref().next;
            if let Some(next_block) = next {
                let end = block.as_ptr() as usize + block.as_ref().size;
                if end == next_block.as_ptr() as usize {
                    // Adjacent — merge by extending the first block.
                    block.as_mut().size += next_block.as_ref().size;
                    block.as_mut().next = next_block.as_ref().next;
                    continue; // re‑check the same block with the new next
                }
            }
            current = block.as_ref().next;
        }
    }
}

impl Drop for FreeListAllocator {
    fn drop(&mut self) {
        unsafe {
            drop(Vec::from_raw_parts(self.heap.as_ptr(), self.size, self.size));
        }
    }
}

/// Round `addr` up to the nearest multiple of `align` (align must be a power of two).
fn align_up(addr: usize, align: usize) -> usize {
    (addr + align - 1) & !(align - 1)
}
