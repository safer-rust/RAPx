#![feature(register_tool)]
#![register_tool(rapx)]
#![feature(allocator_api)]
#![feature(slice_ptr_get)]
#![allow(unsafe_op_in_unsafe_fn)]
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_mut)]
#![allow(unused_comparisons)]

// Challenge 4: Memory safety of BTreeMap's `btree::node` module.
// A faithful, self-contained port of `library/alloc/src/collections/btree/node.rs`.
// Adapted to RAPx by mapping `crate::alloc`/`crate::boxed` to `std` and inlining helper contracts.

use std::alloc::{Allocator, Layout};
use std::boxed::Box;
use std::marker::PhantomData;
use std::mem::{self, MaybeUninit};
use std::num::NonZero;
use std::ptr::{self, NonNull};
use std::slice::SliceIndex;

pub const B: usize = 6;
pub const CAPACITY: usize = 2 * B - 1;
pub const MIN_LEN_AFTER_SPLIT: usize = B - 1;
const KV_IDX_CENTER: usize = B - 1;
const EDGE_IDX_LEFT_OF_CENTER: usize = B - 1;
const EDGE_IDX_RIGHT_OF_CENTER: usize = B;

pub struct LeafNode<K, V> {
    pub parent: Option<NonNull<InternalNode<K, V>>>,
    pub parent_idx: MaybeUninit<u16>,
    pub len: u16,
    pub keys: [MaybeUninit<K>; CAPACITY],
    pub vals: [MaybeUninit<V>; CAPACITY],
}

impl<K, V> LeafNode<K, V> {
    #[rapx::requires(Allocated(this, LeafNode, 1))]
    #[rapx::requires(Align(this, LeafNode))]
    unsafe fn init(this: *mut Self) {
        unsafe {
            (&raw mut (*this).parent).write(None);
            (&raw mut (*this).len).write(0);
        }
    }

    #[rapx::verify]
    pub fn new<A: Allocator + Clone>(alloc: A) -> Box<Self, A> {
        let mut leaf = Box::new_uninit_in(alloc);
        unsafe {
            LeafNode::init(leaf.as_mut_ptr());
            leaf.assume_init()
        }
    }
}

#[repr(C)]
pub struct InternalNode<K, V> {
    pub data: LeafNode<K, V>,
    pub edges: [MaybeUninit<BoxedNode<K, V>>; 2 * B],
}

impl<K, V> InternalNode<K, V> {
    pub unsafe fn new<A: Allocator + Clone>(alloc: A) -> Box<Self, A> {
        let mut node = Box::<Self, _>::new_uninit_in(alloc);
        unsafe {
            LeafNode::init(&raw mut (*node.as_mut_ptr()).data);
            node.assume_init()
        }
    }
}

/// A managed, non-null pointer to a node.
pub type BoxedNode<K, V> = NonNull<LeafNode<K, V>>;

#[rapx::invariant(NonNull(node))]
#[rapx::invariant(Align(node, LeafNode))]
#[rapx::invariant(Allocated(node, LeafNode, 1))]
pub struct NodeRef<BorrowType, K, V, Type> {
    pub height: usize,
    pub node: NonNull<LeafNode<K, V>>,
    _marker: PhantomData<(BorrowType, Type)>,
}

pub type Root<K, V> = NodeRef<marker::Owned, K, V, marker::LeafOrInternal>;

impl<'a, K: 'a, V: 'a, Type> Copy for NodeRef<marker::Immut<'a>, K, V, Type> {}
impl<'a, K: 'a, V: 'a, Type> Clone for NodeRef<marker::Immut<'a>, K, V, Type> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<K, V> NodeRef<marker::Owned, K, V, marker::Leaf> {
    pub fn new_leaf<A: Allocator + Clone>(alloc: A) -> Self {
        Self::from_new_leaf(LeafNode::new(alloc))
    }

    fn from_new_leaf<A: Allocator + Clone>(leaf: Box<LeafNode<K, V>, A>) -> Self {
        let (node, _alloc) = Box::into_non_null_with_allocator(leaf);
        NodeRef { height: 0, node, _marker: PhantomData }
    }
}

impl<K, V> NodeRef<marker::Owned, K, V, marker::Internal> {
    #[rapx::verify]
    fn new_internal<A: Allocator + Clone>(child: Root<K, V>, alloc: A) -> Self {
        let mut new_node = unsafe { InternalNode::new(alloc) };
        new_node.edges[0].write(child.node);
        NodeRef::from_new_internal(new_node, NonZero::new(child.height + 1).unwrap())
    }

    fn from_new_internal<A: Allocator + Clone>(
        internal: Box<InternalNode<K, V>, A>,
        height: NonZero<usize>,
    ) -> Self {
        let (node, _alloc) = Box::into_non_null_with_allocator(internal);
        let mut this =
            NodeRef { height: height.into(), node: node.cast(), _marker: PhantomData };
        this.borrow_mut().correct_all_childrens_parent_links();
        this
    }
}

impl<BorrowType, K, V> NodeRef<BorrowType, K, V, marker::Internal> {
    fn from_internal(node: NonNull<InternalNode<K, V>>, height: usize) -> Self {
        debug_assert!(height > 0);
        NodeRef { height, node: node.cast(), _marker: PhantomData }
    }
}

impl<BorrowType, K, V> NodeRef<BorrowType, K, V, marker::Internal> {
    fn as_internal_ptr(this: &Self) -> *mut InternalNode<K, V> {
        this.node.as_ptr() as *mut InternalNode<K, V>
    }
}

impl<'a, K, V> NodeRef<marker::Mut<'a>, K, V, marker::Internal> {
    #[rapx::verify]
    pub fn as_internal_mut(&mut self) -> &mut InternalNode<K, V> {
        let ptr = Self::as_internal_ptr(self);
        unsafe { &mut *ptr }
    }
}

impl<BorrowType, K, V, Type> NodeRef<BorrowType, K, V, Type> {
    #[rapx::verify]
    pub fn len(&self) -> usize {
        unsafe { usize::from((*Self::as_leaf_ptr(self)).len) }
    }

    pub fn height(&self) -> usize {
        self.height
    }

    pub fn reborrow(&self) -> NodeRef<marker::Immut<'_>, K, V, Type> {
        NodeRef { height: self.height, node: self.node, _marker: PhantomData }
    }

    fn as_leaf_ptr(this: &Self) -> *mut LeafNode<K, V> {
        this.node.as_ptr()
    }
}

impl<BorrowType: marker::BorrowType, K, V, Type> NodeRef<BorrowType, K, V, Type> {
    #[rapx::verify]
    pub fn ascend(
        self,
    ) -> Result<Handle<NodeRef<BorrowType, K, V, marker::Internal>, marker::Edge>, Self> {
        const { assert!(BorrowType::TRAVERSAL_PERMIT) }

        let leaf_ptr: *const _ = Self::as_leaf_ptr(&self);
        unsafe { (*leaf_ptr).parent }
            .as_ref()
            .map(|parent| Handle {
                node: NodeRef::from_internal(*parent, self.height + 1),
                idx: unsafe { usize::from((*leaf_ptr).parent_idx.assume_init()) },
                _marker: PhantomData,
            })
            .ok_or(self)
    }

    #[rapx::verify]
    pub fn first_edge(self) -> Handle<Self, marker::Edge> {
        unsafe { Handle::new_edge(self, 0) }
    }

    #[rapx::verify]
    pub fn last_edge(self) -> Handle<Self, marker::Edge> {
        let len = self.len();
        unsafe { Handle::new_edge(self, len) }
    }

    #[rapx::verify]
    pub fn first_kv(self) -> Handle<Self, marker::KV> {
        let len = self.len();
        assert!(len > 0);
        unsafe { Handle::new_kv(self, 0) }
    }

    #[rapx::verify]
    pub fn last_kv(self) -> Handle<Self, marker::KV> {
        let len = self.len();
        assert!(len > 0);
        unsafe { Handle::new_kv(self, len - 1) }
    }
}

impl<BorrowType, K, V, Type> NodeRef<BorrowType, K, V, Type> {
    fn eq(&self, other: &Self) -> bool {
        let Self { node, height, _marker } = self;
        if node.eq(&other.node) {
            debug_assert_eq!(*height, other.height);
            true
        } else {
            false
        }
    }
}

impl<'a, K: 'a, V: 'a, Type> NodeRef<marker::Immut<'a>, K, V, Type> {
    #[rapx::verify]
    fn into_leaf(self) -> &'a LeafNode<K, V> {
        let ptr = Self::as_leaf_ptr(&self);
        unsafe { &*ptr }
    }

    #[rapx::verify]
    pub fn keys(&self) -> &[K] {
        let leaf = self.into_leaf();
        unsafe { leaf.keys.get_unchecked(..usize::from(leaf.len)).assume_init_ref() }
    }
}

impl<K, V> NodeRef<marker::Dying, K, V, marker::LeafOrInternal> {
    pub unsafe fn deallocate_and_ascend<A: Allocator + Clone>(
        self,
        alloc: A,
    ) -> Option<Handle<NodeRef<marker::Dying, K, V, marker::Internal>, marker::Edge>> {
        let height = self.height;
        let node = self.node;
        let ret = self.ascend().ok();
        unsafe {
            alloc.deallocate(
                node.cast(),
                if height > 0 {
                    Layout::new::<InternalNode<K, V>>()
                } else {
                    Layout::new::<LeafNode<K, V>>()
                },
            );
        }
        ret
    }
}

impl<'a, K, V, Type> NodeRef<marker::Mut<'a>, K, V, Type> {
    pub unsafe fn reborrow_mut(&mut self) -> NodeRef<marker::Mut<'_>, K, V, Type> {
        NodeRef { height: self.height, node: self.node, _marker: PhantomData }
    }

    #[rapx::verify]
    pub fn as_leaf_mut(&mut self) -> &mut LeafNode<K, V> {
        let ptr = Self::as_leaf_ptr(self);
        unsafe { &mut *ptr }
    }

    #[rapx::verify]
    pub fn into_leaf_mut(mut self) -> &'a mut LeafNode<K, V> {
        let ptr = Self::as_leaf_ptr(&mut self);
        unsafe { &mut *ptr }
    }

    pub fn dormant(&self) -> NodeRef<marker::DormantMut, K, V, Type> {
        NodeRef { height: self.height, node: self.node, _marker: PhantomData }
    }
}

impl<K, V, Type> NodeRef<marker::DormantMut, K, V, Type> {
    pub unsafe fn awaken<'a>(self) -> NodeRef<marker::Mut<'a>, K, V, Type> {
        NodeRef { height: self.height, node: self.node, _marker: PhantomData }
    }
}

impl<K, V, Type> NodeRef<marker::Dying, K, V, Type> {
    #[rapx::verify]
    pub fn as_leaf_dying(&mut self) -> &mut LeafNode<K, V> {
        let ptr = Self::as_leaf_ptr(self);
        unsafe { &mut *ptr }
    }
}

impl<'a, K: 'a, V: 'a, Type> NodeRef<marker::Mut<'a>, K, V, Type> {
    #[rapx::requires(ValidNum(index < CAPACITY))]
    unsafe fn key_area_mut<I, Output: ?Sized>(&mut self, index: I) -> &mut Output
    where
        I: SliceIndex<[MaybeUninit<K>], Output = Output>,
    {
        unsafe { self.as_leaf_mut().keys.as_mut_slice().get_unchecked_mut(index) }
    }

    #[rapx::requires(ValidNum(index < CAPACITY))]
    unsafe fn val_area_mut<I, Output: ?Sized>(&mut self, index: I) -> &mut Output
    where
        I: SliceIndex<[MaybeUninit<V>], Output = Output>,
    {
        unsafe { self.as_leaf_mut().vals.as_mut_slice().get_unchecked_mut(index) }
    }
}

impl<'a, K: 'a, V: 'a> NodeRef<marker::Mut<'a>, K, V, marker::Internal> {
    #[rapx::requires(ValidNum(index < CAPACITY + 1))]
    unsafe fn edge_area_mut<I, Output: ?Sized>(&mut self, index: I) -> &mut Output
    where
        I: SliceIndex<[MaybeUninit<BoxedNode<K, V>>], Output = Output>,
    {
        unsafe { self.as_internal_mut().edges.as_mut_slice().get_unchecked_mut(index) }
    }
}

impl<'a, K, V, Type> NodeRef<marker::ValMut<'a>, K, V, Type> {
    unsafe fn into_key_val_mut_at(mut self, idx: usize) -> (&'a K, &'a mut V) {
        let leaf = Self::as_leaf_ptr(&mut self);
        let keys = unsafe { &raw const (*leaf).keys };
        let vals = unsafe { &raw mut (*leaf).vals };
        let keys: *const [_] = keys;
        let vals: *mut [_] = vals;
        let key = unsafe { (&*keys.get_unchecked(idx)).assume_init_ref() };
        let val = unsafe { (&mut *vals.get_unchecked_mut(idx)).assume_init_mut() };
        (key, val)
    }
}

impl<'a, K: 'a, V: 'a, Type> NodeRef<marker::Mut<'a>, K, V, Type> {
    pub fn len_mut(&mut self) -> &mut u16 {
        &mut self.as_leaf_mut().len
    }
}

impl<'a, K, V> NodeRef<marker::Mut<'a>, K, V, marker::Internal> {
    unsafe fn correct_childrens_parent_links<R: Iterator<Item = usize>>(&mut self, range: R) {
        for i in range {
            debug_assert!(i <= self.len());
            unsafe { Handle::new_edge(self.reborrow_mut(), i) }.correct_parent_link();
        }
    }

    fn correct_all_childrens_parent_links(&mut self) {
        let len = self.len();
        unsafe { self.correct_childrens_parent_links(0..=len) };
    }
}

impl<'a, K: 'a, V: 'a> NodeRef<marker::Mut<'a>, K, V, marker::LeafOrInternal> {
    fn set_parent_link(&mut self, parent: NonNull<InternalNode<K, V>>, parent_idx: usize) {
        let leaf = Self::as_leaf_ptr(self);
        unsafe { (*leaf).parent = Some(parent) };
        unsafe { (*leaf).parent_idx.write(parent_idx as u16) };
    }
}

impl<K, V> NodeRef<marker::Owned, K, V, marker::LeafOrInternal> {
    fn clear_parent_link(&mut self) {
        let mut root_node = self.borrow_mut();
        let leaf = root_node.as_leaf_mut();
        leaf.parent = None;
    }
}

impl<K, V> NodeRef<marker::Owned, K, V, marker::LeafOrInternal> {
    pub fn new<A: Allocator + Clone>(alloc: A) -> Self {
        NodeRef::new_leaf(alloc).forget_type()
    }

    pub fn push_internal_level<A: Allocator + Clone>(
        &mut self,
        alloc: A,
    ) -> NodeRef<marker::Mut<'_>, K, V, marker::Internal> {
        take_mut(self, |old_root| NodeRef::new_internal(old_root, alloc).forget_type());

        NodeRef { height: self.height, node: self.node, _marker: PhantomData }
    }

    #[rapx::verify]
    pub fn pop_internal_level<A: Allocator + Clone>(&mut self, alloc: A) {
        assert!(self.height > 0);

        let top = self.node;

        let mut internal_self = unsafe { self.borrow_mut().cast_to_internal_unchecked() };
        let internal_node = internal_self.as_internal_mut();
        self.node = unsafe { internal_node.edges[0].assume_init_read() };
        self.height -= 1;
        self.clear_parent_link();

        unsafe {
            alloc.deallocate(top.cast(), Layout::new::<InternalNode<K, V>>());
        }
    }
}

impl<K, V, Type> NodeRef<marker::Owned, K, V, Type> {
    pub fn borrow_mut(&mut self) -> NodeRef<marker::Mut<'_>, K, V, Type> {
        NodeRef { height: self.height, node: self.node, _marker: PhantomData }
    }

    pub fn borrow_valmut(&mut self) -> NodeRef<marker::ValMut<'_>, K, V, Type> {
        NodeRef { height: self.height, node: self.node, _marker: PhantomData }
    }

    pub fn into_dying(self) -> NodeRef<marker::Dying, K, V, Type> {
        NodeRef { height: self.height, node: self.node, _marker: PhantomData }
    }
}

impl<'a, K: 'a, V: 'a> NodeRef<marker::Mut<'a>, K, V, marker::Leaf> {
    pub unsafe fn push_with_handle<'b>(
        &mut self,
        key: K,
        val: V,
    ) -> Handle<NodeRef<marker::Mut<'b>, K, V, marker::Leaf>, marker::KV> {
        let len = self.len_mut();
        let idx = usize::from(*len);
        assert!(idx < CAPACITY);
        *len += 1;
        unsafe {
            self.key_area_mut(idx).write(key);
            self.val_area_mut(idx).write(val);
            Handle::new_kv(
                NodeRef { height: self.height, node: self.node, _marker: PhantomData },
                idx,
            )
        }
    }

    #[rapx::verify]
    pub fn push(&mut self, key: K, val: V) -> *mut V {
        unsafe { self.push_with_handle(key, val).into_val_mut() }
    }
}

impl<'a, K: 'a, V: 'a> NodeRef<marker::Mut<'a>, K, V, marker::Internal> {
    #[rapx::verify]
    pub fn push(&mut self, key: K, val: V, edge: Root<K, V>) {
        assert!(edge.height == self.height - 1);

        let len = self.len_mut();
        let idx = usize::from(*len);
        assert!(idx < CAPACITY);
        *len += 1;
        unsafe {
            self.key_area_mut(idx).write(key);
            self.val_area_mut(idx).write(val);
            self.edge_area_mut(idx + 1).write(edge.node);
            Handle::new_edge(self.reborrow_mut(), idx + 1).correct_parent_link();
        }
    }
}

impl<BorrowType, K, V> NodeRef<BorrowType, K, V, marker::Leaf> {
    pub fn forget_type(self) -> NodeRef<BorrowType, K, V, marker::LeafOrInternal> {
        NodeRef { height: self.height, node: self.node, _marker: PhantomData }
    }
}

impl<BorrowType, K, V> NodeRef<BorrowType, K, V, marker::Internal> {
    pub fn forget_type(self) -> NodeRef<BorrowType, K, V, marker::LeafOrInternal> {
        NodeRef { height: self.height, node: self.node, _marker: PhantomData }
    }
}

impl<BorrowType, K, V> NodeRef<BorrowType, K, V, marker::LeafOrInternal> {
    pub fn force(
        self,
    ) -> ForceResult<
        NodeRef<BorrowType, K, V, marker::Leaf>,
        NodeRef<BorrowType, K, V, marker::Internal>,
    > {
        if self.height == 0 {
            ForceResult::Leaf(NodeRef {
                height: self.height,
                node: self.node,
                _marker: PhantomData,
            })
        } else {
            ForceResult::Internal(NodeRef {
                height: self.height,
                node: self.node,
                _marker: PhantomData,
            })
        }
    }
}

impl<'a, K, V> NodeRef<marker::Mut<'a>, K, V, marker::LeafOrInternal> {
    pub unsafe fn cast_to_leaf_unchecked(self) -> NodeRef<marker::Mut<'a>, K, V, marker::Leaf> {
        debug_assert!(self.height == 0);
        NodeRef { height: self.height, node: self.node, _marker: PhantomData }
    }

    unsafe fn cast_to_internal_unchecked(self) -> NodeRef<marker::Mut<'a>, K, V, marker::Internal> {
        debug_assert!(self.height > 0);
        NodeRef { height: self.height, node: self.node, _marker: PhantomData }
    }
}

pub struct Handle<Node, Type> {
    pub node: Node,
    pub idx: usize,
    _marker: PhantomData<Type>,
}

impl<Node: Copy, Type> Copy for Handle<Node, Type> {}
impl<Node: Copy, Type> Clone for Handle<Node, Type> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<Node, Type> Handle<Node, Type> {
    pub fn into_node(self) -> Node {
        self.node
    }

    pub fn idx(&self) -> usize {
        self.idx
    }
}

impl<BorrowType, K, V, NodeType> Handle<NodeRef<BorrowType, K, V, NodeType>, marker::KV> {
    #[rapx::requires(ValidNum(idx < node.len()))]
    pub unsafe fn new_kv(node: NodeRef<BorrowType, K, V, NodeType>, idx: usize) -> Self {
        debug_assert!(idx < node.len());

        Handle { node, idx, _marker: PhantomData }
    }

    #[rapx::verify]
    pub fn left_edge(self) -> Handle<NodeRef<BorrowType, K, V, NodeType>, marker::Edge> {
        unsafe { Handle::new_edge(self.node, self.idx) }
    }

    #[rapx::verify]
    pub fn right_edge(self) -> Handle<NodeRef<BorrowType, K, V, NodeType>, marker::Edge> {
        unsafe { Handle::new_edge(self.node, self.idx + 1) }
    }
}

impl<BorrowType, K, V, NodeType, HandleType> PartialEq
    for Handle<NodeRef<BorrowType, K, V, NodeType>, HandleType>
{
    fn eq(&self, other: &Self) -> bool {
        let Self { node, idx, _marker } = self;
        node.eq(&other.node) && *idx == other.idx
    }
}

impl<BorrowType, K, V, NodeType, HandleType>
    Handle<NodeRef<BorrowType, K, V, NodeType>, HandleType>
{
    pub fn reborrow(
        &self,
    ) -> Handle<NodeRef<marker::Immut<'_>, K, V, NodeType>, HandleType> {
        Handle { node: self.node.reborrow(), idx: self.idx, _marker: PhantomData }
    }
}

impl<'a, K, V, NodeType, HandleType>
    Handle<NodeRef<marker::Mut<'a>, K, V, NodeType>, HandleType>
{
    pub unsafe fn reborrow_mut(
        &mut self,
    ) -> Handle<NodeRef<marker::Mut<'_>, K, V, NodeType>, HandleType> {
        Handle { node: unsafe { self.node.reborrow_mut() }, idx: self.idx, _marker: PhantomData }
    }

    pub fn dormant(
        &self,
    ) -> Handle<NodeRef<marker::DormantMut, K, V, NodeType>, HandleType> {
        Handle { node: self.node.dormant(), idx: self.idx, _marker: PhantomData }
    }
}

impl<K, V, NodeType, HandleType>
    Handle<NodeRef<marker::DormantMut, K, V, NodeType>, HandleType>
{
    pub unsafe fn awaken<'a>(
        self,
    ) -> Handle<NodeRef<marker::Mut<'a>, K, V, NodeType>, HandleType> {
        Handle { node: unsafe { self.node.awaken() }, idx: self.idx, _marker: PhantomData }
    }
}

impl<BorrowType, K, V, NodeType> Handle<NodeRef<BorrowType, K, V, NodeType>, marker::Edge> {
    #[rapx::requires(ValidNum(idx <= node.len()))]
    pub unsafe fn new_edge(node: NodeRef<BorrowType, K, V, NodeType>, idx: usize) -> Self {
        debug_assert!(idx <= node.len());

        Handle { node, idx, _marker: PhantomData }
    }

    #[rapx::verify]
    pub fn left_kv(
        self,
    ) -> Result<Handle<NodeRef<BorrowType, K, V, NodeType>, marker::KV>, Self> {
        if self.idx > 0 {
            Ok(unsafe { Handle::new_kv(self.node, self.idx - 1) })
        } else {
            Err(self)
        }
    }

    #[rapx::verify]
    pub fn right_kv(
        self,
    ) -> Result<Handle<NodeRef<BorrowType, K, V, NodeType>, marker::KV>, Self> {
        if self.idx < self.node.len() {
            Ok(unsafe { Handle::new_kv(self.node, self.idx) })
        } else {
            Err(self)
        }
    }
}

pub enum LeftOrRight<T> {
    Left(T),
    Right(T),
}

fn splitpoint(edge_idx: usize) -> (usize, LeftOrRight<usize>) {
    debug_assert!(edge_idx <= CAPACITY);
    match edge_idx {
        0..EDGE_IDX_LEFT_OF_CENTER => (KV_IDX_CENTER - 1, LeftOrRight::Left(edge_idx)),
        EDGE_IDX_LEFT_OF_CENTER => (KV_IDX_CENTER, LeftOrRight::Left(edge_idx)),
        EDGE_IDX_RIGHT_OF_CENTER => (KV_IDX_CENTER, LeftOrRight::Right(0)),
        _ => (KV_IDX_CENTER + 1, LeftOrRight::Right(edge_idx - (KV_IDX_CENTER + 1 + 1))),
    }
}

impl<'a, K: 'a, V: 'a> Handle<NodeRef<marker::Mut<'a>, K, V, marker::Leaf>, marker::Edge> {
    unsafe fn insert_fit(
        mut self,
        key: K,
        val: V,
    ) -> Handle<NodeRef<marker::Mut<'a>, K, V, marker::Leaf>, marker::KV> {
        debug_assert!(self.node.len() < CAPACITY);
        let new_len = self.node.len() + 1;

        unsafe {
            slice_insert(self.node.key_area_mut(..new_len), self.idx, key);
            slice_insert(self.node.val_area_mut(..new_len), self.idx, val);
            *self.node.len_mut() = new_len as u16;

            Handle::new_kv(self.node, self.idx)
        }
    }
}

impl<'a, K: 'a, V: 'a> Handle<NodeRef<marker::Mut<'a>, K, V, marker::Leaf>, marker::Edge> {
    fn insert<A: Allocator + Clone>(
        self,
        key: K,
        val: V,
        alloc: A,
    ) -> (
        Option<SplitResult<'a, K, V, marker::Leaf>>,
        Handle<NodeRef<marker::DormantMut, K, V, marker::Leaf>, marker::KV>,
    ) {
        if self.node.len() < CAPACITY {
            let handle = unsafe { self.insert_fit(key, val) };
            (None, handle.dormant())
        } else {
            let (middle_kv_idx, insertion) = splitpoint(self.idx);
            let middle = unsafe { Handle::new_kv(self.node, middle_kv_idx) };
            let mut result = middle.split(alloc);
            let insertion_edge = match insertion {
                LeftOrRight::Left(insert_idx) => unsafe {
                    Handle::new_edge(result.left.reborrow_mut(), insert_idx)
                },
                LeftOrRight::Right(insert_idx) => unsafe {
                    Handle::new_edge(result.right.borrow_mut(), insert_idx)
                },
            };
            let handle = unsafe { insertion_edge.insert_fit(key, val).dormant() };
            (Some(result), handle)
        }
    }
}

impl<'a, K, V> Handle<NodeRef<marker::Mut<'a>, K, V, marker::Internal>, marker::Edge> {
    fn correct_parent_link(self) {
        let ptr = unsafe { NonNull::new_unchecked(NodeRef::as_internal_ptr(&self.node)) };
        let idx = self.idx;
        let mut child = self.descend();
        child.set_parent_link(ptr, idx);
    }
}

impl<'a, K: 'a, V: 'a> Handle<NodeRef<marker::Mut<'a>, K, V, marker::Internal>, marker::Edge> {
    fn insert_fit(&mut self, key: K, val: V, edge: Root<K, V>) {
        debug_assert!(self.node.len() < CAPACITY);
        debug_assert!(edge.height == self.node.height - 1);
        let new_len = self.node.len() + 1;

        unsafe {
            slice_insert(self.node.key_area_mut(..new_len), self.idx, key);
            slice_insert(self.node.val_area_mut(..new_len), self.idx, val);
            slice_insert(self.node.edge_area_mut(..new_len + 1), self.idx + 1, edge.node);
            *self.node.len_mut() = new_len as u16;

            self.node.correct_childrens_parent_links(self.idx + 1..new_len + 1);
        }
    }

    fn insert<A: Allocator + Clone>(
        mut self,
        key: K,
        val: V,
        edge: Root<K, V>,
        alloc: A,
    ) -> Option<SplitResult<'a, K, V, marker::Internal>> {
        assert!(edge.height == self.node.height - 1);

        if self.node.len() < CAPACITY {
            self.insert_fit(key, val, edge);
            None
        } else {
            let (middle_kv_idx, insertion) = splitpoint(self.idx);
            let middle = unsafe { Handle::new_kv(self.node, middle_kv_idx) };
            let mut result = middle.split(alloc);
            let mut insertion_edge = match insertion {
                LeftOrRight::Left(insert_idx) => unsafe {
                    Handle::new_edge(result.left.reborrow_mut(), insert_idx)
                },
                LeftOrRight::Right(insert_idx) => unsafe {
                    Handle::new_edge(result.right.borrow_mut(), insert_idx)
                },
            };
            insertion_edge.insert_fit(key, val, edge);
            Some(result)
        }
    }
}

impl<'a, K: 'a, V: 'a> Handle<NodeRef<marker::Mut<'a>, K, V, marker::Leaf>, marker::Edge> {
    #[rapx::verify]
    pub fn insert_recursing<A: Allocator + Clone>(
        self,
        key: K,
        value: V,
        alloc: A,
        split_root: impl FnOnce(SplitResult<'a, K, V, marker::LeafOrInternal>),
    ) -> Handle<NodeRef<marker::Mut<'a>, K, V, marker::Leaf>, marker::KV> {
        let (mut split, handle) = match self.insert(key, value, alloc.clone()) {
            (None, handle) => return unsafe { handle.awaken() },
            (Some(split), handle) => (split.forget_node_type(), handle),
        };

        loop {
            split = match split.left.ascend() {
                Ok(parent) => {
                    match parent.insert(split.kv.0, split.kv.1, split.right, alloc.clone()) {
                        None => return unsafe { handle.awaken() },
                        Some(split) => split.forget_node_type(),
                    }
                }
                Err(root) => {
                    split_root(SplitResult { left: root, ..split });
                    return unsafe { handle.awaken() };
                }
            };
        }
    }
}

impl<BorrowType: marker::BorrowType, K, V>
    Handle<NodeRef<BorrowType, K, V, marker::Internal>, marker::Edge>
{
    #[rapx::verify]
    pub fn descend(self) -> NodeRef<BorrowType, K, V, marker::LeafOrInternal> {
        const { assert!(BorrowType::TRAVERSAL_PERMIT) }

        let parent_ptr = NodeRef::as_internal_ptr(&self.node);
        let node = unsafe { (*parent_ptr).edges.get_unchecked(self.idx).assume_init_read() };
        NodeRef { node, height: self.node.height - 1, _marker: PhantomData }
    }
}

impl<'a, K: 'a, V: 'a, NodeType> Handle<NodeRef<marker::Immut<'a>, K, V, NodeType>, marker::KV> {
    #[rapx::verify]
    pub fn into_kv(self) -> (&'a K, &'a V) {
        debug_assert!(self.idx < self.node.len());
        let leaf = self.node.into_leaf();
        let k = unsafe { leaf.keys.get_unchecked(self.idx).assume_init_ref() };
        let v = unsafe { leaf.vals.get_unchecked(self.idx).assume_init_ref() };
        (k, v)
    }
}

impl<'a, K: 'a, V: 'a, NodeType> Handle<NodeRef<marker::Mut<'a>, K, V, NodeType>, marker::KV> {
    #[rapx::verify]
    pub fn key_mut(&mut self) -> &mut K {
        unsafe { self.node.key_area_mut(self.idx).assume_init_mut() }
    }

    #[rapx::verify]
    pub fn into_val_mut(self) -> &'a mut V {
        debug_assert!(self.idx < self.node.len());
        let leaf = self.node.into_leaf_mut();
        unsafe { leaf.vals.get_unchecked_mut(self.idx).assume_init_mut() }
    }

    #[rapx::verify]
    pub fn into_kv_mut(self) -> (&'a mut K, &'a mut V) {
        debug_assert!(self.idx < self.node.len());
        let leaf = self.node.into_leaf_mut();
        let k = unsafe { leaf.keys.get_unchecked_mut(self.idx).assume_init_mut() };
        let v = unsafe { leaf.vals.get_unchecked_mut(self.idx).assume_init_mut() };
        (k, v)
    }
}

impl<'a, K, V, NodeType> Handle<NodeRef<marker::ValMut<'a>, K, V, NodeType>, marker::KV> {
    #[rapx::verify]
    pub fn into_kv_valmut(self) -> (&'a K, &'a mut V) {
        unsafe { self.node.into_key_val_mut_at(self.idx) }
    }
}

impl<'a, K: 'a, V: 'a, NodeType> Handle<NodeRef<marker::Mut<'a>, K, V, NodeType>, marker::KV> {
    #[rapx::verify]
    pub fn kv_mut(&mut self) -> (&mut K, &mut V) {
        debug_assert!(self.idx < self.node.len());
        unsafe {
            let leaf = self.node.as_leaf_mut();
            let key = leaf.keys.get_unchecked_mut(self.idx).assume_init_mut();
            let val = leaf.vals.get_unchecked_mut(self.idx).assume_init_mut();
            (key, val)
        }
    }

    pub fn replace_kv(&mut self, k: K, v: V) -> (K, V) {
        let (key, val) = self.kv_mut();
        (mem::replace(key, k), mem::replace(val, v))
    }
}

impl<K, V, NodeType> Handle<NodeRef<marker::Dying, K, V, NodeType>, marker::KV> {
    pub unsafe fn into_key_val(mut self) -> (K, V) {
        debug_assert!(self.idx < self.node.len());
        let leaf = self.node.as_leaf_dying();
        unsafe {
            let key = leaf.keys.get_unchecked_mut(self.idx).assume_init_read();
            let val = leaf.vals.get_unchecked_mut(self.idx).assume_init_read();
            (key, val)
        }
    }

    pub unsafe fn drop_key_val(mut self) {
        struct Dropper<'a, T>(&'a mut MaybeUninit<T>);
        impl<T> Drop for Dropper<'_, T> {
            #[inline]
            fn drop(&mut self) {
                unsafe {
                    self.0.assume_init_drop();
                }
            }
        }

        debug_assert!(self.idx < self.node.len());
        let leaf = self.node.as_leaf_dying();
        unsafe {
            let key = leaf.keys.get_unchecked_mut(self.idx);
            let val = leaf.vals.get_unchecked_mut(self.idx);
            let _guard = Dropper(val);
            key.assume_init_drop();
        }
    }
}

impl<'a, K: 'a, V: 'a, NodeType> Handle<NodeRef<marker::Mut<'a>, K, V, NodeType>, marker::KV> {
    fn split_leaf_data(&mut self, new_node: &mut LeafNode<K, V>) -> (K, V) {
        debug_assert!(self.idx < self.node.len());
        let old_len = self.node.len();
        let new_len = old_len - self.idx - 1;
        new_node.len = new_len as u16;
        unsafe {
            let k = self.node.key_area_mut(self.idx).assume_init_read();
            let v = self.node.val_area_mut(self.idx).assume_init_read();

            move_to_slice(
                self.node.key_area_mut(self.idx + 1..old_len),
                &mut new_node.keys[..new_len],
            );
            move_to_slice(
                self.node.val_area_mut(self.idx + 1..old_len),
                &mut new_node.vals[..new_len],
            );

            *self.node.len_mut() = self.idx as u16;
            (k, v)
        }
    }
}

impl<'a, K: 'a, V: 'a> Handle<NodeRef<marker::Mut<'a>, K, V, marker::Leaf>, marker::KV> {
    pub fn split<A: Allocator + Clone>(
        mut self,
        alloc: A,
    ) -> SplitResult<'a, K, V, marker::Leaf> {
        let mut new_node = LeafNode::new(alloc);

        let kv = self.split_leaf_data(&mut new_node);

        let right = NodeRef::from_new_leaf(new_node);
        SplitResult { left: self.node, kv, right }
    }

    pub fn remove(
        mut self,
    ) -> ((K, V), Handle<NodeRef<marker::Mut<'a>, K, V, marker::Leaf>, marker::Edge>) {
        let old_len = self.node.len();
        unsafe {
            let k = slice_remove(self.node.key_area_mut(..old_len), self.idx);
            let v = slice_remove(self.node.val_area_mut(..old_len), self.idx);
            *self.node.len_mut() = (old_len - 1) as u16;
            ((k, v), self.left_edge())
        }
    }
}

impl<'a, K: 'a, V: 'a> Handle<NodeRef<marker::Mut<'a>, K, V, marker::Internal>, marker::KV> {
    pub fn split<A: Allocator + Clone>(
        mut self,
        alloc: A,
    ) -> SplitResult<'a, K, V, marker::Internal> {
        let old_len = self.node.len();
        unsafe {
            let mut new_node = InternalNode::new(alloc);
            let kv = self.split_leaf_data(&mut new_node.data);
            let new_len = usize::from(new_node.data.len);
            move_to_slice(
                self.node.edge_area_mut(self.idx + 1..old_len + 1),
                &mut new_node.edges[..new_len + 1],
            );

            let height = NonZero::new_unchecked(self.node.height);
            let right = NodeRef::from_new_internal(new_node, height);

            SplitResult { left: self.node, kv, right }
        }
    }
}

pub struct BalancingContext<'a, K, V> {
    parent: Handle<NodeRef<marker::Mut<'a>, K, V, marker::Internal>, marker::KV>,
    left_child: NodeRef<marker::Mut<'a>, K, V, marker::LeafOrInternal>,
    right_child: NodeRef<marker::Mut<'a>, K, V, marker::LeafOrInternal>,
}

impl<'a, K, V> Handle<NodeRef<marker::Mut<'a>, K, V, marker::Internal>, marker::KV> {
    pub fn consider_for_balancing(self) -> BalancingContext<'a, K, V> {
        let self1 = unsafe { ptr::read(&self) };
        let self2 = unsafe { ptr::read(&self) };
        BalancingContext {
            parent: self,
            left_child: self1.left_edge().descend(),
            right_child: self2.right_edge().descend(),
        }
    }
}

impl<'a, K, V> NodeRef<marker::Mut<'a>, K, V, marker::LeafOrInternal> {
    pub fn choose_parent_kv(self) -> Result<LeftOrRight<BalancingContext<'a, K, V>>, Self> {
        match unsafe { ptr::read(&self) }.ascend() {
            Ok(parent_edge) => match parent_edge.left_kv() {
                Ok(left_parent_kv) => Ok(LeftOrRight::Left(BalancingContext {
                    parent: unsafe { ptr::read(&left_parent_kv) },
                    left_child: left_parent_kv.left_edge().descend(),
                    right_child: self,
                })),
                Err(parent_edge) => match parent_edge.right_kv() {
                    Ok(right_parent_kv) => Ok(LeftOrRight::Right(BalancingContext {
                        parent: unsafe { ptr::read(&right_parent_kv) },
                        left_child: self,
                        right_child: right_parent_kv.right_edge().descend(),
                    })),
                    Err(_) => unreachable!("empty internal node"),
                },
            },
            Err(root) => Err(root),
        }
    }
}

impl<'a, K, V> BalancingContext<'a, K, V> {
    pub fn left_child_len(&self) -> usize {
        self.left_child.len()
    }

    pub fn right_child_len(&self) -> usize {
        self.right_child.len()
    }

    pub fn into_left_child(self) -> NodeRef<marker::Mut<'a>, K, V, marker::LeafOrInternal> {
        self.left_child
    }

    pub fn into_right_child(self) -> NodeRef<marker::Mut<'a>, K, V, marker::LeafOrInternal> {
        self.right_child
    }

    pub fn can_merge(&self) -> bool {
        self.left_child.len() + 1 + self.right_child.len() <= CAPACITY
    }
}

impl<'a, K: 'a, V: 'a> BalancingContext<'a, K, V> {
    #[rapx::verify]
    fn do_merge<
        F: FnOnce(
            NodeRef<marker::Mut<'a>, K, V, marker::Internal>,
            NodeRef<marker::Mut<'a>, K, V, marker::LeafOrInternal>,
        ) -> R,
        R,
        A: Allocator,
    >(
        self,
        result: F,
        alloc: A,
    ) -> R {
        let Handle { node: mut parent_node, idx: parent_idx, _marker } = self.parent;
        let old_parent_len = parent_node.len();
        let mut left_node = self.left_child;
        let old_left_len = left_node.len();
        let mut right_node = self.right_child;
        let right_len = right_node.len();
        let new_left_len = old_left_len + 1 + right_len;

        assert!(new_left_len <= CAPACITY);

        unsafe {
            *left_node.len_mut() = new_left_len as u16;

            let parent_key = slice_remove(parent_node.key_area_mut(..old_parent_len), parent_idx);
            left_node.key_area_mut(old_left_len).write(parent_key);
            move_to_slice(
                right_node.key_area_mut(..right_len),
                left_node.key_area_mut(old_left_len + 1..new_left_len),
            );

            let parent_val = slice_remove(parent_node.val_area_mut(..old_parent_len), parent_idx);
            left_node.val_area_mut(old_left_len).write(parent_val);
            move_to_slice(
                right_node.val_area_mut(..right_len),
                left_node.val_area_mut(old_left_len + 1..new_left_len),
            );

            slice_remove(&mut parent_node.edge_area_mut(..old_parent_len + 1), parent_idx + 1);
            parent_node.correct_childrens_parent_links(parent_idx + 1..old_parent_len);
            *parent_node.len_mut() -= 1;

            if parent_node.height > 1 {
                let mut left_node = left_node.reborrow_mut().cast_to_internal_unchecked();
                let mut right_node = right_node.cast_to_internal_unchecked();
                move_to_slice(
                    right_node.edge_area_mut(..right_len + 1),
                    left_node.edge_area_mut(old_left_len + 1..new_left_len + 1),
                );

                left_node.correct_childrens_parent_links(old_left_len + 1..new_left_len + 1);

                alloc.deallocate(right_node.node.cast(), Layout::new::<InternalNode<K, V>>());
            } else {
                alloc.deallocate(right_node.node.cast(), Layout::new::<LeafNode<K, V>>());
            }
        }
        result(parent_node, left_node)
    }

    pub fn merge_tracking_parent<A: Allocator + Clone>(
        self,
        alloc: A,
    ) -> NodeRef<marker::Mut<'a>, K, V, marker::Internal> {
        self.do_merge(|parent, _child| parent, alloc)
    }

    pub fn merge_tracking_child<A: Allocator + Clone>(
        self,
        alloc: A,
    ) -> NodeRef<marker::Mut<'a>, K, V, marker::LeafOrInternal> {
        self.do_merge(|_parent, child| child, alloc)
    }

    #[rapx::verify]
    pub fn merge_tracking_child_edge<A: Allocator + Clone>(
        self,
        track_edge_idx: LeftOrRight<usize>,
        alloc: A,
    ) -> Handle<NodeRef<marker::Mut<'a>, K, V, marker::LeafOrInternal>, marker::Edge> {
        let old_left_len = self.left_child.len();
        let right_len = self.right_child.len();
        assert!(match track_edge_idx {
            LeftOrRight::Left(idx) => idx <= old_left_len,
            LeftOrRight::Right(idx) => idx <= right_len,
        });
        let child = self.merge_tracking_child(alloc);
        let new_idx = match track_edge_idx {
            LeftOrRight::Left(idx) => idx,
            LeftOrRight::Right(idx) => old_left_len + 1 + idx,
        };
        unsafe { Handle::new_edge(child, new_idx) }
    }

    #[rapx::verify]
    pub fn steal_left(
        mut self,
        track_right_edge_idx: usize,
    ) -> Handle<NodeRef<marker::Mut<'a>, K, V, marker::LeafOrInternal>, marker::Edge> {
        self.bulk_steal_left(1);
        unsafe { Handle::new_edge(self.right_child, 1 + track_right_edge_idx) }
    }

    #[rapx::verify]
    pub fn steal_right(
        mut self,
        track_left_edge_idx: usize,
    ) -> Handle<NodeRef<marker::Mut<'a>, K, V, marker::LeafOrInternal>, marker::Edge> {
        self.bulk_steal_right(1);
        unsafe { Handle::new_edge(self.left_child, track_left_edge_idx) }
    }

    #[rapx::verify]
    pub fn bulk_steal_left(&mut self, count: usize) {
        assert!(count > 0);
        unsafe {
            let left_node = &mut self.left_child;
            let old_left_len = left_node.len();
            let right_node = &mut self.right_child;
            let old_right_len = right_node.len();

            assert!(old_right_len + count <= CAPACITY);
            assert!(old_left_len >= count);

            let new_left_len = old_left_len - count;
            let new_right_len = old_right_len + count;
            *left_node.len_mut() = new_left_len as u16;
            *right_node.len_mut() = new_right_len as u16;

            {
                slice_shr(right_node.key_area_mut(..new_right_len), count);
                slice_shr(right_node.val_area_mut(..new_right_len), count);

                move_to_slice(
                    left_node.key_area_mut(new_left_len + 1..old_left_len),
                    right_node.key_area_mut(..count - 1),
                );
                move_to_slice(
                    left_node.val_area_mut(new_left_len + 1..old_left_len),
                    right_node.val_area_mut(..count - 1),
                );

                let k = left_node.key_area_mut(new_left_len).assume_init_read();
                let v = left_node.val_area_mut(new_left_len).assume_init_read();
                let (k, v) = self.parent.replace_kv(k, v);

                right_node.key_area_mut(count - 1).write(k);
                right_node.val_area_mut(count - 1).write(v);
            }

            match (left_node.reborrow_mut().force(), right_node.reborrow_mut().force()) {
                (ForceResult::Internal(mut left), ForceResult::Internal(mut right)) => {
                    slice_shr(right.edge_area_mut(..new_right_len + 1), count);

                    move_to_slice(
                        left.edge_area_mut(new_left_len + 1..old_left_len + 1),
                        right.edge_area_mut(..count),
                    );

                    right.correct_childrens_parent_links(0..new_right_len + 1);
                }
                (ForceResult::Leaf(_), ForceResult::Leaf(_)) => {}
                _ => unreachable!(),
            }
        }
    }

    #[rapx::verify]
    pub fn bulk_steal_right(&mut self, count: usize) {
        assert!(count > 0);
        unsafe {
            let left_node = &mut self.left_child;
            let old_left_len = left_node.len();
            let right_node = &mut self.right_child;
            let old_right_len = right_node.len();

            assert!(old_left_len + count <= CAPACITY);
            assert!(old_right_len >= count);

            let new_left_len = old_left_len + count;
            let new_right_len = old_right_len - count;
            *left_node.len_mut() = new_left_len as u16;
            *right_node.len_mut() = new_right_len as u16;

            {
                let k = right_node.key_area_mut(count - 1).assume_init_read();
                let v = right_node.val_area_mut(count - 1).assume_init_read();
                let (k, v) = self.parent.replace_kv(k, v);

                left_node.key_area_mut(old_left_len).write(k);
                left_node.val_area_mut(old_left_len).write(v);

                move_to_slice(
                    right_node.key_area_mut(..count - 1),
                    left_node.key_area_mut(old_left_len + 1..new_left_len),
                );
                move_to_slice(
                    right_node.val_area_mut(..count - 1),
                    left_node.val_area_mut(old_left_len + 1..new_left_len),
                );

                slice_shl(right_node.key_area_mut(..old_right_len), count);
                slice_shl(right_node.val_area_mut(..old_right_len), count);
            }

            match (left_node.reborrow_mut().force(), right_node.reborrow_mut().force()) {
                (ForceResult::Internal(mut left), ForceResult::Internal(mut right)) => {
                    move_to_slice(
                        right.edge_area_mut(..count),
                        left.edge_area_mut(old_left_len + 1..new_left_len + 1),
                    );

                    slice_shl(right.edge_area_mut(..old_right_len + 1), count);

                    left.correct_childrens_parent_links(old_left_len + 1..new_left_len + 1);
                    right.correct_childrens_parent_links(0..new_right_len + 1);
                }
                (ForceResult::Leaf(_), ForceResult::Leaf(_)) => {}
                _ => unreachable!(),
            }
        }
    }
}

impl<BorrowType, K, V> Handle<NodeRef<BorrowType, K, V, marker::Leaf>, marker::Edge> {
    pub fn forget_node_type(
        self,
    ) -> Handle<NodeRef<BorrowType, K, V, marker::LeafOrInternal>, marker::Edge> {
        unsafe { Handle::new_edge(self.node.forget_type(), self.idx) }
    }
}

impl<BorrowType, K, V> Handle<NodeRef<BorrowType, K, V, marker::Internal>, marker::Edge> {
    pub fn forget_node_type(
        self,
    ) -> Handle<NodeRef<BorrowType, K, V, marker::LeafOrInternal>, marker::Edge> {
        unsafe { Handle::new_edge(self.node.forget_type(), self.idx) }
    }
}

impl<BorrowType, K, V> Handle<NodeRef<BorrowType, K, V, marker::Leaf>, marker::KV> {
    pub fn forget_node_type(
        self,
    ) -> Handle<NodeRef<BorrowType, K, V, marker::LeafOrInternal>, marker::KV> {
        unsafe { Handle::new_kv(self.node.forget_type(), self.idx) }
    }
}

impl<BorrowType, K, V, Type> Handle<NodeRef<BorrowType, K, V, marker::LeafOrInternal>, Type> {
    pub fn force(
        self,
    ) -> ForceResult<
        Handle<NodeRef<BorrowType, K, V, marker::Leaf>, Type>,
        Handle<NodeRef<BorrowType, K, V, marker::Internal>, Type>,
    > {
        match self.node.force() {
            ForceResult::Leaf(node) => {
                ForceResult::Leaf(Handle { node, idx: self.idx, _marker: PhantomData })
            }
            ForceResult::Internal(node) => {
                ForceResult::Internal(Handle { node, idx: self.idx, _marker: PhantomData })
            }
        }
    }
}

impl<'a, K, V, Type> Handle<NodeRef<marker::Mut<'a>, K, V, marker::LeafOrInternal>, Type> {
    pub unsafe fn cast_to_leaf_unchecked(
        self,
    ) -> Handle<NodeRef<marker::Mut<'a>, K, V, marker::Leaf>, Type> {
        let node = unsafe { self.node.cast_to_leaf_unchecked() };
        Handle { node, idx: self.idx, _marker: PhantomData }
    }
}

impl<'a, K, V> Handle<NodeRef<marker::Mut<'a>, K, V, marker::LeafOrInternal>, marker::Edge> {
    pub fn move_suffix(
        &mut self,
        right: &mut NodeRef<marker::Mut<'a>, K, V, marker::LeafOrInternal>,
    ) {
        unsafe {
            let new_left_len = self.idx;
            let mut left_node = self.reborrow_mut().into_node();
            let old_left_len = left_node.len();

            let new_right_len = old_left_len - new_left_len;
            let mut right_node = right.reborrow_mut();

            assert!(right_node.len() == 0);
            assert!(left_node.height == right_node.height);

            if new_right_len > 0 {
                *left_node.len_mut() = new_left_len as u16;
                *right_node.len_mut() = new_right_len as u16;

                move_to_slice(
                    left_node.key_area_mut(new_left_len..old_left_len),
                    right_node.key_area_mut(..new_right_len),
                );
                move_to_slice(
                    left_node.val_area_mut(new_left_len..old_left_len),
                    right_node.val_area_mut(..new_right_len),
                );
                match (left_node.force(), right_node.force()) {
                    (ForceResult::Internal(mut left), ForceResult::Internal(mut right)) => {
                        move_to_slice(
                            left.edge_area_mut(new_left_len + 1..old_left_len + 1),
                            right.edge_area_mut(1..new_right_len + 1),
                        );
                        right.correct_childrens_parent_links(1..new_right_len + 1);
                    }
                    (ForceResult::Leaf(_), ForceResult::Leaf(_)) => {}
                    _ => unreachable!(),
                }
            }
        }
    }
}

pub enum ForceResult<Leaf, Internal> {
    Leaf(Leaf),
    Internal(Internal),
}

pub struct SplitResult<'a, K, V, NodeType> {
    pub left: NodeRef<marker::Mut<'a>, K, V, NodeType>,
    pub kv: (K, V),
    pub right: NodeRef<marker::Owned, K, V, NodeType>,
}

impl<'a, K, V> SplitResult<'a, K, V, marker::Leaf> {
    pub fn forget_node_type(self) -> SplitResult<'a, K, V, marker::LeafOrInternal> {
        SplitResult {
            left: self.left.forget_type(),
            kv: self.kv,
            right: self.right.forget_type(),
        }
    }
}

impl<'a, K, V> SplitResult<'a, K, V, marker::Internal> {
    pub fn forget_node_type(self) -> SplitResult<'a, K, V, marker::LeafOrInternal> {
        SplitResult {
            left: self.left.forget_type(),
            kv: self.kv,
            right: self.right.forget_type(),
        }
    }
}

pub mod marker {
    use std::marker::PhantomData;

    pub enum Leaf {}
    pub enum Internal {}
    pub enum LeafOrInternal {}

    pub enum Owned {}
    pub enum Dying {}
    pub enum DormantMut {}
    pub struct Immut<'a>(PhantomData<&'a ()>);
    pub struct Mut<'a>(PhantomData<&'a mut ()>);
    pub struct ValMut<'a>(PhantomData<&'a mut ()>);

    pub trait BorrowType {
        const TRAVERSAL_PERMIT: bool = true;
    }
    impl BorrowType for Owned {
        const TRAVERSAL_PERMIT: bool = false;
    }
    impl BorrowType for Dying {}
    impl<'a> BorrowType for Immut<'a> {}
    impl<'a> BorrowType for Mut<'a> {}
    impl<'a> BorrowType for ValMut<'a> {}
    impl BorrowType for DormantMut {}

    pub enum KV {}
    pub enum Edge {}
}

#[rapx::requires(ValidNum(len > idx))]
unsafe fn slice_insert<T>(slice: &mut [MaybeUninit<T>], idx: usize, val: T) {
    unsafe {
        let len = slice.len();
        debug_assert!(len > idx);
        let slice_ptr = slice.as_mut_ptr();
        if len > idx + 1 {
            ptr::copy(slice_ptr.add(idx), slice_ptr.add(idx + 1), len - idx - 1);
        }
        (*slice_ptr.add(idx)).write(val);
    }
}

#[rapx::requires(ValidNum(idx < len))]
unsafe fn slice_remove<T>(slice: &mut [MaybeUninit<T>], idx: usize) -> T {
    unsafe {
        let len = slice.len();
        debug_assert!(idx < len);
        let slice_ptr = slice.as_mut_ptr();
        let ret = (*slice_ptr.add(idx)).assume_init_read();
        ptr::copy(slice_ptr.add(idx + 1), slice_ptr.add(idx), len - idx - 1);
        ret
    }
}

#[rapx::requires(ValidNum(len >= distance))]
unsafe fn slice_shl<T>(slice: &mut [MaybeUninit<T>], distance: usize) {
    unsafe {
        let slice_ptr = slice.as_mut_ptr();
        ptr::copy(slice_ptr.add(distance), slice_ptr, slice.len() - distance);
    }
}

#[rapx::requires(ValidNum(len >= distance))]
unsafe fn slice_shr<T>(slice: &mut [MaybeUninit<T>], distance: usize) {
    unsafe {
        let slice_ptr = slice.as_mut_ptr();
        ptr::copy(slice_ptr, slice_ptr.add(distance), slice.len() - distance);
    }
}

fn move_to_slice<T>(src: &mut [MaybeUninit<T>], dst: &mut [MaybeUninit<T>]) {
    assert!(src.len() == dst.len());
    unsafe {
        ptr::copy_nonoverlapping(src.as_ptr(), dst.as_mut_ptr(), src.len());
    }
}

fn take_mut<T>(t: &mut T, f: impl FnOnce(T) -> T) {
    let ptr = &mut *t;
    unsafe {
        ptr::write(ptr, f(ptr::read(ptr)));
    }
}
