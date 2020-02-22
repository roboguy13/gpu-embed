# Possible Future Work and Research Ideas

## Futures and promises for parallelism in the EDSL

Consider the following code:

    data Future a = Future

    data Tree a = Leaf a | Node (Tree a) (Tree a)

    type FutureTree a = Tree (Future a)

    data Child = LeftChild | RightChild
    type TreePath = [Child]

    parMapTree :: Tree a -> Expr (a -> TreePath -> b) -> Tree b

Consider an implementation of `parMapTree` which sends the computation over to a
GPU.

Calling `parMapTree` with a `FutureTree` allows us to generate the leaf values
of a tree in parallel when we know (and *only* know) the structure of the tree
before the parallel computation gets sent to the GPU.

The entire structure of the `FutureTree` is known before `parMapTree` is
executed. This means the entire tree structure is known before the computation
is sent to the GPU. Additionally, for this particular type, the `Expr`
representation of a `TreePath`, from the perspective of the GPU, could be a more
compressed efficient form (such as a bitstring where a 0 indicates the left
child and a 1 indicates a right child).

Each leaf value could be computed by the GPU in parallel and then put into the
appropriate places in the `Tree` (whose shape has already been fixed). Putting
the values into the tree could possibly happen either on the GPU or the CPU.

Now consider the following function which, again, could be done in parallel on a
GPU:

    parTreeReduce :: Tree a -> Expr (a -> a -> a) -> a

This could be composed with the previous map function to obtain this tree
map/reduce:

    parTreeMapReduce :: Tree a -> Expr (a -> TreePath -> b) -> Expr (a -> a -> a) -> a
    parTreeMapReduce ft map_fn reduce_fn = parTreeReduce (parMapTree ft map_fn) reduce_fn

An unfold tree operation could also be implemented and used in compositions with
the previous functions.

