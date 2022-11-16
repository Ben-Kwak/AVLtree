include "AVLnode.dfy"
include "AVLtree.dfy"

method Test() {
    var avlTree: AVLtree := new AVLtree();
    var avlNode: AVLnode := new AVLnode(3);
    assert(avlNode.balanced());
}