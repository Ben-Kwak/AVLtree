class AVLnode
{
    ghost var nodes: set<AVLnode> 
    ghost var keys: set<int>

    var key: int
    var left: AVLnode?
    var right: AVLnode?
    var height: int

    constructor (k: int) 
        ensures nodes == {this}
        ensures keys == {k}
        ensures key == key
        ensures left == null
        ensures right == null
        ensures height == 0
        ensures valid()
        ensures balanced()
    {
        nodes := {this};
        keys := {k};
        key := k;
        left := null;
        right := null;
        height := 0;
    }

    // need for balance()
    predicate valid()
        reads this, nodes
    {
        this in nodes &&
        (left != null ==> left in nodes &&
                        this !in left.nodes &&
                        left.nodes < nodes && 
                        forall i :: i in left.keys ==> i < key &&
                        left.valid()) &&
        (right != null ==> right in nodes &&
                        this !in right.nodes &&
                        right.nodes < nodes && 
                        forall i :: i in right.keys ==> i > key &&
                        right.valid()) 
    }

    predicate balanced() 
        reads this, nodes
    {
        valid() &&
        (left == null && right != null) ==> (right.height == 0 && right.balanced()) &&
        (left != null && right == null) ==> (left.height == 0  && left.balanced()) &&
        (left != null && right != null && left.height >= right.height) ==> (left.height - right.height <= 1 && 
                                                                            left.balanced() && right.balanced()) &&
        (left != null && right != null && left.height < right.height) ==> (right.height - left.height <= 1 && 
                                                                            left.balanced() && right.balanced())
    }
}