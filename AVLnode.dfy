class AVLnode
{
    var node_set: set<AVLnode> 
    var key_set: set<int>

    var key: int
    var left: AVLnode?
    var right: AVLnode?
    var height: int

    constructor (k: int) 
        ensures node_set == {this}
        ensures key_set == {k}
        ensures key == key
        ensures left == null
        ensures right == null
        ensures height == 0
    {
        node_set := {this};
        key_set := {k};
        key := k;
        left := null;
        right := null;
        height := 0;
    }

    predicate balanced() 
        reads this, this.left, this.right
    {
        (left == null && right != null) ==> right.height == 0 &&
        (left != null && right == null) ==> left.height == 0  &&
        (left != null && right != null && left.height >= right.height) ==> left.height - right.height <= 1 &&
        (left != null && right != null && left.height < right.height) ==> right.height - left.height <= 1 &&
        (left != null) ==> left.balanced() && (right != null) ==> right.balanced() 
    }
}