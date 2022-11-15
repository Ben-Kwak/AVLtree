method max(x: int, y: int) returns (z: int)
    ensures x > y ==> z == x
    ensures x < y ==> z == y
{
    if x > y {
        return x;
    } else {
        return y;
    }
}

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

    predicate balanced() // need to complete
}