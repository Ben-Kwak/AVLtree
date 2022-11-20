include "HelperFunctions.dfy"

class AVLnode {
	ghost var nodes: set<AVLnode> 
    ghost var keys: set<int>

    var key: int
    var left: AVLnode?
    var right: AVLnode?
    var height: int

    constructor (k: int) 
        ensures valid()
        ensures balanced()
        ensures keys == {k}
        ensures nodes == {this};
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
      					left.nodes <= nodes &&
      					left.valid() &&
      					(forall i :: i in left.keys ==> i < key)) &&
    	(right != null ==> right in nodes &&
						this !in right.nodes &&
      					right.nodes <= nodes && 
      					right.valid() &&
      					(forall i :: i in right.keys ==> key < i)) &&
        (left == null && right == null ==> keys == {key}) &&
        (left != null && right == null ==> keys == left.keys + {key}) &&
        (left == null && right != null ==> keys == {key} + right.keys) &&
        (left != null && right != null ==> left.nodes !! right.nodes && keys == left.keys + {key} + right.keys)
  	}
  // predicate Height_Valid() 
  //   reads this, nodes 
  // {
  //   valid() &&
  //   (left == null && right == null) ==> height == -1 &&
  //   (left != null && right == null) ==> height == left.height + 1 &&
  //   (left == null && right != null) ==> height == right.height + 1 &&
  //   (left != null && right != null) ==> height == max(left.height, right.height) + 1 &&
  //   (right != null) ==> right.Height_Valid() &&
  //   (left != null) ==> left.Height_Valid()
  // }
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