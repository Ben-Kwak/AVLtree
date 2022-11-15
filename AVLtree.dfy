include "AVLnode.dfy"

class AVLtree {
    var root: AVLnode?

    constructor() {
        root := null;
    }

    predicate balanced()
        reads this
    {
        root != null ==> root.balanced()
    }

    // Step 1
    // need to complete
    method nodeHeight(avlNode: AVLnode?) returns (height: int) 
    {
        return 0;
    }

    // need to complete
    method heightDiff(avlNode: AVLnode?) returns (diff: int) 
    {
        return 0;
    }

    // need to complete
    method leftRotate()
    method rightRotate()
    method leftRightRotate()
    method rightLeftRotate()

    // Step 2
    
    // need to complete
    method insert(key: int) 
        modifies this
    {
    
    }

    // need to complete
    method delete(key: int) 
        modifies this
    {
    
    }

    // for debug
    method printAVLtree()
        requires balanced()
    {
        
    }
}