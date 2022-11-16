include "AVLnode.dfy"

class AVLtree {
    var root: AVLnode?

    constructor() {
        root := null;
    }

    predicate balanced()
        reads this, this.root
    {
        root != null ==> root.balanced()
    }

    // Step 1
    // Done
    method nodeHeight(avlNode: AVLnode?) returns (height: int) 
    {
        if (avlNode == null) {
            height := -1;
        } else {
            height := avlNode.height;
        }
    }

    // Done
    method heightDiff(avlNode: AVLnode?) returns (diff: int) 
    {
        if (avlNode == null) {
            diff := 0;
        } else {
            var leftHeight: int := nodeHeight(avlNode.left);
            var rightHeight: int := nodeHeight(avlNode.right);
            diff := leftHeight - rightHeight;
        }
    }

    // need to complete
    method leftRotate()
    method rightRotate()
    method leftRightRotate()
    method rightLeftRotate()
    method minNode()

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