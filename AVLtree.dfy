include "AVLnode.dfy"

class AVLtree {
    ghost var objects: set<object> // tree and nodes

    var root: AVLnode?

    constructor () 
        ensures objects == {this}
        ensures root == null
        ensures valid()
        ensures balanced()
    {
        objects := {this};
        root := null;
    }

    // need for balance()
    predicate valid()
        reads this, objects
    {
        root != null ==> (root in objects && root.nodes < objects)
    }

    predicate balanced()
        reads this, objects
    {
        valid() &&
        root != null ==> root.balanced()
    }

    method nodeHeight(avlNode: AVLnode?) returns (height: int) 
    {
        if avlNode == null {
            height := -1;
        } else {
            height := avlNode.height;
        }
    }

    method heightDiff(avlNode: AVLnode?) returns (diff: int) 
    {
        if avlNode == null {
            diff := 0;
        } else {
            var leftHeight: int := nodeHeight(avlNode.left);
            var rightHeight: int := nodeHeight(avlNode.right);
            diff := leftHeight - rightHeight;
        }
    }

    method findNode(node: AVLnode, queryNum: int) returns (found_node: AVLnode?)
        requires node.valid()
        ensures found_node != null ==> found_node in node.nodes
        // Why is this not working?
        // ensures found_node != null ==> found_node.key == queryNum
        decreases node.nodes 
    {
        var temp: AVLnode? := node;
        if temp != null
        {
            if (temp.left != null && queryNum < node.key) {
                temp := findNode(temp.left, queryNum);
            }
            else if (temp.right != null && queryNum > node.key) {
                temp := findNode(temp.right, queryNum);
            }
        }

        return temp;
    }


    // Task 1
    /*
    method leftRotate()
    method rightRotate()
    method leftRightRotate()
    method rightLeftRotate()
    method minNode()
    method findNode()

    // for debug
    method printAVLtree()
        requires balanced()
    {
        
    }
    
    // Task 2
    method insert(key: int) 
        modifies this
    {
    
    }

    method delete(key: int) 
        modifies this
    {
    
    }
    */
}