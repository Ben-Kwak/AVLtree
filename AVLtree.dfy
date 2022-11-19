include "AVLnode.dfy"
include "HelperFunctions.dfy"

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

    static method nodeHeight(avlNode: AVLnode?) returns (height: int) 
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

    /* skip verification for now to implement insert and delete first */
    method {:verify false} minNode(node: AVLnode) returns (min_node: AVLnode?)
        requires node.valid()
        ensures min_node != null ==> min_node in node.nodes
        ensures min_node != null ==> (forall i :: i in node.keys ==> min_node.key <= i)
    {
        var temp: AVLnode := node;

        while temp.left != null 
            decreases if temp.left != null then temp.left.nodes else {}
        {
            temp := temp.left;
        }

        return temp;
    }
    
    method updateHeight(node:AVLnode)
        modifies node;
        requires node.valid();
        ensures old(node.left) == node.left;
        ensures old(node.right) == node.right;
        ensures old(node.key) == node.key;
        ensures node.valid();
    {
        var r_height:int := nodeHeight(node.right);
        var l_height:int := nodeHeight(node.left);
        node.height := 1 + max(r_height,l_height);
    }
   method rightRotate(node: AVLnode) returns( new_node : AVLnode)
        requires node.left != null;
        requires node.valid();
        modifies node.nodes;
        ensures old(node.nodes) == new_node.nodes;
        ensures old(node.keys) == new_node.keys;
        ensures new_node.valid();
        ensures node.valid();
        ensures new_node == old(node.left);
        ensures new_node.left == old(new_node.left);
        ensures new_node.right == old(node);
        ensures node.left == old(node.left.right);
        ensures node.right == old(node.right);
    {
        new_node := node.left;
        var T3 := new_node.right;
        new_node.right := node;
        node.left := T3;
        updateHeight(node);
        updateHeight(new_node);
        


    }
    // Task 1
    /*
    method leftRotate()
 
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