#include "bstree.h"
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>

#include "queue.h"


/*------------------------  BSTreeType  -----------------------------*/

struct _bstree {
    BinarySearchTree* parent;
    BinarySearchTree* left;
    BinarySearchTree* right;
    int key;
};

/*------------------------  BaseBSTree  -----------------------------*/

BinarySearchTree* bstree_create(void) {
    return NULL;
}

/* This constructor is private so that we can maintain the oredring invariant on
 * nodes. The only way to add nodes to the tree is with the bstree_add function
 * that ensures the invariant.
 */
BinarySearchTree* bstree_cons(BinarySearchTree* left, BinarySearchTree* right, int key) {
    BinarySearchTree* t = malloc(sizeof(struct _bstree));
    t->parent = NULL;
    t->left = left;
    t->right = right;
    if (t->left != NULL)
        t->left->parent = t;
    if (t->right != NULL)
        t->right->parent = t;
    t->key = key;
    return t;
}

void freenode(const BinarySearchTree* t, void* n) {
    (void)n;
    free((BinarySearchTree*)t);
}

void bstree_delete(ptrBinarySearchTree* t) {
    bstree_depth_postfix(*t, freenode, NULL);
    *t=NULL;
}

bool bstree_empty(const BinarySearchTree* t) {
    return t == NULL;
}

int bstree_key(const BinarySearchTree* t) {
    assert(!bstree_empty(t));
    return t->key;
}

BinarySearchTree* bstree_left(const BinarySearchTree* t) {
    assert(!bstree_empty(t));
    return t->left;
}

BinarySearchTree* bstree_right(const BinarySearchTree* t) {
    assert(!bstree_empty(t));
    return t->right;
}

BinarySearchTree* bstree_parent(const BinarySearchTree* t) {
    assert(!bstree_empty(t));
    return t->parent;
}

/*------------------------  BSTreeDictionary  -----------------------------*/

/* Obligation de passer l'arbre par référence pour pouvoir le modifier */
void bstree_add(ptrBinarySearchTree* t, int v) {
	if (*t == NULL){
        *t = bstree_cons(NULL, NULL, v);
    }else{
        BinarySearchTree* bn_tree = *t;
        if (v > bn_tree->key){
            bstree_add(&bn_tree->right, v);
            bn_tree->right->parent = *t;
        }else{
            bstree_add(&bn_tree->left, v);
            bn_tree->left->parent = *t;
        } 
    }
}

const BinarySearchTree* bstree_search(const BinarySearchTree* t, int v) {
    if (t != NULL){
        int key = t->key;
        if (v < key){
            return bstree_search(t->left, v);
        }
        else if (v > key){
            return bstree_search(t->right, v);
        }
        else{
            return t;
        }
    }
    return NULL;
}

const BinarySearchTree* bigger_node(const BinarySearchTree* node1, const BinarySearchTree* node2){
    if (node1&&node2){
        int key1 = node1->key;
        int key2 = node2->key;
        return (key1>key2)?node1:node2;
    }else{
        return (node1)?node1:node2;
    }    
}

const BinarySearchTree* smaller_node(const BinarySearchTree* node1, const BinarySearchTree* node2){
    if (node1&&node2){
        int key1 = node1->key;
        int key2 = node2->key;
        return (key1<key2)?node1:node2;
    }else{
        return (node1)?node1:node2;
    }    
}

const BinarySearchTree* bstree_successor(const BinarySearchTree* x) {
    assert(!bstree_empty(x));
    // Find upper successor
    const BinarySearchTree* successor_upper = NULL;
    const BinarySearchTree* successor_lower = NULL;
    if (x->parent!=NULL){
        // if node is the left child of its parent
        const BinarySearchTree* parent = x->parent;
        if (parent->left!=NULL&&parent->left ==x){
            successor_upper = x->parent;
        }else if(parent->parent!=NULL&&(parent->parent)->right == parent){
            successor_upper = parent->parent;
            }
        }
    // Find lower successor
    if (x->right != NULL){
        successor_lower = x->right;
        while (successor_lower->left != NULL){
            successor_lower = successor_lower->left;
        }
    }
    return smaller_node(successor_lower, successor_upper);
}


const BinarySearchTree* bstree_predecessor(const BinarySearchTree* x) {
    assert(!bstree_empty(x));
    // Find upper predecessor
    const BinarySearchTree* predecessor_upper = NULL;
    const BinarySearchTree* predecessor_lower = NULL;
    if (x->parent!=NULL){
        // if node is right child
        const BinarySearchTree* parent = x->parent;
        if (parent->left!=NULL&&parent->left ==x){
            if(parent->parent!=NULL&&(parent->parent)->right == parent){
                predecessor_upper = parent->parent;
            }
        }
        if (parent->right!=NULL&&parent->right == x){
            predecessor_upper = parent;
        }
        
    }
    // Find lower predecessor
    if (x->left != NULL){
        predecessor_lower = x->left;
        while (predecessor_lower->right != NULL){
            predecessor_lower = predecessor_lower->right;
        }
    }
    return bigger_node(predecessor_lower, predecessor_upper);
}


void bstree_swap_nodes(ptrBinarySearchTree* tree, ptrBinarySearchTree from, ptrBinarySearchTree to) {
    assert(!bstree_empty(*tree) && !bstree_empty(from) && !bstree_empty(to));
    (void)tree; (void)from; (void)to;
}

// t -> the tree to remove from, current -> the node to remove
void bstree_remove_node(ptrBinarySearchTree* t, ptrBinarySearchTree current) {
    assert(!bstree_empty(*t) && !bstree_empty(current));
    (void)t; (void)current;
}

void bstree_remove(ptrBinarySearchTree* t, int v) {
    (void)t; (void)v;
}

/*------------------------  BSTreeVisitors  -----------------------------*/

void bstree_depth_prefix(const BinarySearchTree* t, OperateFunctor f, void* environment) {
    if (t!=NULL)
    {
        printf("%i ", t->key);
        bstree_depth_prefix(t->left, f, environment);
        bstree_depth_prefix(t->right, f, environment);
    }
    
}

void bstree_depth_infix(const BinarySearchTree* t, OperateFunctor f, void* environment) {
    if (t!=NULL)
    {
        
        bstree_depth_infix(t->left, f, environment);
        printf("%i ", t->key);
        bstree_depth_infix(t->right, f, environment);
        
    }
}

void bstree_depth_postfix(const BinarySearchTree* t, OperateFunctor f, void* environment) {
    if (t != NULL)
    {
        bstree_depth_postfix(t->left, f, environment);
        bstree_depth_postfix(t->right, f, environment);
        printf("%i ", t->key);
    }
    
}

void bstree_iterative_breadth(const BinarySearchTree* t, OperateFunctor f, void* environment) {
    Queue* q = create_queue();
    if (t != NULL){
        queue_push(q, t);
    }
    while (!queue_empty(q)){
        const BinarySearchTree* node = queue_top(q);
        f(node, environment);
        queue_pop(q);
        if (node->left != NULL){
            queue_push(q, node->left);
        }
        if (node->right != NULL){
            queue_push(q, node->right);
        }
    }
}

void bstree_iterative_depth_infix(const BinarySearchTree* t, OperateFunctor f, void* environment) {
    (void)t; (void) f; (void)environment;
    
}

/*------------------------  BSTreeIterator  -----------------------------*/

struct _BSTreeIterator {
    /* the collection the iterator is attached to */
    const BinarySearchTree* collection;
    /* the first element according to the iterator direction */
    const BinarySearchTree* (*begin)(const BinarySearchTree* );
    /* the current element pointed by the iterator */
    const BinarySearchTree* current;
    /* function that goes to the next element according to the iterator direction */
    const BinarySearchTree* (*next)(const BinarySearchTree* );
};

/* minimum element of the collection */
const BinarySearchTree* goto_min(const BinarySearchTree* e) {
	(void)e;
	return NULL;
}

/* maximum element of the collection */
const BinarySearchTree* goto_max(const BinarySearchTree* e) {
	(void)e;
	return NULL;
}

/* constructor */
BSTreeIterator* bstree_iterator_create(const BinarySearchTree* collection, IteratorDirection direction) {
	(void)collection; (void)direction;
	return NULL;
}

/* destructor */
void bstree_iterator_delete(ptrBSTreeIterator* i) {
    free(*i);
    *i = NULL;
}

BSTreeIterator* bstree_iterator_begin(BSTreeIterator* i) {
    i->current = i->begin(i->collection);
    return i;
}

bool bstree_iterator_end(const BSTreeIterator* i) {
    return i->current == NULL;
}

BSTreeIterator* bstree_iterator_next(BSTreeIterator* i) {
    i->current = i->next(i->current);
    return i;
}

const BinarySearchTree* bstree_iterator_value(const BSTreeIterator* i) {
    return i->current;
}

