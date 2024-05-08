/* SECTION: helpers */
datatype Maybe<T> = Nothing | Just(T)

// ghost predicate Less(a : set<int>, b : set<int>) {
//     forall x, y :: x in a && y in b ==> x < y
// }

ghost function Union<Data> (m : map<int, Data>, node : Node?<Data>) : map<int, Data>
    reads node
{
    if node == null
    then    m
    else    map k | k in (m.Keys + node.M.Keys) :: 
                    if k in m.Keys
                    then    m[k]
                    else    node.M[k]
}


/* SECTION: Map specification */
class MapSpec<Data> {
    ghost var M    : map<int, Data>
    ghost var Repr : set<object>

    ghost predicate Valid()
        reads   this, Repr
        ensures Valid() ==> this in Repr
    
    constructor()
        ensures Valid()
        ensures fresh(Repr)
        ensures M == map[]
    
    function Lookup(key : int) : Maybe<Data>
        requires Valid()
        reads    Repr
        ensures  key  in M.Keys ==> Lookup(key) == Just(M[key])
        ensures  key !in M.Keys ==> Lookup(key) == Nothing
    
    method Add(key : int, value : Data)
        requires Valid()
        modifies Repr
        ensures  Valid()
        ensures  fresh(Repr - old(Repr))
        ensures  M == old(M)[key := value]
}

/* SECTION: Map implementation */
/* IDEA:
    Ordered bin search tree.
   Each Map<Data> IS a Node<Data> which CONSISTS OF:
        key   here
        value here
        left  subtree : Node?<Data> CONSISTS OF:
            keys < root.key
        right subtree : Node?<Data> CONSISTS OF:
            keys > root.key
*/

class Map<Data> {
    ghost var M    : map<int, Data>
    ghost var Repr : set<object>
    var       root : Node?<Data>

    ghost predicate Valid()
        reads   this, Repr
        ensures Valid() ==> this in Repr
    {
        // .; Repr juggling
        this in Repr
        && (root != null ==>
                root in Repr
                && root.Repr <= Repr
                && root.Valid()
        )
        // .; Abstraction relation
        && (root != null ==>
                M == root.M
        )
        && (root == null ==>
                M == map[]
        )
    }
    
    constructor()
        ensures Valid()
        ensures fresh(Repr)
        ensures M == map[]
    {
        root := null;
        M    := map[];
        Repr := {this};
    }
    
    function Lookup(key : int) : Maybe<Data>
        requires Valid()
        reads    Repr
        ensures  key  in M.Keys ==> Lookup(key) == Just(M[key])
        ensures  key !in M.Keys ==> Lookup(key) == Nothing
    {
        if root == null
        then    Nothing
        else    root.Lookup(key)
    }
    
    method Add(key : int, value : Data)
        requires Valid()
        modifies Repr
        ensures  Valid()
        ensures  fresh(Repr - old(Repr))
        ensures  M == old(M)[key := value]
    // {
    //     if root == null {
    //         root := new Node<Data>(key, value);
    //         assert root != null;
    //     } else {
    //         assert root != null;
    //         root.Add(key, value);
    //         assert root != null;  // [2.] seriously?
    //     }
    //     assert root != null;
    //     M := M[key := value];
    //     Repr := Repr + root.Repr;
    // }

    method GetIterator() returns (i : Iterator<Data>)
        requires Valid()
        ensures  fresh(i.Repr - Repr)
        ensures  i.RemainingKeys == M.Keys
        ensures  i.Valid()
        ensures  i.m == this
    {
        i := new Iterator<Data>(this);
    }
}

class Node<Data> {
    // Abstract state
    ghost var M     : map<int, Data>
    ghost var Repr  : set<object>
    // Concrete state
    var       key   : int
    var       value : Data
    var       left  : Node?<Data>
    var       right : Node?<Data>

    ghost predicate Valid()
        reads     this, Repr
        ensures   Valid() ==> this in Repr
        ensures   Valid() ==> |M| > 0 // [1.] Nodes store maps that have >> key := value <<
        decreases Repr
    {
        // .; Repr juggling
        // Repr contents
           this in Repr
        && (left  != null ==> left  in Repr)
        && (right != null ==> right in Repr)
        && (left  != null ==>  left.Repr <= Repr && this !in  left.Repr)
        && (right != null ==> right.Repr <= Repr && this !in right.Repr)
        && (left  != null ==>  left.Valid())
        && (right != null ==> right.Valid())
        // No aliasing
        && (left != null && right != null  ==>
                left.Repr !! right.Repr
        )
        // .; Abstraction relation
        // All stuff in the left map is left of the key
        && (left  != null ==>
            forall  leftKey ::  leftKey in  left.M.Keys ==>
                leftKey < key
        )
        // All stuff in the right map is right of the key
        && (right != null ==>
            forall rightKey :: rightKey in right.M ==>
                key < rightKey
        )
        // M is the union of maps
        && M == Union(Union(map[key := value], left), right)
    }
    
    constructor(key : int, value : Data)
        ensures Valid()
        ensures fresh(Repr)
        ensures M == map[key := value]
    {
        this.key   := key;
        this.value := value;
        left  := null;
        right := null;
        M := map[key := value];
        Repr := {this};
    }
    
    function Lookup(key : int) : Maybe<Data>
        requires Valid()
        reads    Repr
        ensures  key  in M.Keys ==> Lookup(key) == Just(M[key])
        ensures  key !in M.Keys ==> Lookup(key) == Nothing
    {
        if key == this.key                  // If the key is here,
        then    Just(this.value)            // then yield it.
        else    if key < this.key           // If the key is to the left...
                then    if left  != null    // ...then find it on the left...
                        then    left.Lookup(key)
                        else    Nothing
                else    if right != null    // ...otherwise, find it on the right
                        then    right.Lookup(key)
                        else    Nothing
    }
    
    method Add(key : int, value : Data)
        requires  Valid()
        modifies  Repr
        ensures   Valid()
        ensures   fresh(Repr - old(Repr))
        ensures   M == old(M)[key := value]
        ensures   this != null // [2.] ????
        decreases Repr
    // {
    //     // Update concrete state
    //     if key == this.key {
    //         this.value := value;
    //     } else if key < this.key {
    //         if left == null {  // Initialise left if necessary
    //             left := new Node<Data>(key, value);
    //         } else {           // Otherwise, just add in the left
    //             left.Add(key, value);
    //         }
    //         Repr := Repr + left.Repr; // Repr juggling
    //     } else { // this.key < key
    //         if right == null { // Initialise right if necessary
    //             right := new Node<Data>(key, value);
    //         } else {           // Otherwise, just add in the right
    //             right.Add(key, value);
    //         }
    //         Repr := Repr + right.Repr; // Repr juggling
    //     }

    //     // Keep track of abstract state
    //     M := M[key := value];
    //     // assert M == old(M)[key := value];
    // }
}

/* SECTION: Iterator */
class Iterator<Data> {
    var       m             : Map<Data>
    ghost var RemainingKeys : set<int>
    ghost var Repr          : set<object>

    ghost predicate Valid()
        ensures Valid() ==>
                    this in Repr
                    && m.Valid()
                    && RemainingKeys <= m.M.Keys
    
    constructor (m : Map)
        ensures Valid()
        ensures fresh(Repr)
        ensures m.Valid()
        ensures this.m == m
        ensures RemainingKeys == m.M.Keys
    
    method GetNext() returns (r : Maybe<(int, Data)>)
        requires Valid()
        modifies Repr - m.Repr // [3.]
        ensures  Valid()
        ensures  fresh(Repr - old(Repr))
        ensures  match r
                    case Nothing      =>
                        old(RemainingKeys) == {}
                        && RemainingKeys == old(RemainingKeys)
                    case Just((k, v)) => 
                        k in old(RemainingKeys)
                        && m.M[k] == v // BUG: Why??
                        && RemainingKeys == old(RemainingKeys) - {k}
        // ensures  RemainingKeys <= old(RemainingKeys)
}