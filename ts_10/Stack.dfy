/* SECTION: Stack */
class Stack<Data> {
    ghost var Repr  : set<object>
    ghost var stack : seq<Data>
    var       head  : Node?<Data>

    ghost predicate Valid()
        reads   this, Repr
        ensures Valid() ==> this in Repr
    {
        // .; Obligatory
        this in Repr                  // Obligatory
        && (head != null ==> 
                head in Repr          // obligatory
                && head.Repr <= Repr  // obligatory
                && head.Valid()       // obligatory
                && this !in head.Repr // obligatory
        )
        // .; Abstraction relation
        && (head == null ==>
                stack == []
        )
        && (head != null ==>
                stack == [head.data] + head.later
        )
    }
    
    constructor()
        ensures Valid()
        ensures fresh(Repr)
        ensures stack == []
    {
        head  := null;
        stack := [];
        Repr  := {this};
    }
    
    method Push(data : Data)
        requires Valid()
        modifies Repr
        ensures  Valid()
        ensures  fresh(Repr - old(Repr))
        ensures  stack == [data] + old(stack)
    {
        // Make new data
        var newNode := new Node<Data>(data);
        // Chuck it on
        newNode.SetNext(head);
        head := newNode;
        // Update abstract state
        stack := [data] + stack;
        Repr  := Repr + head.Repr;
    }
    
    method Pop() returns (data : Data)
        requires Valid()
        requires stack != []
        modifies Repr
        ensures  Valid()
        ensures  fresh(Repr - old(Repr))
        ensures  [data] + stack == old(stack)
    {
        // Grab data
        data := head.GetValue();
        // Trash head
        assert this !in head.Repr;
        var head' := head.GetNext();
        assert (head' != null ==> head'.Valid());
        assert (head' != null ==> this !in head'.Repr); // ATTENTION: I don't understand dude...
        head := head';
        assert (head' != null ==> this !in head.Repr);
        assert (head == head');
        assert (head' != null ==> head'.Valid()); // This might be aliasing...
        assert (head != null ==> head'.Valid() && head.Valid());
        // Update abstract state
        stack := stack[1..];
        if head != null {
            Repr := Repr + head.Repr;
        }
        assert (head != null ==> head.Valid());
    }
}


/* SECTION: Node */
class Node<Data> {
    ghost var Repr  : set<object>
    ghost var later : seq<Data>
    ghost var data  : Data
    var       next  : Node?<Data>
    var       data' : Data

    ghost predicate Valid()
        reads   this, Repr
        ensures Valid() ==> this in Repr
    {
        // .; obligatory
        this in Repr
        && (next != null ==> 
                next in Repr
                && next.Repr <= Repr
                && this !in next.Repr
        )
        // .; Abstraction relation
        && (next == null ==> later == [])
        && (next != null ==> later == [next.data] + next.later)
    }
    
    constructor(data : Data)
        ensures Valid()
        ensures fresh(Repr)
        ensures later == []
        ensures this.data == data
    
    method SetNext(next' : Node?<Data>)
        requires Valid()
        modifies Repr
        ensures  Valid()
        ensures  fresh(Repr - old(Repr))
        ensures  next' == null ==> later == []
        ensures  next' != null ==> later == [next'.data] + next'.later
        ensures  data == old(data)
    
    function GetNext() : Node?<Data>
        requires Valid()
        reads    Repr
        ensures  Valid()
        ensures  GetNext() == null ==>
                    later == []
        ensures  GetNext() != null ==>
                    later != []
                    && [GetNext().data] + GetNext().later == later
                    && GetNext().Valid()
    
    function GetValue() : Data
        requires Valid()
        reads    Repr
        ensures  Valid()
        ensures  GetValue() == data
}