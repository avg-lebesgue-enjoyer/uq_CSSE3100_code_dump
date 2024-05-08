/* SECTION: Class specification */
class BoundedQueueSpec<T> {
    ghost var   Elements      : seq<T>
    ghost const maxLength     : nat
    ghost var   currentLength : nat
    ghost var   Repr          : set<object>

    ghost predicate Valid()
        reads   this, Repr
        ensures Valid() ==> this in Repr
        ensures Valid() ==> |Elements| <= maxLength
        ensures Valid() ==> |Elements| == currentLength
    
    constructor(maxLength' : nat)
        requires maxLength' > 0
        ensures  fresh(Repr)
        ensures  Valid()
        ensures  Elements == []
        ensures  maxLength == maxLength'
        ensures  currentLength == 0
    
    method enqueue(value : T)
        requires Valid()
        requires currentLength != maxLength
        modifies Repr
        ensures  Valid()
        ensures  fresh(Repr - old(Repr))
        ensures  maxLength     == old(maxLength)
        ensures  currentLength == old(currentLength + 1)
        ensures  Elements      == [value] + old(Elements)
    
    method dequeue() returns (result : T)
        requires Valid()
        requires currentLength != 0
        modifies Repr
        ensures  Valid()
        ensures  maxLength           == old(maxLength)
        ensures  currentLength       == old(currentLength) - 1
        ensures  Elements + [result] == old(Elements)
        ensures  result              == old(Elements[|Elements| - 1])
}



/* SECTION: Class implementation */
class BoundedQueue<T(0)> {
    // Abstract state
    ghost var   Elements      : seq<T>
    ghost const maxLength     : nat
    ghost var   currentLength : nat
    ghost var   Repr          : set<object>
    // Concrete state
    var theArray : array<T>
    var wr       : nat
    var rd       : nat

    ghost predicate Valid()
        reads   this, Repr
        ensures Valid() ==> this in Repr
        ensures Valid() ==> |Elements| <= maxLength
        ensures Valid() ==> |Elements| == currentLength
    {
        // Pleasantries
        this in Repr
        && theArray in Repr
        // Abstraction relation
        && theArray.Length == maxLength
        && |Elements| <= maxLength
        && |Elements| == currentLength
        && 0 <= wr < maxLength
        && 0 <= rd < maxLength
        && (forall i :: 0 <= i < currentLength ==>
                theArray[(rd + i) % theArray.Length] == Elements[i]
        )
    }
    
    constructor(maxLength' : nat)
        requires maxLength' > 0
        ensures  fresh(Repr)
        ensures  Valid()
        ensures  Elements == []
        ensures  maxLength == maxLength'
        ensures  currentLength == 0
    {
        Elements      := [];
        maxLength     := maxLength';
        currentLength := 0;
        theArray      := new T[maxLength'];
        wr            := 0;
        rd            := 0;
        Repr          := {this, theArray};
    }
    
    method enqueue(value : T)
        requires Valid()
        requires currentLength != maxLength
        modifies Repr
        ensures  Valid()
        ensures  fresh(Repr - old(Repr))
        ensures  maxLength     == old(maxLength)
        ensures  currentLength == old(currentLength + 1)
        ensures  Elements      == [value] + old(Elements)
    // {
    //     Elements      := [value] + Elements;
    //     currentLength := currentLength + 1;
    //     theArray[wr]  := value;
    //     wr            := (wr + 1) % theArray.Length;
    // }
    
    method dequeue() returns (result : T)
        requires Valid()
        requires currentLength != 0
        modifies Repr
        ensures  Valid()
        ensures  maxLength           == old(maxLength)
        ensures  currentLength       == old(currentLength) - 1
        ensures  Elements + [result] == old(Elements)
        ensures  result              == old(Elements[|Elements| - 1])
}

