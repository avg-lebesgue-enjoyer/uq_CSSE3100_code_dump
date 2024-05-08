/* SECTION: Class specification */
class ExtensibleArraySpec<T> {
    ghost var Elements : seq<T>
    ghost var Repr : set<object>

    ghost predicate Valid()
        reads this, Repr
        ensures Valid() ==> this in Repr
    
    constructor()
        ensures Valid()
        ensures fresh(Repr)
        ensures Elements == [] // [1.] >>[]<< is the empty >>seq<T><<.

    function Get(index : nat) : T
        reads    Repr
        requires Valid()
        requires index < |Elements|
        // [1.] No need fore >> ensures Valid() << since functions don't change state
        ensures  Get(index) == Elements[index] 
    
    method Set(index : nat, value : T)
        modifies Repr
        requires Valid()
        requires index < |Elements|
        ensures  Valid()
        ensures  fresh(Repr - old(Repr))
        ensures  Elements == old(Elements)[index := value] // [1.] replace the index with the value
    
    method Add(value : T)
        modifies Repr
        requires Valid()
        ensures  Valid()
        ensures  fresh(Repr - old(Repr))
        ensures  Elements == old(Elements) + [value]
}



/* SECTION: Class implementation */
class ExtensibleArray<T(0)> { // [7.] >> T(0) << is a generic type *with an initial value*
    // Abstract state
    ghost var Elements : seq<T>
    ghost var Repr : set<object>
    // Concrete state
    var front  : array?<T>
    var depot  : ExtensibleArray?<array<T>>
    var length : nat                        // Total number of elements in this
    var M      : nat                        // Number of elements in the depot

    ghost predicate Valid()
        reads     this, Repr
        ensures   Valid() ==> this in Repr
        decreases Repr + {this}                 // [5.] Default >>decreases<< clause is "union all of >>reads<<".
    {
        // .; Standard patterns
        this in Repr                            // [4.] (a)
        // && front in Repr                     // [2.] DON'T ALLOW >>null<< IN >>Repr<<
        && (front != null ==> front in Repr)
        && (depot != null ==>                   // [2.] (this is to help ensure that >>Repr<<s are disjoint.)
                depot in Repr
                && depot.Repr <= this.Repr      // [4.] (c)
                && (forall j :: 0 <= j < |depot.Elements| ==>   // [3.] Transitively close subsets.
                        depot.Elements[j] in Repr
                    )
            )
        && (depot != null ==>
                // NOTE: No aliasing among this, frot with depot
                {this, front} !! depot.Repr     // [4.] (b) Necessary for termination below. // c.f. Ax. Foundation
                && depot.Valid()                // [4.] This recursive call terminates only when >>depot == null<<.
            )                                   //      (c) establishes depot.Repr <= this.Repr, and (a, b) establish that this is a proper subset
        && (depot != null ==>
            forall j :: 0 <= j < |depot.Elements| ==>
                depot.Elements[j] !in depot.Repr
                // NOTE: No aliasing between depot.Elements and front
                && depot.Elements[j] != front
                // NOTE: No aliasing among depot.Elements
                && forall k :: 0 <= k < |depot.Elements| && j != k ==>
                    depot.Elements[j] != depot.Elements[k]
        )
        // .; Abstraction relation / implementation details
        // NOTE: Goal is to keep track of *everything* we know about *every* variable.
        //       i.e. this is a huge brain-dump.
        // All arrays are of length 256
        && (front != null ==> front.Length == 256) // Design decision. This number is hard-coded because Dafny's verification has a tough time with arbitrary constants.
        && (depot != null ==>
                forall j :: 0 <= j < |depot.Elements| ==>
                    depot.Elements[j].Length == 256
        )
        // M is the number of elements in depot
        && M == (if depot == null then 0 else |depot.Elements| * 256) 
        // length is the number of elements in this
        && (front == null <==> length == M)
        && length == |Elements|
        // Depot increases in blocks of 256
        && M <= |Elements| < M + 256
        // [6.] ELEMENTS IN THE DEPOT ARE IN THE DEPOT
        && (forall i :: 0 <= i < M ==>
                Elements[i] == depot.Elements[i / 256][i % 256] // [which array][which position in that array]
        )
        // [6.] ELEMENTS NOT IN THE DEPOT ARE IN THE FRONT
        && (forall i :: M <= i < |Elements| ==>
                Elements[i] == front[i - M] // == front[i % 256]
        )
    }
    
    constructor()
        ensures Valid()
        ensures fresh(Repr)
        ensures Elements == []
    {
        Elements := [];
        Repr     := {this};
        front    := null;
        depot    := null;
        length   := 0;
        M        := 0;
    }

    function Get(index : nat) : T
        reads    Repr
        requires Valid()
        requires index < |Elements|
        ensures  Get(index) == Elements[index] 
    {
        if index < M
        then    depot.Get(index / 256)[index % 256] // NOTE: >>depot.Elements<< is >>ghost<<, so use >>depot.Get()<<
        else    front[index - M] // front[index % 256]
    }
    
    method Set(index : nat, value : T)
        modifies Repr
        requires Valid()
        requires index < |Elements|
        ensures  Valid()
        ensures  fresh(Repr - old(Repr))
        ensures  Elements == old(Elements)[index := value]
    {
        if index >= M {
            front[index - M] := value;
        } else {
            depot.Get(index / 256)[index % 256] := value;
        }
        Elements := Elements[index := value];
    }
    
    // [7.] we need an initial value here, for when we allocate our arrays.
    method Add(value : T)
        modifies  Repr
        requires  Valid()
        ensures   Valid()
        ensures   fresh(Repr - old(Repr))
        ensures   Elements == old(Elements) + [value]
        decreases |Elements| // [8.] for recursion termination
        //decreases length   // [8.] alternative >>decreases<< clause (this one also verifies)
    {
        if front == null {
            front := new T[256]; // [7.] requires initial values for T
            Repr  := Repr + {front};
        }
        front[length - M] := value;
        length            := length + 1;
        Elements          := Elements + [value];
        if length % 256 == 0 {
            if depot == null {
                depot := new ExtensibleArray<array<T>>(); // or type inferring >>ExtensibleArray()<<
            }
            depot.Add(front); // [8.]
            M     := M + 256;
            Repr  := Repr + depot.Repr;
            front := null;
        }
    }
}