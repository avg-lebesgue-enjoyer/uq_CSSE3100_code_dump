// SECTION: Exercise 7.1
// Prove correctness of M.
method M (a : array<int>, d : int)
    ensures forall i :: 0 <= i < a.Length ==> a[i] == d + 1
{
    /* true
    */
    /* forall a^af ::
    //      true
    */
    /* forall a^af ::
    //      a^af.Length == a.Length
    //      && (forall i :: 0 <= i < a^af.Length ==> a^af[i] == d)
    //      ==> forall i :: 0 <= i < a^af.Length ==> a^af[i] == d
    */
    InitialiseArray(a, d);
    /* forall i :: 0 <= i < a.Length ==> a[i] == d
    */
    /* forall a^af ::                                           
    //      a^af.Length == a.Length
    //      && forall i :: 0 <= i < a.Length ==> a[i] == d
    */
    /* forall a^af ::                                           
    //      a^af.Length == a.Length
    //      && forall i :: 0 <= i < a.Length ==> a[i] + 1 == d + 1
    */ // ^^ strengthened
    /* forall a^af ::
    //      a^af.Length == a.Length // NOTE: I didn't think about this...
    //      && (forall i :: 0 <= i < a^af.Length ==> a^af[i] == a[i] + 1)
    //      ==> (forall i :: 0 <= i < a^af.Length ==> a^af[i] == d + 1)
    */
    IncrementArray(a);
    // forall i :: 0 <= i < a.Length ==> a[i] == d + 1
}

// given these for free
method InitialiseArray<T> (a : array<T>, d : T)
    ensures forall i :: 0 <= i < a.Length ==> a[i] == d

method IncrementArray (a : array<int>)
    ensures forall i :: 0 <= i < a.Length ==> a[i] == old(a[i] + 1)

// \qed.




// SECTION: Exercise 7.2a
// pv. partial correct
method Mult (x : int, y : int) returns (r : int)
    requires x >= 0 && y >= 0
    ensures  r == x * y
{
    /* x >= 0 && y >= 0
    */
    /* (x == 0 ==> (x == 0 || y == 0))
    // && (x != 0 ==> x - 1 >= 0 && y >= 0)
    */
    if x == 0 {
        /* x == 0 || y == 0
        */
        /* 0 == x * y
        */
        r := 0;
        /* r == x * y
        */
    } else {
        /* x - 1 >= 0 && y >= 0
        */
        /* x - 1 >= 0 && y >= 0
        // && (x - 1) * y + y == x * y
        */
        var z := Mult(x - 1, y);
        /* z + y == x * y
        */
        r := z + y;
        /* r == x * y
        */
    }
    /* r == x * y
    */ 
}

// SECTION: Exercise 7.2b
// Termination metric is x.



// SECTION: Exercise 7.3

function F(x : int) : int 
    decreases x
{
    if x < 10 then x else F(x - 1)
}

function G(x : int) : int
    decreases x
{
    if x >= 0 then G(x - 2) else x
}

function H(x : int) : int
    decreases x + 60
{
    if x < -60 then x else H(x - 1)
}

function I (x : nat, y : nat) : int 
    decreases x, y
{
    if x == 0 || y == 0 then
        12
    else if x % 2 == y % 2 then
        I(x - 1, y)
    else
        I(x, y - 1)
}

function M'(x : int, b : bool) : int
    decreases !b
{
    if b then x else M'(x + 25, true)
}

function L (x : int) : int
    decreases 100 - x
{
    if x < 100 then L(x + 1) + 10 else x
}

function J (x : nat, y : nat) : int
    decreases x, y
{
    if x == 0 then
        y
    else if y == 0 then
        J(x - 1, 3)
    else
        J(x, y - 1)
}



// SECTION: Exercise 7.4
/*  a: >
    b: <
    c: >
    d: <
    e: >
    f: >
    g: >
    h: incomparable // NOTE: Dafny will bail out to *false* here.
    i: <
    j: idk if < is defined on {} // NOTE: It is, and it's \subsetneq
*/



// SECTION: Exercise 7.5a

method Outer(a : nat) 
    decreases a
{
    if a != 0 {
        var b := a - 1;
        Inner(a, b);
    }
}

method Inner (a : nat, b : nat)
    decreases a, b
    requires a != 0
{
    if b == 0 {
        Outer (a - 1);
    } else {
        Inner (a, b - 1);
    }
}

// SECTION: Exercise 7.5b

method Outer' (a : nat) 
    decreases a, false
{
    if a != 0 {
        var b := a - 1;
        Inner'(a - 1, b);
    }
}

method Inner' (a : nat, b : nat)
    decreases  a, true, b
{
    if b == 0 {
        Outer'(a);
    } else {
        Inner'(a, b - 1);
    }
}
