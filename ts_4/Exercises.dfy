// SECTION: Exercise 4.1
method FirstLinearSearch<T> (a : array<T>, P : T -> bool) returns (n : int)
    ensures -1 <= n < a.Length
    ensures n == -1  ==>  !(exists i :: 0 <= i < a.Length && P(a[i]))
    ensures n != -1  ==>  P(a[n]) && (forall i :: 0 <= i < n ==> ! P(a[i]))
{
    n := 0;
    while n < a.Length
        invariant 0 <= n <= a.Length
        invariant forall i :: 0 <= i < n ==> ! P(a[i])
    {
        if P(a[n]) {
            return;
        }
        n := n + 1;
    }
    n := -1;
}



// SECTION: Exercise 4.2
// NOTE: EX 4.2a, 4.2b
method BinarySearch(a: array<int>, key: int) returns (n: int) 
    // requires forall i :: 0 <= i < a.Length - 1 ==> a[i] <= a[i + 1] // NOTE: Dafny won't inductively prove the condition below on its own!
    requires forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
    ensures 0 <= n <= a.Length
    ensures forall i :: 0 <= i < n ==> a[i] < key 
    ensures forall i :: n <= i < a.Length ==> key <= a[i]
{
    var lo, hi := 0, a.Length; 
    while lo < hi 
        invariant 0 <= lo <= hi <= a.Length
        //invariant forall i :: 0 <= i < a.Length - 1 ==> a[i] <= a[i + 1]
        invariant forall i :: 0 <= i < lo ==> a[i] < key 
        invariant forall i :: hi <= i < a.Length ==> key <= a[i] 
        decreases hi - lo
    {
        var mid := (lo + hi) / 2; 
        if a[mid] < key {
            lo := mid + 1;
        } else {
            hi := mid;
        } 
    } 
    n := lo;
}

// NOTE: EX 4.2c
method BinarySearchC(a: array<int>, key: int) returns (n: int) 
    requires forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
    ensures 0 <= n <= a.Length
    ensures forall i :: 0 <= i < n ==> a[i] <= key 
    ensures forall i :: n <= i < a.Length ==> key < a[i]
{
    var lo, hi := 0, a.Length; 
    while lo < hi 
        invariant 0 <= lo <= hi <= a.Length
        //invariant forall i :: 0 <= i < a.Length - 1 ==> a[i] <= a[i + 1]
        invariant forall i :: 0 <= i < lo ==> a[i] <= key 
        invariant forall i :: hi <= i < a.Length ==> key < a[i] 
        decreases hi - lo
    {
        var mid := (lo + hi) / 2; 
        if a[mid] <= key {
            lo := mid + 1;
        } else {
            hi := mid;
        } 
    } 
    n := lo;
}

// NOTE: EX 4.2d
method BinarySearchD(a: array<int>, key: int) returns (n: int) 
    requires forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
    ensures 0 <= n < a.Length || n == -1
    ensures (exists i :: 0 <= i < a.Length &&  a[i] == key) ==> n != -1 && a[n] == key
    ensures (forall i :: 0 <= i < a.Length ==> a[i] != key) ==> n == -1
{
    var lo, hi := 0, a.Length; 
    while lo < hi 
        invariant 0 <= lo <= hi <= a.Length
        invariant forall i :: 0 <= i < lo ==> a[i] < key 
        invariant forall i :: hi <= i < a.Length ==> key < a[i] 
        decreases hi - lo
    {
        var mid := (lo + hi) / 2; 
        if a[mid] < key {
            lo := mid + 1;
        } else if a[mid] == key {
            n := mid;
            return;
        } else {
            hi := mid;
        } 
    } 
    n := -1;
}

// NOTE: EX 4.2e
method BinarySearchE(a: array<int>, key: int) returns (n: int) 
    requires forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
    requires exists i :: 0 <= i < a.Length && a[i] == key
    ensures 0 <= n < a.Length
    ensures a[n] == key
{
    var lo, hi := 0, a.Length; 
    while lo < hi 
        invariant 0 <= lo <= hi <= a.Length
        //invariant forall i :: 0 <= i < a.Length - 1 ==> a[i] <= a[i + 1]
        invariant forall i :: 0 <= i < lo ==> a[i] < key 
        invariant forall i :: hi <= i < a.Length ==> key < a[i] 
        decreases hi - lo
    {
        var mid := (lo + hi) / 2; 
        if a[mid] < key {
            lo := mid + 1;
        } else if a[mid] == key {
            n := mid;
            return;
        } else {
            hi := mid;
        } 
    } 
}


// SECTION: Exercise 4.3
method Min(a: array<int>) returns (m: int) 
    requires a.Length != 0
    //ensures forall i :: 0 <= i < a.Length ==> m <= a[i]
    ensures forall i :: 1 <= i < a.Length ==> m <= a[i]
    ensures exists i :: 0 <= i < a.Length &&  m == a[i]



// SECTION: Exercise 4.4
/*  Specify and write a method to compute the maximum of an array of type 
    array<nat>. Allow the array to be empty, and in that case return 0 as
    the maximum. Verify your method is correct using the Dafny verifier
*/
method Maximussy (a : array<nat>) returns (mm : nat)
    ensures mm == 0
            || (exists i :: 0 <= i < a.Length && mm == a[i])
    ensures forall i :: 0 <= i < a.Length ==> a[i] <= mm
{
    // Edge case
    if a.Length == 0{
        mm := 0;
        return;
    }
    // Standard case
    mm := a[0];
    var i := 1;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant exists m :: 0 <= m < i && a[m] == mm
        invariant forall j :: 0 <= j < i ==> a[j] <= mm
        decreases a.Length - i
    {
        if a[i] > mm {
            mm := a[i];
        }
        i := i + 1;
    }
}


