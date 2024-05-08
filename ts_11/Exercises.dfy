/* SECTION: Exercise 11.1 */
lemma IncreasingArray(a : array<int>, i : int)
    requires  0 <= i < a.Length
    requires  forall j :: i + 1 <= j < a.Length ==>
        a[j - 1] < a[j]
    ensures   forall j :: 0 <= i < j < a.Length ==>
        a[i] < a[j]
    decreases a.Length - i
{
    if i == a.Length - 1 {
        return;
    } else {
        IncreasingArray(a, i + 1);
    }
}



/* SECTION: Exercise 11.2 */
method LinearSearch(a : array<int>, x : int) returns (n : int)
    requires forall i :: 0 <= i < a.Length - 1 ==> a[i] < a[i + 1]
    ensures  0 <= n <= a.Length
    ensures  n == a.Length || a[n] == x
    ensures forall i :: 0 <= i < n ==> a[i] != x
{
    n := 0;
    while n != a.Length
        invariant 0 <= n <= a.Length
        invariant forall i :: 0 <= i < n ==> a[i] < x
    {
        if a[n] == x {
            return;
        }
        if a[n] > x {
            IncreasingArray(a, n); // The array is increasing, and we're already fucked here.
            n := a.Length;         // Therefore, we're fucked for the rest of the array. :)
            return;
        }
        n := n + 1;
    }
}



/* SECTION: Exercise 11.3 */
// Done in lecture notes!
