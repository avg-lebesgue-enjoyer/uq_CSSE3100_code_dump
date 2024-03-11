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