method Amogus(a : array<int>) returns (h : int)
    requires a.Length > 0
    ensures  h == a[0]
{
    h := a[0];
}



method Test(a : array<int>) returns ()
{
    assert a == null;
    assert a.Length > 0;
}
