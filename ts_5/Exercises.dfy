// SECTION: Exercise 5.1
method IncrementMatrix (m : array2<int>)
    modifies m
    ensures  forall i, j :: 
                0 <= i < m.Length0 
                && 0 <= j < m.Length1 
                ==> m[i, j] == old(m[i, j] + 1)
{
    var i := 0;
    var j := 0;
    while i < m.Length0
        invariant 0 <= i <= m.Length0
        invariant 0 <= j <= m.Length1
        // "Rows before row i are done"
        invariant forall i', j' :: 0 <= i' < i         && 0 <= j' < m.Length1 ==>
                    m[i', j'] == old(m[i', j'] + 1)
        // "Rows after row i, including row i, are untouched"
        invariant forall i', j' :: i <= i' < m.Length0 && 0 <= j' < m.Length1 ==>
                    m[i', j'] == old(m[i', j'])
    {
        j := 0;
        while j < m.Length1
            invariant 0 <= i <  m.Length0
            invariant 0 <= j <= m.Length1
            // "Rows before row i are done"
            invariant forall i', j' :: 0 <= i' < i         && 0 <= j' < m.Length1 ==>
                        m[i', j'] == old(m[i', j'] + 1)
            // "Rows after row i are untouched"
            invariant forall i', j' :: i <  i' < m.Length0 && 0 <= j' < m.Length1 ==>
                        m[i', j'] == old(m[i', j'])
            // "Things along this row before column j are done"
            invariant forall j' ::     0 <= j' < j ==>
                        m[i,  j'] == old(m[i,  j'] + 1)
            // "Things along this row after column j are untouched"
            invariant forall j' ::     j <= j' < m.Length1 ==>
                        m[i,  j'] == old(m[i,  j'])
        {
            m[i, j] := m[i, j] + 1;
            j := j + 1;
        }
        i := i + 1;
    }
}



// SECTION: Exercise 5.2
method CopyMatrix<T> (source : array2<T>, destination : array2<T>)
    requires source.Length0 == destination.Length0
    requires source.Length1 == destination.Length1
    requires source != destination
    modifies destination
    ensures  forall i, j :: 
                0 <= i < source.Length0 &&
                0 <= j < source.Length1 ==>
                    destination[i, j] == source[i, j]
{
    var i := 0;
    var j := 0;
    while i < source.Length0
        // Valid indices
        invariant 0 <= i <= source.Length0
        invariant 0 <= j <= source.Length1
        // Rows before row i are done
        invariant forall i', j' ::
                    0 <= i' < i &&
                    0 <= j' < source.Length1 ==>
                        destination[i', j'] == source[i', j']
    {
        j := 0;
        while j < source.Length1
            // Valid indices
            invariant 0 <= i <  source.Length0
            invariant 0 <= j <= source.Length1
            // Rows before row i are done
            invariant forall i', j' ::
                        0 <= i' < i &&
                        0 <= j' < source.Length1 ==>
                            destination[i', j'] == source[i', j']
            // On row i, columns before column j are done
            invariant forall j' ::
                        0 <= j' < j ==>
                            destination[i,  j'] == source[i,  j']
        {
            destination[i, j] := source[i, j];
            j := j + 1;
        }
        i := i + 1;

    }
}



// SECTION: Exercise 5.3
method DoubleArray (src : array<int>, dst : array<int>)
    requires src.Length == dst.Length
    modifies dst
    ensures  forall i :: 0 <= i < src.Length ==>
                dst[i] == old(2 * src[i])
{
    var i := 0;
    while i < src.Length
        // Valid index
        invariant 0 <= i <= src.Length
        // dst: Entries before index i are done
        invariant forall i' :: 0 <= i' < i ==>
                    dst[i'] == old(2 * src[i'])
        // src: Entries at or after index i are untouched
        invariant forall i' :: i <= i' < src.Length ==>
                    src[i'] == old(src[i'])
    {
        dst[i] := 2 * src[i];
        i := i + 1;
    }
}



// SECTION: Exercise 5.4
method GetRotated (a : array)
    // requires a.Length != 0
    modifies a
    ensures  a.Length != 0 ==>
                a[a.Length - 1] == old(a[0])
    ensures forall i :: 0 <= i < a.Length - 1 ==>
                a[i] == old(a[i + 1])
{
    // Edge case: Length 0
    if a.Length == 0
    {
        return;
    }

    var i := 0;
    var oldHead := a[0];
    while i < a.Length - 1
        // Valid index
        invariant 0 <= i <= a.Length - 1
        // Done up to index i
        invariant forall i' :: 0 <= i' < i ==>
                a[i'] == old(a[i' + 1])
        // At or after index i is untouched
        invariant forall i' :: i <= i' < a.Length ==>
                a[i'] == old(a[i'])
    {
        a[i] := a[i + 1];
        i := i + 1;
    }
    a[a.Length - 1] := oldHead;
}



// SECTION: Exercise 5.5
// This is the same as Exercise 5.4. I'm not gonna waste my time here.
