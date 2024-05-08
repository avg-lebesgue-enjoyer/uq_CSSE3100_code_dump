/* SECTION: Toy example */

method AssignmentsToMark(students : int, tutors : int) returns (r : int)
    requires students > 0 && tutors > 1
    ensures  r < students
{
    DivisionLemma(students, tutors); // [1.] Without this lemma, the thingo doesn't verify.
    r := students/tutors;            // [1.] Not happy because of non-linear arithmetic!
}

lemma DivisionLemma(n : int, d : int)
    requires n > 0 && d > 1
    ensures  n/d < n
{
    calc <==> {
        1/d     < 1;    //      this line
        (n/n)/d  < n/n; // <==> this line
        n/d     < n;    // <==> this line   // this isn't necessary; Dafny is smart enough to deduce this line on its own
    }
}



/* SECTION: calc */
// Proof calculation. Like proofs by hand on paper.

ghost method CalcExample(x : int, n : nat)
{
    calc == {
        3;              //    3
        2 + 1;          // == 2 + 1
        1 + 1 + 1;      // == 1 + 1 + 1
    }

    calc {
        (x < 10 ==> x >= 20) && (x > 10 ==> true);
    ==> (x >= 10 || x >= 20) && true;
    ==> (x >= 10 || x >= 20);
    ==> x >= 10;
    }

    calc {
        3 * x + n + n;
    ==  3 * x + 2 * n;
    <=  3 * x + 3 * n;
    == 3 * (x + n);
    }

    // Default operators are provided like this:
    calc == {
        3 * x + n + n;
        3 * x + 2 * n;
    <=  3 * x + 3 * n;
        3 * (x + n);
    }

    calc { // == is the default when none is provided.
        3 * x + n + n;
        3 * x + 2 * n;
    <=  3 * x + 3 * n;
        3 * (x + n);
    }
    
}



/* SECTION: Sum function */

ghost function Sum(a : array<int>, i : int, j : int) : int
    requires  0 <= i <= j <= a.Length
    reads     a
    decreases j - i
{
    if i == j
    then    0
    else    a[i] + Sum(a, i + 1, j)
}

ghost method Tester(a : array<int>, i : int, j : int)
    requires 0 <= i <= j < a.Length
{
    SumFromRight(a, i, j);
    assert Sum(a, i, j) + a[j] == Sum(a, i, j + 1);
}

lemma SumFromRight(a : array<int>, i : int, j : int)
    requires  0 <= i <= j < a.Length
    ensures   Sum(a, i, j) + a[j] == Sum(a, i, j + 1)
    decreases j - i
{
    // [2.] Inductive prooof.
    if i == j {
        // [2.] Dafny can figure out the base case :)
    } else {
        // [2.] Inductive step
        SumFromRight(a, i + 1, j);
    }
}



/* SECTION: Coincidence count */

method CoincidenceCount(a : array<int>, b : array<int>) returns (c : nat)
    requires forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
    requires forall i, j :: 0 <= i < j < b.Length ==> b[i] <= b[j]
    ensures  c == |multiset(a[..]) * multiset(b[..])| // [4.] * is multiset intersection
{
    c := 0;
    var m, n := 0, 0;
    while m < a.Length && n < b.Length
        invariant 0 <= m <= a.Length
        invariant 0 <= n <= b.Length
        invariant c + |multiset(a[m..]) * multiset(b[n..])|
                  ==  |multiset(a[..])  * multiset(b[..])|
    {
        if a[m] == b[n] {
            CaseEq(a, b, m, n);
            assert // [5.] The lemma CaseEq() handles this assertion
                multiset(a[m..]) * multiset(b[n..])
                ==  multiset([a[m]]) 
                    + (multiset(a[m + 1 ..]) * multiset(b[n + 1 ..])) // [4.] + is multiset union
            ;
            c, m, n := c + 1, m + 1, n + 1;
            assert // [5.] The previous assertion lets this one go through
                c + |multiset(a[m..]) * multiset(b[n..])|
                  ==  |multiset(a[..])  * multiset(b[..])|
            ;
        } else if a[m] < b[n] {
            CaseLess(a, b, m, n);
            assert // [6.] The lemma CaseLess() handles this assertion
                multiset(a[m..]) * multiset(b[n..])
                ==  multiset(a[m + 1 ..]) * multiset(b[n..])
            ;
            m := m + 1;
            assert // [6.] The previous assertion lets this one go through
                c + |multiset(a[m..]) * multiset(b[n..])|
                  ==  |multiset(a[..])  * multiset(b[..])|
            ;
        } else { // b[n] < a[m]
            // [8.] Do either this...
            CaseGreater(a, b, m, n);
            // [8.] Or this...
            CaseLess(b, a, n, m);
            assert multiset(b[n..]) * multiset(a[m..])  // Multiset intersection is commutative
                == multiset(a[m..]) * multiset(b[n..])
            ;
            // [8.] Either way, the assertion below finally holds
            assert // [7.] The lemma CaseGreater() handles this assertion
                multiset(a[m..]) * multiset(b[n..])
                ==  multiset(a[m..]) * multiset(b[n + 1..])
            ;
            n := n + 1;
            assert // [7.] The previous assertion lets this one go through
                c + |multiset(a[m..]) * multiset(b[n..])|
                  ==  |multiset(a[..])  * multiset(b[..])|
            ;
        }
    }
}

lemma FundamentalMultiset(a : array<int>, m : nat)
    requires m < a.Length
    ensures  multiset(a[m..]) == multiset([a[m]]) + multiset(a[m + 1 ..])
{
    // Implementation with calc
    calc {
                 a[m..]  ==          [a[m]] +           a[m + 1 ..];
        multiset(a[m..]) == multiset([a[m]]) + multiset(a[m + 1 ..]);
    }
}

lemma FundamentalMultiset'(a : array<int>, m : nat)
    requires m < a.Length
    ensures  multiset(a[m..]) == multiset([a[m]]) + multiset(a[m + 1 ..])
{
    // This implementation works too
    assert a[m..] == [a[m]] + a[m + 1 ..];
}

lemma CaseEq(a : array<int>, b : array<int>, m : nat, n : nat)
    requires m < a.Length
    requires n < b.Length
    requires a[m] == b[n]
    ensures  multiset(a[m..]) * multiset(b[n..])
                ==  multiset([a[m]]) 
                    + (multiset(a[m + 1 ..]) * multiset(b[n + 1 ..]))
{
    FundamentalMultiset(a, m);
    FundamentalMultiset(b, n);
    // calc {
    //     a[m..] == [a[m]] + a[m + 1 ..] 
    //         && b[n..] == [b[n]] + b[n + 1 ..]
    //     ;
    //     multiset(a[m..]) == multiset([a[m]]) + multiset(a[m + 1 ..])
    //         && multiset(b[n..]) == multiset([b[n]]) + multiset(b[n + 1 ..])
    //     ;
    // }
}

lemma CaseLess(a : array<int>, b : array<int>, m : nat, n : nat)
    requires m < a.Length
    requires n < b.Length
    requires forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
    requires forall i, j :: 0 <= i < j < b.Length ==> b[i] <= b[j]
    requires a[m] < b[n]
    ensures  multiset(a[m..]) * multiset(b[n..])
                ==  multiset(a[m + 1 ..]) * multiset(b[n..])
{
    FundamentalMultiset(a, m);
}

lemma CaseGreater(a : array<int>, b : array<int>, m : nat, n : nat)
    requires m < a.Length
    requires n < b.Length
    requires forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
    requires forall i, j :: 0 <= i < j < b.Length ==> b[i] <= b[j]
    requires a[m] > b[n]
    ensures  multiset(a[m..]) * multiset(b[n..])
                ==  multiset(a[m..]) * multiset(b[n + 1 ..])
{
    FundamentalMultiset(b, n);
}
