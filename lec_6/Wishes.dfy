// Implement the following specification using only +, :=, ==, while.
method Cube(n : nat) returns (c : nat)
    ensures c == n * n * n
{
    // 1. Replace a constant by a variable.
    //      Here, replace n by a counter n' going up to n
    var n' := 0;    // Loop counter
    c := 0;         // Initially, c == 0 * 0 * 0 == 0
    var x := 0;     // Initially, x == 3 * 0 * 0 == 0
    var y := 0;     // Initially, y == 3 * 0     == 0
    while n' < n
        invariant 0 <= n' <= n
        invariant c == n' * n' * n'
        invariant x == 3  * n' * n'
        invariant y == 3  * n'
    {
        // Invariants hold :)
        // c                     == n' * n' * n'
        //  && x                 == 3 * n' * n'
        //  && y                 == 3 * n'
        // c + x + y + 1         == n' * n' * n'  +  x  +  y  +  1
        //  && x                 == 3 * n' * n'
        //  && y                 == 3 * n'
        // c + x + y + 1         == n' * n' * n'  +  3 * n' * n'  +  3 * n'  +  1
        //  && x                 == 3 * n' * n'
        //  && y                 == 3 * n'
        // c + x + y + 1         == n' * n' * n'  +  3 * n' * n'  +  3 * n'  +  1
        //  && x  +  2 * y  +  3 == 3 * n' * n'  +  2 * y  + 3
        //  && y                 == 3 * n'
        // c + x + y + 1         == n' * n' * n'  +  3 * n' * n'  +  3 * n'  +  1
        //  && x  +  2 * y  +  3 == 3 * n' * n'  +  2 * 3 * n'  + 3
        //  && y                 == 3 * n'
        // c + x + y + 1         == n' * n' * n'  +  3 * n' * n'  +  3 * n'  +  1
        //  && x  +  2 * y  +  3 == 3 * n' * n'  +  2 * 3 * n'  + 3
        //  && y  +  3           == 3 * n'  +  3
        c, x, y := 
            c + x + y + 1, 
            x + y + y + 3, 
            y + 3;
        // c == (previous c)  +  (previous x)  +  (previous y)  +  1
        //  && x == (previous x)  +  2 * (previous y)  + 3
        //  && y == (previous y)  +  3
        // c == n' * n' * n'  +  3 * n' * n'  +  3 * n'  +  1
        //  && x == 3 * n' * n'  +  2 * 3 * n'  + 3
        //  && y == 3 * n'  +  3
        // 2. Wish for expressions
        //      3 * n' * n'  as  x
        //      3 * n'       as  y
        // c == n' * n' * n'  +  3 * n' * n'  +  3 * n'  +  1
        //  && x == 3 * n' * n'  +  2 * 3 * n'  + 3
        //  && y == 3 * n'  +  3
        // c == (n' + 1) * (n' + 1) * (n' + 1)
        //  && x == 3 * (n' + 1) * (n' + 1)
        //  && y == 3 * (n' + 1)
        n' := n' + 1;
        // c == n' * n' * n'
        //  && x == 3 * n' * n'
        //  && y == 3 * n'
    }
}