/* SECTION: First iteration of ChecksumCalculator */
class ChecksumCalculator1 {
    ghost var data : string // for specification and reasoning only
    var s : int

    // NOTE: Default constructor.
    constructor ()
        ensures data == ""
        ensures Valid() // [2.]
    {
        data := "";
        s := 0;
    }
    
    // NOTE: CLASS INVARIANT!
    // NOTE: Calling it "Valid()" is a convention.
    // [2.] This should be required everywhere!
    // [2.] This should be ensured  everywhere! (except after functions)
    ghost predicate Valid()
        reads this
    {
        s == SumChars(data) // [1.]
    }
    
    method Append(d : string)
        requires Valid() // [2.]
        modifies this
        ensures  data == old(data) + d
        ensures  Valid() // [2.]
    {
        var i := 0;
        while i < |d|
            invariant 0 <= i <= |d|
            invariant Valid()
            invariant data == old(data) + d[..i]
            decreases |d| - i 
        {
            s := s + (d[i] as int); // NOTE: <This needs to happen at the
            data := data + [d[i]];  // same time as <this, since otherwise
            i := i + 1;             // Valid() won't be an invariant.
        }
    }
    
    function Checksum() : int
        reads this
        requires Valid() // [2.]
        ensures Checksum() == Hash(data)
        // ensures Valid() // NOTE: This is not needed, since >>function<<s can't change state!
    {
        s % 137
        // NOTE: Abstraction relation: s == SumChars(data). 
        //       This is built-in at [1.]
    }
    
    ghost function Hash(s : string) : int {
        SumChars(s) % 137
    }

    ghost function SumChars(s : string) : int {
        if |s| == 0 then 
            0 
        else
            // >> as int << is a typecast
            (s[|s| - 1] as int) + SumChars(s[.. |s| - 1])
    }
}



/* SECTION: First iteration of ChecksumCalculator */
class ChecksumCalculator2 {
    // The idea for [3.] is that at the cost of more complicated state, we can
    //  cache the result of a checksum.
    ghost var data : string // for specification and reasoning only
    var s  : int    // Current data sum
    var b  : bool   // Has the state changed since the last checksum?
    var cs : int    // Last calculated checksum

    // NOTE: Default constructor.
    constructor ()
        ensures data == ""
        ensures Valid() // [2.]
    {
        data := "";
        s  := 0;
        b  := false;
        cs := 0;
    }
    
    // NOTE: CLASS INVARIANT!
    // [2.] This should be required everywhere!
    // [2.] This should be ensured  everywhere! (except after functions)
    ghost predicate Valid()
        reads this
    {
        s == SumChars(data) // [1.]
        && (b ==> cs == Hash(data)) // [3.]
    }
    
    method Append(d : string)
        requires Valid() // [2.]
        modifies this
        ensures  data == old(data) + d
        ensures  Valid() // [2.]
    {
        b := false;
        var i := 0;
        while i < |d|
            invariant 0 <= i <= |d|
            invariant Valid()
            invariant !b        // b isn't touched by the loop!
            invariant data == old(data) + d[..i]
            decreases |d| - i 
        {
            s := s + (d[i] as int); 
            data := data + [d[i]];  
            i := i + 1;             
        }
    }
    
    method Checksum() returns (checksum : int)
        requires Valid() // [2.]
        modifies this
        ensures  checksum == Hash(data)
        ensures  Valid()
    {
        if !b {
            cs := s % 137;
            b  := true;
        }
        checksum := cs;
    }
    
    ghost function Hash(s : string) : int {
        SumChars(s) % 137
    }

    ghost function SumChars(s : string) : int {
        if |s| == 0 then 
            0 
        else
            (s[|s| - 1] as int) + SumChars(s[.. |s| - 1])
    }
}
