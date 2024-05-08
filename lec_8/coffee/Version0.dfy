/* SECTION: Version 0 */

class Grinder {
    ghost var hasBeans : bool

    // NOTE: Class invariant!
    ghost predicate Valid()
        reads this
    
    // NOTE: Default constructor!
    constructor ()
        ensures !hasBeans
        ensures Valid()
    
    predicate Ready()
        requires Valid()
        reads    this
        ensures  Ready() == hasBeans
    
    method AddBeans()
        requires Valid()
        modifies this
        ensures  hasBeans
        ensures  Valid()
    
    method Grind()
        requires Valid()
        requires hasBeans
        modifies this
        ensures Valid()
}


class WaterTank {
    ghost var waterLevel : nat
    
    // NOTE: Class invariant!
    ghost predicate Valid()
        reads this
    
    // NOTE: Default constructor!
    constructor ()
        ensures waterLevel == 0
        ensures Valid()
    
    // Destructor
    function Level() : nat
        requires Valid()
        reads    this
        ensures Level() == waterLevel
    
    method Fill()
        requires Valid()
        modifies this
        ensures  waterLevel == 10
        ensures  Valid()
    
    method Use()
        requires Valid()
        requires waterLevel != 0
        modifies this
        ensures  waterLevel == old(waterLevel) - 1
        ensures  Valid()
}


/* ATTENTION: Assume the above are implemented! */



class CoffeeMaker{
    ghost var ready : bool
    var g : Grinder
    var w : WaterTank

    // NOTE: Class invariant!
    ghost predicate Valid()
        reads this
        reads g     // necessary for g.Valid()'s >> reads this <<
        reads w     // necessary for w.Valid()'s >> reads this <<
        // FIXME: >> reads g, w << exposes the implementation.
        //        This is terrible.
    {
        g.Valid()
        && w.Valid()
        && ready == (g.hasBeans && w.waterLevel != 0)
    }
    
    
    // NOTE: Default constructor
    constructor ()
        ensures !ready
        ensures Valid()
    
    predicate Ready()
        // requires Valid() // FIXME: Broken specification! Insufficient reads clause for >> Valid() <<
        reads    this
        ensures  Ready() == ready
    
    method Restock()
        requires Valid()
        modifies this
        ensures  Valid()
        ensures  Ready() // ???
    
    method Dispense()
        requires Valid()
        requires Ready()
        modifies this
        ensures  Valid()
}
