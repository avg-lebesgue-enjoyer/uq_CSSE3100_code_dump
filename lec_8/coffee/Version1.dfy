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
    ghost var Repr  : set<object> // NOTE: >>object<< is the type for anything on the heap
    // Repr is a *representation set* for >>this<<
    var g : Grinder
    var w : WaterTank

    // NOTE: Class invariant!
    ghost predicate Valid()
        reads this // Still need to read this,
        reads Repr // because we don't know that >> this in Repr <<
    {
        // Repr captures the current state
        this in Repr
        && g in Repr
        && w in Repr
        // NOTE: It's fine to have more than just {this, g, w} <= Repr.
        // Validity
        && g.Valid()
        && w.Valid()
        && ready == (g.hasBeans && w.waterLevel != 0)
    }
    
    
    // NOTE: Default constructor
    constructor ()
        ensures !ready
        ensures Valid()
        ensures fresh(Repr)
    {
        g := new Grinder();   // initially empty
        w := new WaterTank(); // initially empty
        Repr  := {this, g, w};
        ready := false;
    }
    
    predicate Ready()
        requires Valid()
        reads    Repr
        ensures  Ready() == ready
    {
        // NOTE: can't refer to >>g.hasBeans<< since this is a ghost field.
        // NOTE: similarly, can't refer to >>w.Level()<<
        g.Ready() && w.Level() != 0
    }
    
    method Restock()
        requires Valid()
        modifies Repr
        ensures  Valid()
        // ensures  Repr == old(Repr) // [4.] Our internal objects don't change!
        ensures  fresh(Repr - old(Repr)) // see [5.]
        ensures  Ready()
    {
        g.AddBeans();
        w.Fill();
        ready := true;
    }
    
    method Dispense()
        requires Valid()
        requires Ready()
        modifies Repr
        // ensures  Repr == old(Repr)    // [4.] Typing this out is a pain the ass.
        //                               //      Also, we might want Repr to change...
        ensures  fresh(Repr - old(Repr)) // [5.] This is a better solution to [4.]
        ensures  Valid()
    {
        g.Grind();
        w.Use();
        ready := g.hasBeans && (w.waterLevel != 0);
    }

    // NOTE: New method! Not from specification.
    method ChangeGrinder()
        requires Valid()
        modifies Repr
        ensures  fresh(Repr - old(Repr)) // [5.]
        ensures  Valid()
    {
        g := new Grinder(); // NOTE: >>old(g)<< will get garbage-collected
        // NOTE: All of the following are fine.
        //       Repr doesn't get compiled anyway, so there
        //        are no space concerns or anything.
        // Repr := {this, g, w};
        // Repr := Repr + {g} - {old(g)};
        Repr := Repr + {g};
        ready := false;
    }
}



/* SECTION: Test harness! */

method CoffeeTestHarness() returns (success : bool) {
    var cm := new CoffeeMaker();
    cm.Restock();
    cm.Dispense();
    cm.Restock();

    success := false;
}
