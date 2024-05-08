/* SECTION: Specification */

class Grinder {
    ghost var hasBeans : bool
    ghost var Repr     : set<object>

    // NOTE: Class invariant!
    ghost predicate Valid()
        reads this, Repr
        ensures Valid() ==> this in Repr // [1.] We're always here (WAH?); always do for Valid()
    
    // NOTE: Default constructor!
    constructor ()
        ensures !hasBeans
        ensures Valid()
        ensures fresh(Repr) // [2.] Always do this on constructors
    
    predicate Ready()
        requires Valid()
        reads    Repr
        ensures  Ready() == hasBeans
    
    method AddBeans()
        requires Valid()
        modifies Repr
        ensures  Valid()
        ensures  fresh(Repr - old(Repr)) // [3.] Methods that modify must do this
        ensures  hasBeans
    
    method Grind()
        requires Valid()
        requires hasBeans
        modifies Repr
        ensures  Valid()
        ensures  fresh(Repr - old(Repr)) // [3.] Methods that modify must do this
}


class WaterTank {
    ghost var waterLevel : nat
    ghost var Repr       : set<object>
    
    // NOTE: Class invariant!
    ghost predicate Valid()
        reads   this, Repr
        ensures Valid() ==> this in Repr // [1.]
    
    // NOTE: Default constructor!
    constructor ()
        ensures waterLevel == 0
        ensures Valid()
        ensures fresh(Repr) // [2.]
    
    // Destructor
    function Level() : nat
        requires Valid()
        reads    Repr
        ensures  Level() == waterLevel
    
    method Fill()
        requires Valid()
        modifies Repr
        ensures  waterLevel == 10
        ensures  Valid()
        ensures  fresh(Repr - old(Repr)) // [3.]
    
    method Use()
        requires Valid()
        requires waterLevel != 0
        modifies Repr
        ensures  Valid()
        ensures  fresh(Repr - old(Repr)) // [3.]
        ensures  waterLevel == old(waterLevel) - 1
}



/* ATTENTION: Assume the above are implemented. */ 



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
        && g.Repr <= Repr // [4.] Must assert that the state of CoffeeMaker includes that of g
        && w.Repr <= Repr // [4.] NOTE: >> <= << is \subseteq
        // NOTE: It's fine to have more than just {this, g, w} <= Repr.
        // Validity
        && g.Valid()
        && w.Valid()
        && g.Repr !! w.Repr // [6.] See problem described below. Sub-objects should have disjoint representations
        && this !in g.Repr  // [7.] See problem described below.
        && this !in w.Repr  // [7.] Sub-objects shouldn't up-reference.
        && ready == (g.hasBeans && w.waterLevel != 0)
    }
    
    
    // NOTE: Default constructor
    constructor ()
        ensures !ready
        ensures Valid()
        ensures fresh(Repr)
    {
        /* NOTE: Dafny has 2-phase constructors.
            Phase 1:
                Set up pointers to heap for >>this<<.
            NOTE: Keyword >> new; << separates these phases.
            Phase 2:
                In this phase, >>g, w<< are able to be read.
        */
        g := new Grinder();   // initially empty
        w := new WaterTank(); // initially empty
        Repr  := {this, g, w};
        ready := false;
        new;
        Repr  := Repr + g.Repr + w.Repr; // [4.]
    }
    
    predicate Ready()
        requires Valid()
        reads    Repr
        ensures  Ready() == ready
    {
        g.Ready() 
        && w.Level() != 0
    }
    
    method Restock()
        requires Valid()
        modifies Repr
        ensures  Valid()
        // ensures  Repr == old(Repr) // [4.] Our internal objects don't change!
        ensures  fresh(Repr - old(Repr)) // see [5.]
        ensures  Ready()
    {
        // assert w.Valid(); // <!> Assertion passes
        g.AddBeans();
        // DEBUG:
        // assert Valid();          // <!> Assertion fails
        // assert w.Valid();        // <!> Assertion fails
        // assert g.Repr !! w.Repr; // <!> Assertion fails // NOTE: >>!!<< is "disjoint"
        // NOTE: These assertions pick up the following error:
        //  Suppose there's aliasing between g and w; i.e.
        //   g has some stuff in g.Repr that w also has in
        //   w.Repr.
        //  Then, g may modify that common stuff, which might
        //   throw off w.Valid().
        // This is fixed by [6.].
        // :DEBUG
        // DEBUG:
        // assert this !in g.Repr; // <!> Assertion fails
        // assert this !in w.Repr; // <!> Assertion fails
        // NOTE: These assertions pick up the following error:
        //  Suppose >> this in g.Repr <<. Then, >> g.AddBeans() <<
        //   might modify >>this<<, so we are mega fucked.
        // This aliasing is fixed by [7.].
        // :DEBUG
        w.Fill();
        ready := true;
        // DEBUG:
        // assert g.Repr <= Repr; // <!> Assertion fails
        // assert w.Repr <= Repr; // <!> Assertion fails
        // NOTE: These assertions pick up the following error:
        //  g.AddBeans()   might modify g.Repr;
        //   sym. w.Fill() might modify w.Repr;
        //   but any new objects added to g.Repr or w.Repr may
        //   not be shoved into this.Repr.
        // This is fixed by [8.].
        // :DEBUG
        Repr := Repr + g.Repr + w.Repr; // [8.]
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
        Repr  := Repr + g.Repr + w.Repr; // [8.]
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
        Repr  := Repr + {g};
        ready := false;
        Repr  := Repr + g.Repr + w.Repr; // [8.]
    }
}
