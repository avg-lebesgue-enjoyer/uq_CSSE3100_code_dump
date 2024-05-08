class Grinder { 
	ghost var hasBeans: bool 
	ghost var Repr: set<object>

	ghost predicate Valid() 
		reads this, Repr
        ensures Valid() ==> this in Repr
		
	constructor() 
		ensures Valid() && fresh(Repr) && !hasBeans

	function Ready(): bool 
		requires Valid() 
		reads Repr
		ensures Ready() == hasBeans

	method AddBeans() 
		requires Valid() 
		modifies Repr 
		ensures Valid() && hasBeans && fresh(Repr-old(Repr))

	method Grind() 
		requires Valid() && hasBeans 
		modifies Repr 
		ensures Valid() && fresh(Repr-old(Repr))
}

class WaterTank { 
	ghost var waterLevel: nat
	ghost var Repr: set<object>

	ghost predicate Valid() 			 
		reads this, Repr 		
        ensures Valid() ==> this in Repr

	constructor() 				 
		ensures Valid() && fresh(Repr) && waterLevel == 0

	function Level(): nat 
		requires Valid()
		reads Repr
		ensures Level() == waterLevel

	method Fill() 
		requires Valid() 
		modifies Repr 
		ensures Valid() && fresh(Repr-old(Repr)) && waterLevel == 10 

	method Use() 
		requires Valid() && waterLevel != 0 
		modifies Repr 
		ensures Valid() && fresh(Repr-old(Repr)) && waterLevel == old(Level()) - 1  
}

class CoffeeMaker { 	
	var g: Grinder 	
	var w: WaterTank
	ghost var ready: bool
	ghost var Repr: set<object>

	ghost predicate Valid() 
		reads this, Repr
		ensures Valid() ==> this in Repr
	{ 
		this in Repr && g in Repr && w in Repr &&
		g.Repr <= Repr && w.Repr <= Repr &&
		g.Repr !! w.Repr && this !in g.Repr && this !in w.Repr &&
		g.Valid() && w.Valid() && 
		ready == (g.hasBeans && w.waterLevel != 0) 
	}

	constructor() 
		ensures Valid() && fresh(Repr)
	{ 
		g := new Grinder(); 
		w := new WaterTank(); 
		ready := false;
		new;
		Repr := {this, g, w} + g.Repr + w.Repr;
	}

	predicate Ready() 
		requires Valid() 
		reads Repr
		ensures Ready() == ready
	{ 
		g.Ready() && w.Level() != 0
	}

	method Restock() 
		requires Valid() 
		modifies Repr 
		ensures Valid() && Ready() && fresh(Repr - old(Repr))
	{ 
		g.AddBeans(); 
		w.Fill();  
		ready := true;
		Repr := Repr + g.Repr + w.Repr;
	} 

	method Dispense()
		requires Valid() && Ready() 
		modifies Repr 
		ensures Valid() && fresh(Repr - old(Repr))
	{ 	
		g.Grind(); 
		w.Use(); 
		ready := g.hasBeans && w.waterLevel != 0;
		Repr := Repr + g.Repr + w.Repr;
	}

    method ChangeGrinder() 
        requires Valid()
        modifies Repr
        ensures  Valid()
        ensures  fresh(Repr - old(Repr))
        ensures  ready == false
    {
        g := new Grinder();
        ready := false;
        Repr := Repr + {g};
        Repr := Repr + g.Repr; // [1.] Added by me to fix >> g.Repr <= Repr <<
    }

    method InstallCustomGridner(grinder : Grinder)
        requires Valid()
        requires grinder.Valid()
        requires grinder.Repr !! Repr // [2.] Specification changed
        modifies Repr
        ensures  Valid()
        ensures  fresh(Repr - old(Repr) - {grinder} - grinder.Repr) // [2.] Specification changed
    {
        assert this !in grinder.Repr;
        g := grinder;
        ready := g.hasBeans && w.waterLevel != 0;
        Repr := Repr + {g};
        Repr := Repr + g.Repr;
    }



    method RemoveGrinder() returns (g' : Grinder)
        requires Valid()
        modifies Repr
        // ensures  Valid()
        // ensures  fresh(Repr - old(Repr))
        // ensures  g'.Valid()
        // ensures  g'.Repr !! Repr
        // ensures  g' == old(g)
        // ensures  ready == false
        // ensures  g' in old(Repr) - Repr
        ensures  Valid()
        ensures  fresh(Repr - old(Repr))
        ensures  ready == false
        ensures  g'.Valid()
        ensures  g' in old(Repr) - Repr
        ensures  g'.Valid() //????????????
    {
        g' := g;
        Repr := Repr - g'.Repr;
        g := new Grinder();
        Repr := Repr + g.Repr;
        ready := false;
    }
}

method CoffeeTestHarness() { 
	var cm := new CoffeeMaker(); 
	cm.Restock(); 
	cm.Dispense();
}



method RemoveGrinderHarness() {
    var cm := new CoffeeMaker();
    var grinder := cm.RemoveGrinder();
    cm.Restock();
    grinder.AddBeans();
}