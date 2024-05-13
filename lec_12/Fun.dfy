/* SECTION: Example for List<T> */
datatype List<T> = Nil | Cons(head : T, tail : List<T>)

method ListTestHarness() {
    var gamer := List<int -> bool>.Nil;
    assert gamer == Nil;
    var gamer2 := Cons(IsZero, Nil);
    assert gamer2.head == IsZero;
    assert forall x :: gamer2.head(x) == IsZero(x);
    // assert gamer2.head != IsOne;                     // assertion fails
    // assert exists x :: gamer2.head(x) != IsOne(x);   // assertion fails
    // var inf := Cons(1, inf);                         // unresolved identifier
}

function IsZero(x : int) : bool
{
    x == 0
}

function IsOne(x : int) : bool
{
    x == 1
}



/* SECTION: match */
predicate IsEmpty'<T>(xs : List<T>)
{
    match xs
    case Nil        => true
    case Cons(_,_)  => false
}



/* SECTION: Destructors */
function GetHead<T> (xs : List<T>) : T
    requires xs.Cons?   // >> .Cons? << returns true iff xs constructed by >>Cons<<
{
    match xs
    case Cons(x, _) => x
}

function IsEmpty<T> (xs : List<T>) : bool
{
    xs.Nil?
}

function Length<T> (xs : List<T>) : nat
{
    match xs
    case Nil =>             0
    case Cons(_, tail) =>   1 + Length(tail)
}

// Cons<T> backwards
function Snoc<T> ( xs : List<T>, x : T ) : List<T>
{
    match xs
    case Nil =>             Cons(x, Nil)
    case Cons(x', tail) =>  Cons(x', Snoc(tail, x))
}

lemma LengthSnoc<T> ( xs : List<T> , x : T )
    ensures Length(Snoc(xs, x)) == Length(xs) + 1
{}

function Foldr<S, T> ( update : (S, T) -> T, base : T, list : List<S> ) : T
{
    match list
    case  Nil           =>  base
    case  Cons(x, xs)   =>  update(x, Foldr(update, base, xs))
}




/* SECTION: Extrinsic and intrinsic properties */
/*  Def. (Intrinsic property of a function)
        For a function >>f<<, an *intrinsic* property of it is one     in its >>ensures<< clause.
        NOTE:   These are known to Dafny any time >>f<< is invoked.
    Def. (Extrinsic property of a function)
        For a function >>f<<, an *extrinsic* property of it is one NOT in its >>ensures<< clause.
        NOTE:   These are NOT known to Dafny any time >>f<< is invoked. Such a property needs to be in
                a >>lemma<<, and said >>lemma<< must be called to use this property.
    NOTE:   Having lots of >>ensures<< clauses is expensive for Dafny's verifier. Usually, we factor
            things into >>lemma<<s, only leaving things in >>ensures<< clauses if they're gonna be used
            practically *every time* that the function is called.
*/

function Append<T> (xs : List<T>, ys : List<T>) : List<T>
    ensures Length(Append(xs, ys)) == Length(xs) + Length(ys)           // NOTE: Intrinsic property!
{
    match xs
    case  Nil          =>   ys
    case  Cons(x, xs') =>   Cons(x, Append(xs', ys))
}

lemma AssocAppend<T> (xs : List<T>, ys : List<T>, zs : List<T>)
    ensures Append(xs, Append(ys, zs)) == Append(Append(xs, ys), zs)    // NOTE: Extrinsic property!
{}

/** Linear search.
    Returns:
        Length(xs) iff y not present in xs
        First index in xs at which y is found, else.
 */
function Find<T(==)> ( xs : List<T>, y : T ) : nat
    ensures Find(xs, y) <= Length(xs)                                   // NOTE: Intrinsic property!
{
    match xs
    case  Nil => 
        0
    case  Cons(x, tail) =>
        if x == y
        then 0
        else 1 + Find(tail, y)
}

lemma FindAppend<T> ( xs : List<T> , ys : List<T> , z : T )
    ensures Find(xs, z) != Length(xs) ==> Find(Append(xs, ys), z) == Find(xs, z)
{}



/* SECTION: Insertion sort */

function InsertionSort(xs : List<int>) : List<int>
{
    match xs
    case  Nil => Nil
    case  Cons(x, tail) => Insert(x, InsertionSort(tail))
}

function Insert(i : int, xs : List<int>) : List<int>
{
    match xs
    case  Nil => 
        Cons(i, Nil)
    case  Cons(x, tail) =>
        if i < x
        then    Cons(i, xs)
        else    Cons(x, Insert(i, tail))
}

predicate Ordered(xs : List<int>)
{
    match xs
    case  Nil => 
        true
    case  Cons(_, Nil) =>
        true
    case  Cons(x, Cons(y, _)) =>
        x <= y
        && Ordered(xs.tail)
}

lemma InsertionSortSorts(xs : List<int>)
    ensures Ordered(InsertionSort(xs))
{
    match xs
    case  Nil =>
        // Empty proof; Dafny can figure this out
    case  Cons(x, tail) => 
        // Non-empty proof.
        InsertionSorts(x, InsertionSort(tail));
}

lemma InsertionSorts(i : int, xs : List<int>)
    requires Ordered(xs)
    ensures  Ordered(Insert(i, xs))
{}

function Count<T(==)>(xs : List<T>, v : T) : int
{
    match xs
    case  Nil => 0
    case  Cons(x, tail) =>
        (if x == v then 1 else 0) + Count(tail, v)
}

lemma InsertionSortSameElements(xs : List<int>, p : int)
    ensures Count(xs, p) == Count(InsertionSort(xs), p)
{
    match xs
    case  Nil =>
        // Empty proof
    case  Cons(x, xs') =>
        InsertionSortSorts(xs'); // ensures Ordered(InsertionSort(xs'))
        InsertSameElements(x, InsertionSort(xs'), p); // ^^ is a precondition for this call
}

lemma InsertSameElements(x : int, xs : List<int>, p : int)
    requires Ordered(xs)
    ensures  Count(Cons(x, xs), p) == Count(Insert(x, xs), p)
{}



/* SECTION: Binary search tree */
datatype Tree<Data> = 
        Empty
    |   Leaf(key : int, value : Data)
    |   Tree(key : int, value : Data, left : Tree, right : Tree)

datatype Maybe<T> = 
        Nothing
    |   Just(T)

function Lookup<Data> (key : int, t : Tree<Data>) : Maybe<Data>
    decreases t     // NOTE: Dafny has a default >>decreases<< for inductive data types. 
                    //       This >>decreases<< is "number of constructors".
{
    match t
    case  Empty =>
        Nothing
    case  Leaf(k, v) =>
        if k == key
        then    Just(v)
        else    Nothing
    case  Tree(k, v, left, right) =>
        if k == key
        then    Just(v)
        else    if key < key
                then    Lookup(k, left)
                else    Lookup(k, right)
}

function Add<Data> (key : int, value : Data, t : Tree<Data>) : Tree<Data>
{
    match t
    case  Empty =>
        Leaf(key, value)
    case  Leaf(k, v) =>
        if k == key
        then    Leaf(key, value)
        else if key < k
        then    Tree(k, v, Leaf(key, value), Empty)
        else    Tree(k, v, Empty, Leaf(key, value))
    case  Tree(k, v, left, right) =>
        if k == key
        then    Tree(k, value, left, right)
        else if key < k
        then    Tree(k, v, Add(key, value, left), right)
        else    Tree(k, v, left, Add(key, value, right))
}

predicate TreeOrdered<Data> (t : Tree<Data>)
{
    match t
    case  Empty =>
        true
    case  Leaf(_,_) =>
        true
    case  Tree(k, _, left, right) =>
        (left  != Empty ==>
            TreeOrdered(left)
            && left.key < k)
        && (right != Empty ==> 
            TreeOrdered(right)
            && k < right.key)
}

lemma AddLemma<Data> (k : int, v : Data, t : Tree<Data>)
    requires TreeOrdered(t)
    ensures  TreeOrdered(Add(k, v, t))
{}
