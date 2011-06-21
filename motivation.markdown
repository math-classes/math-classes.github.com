---
layout: default
title: Motivation
---

Introduction
------------

The aim of this project is to build theory and programs on top of
abstract interfaces instead of concrete implementations. This layer of
abstraction makes both proof engineering and programming more flexible:
it avoids duplication of code, it introduces a canonical way to refer to
operations and properties, both by names and notations, and it allows us
to easily swap different implementations of number representations and
their operations.

A prerequisite for this goal was to develop interfaces for:

 - Algebraic hierarchy (groups, rings, fields, ...)
 - Relations, orders, ...
 - Categories, functors, universal algebra, ...
 - Numbers: ℕ, ℤ, ℚ, ...
 - Operations, (shift, power, abs, ...)

Providing:

 - Structure inference
 - Multiple inheritance/sharing
 - Convenient algebraic manipulation (e.g. rewriting)
 - Idiomatic use of notations

Since all existing solutions (dependent records, packed classes
(Ssreflect) and modules) suffer from drawbacks we propose a new
solution: type classes! On this page we will try to explain the
difficulties involved and our solutions.

Interfaces for algebraic structures
-----------------------------------

Algebraic structures are expressed in terms of a number of carrier sets,
a number of relations and operations, and a number of laws that the
operations satisfy. One way of describing such a structure is by a
_bundled representation_: one uses a dependently typed record that
contains the carrier, operations and laws. For example a semigroup can
be represented as follows. (The fields `sg_car` and `sg_proper` support
our explicit handling of naive set theory in type theory.)

<pre>
Record SemiGroup : Type := { 
  sg_car :> Setoid ;
  sg_op : sg_car → sg_car → sg_car ;
  sg_proper : Proper ((=) ==> (=) ==> (=)) sg_op ;
  sg_ass : ∀ x y z, sg_op x (sg_op y z) = sg_op (sg_op x y) z) }
</pre>

However, this approach has some serious limitations, the most important
one being a lack of support for _sharing_ components. For example,
suppose we group together two `CommutativeMonoid`s in order to create a
`SemiRing`. Now awkward hacks are necessary to establish equality
between the carriers. A second problem is that if we stack up these
records to represent higher structures the projection paths become
increasingly long.

Historically these problems have been an acceptable trade-off because
_unbundled representations_, in which the carrier and operations
are parameterized, introduce even more problems.

<pre>
Record SemiGroup {A} (e : A → A → Prop) (sg_op : A → A → A) : Prop := { 
  sg_proper : Proper (e ==> e ==> e) sg_op ;
  sg_ass : ∀ x y z, e (sg_op x (sg_op y z)) (sg_op (sg_op x y) z) }
</pre>

There is nothing to bind notation to, no structure inference, and
declaring and passing requires too much manual bookkeeping. Spitters and
van der Weegen have proposed a use of Coq's new type class machinery
that resolves many of the problems of unbundled representations. Our
current experiment confirms that this is a viable approach.

An alternative solution is provided by packed classes which use an
alternative, and older, implementation of a semblance of type classes:
canonical structures. Yet another approach would be to use modules.
However, as these are not fist class, we would be unable to define,
e.g. homomorphisms between algebraic structures.

An _operational type class_ is defined for each operation and relation.

<pre>
Class Equiv A := equiv: relation A.
Infix "=" := equiv: type_scope.
Class RingPlus A := ring_plus: A → A → A.
Infix "+" := ring_plus.
</pre>

Now an algebraic structure is just a type class living in `Prop` that
is parametrized by its carrier, relations and operations. This class
contains all laws that the operations should satisfy. Since the
operations are unbundled we can easily support sharing. For example let
us consider the `SemiRing` interface.

<pre>
Class SemiRing A {e : Equiv A} {plus: RingPlus A} 
   {mult: RingMult A} {zero: RingZero A} {one: RingOne A} : Prop := { 
  semiring_mult_monoid :> @CommutativeMonoid A e mult one ;
  semiring_plus_monoid :> @CommutativeMonoid A e plus zero ;
  semiring_distr :> Distribute (.*.) (+) ;
  semiring_left_absorb :> LeftAbsorb (.*.) 0 }.
</pre>

Without type classes it would be a burden to manually carry around the
carrier, relations and operations. However, because these parameters are
just type class instances, the type class machinery will perform that
job for us. For example,

<pre>
Lemma example `{SemiRing R} x : 1 * x = x + 0.
</pre>

The backtick instructs Coq to automatically insert implicit
declarations, namely `e plus mult zero one`. It also lets us omit a name
for the `SemiRing R` parameter itself. All of these parameters will be
given automatically generated names that we will never refer to.
Furthermore, instance resolution will automatically find instances of
the operational type classes for the written notations. Thus the above
is really:

<pre>
Lemma example {R e plus mult zero one} {P : @SemiRing R e plus mult zero one} x :
  @equiv R e
    (@ring_mult R mult (@ring_one R one) x)
    (@ring_plus R plus x (@ring_zero R zero)).
</pre>

The syntax `:>` in the definition of `SemiRing` declares certain fields
as substructures.

Defining instances
------------------

Proving that an actual structure is an instance of the
`SemiRing` interface is straightforward. First we define
instances of the operational type classes.

<pre>
Instance nat_equiv: Equiv nat := eq.
Instance nat_plus: RingPlus nat := plus.
Instance nat_0: RingZero nat := 0%nat.
Instance nat_1: RingOne nat := 1%nat.
Instance nat_mult: RingMult nat := mult.
</pre>

Here we see that instances are just ordinary constants of the class
types. However, we use the `Instance` keyword instead of `Definition` to
let the type class machinery register the instance. Now, to prove that
the Peano naturals are in fact a semiring, we just write:

<pre>
Instance: SemiRing nat.
Proof.   ...   Qed.
</pre>

Example: ℕ
----------

This approach to interfaces proved useful to formalize a standard
algebraic hierarchy. For example,combined with category theory and
universal algebra, ℕ and ℤ are represented as interfaces specifying an
initial semiring and initial ring.

<pre>
Class NaturalsToSemiRing (A : Type) :=
  naturals_to_semiring: ∀ B `{RingMult B} `{RingPlus B} `{RingOne B} `{RingZero B}, A → B.
Class Naturals A {e plus mult zero one} `{U: NaturalsToSemiRing A} :=  {
  naturals_ring :> @SemiRing A e plus mult zero one;
  naturals_to_semiring_mor :> ∀ `{SemiRing B}, SemiRing_Morphism (naturals_to_semiring A B);
  naturals_initial :> Initial (semirings.object A) }.
</pre>


<!--
These abstract interfaces for the naturals and integers make it easier
to change the concrete representation in the future.  No such simple
specification for ℚ seems to exists, so we choose to specify it as the
field of fractions of ℤ. More precisely, ℚ is specified as a field
containing ℤ that moreover can be embedded into the field of fractions
of ℤ.

<pre>
Inductive Frac R `{e : Equiv R} `{zero : RingZero R} : Type := 
  frac { num : R ; den : R ; den_nonzero : den ≠ 0 }.
Class RationalsToFrac (A : Type) := rationals_to_frac : ∀ B `{Integers B}, A → Frac B.
Class Rationals A {e plus mult zero one opp inv} `{U : !RationalsToFrac A} : Prop :=  { 
  rationals_field :> @DecField A e plus mult zero one opp inv ; 
  rationals_frac :> ∀ `{Integers Z}, Injective (rationals_to_frac A Z) ; 
  rationals_frac_mor :> ∀ `{Integers Z}, SemiRing_Morphism (rationals_to_frac A Z) ; 
  rationals_embed_ints :> ∀ `{Integers Z}, Injective (integers_to_ring Z A) }.
</pre>
-->
