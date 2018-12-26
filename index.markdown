---
layout: default
title: About
---

__Math classes__ is a library of abstract interfaces for mathematical
structures, such as

 - Algebraic hierarchy (groups, rings, fields, ...)
 - Relations, orders, ...
 - Categories, functors, universal algebra, ...
 - Numbers: ℕ, ℤ, ℚ, ...
 - Operations, (shift, power, abs, ...)

It is heavily based on Coq's new type classes in order to provide:
structure inference, multiple inheritance/sharing, convenient algebraic
manipulation (e.g. rewriting) and idiomatic use of notations.

Here is a SVG diagram showing all files and their dependencies with
links to the coqdoc
[dependencies](http://robbertkrebbers.nl/math-classes.svg).

Here are two diagrams showing the main components of the algebraic
hierarchy and the various orders in math classes.

![Algebraic Hierarchy](hierarchy.png)
![Order Hierarchy](orders.png)

Math classes is used in [C-CoRN](http://corn.cs.ru.nl) to implement high
performance exact real number arithmetic.

## Install
Add the [Coq repository](coq.io/opam/):

    opam repo add coq-released https://coq.inria.fr/opam/released

and run:

    opam install coq-math-classes
