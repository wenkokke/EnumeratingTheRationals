Enumerating The Rationals
=========================

In this repository I present a formalization of the functional pearl ["Enumerating the Rationals"][paper-url] by Gibbons, Lester and Bird in Coq.

My approach is divided into two parts:

  1. implement the primitives for reasoning about codata;
  2. implement the enumerations discussed in the paper.
  
Each module is implemented in literal Coq, and contains further documentation.
  
Data and CoData
-------------------------

There aren't many theories regarding CoData (or CoInductives) in Coq's standard library.
Because of this, I've implemented several structures myself. These packages can be found
in the `CoData` directory.

First of all, I've implemented a library for reaoning about CoLists, based on Coq's Stream
datatype. I've adapted the names to match better with the similar constructs for lists,
and implemented several theories regarding membership, concatination and the relation with
finite lists.
For more on CoLists see [the CoList module][colists].

Secondly, I've implemented a library for reaoning about CoTrees. This libary was written from
the ground up, and includes many of the same structures as the CoList module. Aside from this,
it also includes several theories that will be especially usefull when implementing the
enumerations from the paper, such as breath-first traversal.
For more on CoTrees see [the CoTree module][cotrees].

Lastly, I've implemented a small extension over the standard List module, which can be found
in the `Data` directory. For more on this, see [the List module][lists].

The Naive Tree
-------------------------

Our very first attempt is not discussed in the paper, but was written to test the `CoTree` module.
It describes a tree of rational numbers, where branching to the left means an increase in numerator
and branching to the right means an increase in the denominator.

It is simple to see that this tree contains all rational numbers, and it in fact many, many duplicates.

While we had little trouble construcing this tree, and subsequently in deconstructing it to an enumeration,
it already proved quite hard to prove some simple properties with regard to this tree.

For more on this approach see [the NaiveTree module][naivetree].

The Naive Enumeration
-------------------------

The first formalisation of an algorithm disussed in the paper involves deforesting the matrix in which,
much as in the previous approach, moving to the next column increases the numerator and moving to the
next row increases the denominator.

It is simple to see that this matrix contains all rational numbers, but the problem here is that it still
contains pairs of rationals that reduce to one another.

We have adapted the algorithm that generates the deforested matrix directly, but this already proved quite
the challenge, and it involves a concatination of a colist of lists, which is only possible if we know
for certain that eventually we will encounter a nonempty list.

For more on this approach see [the NaiveEnum module][naiveenum].

The Stern-Brocot Tree
-------------------------

The second formalisation involves deforesting the Stern-Brocot tree, which exploits the relation between
the execution trace of Eulid's GCD algorithm and its usage in the reduction of rational numbers.

We have adapted the algorithm that generates the tree using a stepper function, and have attempted to
prove several properties with regard to this implementation. Furthermore, we have implemented a GCD
function that records its trace, and have attempted to prove several claims made in the paper with
regards to this algorithm.

For more on this approach see [the SternBrocot module][sternbrocot].

The Calkin-Wilf Tree
-------------------------

The last formalisation involves a direct construction of the Calkin-Wilf tree. Though we haven't had the
time to prove much with regards to this tree, it's construction was too simple not to include.

For more on this approach see [the CalkinWilf module][calkinwilf].

[paper-url]: http://www.cs.ox.ac.uk/people/jeremy.gibbons/publications/rationals.pdf
[colists]: doc/CoList.html
[cotrees]: doc/CoTree.html
[lists]: doc/List.html
[naivetree]: doc/NaiveTree.html
[naiveenum]: doc/NaiveEnum.html
[sternbrocot]: doc/SternBrocot.html
[calkinwilf]: doc/CalkinWilf.html