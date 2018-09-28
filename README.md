# Divide and Conquer in Agda

created by Eva Richter, Matti Richter April 2018

This repositiory implements the divide and donquer programming scheme as described by  Douglas R. Smith in "The Design of Divide and Conquer Algorithms", 1984 in Agda. 

The module DivideEtImpera realizes the implementation of the scheme as described in the paper, as well as a second version which is very similar, but features a second recursive call of the algorithm. It seemed to us that this second version is actually divide and conquer, whereas the first version simply describes a general recursive algorithm with a single recursive call (i. e. no real "divide" part).

The algorithms scheme consists of a single big function, which requires a series of inputs such as a well founded relation upon which the recursion is done, a "directly solve" function, a "decompose" function, a "compose" function and proofs, that all of these functions fulfill certain conditions. It then returns a functions which guarantees certain output conditions, given certain input conditions.

The modules Quicksort and Mergesort then implement all of these small parts for the respective algorithms (quicksort and mergesort), and use the scheme to build sorting algorithms for lists. In the proofs of these modules, the contens of lists were compared with a notion of bag equivalence which Niels Anders Danielsson described in his paper "Bag Equivalence via a Proof-Relevant Membership Relation".

The module Equivalence contains some basic syntax for equational reasoning with equality, equivalence, and one-to-one correspondence of sets. 

The module BagEquality contains the notion of bag equivalence as described in the paper by Danielsson and also just reimplements parts of the code he presented in the paper.

The module Lists establishes a relation on litst by their length, and proves it's wellfoundedness. It also introduces a notion of an ordered list, and two different notions of what it means for a list to be primitive (one for quicksort, one for mergesort), and proves their decidability.

The modules Quicksort and Mergesort then use the preparations in the other modules to define "compose", "decompose" etc. for the two algorithms and prove all necessary properties. Finally, the divide and conquer scheme is use to created sorting functions on lists, which are guaranteed to resturn a sprted list with the same content as the input.  

