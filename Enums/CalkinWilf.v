(* begin hide *)
Require Import CoList.
Require Import CoTree.
Require Import PArith.
Require Import QArith.
(* end hide *)

(** * Enumerating The Rationals: The Calkin-Wilf Tree *)

(** _Current Status: while the implementation of the tree and the deforestation
    algorithm function perfectly, and were easy to implement, we haven't acutally
    had the time to investigate proving anything with regard to our implementation_.
  *)
  
(** The third approach of enumerating the rationals explored in the paper is the
    construction and deforestation of the Calkin-Wilf tree.
    
    The Calkin-Wilf tree maps all levels in the Stern-Brocot tree to their
    bit-reversal permutation.
    
  #
    <img style="width:100%;" alt="The Calkin-Wilf Tree" src="calkin_wilf.png" />
  #
  
    Below we will construct the Calkin-Wilf tree.
  *)

Module CalkinWilf.

  Local Open Scope positive_scope.
  
  (** The algorithm used to construct the Calkin-Wilf tree in the paper can be
      seen below. It trivially translates to Coq, because it avoids all [0]'s,
      and therefore we have no issues constructing rationals. Furthermore, it is
      in itself much simpler.
<<
    rats6 :: [Rational]
    rats6 = bf (unfold next (1, 1))
      where next (m, n) = (m / n, (m, m + n), (n + m, n))
>>
      Our translation of the algorithm can be seen below.
    *)

  Definition next (q:positive*positive) : (positive*positive)*Q*(positive*positive) :=
      match q with
        | (m,n) => ((m,m + n),Zpos m # n,(m + n,n))
      end.
  
  Definition tree : cotree Q := CoTree.unfold next (1,1).
  
  Definition enum : colist Q := CoTree.bf tree.

End CalkinWilf.