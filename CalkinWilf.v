Require Import CoList.
Require Import CoTree.
Require Import PArith.
Require Import QArith.

(** ** The Calkin-Wilf Tree *)
Module CalkinWilf.

  Local Open Scope positive_scope.

  Definition next (q:positive*positive) : (positive*positive)*Q*(positive*positive) :=
      match q with
        | (m,n) => ((m,m + n),Zpos m # n,(m + n,n))
      end.
  
  Definition tree : cotree Q := CoTree.unfold next (1,1).
  
  Definition enum : colist Q := CoTree.bf tree.

End CalkinWilf.