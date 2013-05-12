
Module Tree.

  CoInductive Tree (A: Type) : Type :=
  | Leaf : A -> Tree A
  | Node : Tree A -> A -> Tree A -> Tree A.

  CoFixpoint unfold (A B: Type) (f: B -> (B*A*B)) (x: B) : Tree A :=
    match f x with
      | (l,a,r) => Node A (unfold _ _ f l) a (unfold _ _ f r)
    end.

End Tree.


(** The Stern-Brocot Tree *)

Module SternBrocot.

  Theorem adj_ge_l : forall a b c d n m,
    (a > 0 \/ c > 0) /\ ((n,m) = adj (a,b) (c,d)) -> n > 0.
  
  Theorem adj_ge_r : forall a b c d n m,
    (b > 0 \/ d > 0) /\ ((n,m) = adj (a,b) (c,d)) -> m > 0.
  
  Definition adj (l r : N*N)
  Definition step s
  Definition tree : Tree Q

End SternBrocot.
