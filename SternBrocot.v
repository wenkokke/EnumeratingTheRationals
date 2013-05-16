Require Import Coq.Init.Peano.
Require Import Coq.Arith.Arith.

CoInductive Tree (a: Type) :=
| Node (l: Tree a) (x: a) (r: Tree a).

CoFixpoint unfold (A B: Type) (f: B -> (B*A*B)) (x: B) : Tree A :=
match f x with
| (l,x,r) => Node A (unfold _ _ f l) x (unfold _ _ f r)
end.

Inductive rat :=
| Q (n: nat) (d: nat) (H: d > 0) : rat.

Notation "n # d" := (Q n d _) (at level 40, left associativity).

Definition next (l r : nat*nat) :=
match l,r with
| (l0,l1),(r0,r1) => (l0+r0,l1+r1)
end.

Lemma next_d : forall l0 l1 r0 r1 n d : nat,
  (n,d) = next (l0,l1) (r0,r1) -> d = l1 + r1.
Proof.
  intros l0 l1 r0 r1 n d H.
  unfold next in H.
  apply (f_equal (@snd _ _)) in H.
  simpl in H.
  assumption.
Qed.

Theorem next_d_gt_0 : forall l0 l1 r0 r1 n d : nat,
  ((n,d) = next (l0,l1) (r0,r1)) /\ (l1 > 0 \/ r1 > 0) -> d > 0.
Proof.
  intros l0 l1 r0 r1 n d H.
  unfold next in H.
  decompose [and] H.
  elim H1.
  - intros H2.
    destruct l1 as [|l1].
    * apply gt_irrefl in H2. inversion H2.
    * apply next_d in H0. rewrite H0. simpl. apply gt_Sn_O.
  - intros H2.
    destruct r1 as [|r1].
    * apply gt_irrefl in H2. inversion H2.
    * apply next_d in H0. rewrite H0. rewrite plus_comm. simpl. apply gt_Sn_O.
Qed.


