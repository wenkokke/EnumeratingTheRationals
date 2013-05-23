Require Import List.

Inductive tree (A: Type) :=
  | leaf : tree A
  | node : tree A -> A -> tree A -> tree A.

Fixpoint tree_fold {A B: Type} (f: (B*A*B) -> B) (e: B) (t: tree A) : B :=
  match t with
  | leaf       => e
  | node l x r => f (tree_fold f e l, x, tree_fold f e r)
  end.

CoInductive colist (A: Type) :=
  | cocons : A -> colist A -> colist A.

CoFixpoint colist_unfold {A B: Type} (f: B -> (A*B)) (e: B) : colist A :=
  match f e with
  | (x,xs) => cocons _ x (colist_unfold f xs)
  end.

Fixpoint colist_take {A: Type} (n: nat) (xs: colist A) : list A :=
  match n with
    | O => nil
    | S n =>
      match xs with
        | cocons x xs => cons x (colist_take n xs)
      end
  end.

CoInductive cotree (A: Type) :=
  | conode : cotree A -> A -> cotree A -> cotree A.

CoFixpoint cotree_unfold {A B: Type} (f: B -> (B*A*B)) (e: B) : cotree A :=
  match f e with
  | (l,x,r) => conode _ (cotree_unfold f l) x (cotree_unfold f r)
  end.

CoFixpoint cotree_bf_acc {A: Type} (ts: list (cotree A)) : ts<>nil -> colist A.
  refine (match ts as xs return xs<>nil -> colist A with
    | nil =>
      fun h => _
    | cons t ts =>
      fun h  => 
        match t with
          | conode l x r => cocons _ x (cotree_bf_acc _ (ts ++ (cons l (cons r nil))) _)
        end
  end).
  exfalso; apply h; reflexivity.
  apply not_eq_sym; apply app_cons_not_nil.
Defined.

Definition cotree_bf {A: Type} (t: cotree A) : colist A.
  refine (cotree_bf_acc (t :: nil) _).
  apply not_eq_sym; apply nil_cons.
Defined.

(** **** CoTrees of Rational Numbers *)

Require Import PArith.
Require Import NArith.
Require Import QArith.

(** **** The Calkin-Wilf Tree *)

Definition calkin_wilf_step (q:positive*positive) : (positive*positive)*Q*(positive*positive) :=
  match q with
    | (m,n) => ((m,(m + n)%positive),Qmake (Zpos m) n,((m + n)%positive,n))
  end.

Definition calkin_wilf_tree : cotree Q := cotree_unfold calkin_wilf_step (1,1)%positive.

Definition calkin_wilf_enum : colist Q := cotree_bf calkin_wilf_tree.

Eval compute in colist_take 10 calkin_wilf_enum.

(** **** The Stern-Brocot Tree *)

Definition N_pos (n:N) : n<>N0 -> positive.
  refine (match n as n' return n'<>N0 -> positive with
            | N0     => fun h => _
            | Npos p => fun h => p
          end).
  exfalso; apply h; reflexivity.
Defined.

Definition N_Z (n:N) : Z :=
  match n with
    | N0     => Z0 
    | Npos n => Zpos n
  end.

Lemma Npos_over_Nplus_l : forall n m : N,
  n <> N0 -> (n + m)%N <> N0.
Proof.
  intros n m H.
  destruct n as [|n].
  - exfalso; apply H; reflexivity.
  - destruct m as [|m].
    * simpl; assumption.
    * simpl; discriminate.
Qed.

Lemma Npos_over_Nplus_r : forall n m : N,
  m <> N0 -> (n + m)%N <> N0.
Proof.
  intros n m.
  rewrite Nplus_comm.
  apply Npos_over_Nplus_l.
Qed.

Lemma Npos_over_Nplus : forall n m : N,
  (n <> N0 \/ m <> N0) -> (n + m)%N <> N0.
Proof.
  intros n m H.
  elim H.
  - apply Npos_over_Nplus_l.
  - apply Npos_over_Nplus_r.
Qed.

Inductive stern_brocot_pair : Type :=
| Qpair (lm ln rm rn : N) (HL: lm<>N0 \/ rm<>N0) (HR: ln<>N0 \/ rn<>N0) : stern_brocot_pair.

Definition stern_brocot_step (q:stern_brocot_pair) : stern_brocot_pair*Q*stern_brocot_pair.
  refine (match q with
            | Qpair a b c d HL HR =>
              let ac := (a + c)%N in
              let bd := (b + d)%N in
              let l  := Qpair a  b  ac bd _ _ in
              let r  := Qpair ac bd  c  d _ _ in
              let q  := Qmake (N_Z ac) (N_pos bd _) in
              (l,q,r)
          end).
  - right; unfold ac; apply Npos_over_Nplus in HL; assumption.
  - right; unfold bd; apply Npos_over_Nplus in HR; assumption.
  - left ; unfold ac; apply Npos_over_Nplus in HL; assumption.
  - left ; unfold bd; apply Npos_over_Nplus in HR; assumption.
  - unfold bd; apply Npos_over_Nplus in HR; assumption.
Qed.

Definition stern_brocot_tree : cotree Q.
  refine (cotree_unfold stern_brocot_step (Qpair 0 1 1 0 _ _)%N).
  - right; discriminate.
  - left ; discriminate.
Qed.

Definition stern_brocot_enum : colist Q := cotree_bf stern_brocot_tree.

(** there's something funny going on here *)

Definition test_stern_brocot_step1 : stern_brocot_pair*Q*stern_brocot_pair.
Proof.
  refine (stern_brocot_step (Qpair 0 1 1 0 _ _)%N).
  - right; discriminate.
  - left ; discriminate.
Defined.

Eval compute in test_stern_brocot_step1.
