(** * Enumerating The Rationals *)

Require Import List.
Require Import Streams.
Require Import PArith.
Require Import NArith.
Require Import QArith.

(** ** Datatypes: Trees and CoTrees *)

(** *** CoLists *)

Module CoLists.

  Definition colist := Stream.
  Definition cocons := Cons.

  CoFixpoint unfold {A B: Type} (f: B -> (A*B)) (e: B) : colist A :=
    match f e with
      | (x,xs) => cocons _ x (unfold f xs)
    end.
  
  Fixpoint take {A: Type} (n: nat) (xs: colist A) : list A :=
    match n with
      | O => nil
      | S n =>
        match xs with
          | cocons x xs => cons x (take n xs)
        end
    end.

End CoLists.

(** Import [CoLists.colist] into the local scope. *)
Definition colist := CoLists.colist.
Definition cocons := CoLists.cocons.
  
(** *** CoTrees *)
Module CoTrees.

  CoInductive cotree (A: Type) :=
  | conode : cotree A -> A -> cotree A -> cotree A.

  CoFixpoint unfold {A B: Type} (f: B -> (B*A*B)) (e: B) : cotree A :=
    match f e with
      | (l,x,r) => conode _ (unfold f l) x (unfold f r)
    end.
  
  CoFixpoint bf_acc {A: Type} (ts: list (cotree A)) : ts<>nil -> colist A.
    refine (match ts as xs return xs<>nil -> colist A with
              | nil =>
                fun h => _
              | cons t ts =>
                fun h  => 
                  match t with
                    | conode l x r => cocons _ x (bf_acc _ (ts ++ (cons l (cons r nil))) _)
                  end
            end).
    exfalso; apply h; reflexivity.
    apply not_eq_sym; apply app_cons_not_nil.
  Defined.
  
  Definition bf {A: Type} (t: cotree A) : colist A.
    refine (bf_acc (t :: nil) _).
    apply not_eq_sym; apply nil_cons.
  Defined.

  Definition hd {A: Type} (t: cotree A) : A :=
    match t with
      | conode _ x _ => x
    end.
  
  Definition left {A: Type} (t: cotree A) : cotree A :=
    match t with
      | conode l _ _ => l
    end.
  
  Definition right {A: Type} (t: cotree A) : cotree A :=
    match t with
      | conode _ _ r => r
    end.

  CoInductive cotree_eq {A: Type} : cotree A -> cotree A -> Prop :=
  | conode_eq : forall x l1 r1 l2 r2,
    cotree_eq l1 l2
    -> cotree_eq r1 r2
    -> cotree_eq (conode _ l1 x r1) (conode _ l2 x r2).

  Theorem cotree_eq_hd : forall {A: Type} (t1 t2: cotree A), cotree_eq t1 t2 -> hd t1 = hd t2.
    intros A t1 t2 H; destruct H; reflexivity.
  Qed.

  Theorem cotree_eq_left : forall {A: Type} (t1 t2: cotree A), cotree_eq t1 t2 -> cotree_eq (left t1) (left t2).
    intros A t1 t2 H; destruct H; simpl; assumption.
  Qed.

  Theorem cotree_eq_right : forall {A: Type} (t1 t2: cotree A), cotree_eq t1 t2 -> cotree_eq (right t1) (right t2).
    intros A t1 t2 H; destruct H; simpl; assumption.
  Qed.

  Section cotree_eq_coind.
    Variable A: Type.
    Variable R: cotree A -> cotree A -> Prop.
    
    Hypothesis cotree_case_hd    : forall t1 t2, R t1 t2 -> hd t1 = hd t2.
    Hypothesis cotree_case_left  : forall t1 t2, R t1 t2 -> R (left t1) (left t2).
    Hypothesis cotree_case_right : forall t1 t2, R t1 t2 -> R (right t1) (right t2).
    
    Theorem cotree_eq_coind : forall t1 t2: cotree A, R t1 t2 -> cotree_eq t1 t2.
      cofix.
      destruct t1 as [l1 x1 r1].
      destruct t2 as [l2 x2 r2].
      intro H.
      generalize H; intro Heq.
      apply cotree_case_hd in Heq; simpl in Heq; rewrite Heq.
      constructor.
      - apply cotree_case_left in H; simpl in H.
        apply cotree_eq_coind; assumption.
      - apply cotree_case_right in H; simpl in H.
        apply cotree_eq_coind; assumption.
    Qed.
  End cotree_eq_coind.
  
  Theorem cotree_eq_refl : forall {A: Type} (t: cotree A), cotree_eq t t.
    intros A t.
    apply (cotree_eq_coind A (fun t1 t2 => t1 = t2)).
    - intros t1 t2 H; rewrite H; reflexivity.
    - intros t1 t2 H; rewrite H; reflexivity.
    - intros t1 t2 H; rewrite H; reflexivity.
    - reflexivity.
  Qed.

  Theorem cotree_eq_sym : forall {A: Type} (t1 t2: cotree A), cotree_eq t1 t2 -> cotree_eq t2 t1.
    cofix.
    intros A t1 t2 H.
    destruct t1 as [l1 x1 r1].
    destruct t2 as [l2 x2 r2].
    generalize H; intro Heq; apply cotree_eq_hd in Heq; simpl in Heq.
    rewrite <- Heq.
    constructor.
    - apply cotree_eq_left in H; simpl in H.
      generalize H; apply cotree_eq_sym.
    - apply cotree_eq_right in H; simpl in H.
      generalize H; apply cotree_eq_sym.
  Qed.

  Theorem cotree_eq_trans : forall {A: Type} (t1 t2 t3: cotree A), cotree_eq t1 t2 -> cotree_eq t2 t3 -> cotree_eq t1 t3.
    cofix.
    intros A t1 t2 t3 H12 H23.
    destruct t1 as [l1 x1 r1].
    destruct t2 as [l2 x2 r2].
    destruct t3 as [l3 x3 r3].
    generalize H12; intro Heq12; apply cotree_eq_hd in Heq12; simpl in Heq12.
    generalize H23; intro Heq23; apply cotree_eq_hd in Heq23; simpl in Heq23.
    rewrite <- Heq23, <- Heq12.
    constructor.
    - apply cotree_eq_left in H12; simpl in H12.
      apply cotree_eq_left in H23; simpl in H23.
      generalize H12 H23.
      apply cotree_eq_trans.
    - apply cotree_eq_right in H12; simpl in H12.
      apply cotree_eq_right in H23; simpl in H23.
      generalize H12 H23.
      apply cotree_eq_trans.
  Qed.

  Inductive cotree_exists {A: Type} (P: cotree A -> Prop) (t: cotree A) : Prop :=
  | here    : P t -> cotree_exists P t
  | further : cotree_exists P (left t) -> cotree_exists P (right t) -> cotree_exists P t.
  
  CoInductive cotree_forall {A: Type} (P: cotree A -> Prop) (t: cotree A) : Prop :=
  | always  : P t -> cotree_forall P (left t) -> cotree_forall P (right t) -> cotree_forall P t.

End CoTrees.

(** Import [CoTrees.cotree] into local scope. *)
Definition cotree := CoTrees.cotree.
Definition conode := CoTrees.conode.
    
(** ** CoTrees of Rational Numbers *)
    
(** *** The Calkin-Wilf Tree *)
Module CalkinWilf.

  Definition step (q:positive*positive) : (positive*positive)*Q*(positive*positive) :=
    match q with
      | (m,n) => ((m,(m + n)%positive),Zpos m # n,((m + n)%positive,n))
    end.
  
  Definition tree : cotree Q := CoTrees.unfold step (1,1)%positive.
  
  Definition enum : colist Q := CoTrees.bf tree.
  
  Eval compute in CoLists.take 10 enum.
  
End CalkinWilf.

(** *** The Stern-Brocot Tree *)
Module SternBrocot.

  (** **** Additional Proofs on Natural Numbers *)
  
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
    (n <> 0 -> n + m <> 0)%N.
  Proof.
    intros n m H.
    destruct n as [|n].
    - exfalso; apply H; reflexivity.
    - destruct m as [|m].
      * simpl; assumption.
      * simpl; discriminate.
  Qed.
  
  Lemma Npos_over_Nplus_r : forall n m : N,
    (m <> 0 -> n + m <> 0)%N.
  Proof.
    intros n m.
    rewrite Nplus_comm.
    apply Npos_over_Nplus_l.
  Qed.
  
  Lemma Npos_over_Nplus : forall n m : N,
    (n <> 0 \/ m <> 0 -> n + m <> 0)%N.
  Proof.
    intros n m H.
    elim H.
    - apply Npos_over_Nplus_l.
    - apply Npos_over_Nplus_r.
  Qed.

  (** **** Construction of the Tree *)

  Inductive Qpair : Type :=
  | qpair (a b c d : N) (HL: a<>0%N \/ c<>0%N) (HR: b<>0%N \/ d<>0%N) : Qpair.

  Definition step (q:Qpair) : Qpair*Q*Qpair.
    refine (match q with
              | qpair a b c d HL HR =>
                let ac := (a + c)%N in
                let bd := (b + d)%N in
                let l  := qpair a  b  ac bd _ _ in
                let r  := qpair ac bd  c  d _ _ in
                let q  := N_Z ac # N_pos bd _ in
                (l,q,r)
            end).
    - right; unfold ac; apply Npos_over_Nplus in HL; assumption.
    - right; unfold bd; apply Npos_over_Nplus in HR; assumption.
    - left ; unfold ac; apply Npos_over_Nplus in HL; assumption.
    - left ; unfold bd; apply Npos_over_Nplus in HR; assumption.
    - unfold bd; apply Npos_over_Nplus in HR; assumption.
  Defined.

  Definition tree : cotree Q.
    refine (CoTrees.unfold step (qpair 0 1 1 0 _ _)%N).
    - right; discriminate.
    - left ; discriminate.
  Defined.
  
  Definition enum : colist Q := CoTrees.bf tree.
  
  Eval compute in CoLists.take 10 enum.

End SternBrocot.
