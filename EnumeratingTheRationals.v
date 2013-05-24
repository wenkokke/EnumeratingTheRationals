(** * Enumerating The Rationals *)

Require Import List.
Require Import Streams.
Require Import PArith.
Require Import NArith.
Require Import QArith.

(** ** CoLists *)

Module CoLists.

  (** A [colist] is defined by analogy to the [Stream] datatype,
      so that we can use the high-level predicates defined in the
      [Coq.Lists.Streams] module. *)

  Definition colist := Stream.
  Definition cocons := Cons.

  (** Constructs [colist]s by iteratively unfolding values. *)

  CoFixpoint unfold {A B: Type} (f: B -> (A*B)) (e: B) : colist A :=
    match f e with
      | (x,xs) => cocons _ x (unfold f xs)
    end.
  
  (** Takes a finite prefix of an infinite [colist]. *)

  Fixpoint take {A: Type} (n: nat) (xs: colist A) : list A :=
    match n with
      | O => nil
      | S n =>
        match xs with
          | cocons x xs => cons x (take n xs)
        end
    end.

End CoLists.

Notation colist        := CoLists.colist.
Notation cocons        := CoLists.cocons.
Notation colist_unfold := CoLists.unfold.
Notation colist_take   := CoLists.take.

(** ** CoTrees *)

Module CoTrees.

  Delimit Scope cotree_scope with cotree.

  CoInductive cotree (A: Type) :=
  | conode : cotree A -> A -> cotree A -> cotree A.

  (** Constructs [cotrees]s by iteratively unfolding values. *)

  CoFixpoint unfold {A B: Type} (f: B -> (B*A*B)) (e: B) : cotree A :=
    match f e with
      | (l,x,r) => conode _ (unfold f l) x (unfold f r)
    end.

  (** Performs a breadth-first walk over a forest of [cotree]s, provided that
      the forest is provably non-empty. *)
  
  CoFixpoint bf_acc {A: Type} (ts: list (cotree A)) : ts<>nil -> colist A.
    refine (match ts as xs return xs<>nil -> colist A with
              | nil       => fun h => _
              | cons t ts => fun h => 
                match t with
                  | conode l x r => cocons _ x (bf_acc _ (ts ++ (cons l (cons r nil))) _)
                end
            end).
    exfalso; apply h; reflexivity.
    apply not_eq_sym; apply app_cons_not_nil.
  Defined.

  (** Performs a breadth-first walk over a [cotree], returning a [colist]. *)
  
  Definition bf {A: Type} (t: cotree A) : colist A.
    refine (bf_acc (t :: nil) _).
    apply not_eq_sym; apply nil_cons.
  Defined.

  (** Returns the [root] of a [cotree], which is the topmost value. *)

  Definition root {A: Type} (t: cotree A) : A :=
    match t with
      | conode _ x _ => x
    end.

  (** Returns the left subtree of a [cotree]. *)
  
  Definition left {A: Type} (t: cotree A) : cotree A :=
    match t with
      | conode l _ _ => l
    end.

  (** Returns the right subtree of a [cotree]. *)
  
  Definition right {A: Type} (t: cotree A) : cotree A :=
    match t with
      | conode _ _ r => r
    end.

  (** Equality as defined on [cotree]s; to prove (co)equality,
      one must show that the [root]s of the two trees are equal,
      and that both of their subtrees are equal.
   
      Note that the constructor [conode_eq] can only be applied
      when both roots are already proven equal. *)

  CoInductive Eq {A: Type} : cotree A -> cotree A -> Prop :=
    cotree_eq : forall x l1 r1 l2 r2,
                  Eq l1 l2
                  -> Eq r1 r2
                  -> Eq (conode _ l1 x r1) (conode _ l2 x r2).

  Theorem Eq_root : forall {A: Type} (t1 t2: cotree A), Eq t1 t2 -> root t1 = root t2.
    intros A t1 t2 H; destruct H; reflexivity.
  Qed.

  Theorem Eq_left : forall {A: Type} (t1 t2: cotree A), Eq t1 t2 -> Eq (left t1) (left t2).
    intros A t1 t2 H; destruct H; simpl; assumption.
  Qed.

  Theorem Eq_right : forall {A: Type} (t1 t2: cotree A), Eq t1 t2 -> Eq (right t1) (right t2).
    intros A t1 t2 H; destruct H; simpl; assumption.
  Qed.

  Section Eq_coind.
    Variable A: Type.
    Variable R: cotree A -> cotree A -> Prop.
    
    Hypothesis Case_root  : forall t1 t2, R t1 t2 -> root t1 = root t2.
    Hypothesis Case_left  : forall t1 t2, R t1 t2 -> R (left t1) (left t2).
    Hypothesis Case_right : forall t1 t2, R t1 t2 -> R (right t1) (right t2).
    
    Theorem Eq_coind : forall t1 t2: cotree A, R t1 t2 -> Eq t1 t2.
      cofix.
      destruct t1 as [l1 x1 r1].
      destruct t2 as [l2 x2 r2].
      intro H.
      generalize H; intro Heq.
      apply Case_root in Heq; simpl in Heq; rewrite Heq.
      constructor.
      - apply Case_left in H; simpl in H.
        apply Eq_coind; assumption.
      - apply Case_right in H; simpl in H.
        apply Eq_coind; assumption.
    Qed.
  End Eq_coind.
  
  Theorem Eq_refl : forall {A: Type} (t: cotree A), Eq t t.
    intros A t.
    apply (Eq_coind A (fun t1 t2 => t1 = t2)).
    - intros t1 t2 H; rewrite H; reflexivity.
    - intros t1 t2 H; rewrite H; reflexivity.
    - intros t1 t2 H; rewrite H; reflexivity.
    - reflexivity.
  Qed.

  Theorem Eq_sym : forall {A: Type} (t1 t2: cotree A), Eq t1 t2 -> Eq t2 t1.
    cofix.
    intros A t1 t2 H.
    destruct t1 as [l1 x1 r1].
    destruct t2 as [l2 x2 r2].
    generalize H; intro Heq; apply Eq_root in Heq; simpl in Heq.
    rewrite <- Heq.
    constructor.
    - apply Eq_left in H; simpl in H.
      generalize H; apply Eq_sym.
    - apply Eq_right in H; simpl in H.
      generalize H; apply Eq_sym.
  Qed.

  Theorem Eq_trans : forall {A: Type} (t1 t2 t3: cotree A), Eq t1 t2 -> Eq t2 t3 -> Eq t1 t3.
    cofix.
    intros A t1 t2 t3 H12 H23.
    destruct t1 as [l1 x1 r1].
    destruct t2 as [l2 x2 r2].
    destruct t3 as [l3 x3 r3].
    generalize H12; intro Heq12; apply Eq_root in Heq12; simpl in Heq12.
    generalize H23; intro Heq23; apply Eq_root in Heq23; simpl in Heq23.
    rewrite <- Heq23, <- Heq12.
    constructor.
    - apply Eq_left in H12; simpl in H12.
      apply Eq_left in H23; simpl in H23.
      generalize H12 H23.
      apply Eq_trans.
    - apply Eq_right in H12; simpl in H12.
      apply Eq_right in H23; simpl in H23.
      generalize H12 H23.
      apply Eq_trans.
  Qed.

  Inductive Exists {A: Type} (P: cotree A -> Prop) (t: cotree A) : Prop :=
  | Here  : P t -> Exists P t
  | Left  : Exists P (left t) -> Exists P t
  | Right : Exists P (right t) -> Exists P t.
  
  CoInductive Forall {A: Type} (P: cotree A -> Prop) (t: cotree A) : Prop :=
  | Always : P t -> Forall P (left t) -> Forall P (right t) -> Forall P t.

End CoTrees.

(** Import [CoTrees] into the global scope. *)

Notation cotree               := CoTrees.cotree.
Notation conode               := CoTrees.conode.
Notation cotree_unfold        := CoTrees.unfold.
Notation cotree_bf            := CoTrees.bf.
Notation cotree_root          := CoTrees.root.
Notation cotree_left          := CoTrees.left.
Notation cotree_right         := CoTrees.right.
Notation cotree_eq            := CoTrees.Eq.
Notation cotree_eq_refl       := CoTrees.Eq_refl.
Notation cotree_eq_sym        := CoTrees.Eq_sym.
Notation cotree_eq_trans      := CoTrees.Eq_trans.
Notation cotree_exists        := CoTrees.Exists.
Notation cotree_exists_here   := CoTrees.Here.
Notation cotree_exists_left   := CoTrees.Left.
Notation cotree_exists_right  := CoTrees.Right.
Notation cotree_forall        := CoTrees.Forall.
Notation cotree_forall_always := CoTrees.Always.
    
(** ** The Calkin-Wilf Tree *)
Module CalkinWilf.

  Local Open Scope positive_scope.

  Definition next (q:positive*positive) : (positive*positive)*Q*(positive*positive) :=
    match q with
      | (m,n) => ((m,m + n),Zpos m # n,(m + n,n))
    end.
  
  Definition tree : cotree Q := CoTrees.unfold next (1,1).
  
  Definition enum : colist Q := CoTrees.bf tree.
  
End CalkinWilf.

Notation calkin_wilf_next := CalkinWilf.next.
Notation calkin_wilf_tree := CalkinWilf.tree.
Notation calkin_wilf_enum := CalkinWilf.enum.

(** ** The Stern-Brocot Tree *)
Module SternBrocot.

  (** *** Required Proofs on Natural Numbers *)

  Local Open Scope N_scope.
  
  Section N_Properties.

    Definition N_pos (n:N) : n<>0 -> positive.
      refine (match n as n' return n'<>0 -> positive with
                | 0      => fun h => _
                | Npos p => fun h => p
              end).
      exfalso; apply h; reflexivity.
    Defined.
  
    Definition N_Z (n:N) : Z :=
      match n with
        | 0      => Z0 
        | Npos n => Zpos n
      end.
    
    Lemma Npos_over_Nplus_l : forall n m : N,
      n <> 0 -> n + m <> 0.
    Proof.
      intros n m H.
      destruct n as [|n].
      - exfalso; apply H; reflexivity.
      - destruct m as [|m].
        * simpl; assumption.
        * simpl; discriminate.
    Qed.
  
    Lemma Npos_over_Nplus_r : forall n m : N,
      m <> 0 -> n + m <> 0.
    Proof.
      intros n m.
      rewrite Nplus_comm.
      apply Npos_over_Nplus_l.
    Qed.
    
    Lemma Npos_over_Nplus : forall n m : N,
      n <> 0 \/ m <> 0 -> n + m <> 0.
    Proof.
      intros n m H.
      elim H.
      - apply Npos_over_Nplus_l.
      - apply Npos_over_Nplus_r.
    Qed.

  End N_Properties.

  (** *** Construction of the Tree *)

  Inductive Qpair : Type :=
  | qpair (a b c d : N) (HL: a<>0 \/ c<>0) (HR: b<>0 \/ d<>0) : Qpair.

  Definition next (q:Qpair) : Qpair*Q*Qpair.
    refine (match q with
              | qpair a b c d HL HR =>
                let ac := a + c in
                let bd := b + d in
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
    refine (CoTrees.unfold next (qpair 0 1 1 0 _ _)).
    - right; discriminate.
    - left ; discriminate.
  Defined.
  
  Definition enum : colist Q := CoTrees.bf tree.
  
End SternBrocot.

Notation stern_brocot_next := SternBrocot.next.
Notation stern_brocot_tree := SternBrocot.tree.
Notation stern_brocot_enum := SternBrocot.enum.
