(** * Enumerating The Rationals *)

Require Import List.
Require Import Streams.
Require Import PArith.
Require Import NArith.
Require Import QArith.
Require Import Recdef.

(** ** CoLists *)

Module CoList.

  (** A [colist] is defined by analogy to the [Stream] datatype,
      so that we can use the high-level predicates defined in the
      [Coq.Lists.Streams] module. *)

  Notation colist         := Stream.
  Notation cocons         := Cons.
  Notation Eq             := EqSt.
  Notation Eq_refl        := EqSt_reflex.
  Notation Eq_sym         := sym_EqSt.
  Notation Eq_trans       := trans_EqSt.
  Notation Exists         := Exists.
  Notation Exists_here    := Here.
  Notation Exists_further := Further.
  Notation Forall         := ForAll.
  Notation Always         := HereAndFurther.
  Notation lookup         := Str_nth.

  (** Ensure that [lookup] is transparent. *)

  Hint Unfold lookup.

  (** Constructs [colist]s by iteratively unfolding values. *)

  CoFixpoint unfold {A B: Type} (f: B -> (A*B)) (e: B) : colist A :=
    match f e with
      | (x,xs) => cocons  x (unfold f xs)
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

  Inductive In {A: Type} (x: A) (xs: colist A) : Prop :=
  | In_here    : (x = hd xs) -> In x xs
  | In_further : In x (tl xs) -> In x xs.
  
  Definition At : forall {A: Type} (x: A) (xs: colist A) (n: nat), (x = lookup n xs) -> In x xs.
  Proof.
    intros A x xs n; generalize xs; clear xs.
    induction n as [|n].
    - apply In_here.
    - intro xs; destruct xs as [y ys]; unfold lookup in *; simpl in *; intro H.
      apply IHn in H; apply In_further; simpl; assumption.
  Defined.

  Theorem In_At : forall {A: Type} (x: A) (xs: colist A),
    In x xs -> exists n, x = lookup n xs.
  Proof.
    intros A x xs H; elim H; clear H xs.
    - intros xs H; exists 0%nat; destruct xs. unfold lookup. simpl in *; assumption.
    - intros xs H IH; elim IH; clear IH; intros n IH; exists (S n).
      unfold lookup in *; simpl in *; assumption.
  Qed.

  Definition At_Exists : forall {A: Type} (P: A -> Prop) (xs: colist A) (n: nat),
    P (lookup n xs) -> Exists (fun l => P (hd l)) xs.
  Proof.
    intros A P xs n; generalize xs; clear xs.
    induction n as [|n].
    - intros xs H; unfold lookup in H; simpl in H.
      apply Exists_here; assumption.
    - intros xs H; unfold lookup in *; simpl in *.
      apply IHn in H; apply Exists_further; assumption.
  Defined.
      
  Theorem In_Exists : forall {A: Type} (P: A -> Prop) (x: A) (xs: colist A),
    P x /\ In x xs -> Exists (fun l => P (hd l)) xs.
  Proof.
    intros A P x xs H; elim H; clear H; intros HP HM.
    apply In_At in HM; elim HM; clear HM; intros n HM.
    apply (At_Exists P xs n); rewrite HM in HP; assumption.
  Qed.

  Theorem Exists_In : forall {A: Type} (P: A -> Prop) (xs: colist A),
    Exists (fun l => P (hd l)) xs -> exists x, P x /\ In x xs.
  Proof.
    intros A P xs H; elim H; clear H xs.
    - intros xs H; exists (hd xs); split.
      * assumption.
      * apply In_here; reflexivity.
    - intros xs H IH; elim IH; clear IH; intros x IH; elim IH; clear IH.
      intros HP IH; exists x; split.
      * assumption.
      * apply In_further; assumption.
  Qed.

  Lemma Forall_here : forall {A: Type} (P: A -> Prop) xs,
    Forall (fun l => P (hd l)) xs -> P (hd xs).
  Proof.
    intros A P xs H; destruct H; assumption.
  Qed.

  Lemma Forall_further : forall {A: Type} (P: colist A -> Prop) xs,
    Forall P xs -> Forall P (tl xs).
  Proof.
    intros A P xs H; destruct H; assumption.
  Qed.

  Theorem Forall_In : forall {A: Type} (P: A -> Prop) xs,
    Forall (fun l => P (hd l)) xs -> forall x, In x xs -> P x.
  Proof.
    intros A P xs Hall x Hin.
    apply In_At in Hin; elim Hin; intros n Heq.
    generalize Hall Heq; clear Hall Hin Heq.
    generalize xs; clear xs.
    induction n as [|n].
    - intros xs Hall Heq.
      destruct xs as [y ys]; unfold lookup in Heq; simpl in Heq.
      apply Forall_here in Hall; simpl in Hall; rewrite Heq; assumption.
    - intros xs Hall Heq.
      apply Forall_further in Hall; apply IHn in Hall; assumption.    
  Qed.
  
End CoList.

Notation colist := CoList.colist.
Notation cocons := CoList.cocons.

(**
Notation colist_unfold         := CoList.unfold.
Notation colist_take           := CoList.take.
Notation colist_eq             := CoList.Eq.
Notation colist_eq_refl        := CoList.Eq_refl.
Notation colist_eq_sym         := CoList.Eq_sym.
Notation colist_eq_trans       := CoList.Eq_trans.
Notation colist_exists         := CoList.Exists.
Notation colist_exists_here    := CoList.Exists_here.
Notation colist_exists_further := CoList.Exists_further.
Notation colist_forall         := CoList.Forall.
Notation colist_forall_always  := CoList.Always.
Notation in_colist             := CoList.In.
Notation in_colist_at          := CoList.At.
Notation colist_in_at          := CoList.In_At.
Notation colist_at_exists      := CoList.At_Exists.
Notation colist_exists_in      := CoList.Exists_In.
Notation colist_in_exists      := CoList.In_Exists.
**)

(** ** CoTrees *)

Module CoTree.

  CoInductive cotree (A: Type) :=
  | conode : cotree A -> A -> cotree A -> cotree A.

  (** Constructs [cotrees]s by iteratively unfolding values. *)

  CoFixpoint unfold {A B: Type} (f: B -> (B*A*B)) (e: B) : cotree A :=
    match f e with
      | (l,x,r) => conode _ (unfold f l) x (unfold f r)
    end.

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

  (** Define an inductive datatype for performing queries on
      [cotree]s, as the [nat] type is for [colist]s. *)

  Inductive path : Type :=
  | Here  : path
  | Left  : path -> path
  | Right : path -> path.

  Fixpoint lookup {A: Type} (p: path) (t: cotree A) : A :=
    match p with
      | Here    => root t
      | Left  p => lookup p (left t)
      | Right p => lookup p (right t)
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

  Section Eq_coind_def.
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
  End Eq_coind_def.
  
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

  (** [In] defines proofs on the elements of a [cotree]. *)
  
  Inductive In {A: Type} (x: A) (t: cotree A) : Prop :=
  | In_root  : (x = root t) -> In x t
  | In_left  : In x (left t) -> In x t
  | In_right : In x (right t) -> In x t.

  Definition At : forall {A: Type} (x: A) (t: cotree A) (p: path), (x = lookup p t) -> In x t.
  Proof.
    intros A x t p; generalize t; clear t.
    induction p as [|p|p].
    - apply In_root.
    - intros t H; apply In_left ; destruct t as [l y r]; simpl in *; apply IHp in H; assumption.
    - intros t H; apply In_right; destruct t as [l y r]; simpl in *; apply IHp in H; assumption.
  Defined.

  Theorem In_At : forall {A: Type} (x: A) (t: cotree A),
    In x t -> exists p, x = lookup p t.
  Proof.
    intros A x t H; elim H; clear H t.
    - intros t H; exists Here; destruct t as [l y r]; simpl in *; assumption.
    - intros t H IH; elim IH; clear IH; intros p IH; exists (Left  p); destruct t; simpl in *; assumption.
    - intros t H IH; elim IH; clear IH; intros p IH; exists (Right p); destruct t; simpl in *; assumption.
  Qed.
    
  (** [Exists] defines proofs on the subtrees of a [cotree] *)

  Inductive Exists {A: Type} (P: cotree A -> Prop) (t: cotree A) : Prop :=
  | Exists_here  : P t -> Exists P t
  | Exists_left  : Exists P (left t) -> Exists P t
  | Exists_right : Exists P (right t) -> Exists P t.

  Definition At_Exists : forall {A: Type} (P: A -> Prop) (t: cotree A) (p: path),
    P (lookup p t) -> Exists (fun t => P (root t)) t.
  Proof.
    intros A P t p; generalize t; clear t.
    induction p as [|p|p].
    - intro t; simpl; intro H; apply Exists_here ; assumption.
    - intro t; simpl; intro H; apply Exists_left ; apply IHp in H; assumption.
    - intro t; simpl; intro H; apply Exists_right; apply IHp in H; assumption.
  Qed.

  Theorem In_Exists : forall {A: Type} (P: A -> Prop) (x: A) (t: cotree A),
    P x /\ In x t -> Exists (fun t => P (root t)) t.
  Proof.
    intros A P x t H; elim H; intros HP IH.
    apply In_At in IH; elim IH; clear IH; intros p IH.
    apply (At_Exists P t p); rewrite IH in HP; assumption.
  Qed.

  Definition Exists_In : forall {A: Type} (P: A -> Prop) (t: cotree A),
    Exists (fun t => P (root t)) t -> exists x, P x /\ In x t.
  Proof.
    intros A P t H; elim H; clear H t.
    - intros t H; exists (root t); split.
      assumption. apply In_root; reflexivity.
    - intros t H IH; elim IH; clear IH; intros x IH; elim IH; clear IH.
      intros HP IH; exists x; split. assumption. apply In_left; assumption.
    - intros t H IH; elim IH; clear IH; intros x IH; elim IH; clear IH.
      intros HP IH; exists x; split. assumption. apply In_right; assumption.
  Qed.

  (** [Forall] defines a proof on all subtrees of a [cotree] *)

  CoInductive Forall {A: Type} (P: cotree A -> Prop) (t: cotree A) : Prop :=
  | Always : P t -> Forall P (left t) -> Forall P (right t) -> Forall P t.

  Section Forall_coind_def.
    Variable A: Type.
    Variable P: cotree A -> Prop.
    Variable R: cotree A -> Prop.

    Hypothesis Case_here  : forall t, R t -> P t.
    Hypothesis Case_left  : forall t, R t -> R (left t).
    Hypothesis Case_right : forall t, R t -> R (right t).
    
    Theorem Forall_coind : forall t, R t -> Forall P t.
      cofix.
      constructor.
      - apply Case_here  in H; assumption.
      - apply Case_left  in H; apply Forall_coind in H; assumption.
      - apply Case_right in H; apply Forall_coind in H; assumption.
    Qed.
  End Forall_coind_def.

  Lemma Forall_here : forall {A} P (t: cotree A), Forall P t -> P t.
    intros A P t H; destruct H as [H0 HL HR]; assumption.
  Qed.

  Lemma Forall_left : forall {A} P (t: cotree A), Forall P t -> Forall P (left t).
    intros A P t H; destruct H as [H0 HL HR]; assumption.
  Qed.
    
  Lemma Forall_right : forall {A} P (t: cotree A), Forall P t -> Forall P (right t).
    intros A P t H; destruct H as [H0 HL HR]; assumption.
  Qed.

  Theorem ForallP_ExistsP : forall {A} P (t: cotree A),
    Forall P t -> Exists P t.
  Proof.
    intros A P t.
    intro H; apply Forall_here in H.
    constructor; assumption.
  Qed.

  Theorem ForallP_NotExistsNotP : forall {A} P (t: cotree A),
    Forall P t -> ~(Exists (fun t => ~P t) t).
  Proof.
    intros A P t H F.
    induction F as [t F0|t FL IHL|t FR IHR].
    - apply Forall_here  in H; elim F0; assumption.
    - apply Forall_left  in H; apply IHL in H; assumption.
    - apply Forall_right in H; apply IHR in H; assumption.
  Qed.

  Theorem ExistsNotNotP_NotForallNotP : forall {A} P (t: cotree A),
    Exists (fun t => ~ ~ P t) t -> ~ Forall (fun t => ~P t) t.
  Proof. 
    intros A P t H F.
    destruct H.
    - apply Forall_here  in F; elim H; assumption.
    - apply Forall_left  in F; apply ForallP_NotExistsNotP in F; elim F. assumption.
    - apply Forall_right in F; apply ForallP_NotExistsNotP in F; elim F. assumption.
  Qed.

  Theorem In_Forall : forall {A} (P: A -> Prop) t,
    (forall x t, In x t -> P x) -> Forall (fun t => P (root t)) t.
  Proof.
    intros A P t H.
    constructor.
    - apply (H (root t) t). apply In_root. reflexivity.
  Admitted.
      
  Theorem Forall_In : forall {A} P (t: cotree A),
    Forall (fun t => P (root t)) t -> forall x, In x t -> P x.
  Proof.
    intros A P t H x IH; generalize H; clear H; elim IH; clear IH t.
    - intros t H0 H; rewrite H0. apply Forall_here in H; assumption.
    - intros t H0 IH H. apply Forall_left  in H; apply IH in H. assumption.
    - intros t H0 IH H. apply Forall_right in H; apply IH in H. assumption.
  Qed.

  Section map_def.
    
    (** Definition of [map] over [cotree]s. *)

    CoFixpoint map {A B: Type} (f: A -> B) (t: cotree A) : cotree B :=
      match t with
        | conode l x r => conode _ (map f l) (f x) (map f r)
      end.
    
    Theorem Forall_map : forall {A B: Type} (P: cotree B -> Prop) (f: A -> B) (t: cotree A),
      Forall (fun t => P (map f t)) t -> Forall P (map f t).
    Proof.
      intros A B P f; cofix; intros t H.
      constructor.
      - apply Forall_here in H; assumption.
      - apply Forall_left in H.
        destruct t as [l x r]; simpl in *.
        apply Forall_map in H; assumption.
      - apply Forall_right in H.
        destruct t as [l x r]; simpl in *.
        apply Forall_map in H; assumption.
    Qed.

  End map_def.

  Section bf_def.

    (** Performs a breadth-first walk over a forest of [cotree]s, provided that
        the forest is provably non-empty. *)
  
    CoFixpoint bf_acc {A: Type} (ts: list (cotree A)) : ts<>nil -> colist A.
      refine (match ts as xs return xs<>nil -> colist A with
                | nil       => fun h => _
                | cons t ts => fun h =>
                  match t with
                    | conode l x r => cocons x (bf_acc _ (ts ++ (cons l (cons r nil))) _)
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

    Lemma In_path : forall {A} x (t: cotree A),
      In x t -> exists p, x = lookup p t.
    Proof.
      intros A x t H.
      induction H as [|t H IH|t H IH].
      - exists Here; auto.
      - elim IH; clear IH; intros p IH; exists (Left p); auto.
      - elim IH; clear IH; intros p IH; exists (Right p); auto.
    Qed.

    Theorem In_bf : forall {A} x (t: cotree A),
      In x t -> CoList.In x (bf t).
    Proof.
      intros A x t H.
      apply In_path in H; elim H; clear H; intros p H.
    Admitted.

  End bf_def.

End CoTree.

Notation cotree := CoTree.cotree.
Notation conode := CoTree.conode.
Notation path   := CoTree.path.

(** ** Naive Enumeration of Rationals *)
Module Naive.
  
  Definition next (q: Q) : Q*Q*Q :=
    (Z.succ (Qnum q) # Qden q, q, Qnum q # Pos.succ (Qden q)).

  Definition tree := CoTree.unfold next (1 # 1).

  Definition enum := CoTree.bf tree.

  Fixpoint findn (n d: nat) : (n<>0)%nat -> (d<>0)%nat -> CoTree.path.
    intros Hn Hd.
    destruct n as [|n]; [exfalso; auto| ].
    induction n as [|n IHn].
    - destruct d as [|d]; [exfalso; auto| ].
      induction d as [|d IHd].
      * apply CoTree.Here.
      * apply CoTree.Right,IHd; auto.
    - apply CoTree.Left,IHn; auto.
  Defined.

  Definition findp (n d: positive) : CoTree.path.
    apply (findn (Pos.to_nat n) (Pos.to_nat d)).
    apply not_eq_sym,lt_0_neq,Pos2Nat.is_pos.
    apply not_eq_sym,lt_0_neq,Pos2Nat.is_pos.
  Defined.

  Definition find (q: Q) : 0 < q -> CoTree.path.
    intros Hq.
    destruct q as [n d].
    destruct n as [|n|n]; try discriminate Hq.
    apply (findp n d).
  Defined.
  
  Theorem all_Q_in_tree : forall q, 0 < q -> CoTree.In q tree.
  Proof.
    intros q Hq.
    destruct q as [n' d'].
    destruct n' as [|n'|n']; try discriminate Hq. clear Hq.
    pose proof (Pos2Nat.is_pos n') as Hn; apply lt_0_neq,not_eq_sym in Hn.
    pose proof (Pos2Nat.is_pos d') as Hd; apply lt_0_neq,not_eq_sym in Hd.
    remember (Pos.to_nat n')   as n eqn:Heqn; replace (Pos.to_nat n') with n in Hn by apply Heqn.
    remember (Pos.to_nat d')   as d eqn:Heqd; replace (Pos.to_nat d') with d in Hd by apply Heqd.
    remember (findn n d Hn Hd) as p eqn:Heqp; apply (CoTree.At ('n' # d') tree p).
    destruct n as [|n]; [exfalso; auto| ].
    induction n as [|n IHn].
    - destruct d as [|d]; [exfalso; auto| ].
      induction d as [|d IHd].
      * rewrite Heqp; simpl.
  Admitted.
End Naive.

(** ** The Stern-Brocot Tree *)
Module SternBrocot.

  (** *** Required Proofs on Natural Numbers *)

  Section N_properties.

    Local Open Scope N_scope. 

    Definition N_pos (n:N) : n<>0 -> positive.
      refine (match n as n' return n'<>0 -> positive with
                | 0      => fun h => _
                | Npos p => fun h => p
              end).
      exfalso; auto.
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
      - exfalso; auto.
      - destruct m as [|m].
        * simpl; discriminate.
        * simpl; discriminate.
    Qed.
  
    Lemma Npos_over_Nplus_r : forall n m : N,
      m <> 0 -> n + m <> 0.
    Proof.
      intros; rewrite Nplus_comm; apply Npos_over_Nplus_l; assumption.
    Qed.
    
    Theorem Npos_over_Nplus : forall n m : N,
      n <> 0 \/ m <> 0 -> n + m <> 0.
    Proof.
      intros n m H; elim H; [apply Npos_over_Nplus_l|apply Npos_over_Nplus_r].
    Qed.

  End N_properties.

  (** *** Construction of the Tree *)

  Section tree_def.

    Local Open Scope N_scope.

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
      refine (CoTree.unfold next (qpair 0 1 1 0 _ _)).
      - right ; discriminate.
      - left  ; discriminate.
    Defined.
    
  End tree_def.

  Section enum_def.

    Definition enum : colist Q := CoTree.bf tree.

  End enum_def.

  Section gcd_trace_def.

    Local Open Scope N_scope. 

    (** *** Computational Trace of a GCD Computation *)

    Definition step (qs: path -> path) (acc: N*path) :=
      match acc with
        | (d,q0) => (d,qs q0)
      end.

    Definition pairsum (p: N*N) :=
      match p with (m,n) => N.to_nat (m + n) end.

    Section gcd_lemma_def.
      Local Open Scope nat_scope.

      Lemma gcd_lemma1 : forall m n, m<>0 -> n<>0 -> m<n -> (m + (n - m)) < (m + n).
      Proof. intros m n Om On Hlt; omega. Qed.
      Lemma gcd_lemma2 : forall m n, m<>0 -> n<>0 -> (m - n + n) < (m + n).
      Proof. intros m n Om On; omega. Qed.
      Lemma gcd_lt_neq : forall n:N, (0 < n)%N -> (N.to_nat n <> 0)%nat.
      Proof.
        intros n H; destruct n as [|n]; [discriminate H| ].
        simpl; apply not_eq_sym,lt_O_neq,Pos2Nat.is_pos.
      Qed.
    End gcd_lemma_def.

    Function gcd_trace' (p: N*N) {measure pairsum p} :=
      match p with (m,n) => 
        if ((m <? n) && (0 <? m) && (0 <? n)) then step CoTree.Left  (gcd_trace' (m,(n - m))) else
        if ((n <? m) && (0 <? m) && (0 <? n)) then step CoTree.Right (gcd_trace' ((m - n),n)) else
        (m, CoTree.Here)
      end.
    Proof.
      intros p m n Hp H0.
      apply andb_prop in H0; inversion H0 as [H1 Onb]; clear H0.
      apply andb_prop in H1; inversion H1 as [Hltb Omb]; clear H1.
      pose proof (N.ltb_spec m n) as Hlt; destruct Hlt as [Hlt|Hlt];
      pose proof (N.ltb_spec 0 n) as On; destruct On as [On|On];
      pose proof (N.ltb_spec 0 m) as Om; destruct Om as [Om|Om];
      try inversion Hltb; try inversion Omb; try inversion Onb.

      simpl; rewrite 2!N2Nat.inj_add; rewrite 1!N2Nat.inj_sub; apply gcd_lemma1.
      (**) apply (gcd_lt_neq m Om).
      (**) apply (gcd_lt_neq n On).
      (**) destruct m as [|m], n as [|n].
           (**) discriminate Hlt.
           (**) discriminate Om.
           (**) discriminate On.
           (**) simpl; apply Pos2Nat.inj_lt; auto.

      intros p m n Hp _ H0.
      apply andb_prop in H0; inversion H0 as [H1 Onb]; clear H0.
      apply andb_prop in H1; inversion H1 as [Hltb Omb]; clear H1.
      pose proof (N.ltb_spec m n) as Hlt; destruct Hlt as [Hlt|Hlt];
      pose proof (N.ltb_spec 0 n) as On; destruct On as [On|On];
      pose proof (N.ltb_spec 0 m) as Om; destruct Om as [Om|Om];
      try inversion Hltb; try inversion Omb; try inversion Onb.

      simpl; rewrite 2!N2Nat.inj_add; rewrite 1!N2Nat.inj_sub; apply gcd_lemma2.
      (**) apply (gcd_lt_neq m Om).
      (**) apply (gcd_lt_neq n On).
      (**) destruct m as [|m], n as [|n].
           (**) discriminate On.
           (**) discriminate Om.
           (**) discriminate On.
           (**) unfold pairsum. rewrite 2!N2Nat.inj_add, 1!N2Nat.inj_sub. apply gcd_lemma2.
      (**) apply (gcd_lt_neq (N.pos m) Om).
      (**) apply (gcd_lt_neq (N.pos n) On).
    Defined.

    Definition gcd_trace (p: positive*positive) :=
      match p with
        | (n,d) =>
          match gcd_trace' (N.pos n,N.pos d) with
            | (_,p) => p
          end
      end.
  End gcd_trace_def.
  
  Theorem correctness : forall (n:positive) (d:positive), CoTree.lookup (gcd_trace (n,d)) tree = (Z.pos n # d).
  Proof.
  Admitted.
  
End SternBrocot.

(** ** The Calkin-Wilf Tree *)
Module CalkinWilf.

  Local Open Scope positive_scope.

  Section tree_def.

    Definition next (q:positive*positive) : (positive*positive)*Q*(positive*positive) :=
      match q with
        | (m,n) => ((m,m + n),Zpos m # n,(m + n,n))
      end.
  
    Definition tree : cotree Q := CoTree.unfold next (1,1).

  End tree_def.
  
  Section enum_def.
    
    Definition enum : colist Q := CoTree.bf tree.

  End enum_def.

End CalkinWilf.


