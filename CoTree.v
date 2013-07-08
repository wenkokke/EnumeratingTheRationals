Require Import List.
Require Import CoList.

(** ** Lists *)

Module List.
  
  Definition hd {A} (xs: list A) : nil<>xs -> A.
    refine(match xs as ys return nil<>ys -> A with
             | nil      => fun h => _
             | cons x _ => fun h => x
           end).
    exfalso; apply h; reflexivity.
  Defined.

End List.

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

  Theorem In_Forall : forall {A} (P: A -> Prop) (t: cotree A),
    (forall x, In x t -> P x) -> Forall (fun t => P (root t)) t.
  Proof.
    cofix.
    intros A P t H.
    constructor.
    - apply H. apply In_root. auto.
    - apply In_Forall. intros x HI. apply H. apply In_left. auto.
    - apply In_Forall. intros x HI. apply H. apply In_right. auto.
  Qed.
      
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
  
    CoFixpoint bf_acc {A: Type} (ts: list (cotree A)) : nil<>ts -> colist A.
      refine (match ts as xs return nil<>xs -> colist A with
                | nil       => fun h => _
                | cons t ts => fun h =>
                  match t with
                    | conode l x r => cocons x (bf_acc _ (ts ++ (cons l (cons r nil))) _)
                  end
              end).
      exfalso; apply h; reflexivity.
      apply app_cons_not_nil.
    Defined.

    (** Performs a breadth-first walk over a [cotree], returning a [colist]. *)
    
    Definition bf {A: Type} (t: cotree A) : colist A.
      refine (bf_acc (t :: nil) _).
      apply nil_cons.
    Defined.

    Lemma bf_acc_hd {A} (ts: list (cotree A)) (H: nil<>ts) : CoList.hd (bf_acc ts H) = root (List.hd ts H).
    Proof.
      destruct ts as [|t ts].
      - exfalso; apply H; reflexivity.
      - destruct t; reflexivity.
    Qed.

    Lemma In_path : forall {A} x (t: cotree A),
      In x t -> exists p, x = lookup p t.
    Proof.
      intros A x t H.
      induction H as [|t H IH|t H IH].
      - exists Here; auto.
      - elim IH; clear IH; intros p IH; exists (Left p); auto.
      - elim IH; clear IH; intros p IH; exists (Right p); auto.
    Qed.

    Lemma In_parent : forall {A} x (l: cotree A),
      forall y r, CoList.In x (bf l) -> CoList.In x (bf (conode A l y r)).
    Proof.
      intros A x l y r H.
      apply CoList.In_further.
    Admitted.

    Theorem In_bf : forall {A} x (t: cotree A),
      In x t -> CoList.In x (bf t).
    Proof.
      intros A x t H.
      induction H as [|t H IH|t H IH].
      - destruct t; apply CoList.In_here; auto.
      - destruct t as [l y r].
        apply CoList.In_further.
        simpl in H,IH.
    Admitted.

  End bf_def.

End CoTree.

Notation cotree := CoTree.cotree.
Notation conode := CoTree.conode.
Notation path   := CoTree.path.
