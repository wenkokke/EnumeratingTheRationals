(* begin hide *)
Require Import List.
Require Import CoList.
(* end hide *)

(** * CoTrees *)

Module CoTree.

  (** ** Defining CoTrees *)
  (** We define [cotree]s to have a single constructor; [cocons].
      This guarantees that the tree does not have any terminating
      branches, which will be extremely convenient later on.
    *)

  CoInductive cotree (A: Type) :=
  | conode : cotree A -> A -> cotree A -> cotree A.

  (** We can construct [cotree]s by iteratively unfolding values. *)

  CoFixpoint unfold {A B: Type} (f: B -> (B*A*B)) (e: B) : cotree A :=
    match f e with
      | (l,x,r) => conode _ (unfold f l) x (unfold f r)
    end.
    
  (** Below we introduce a number of operations to deconstruct [cotree]s,
      analogous to the [hd] and [tl] and tail operations on a [colist]:
      
      [root] returns the [root] of a [cotree], which is the topmost value,
    *)

  Definition root {A: Type} (t: cotree A) : A :=
    match t with
      | conode _ x _ => x
    end.

  (** and [left] and [right] return the left or right subtrees of a [cotree]. *)
  
  Definition left {A: Type} (t: cotree A) : cotree A :=
    match t with
      | conode l _ _ => l
    end.
  
  Definition right {A: Type} (t: cotree A) : cotree A :=
    match t with
      | conode _ _ r => r
    end.
    
  (** ** Indexing CoTrees *)

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
    
  (** ** Properties on CoTrees *)
  
  (** *** Equality between subtrees *)
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

  (** *** Membership of subtrees *)
  (** The predicate [In] [x] [t] proves the membership of an element
      [x] to the [cotree] [t], and the predicate [At] relates membership
      proofs to the [lookup] function.
    *)
  
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
  
  Lemma In_path : forall {A} x (t: cotree A),
    In x t -> exists p, x = lookup p t.
  Proof.
    intros A x t H.
    induction H as [|t H IH|t H IH].
    - exists Here; auto.
    - elim IH; clear IH; intros p IH; exists (Left p); auto.
    - elim IH; clear IH; intros p IH; exists (Right p); auto.
  Qed.
    
  (** *** Existential proofs on subtrees *)
  (** [Exists] defines an existential proof on the subtrees of
      a [cotree]; it's meaning is that in the [cotree], there will
      _eventually_ be a subtree for which a certain predicate [P] holds.
    *)

  Inductive Exists {A: Type} (P: cotree A -> Prop) (t: cotree A) : Prop :=
  | Exists_here  : P t -> Exists P t
  | Exists_left  : Exists P (left t) -> Exists P t
  | Exists_right : Exists P (right t) -> Exists P t.
  
  (** Again, we relate the more general [Exists] predicate to the previously
      defined [In] and [At] predicates.
    *)

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

  (** *** Universal proofs on subtrees *)
  (** [Forall] defines a proof on all subtrees of a [cotree]; it's meaning
      is that for all the subtrees of a [cotree] a predicate [P] holds. *)

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
  
  (** Below we define a few simple lemmas to help deconstrucing
      [Forall] proofs.
    *)

  Lemma Forall_here : forall {A} P (t: cotree A), Forall P t -> P t.
    intros A P t H; destruct H as [H0 HL HR]; assumption.
  Qed.

  Lemma Forall_left : forall {A} P (t: cotree A), Forall P t -> Forall P (left t).
    intros A P t H; destruct H as [H0 HL HR]; assumption.
  Qed.
    
  Lemma Forall_right : forall {A} P (t: cotree A), Forall P t -> Forall P (right t).
    intros A P t H; destruct H as [H0 HL HR]; assumption.
  Qed.
  
  (** And again, we relate the new predicate [Forall] to the previously
      defined predicates.
    *)

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
  
  (** ** Functions on CoTrees *)
  (** Below we shall introduce several usefull functions on [cotree]s. *)

  (** *** Maps over CoTrees *)
  (** The [map] function applies a function to every element of a [cotree]. *)
  
  Section map_def.

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
  
  (** *** Breadth-First Traversal of CoTrees *)
  (** _Current Status: though breadth-first traversal works, proving its correctness is quite hard_.
    *)

  Section bf_def.
    
    (** The implementation of [bf] as originally used in the paper
        is as follows.
<<
    bf :: Tree a -> [a]
    bf = concat . foldTree glue
      where
      glue (a,xs,ys) = [a] : zipWith (++) xs ys
>>
        We have, however, only recently started investigating translating
        this function to Coq, due to its dependency on [concat] (and therefore
        on proofs for [AlwaysExistsNonEmpty], which are quite hard to do.
        
        The implementation we use could instead be read as follows.
<<
    bf :: Tree a -> [a]
    bf t = bf_acc [t]
      where
      bf_acc :: [Tree a] -> [a]
      bf_acc ((Node l x r) : rest) = x : (bf_acc (rest ++ [l,r]))
>>

        Here [bf_acc] Performs a breadth-first walk over a list of [cotree]s, provided that
        the list is not empty.
      *)
  
    CoFixpoint bf_acc {A: Type} (ts: list (cotree A)) : nil <> ts -> colist A.
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

    (** And [bf] simply delegates to [bf_acc]. *)
    
    Definition bf {A: Type} (t: cotree A) : colist A.
      refine (bf_acc (t :: nil) _).
      apply nil_cons.
    Defined.

    Lemma bf_acc_hd {A} (ts: list (cotree A)) (H: nil <> ts) :
      CoList.hd (bf_acc ts H) = root (List.hd ts H).
    Proof.
      destruct ts as [|t ts].
      - exfalso; apply H; reflexivity.
      - destruct t; reflexivity.
    Qed.

    Theorem bf_correct : forall {A} x (t: cotree A),
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
