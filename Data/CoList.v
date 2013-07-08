(* begin hide *)
Require Import List.
Require Import Streams.
(* end hide *)

(** * CoLists *)

Module CoList.

  (** ** Defining CoLists *)
  (** A [colist] is defined by analogy to the [Stream] datatype,
      so that we can use the high-level predicates defined in the
      [Coq.Lists.Streams] module. *)

  Notation colist         := Stream.
  Notation cocons         := Cons.
  Notation hd             := hd.
  Notation tl             := tl.
  Notation map            := map.
  Notation Eq             := EqSt.
  Notation Eq_refl        := EqSt_reflex.
  Notation Eq_sym         := sym_EqSt.
  Notation Eq_trans       := trans_EqSt.
  Notation Exists         := Exists.
  Notation Exists_here    := Here.
  Notation Exists_further := Further.
  Notation Forall         := ForAll.
  Notation Always         := HereAndFurther.
  Notation Forall_coind   := ForAll_coind.
  Notation lookup         := Str_nth.

  (** We'd like [lookup] to be transparent. *)

  Hint Unfold lookup.

  (** Constructing [colist]s is done by iteratively unfolding values. *)

  CoFixpoint unfold {A B: Type} (f: B -> (A*B)) (e: B) : colist A :=
    match f e with
      | (x,xs) => cocons  x (unfold f xs)
    end.
    
  (** Furthermore, we can limit [colist]s to [list]s by taking any finite prefix. *)

  Fixpoint take {A: Type} (n: nat) (xs: colist A) : list A :=
    match n with
      | O => nil
      | S n =>
        match xs with
          | cocons x xs => cons x (take n xs)
        end
    end.
    
  (** ** Properties on CoLists *)
  (** We need some ways to prove properties on [colist]s.
      The simpelest of such proves is to prove that an [x]
      is an element of a certain [colist].
    *)

  Inductive In {A: Type} (x: A) (xs: colist A) : Prop :=
  | In_here    : (x = hd xs) -> In x xs
  | In_further : In x (tl xs) -> In x xs.
  
  (** Below we define [At], which turns a witness index into
      a [colist] into a proof that an element is in the [colist]
      (at that position).
    *)
  
  Definition At : forall {A: Type} (x: A) (xs: colist A) (n: nat), (x = lookup n xs) -> In x xs.
  Proof.
    intros A x xs n; generalize xs; clear xs.
    induction n as [|n].
    - apply In_here.
    - intro xs; destruct xs as [y ys]; unfold lookup in *; simpl in *; intro H.
      apply IHn in H; apply In_further; simpl; assumption.
  Defined.

  (** Furthermore, we define the relations between the [In] predicate,
      and the predefined [Exists] and [Forall] predicates.
    *)
  
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
  
  (** ** Concatinating an infinite list of lists *)
  (** We'll need a function to concatinate an infinite list of lists
      in order to define the naive enumeration of rationals later on.
      
      We can only do this if we have a guarantee that always,
      eventually there will be some list that isn't [nil], as an infinite
      list of [nil]s would never produce a [cocons].
    *)

  Definition AlwaysExistsNonEmpty {A: Type} (xs: colist (list A)) :=
    Forall (Exists (fun ys => nil <> hd ys)) xs.
  
  (** However, this notion is rather hard to prove, and since in most
      cases none of the [list]s will be [nil], we'll allow a proof of
      [AlwaysExistsNonEmpty] based on a proof of [AlwaysNonEmpty], using
      the [Always_AlwaysExists] lemma.
    *)

  Definition AlwaysNonEmpty {A: Type} (xs: colist (list A)) :=
    Forall (fun ys => nil <> hd ys) xs.
  
  Lemma Always_AlwaysExists : forall {A: Type} (P: colist A -> Prop) (xs: colist A),
    Forall P xs -> Forall (Exists P) xs.
  Proof.
    cofix.
    intros A P xs H; case H as [H0 H1].
    constructor.
    - constructor; assumption.
    - apply Always_AlwaysExists in H1; assumption.
  Qed.
  
  (** Since the [concat] function using proofs of the type [AlwaysExistsNonEmpty]
      is also rather hard to write, the current version is using the much stronger
      predicate [AlwaysNonEmpty].
      
      _TODO: Update [concat] to depend only on the weakened [AlwaysExistsNonEmpty]_.
    *)

  CoFixpoint concat {A: Type} (l: colist (list A)) : AlwaysNonEmpty l -> colist A.
    intro H.
    case l as [xs l'].
    case xs as [|y ys]; [case H as [H _]; exfalso; apply H; reflexivity| ].
    case ys as [|z zs].
    - apply (cocons y),(concat A l'); case H as [_ H]; auto.
    - apply (cocons y),(concat A (cocons (z :: zs) l')).
      case H as [_ H].
      constructor; [apply nil_cons|apply H].
  Defined.
  
  (** To check the function of [concat], we can run a small testcase. *)

  Definition test1 : colist (list nat) := unfold (fun x => (1 :: 2 :: nil, x)) 1.
  
  Lemma AlwaysNonEmpty_test1 : AlwaysNonEmpty test1.
  Proof. cofix; constructor; [apply nil_cons|auto]. Qed.

  Example test1_concat : (take 4 (concat test1 AlwaysNonEmpty_test1)) = 1 :: 2 :: 1 :: 2 :: nil.
  Proof. reflexivity. Qed.

End CoList.

Notation colist := CoList.colist.
Notation cocons := CoList.cocons.
