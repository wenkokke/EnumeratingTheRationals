(* begin hide *)
Require Import List.
Require Import CoList.
Require Import PArith.
Require Import QArith.
Require Import Recdef.
(* end hide *)

(** * Enumerating The Rationals: Naive Approach *)

Module NaiveEnum.
  
  Local Open Scope positive_scope.

  Definition enumFrom n := CoList.unfold (fun n => (n,Pos.succ n)) n.

  Fixpoint stepwise n (m: nat) := 
    match m with
      | O   => nil
      | S m => cons n (stepwise (n + 1) m)
    end.

  Definition enumFromTo n m :=
    if (m <=? n) then nil else stepwise n (Pos.to_nat (m - n)).
  
  (** Define the rats2 enumeration. *)

  Lemma enumFromTo_nil : forall n, 1 < n -> nil <> enumFromTo 1 n.
  Proof.
    intros n H.
    induction n as [|n] using Pos.peano_ind.
    - inversion H.
  Admitted.

  Lemma map_nil_cons : forall {A B} (f: A -> B) xs, nil <> xs -> nil <> (map f xs).
  Proof.
    intros A B f xs H.
    case xs as [|x xs].
    - exfalso; apply H; reflexivity.
    - simpl; apply nil_cons.
  Qed.

  Definition enum : colist Q.
    refine (CoList.concat (CoList.map (fun d => List.map (fun m => 'm # (d - m)) (enumFromTo 1 d)) (enumFrom 2)) _).
  Admitted.

End NaiveEnum.
