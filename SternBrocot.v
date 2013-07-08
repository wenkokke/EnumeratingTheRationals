Require Import CoList.
Require Import CoTree.
Require Import PArith.
Require Import NArith.
Require Import QArith.
Require Import Recdef.

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

  Section gcd_def.

    Local Open Scope positive_scope.

    (** *** Computational Trace of a GCD Computation *)

    Definition step (qs: path -> path) (acc: positive*path) :=
      match acc with
        | (d,q0) => (d,qs q0)
      end.

    Definition pairsum (p: positive*positive) :=
      match p with
        | (m,n) => Pos.to_nat (m + n)
      end.

    Section igcd_lemma.
      Local Open Scope nat_scope.

      Lemma igcd_lemma1 : forall m n, m<>0 -> n<>0 -> m<n -> (m + (n - m)) < (m + n).
      Proof. intros m n Om On Hlt; omega. Qed.
      Lemma igcd_lemma2 : forall m n, m<>0 -> n<>0 -> (m - n + n) < (m + n).
      Proof. intros m n Om On; omega. Qed.
      Lemma igcd_lemma3 : forall n, Pos.to_nat n <> 0.
      Proof.
        intro n; pose proof (Pos2Nat.is_pos n) as H.
        simpl; apply not_eq_sym,lt_O_neq,Pos2Nat.is_pos.
      Qed.

    End igcd_lemma.

    Function igcd (p: positive*positive) {measure pairsum p} :=
      match p with (m,n) => 
        if (m <? n) then step CoTree.Left  (igcd (m,(n - m))) else
        if (n <? m) then step CoTree.Right (igcd ((m - n),n)) else
        (m, CoTree.Here)
      end.
    Proof.
      intros p m n Hp Hltb.
      pose proof (Pos.ltb_spec m n) as Hlt; destruct Hlt as [Hlt|Hlt].
      pose proof (Pos2Nat.is_pos m) as Om.
      pose proof (Pos2Nat.is_pos n) as On.
      simpl; rewrite 2!Pos2Nat.inj_add, 1!Pos2Nat.inj_sub. apply igcd_lemma1.
      (**) apply igcd_lemma3.
      (**) apply igcd_lemma3.
      (**) apply Pos2Nat.inj_lt; auto.
      (**) auto.
      simpl. rewrite 2!Pos2Nat.inj_add, 1!Pos2Nat.inj_sub. apply igcd_lemma1.
      (**) apply igcd_lemma3.
      (**) apply igcd_lemma3.
      (**) apply Pos2Nat.inj_lt; auto.
      (**) inversion Hltb.
      (**) inversion Hltb.

      intros p m n Hp _ Hltb.
      pose proof (Pos.ltb_spec n m) as Hlt; destruct Hlt as [Hlt|Hlt].
      simpl; rewrite 2!Pos2Nat.inj_add; rewrite 1!Pos2Nat.inj_sub. apply igcd_lemma2.
      (**) apply igcd_lemma3.
      (**) apply igcd_lemma3.
      (**) auto.
      simpl; rewrite 2!Pos2Nat.inj_add; rewrite 1!Pos2Nat.inj_sub. apply igcd_lemma2.
      (**) apply igcd_lemma3.
      (**) apply igcd_lemma3.
      (**) inversion Hltb.
    Defined.

    Definition gcd (x y: positive) := fst (igcd (x,y)).
    Definition pgcd (x y: positive) := snd (igcd (x,y)).

    Theorem gcd_equiv : forall x y, Pos.gcd x y = gcd x y.
    Admitted.
    Theorem gcd_divide_l : forall x y, (gcd x y | x).
    Admitted.
    Theorem gcd_divide_r : forall x y, (gcd x y | y).
    Admitted.
    Definition qred (n d: positive) : Q.
    Admitted.
      
  End gcd_def.
    
End SternBrocot.