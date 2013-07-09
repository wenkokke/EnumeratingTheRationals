(* begin hide *)
Require Import CoList.
Require Import CoTree.
Require Import PArith.
Require Import NArith.
Require Import QArith.
Require Import Recdef.
(* end hide *)

(** * Enumerating The Rationals: The Stern-Brocot Tree *)

(** _Current Status: while the implementation of the tree and the deforestation
    algorithm function perfectly, it is quite hard to prove properties such as the
    equivalence of our euclidian [gcd] and the implementation of the binary [gcd]
    algorithm that Coq's standard library uses_.
  *)
  
(** The second approach of enumerating the rationals explored in the paper is the
    construction and deforestation of the Stern-Brocot tree, explointing the relation
    between [igcd] and [ungcd] and the usage of [gcd] in the reduction algorithm for
    rational numbers.
    
    The Stern-Brocot tree maps the execution traces of the Euclidian [gcd] to reduced 
    rational numbers. The first few levels of the tree can be seen below.
    
  #
    <img style="width:100%;" alt="The Stern-Brocot Tree" src="stern_brocot.png" />
  #
  
    Below we will construct the Stern-Brocot tree, but first we'll prove a few lemmas
    on natural numbers.
  *)

Module SternBrocot.

  (** ** Additional Proofs on Natural Numbers *)
  (** In order to construct the Stern-Brocot tree, we required
      some simple lemmas on the natural numbers [N]. We use these
      lemmas to guarantee that [next] never generates a rational
      number with [0] as a denumerator. See below.
    *)

  Section N_properties.

    Local Open Scope N_scope. 

    (** Since we'll be working with natural numbers, we'll want
        to be able to easily convert them to rational numbers.
        The below definitions take care of that.
        
        Given a proof that [n] is not zero, [N_pos] will allow us to
        safely convert it to a [positive] number.
       *)
    
    Definition N_pos (n:N) : n<>0 -> positive.
      refine (match n as n' return n'<>0 -> positive with
                | 0      => fun h => _
                | Npos p => fun h => p
              end).
      exfalso; auto.
    Defined.
    
    (** Since any natural number is also an integer, we can always
        convert members of [N] to members of [Z].
      *)
  
    Definition N_Z (n:N) : Z :=
      match n with
        | 0      => Z0 
        | Npos n => Zpos n
      end.
      
    (** Furthermore, for the propagation of the nonzero proofs over
        the [next] function below, it is important to know that given
        a nonzero natural [n], we'll need the fact that the sum of [n]
        and some other natural number [m] is also nonzero.
      *)
    
    Lemma Npos_over_Nplus_l : forall n m : N,
      n <> 0 -> n + m <> 0.
    Proof.
      intros n m H; destruct n as [|n].
      - exfalso; auto.
      - destruct m as [|m]; simpl; discriminate.
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

  (** ** Construction of the Tree *)
  
  Section enum_def.

    Local Open Scope N_scope.
    
    (** The main issue with constructing the Stern-Brocot tree is that the [next]
        function passes along "pseudo"-rationals, such as $\frac{1}{0}$#1/0# and
        $\frac{1}{0}$#0/1#. In order to safely be able to construct rationals using
        these pseudo-rationals, we pass along proofs of the fact that the denumerator
        can never be zero.
        
        We call these pairs of pseudo-rationals [Qpair]s.
      *)

    Inductive Qpair : Type :=
    | qpair (a b c d : N) (HL: a<>0 \/ c<>0) (HR: b<>0 \/ d<>0) : Qpair.
    
    (** The [next] function that is used to unfold the tree can be seen 
        as follows (adapted from the paper), where [Qpair] is shorthand
        for the type [((Integer,Integer),(Integer,Integer))].
<<
    next :: Qpair -> (Qpair,Rational,Qpair)
    next ((m, n), (m', n')) = ((mm', n), mm' / nn', (m, nn'))
      where mm' = m + m'
            nn' = n + n'
>>
        Our translation of this stepper function to Coq can be seen below.
      *)
    
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
    
    (** Finally, we can construct the Stern-Brocot tree and enumeration,
        using the algorithm referred to as [rats4] in the original paper.
<<
    rats4 :: [Rational]
    rats4 = bf (unfold next ((0, 1), (1, 0)))
>>
        Below we first construct the tree, and later in the definition of
        [enum] we deforest this tree to an enumeration using a breadth-first
        traversal.
      *)

    Definition tree : cotree Q.
      refine (CoTree.unfold next (qpair 0 1 1 0 _ _)).
      - right ; discriminate.
      - left  ; discriminate.
    Defined.

    Definition enum : colist Q := CoTree.bf tree.
    
  End enum_def.
  
  (** ** Relation with the Greatest Common Divisor *)
  
  (** The paper initially explores the relation between the paths in the
      Stern-Brocot tree and the execution traces of the Euclidian algorithm
      for calculating the greatest common divisor (or gcd).
      
      An 'instrumental' version of the [gcd] algorithm is introduced.
<<
    igcd :: (Integer,Integer) -> (Integer,[Bool])
    igcd (m,n) =
      if m<n then step False (igcd (m,n−m)) else
      if m>n then step True  (igcd (m−n,n)) else (m,[ ])
      where step b (d,bs) = (d,b:bs)
>>
      In our implementation we use the [path] datatype for indexing [cotree]s
      instead of binary sequences, as the paper does. Our implementation of
      the [igcd] function and its derivatives [gcd] and [pgcd] can be found below.
    *)

  Section gcd_def.

    Local Open Scope positive_scope.
    
    (** First, however, we require a few lemmas to prove termination of the
        [igcd] algorithm. We prove its termination based on the decreasing of
        the _sum_ of its arguments, using [pairsum]. *)

    Section igcd_lemma.

      Definition pairsum (p: positive*positive) :=
        match p with
          | (m,n) => Pos.to_nat (m + n)
        end.
    
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
    
    Definition step (ps: path -> path) (acc: positive*path) :=
      match acc with (d,p0) => (d,ps p0) end.

    Function igcd (p: positive*positive) {measure pairsum p} :=
      match p with (m,n) => 
        if (m <? n) then step CoTree.Left  (igcd (m,(n - m))) else
        if (n <? m) then step CoTree.Right (igcd ((m - n),n)) else
        (m, CoTree.Here)
      end.
    Proof.
      (* prove termination for the first recursive call *)
      intros p m n Hp Hltb.
      pose proof (Pos.ltb_spec m n) as Hlt; destruct Hlt as [Hlt|Hlt].
      pose proof (Pos2Nat.is_pos m) as Om.
      pose proof (Pos2Nat.is_pos n) as On.
      simpl; rewrite 2!Pos2Nat.inj_add, 1!Pos2Nat.inj_sub. apply igcd_lemma1.
      - apply igcd_lemma3.
      - apply igcd_lemma3.
      - apply Pos2Nat.inj_lt; auto.
      - auto.
      - inversion Hltb.

      (* prove termination for the second recursive call *)
      - intros p m n Hp _ Hltb.
        pose proof (Pos.ltb_spec n m) as Hlt; destruct Hlt as [Hlt|Hlt].
        simpl; rewrite 2!Pos2Nat.inj_add; rewrite 1!Pos2Nat.inj_sub. apply igcd_lemma2.
        * apply igcd_lemma3.
        * apply igcd_lemma3.
        * auto.
        * inversion Hltb.
    Defined.

    (** The [gcd] function returns the first result of [igcd], i.e. the gcd. *)
    
    Definition gcd (x y: positive) := fst (igcd (x,y)).
    
    (** The [pgcd] function returns the second result of [igcd], i.e. the execution trace. *)
    
    Definition pgcd (x y: positive) := snd (igcd (x,y)).

    (** We would like to be able to prove equivalence between our Euclidian [gcd]
        algorithm, and the binary [gcd] in the Coq standard libraries, as this would
        allow us to use useful theorems such as [gcd_divide_l] and [gcd_divide_r].
      *)
    
    Theorem gcd_equiv : forall x y, Pos.gcd x y = gcd x y.
    Admitted.
    
    (** The [ungcd] algorithm presented in the paper translates effortlessly to Coq.
<<
    ungcd::(Integer,[Bool]) -> (Integer,Integer)
    ungcd (d,bs) = foldr undo (d,d) bs
      where
      undo False (m,n) = (m,n+m)
      undo True  (m,n) = (m+n,n)
>>
        Our translation of the algorithm can be seen below. We have inlined the [undo]
        function, and are using the recursion in our [path] structure instead of the
        [fold] function on binary sequences.
      *)
    
    Fixpoint ungcd_acc (p: path) (m n: positive) : positive*positive :=
      match p with
        | CoTree.Here    => (m,n)
        | CoTree.Left  p => ungcd_acc p m (n + m)
        | CoTree.Right p => ungcd_acc p (n + m) n
      end.

    Definition ungcd (p: positive*path) : positive*positive :=
      let g := fst p in ungcd_acc (snd p) g g.
      
    (** Lastly, we have explored a few claims stated in the paper,
        such as the relation between [igcd] and [ungcd].
      *)
    
    Theorem igcd_ungcd : forall m n, ungcd (igcd (m,n)) = (m,n).
    Proof.
      intros m n.
      induction m as [|m] using Pos.peano_ind.
      - induction n as [|n] using Pos.peano_ind.
        * reflexivity.
    Admitted.

    (** And the claim that all [path]s map to a unqiue rational number. *)

    Theorem ungcd_unique : forall p q,
      ungcd p = ungcd q -> p = q.
    Proof.
      intros p q H.
      case p as [x p].
      case q as [y q].
      induction p as [|p|p].
      - induction q as [|q|q].
        * replace x with y. reflexivity.
          apply (f_equal (@fst positive positive)) in H.
          compute in H.
          symmetry.
          assumption.
        * clear IHq; exfalso.
    Admitted.

    (** And the claim that if two rationals map to the same path, their
        reductions are also equal. *)
    
    Definition qred (m n: positive) : positive*positive.
    Admitted.

    Theorem pgcd_unique : forall m n m' n',
      pgcd m n = pgcd m' n' -> qred m n = qred m' n'.
    Admitted.

  End gcd_def.
    
End SternBrocot.