(* begin hide *)
Require Import CoList.
Require Import CoTree.
Require Import PArith.
Require Import QArith.
(* end hide *)

(** * Enumerating The Rationals: Naive Tree *)

(** _Current Status: it seems to be quite diffucult to prove the correctness
    of [find] on a specific tree. The problem with an induction proof here is
    that the tree's structure is hard-coded in the [find] function, but is
    passed as an argument to the [lookup] function_.
  *)
  
(** Though not presented in the paper, we have constructed this simple
    example to test the CoTree module, and the general proof strategy.
    
    The properties of this naive approach are even worse than those of
    the naive enumeration presented in [NaiveEnum], as the tree will
    contain many duplicates of the same _unreduced_ rational.
  *)

Module Naive.

  (** The [next] function for this tree can be seen as the equivalent Haskell function below.
<<
    next (n,d) = ((n + 1, d), n / d, (n, d + 1))
>>
      Below you can find the Coq translation of this function, as well as the [tree] and [enum]
      definition using this function.
    *)

  Definition next (p: positive*positive) : (positive*positive)*Q*(positive*positive) :=
    match p with (n,d) => ((Pos.succ n, d), Z.pos n # d, (n, Pos.succ d)) end.

  Definition tree := CoTree.unfold next (1,1)%positive.

  Definition enum := CoTree.bf tree.
  
  (** Next, we define a [find] function that maps rationals to their position in the
      tree--in this case, it maps it to the rightmost version.
      The idea is that proving the correctness of this function will bring us a long
      way towards proving our enumeration.
    *)
  
  Definition findp (n d: positive) : path :=
    Pos.peano_rec
      (*Type*) (fun _ => path)
      (*Zero*) (Pos.peano_rec
               (*Type*) (fun _ => path)
               (*Zero*) (CoTree.Here)
               (*Succ*) (fun _ p => CoTree.Right p)
               (*Args*) d
               )
      (*Succ*) (fun _ p => CoTree.Left p)
      (*Args*) n.

  Lemma findp_l (n d: positive) : findp (Pos.succ n) d = CoTree.Left (findp n d).
  Proof.
    unfold findp,Pos.peano_rec.
    rewrite Pos.peano_rect_succ.
    reflexivity.
  Qed.

  Lemma findp_r (d: positive) : findp 1 (Pos.succ d) = CoTree.Right (findp 1 d).
  Proof.
    unfold findp,Pos.peano_rec.
    rewrite Pos.peano_rect_succ.
    reflexivity.
  Qed.

  (** We have to somehow prove a duality between [next] and [findp],
      where in [next] if [n] increases we consume a [Left] path, if [d]
      increases we consume a [Right] path, and in [findp] we generate
      a [Left] path as long as we can consume successors of [n], and 
      [Right] paths as long as we can consume successors of [d].
    *)

  Lemma findp_correct (n d: positive) : CoTree.lookup (findp n d) tree = 'n # d.
  Proof.
    unfold tree.
    induction n as [|n] using Pos.peano_ind.
    - induction d as [|d] using Pos.peano_ind.
      * reflexivity.
      * rewrite findp_r.
  Admitted.

  Definition find (q: Q) : 0 < q -> CoTree.path.
    intros Hq.
    destruct q as [n d].
    destruct n as [|n|n]; try discriminate Hq.
    apply (findp n d).
  Defined.
  
  Theorem find_correct (q: Q) (H: 0 < q) : CoTree.lookup (find q H) tree = q.
  Proof.
    case q as [n d].
    case n as [|n|n].
    - inversion H.
    - unfold find; apply findp_correct.
    - inversion H.
  Qed.
End Naive.
