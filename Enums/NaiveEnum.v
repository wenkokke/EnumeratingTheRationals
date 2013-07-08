(* begin hide *)
Require Import List.
Require Import CoList.
Require Import PArith.
Require Import QArith.
Require Import Recdef.
(* end hide *)

(** * Enumerating The Rationals: Naive Approach *)

(** _Current Status: although the function quite easily translates to
    Coq, we require a proof of [AlwaysExistsNonEmpty] in order to use
    the [concat] function; at the moment this is still the bottleneck_.
  *)
  
(** The first explored approach to enumerating the rationals in the paper
    is a naive approach of deconstructing the following matrix.
    
    #
    <blockquote><table>
    <tr><td> 1/1      </td><td> 2/1 </td><td> 3/1 </td><td> &hellip; </td><td> m/1 </td></tr>
    <tr><td> 1/2      </td><td> 2/2 </td><td> 3/2 </td><td>          </td><td> m/2 </td></tr>
    <tr><td> 1/3      </td><td> 2/3 </td><td> 3/3 </td><td>          </td><td> m/3 </td></tr>
    <tr><td> &vellip; </td><td>     </td><td>     </td><td> &dtdot;  </td><td>     </td></tr>
    <tr><td> 1/n      </td><td> 2/n </td><td> 3/n </td><td>          </td><td> m/n </td></tr>
    </table></blockquote>
    #
    
    Which the original paper renders in Haskell as follows.
<<
    rats2 :: [Rational]
    rats2 = concat [[ m / (d - m) | m <- [1..d -1]]| d <- [2..]]
>>  
    Below we'll attempt to translate this function to Coq.
  *)

Module NaiveEnum.
  
  Local Open Scope positive_scope.
  
  (** ** Working with Enumerations *)
  
  (** First, we'll need to implement the notations "[[n..]]" and "[[m..n]]",
      which Haskell translates to [enumFrom n] and [enumFromTo m n].
      
      [enumFrom] creates an infinite list, counting from the given number.
    *)

  Definition enumFrom n := CoList.unfold (fun n => (n,Pos.succ n)) n.

  (** [enumFromTo] creates a finite list, counting from the first number
      upto the second number.
    *)

  Fixpoint enumFromTo' n (m: nat) := 
    match m with
      | O   => nil
      | S m => cons n (enumFromTo' (n + 1) m)
    end.

  Definition enumFromTo n m :=
    if (m <=? n) then nil else enumFromTo' n (Pos.to_nat (m - n)).

  (** ** Constructing the Enumeration *)
  
  (** Then, before we can define the final enumeration, we will need some lemmas
      to help us prove [AlwaysExistsNonEmpty] on the intermediate result.
    *)
  
  Lemma map_nil_cons : forall {A B} (f: A -> B) xs, nil <> xs -> nil <> (map f xs).
  Proof.
    intros A B f xs H.
    case xs as [|x xs].
    - exfalso; apply H; reflexivity.
    - simpl; apply nil_cons.
  Qed.
  
  (** For our translation we have rewritten the original Haskell code to the the
      equivalent code below, which gets rid of the list comprehensions.
<<
    rats2 :: [Rational]
    rats2 = concat (map (\d -> map (\m -> m / (d - m)) [1..d-1]) [2..])
>>
      Finally, we can enumerate the rationals.
    *)

  Definition enum : colist Q.
    refine (CoList.concat (CoList.map (fun d => List.map (fun m => 'm # (d - m)) (enumFromTo 1 d)) (enumFrom 2)) _).
  Admitted.

End NaiveEnum.
