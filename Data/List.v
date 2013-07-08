(* begin hide *)
Require Import List.
Require Export List.
(* end hide *)

(** ** Lists *)
(** We require a small extension to the default List module.
    Therefore, we both import and export the default List module.
  *)

Module List.

  (** The below function allows for the safe removal of
      a [list]'s head element when given a proof that the
      list is not [nil].
    *)
  
  Definition hd {A} (xs: list A) : nil <> xs -> A.
    refine(match xs as ys return nil <> ys -> A with
             | nil      => fun h => _
             | cons x _ => fun h => x
           end).
    exfalso; apply h; reflexivity.
  Defined.

End List.