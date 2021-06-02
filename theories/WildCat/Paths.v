Require Import Basics.
Require Import WildCat.Core.

(** * Path groupoids as wild categories *)

(** Not global instances for now *)
Local Instance isgraph_paths (A : Type) : IsGraph A.
Proof.
  constructor.
  intros x y; exact (x = y).
Defined.

Local Instance is01cat_paths (A : Type) : Is01Cat A.
Proof.
  unshelve econstructor.
  - intros a; reflexivity.
  - intros a b c q p; exact (p @ q).
Defined.

Local Instance is0gpd_paths (A : Type) : Is0Gpd A.
Proof.
  constructor.
  intros x y p; exact (p^).
Defined.

Local Instance is1cat_paths (A : Type) : Is1Cat A.
Proof.
  unshelve econstructor.
  { intros a b c g; split; intros h i j.
    exact (whiskerR j g). }
  { intros a b c g; split; intros h i j.
    exact (whiskerL g j). }
  { intros a b c d f g h.
    apply concat_p_pp. }
  1: intros a b f; apply concat_p1.
  intros a b f; apply concat_1p.
Defined.
    