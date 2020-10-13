Require Import Basics Types.
Require Import Colimits.Pushout.
Require Import WildCat.

(** Proof that h-initiality implies induction principle for the circle. *)

Record CircleAlgebra := {
  ca_type : Type ;
  ca_base  : ca_type ;
  ca_loop : ca_base = ca_base ;
}.

Record CircleMorphism (X Y : CircleAlgebra) := {
  cm_fun : ca_type X -> ca_type Y ;
  cm_base : cm_fun (ca_base X) = ca_base Y ;
  cm_loop : ap cm_fun (ca_loop X) @ cm_base = cm_base @ ca_loop Y ;
}.

Arguments cm_fun {X Y}.
Arguments cm_base {X Y}.
Arguments cm_loop {X Y}.

Definition cm_id (X : CircleAlgebra) : CircleMorphism X X.
Proof.
  snrapply Build_CircleMorphism.
  - exact idmap.
  - reflexivity.
  - refine (concat_p1 _ @ ap_idmap _ @ (concat_1p _)^).
Defined.

Section CellDiagram.

  Context {X : Type} {a1 a2 b1 b2 c1 c2 : X}.
  Context {ab1 : a1 = b1} {ab2 : a2 = b2}.
  Context {ac1 : a1 = c1} {ac2 : a2 = c2}.
  Context {bc1 : b1 = c1} {bc2 : b2 = c2}.
  Context {a12 : a1 = a2} {b12 : b1 = b2} {c12 : c1 = c2}.
  Context (gamma1 : a12 @ ac2 = ac1 @ c12) (gamma2 : b12 @ bc2 = bc1 @ c12).
  Context (theta1 : ab1 @ bc1 = ac1) (theta2 : ab2 @ bc2 = ac2).
  Context (phi : ab1 @ b12 = a12 @ ab2).

  Local Definition left : (ab1 @ b12) @ bc2 = ac1 @ c12.
  Proof.
    refine (concat_pp_p _ _ _ @ whiskerL _ gamma2 @ _).
    refine (concat_p_pp _ _ _ @ whiskerR theta1 _).
  Defined.

  Local Definition right : (ab1 @ b12) @ bc2 = ac1 @ c12.
  Proof.
    refine (whiskerR phi _ @ concat_pp_p _ _ _ @ _).
    refine (whiskerL _ theta2 @ gamma1).
  Defined.

  Local Definition CellDiagram := left = right.

End CellDiagram.

Record CircleCell {X Y : CircleAlgebra} (F G : CircleMorphism X Y) := {
  cc_hom : cm_fun F == cm_fun G ;
  cc_base : cc_hom (ca_base X) @ cm_base G = cm_base F ;
  cc_loop : CellDiagram (cm_loop F) (cm_loop G) cc_base cc_base (concat_Ap cc_hom (ca_loop X))^ ;
}.

Arguments cc_hom {X Y F G}.
Arguments cc_base {X Y F G}.
Arguments cc_loop {X Y F G}.

Definition issig_CircleAlgebra : _ <~> CircleAlgebra := ltac:(issig).
Definition issig_CircleMorphism X Y
  : _ <~> CircleMorphism X Y := ltac:(issig).
Definition issig_CircleCell {X Y} (F G : CircleMorphism X Y)
  : _ <~> CircleCell F G := ltac:(issig).

Lemma concat_Ap_1 {X Y : Type} {h : X -> Y} {x y : X} (q : x = y) :
  concat_Ap (apD10 1) q = concat_p1 (ap h q) @ (concat_1p (ap h q))^.
Proof.
  destruct q; reflexivity.
Defined.

Section PathIsCell.

  Context `{Funext}.

  Let E {X} {a b : X} {p q : a = b}
    : p = q <~> 1 @ q = p.
  Proof.
    transitivity (q = p).
    - snrapply equiv_path_inverse.
    - snrapply (equiv_concat_l (concat_1p q)).
  Defined.

  Let e {X} {a b : X} (p : a = b) : p @ 1 = 1 @ p
    := concat_p1 p @ (concat_1p p)^.

  Let left_red {X} {a1 b2 c1 c2 : X} {ac1 : a1 = c1} {bc2 : b2 = c2}
    {b12 : a1 = b2} {c12 : c1 = c2} (gamma2 : b12 @ bc2 = ac1 @ c12) :
    left gamma2 (concat_1p ac1 @ 1) = whiskerR (concat_1p b12) bc2 @ gamma2.
  Proof.
    destruct b12, c12, bc2; revert gamma2.
    srapply (functor_forall_equiv_pb (equiv_concat_r (concat_p1 ac1)^ _)).
    intro gamma2; destruct gamma2; reflexivity.
  Defined.

  Let right_red {X} {a1 a2 c1 c2 : X} {ac1 : a1 = c1} {ac2 : a2 = c2}
    {a12 : a1 = a2} {c12 : c1 = c2} (gamma1 : a12 @ ac2 = ac1 @ c12) :
    right gamma1 (concat_1p ac2 @ 1) (e a12)^ = whiskerR (concat_1p a12) ac2 @ gamma1.
  Proof.
    destruct a12, c12, ac2; revert gamma1.
    srapply (functor_forall_equiv_pb (equiv_concat_r (concat_p1 ac1)^ _)).
    intro gamma1; destruct gamma1; reflexivity.
  Defined.

  Lemma path_cm_equiv_cc {X Y : CircleAlgebra} (F G : CircleMorphism X Y) :
    F = G <~> CircleCell F G.
  Proof.
    refine (equiv_compose' (issig_CircleCell _ _) _); revert F G.
    srapply (functor_forall_equiv_pb (issig_CircleMorphism _ _)); intro F; simpl.
    srapply (functor_forall_equiv_pb (issig_CircleMorphism _ _)); intro G; simpl.
    refine (equiv_compose' _ (equiv_inverse (equiv_ap (issig_CircleMorphism _ _) _ _))).
    refine (equiv_compose' _ (equiv_inverse (equiv_path_sigma _ _ _))); simpl.
    destruct F as [F [F_base F_loop]]; destruct G as [G [G_base G_loop]]; simpl.
    srapply (equiv_functor_sigma' (equiv_apD10 _ _ _)); intro h; destruct h; simpl.
    refine (equiv_compose' _ (equiv_inverse (equiv_path_sigma _ _ _))); simpl.
    srapply (equiv_functor_sigma' E); intro h_base; destruct h_base; simpl.
    refine (equiv_compose' (equiv_concat_l (left_red _) _) _).
    refine (equiv_compose' (equiv_concat_r (ap _ (ap _ (concat_Ap_1 _)^)) _) _).
    refine (equiv_compose' (equiv_concat_r (right_red _)^ _) _).
    refine (equiv_compose' _ (equiv_path_inverse _ _)); apply equiv_whiskerL.
  Defined.

End PathIsCell.

Section MainProof.

  Context (X : CircleAlgebra).
  Context {H : forall (Y : CircleAlgebra), Contr (CircleMorphism X Y)}.
  Context (P : ca_type X -> Type).
  Context (b : P (ca_base X)).
  Context (l : ca_loop X # b = b).

  Definition ca_sig : CircleAlgebra.
  Proof.
    snrapply Build_CircleAlgebra.
    - exact (sig P).
    - exact (ca_base X; b).
    - srapply path_sigma.
      + exact (ca_loop X).
      + exact l.
  Defined.

  Definition F : CircleMorphism X ca_sig := center _.

    Let e {a b : ca_type X} (p : a = b) : 1 @ p = p @ 1
      := concat_1p p @ (concat_p1 p)^.

    Let e' {a b : ca_type X} (p : a = b) : ap idmap p @ 1 = 1 @ p
      := concat_p1 (ap idmap p) @ ap_idmap p @ (concat_1p p)^.

    Let delta {x y z w : sig P} {xy : x = y} {yz : y = z} {xw : x = w} {wz : w = z}
      : xy @ yz = xw @ wz -> xy..1 @ yz..1 = xw..1 @ wz..1
      := fun phi => ((ap_pp _ _ _)^ @ ap _ phi @ ap_pp _ _ _).

    Let delta_red {x z : sig P} (xz : x = z)
      : delta (concat_1p xz @ (1 @ (concat_p1 xz)^)) = e xz..1.
    Proof.
      destruct xz; reflexivity.
    Defined.

    Let gamma {x1 x2} {y1 : P x1} {y2 : P x2} (p : x1 = x2) (q : p # y1 = y2)
      {b1 : cm_fun F x1 = (x1; y1)} {b2 : cm_fun F x2 = (x2; y2)}
      (phi : ap (cm_fun F) p @ b2 = b1 @ path_sigma P (x1; y1) (x2; y2) p q)
      : ap (pr1 o cm_fun F) p @ b2..1 = b1..1 @ p
      := whiskerR (ap_compose _ _ _) _ @ delta phi @ whiskerL _ (pr1_path_sigma _ _).

    Definition fstoF : CircleMorphism X X.
    Proof.
      snrapply Build_CircleMorphism.
      - exact (fun x => (cm_fun F x).1).
      - exact ((cm_base F)..1).
      - exact (gamma _ l (cm_loop F)).
    Defined.

    Context `{Funext}.

    Definition h : CircleCell fstoF (cm_id X).
    Proof.
      srapply path_cm_equiv_cc; apply path_contr.
    Defined.

    Definition circle_ind_hinitial w : P w
      := transport P (cc_hom h w) (cm_fun F w).2.

    Let comp {x} {y : P x} (g : cm_fun F x = (x; y)) (t : cc_hom h x @ 1 = g..1)
      : cc_hom h x # (cm_fun F x).2 = y.
    Proof.
      refine (_ @ apD pr2 g).
      refine (_ @ (transport_compose _ _ _ _)^).
      snrapply ap10; apply ap; refine (_ @ t).
      exact (concat_p1 _)^.
    Defined.

    Lemma circle_ind_hinitial_base :
      circle_ind_hinitial (ca_base X) = b.
    Proof.
      exact (comp (cm_base F) (cc_base h)).
    Defined.

    Let left_red {a1 b1 : ca_type X} {ab1 : a1 = b1} {ac1 : a1 = b1} (t1 : ab1 @ 1 = ac1)
      : concat_p1 (ab1 @ 1) @ t1 = left 1 t1 @ concat_p1 ac1.
    Proof.
      destruct ab1, t1; reflexivity.
    Defined.

    Let right_red {a1 b1 : ca_type X} {ab1 : a1 = b1} {ac1 : a1 = b1} (t2 : ab1 @ 1 = ac1)
      : right (e ac1) t2 (e ab1)^ @ concat_p1 ac1 = concat_p1 (ab1 @ 1) @ t2.
    Proof.
      destruct ab1, t2; reflexivity.
    Defined.

    Let E {x y : sig P} {p q : x = y}
      : p = q <~> 1 @ p = q @ 1.
    Proof.
      transitivity (p = q @ 1).
      - snrapply (equiv_concat_r (concat_p1 q)^).
      - snrapply (equiv_concat_l (concat_1p p)).
    Defined.

    Let coh {x1 x2} {y1 : P x1} {y2 : P x2} {p : x1 = x2} {q : p # y1 = y2}
      {b1 : cm_fun F x1 = (x1; y1)} {b2 : cm_fun F x2 = (x2; y2)}
      (t1 : cc_hom h x1 @ 1 = b1..1) (t2 : cc_hom h x2 @ 1 = b2..1)
      (phi : ap (cm_fun F) p @ b2 = b1 @ path_sigma P (x1; y1) (x2; y2) p q)
      (psi: left (e' p) t1 = right (gamma p q phi) t2 (concat_Ap (cc_hom h) p)^)
      : apD circle_ind_hinitial p @ comp b2 t2 = ap (transport P p) (comp b1 t1) @ q.
    Proof.
      destruct p; destruct q; revert psi; revert phi.
      srapply (functor_forall_equiv_pb E); intro phi; destruct phi; intro Hlr.
      assert (Ht : t1 = t2).
      2: destruct Ht; refine (_ @ (concat_p1 _)^); reflexivity.
      refine (cancelL (concat_p1 (_ @ 1)) _ _ (left_red _ @ _ @ right_red _)).
      refine (whiskerR Hlr _ @ ap10 (ap _ (ap10 _ _)) _).
      refine (ap10 (ap _ (concat_p1 _ @ concat_1p _ @ delta_red b2)) _).
    Defined.

    Lemma circle_ind_hinitial_loop :
      apD circle_ind_hinitial (ca_loop X) @ circle_ind_hinitial_base
      = ap (transport P (ca_loop X)) (circle_ind_hinitial_base) @ l.
    Proof.
      snrapply coh.
      - exact (cm_loop F).
      - exact (cc_loop h).
    Defined.

  End MainProof.
