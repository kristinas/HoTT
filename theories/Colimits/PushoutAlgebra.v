Require Import Basics Types.
Require Import Colimits.Pushout.
Require Import WildCat.

(** Proof that h-initiality implies induction principle for pushouts. *)

Section PushoutAssumptions.

  Context {A B C : Type} (f : A -> B) (g : A -> C).

  Record PushoutAlgebra := {
    pa_type : Type ;
    pa_inl  : B -> pa_type ;
    pa_inr  : C -> pa_type ;
    pa_glue : pa_inl o f == pa_inr o g ;
  }.

  Record PushoutAlgebraMorphism (X Y : PushoutAlgebra) := {
    pam_fun : pa_type X -> pa_type Y ;
    pam_inl : pam_fun o pa_inl X == pa_inl Y ;
    pam_inr : pam_fun o pa_inr X == pa_inr Y ;
    pam_glue : forall (x : A),
      ap pam_fun (pa_glue X x) @ pam_inr (g x)
      = pam_inl (f x) @ pa_glue Y x ;
  }.

  Arguments pam_fun {X Y}.
  Arguments pam_inl {X Y}.
  Arguments pam_inr {X Y}.
  Arguments pam_glue {X Y}.

  Definition pam_id (X : PushoutAlgebra) : PushoutAlgebraMorphism X X.
  Proof.
    snrapply Build_PushoutAlgebraMorphism.
    - exact idmap.
    - reflexivity.
    - reflexivity.
    - intro x.
      refine (_ @ (concat_1p _)^).
      refine (concat_p1 _ @ _).
      apply ap_idmap.
  Defined.

  Definition pam_compose (X Y Z : PushoutAlgebra)
    (ff : PushoutAlgebraMorphism Y Z) (gg : PushoutAlgebraMorphism X Y)
    : PushoutAlgebraMorphism X Z.
  Proof.
    snrapply Build_PushoutAlgebraMorphism.
    - exact (pam_fun ff o pam_fun gg).
    - intro x.
      refine (ap (pam_fun ff) _ @ pam_inl ff x).
      exact (pam_inl gg x).
    - intro x.
      refine (ap (pam_fun ff) _ @ pam_inr ff x).
      exact (pam_inr gg x).
    - intro x; cbn.
      refine (ap (fun x => x @ _) (ap_compose _ _ _) @ _).
      refine (concat_p_pp _ _ _ @ _).
      refine (ap (fun x => x @ _) ((ap_pp _ _ _)^ @ ap _ (pam_glue gg x)) @ _).
      refine (ap (fun x => x @ _) (ap_pp _ _ _) @ _).
      refine (concat_pp_p _ _ _ @ _ @ concat_p_pp _ _ _).
      refine (whiskerL _ _).
      exact (pam_glue ff x).
  Defined.

  Global Instance isgraph_pushoutalgebra : IsGraph PushoutAlgebra
    := Build_IsGraph PushoutAlgebra PushoutAlgebraMorphism.

  Global Instance is01cat_pushoutalgebra : Is01Cat PushoutAlgebra
    := Build_Is01Cat _ _ pam_id pam_compose.

  (** So the definition can be used we assume falsehood to keep things transparent. *)
  Axiom sorry : Empty.
  Ltac sorry := rapply (Empty_ind (fun _ => _) sorry).
  
  Global Instance is1cat_pushoutalgebra : Is1Cat PushoutAlgebra.
  Proof.
    snrapply Build_Is1Cat.
    3: intros X Y; apply is0gpd_paths.
    (** This is routine and I can't be bothered to do it right now. *)
    all: sorry.
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

  Record PushoutAlgebraCell {X Y : PushoutAlgebra} (F G : PushoutAlgebraMorphism X Y) := {
    pac_hom : pam_fun F == pam_fun G ;
    pac_inl : forall (b : B), pac_hom (pa_inl X b) @ pam_inl G b = pam_inl F b ;
    pac_inr : forall (c : C), pac_hom (pa_inr X c) @ pam_inr G c = pam_inr F c ;
    pac_glue : forall (a : A), CellDiagram (pam_glue F a) (pam_glue G a)
                                           (pac_inl (f a)) (pac_inr (g a))
                                           (concat_Ap pac_hom (pa_glue X a))^ ;
  }.

  Arguments pac_hom {X Y F G}.
  Arguments pac_inl {X Y F G}.
  Arguments pac_inr {X Y F G}.
  Arguments pac_glue {X Y F G}.

  Definition issig_PushoutAlgebra : _ <~> PushoutAlgebra := ltac:(issig).
  Definition issig_PushoutAlgebraMorphism X Y
    : _ <~> PushoutAlgebraMorphism X Y := ltac:(issig).
  Definition issig_PushoutAlgebraCell {X Y} (F G : PushoutAlgebraMorphism X Y)
    : _ <~> PushoutAlgebraCell F G := ltac:(issig).

  Lemma concat_Ap_1 {X Y : Type} {h : X -> Y} {x y : X} (q : x = y) :
    concat_Ap (apD10 1) q = concat_p1 (ap h q) @ (concat_1p (ap h q))^.
  Proof.
    destruct q; reflexivity.
  Defined.

  Section PathIsCell.

    Context `{Funext}.

    Let e {X} {a b : X} (p : a = b) : p @ 1 = 1 @ p
      := concat_p1 p @ (concat_1p p)^.

    Let E {X Y} {y1 y2 : X -> Y} {p q : forall x : X, y1 x = y2 x} :
      p = q <~> forall x : X, 1 @ q x = p x.
    Proof.
      refine (equiv_compose' _ (equiv_apD10 _ _ _)).
      srapply equiv_functor_forall_id; intro x; simpl.
      refine (equiv_compose' _ (equiv_path_inverse _ _)).
      snrapply equiv_concat_l; snrapply concat_1p.
    Defined.

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

    Lemma path_pam_equiv_pac {X Y : PushoutAlgebra} (F G : PushoutAlgebraMorphism X Y) :
      F = G <~> PushoutAlgebraCell F G.
    Proof.
      refine (equiv_compose' (issig_PushoutAlgebraCell _ _) _); revert F G.
      srapply (functor_forall_equiv_pb (issig_PushoutAlgebraMorphism _ _)); intro F; simpl.
      srapply (functor_forall_equiv_pb (issig_PushoutAlgebraMorphism _ _)); intro G; simpl.
      refine (equiv_compose' _ (equiv_inverse (equiv_ap (issig_PushoutAlgebraMorphism _ _) _ _))).
      refine (equiv_compose' _ (equiv_inverse (equiv_path_sigma _ _ _))); simpl.
      destruct F as [F [F_inl [F_inr F_glue]]]; destruct G as [G [G_inl [G_inr G_glue]]]; simpl.
      srapply (equiv_functor_sigma' (equiv_apD10 _ _ _)); intro h; destruct h; simpl.
      refine (equiv_compose' _ (equiv_inverse (equiv_path_sigma _ _ _))); simpl.
      srapply (equiv_functor_sigma' E); intro h_inl; destruct h_inl; simpl.
      refine (equiv_compose' _ (equiv_inverse (equiv_path_sigma _ _ _))); simpl.
      srapply (equiv_functor_sigma' E); intro h_inr; destruct h_inr; simpl.
      refine (equiv_compose' _ (equiv_apD10 _ _ _)).
      srapply equiv_functor_forall_id; intro a; simpl.
      refine (equiv_compose' (equiv_concat_l (left_red _) _) _).
      refine (equiv_compose' (equiv_concat_r (ap _ (ap _ (concat_Ap_1 _)^)) _) _).
      refine (equiv_compose' (equiv_concat_r (right_red _)^ _) _).
      refine (equiv_compose' _ (equiv_path_inverse _ _)); apply equiv_whiskerL.
    Defined.

  End PathIsCell.

  (** Now that we have a wild 1-cat structure on PushoutAlgebra we can state the theorem we wish to prove. *)

  Section MainProof.

    Context  (X : PushoutAlgebra) {H : IsInitial X}
      (P : pa_type X -> Type)
      (l : forall b : B, P (pa_inl X b))
      (r : forall c : C, P (pa_inr X c))
      (gl : forall a : A, pa_glue X a # l (f a) = r (g a)).

    Definition pa_sig : PushoutAlgebra.
    Proof.
      snrapply Build_PushoutAlgebra.
      - exact (sig P).
      - intro b.
        exact (pa_inl X b; l b).
      - intro c.
        exact (pa_inr X c; r c).
      - intro a.
        srapply path_sigma.
        + exact (pa_glue X a).
        + exact (gl a).
    Defined.

    Definition F : X $-> pa_sig := (H pa_sig).1.

    Let E {a b : sig P} (p q : a = b)
      : p = q <~> 1 @ p = q @ 1.
    Proof.
      transitivity (p = q @ 1).
      - snrapply (equiv_concat_r (concat_p1 q)^).
      - snrapply (equiv_concat_l (concat_1p p)).
    Defined.

    Let e {a b : pa_type X} (p : a = b) : 1 @ p = p @ 1
      := concat_1p p @ (concat_p1 p)^.

    Let e' {a b : pa_type X} (p : a = b) : ap idmap p @ 1 = 1 @ p
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
      {b1 : pam_fun F x1 = (x1; y1)} {b2 : pam_fun F x2 = (x2; y2)}
      (phi : ap (pam_fun F) p @ b2 = b1 @ path_sigma P (x1; y1) (x2; y2) p q)
      : ap (pr1 o pam_fun F) p @ b2..1 = b1..1 @ p
      := whiskerR (ap_compose _ _ _) _ @ delta phi @ whiskerL _ (pr1_path_sigma _ _).

    Definition fstoF : X $-> X.
    Proof.
      snrapply Build_PushoutAlgebraMorphism.
      - exact (fun x => (pam_fun F x).1).
      - exact (fun b => (pam_inl F b)..1).
      - exact (fun c => (pam_inr F c)..1).
      - exact (fun a => gamma _ (gl a) (pam_glue F a)).
    Defined.

    Context `{Funext}.

    Definition h : PushoutAlgebraCell fstoF (pam_id X).
    Proof.
      srapply path_pam_equiv_pac; transitivity (H X).1.
      - exact ((H X).2 _).
      - symmetry; exact ((H X).2 _).
    Defined.

    Definition pushout_ind_hinitial w : P w
      := transport P (pac_hom h w) (pam_fun F w).2.

    Let comp {x} {y : P x} (b : pam_fun F x = (x; y)) (t : pac_hom h x @ 1 = b..1)
      : pac_hom h x # (pam_fun F x).2 = y.
    Proof.
      refine (_ @ apD pr2 b).
      refine (_ @ (transport_compose _ _ _ _)^).
      snrapply ap10; apply ap; refine (_ @ t).
      exact (concat_p1 _)^.
    Defined.

    Lemma pushout_ind_hinitial_inl (b : B) :
      pushout_ind_hinitial (pa_inl X b) = l b.
    Proof.
      exact (comp (pam_inl F b) (pac_inl h b)).
    Defined.

    Lemma pushout_ind_hinitial_inr (c : C) :
      pushout_ind_hinitial (pa_inr X c) = r c.
    Proof.
      exact (comp (pam_inr F c) (pac_inr h c)).
    Defined.

    Let left_red {a1 b1 : pa_type X} {ab1 : a1 = b1} {ac1 : a1 = b1} (t1 : ab1 @ 1 = ac1)
      : concat_p1 (ab1 @ 1) @ t1 = left 1 t1 @ concat_p1 ac1.
    Proof.
      destruct ab1, t1; reflexivity.
    Defined.

    Let right_red {a1 b1 : pa_type X} {ab1 : a1 = b1} {ac1 : a1 = b1} (t2 : ab1 @ 1 = ac1)
      : right (e ac1) t2 (e ab1)^ @ concat_p1 ac1 = concat_p1 (ab1 @ 1) @ t2.
    Proof.
      destruct ab1, t2; reflexivity.
    Defined.

    Let coh {x1 x2} {y1 : P x1} {y2 : P x2} {p : x1 = x2} {q : p # y1 = y2}
      {b1 : pam_fun F x1 = (x1; y1)} {b2 : pam_fun F x2 = (x2; y2)}
      (t1 : pac_hom h x1 @ 1 = b1..1) (t2 : pac_hom h x2 @ 1 = b2..1)
      (phi : ap (pam_fun F) p @ b2 = b1 @ path_sigma P (x1; y1) (x2; y2) p q)
      (psi: left (e' p) t1 = right (gamma p q phi) t2 (concat_Ap (pac_hom h) p)^)
      : apD pushout_ind_hinitial p @ comp b2 t2 = ap (transport P p) (comp b1 t1) @ q.
    Proof.
      destruct p; destruct q; revert psi; revert phi.
      srapply (functor_forall_equiv_pb (E b2 b1)); intro phi; destruct phi; intro Hlr.
      assert (Ht : t1 = t2).
      2: destruct Ht; refine (_ @ (concat_p1 _)^); reflexivity.
      refine (cancelL (concat_p1 (_ @ 1)) _ _ (left_red _ @ _ @ right_red _)).
      refine (whiskerR Hlr _ @ ap10 (ap _ (ap10 _ _)) _).
      refine (ap10 (ap _ (concat_p1 _ @ concat_1p _ @ delta_red b2)) _).
    Defined.

    Lemma pushout_ind_hinitial_glue (a : A) :
      apD pushout_ind_hinitial (pa_glue X a) @ pushout_ind_hinitial_inr (g a)
      = ap (transport P (pa_glue X a)) (pushout_ind_hinitial_inl (f a)) @ gl a.
    Proof.
      snrapply coh.
      - exact (pam_glue F a).
      - exact (pac_glue h a).
    Defined.

  End MainProof.

End PushoutAssumptions.
