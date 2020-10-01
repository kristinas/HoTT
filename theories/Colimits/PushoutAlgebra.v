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

  (** Now that we have a wild 1-cat structure on PushoutAlgebra we can state the theorem we wish to prove. *)

  Section MainProof.

    Context  (X : PushoutAlgebra) {H : IsInitial X}
      (P : pa_type X -> Type)
      (l : forall b : B, P (pa_inl X b))
      (r : forall c : C, P (pa_inr X c))
      (gl : forall a : A, transport P (pa_glue X a) (l (f a)) = r (g a)).

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

    Definition h : X $-> pa_sig := (H pa_sig).1.

    Definition isinitial_initial_morphism
      : forall g : X $-> pa_sig, g = h
      := (H pa_sig).2.

    Lemma lemma1 : pr1 o pam_fun h == idmap.
    Proof.
      simpl.
    Admitted.

    Theorem pushout_ind_hinitial : forall w : pa_type X, P w.
    Proof.
      intro w.
      refine (transport P (lemma1 w) _).
      apply pr2.
    Defined.

  End MainProof.

End PushoutAssumptions.
