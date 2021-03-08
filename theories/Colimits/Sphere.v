Require Import Basics Types.

Section SuspensionAssumptions.

  (** Suspension assumptions. *)
  Context (Susp : Type -> Type).
  Context (N : forall X, Susp X).
  Context (S : forall X, Susp X).
  Context (M : forall X (x : X), N X = S X).

  Arguments N {X}.
  Arguments S {X}.
  Arguments M {X}.

  Context (ind : forall X (P : Susp X -> Type) (n : P N) (s : P S)
    (m : forall x, M x # n = s) (w : Susp X), P w).

  Arguments ind {X}.

  Context (ind_N : forall X (P : Susp X -> Type) (n : P N) (s : P S)
    (m : forall x, M x # n = s), ind P n s m N = n).

  Context (ind_S : forall X (P : Susp X -> Type) (n : P N) (s : P S)
    (m : forall x, M x # n = s), ind P n s m S = s).

  Arguments ind_N {X}.
  Arguments ind_S {X}.

  Context (ind_M : forall X (P : Susp X -> Type) (n : P N) (s : P S) (m : forall x, M x # n = s) (x : X),
    apD (ind P n s m) (M x) @ ind_S P n s m = ap (transport P (M x)) (ind_N P n s m) @ m x).

  Arguments ind_M {X}.

  Definition rec X P (n : P) (s : P) (m : X -> n = s)
    : Susp X -> P.
  Proof.
    snrapply (ind _ n s); intro x; refine (transport_const _ _ @ m x).
  Defined.

  Arguments rec {X}.

  Definition rec_N X P (n : P) (s : P) (m : X -> n = s)
    : rec P n s m N = n.
  Proof.
    snrapply ind_N.
  Defined.

  Definition rec_S X P (n : P) (s : P) (m : X -> n = s)
    : rec P n s m S = s.
  Proof.
    snrapply ind_S.
  Defined.

  Arguments rec_N {X}.
  Arguments rec_S {X}.

  Definition rec_M X P (n : P) (s : P) (m : X -> n = s) (x : X)
    : ap (rec P n s m) (M x) @ rec_S P n s m = rec_N P n s m @ m x.
  Proof.
    refine (cancelL (transport_const (M x) _) _ _ _).
    refine (_ @ concat_pp_p _ _ _).
    refine (_ @ whiskerR (concat_A1p _ _) _).
    refine (_ @ concat_p_pp _ _ _).
    refine (concat_p_pp _ _ _ @ _).
    refine (whiskerR (apD_const _ _)^ _ @ _).
    snrapply ind_M.
  Defined.

  (** Suspension universal property. *)
  Definition susp_universalD `{Funext} X (Y : Susp X -> Type) (f : forall x, Y x)
    : {y1 : Y N & {y2 : Y S & forall x, M x # y1 = y2}}.
  Proof.
    refine (f N; (f S; _)); intro x; exact (apD f (M x)).
  Defined.

  Global Instance susp_universalD_isequiv `{Funext} X Y : IsEquiv (susp_universalD X Y).
  Proof.
    snrapply isequiv_adjointify.
    - intros [y1 [y2 r]]; exact (ind Y y1 y2 r).
    - intros [y1 [y2 r]].
      pose proof (Hm := ind_M Y y1 y2 r); revert Hm.
      generalize (ind_N Y y1 y2 r); intro Hn.
      generalize (ind_S Y y1 y2 r); intro Hs.
      revert Hn Hs; generalize (ind Y y1 y2 r); intros f Hn Hs Hm.
      destruct Hn; destruct Hs.
      snrapply path_sigma_uncurried; split with idpath.
      snrapply path_sigma_uncurried; split with idpath.
      apply path_forall; intro x; simpl.
      refine ((concat_p1 _)^ @ Hm x @ concat_1p _).
    - intros f; apply path_forall; snrapply ind; simpl.
      * apply ind_N.
      * apply ind_S.
      * intro x; refine (transport_paths_FlFr_D _ _ @ concat_pp_p _ _ _ @ _).
        apply moveR_Vp; symmetry; srapply ind_M.
  Defined.

  Definition susp_universalD_equiv `{Funext} X (Y : Susp X -> Type)
    : (forall x, Y x) <~> {y1 : Y N & {y2 : Y S & forall x, M x # y1 = y2}}
    := Build_Equiv _ _ _ (susp_universalD_isequiv X Y).

  Definition susp_universal `{Funext} X Y (f : Susp X -> Y)
    : {y1 : Y & {y2 : Y & X -> y1 = y2}}.
  Proof.
    refine (f N; (f S; _)); intro x; exact (ap f (M x)).
  Defined.

  Local Definition susp_universal' `{Funext} X Y
    : (Susp X -> Y) <~> {y1 : Y & {y2 : Y & X -> y1 = y2}}.
  Proof.
    refine (equiv_compose' _ (susp_universalD_equiv _ _)).
    snrapply equiv_functor_sigma_id; intro y1.
    snrapply equiv_functor_sigma_id; intro y2.
    srapply equiv_functor_forall_id; intro x.
    apply equiv_concat_l; apply symmetry; apply transport_const.
  Defined.

  Local Definition susp_universal_hom `{Funext} X Y
    : susp_universal' X Y == susp_universal X Y.
  Proof.
    intro f. srapply path_sigma.
    - exact idpath.
    - srapply path_sigma.
      * exact idpath.
      * srapply path_forall; intro x; cbn.
         apply moveR_Vp; apply apD_const.
  Defined.

  Global Instance susp_universal_isequiv `{Funext} X Y : IsEquiv (susp_universal X Y).
  Proof.
    srapply (isequiv_homotopic _ (susp_universal_hom X Y)).
  Defined.

  Definition susp_universal_equiv `{Funext} X Y
    : (Susp X -> Y) <~> {y1 : Y & {y2 : Y & X -> y1 = y2}}
    := Build_Equiv _ _ _ (susp_universal_isequiv X Y).

  (** Pointed types. *)
  Definition PType : Type := {X : Type & X}.

  Definition FibPType (X : PType) : Type.
  Proof.
    destruct X as [X x]; exact {E : X -> Type & E x}.
  Defined.

  Definition PTypeMorphism (X Y : PType) : Type.
  Proof.
    destruct X as [X x]; destruct Y as [Y y]; exact {f : X -> Y & f x = y}.
  Defined.

  Definition FibPTypeMorphism (X : PType) (Y : FibPType X) : Type.
  Proof.
    destruct X as [X x]; destruct Y as [Y y]; exact {f : forall x, Y x & f x = y}.
  Defined.

  (** Carriers of pointed types. *)
  Definition PType_carrier (X : PType) : Type.
  Proof.
    destruct X as [X _]; exact X.
  Defined.

  Notation "| X |_t" := (PType_carrier X).

  Definition FibPType_carrier {X : PType} (Y : FibPType X) : |X|_t -> Type.
  Proof.
    destruct X as [X x]; destruct Y as [Y _]; exact Y.
  Defined.

  Notation "| X |_ft" := (FibPType_carrier X).

  Definition PTypeMorphism_carrier {X Y : PType} (F : PTypeMorphism X Y) : |X|_t -> |Y|_t.
  Proof.
    destruct X as [X x]; destruct Y as [Y y]; destruct F as [f _]; exact f.
  Defined.

  Notation "| F |_m" := (PTypeMorphism_carrier F).

  Definition FibPTypeMorphism_carrier {X : PType} {Y : FibPType X} (F : FibPTypeMorphism X Y)
    : forall x : |X|_t , |Y|_ft x.
  Proof.
    destruct X as [X x]; destruct Y as [Y y]; destruct F as [f _]; exact f.
  Defined.

  Notation "| F |_fm" := (PTypeMorphism_carrier F).

  (** Loop spaces of pointed types. *)
  Definition Loop (X : PType) : PType.
  Proof.
    destruct X as [X x]; exact (x = x; idpath).
  Defined.

  Definition FibLoop (X : PType) (Y : FibPType X) : FibPType (Loop X).
  Proof.
    destruct X as [X x]; destruct Y as [Y y].
    exact (fun l : x = x => l # y = y; idpath).
  Defined.

  Definition loop (X Y : PType) (F : PTypeMorphism X Y)
    : PTypeMorphism (Loop X) (Loop Y).
  Proof.
    destruct X as [X x]; destruct Y as [Y y]; destruct F as [f p]; destruct p.
    exact (ap f; idpath).
  Defined.

  Definition fibLoop (X : PType) (Y : FibPType X) (F : FibPTypeMorphism X Y)
    : FibPTypeMorphism (Loop X) (FibLoop X Y).
  Proof.
    destruct X as [X x]; destruct Y as [Y y]; destruct F as [f p]; destruct p.
    exact (apD f; idpath).
  Defined.

  Definition NLoop (n : nat) (X : PType) : PType.
  Proof.
    revert X; induction n as [ | n NLoop].
    - exact (fun X => X).
    - exact (fun X => NLoop (Loop X)).
  Defined.

  Definition NFibLoop (n : nat) (X : PType) (Y : FibPType X) : FibPType (NLoop n X).
  Proof.
    revert X Y; induction n as [ | n NFibLoop].
    - exact (fun X Y => Y).
    - exact (fun X Y => NFibLoop (Loop X) (FibLoop X Y)).
  Defined.

  Definition Nloop (n : nat) (X Y : PType) (F : PTypeMorphism X Y)
    : PTypeMorphism (NLoop n X) (NLoop n Y).
  Proof.
    revert X Y F; induction n as [ | n Nloop].
    - exact (fun X Y F => F).
    - exact (fun X Y F => Nloop (Loop X) (Loop Y) (loop X Y F)).
  Defined.

  Definition NfibLoop (n : nat) (X : PType) (Y : FibPType X) (F : FibPTypeMorphism X Y)
    : FibPTypeMorphism (NLoop n X) (NFibLoop n X Y).
  Proof.
    revert X Y F; induction n as [ | n NfibLoop].
    - exact (fun X Y F => F).
    - exact (fun X Y F => NfibLoop (Loop X) (FibLoop X Y) (fibLoop X Y F)).
  Defined.

  (** sphere n+1 := S^n *)
  Local Definition sphere (n : nat) : Type.
  Proof.
    induction n as [ | n X].
    - exact Empty.
    - exact (Susp X).
  Defined.

  (** The two ways to formulate a sphere algebra. *)
  Record sphere_susp_algebra n := {
    ssa_type : Type ;
    ssa_north : ssa_type ;
    ssa_south : ssa_type ;
    ssa_mer : sphere n -> ssa_north = ssa_south ;
  }.

  Record sphere_loop_algebra n := {
    sla_type : Type ;
    sla_base : sla_type ;
    sla_loop : |NLoop n (sla_type; sla_base)|_t ;
  }.

  Arguments ssa_type {n}.
  Arguments ssa_north {n}.
  Arguments ssa_south {n}.
  Arguments ssa_mer {n}.
  Arguments sla_type {n}.
  Arguments sla_base {n}.
  Arguments sla_loop {n}.

  Definition issig_sphere_susp_algebra n
    : _ <~> sphere_susp_algebra n := ltac:(issig).

  Definition issig_sphere_loop_algebra n
    : _ <~> sphere_loop_algebra n := ltac:(issig).

  (** We now show they are equivalent. **)
  Let sphere_loop_equiv `{Funext} n Y (y1 : Y)
    : {y2 : Y & sphere n -> y1 = y2} <~> |NLoop n (Y; y1)|_t.
  Proof.
    revert Y y1; induction n as [ | n F]; intros Y y1.
    { srapply equiv_sigma_contr. }
    transitivity {y2 : _ & {p : _ & {q : y1 = y2 & sphere n -> p = q}}}.
    { apply equiv_functor_sigma_id; intro y2; apply susp_universal_equiv. }
    transitivity {y2 : _ & {p : _ & |NLoop n (y1 = y2; p)|_t}}.
    { apply equiv_functor_sigma_id; intro y2.
      apply equiv_functor_sigma_id; intro p.
      exact (F (y1 = y2) p). }
    refine (equiv_compose' _ (equiv_sigma_assoc' _ _)).
    srapply (@equiv_contr_sigma {y2 : Y & y1 = y2}).
  Defined.

  Definition sphere_susp_loop_algebra_equiv `{Funext} n
    : sphere_susp_algebra n <~> sphere_loop_algebra n.
  Proof.
    refine (equiv_compose' _ (equiv_inverse (issig_sphere_susp_algebra _))).
    refine (equiv_compose' (issig_sphere_loop_algebra _) _).
    snrapply equiv_functor_sigma_id; intro Y; simpl.
    snrapply equiv_functor_sigma_id; intro y1; simpl.
    exact (sphere_loop_equiv n Y y1).
  Defined.

  (** The two ways to formulate a fibered sphere algebra. *)
  Record sphere_fib_susp_algebra n (Y : sphere_susp_algebra n) := {
    sfsa_type_fam : ssa_type Y -> Type ;
    sfsa_north : sfsa_type_fam (ssa_north Y) ;
    sfsa_south : sfsa_type_fam (ssa_south Y) ;
    sfsa_mer : forall (x : sphere n), ssa_mer Y x # sfsa_north = sfsa_south ;
  }.

  Record sphere_fib_loop_algebra n (Y : sphere_loop_algebra n) := {
    sfla_type_fam : sla_type Y -> Type ;
    sfla_base : sfla_type_fam (sla_base Y) ;
    sfla_loop : |NFibLoop n (sla_type Y; sla_base Y) (sfla_type_fam; sfla_base)|_ft (sla_loop Y) ;
  }.

  Arguments sfsa_type_fam {n Y}.
  Arguments sfsa_north {n Y}.
  Arguments sfsa_south {n Y}.
  Arguments sfsa_mer {n Y}.
  Arguments sfla_type_fam {n Y}.
  Arguments sfla_base {n Y}.
  Arguments sfla_loop {n Y}.

  Definition issig_sphere_fib_susp_algebra n Y
    : _ <~> sphere_fib_susp_algebra n Y := ltac:(issig).

  Definition issig_sphere_fib_loop_algebra n Y
    : _ <~> sphere_fib_loop_algebra n Y := ltac:(issig).

  (** We now show they are suitably equivalent. **)
  Let sphere_fib_loop_equiv `{Funext} n Y y1 y2 r (E : Y -> Type) (e1 : E y1)
    : {e2 : E y2 & forall (x : sphere n), r x # e1 = e2} <~>
      |NFibLoop n (Y; y1) (E; e1)|_ft (sphere_loop_equiv n Y y1 (y2; r)).
  Proof.
    revert Y y1 y2 r E e1; induction n as [ | n F]; intros Y y1 y2 r E e1.
    { srapply equiv_sigma_contr. }
    pose (r' := fun x => ap r (M x)).
    pose (E' := fun e2 (p : y1 = y2) => p # e1 = e2).
    pose (l := sphere_loop_equiv n (y1 = y2) (r N) (r S; r')).
    transitivity {e2 : _ & {p : _ & |NFibLoop n (y1 = y2; r N) (E' e2; p)|_ft l}}.
    { apply equiv_functor_sigma_id; intro e2.
      refine (equiv_compose' _ (susp_universalD_equiv _ _)).
      apply equiv_functor_sigma_id; intro p.
      refine (equiv_compose' (F (y1 = y2) (r N) (r S) r' (E' e2) p) _).
      apply equiv_functor_sigma_id; intro q.
      apply equiv_functor_forall_id; intro x.
      apply equiv_concat_l; symmetry.
      srapply transport_compose. }
    refine (equiv_compose' _ (equiv_sigma_assoc' _ _)).
    refine (equiv_compose' _ (@equiv_contr_sigma {e2 : E y2 & r N # e1 = e2} _ _)).
    simpl. unfold Loop, FibLoop, E'; simpl.
    change (sphere_loop_equiv n _ _ _) with l. generalize l. clear l; intro l.
    clear E' r'.
    revert l. revert r. generalize y2. generalizr 
    destruct (r N).

    transitivity {e2 : _ & {p : _ & {q : E' e2 (r S) & forall x, r' x # p = q}}}.
    { apply equiv_functor_sigma_id; intro e2.
      refine (equiv_compose' _ (susp_universalD_equiv _ _)).
      apply equiv_functor_sigma_id; intro p.
      apply equiv_functor_sigma_id; intro q.
      apply equiv_functor_forall_id; intro x.
      apply equiv_concat_l; symmetry.
      srapply transport_compose. }
    transitivity {e2 : _ & {p : _ & |NFibLoop n (y1 = y2; r N) (E' e2; p)|_ft l}}.
    { apply equiv_functor_sigma_id; intro e2.
      apply equiv_functor_sigma_id; intro p.
      exact (F (y1 = y2) (r N) (r S) r' (E' e2) p). }
    unfold l; simpl.
    refine (equiv_compose' _ (equiv_sigma_assoc' _ _)).
    refine (equiv_compose' _ (@equiv_contr_sigma {e2 : E y2 & r N # e1 = e2} _ _)).
    pose (r'' := fun x : sphere n => ap r (M x)). cbn.
    unfold Loop, FibLoop, E'; simpl.
    generalize (existT (fun q => sphere n -> r N = q) (r S) (fun x : sphere n => ap r (M x))).

    generalize (sphere_loop_equiv n (y1 = y2) (r N) (r S; fun x : sphere n => ap r (M x))).


    
    
generalize r'; clear r'. simpl.= 






    { apply equiv_functor_sigma_id; intro y2; apply susp_universal. }
    transitivity {y2 : Y & {p : y1 = y2 & |NLoop n (y1 = y2; p)|_t}}.
    { apply equiv_functor_sigma_id; intro y2.
      apply equiv_functor_sigma_id; intro p.
      exact (F (y1 = y2) p). }
    refine (equiv_compose' _ (equiv_sigma_assoc' _ _)).
    srapply (@equiv_contr_sigma {y2 : Y & y1 = y2}).
  Defined.


  Definition sphere_fib_susp_loop_algebra_equiv `{Funext} n (Y : sphere_susp_algebra n)
    : sphere_fib_susp_algebra n Y <~> sphere_fib_loop_algebra n (sphere_susp_loop_algebra_equiv n Y).
  Proof.
    revert Y.
    srapply (functor_forall_equiv_pb (issig_sphere_susp_algebra _)).
    intros [Y [y1 [y2 r]]].
    refine (equiv_compose' _ (equiv_inverse (issig_sphere_fib_susp_algebra _ _))); simpl.
    refine (equiv_compose' (issig_sphere_fib_loop_algebra _ _) _); simpl.
    snrapply equiv_functor_sigma_id; intro E; simpl.
    snrapply equiv_functor_sigma_id; intro e1; simpl.
    revert Y y1 y2 r E e1; induction n as [ | n F]; intros Y y1 y2 r E e1.
    { srapply equiv_sigma_contr. }

sphere_loop_equiv
    refine (equiv_compose' _ (equiv_functor_sigma_id (fun e2 => equiv_functor_sigma_id (fun p => F
    2:{ intro e2. equiv_compose' _ (equiv_functor_sigma_id _
    


    transitivity {e2 : E y2 & {p : E' e2 (r N) & |NFibLoop n (y1 = y2; r N) (E' e2; p)|_ft _}}.
    transitivity {e2 : E y2 & {p : E' e2 (r N) & {q : E' e2 (r S) & forall x, ap r (M x) # p = q}}}.
    

    transitivity {y2 : Y & {p : y1 = y2 & |NLoop n (y1 = y2; p)|_t}}.
    { apply equiv_functor_sigma_id; intro y2.
      apply equiv_functor_sigma_id; intro p.
      exact (F (y1 = y2) p). }
    refine (equiv_compose' _ (equiv_sigma_assoc' _ _)).
    srapply (@equiv_contr_sigma {y2 : Y & y1 = y2}).
  Defined.


  Definition sphere_fib_fun_space_loop_algebra_ops_equiv `{Funext} n Y y l E
    : (forall x, E (sphere_fun_space_loop_algebra_ops_equiv n Y)^-1 (y; l)) <~>
      {e : Y & |NLoop n (Y; y)|_t}.
  Proof.
    revert Y; induction n as [ | n F]; intro Y.
    all: srapply (equiv_compose' _ (equiv_inverse  (susp_rec_equiv _ _))).
    all: snrapply equiv_functor_sigma_id; intro y1; simpl.
    - srapply equiv_sigma_contr.
    - refine (equiv_compose' _ (equiv_functor_sigma_id _)).
      2: exact (fun y2 => F (y1 = y2)).
      refine (equiv_compose' _ (equiv_sigma_assoc' _ _)).
      srapply (@equiv_contr_sigma {y2 : Y & y1 = y2}).
  Defined.

  Let R `{Funext} n Y : (sphere n.+1 -> Y) <~> {y : Y & |NLoop n (Y; y)|_t}.
  Proof.
    revert Y; induction n as [ | n F]; intro Y.
    all: srapply (equiv_compose' _ (equiv_inverse  (susp_rec_equiv _ _))).
    all: snrapply equiv_functor_sigma_id; intro y1; simpl.
    - srapply equiv_sigma_contr.
    - exact (P n F _ _).
  Defined.

  Definition sphere_susp_loop_algebra_equiv `{Funext} n
    : sphere_susp_algebra n <~> sphere_loop_algebra n.
  Proof.
    refine (equiv_compose' _ (equiv_inverse (issig_sphere_susp_algebra _))).
    refine (equiv_compose' (issig_sphere_loop_algebra _) _).
    snrapply equiv_functor_sigma_id; intro Y; simpl.
    snrapply equiv_functor_sigma_id; intro y1; simpl.
    destruct n as [ | n].
    - srapply equiv_sigma_contr.
    - exact (P n (R n) _ _).
  Defined.




  Definition sphere_fib_susp_loop_algebra_equiv `{Funext} n (Y : sphere_susp_algebra n)
    : sphere_fib_susp_algebra n Y <~> sphere_fib_loop_algebra n (sphere_susp_loop_algebra_equiv n Y).
  Proof.
    revert Y.
    srapply (functor_forall_equiv_pb (equiv_inverse (sphere_susp_loop_algebra_equiv _))).
    srapply (functor_forall_equiv_pb (issig_sphere_loop_algebra _)); intros [Y [y l]].
    refine (equiv_compose' _ (equiv_inverse (issig_sphere_fib_susp_algebra _ _))).
    refine (equiv_compose' (issig_sphere_fib_loop_algebra n _) _).
    snrapply equiv_functor_sigma_id.
    induction n as [ | n F]; intro E.
    all: snrapply equiv_functor_sigma_id; intro e1.
    - srapply equiv_sigma_contr.
    - transitivity {e2 : E y & {p : y1 = y2 & |NLoop n (y1 = y2; p)|_t}}.
      * snrapply equiv_functor_sigma_id; intro y2; simpl.
        refine (equiv_compose' _ (susp_universal _ _)).
        exact (E (y1 = y2)).
      * refine (equiv_compose' _ (equiv_sigma_assoc' _ _)).
        refine (equiv_compose' _ (equiv_contr_sigma _)).
        reflexivity.
  Defined.

  Definition sphere_susp_loop_algebra_equiv `{Funext} n
    : sphere_susp_algebra n <~> sphere_loop_algebra n.
  Proof.
    snrapply equiv_functor_sigma_id; intro y1; simpl.
    srapply sphere_susp_loop_algebra_structure_equiv.
  Defined.

  



