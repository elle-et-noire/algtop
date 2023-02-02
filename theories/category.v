Generalizable All Variables.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Reversible Pattern Implicit.
Set Primitive Projections.
Set Universe Polymorphism.

Require Export setoid.
Require Import ProofIrrelevance.

Declare Scope cat_scope.
Open Scope setoid_scope.
Open Scope cat_scope.

Obligation Tactic := (try now intros x); intros; (try apply \ISE).

Inductive Composables {X Y} {cod dom : Map X Y} :=
  cpair : forall f g, cod f == dom g -> Composables.
Notation "$[ g , f | H ]" := (@cpair _ _ _ _ f g H)
  (at level 0, format "$[  g ,  f  |  H  ]") : cat_scope.

Definition composables_eq {X Y} {cod dom : Map X Y}
  : @Composables _ _ cod dom -> @Composables _ _ cod dom -> Prop.
intros. destruct X0, X1. apply (f == f0 /\ g == g0). Defined.
#[global] Hint Unfold composables_eq : eq.
Program Canonical Structure ComposablesSetoid {X Y} {cod dom : Map X Y} :=
  [ _ | ==: (@composables_eq _ _ cod dom) ].
Next Obligation.
  split; intros [f g H]; try intros [f0 g0 H0];
  try intros [f1 g1 H1]; simpeq_all; intuition;
  now (rewrite H4 || rewrite H5).
Defined.

Definition composables_S {X Y} {cod dom : Map X Y}
  : @Composables _ _ cod dom -> @ComposablesSetoid _ _ cod dom := fun c => c.


Class IsCategory `(comp : @Composables hom obj cod dom -> hom)
  (id : obj -> hom) :=
{
  comp_dom : forall f g H, dom (comp $[g,f|H]) == dom f;
  comp_cod : forall f g H, cod (comp $[g,f|H]) == cod g;
  compcA : forall f g h H H0 H1 H2,
    comp $[ h, comp $[ g, f | H ] | H0 ]
    == comp $[ comp $[ h, g | H1 ], f | H2 ];
  id_dom : forall A, dom (id A) == A;
  id_cod : forall A, cod (id A) == A;
  compc1 : forall f H, comp $[ f, id (dom f) | H ] == f;
  comp1c : forall f H, comp $[ id (cod f), f | H ] == f;
}.

Structure Category := {
  catobj :> Setoid;
  cathom : Setoid;
  dom : Map cathom catobj;
  cod : Map cathom catobj;
  catcomp : Map (@Composables _ _ cod dom) cathom;
  catid : Map catobj cathom;

  catprf :> IsCategory catcomp catid
}.
#[global] Existing Instance catprf.

Arguments dom {_}.
Arguments cod {_}.

Notation "[ 'dom:' dom , 'cod:' cod , 'o:' comp , '1:' id ]"
  := (@Build_Category _ _ dom cod comp id _)
  (at level 0, comp, id at level 99) : cat_scope.
Notation "g o[ 'by' H ] f" := (@catcomp _ $[g,f|H])
  (at level 60, right associativity, format "g  o[ 'by'  H ]  f")
  : cat_scope.
Notation "1_ A" := (@catid _ A)
  (at level 0, A at level 99, no associativity,
  format "1_ A") : cat_scope.

Program Definition homDC {X : Category} (A B : X)
  := [ f | dom f == A /\ cod f == B ].
Next Obligation.
  intros f f0 E; split; intros [H H0]; split; now rewrite2 E.
Defined.
Notation "A ~[ X ]> B" := (@homDC X A B)
  (at level 99, right associativity) : cat_scope.
Notation "A ~> B" := (A ~[_]> B)
  (at level 99, right associativity) : cat_scope.

(* Class IsInverse (C : Category) (A B : C) (f : A ~> B)
   (g : B ~> A) := {
  invcomp1 : g o f == 1_A;
  invcomp2 : f o g == 1_B
}.

Structure Isomorph (C : Category) (A B : C) := {
  orthohom : A ~> B;
  invhom : B ~> A;
  isoprf :> IsInverse orthohom invhom
}.
#[global] Existing Instance isoprf. *)

Lemma compeq {X : Category} {f g : cathom X} H H0 :
  g o[by H] f == g o[by H0] f.
Proof. now apply map_equal. Qed.

Lemma compceq {X : Category} {f g h : cathom X} :
  forall H H0 H1 H2,
  h o[by H0] g o[by H] f == h o[by H2] g o[by H1] f.
Proof. 
  intros. apply map_equal. split; try now simpl. apply compeq.
Qed.

Lemma ccompeq {X : Category} {f g h : cathom X} :
  forall H H0 H1 H2,
  (h o[by H] g) o[by H0] f == (h o[by H1] g) o[by H2] f.
Proof. 
  intros. apply map_equal. split; try now simpl. apply compeq.
Qed.

Program Definition OppCat (X : Category) :=
  [ dom: @cod X, cod: @dom X,
     o: map p => let (f,g,H) := p in f o[by _] g, 1: catid X ].
Next Obligation.
  intros [f g H] [f0 g0 H0] E. apply map_equal. now simpl in *. 
Defined.
Next Obligation.
  split; simpl; intuition.
  - apply comp_cod.
  - apply comp_dom.
  - rewrite ccompeq, compcA. apply map_equal; split;
    try (apply map_equal; split); intuition.
    Unshelve. all:intuition.    
  - apply id_cod.
  - apply id_dom.
  - apply comp1c.
  - apply compc1.
Defined.

Notation "C ^op" := (@OppCat C)
  (at level 40, left associativity, format "C ^op") : cat_scope.

Class IsFunctor (X Y : Category) (fobj : Map X Y)
  (fhom : Map (cathom X) (cathom Y)) :=
{
  comm_dom : forall f, dom (fhom f) == fobj (dom f);
  comm_cod : forall f, cod (fhom f) == fobj (cod f);
  comm_comp : forall f g H H0,
    fhom (g o[by H] f) == (fhom g) o[by H0] fhom f;
  comm_id : forall A, fhom (1_A) == 1_(fobj A)
}.

Structure Functor (X Y : Category) := {
  funobj :> Map X Y;
  funhom : Map (cathom X) (cathom Y);
  funprf :> IsFunctor funobj funhom
}.
#[global] Existing Instance funprf.

Notation "X --> Y" := (@Functor X Y) : cat_scope.
Notation "F ':o' f" := (@funhom _ _ F f)
  (at level 60, right associativity) : cat_scope.
Notation "[ 'obj:' F | 'hom:' Ff ]" :=
  (@Build_Functor _ _ F Ff _)
  (at level 0, F, Ff at level 99, no associativity) : cat_scope.
Notation "[ 'obj' A => FA | 'hom' f => Ff ]" :=
  [ obj: map A => FA | hom: map f => Ff ]
  (at level 0, A, FA, f, Ff at level 99, no associativity)
  : cat_scope.

Program Canonical Structure FunctorSetoid X Y :=
  [ X --> Y | ==: fun F G => forall f, F :o f == G :o f ].
Next Obligation.
  split.
  - now intros F f.
  - intros F G H f. now rewrite H.
  - intros F G H H0 H1 f. now rewrite H0.
Defined.
Notation "X [-->] Y" := (@FunctorSetoid X Y)
  (at level 55) : cat_scope.

Definition eqSetoid X := [ X | ==: eq ].
Notation "[ 'eqS' X ]" := (@eqSetoid X)
  (at level 0, format "[ 'eqS'  X ]") : cat_scope.

Structure Carto {X} (F : X -> X -> Setoid):= {
  cdom : [eqS X];
  ccod : [eqS X];
  cfun :> F cdom ccod
}.

Inductive cfun_eq `{F : X -> X -> Setoid}
  A B (f : F A B) : forall C D, F C D -> Prop :=
  cfun_eqref : forall g : F A B, f == g -> cfun_eq f g.

Program Canonical Structure CartoSetoid
  `(F : X -> X -> Setoid) :=
  [ Carto F | ==: fun F G => @cfun_eq _ _ (cdom F) (ccod F) (cfun F) _ _ G ].
Next Obligation.
  split; try now intros [f]; try now intros [g] [H].
  intros [f] [g] [h] [H0 H1] [H2 H3]. split. simpl in *.
  now rewrite H1, H3.
Defined.

(* Type Category *)

Program Definition funcSetoid X Y :=
  [ X -> Y | ==: fun f g => forall x, f x = g x ].
Next Obligation.
  split; intuition. intros f g h E E0 x. now rewrite E.
Defined.

Definition funcS_comp `(f : funcSetoid X Y) `(g : funcSetoid Z W)
  : Y = Z -> funcSetoid X W.
Proof.
  intros H. revert f g. case H. intros f g.
  refine (fun x => g (f x)).
Defined.

Program Definition TypeCat :=
  [ dom: map F => cdom F, cod: map F => ccod F,
    o: map p => let (f,g,H) := p in Build_Carto (funcS_comp (cfun f) (cfun g) H),
    1: map X => (@Build_Carto _ _ X X (fun x => x)) ].
Next Obligation. now intros [d c f] [d0 c0 f0] [E H]. Defined.
Next Obligation. now intros [d c f] [d0 c0 f0] [E H]. Defined.
Next Obligation.
  intros [[df cf f] [dg cg g] H] [[df0 cf0 f0] [dg0 cg0 g0] H0] [E E0].
  simpl in *. destruct E, E0, H.
  rewrite (proof_irrelevance _ H0 (eq_refl _)).
  split. compute. intros x. now rewrite H2, H1.
Defined.
Next Obligation.
  intros X X0 E. destruct E. split. now simpl.
Defined.
Next Obligation.
  split; try intros [df cf f] [dg cg g] H; try now simpl in *.
  2,3: intros [df cf f] H;
  rewrite (proof_irrelevance _ H (eq_refl _));
  split; now compute.
  destruct H as [dh ch h]. intros H H0 H1 H2. simpl in *.
  destruct H, H0.
  rewrite (proof_irrelevance _ H1 (eq_refl _)).
  rewrite (proof_irrelevance _ H2 (eq_refl _)).
  split. now compute.
Defined.

(* CAT *)

Program Definition Functor_comp `(F : X --> Y)  `(G : Y --> Z)
  := [ obj A => G (F A) | hom f => G :o F :o f ].
Next Obligation. intros A A0 E. now rewrite E. Defined.
Next Obligation. intros f f0 E. now rewrite E. Defined.
Next Obligation.
  split.
  1,2: destruct F as [Fobj Ffun [Fdom Fcod]];
  destruct G as [Gobj Gfun [Gdom Gcod]];
  simpl in *; intros f.
  (* split; simpl in *; intros f. *)
  - now rewrite Gdom, Fdom.
  - now rewrite Gcod, Fcod.
  - intros f g H H0. simpl in *. rewrite !comm_comp, map_equal.
    intuition. eapply _. Unshelve.
  + now rewrite comm_dom, comm_cod, H.
  + apply $[_,_|H0].
  + intuition.
  - intros A. simpl. now rewrite !comm_id.  
Defined.

Definition FunctorC_comp `(f : X [-->] Y) `(g : Z [-->] W)
  : Y = Z -> X [-->] W.
Proof.
  intros H. revert f g. case H. intros f g.
  refine (Functor_comp f g).
Defined.

Program Definition Functor_id (X : Category)
  := [ obj A => A | hom f => f ].
Next Obligation.
  split; try now intros f.
  intros f g H H0. simpl. apply map_equal. now split.
Defined.

Program Canonical Structure CAT :=
  [ dom: map F => cdom F, cod: map F => ccod F,
    o: map p => let (f,g,H) := p in Build_Carto (FunctorC_comp (cfun f) (cfun g) H),
    1: map X => (@Build_Carto _ _ X X (Functor_id X)) ].
Next Obligation.
  intros [dF cF F] [dF0 cF0 F0] [E]. now simpl in *.
Defined.
Next Obligation.
  intros [dF cF F] [dF0 cF0 F0] [E]. now simpl in *.
Defined.
Next Obligation.
  intros [[df cf f] [dg cg g] H] [[df0 cf0 f0] [dg0 cg0 g0] H0] [E E0].
  simpl in *. destruct E, E0, H. split. simpl in *. intros f0.
  rewrite (proof_irrelevance _ H0 eq_refl). simpl.
  now rewrite H1, H2.
Defined.
Next Obligation. intros X Y E. now destruct E. Defined.
Next Obligation.
  split; try intros [df cf f] [dg cg g] H; try now simpl in *.
  2,3: intros [df cf f] H;
  rewrite (proof_irrelevance _ H (eq_refl _));
  split; now compute.
  destruct H as [dh ch h]. intros H H0 H1 H2. simpl in *.
  destruct H, H0.
  rewrite (proof_irrelevance _ H1 (eq_refl _)).
  rewrite (proof_irrelevance _ H2 (eq_refl _)).
  split. now compute.
Defined.
