Generalizable All Variables.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Reversible Pattern Implicit.
Set Primitive Projections.
Set Universe Polymorphism.

Require Export setoid.
(* Require Import ProofIrrelevance. *)
Require Import ChoiceFacts.

Declare Scope cat_scope.
Open Scope setoid_scope.
Open Scope cat_scope.

Obligation Tactic :=
  (try now intros x); (try now split; intros x); intros; (try apply \ISE).

Inductive Composables {obj hom : Setoid} (dom cod : Map hom obj) :=
  ligature : forall f g, cod f == dom g -> Composables _ _.
Notation "$[ g , f | H ]" := (@ligature _ _ _ _ f g H)
  (at level 0, format "$[ g ,  f  |  H ]") : cat_scope.
Notation "{ 'o' dom , cod }" := (@Composables _ _ dom cod)
  (at level 0, dom, cod at level 99,
  format "{ 'o'  dom ,  cod }") : cat_scope.

Definition composables_eq {obj hom : Setoid} {dom cod : Map hom obj}
  (c c0 : Composables dom cod) :=
  let (f, g, H) := c in let (f0, g0, H0) := c0 in f == f0 /\ g == g0.
#[global] Hint Unfold composables_eq : eq.

Program Canonical Structure ComposablesSetoid
  {obj hom : Setoid} (dom cod : Map hom obj) :=
  [ _ | ==: @composables_eq _ _ dom cod ].
Next Obligation.
  split.
  - intros [f g H]. now split.
  - intros [f g H] [f0 g0 H0] [E E0]. now split.
  - intros [f g H] [f0 g0 H0] [f1 g1 H1] [E E0] [E1 E2].
    split; now (rewrite E || rewrite E0).
Defined.
Notation "[ 'o' dom , cod ]" := (@ComposablesSetoid _ _ dom cod)
  (at level 0, dom, cod at level 99,
  format "[ 'o'  dom ,  cod ]") : cat_scope.

Class IsCategory {obj hom : Setoid} (dom cod : Map hom obj)
  (comp : Binop hom) (id : Map obj hom) (actual : {ens hom}) :=
{
  comp_dom : forall f g, dom (comp f g) == dom f;
  comp_cod : forall f g, cod (comp f g) == cod g;
  comp_assoc : forall f g h,
    comp (comp f g) h == comp f (comp g h);
  comp_actual : forall f g,
    actual (comp f g) == (actual f /\ actual g /\ cod f == dom g);
  id_dom : forall A, dom (id A) == A;
  id_cod : forall A, cod (id A) == A;
  comp_idr : forall f, comp (id (dom f)) f == f;
  comp_idl : forall f, comp f (id (cod f)) == f;
  id_actual : forall A, actual (id A)
}.

Structure Category := {
  catobj :> Setoid;
  cathom : Setoid;
  catdom : Map cathom catobj;
  catcod : Map cathom catobj;
  homcomp : Binop cathom;
  catid : Map catobj cathom;
  actual : {ens cathom};

  catprf :> IsCategory catdom catcod homcomp catid actual
}.
#[global] Existing Instance catprf.

Notation "[ 'dom:' dom , 'cod:' cod , 'o:' comp , '1:' id ]"
  := (@Build_Category _ _ dom cod comp id _)
  (at level 0, dom, cod, comp, id at level 99) : cat_scope.
Notation "[ 'dom' F => A , 'cod' G => B , 'comp' C => P , 'id' D => Q ]"
  := [ dom: map F => A, cod: map G => B, o: map C => P, 1: map D => Q ]
  (at level 0, F binder, G binder, C binder, D binder,
  A, B, P, Q at level 99) : cat_scope.
Notation "'dom' f" := (@catdom _ f)
  (at level 60, right associativity) : cat_scope.
Notation "'cod' f" := (@catcod _ f)
  (at level 60, right associativity) : cat_scope.
Notation "g o[ 'by' H ] f" := (@homcomp _ $[g, f | H])
  (at level 60, H at level 99, right associativity,
  format "g  o[ 'by'  H ]  f") : cat_scope.
Notation "g o[] f" := (g o[by _] f)
  (at level 60, right associativity, format "g  o[]  f") : cat_scope.
Notation "1_ A" := (@catid _ A)
  (at level 0, right associativity, format "1_ A") : cat_scope.

Section uouo.
Variables obj hom : Setoid.
Variables Dom Cod : Map hom obj.
Check [o Dom, Cod].
Variables X : Category.
Variables f g : cathom X.
Variables H : cod f == dom g.
Check (g o[by H] f).
End uouo.

Program Definition homDC {X : Category} :=
  dmap A B => [ f | dom f == A /\ cod f == B ].
Next Obligation.
  intros f f0 E. split; intros [E0 E1]; split; now rewrite2 E.
Defined.
Next Obligation.
  intros A A0 E B B0 E0 f f0 E1. split; intros [H H0]; split;
  rewrite2 E1; try (now rewrite H); now rewrite H0.
Defined.
Notation "A ~> B" := (@homDC _ A B)
  (at level 90, no associativity) : cat_scope.

Program Definition homDC_comp {X : Category} {A B C : X}
  : Dymap (A ~> B) (B ~> C) (A ~> C)
  := dmap f g => $[g o[by _] f, _].
Next Obligation.
  destruct f as [f [H H0]]. destruct g as [g [H1 H2]].
  simpl. now rewrite H0.
Defined.
Next Obligation.
  destruct f as [f [H H0]]. destruct g as [g [H1 H2]].
  split; simpl in *; now (rewrite comp_dom || rewrite comp_cod).
Defined.
Next Obligation.
  intros f f0 E g g0 E0. simpeq_all. apply map_equal. split; now simpl.
Defined.
Notation "g 'o' f" := (@homDC_comp _ _ _ _ f g)
  (at level 60, right associativity) : cat_scope.

Program Definition idDC {X : Category} (A : X) : A ~> A
  := $[1_A, _].
Next Obligation. split; now (rewrite id_dom || rewrite id_cod). Defined.
Notation "1_[ A ]" := (@idDC _ A)
  (at level 0, format "1_[ A ]") : cat_scope.

Program Definition hom_homDC `(f : cathom X) : dom f ~> cod f
  := $[f, _].

Section CatTheory.
  Context {X : Category}.
  Implicit Types (A B C D : X) (f g : cathom X).

  Lemma compeq f g H H0 : g o[by H] f == g o[by H0] f.
  Proof. apply map_equal. now split. Qed.

  Lemma comp1fH f H : 1_(cod f) o[by H] f == f.
  Proof. apply comp_idl. Qed.

  Lemma comp1F A B (F : A ~> B) : 1_[B] o F == F.
  Proof.
    case F as [f [H H0]]. simpeq.
    assert (cod f == dom 1_(cod f)) by now rewrite id_dom.
    rewrite <-(comp_idl H1) at 3. apply map_equal.
    split; intuition. now apply map_equal.
  Qed.

  Lemma compF1 A B (F : A ~> B) : F o 1_[A] == F.
  Proof.
    case F as [f [H H0]]. simpeq.
    assert (cod 1_(dom f) == dom f) by now rewrite id_cod.
    rewrite <-(comp_idr H1) at 6. apply map_equal.
    split; intuition. now apply map_equal.
  Qed.

  Lemma compA A B C D (F : A ~> B) (G : B ~> C) (H : C ~> D)
    : H o G o F == (H o G) o F.
  Proof. apply comp_assoc. Qed.
End CatTheory.

Class IsIsopair {X : Category} {A B : X} (f : A ~> B) (g : B ~> A) := {
  isodom : g o f == 1_[A];
  isocod : f o g == 1_[B]
}.

Definition IsIsomorphic (X : Category) (A B : X) :=
  exists (f : A ~> B) (g : B ~> A), IsIsopair f g.

Program Definition IsomorphSetoid (X : Category) :=
  [ X | ==: @IsIsomorphic X ].
Next Obligation.
  split; intros A.
  - exists 1_[A], 1_[A]. split; now rewrite comp1F.
  - intros B [f [g [H H0]]]. exists g, f. now split.
  - intros B C [f [g [H H0]]] [f0 [g0 [H1 H2]]].
    exists (f0 o f), (g o g0). split.
  + now rewrite <-compA, (compA f), H1, comp1F.
  + now rewrite <-compA, (compA g0), H0, comp1F.
Defined.
Notation "A === B" := (A == B in @IsomorphSetoid _)
  (at level 70, no associativity) : cat_scope.

Program Definition OppCat (X : Category) :=
  [ dom: catcod X, cod: catdom X,
    o: map c => let (f, g, H) := c in f o[by _] g,
    1: catid X ].
Next Obligation.
  intros [f g H] [f0 g0 H0] [E E0]. apply map_equal. now split.
Defined.
Next Obligation.
  split; intuition; simpl.
  - apply comp_cod.
  - apply comp_dom.
  - symmetry. apply comp_assoc.
  - apply id_cod.
  - apply id_dom.
  - apply comp_idl.
  - apply comp_idr.
Defined.
Notation "C ^op" := (@OppCat C)
  (at level 40, left associativity, format "C ^op") : cat_scope.

Class IsFunctor (X Y : Category) (fobj : X -> Y)
  (fhom : Map (cathom X) (cathom Y)) :=
{
  compF_dom : forall f, dom (fhom f) == fobj (dom f);
  compF_cod : forall f, cod (fhom f) == fobj (cod f);
  compF_morph : forall f g H H0,
    fhom (g o[by H] f) == (fhom g) o[by H0] (fhom f);
  idF_morph : forall A, fhom 1_A == 1_(fobj A)
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
Notation "[ 'obj:' F , 'hom:' Ff ]" :=
  (@Build_Functor _ _ F Ff _)
  (at level 0, F, Ff at level 99, no associativity) : cat_scope.
Notation "[ 'obj' A => FA , 'hom' f => Ff ]" :=
  [ obj: map A => FA , hom: map f => Ff ]
  (at level 0, A binder, f binder,
  FA, Ff at level 99, no associativity)
  : cat_scope.

Program Canonical Structure FunctorSetoid X Y :=
  [ ==: (F : X --> Y) G => forall f, F :o f == G :o f ].
Next Obligation.
  split; try now intros F.
  intros F G H H0 H1 f. now rewrite H0, H1.
Defined.
Notation "X [-->] Y" := (@FunctorSetoid X Y)
  (at level 55) : cat_scope.

Program Definition funhomDC `(F : X --> Y) (A B : X)
  : Map (A ~> B) (F A ~> F B) := map f => $[F :o f, _].
Next Obligation.
  destruct F as [Fo Ff H]. destruct f as [f [H0 H1]].
  split; simpl; [rewrite compF_dom | rewrite compF_cod];
  now apply map_equal.
Defined.
Next Obligation.
  intros f f0 E. simpeq_all. now apply map_equal.
Defined.
Notation "F :[o] f" := (@funhomDC _ _ F _ _ f)
  (at level 60, right associativity) : cat_scope.

Section FunctorTheory.
  Context {X Y : Category} {F : X --> Y}.
  Implicit Types (A B C : X).

  Lemma compFM A B C (f : A ~> B) (g : B ~> C) :
    F :[o] (g o f) == (F :[o] g) o F :[o] f.
  Proof. apply compF_morph. Qed.

  Lemma idFM A : F :[o] 1_[A] == 1_[F A].
  Proof. apply idF_morph. Qed.
End FunctorTheory.

Definition eqSetoid X := [ X | ==: @eq X ].
Notation "[ 'eqS' X ]" := (@eqSetoid X)
  (at level 0, format "[ 'eqS'  X ]") : cat_scope.

Structure Carto {X} (F : X -> X -> Setoid) := {
  cdom : [eqS X];
  ccod : [eqS X];
  cfun :> F cdom ccod
}.

Inductive cfun_eq `{F : X -> X -> Setoid}
  A B (f : F A B) : forall C D, F C D -> Prop :=
  cfun_eqref : forall g : F A B, f == g -> cfun_eq f g.

Program Canonical Structure CartoSetoid `(F : X -> X -> Setoid) :=
  [ ==: (f : Carto F) G => @cfun_eq _ _ (cdom f) (ccod f) (cfun f) _ _ G ].
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

Program Definition Functor_comp {X Y Z : Category}
  : Dymap (X --> Y) (Y --> Z) (X --> Z) := dmap F G =>
  [ obj (A : X) => G (F A), hom (f : cathom X) => G :o F :o f ].
Next Obligation. intros A A0 E. now rewrite E. Defined.
Next Obligation. intros f f0 E. now rewrite E. Defined.
Next Obligation.
  split; simpl in *; intros f.
  - now rewrite !compF_dom.
  - now rewrite !compF_cod.
  - intros g H H0. now rewrite !compF_morph.
  - now rewrite !idF_morph. Unshelve.
    now rewrite compF_cod, compF_dom, H.  
Defined.
Next Obligation.
  intros F F0 E G G0 E0 f. simpl in *. now rewrite E0, E.
Defined.

Definition FunctorC_comp `(f : X [-->] Y) `(g : Z [-->] W)
  : Y = Z -> X [-->] W.
Proof.
  intros H. revert f g. case H. intros f g.
  refine (Functor_comp f g).
Defined.

Program Definition Functor_id (X : Category)
  := [ obj A => A, hom f => f ].
Next Obligation.
  split; intros f; simpl; intuition. now apply map_equal.
Defined.

Program Canonical Structure CAT :=
  [ dom F => cdom F, cod F => ccod F,
    comp p => let (f,g,H) := p in Build_Carto (FunctorC_comp (cfun f) (cfun g) H),
    id X => (@Build_Carto _ _ X X (Functor_id X)) ].
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

Class IsFaithful `(F : X --> Y) := {
  faith : forall A B (f g : A ~> B), F :o f == F :o g -> f == g
}.

Class IsFull `(F : X --> Y) := {
  full : forall A B (f : F A ~> F B),
    exists (g : A ~> B), F :o g == f
}.

Class IsNattrans {X Y} (F G : X --> Y) (c : Map X (cathom Y)) := {
  nat_dom : forall A, dom (c A) == F A;
  nat_cod : forall A, cod (c A) == G A;
  natural : forall f H H0,
    (c (cod f)) o[by H] (F :o f) == (G :o f) o[by H0] (c (dom f))
}.

Structure Nattrans {X Y} (F G : X --> Y) := {
  component :> Map X (cathom Y);
  ntprf :> IsNattrans F G component
}.
#[global] Existing Instance ntprf.

Notation "F ==> G" := (@Nattrans _ _ F G) : cat_scope.
Notation "[ ==>: C ]" := (@Build_Nattrans _ _ _ _ C _)
  (at level 0, C at level 99) : cat_scope.
Notation "[ 'nt' A => P ]" := [ ==>: fun A => P ]
  (at level 0, A binder, P at level 99) : cat_scope.

Lemma ntcomm X Y (F G : X --> Y) (a : F ==> G) A B (f : A ~> B)
  : (a B) o (F :[o] f) == (G :[o] f) o (a A).
Proof. apply ntprf. Qed.

Definition nt_eq {X Y} (F G : X --> Y) (a b : F ==> G) :=
  forall A, a A == b A.
#[global] Hint Unfold nt_eq : eq.
Program Canonical Structure NattransSetoid {X Y}
  (F G : X --> Y) := [ _ | ==: @nt_eq _ _ F G ].
Next Obligation.
  split; try now intros a. intros a b c H H0 A.
  simpeq_all. now rewrite H, H0.
Defined.
Notation "F [==>] G" := (@NattransSetoid _ _ F G)
  (at level 55, right associativity) : cat_scope.

Program Definition Nattrans_vcomp {X Y} {F G H : X --> Y}
  : Dymap (F ==> G) (G ==> H) (F ==> H) := dmap a b =>
  [ nt A => (b A) o (a A) ].
Next Obligation.
  split; intros. now rewrite <-compA, ntcomm, compA, ntcomm, compA.
Defined.
Next Obligation.
  intros a a0 E b b0 E0 A. simpeq_all.
  apply map_equal. split; simpl; now (rewrite E || rewrite E0).
Defined.
Notation "b |o| a" := (@Nattrans_vcomp _ _ _ _ _ a b)
  (at level 53, right associativity) : cat_scope.

Definition NatrransC_vcomp {X Y} {F F0 F1 F2 : X --> Y}
  (a : F ==> F0) (b : F1 ==> F2) : F0 == F1 -> F0 ==> F2.
Proof.
  intros H. rewrite H.

`(f : X [-->] Y) `(g : Z [-->] W)
  : Y = Z -> X [-->] W.
Proof.
  intros H. revert f g. case H. intros f g.
  refine (Functor_comp f g).
Defined.

Program Definition Functor_id (X : Category)
  := [ obj A => A, hom f => f ].
Next Obligation.
  split; intros f; simpl; intuition. now apply map_equal.
Defined.

Program Canonical Structure FunctorCat (X Y : Category) :=
  [ dom F => cdom F, cod F => ccod F,
    comp p => let (f, g, H) := p in Build_Carto (cfun f |o| cfun g),
    id X => (@Build_Carto _ _ X ) ]
[ dom F => cdom F, cod F => ccod F,
comp p => let (f,g,H) := p in Build_Carto (FunctorC_comp (cfun f) (cfun g) H),
id X => (@Build_Carto _ _ X X (Functor_id X)) ].
  [ dom  ]
  [ hom (F : X --> Y) G => Nattrans F G, comp F G H a b => b |o| a,
    id F => [ nt A => 1_(F A) ] ].
Next Obligation. apply Nattrans_vcomp_obligation_2. Defined.
Next Obligation. split; intros. now rewrite compf1, comp1f. Defined.
Next Obligation.
  split; intros; simpeq; intros.
  - now rewrite compA.
  - now rewrite compf1.
  - now rewrite comp1f.
Defined.
Notation "[ X , Y ]" := (@FunctorCat X Y)
  (at level 0, X, Y at level 99) : cat_scope.

Lemma natiso_cmpiso X Y (F G : X --> Y) (a : F ==> G) :
  DependentFunctionalChoice ->
  IsIsomorphism a == forall A, IsIsomorphism (a A).
Proof.
  intros DFC. unfold IsIsomorphism. split; simpeq_all.
  - intros [g [E E0]] A. exists (g A). split;
    (apply E || apply E0).
  - intros H.
    pose (DFC X (fun A => G A ~> F A) (fun A g => g o a A == 1_(F A) /\ a A o g == 1_(G A))).
    simpl in *. destruct (e H) as [g H0].
    assert (IsNattrans g).
    { split. intros. now rewrite <-(compf1 (G :o f)),
      <-(proj2 (H0 A)), (compA (g A)), <-natural, !compA,
      (proj1 (H0 B)), comp1f. }
    exists (Build_Nattrans H1). split; intros A; simpl in *;
    apply (proj1 (H0 A)) || apply (proj2 (H0 A)).
Qed.

Class IsEquivCat `(F : X --> Y) (G : Y --> X) (eta : 1_X ==> G :o: F)
  (xi : F :o: G ==> 1_Y) :=
{
  ecetaiso : IsIsomorphism eta;
  ecxiiso : IsIsomorphism xi
}.

Structure EquivCat (X Y : Category) := {
  ecfwd : X --> Y;
  ecrev : Y --> X;
  eceta : 1_X ==> ecrev :o: ecfwd;
  ecxi : ecfwd :o: ecrev ==> 1_Y;
  ecprf :> IsEquivCat eceta ecxi
}.
#[global] Existing Instance ecprf.

Program Definition Nattrans_hcomp {X Y Z} {F G : X --> Y} {F0 G0 : Y --> Z}
  : Dymap (F ==> G) (F0 ==> G0) (F0 :o: F ==> G0 :o: G) := dmap a b =>
  [ nt A => b (G A) o (F0 :o a A) ].
Next Obligation.
  split. intros A B f. simpl. rewrite !ntcomm.
  rewrite <-!compA. rewrite !ntcomm. rewrite compA.
  now rewrite <-compFC, !ntcomm, compFC, compA.
Defined.
Next Obligation.
  intros a a0 E b b0 E0 A. simpeq_all. now rewrite E, E0.
Defined.
Notation "b =o= a" := (@Nattrans_hcomp _ _ _ _ _ _ _ a b)
  (at level 53, right associativity) : cat_scope.

Program Definition nt1_1o1 {X : Category} : 1_X ==> 1_X :o: 1_X :=
  [ nt A => 1_A ].
Next Obligation.
  split. intros A B f. simpl. now rewrite comp1f, compf1.
Defined.

Program Definition nt1o1_1 {X : Category} : 1_X :o: 1_X ==> 1_X :=
  [ nt A => 1_A ].
Next Obligation.
  split. intros A B f. simpl. now rewrite comp1f, compf1.
Defined.

(* Program Definition nt_refconv {X Y} {F F0 G G0 : X --> Y}
  (E : F == F0) (E0 : G == G0) (a : F ==> G) : F0 ==> G :=
  [ nt A => a A ]. *)

(* Program Definition nt_reflconv0 {X Y X} {F : X --> Y} {G : Y --> X}
  {F0 : Y --> Z} {G0 : Z --> Y}
  (eta0 : 1_Y ==> G0 :o: F0) *)

Program Definition nt_revlconv {X Y} {F F0 : X --> Y} (H : F == F0)
  : F ==> F0.
rewrite H.

Program Definition EquivCatSetoid :=
  [ ==: (X : Category) Y => exists (F : X --> Y) (G : Y --> X)
    (eta : 1_X ==> G :o: F) (xi : F :o: G ==> 1_Y),
    IsEquivCat eta xi ].
Next Obligation.
  split.
  - intros X. exists 1_X, 1_X, nt1_1o1, nt1o1_1.
    split; unfold IsIsomorphism; [exists nt1o1_1 | exists nt1_1o1];
    split; simpeq; intros A; now rewrite comp1f.
  - intros X Y [F [G [eta [xi [[g [H H0]] [g0 [H1 H2]]]]]]].
    exists G, F, g0, g. split; [exists xi | exists eta]; split; intuition.
  - intros X Y Z [F [G [eta [xi H]]]] [F0 [G0 [eta0 [xi0 H0]]]].
    exists (F0 :o: F), (G :o: G0).
    pose (1_G =o= eta0 =o= 1_F). pose (s o eta). exists s. simpl in s. pose (eta0 o eta).