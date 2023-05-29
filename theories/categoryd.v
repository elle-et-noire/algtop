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

#[export]
Obligation Tactic :=
  (try now intros x); (try now split; intros x); intros.

Inductive Composables {obj hom : Setoid} (dom cod : Map hom obj) :=
  ligature : forall f g, cod f == dom g -> Composables _ _.
Notation "$[ g , f | H ]" := (@ligature _ _ _ _ f g H)
  (at level 0, format "$[ g ,  f  |  H ]") : cat_scope.
Notation "{ 'o' dom , cod }" := (@Composables _ _ dom cod)
  (at level 0, dom, cod at level 99,
  format "{ 'o'  dom ,  cod }") : cat_scope.

Program Canonical Structure ComposablesSetoid
  {obj hom : Setoid} (dom cod : Map hom obj) :=
  [ ==: (c : Composables dom cod) c0 => let (f, g, H) := c
    in let (f0, g0, H0) := c0 in f == f0 /\ g == g0].
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

Class IsCategory {obj hom : Setoid} {dom cod : Map hom obj}
  (comp : Map [o dom, cod] hom) (id : obj -> hom) :=
{
  comp_dom : forall f g H, dom (comp $[g, f | H]) == dom f;
  comp_cod : forall f g H, cod (comp $[g, f | H]) == cod g;
  comp_assoc : forall f g h H H0 H1 H2,
    comp $[h, comp $[g, f | H] | H0] ==
    comp $[comp $[h, g | H1], f | H2];
  id_dom : forall A, dom (id A) == A;
  id_cod : forall A, cod (id A) == A;
  comp_idr : forall f A H, comp $[f, id A | H] == f;
  comp_idl : forall f A H, comp $[id A, f | H] == f;
}.

Structure Category := {
  catobj :> Setoid;
  cathom : Setoid;
  catdom : Map cathom catobj;
  catcod : Map cathom catobj;
  homcomp : Map [o catdom, catcod] cathom;
  catid : Map catobj cathom;

  catprf :> IsCategory homcomp catid
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
Notation "1_ A" := (@catid _ A)
  (at level 0, right associativity, format "1_ A") : cat_scope.

Definition IsIsopair {X : Category} (f g : cathom X) H H0 :=
  g o[by H] f == 1_(dom f) /\ f o[by H0] g == 1_(dom g).

Definition IsIsomorphism {X : Category} (f : cathom X) :=
  exists g H H0, @IsIsopair X f g H H0.

Definition IsIsomorphic (X : Category) (A B : X) :=
  exists (f : cathom X), IsIsomorphism f /\ dom f == A /\ cod f == B.

Program Definition IsomorphSetoid (X : Category) :=
  [ X | ==: @IsIsomorphic X ].
Next Obligation.
  split; intros A.
  - exists 1_A. split; try split.
  + exists 1_A. assert (cod 1_A == dom 1_A).
    { now rewrite id_cod, id_dom. } exists H, H.
    split; now rewrite comp_idr, id_dom.
  + apply id_dom.
  + apply id_cod.
  - intros B [f [[g [H [H0 [H1]]]] [df cf]]].
    exists g. split; try split.
  + exists f, H0, H. now split.
  + now rewrite <-H.
  + now rewrite H0.
  - intros B C [f [[g [H [H0 [H1]]]] [df cf]]] [f0 [[g0 [H3 [H4 [H5]]]] [df0 cf0]]].
    assert (cod f == dom f0) by now rewrite df0.
    exists (f0 o[by H7] f). split; try split.
  + assert (cod g0 == dom g) by now rewrite H4, df0, <-H.
    exists (g o[by H8] g0).
    assert (cod f0 o[by H7] f == dom g o[by H8] g0).
    { now rewrite comp_cod, comp_dom. }
    assert (cod g o[by H8] g0 == dom f0 o[by H7] f).
    { now rewrite comp_cod, comp_dom. }
    exists H9, H10. split.
  * assert (forall H00 H01 H02 H03 H04, (g o[by H00] g0) o[by H02] f0 o[by H01] f
    == g o[by H04] 1_(dom f0) o[by H03] f).
    { intros. rewrite <-comp_assoc. apply map_equal. split.
      rewrite comp_assoc. apply map_equal. split. reflexivity.
      rewrite <-H5. now apply map_equal. reflexivity. }
    rewrite H11.
    assert (forall H00 H01 H02, g o[by H01] 1_(dom f0) o[by H00] f == g o[by H02] f).
    { intros. apply map_equal. split. now rewrite comp_idl. reflexivity. }
    rewrite H12, comp_dom, <-H1. now apply map_equal.
  * rewrite comp_dom, <-H6, comp_assoc. apply map_equal. split.
    reflexivity. rewrite <-comp_assoc.
    assert (forall H00, f0 o[by H00] 1_(dom f0) == f0).
    { intros. apply comp_idr. }
    rewrite <-H11 at 2. apply map_equal. split.
    rewrite <-H7, H, <-H2. apply map_equal. now split.
    reflexivity.
  + now rewrite comp_dom.
  + now rewrite comp_cod.
  Unshelve.
  * now rewrite comp_cod.
  * now rewrite comp_cod.
  * now rewrite comp_dom.
  * now rewrite id_dom.
  * now rewrite comp_cod, id_cod, <-H7.
  * now rewrite comp_dom, H0.
  * now rewrite comp_dom.
  * now idtac.
  * now rewrite comp_cod.
  * now rewrite id_cod.
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

Class IsFunctor (X Y : Category)
  (fhom : Map (cathom X) (cathom Y)) :=
{
  compatF_dom : forall f g, dom f == dom g -> dom (fhom f) == dom (fhom g);
  compatF_cod : forall f g, cod f == cod g -> cod (fhom f) == cod (fhom g);
  compF_morph : forall f g H H0,
    fhom (g o[by H] f) == (fhom g) o[by H0] (fhom f);
  idF_morph0 : forall A, fhom 1_A == 1_(dom fhom 1_A)
}.

Structure Functor (X Y : Category) := {
  funhom : Map (cathom X) (cathom Y);
  funprf :> IsFunctor funhom
}.
#[global] Existing Instance funprf.

Notation "X --> Y" := (@Functor X Y) : cat_scope.
Notation "F ':o' f" := (@funhom _ _ F f)
  (at level 60, right associativity) : cat_scope.
Notation "[ 'hom:' Ff ]" :=
  (@Build_Functor _ _ Ff _)
  (at level 0, Ff at level 99, no associativity) : cat_scope.

Program Coercion funobj `(F : X --> Y) : Map X Y
  := map (A : X) => dom (F :o 1_A).
Next Obligation.
  intros A A0 E. now rewrite E.
Defined.

Program Canonical Structure FunctorSetoid X Y :=
  [ ==: (F : X --> Y) G => funhom F == funhom G ].
Next Obligation.
  split; try now intros F. intros F G H H0 H1 f g E.
  rewrite (H0 f g); [now apply H1 | apply E].
Defined.
Notation "X [-->] Y" := (@FunctorSetoid X Y)
  (at level 55) : cat_scope.

Lemma compF_dom `(F : X --> Y) (f : cathom X) : 
  F (dom f) == dom (F :o f).
Proof.
  simpl. rewrite compatF_dom. reflexivity. apply id_dom.
Qed.

Lemma compF_cod `(F : X --> Y) (f : cathom X) :
  F (cod f) == cod (F :o f).
Proof.
  simpl. rewrite <-id_cod, <-idF_morph0, compatF_cod.
  reflexivity. apply id_cod.
Qed.

Lemma idF_morph `(F : X --> Y) (A : X) : F :o 1_A == 1_(F A).
Proof. apply idF_morph0. Qed.

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
  2,3: intros [df cf f] H; compute; intros H0; now destruct H0.
  destruct H as [dh ch h]. intros H H0 H1 H2. simpl in *.
  destruct H, H0.
  rewrite (proof_irrelevance _ H1 (eq_refl _)).
  rewrite (proof_irrelevance _ H2 (eq_refl _)).
  split. now compute.
Defined.

(* CAT *)

Program Definition Functor_comp {X Y Z : Category}
  : Dymap (X --> Y) (Y --> Z) (X --> Z) := dmap F G =>
  [ hom: map (f : cathom X) => G :o F :o f ].
Next Obligation. intros A A0 E. now rewrite E. Defined.
Next Obligation.
  split; simpl in *.
  - intros f g E. rewrite compatF_dom. reflexivity. now rewrite compatF_dom.
  - intros f g E. rewrite compatF_cod. reflexivity. now rewrite compatF_cod.
  - intros f g H H0. rewrite !compF_morph. apply map_equal. now split.
  - intros A. now rewrite 2!idF_morph, id_dom.
  Unshelve.
  + now rewrite <-compF_cod, <-compF_dom, H.
  + apply H0.
Defined.
Next Obligation.
  intros F F0 E G G0 E0 f g E1. simpl in *. apply E0, E, E1.
Defined.
Notation "G :o: F" := (@Functor_comp _ _ _ F G)
  (at level 60, right associativity) : cat_scope.

Definition FunctorC_comp `(f : X [-->] Y) `(g : Z [-->] W)
  : Y = Z -> X [-->] W.
Proof.
  intros H. revert f g. case H. intros f g.
  refine (Functor_comp f g).
Defined.

Program Definition Functor_id (X : Category) : X --> X
  := [ hom: map f => f ].
Next Obligation.
  split; intros f; simpl; try now idtac.
  intros. now apply map_equal. now rewrite id_dom.
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
  simpl in *. destruct E, E0, H. split. simpl in *. intros f0 f1 E.
  rewrite (proof_irrelevance _ H0 eq_refl). simpl. apply H2, H1, E.
Defined.
Next Obligation. intros X Y E. now destruct E. Defined.
Next Obligation.
  split; try intros [df cf f] [dg cg g] H; try now simpl in *.
  - destruct H as [dh ch h]. intros H H0 H1 H2. simpl in *.
    destruct H, H0.
    rewrite (proof_irrelevance _ H1 (eq_refl _)).
    rewrite (proof_irrelevance _ H2 (eq_refl _)).
    split. compute. intros f0 g0 E. now rewrite E.
  - simpl in *. rewrite H. 
    assert (FunctorC_comp (Functor_id df) f eq_refl == f).
    { intros f0 g0 E. now rewrite E. } apply (cfun_eqref H0).
  - simpl in *. rewrite <-H.
    assert (FunctorC_comp f (Functor_id cf) eq_refl == f).
    { intros f0 g0 E. now rewrite E. } apply (cfun_eqref H0).
Defined.

Class IsFaithful `(F : X --> Y) := {
  faith : forall f g, dom f == dom g /\ cod f == cod g ->
    F :o f == F :o g -> f == g
}.

Class IsFull `(F : X --> Y) := {
  full : forall f, (exists A B, dom f == F A /\ cod f == F B) ->
    exists g, F :o g == f
}.

Class IsNattrans {X Y} (F G : X [-->] Y) (c : Map X (cathom Y)) := {
  nat_dom : forall A, dom (c A) == F A;
  nat_cod : forall A, cod (c A) == G A;
  natural : forall f H H0,
    (c (cod f)) o[by H] (F :o f) == (G :o f) o[by H0] (c (dom f))
}.

Structure Nattrans (X Y : Category) := {
  ntdom : X [-->] Y;
  ntcod : X [-->] Y;
  component :> Map X (cathom Y);
  ntprf :> IsNattrans ntdom ntcod component
}.
#[global] Existing Instance ntprf.

(* Notation "F ==> G" := (@Nattrans _ _ F G) : cat_scope.
Notation "[ ==>: C ]" := (@Build_Nattrans _ _ _ _ C _)
  (at level 0, C at level 99) : cat_scope. *)
Notation "[ 'ntdom:' F , 'ntcod:' G , 'nt' A => P ]" :=
  (@Build_Nattrans _ _ F G (map A => P) _)
  (at level 0, A binder, P at level 99) : cat_scope.

Program Canonical Structure NattransSetoid (X Y : Category)
  := [ ==: (a : Nattrans X Y) b =>
   ntdom a == ntdom b /\ ntcod a == ntcod b /\ component a == component b ].
Next Obligation.
  split; try now intros a.
  intros a b c [E [E0 E1]] [E2 [E3 E4]]. split; try split.
  - now rewrite E, E2.
  - now rewrite E0, E3.
  - now rewrite E1, E4.
Defined.
(* Notation "F [==>] G" := (@NattransSetoid _ _ F G)
  (at level 55, right associativity) : cat_scope. *)

Lemma Functoreq_obj {X Y} (F G : X [-->] Y) : F == G -> forall A, F A == G A.
Proof.
  intros E A. assert (1_A == 1_A) by reflexivity.
  pose (E 1_A 1_A H) as H0.
  assert (dom F :o 1_A == dom G :o 1_A) by now rewrite H0.
  now rewrite <-!compF_dom, id_dom in H1.
Qed.

Program Canonical Structure ntdomMap {X Y : Category}
  : Map (NattransSetoid X Y) (X [-->] Y)
  := map a => ntdom a.
Next Obligation. now intros [a] [b] [E [E0 E1]]. Defined.

Program Canonical Structure ntcodMap {X Y : Category}
  : Map (NattransSetoid X Y) (X [-->] Y)
  := map a => ntcod a.
Next Obligation. now intros [a] [b] [E [E0 E1]]. Defined.

Lemma ntdom_ref {X Y : Category} (a : Nattrans X Y) : ntdomMap a == ntdom a.
Proof. reflexivity. Qed.

Lemma ntcod_ref {X Y : Category} (a : Nattrans X Y) : ntcodMap a == ntcod a.
Proof. reflexivity. Qed.


Program Definition Nattrans_vcomp {X Y : Category}
  : Map (Composables (@ntdomMap X Y) (@ntcodMap X Y)) (Nattrans X Y) :=
  map c => let (a,b,H) := c in 
  [ ntdom: (ntdom a), ntcod: (ntcod b), nt A => (b A) o[by _] (a A) ].
Next Obligation.
  pose (H 1_A 1_A). simpl in e. assert (1_A == 1_A) by reflexivity.
  apply e in H0.
  assert (dom (ntcod a :o 1_A) == dom (ntdom b :o 1_A)).
  { now rewrite H0. }
  rewrite nat_cod, nat_dom. apply H1.
Defined.
Next Obligation.
  intros A B E. apply map_equal. split; now rewrite E.
Defined.
Next Obligation.
  split.
  - intros A. simpl. now rewrite comp_dom, nat_dom.
  - intros A. simpl. now rewrite comp_cod, nat_cod.
  - intros f H0 H1. simpl. rewrite <-comp_assoc.
    assert (forall H00 H01 H02 H03, b (cod f) o[by H01] a (cod f) o[by H00] ntdom a :o f
    == b(cod f) o[by H03] (ntcod a :o f) o[by H02] a (dom f)).
    { intros. apply map_equal. split. apply natural. reflexivity. }
    rewrite H2, !comp_assoc. apply map_equal. split.
    reflexivity. 
    assert (forall H00 H01, b (cod f) o[by H00] ntcod a :o f ==
    b (cod f) o[by H01] ntdom b :o f).
    { intros. apply map_equal. split. now apply H. reflexivity. }
    rewrite H3. apply natural.
    Unshelve.
  + now rewrite nat_dom, compF_cod.
  + rewrite comp_cod. rewrite nat_cod, nat_dom.
    assert (f == f) by reflexivity.
    pose (H f f H2).
    assert (cod (ntcodMap a :o f) == cod (ntdomMap b :o f)).
    { now rewrite e. }
    simpl in H3. now rewrite compF_cod, compF_cod.
  + rewrite nat_cod. simpl. apply compatF_dom, id_dom. 
  + rewrite comp_cod, nat_dom, compF_cod. apply map_equal.
    now apply H.
  + rewrite nat_dom, compF_cod. apply map_equal. now apply H.
  + rewrite comp_dom, nat_cod. apply compatF_dom. apply id_dom.
  + rewrite nat_cod. apply compatF_dom. apply id_dom.
  + rewrite comp_dom, nat_dom, nat_cod. simpl. now apply map_equal, H.
  + now rewrite <-compF_cod, nat_dom.
Defined.
Next Obligation.
  intros [f g H] [f0 g0 H0] [Ef Eg]. split; try split.
  - apply Ef.
  - apply Eg.
  - simpl. intros A B E. apply map_equal. split; rewrite E;
    [now apply Ef | now apply Eg].
Defined.
Notation "b |o|[ 'by' H ] a" := (@Nattrans_vcomp _ _ $[b, a | H])
  (at level 53, right associativity,
  format "b  |o|[ 'by'  H ]  a") : cat_scope.

Program Definition Nattrans_id {X Y : Category} (F : X --> Y)
  := [ ntdom: F, ntcod: F, nt (A : X) => 1_(F A)].
Next Obligation. intros A B E. now rewrite E. Defined.
Next Obligation.
  split; intros; simpl.
  - now rewrite id_dom.
  - now rewrite id_cod.
  - now rewrite comp_idl, comp_idr.
Defined.

Program Canonical Structure FunctorCat (X Y : Category) :=
  [ dom: map (a : NattransSetoid X Y) => ntdom a, cod: map a => ntcod a,
    o: Nattrans_vcomp,
    1: map F => Nattrans_id F ].
Next Obligation.
  intros F G E. split; try split; try apply E.
  intros A B E0. rewrite E0. simpl.
  now apply map_equal, map_equal, E.
Defined.
Next Obligation.
  split.
  - intros f g H. simpl. intros A B E. now rewrite E.
  - intuition. simpl. intros A B E. now rewrite E.
  - intuition. split; try split; simpl in *.
  1,2: intros A B E; now rewrite E.
  intros A B E. rewrite comp_assoc. apply map_equal. split.
  now rewrite E. apply map_equal. split; now rewrite E.
  - intros F. intros A B E. now rewrite E.
  - intros F. intros A B E. now rewrite E.
  - intros a F H. split; try split; simpl in *.
  + apply H.
  + intros A B E. now rewrite E.
  + intros A B E. rewrite comp_idr. now rewrite E.
  - intros a F H. split; try split; simpl in *.
  + intros A B E. now rewrite E.
  + intros A B E. now rewrite E, <-(H A B E), E.
  + intros A B E. now rewrite comp_idl, E.
  Unshelve.
  rewrite nat_cod, nat_dom. simpl. now apply map_equal, H1.
  rewrite comp_dom, nat_cod, nat_dom. simpl. now apply map_equal, H.
Defined.
Notation "[ X , Y ]" := (@FunctorCat X Y)
  (at level 0, X, Y at level 99) : cat_scope.

Lemma compNtV_assoc (X Y : Category) (a b c : Nattrans X Y)
  H H0 H1 H2 : a |o|[by H0] b |o|[by H] c == (a |o|[by H1] b) |o|[by H2] c.
Proof. apply comp_assoc. Qed.


Lemma NattransLig_componentLig X Y (a b : Nattrans X Y) :
  cod a == dom b -> forall A, cod (a A) == dom (b A).
Proof.
  intros H A. rewrite nat_dom, nat_cod. simpl in *.
  now apply map_equal, H.
Qed.

Lemma stdeq_refl (X : Setoid) (A : X) : A == A.
Proof. reflexivity. Qed.

Lemma NattransIso_componentIso X Y (a b : Nattrans X Y) H H0 : 
  @IsIsopair _ a b H H0 == forall A, @IsIsopair _ (a A) (b A)
  (NattransLig_componentLig H A) (NattransLig_componentLig H0 A).
Proof.
  split.
  - intros [[H1 [H2]] [H4 [H5]]] A. split.
  + pose (H3 A A (stdeq_refl A)). simpl in e.
    rewrite nat_dom, <-e. now apply map_equal.
  + pose (H6 A A (stdeq_refl A)). simpl in e.
    rewrite nat_dom, <-e. now apply map_equal.
  - intros H1. split; split; try split; try now simpl;
    try now (intros A B E; rewrite E).
  + intros A B E. simpl.
    pose (H1 A). destruct i.
    rewrite nat_dom in H2. simpl in H2. rewrite <-E, <-H2.
    now apply map_equal.
  + intros A B E. pose (H1 B). destruct i.
    simpl. rewrite nat_dom in H3. simpl in H3.
    rewrite <-H3. apply map_equal. split; now rewrite E.
Qed.

Program Definition Nattrans_hcomp {X Y Z}
  : Dymap (Nattrans X Y) (Nattrans Y Z) (Nattrans X Z)
  := dmap a b => [ ntdom: (ntdom b) :o: (ntdom a),
    ntcod: (ntcod b) :o: (ntcod a),
    nt A => b ((ntcod a) A) o[by _] ((ntdom b) :o a A) ].
Next Obligation.
  now rewrite nat_dom, <-compF_cod, nat_cod.
Defined.
Next Obligation.
  intros A B E. apply map_equal. split; now rewrite E.
Defined.
Next Obligation.
  split.
  - intros A. simpl. now rewrite comp_dom, <-!compF_dom, nat_dom, id_dom.
  - intros A. simpl. now rewrite comp_cod, nat_cod, compF_dom.
  - intros. simpl in *. rewrite <-comp_assoc.
    assert (forall H00 H01 H02 H03, b (ntcod a (cod f)) o[by H01] (ntdom b :o a (cod f)) o[by H00]
      ntdom b :o ntdom a :o f == b (ntcod a (cod f)) o[by H03] ((ntdom b) :o (ntcod a :o f)) o[by H02] ((ntdom b) :o a (dom f)))
    as H2.
    { intros. apply map_equal. split.  rewrite <-!compF_morph.
      apply map_equal. rewrite natural. apply map_equal.
      split. all: reflexivity. }
    rewrite H2, !comp_assoc. apply map_equal. split.
    reflexivity.
    assert (forall f0, cod ntdom b :o f0 == dom b (cod f0)) as H1.
    { intros. now rewrite nat_dom, compF_cod. }
    assert (forall f0, cod b (dom f0) == dom ntcod b :o f0) as H3.
    { intros. now rewrite nat_cod, compF_dom. }
    pose (natural (H1 (ntcod a :o f)) (H3 (ntcod a :o f))) as e.
    assert (forall H8, (ntcod b :o ntcod a :o f) o[by H8] b (ntcod a (dom f))
      == (ntcod b :o ntcod a :o f) o[by H3 (ntcod a :o f)] 
      b (dom ntcod a :o f)) as H4.
    { intros. apply map_equal. split. now rewrite compF_dom. reflexivity. }
    rewrite H4, <-e. apply map_equal. split.
    reflexivity. now rewrite compF_cod.
    Unshelve.
    + now rewrite <-compF_cod, <-compF_dom, <-compF_cod, nat_dom.
    + now rewrite comp_cod, <-compF_cod, nat_dom, nat_cod.
    + now rewrite <-compF_cod, nat_dom.
    + now rewrite <-compF_dom, nat_cod.
    + now rewrite <-compF_dom, nat_cod.
    + now rewrite <-compF_cod, <-!compF_dom, nat_cod.
    + now rewrite comp_cod, <-!compF_cod, nat_dom.
    + now rewrite compF_cod, nat_dom, compF_cod.
    + now rewrite comp_dom, <-compF_cod, <-!compF_dom, nat_cod.
    + now rewrite nat_cod, <-!compF_dom, id_dom.
    + now rewrite comp_dom, <-compF_cod, nat_dom, nat_cod.
Defined.
Next Obligation.
  intros a a0 E b b0 E0. split; try split.
  - intros f f0 Ef. simpl. rewrite Ef.
    destruct E0 as [E0 [E00 E01]]. apply E0.
    destruct E as [E]. now apply E.
  - intros f f0 Ef. simpl.
    destruct E0 as [E0 [E00]]. apply E00.
    destruct E as [E1 [E2]]. now apply E2.
  - simpl. intros A A0 EA. apply map_equal. split.
    destruct E0 as [E0]. apply E0. now apply E.
    destruct E0 as [E0 [E00 E01]]. apply E01.
    destruct E as [E [E1]]. simpl in E1.
    rewrite EA. rewrite <-(id_dom A0), id_dom.
    now apply map_equal, E1.
Defined.
Notation "b =o= a" := (@Nattrans_hcomp _ _ _ a b)
  (at level 53, right associativity) : cat_scope.

Class IsEquivCat `(F : X --> Y) (G : Y --> X) 
  (eta : Nattrans X X) (xi : Nattrans Y Y) :=
{
  eqcat_etadom : dom eta == Functor_id X;
  eqcat_etacod : cod eta == G :o: F;
  eqcat_xidom : dom xi == F :o: G;
  eqcat_xicod : cod xi == Functor_id Y;
  eqcat_eta_iso : IsIsomorphism eta;
  eqcat_xi_iso : IsIsomorphism xi
}.

Structure EquivCat (X Y : Category) := {
  eqcat_fwd : X --> Y;
  eqcat_rev : Y --> X;
  eqcat_eta : Nattrans X X;
  eqcat_xi : Nattrans Y Y;
  eqcatprf :> IsEquivCat eqcat_fwd eqcat_rev eqcat_eta eqcat_xi
}.
#[global] Existing Instance eqcatprf.

Lemma compF_comp_assoc (X Y Z : Category) (F : X --> Y) (G : Y --> Z)
  (f : cathom X) : G :o F :o f == (G :o: F) :o f.
Proof. now idtac. Qed.

Lemma compF_assoc (X Y Z W : Category) (F : X --> Y) (G : Y --> Z)
  (H : Z --> W) : H :o: G :o: F == (H :o: G) :o: F.
Proof. intros f f0 Ef. now rewrite Ef. Qed.

Lemma Functor_eq (X Y : Category) (F G : X --> Y) (f : cathom X) :
  F == G -> F :o f == G :o f.
Proof. intros H. now apply H. Qed.

Notation "g o[] f" := (@homcomp _ $[g, f | _])
  (at level 60, right associativity,
  format "g  o[]  f") : cat_scope.

Lemma compatNtV_NtH (X Y Z : Category) (a b : Nattrans X Y)
  (a0 b0 : Nattrans Y Z) H H0 H1 :
  (b0 o[by H] a0) =o= (b o[by H0] a) == (b0 =o= b) o[by H1] (a0 =o= a).
Proof.
  split; try split.
  - intros f g E. simpl. now rewrite !compF_comp_assoc, E.
  - intros f g E. simpl. now rewrite !compF_comp_assoc, E.
  - intros A B E. rewrite E. simpl. rewrite <-!comp_assoc.
    apply map_equal. split. 2:reflexivity.
    assert (forall H00 H01 H02 H03,
      a0 (dom ntcod b :o 1_B) o[by H01] ntdom a0 :o b B o[by H00] a B
      == a0 (dom ntcod b :o 1_B) o[by H03] (ntdom a0 :o b B) o[by H02] ntdom a0 :o a B)
      as H2.
    { intros. apply map_equal. split. 2:reflexivity. apply compF_morph. }
    rewrite H2, !comp_assoc. apply map_equal. split. reflexivity.
    assert (forall H00 H01, (ntdom b0 :o b B) o[by H00] a0 (dom ntcod a :o 1_B)
      == (ntcod a0 :o b B) o[by H01] a0 (dom b B)) as H3.
    { intros. apply map_equal. split. apply map_equal.
      rewrite nat_dom, <-compF_dom, id_dom. simpl. apply map_equal.
      now apply (H0 1_B 1_B). now apply Functor_eq. }
    rewrite H3, <-natural. apply map_equal. split.
    reflexivity. rewrite nat_cod. now simpl.
    Unshelve.
  + rewrite compF_morph, comp_cod, nat_dom, <-compF_cod. apply map_equal.
    now rewrite idF_morph, id_dom, nat_cod.
  + rewrite comp_cod, nat_cod, nat_dom. simpl. apply map_equal.
    simpl in H. now apply H.
  + rewrite comp_cod, nat_cod. rewrite <-(compF_dom (ntdom b0)).
    simpl. apply map_equal. simpl in H. apply H.
    apply map_equal. rewrite <-compF_dom, id_dom, nat_dom.
    simpl. apply map_equal. simpl in H0. now apply H0.
  + rewrite comp_cod, <-compF_cod, nat_dom. apply map_equal.
    now rewrite nat_cod, <-compF_dom, id_dom.
  + rewrite <-compF_cod, <-compF_dom. apply map_equal.
    rewrite nat_cod, nat_dom. simpl. apply map_equal.
    simpl in H0. now apply H0.
  + rewrite comp_cod, <-compF_cod, nat_dom. apply map_equal.
    now rewrite nat_cod, <-compF_dom, id_dom.
  + rewrite <-compF_cod, nat_dom. apply map_equal.
    now rewrite nat_cod, <-compF_dom, id_dom.
  + rewrite comp_dom, <-compF_cod, <-compF_dom. apply map_equal.
    rewrite nat_cod, nat_dom. simpl. simpl in H0.
    now apply map_equal, H0.
  + rewrite nat_cod, <-!compF_dom, id_dom, nat_dom. simpl in *.
    now apply map_equal, H, map_equal, map_equal, H0.
  + now rewrite comp_dom, <-compF_cod, nat_dom, nat_cod, <-compF_dom, id_dom.
  + now rewrite <-compF_dom, nat_cod, nat_dom.
  + now rewrite <-compF_cod, nat_dom, nat_cod.
  Unshelve.
  rewrite <-compF_cod, <-compF_dom. apply map_equal.
  rewrite nat_cod, nat_dom. simpl in *. now apply map_equal, H0.
Qed.

Program Definition EquivCatSetoid :=
  [ ==: (X : Category) Y => exists (F : X --> Y) (G : Y --> X)
    (eta : Nattrans X X) (xi : Nattrans Y Y),
    IsEquivCat F G eta xi ].
Next Obligation.
  split.
  - intros X. exists (Functor_id X), (Functor_id X),
    1_(Functor_id X), 1_(Functor_id X). split.
  + apply id_dom.
  + now rewrite id_cod.
  + now rewrite id_dom.
  + now rewrite id_cod.
  + exists 1_(Functor_id X).
    assert (cod 1_(Functor_id X) == dom 1_(Functor_id X)) as H.
    { now rewrite id_dom, id_cod. }
    exists H, H. split.
  * split; try split; try apply map_equal; try rewrite comp_idl;
    try now rewrite id_dom. intros f f0 E. simpl. now rewrite comp_idl, E.
  * now rewrite comp_idl, id_dom.
  + exists 1_(Functor_id X).
    assert (cod 1_(Functor_id X) == dom 1_(Functor_id X)) as H.
    { now rewrite id_dom, id_cod. }
    exists H, H. split.
  * split; try split; try apply map_equal; try rewrite comp_idl;
    try now rewrite id_dom. intros f f0 E. simpl. now rewrite comp_idl, E.
  * now rewrite comp_idl, id_dom.
  - intros X Y [F [G [eta [xi [E E0 E1 E2 [f] [g]]]]]].
    exists G, F, g, f. split.
  + rewrite <-E2. now destruct H0.
  + rewrite <-E1. now destruct H0 as [H0 [H1]].
  + rewrite <-E0. now destruct H.
  + rewrite <-E. now destruct H as [H [H1]].
  + exists xi. destruct H0 as [H0 [H1]]. exists H1, H0.
    destruct H2. now split.
  + exists eta. destruct H as [H [H1]]. exists H1, H.
    destruct H2. now split.
  - intros X Y Z [F [G [eta [xi [E E0 E1 E2 [f] [g]]]]]].
    intros [F0 [G0 [eta0 [xi0 [E00 E01 E02 E03 [f0] [g0]]]]]].
    exists (F0 :o: F), (G :o: G0).
    pose (1_G =o= eta0 =o= 1_F) as eta1.
    assert (cod eta == dom eta1) as H3.
    { rewrite E0. simpl. intros f1 f2 Ef. rewrite Ef. rewrite !compF_comp_assoc.
      apply Functor_eq. rewrite E00. intros f3 f4 Ef3. now rewrite Ef3. }
    exists (eta1 |o|[by H3] eta).
    pose (1_F0 =o= xi =o= 1_G0) as xi1.
    assert (cod xi1 == dom xi0) as H4.
    { rewrite E02. simpl. intros f1 f2 Ef. rewrite Ef, !compF_comp_assoc.
      apply Functor_eq. rewrite E2. intros f3 f4 Ef3. now rewrite Ef3. }
    exists (xi0 |o|[by H4] xi1).
    split.
  + simpl. intros f1 f2 Ef. pose (E f1 f2 Ef). simpl in e.
    now rewrite e.
  + rewrite compF_assoc, <-(compF_assoc F0), <-E01. simpl.
    intros f1 f2 Ef. now rewrite Ef.
  + rewrite compF_assoc, <-(compF_assoc G), <-E1. simpl.
    intros f1 f2 Ef. now rewrite Ef.
  + now rewrite E03.
  + destruct H as [Ef [Ef1 [H H5]]].
    destruct H0 as [Eg [Eg1 [H6 H7]]].
    destruct H1 as [Ef0 [Ef01 [Hf0 Hf01]]].
    destruct H2 as [Eg0 [Eg01 [Hg0 Hg01]]].
    pose (1_G =o= f0 =o= 1_F) as f1.
    assert (cod f1 == dom f) as H0.
    { rewrite <-Ef, E0. simpl. intros f01 f02 Ef02.
      rewrite Ef02, !compF_comp_assoc. apply Functor_eq.
      rewrite Ef01, E00. intros f03 f04 Ef03. now rewrite Ef03. }
    exists (_ |o|[by H0] _).
    assert (cod eta1 |o|[by H3] eta == dom f |o|[by H0] f1) as H1.
    { rewrite comp_dom, comp_cod. intros f01 f02 Ef02. simpl.
      rewrite !compF_comp_assoc, Ef02. apply Functor_eq.
      now rewrite Ef0. } 
    assert (cod f |o|[by H0] f1 == dom eta1 |o|[by H3] eta) as H2.
    { now rewrite comp_cod, comp_dom. }
    exists H1, H2. split.
  * rewrite comp_dom, E. rewrite comp_assoc.
    assert (forall H00, f1 o[by H00] eta1 == Nattrans_id _).
  split; try split.
  -- intros f01 f02 Ef02. pose (E f01 f02 Ef02). now rewrite e.
  -- intros f01 f02 Ef02.
     assert (cod f == Functor_id X) as H8 by now rewrite Ef1.
     pose (H8 _ _ Ef02). now rewrite e.
  -- assert (f |o|[by H0] f1 o[by H1] eta1 |o|[by H3] eta
      == (f |o|[by H0] f1) |o|[by H1] (eta1 |o|[by H3] eta)).
     { reflexivity. }
     rewrite H8.
      rewrite compNtV_assoc.