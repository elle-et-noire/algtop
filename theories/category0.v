Generalizable All Variables.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Reversible Pattern Implicit.
Set Primitive Projections.
Set Universe Polymorphism.

Require Export setoid.
Require Import ChoiceFacts.

Declare Scope cat_scope.
Open Scope setoid_scope.
Open Scope cat_scope.

Obligation Tactic :=
  (try now intros x); (try now split; intros x); intros; (try apply \ISE).

Class IsCategory obj (hom : obj -> obj -> Setoid)
  (comp : forall {A B C}, hom A B -> hom B C -> hom A C)
  (id : forall A, hom A A) :=
{
  comp_assoc : forall A B C D (f : hom A B)
    (g : hom B C) (h : hom C D),
    comp (comp f g) h == comp f (comp g h);
  comp_idr : forall A B (f : hom A B), comp (id A) f == f;
  comp_idl : forall A B (f : hom A B), comp f (id B) == f;
}.

Structure Category := {
  catobj :> Type;
  cathom :> catobj -> catobj -> Setoid;
  #[canonical=no]homcomp : forall A B C,
    Dymap (cathom A B) (cathom B C) (cathom A C);
  catid : forall A, cathom A A;

  catprf : IsCategory homcomp catid
}.
#[global] Existing Instance catprf.

Notation "[ '~>:' hom , 'o:' comp , '1:' id ]"
  := (@Build_Category _ hom comp id _)
  (at level 0, hom, comp, id at level 99) : cat_scope.
Notation "[ 'hom' A B => P , 'comp' A0 B0 C f g => P0 , 'id' A1 => P1 ]"
  := [ ~>: fun A B => P, o: fun A0 B0 C => dmap f g => P0, 1: fun A1 => P1 ]
  (at level 0, A binder, B binder, A0 binder, B0 binder, C binder,
  f binder, g binder, A1 binder, P, P0, P1 at level 99) : cat_scope.
Notation "A ~[ X ]> B" := (@cathom X A B)
  (at level 90, no associativity) : cat_scope.
Notation "A ~> B" := (A ~[_]> B)
  (at level 90, no associativity) : cat_scope.
Notation "g 'o' f" := (@homcomp _ _ _ _ f g)
  (at level 60, right associativity) : cat_scope.
Notation "1_ A" := (@catid _ A)
  (at level 0, right associativity,
  format "1_ A") : cat_scope.

Lemma compA (X : Category) (A B C D : X) (f : A ~> B)
  (g : B ~> C) (h : C ~> D) : h o g o f == (h o g) o f.
Proof. apply (comp_assoc(IsCategory:=catprf X)). Qed.

Lemma compf1 (X : Category) (A B : X) (f : A ~> B) : f o 1_A == f.
Proof. apply (comp_idr(IsCategory:=catprf X)). Qed.

Lemma comp1f (X : Category) (A B : X) (f : A ~> B) : 1_B o f == f.
Proof. apply (comp_idl(IsCategory:=catprf X)). Qed.

Definition IsIsomorphism (X : Category) (A B : X) (f : A ~> B) :=
  exists g : B ~> A, g o f == 1_A /\ f o g == 1_B.

Definition IsIsomorphic (X : Category) (A B : X) :=
  exists f : A ~> B, IsIsomorphism f.
#[global] Hint Unfold IsIsomorphism IsIsomorphic : eq.
Program Definition IsomorphSetoid (X : Category) :=
  [ X | ==: @IsIsomorphic X ].
Next Obligation.
  split; intros A; simpeq_all.
  - exists 1_A, 1_A. split; now rewrite comp1f.
  - intros B [f [g [E E0]]]. exists g, f. now split.
  - intros B C [f [g [E E0]]] [f0 [g0 [E1 E2]]].
    exists (f0 o f), (g o g0). split.
  + now rewrite <-compA, (compA _ _ g0), E1, comp1f.
  + now rewrite <-compA, (compA _ _ f), E0, comp1f.
Defined.
Notation "A === B" := (A == B in @IsomorphSetoid _)
  (at level 70, no associativity) : cat_scope.

Program Definition OppCat (X : Category) :=
  [ hom B A => A ~> B,
    comp A B C f g => f o g ,
     id A => 1_A ].
Next Obligation.
  intros f f0 E g g0 E0. now rewrite E, E0.
Defined.
Next Obligation.
  split; simpl; intuition.
  - now rewrite compA.
  - now rewrite comp1f.
  - now rewrite compf1.
Defined.

Notation "C ^op" := (@OppCat C)
  (at level 40, left associativity, format "C ^op") : cat_scope.

Class IsFunctor (X Y : Category) (fobj : X -> Y)
  (fhom : forall {A B}, Map (A ~> B) (fobj A ~> fobj B)) :=
{
  compFC : forall A B C (f : A ~> B) (g : B ~> C),
    fhom (g o f) == (fhom g) o (fhom f);
  idFC : forall A, fhom 1_A == 1_(fobj A)
}.

Structure Functor (X Y : Category) := {
  funobj :> X -> Y;
  funhom : forall A B, Map (A ~> B) (funobj A ~> funobj B);
  funprf :> IsFunctor funhom
}.
#[global] Existing Instance funprf.

Notation "X --> Y" := (@Functor X Y) : cat_scope.
Notation "F ':o' f" := (@funhom _ _ F _ _ f)
  (at level 60, right associativity) : cat_scope.
Notation "[ 'obj:' F , 'hom:' Ff ]" :=
  (@Build_Functor _ _ F Ff _)
  (at level 0, F, Ff at level 99, no associativity) : cat_scope.
Notation "[ 'obj' A => FA , 'hom' B C f => Ff ]" :=
  [ obj: fun A => FA , hom: fun B C => map f => Ff ]
  (at level 0, A binder, B binder, C binder, f binder,
  FA, Ff at level 99, no associativity)
  : cat_scope.

Inductive hom_eq {X : Category} {A B : X} (f : A ~> B)
  : forall {C D}, C ~> D -> Prop :=
  hom_eqref : forall (g : A ~> B), f == g -> hom_eq f g.
Notation "f =H g" := (@hom_eq _ _ _ f _ _ g)
  (at level 70, no associativity) : cat_scope.

Program Canonical Structure FunctorSetoid X Y :=
  [ ==: (F : X --> Y) G => forall A B (f : A ~> B), F :o f =H G :o f ].
Next Obligation.
  split.
  - now intros F f.
  - intros F G H A B f. destruct (H _ _ f). now split.
  - intros F G H H0 H1 A B f. destruct (H1 _ _ f).
    destruct (H0 _ _ f). split. now rewrite H3.
Defined.
Notation "X [-->] Y" := (@FunctorSetoid X Y)
  (at level 55) : cat_scope.

Program Definition funcSetoid X Y :=
  [ X -> Y | ==: fun f g => forall x, f x = g x ].
Next Obligation.
  split; intuition. intros f g h E E0 x. now rewrite E.
Defined.

Program Definition TypeCat :=
  [ hom A B => funcSetoid A B, comp A B C f g => fun x => g (f x),
    id A => fun x => x ].
Next Obligation.
  intros f f0 E g g0 E0 x. now rewrite E, E0.
Defined.

Program Definition Functor_comp {X Y Z : Category}
  : Dymap (X --> Y) (Y --> Z) (X --> Z) := dmap F G =>
  [ obj A => G (F A), hom A B f => G :o (F :o f) ].
Next Obligation.
  intros f f0 E. now rewrite E.
Defined.
Next Obligation.
  split.
  - intros A B C f g. simpl. now rewrite !compFC.
  - intros A. simpl. now rewrite !idFC.
Defined.
Next Obligation.
  intros F F0 E G G0 E0 A B f. simpl in *.
  destruct (E A B f). destruct (E0 (F A) (F B) g).
  split. now rewrite H.
Defined.
Notation "G :o: F" := (@Functor_comp _ _ _ F G)
  (at level 54, right associativity) : cat_scope.

Program Canonical Structure CAT :=
  [ hom X Y => X [-->] Y, comp X Y Z F G => G :o: F,
    id X => [ obj A => A, hom A B f => f ] ].
Next Obligation. apply Functor_comp_obligation_3. Defined.
Check CAT_obligation_4.

Class IsFaithful `(F : X --> Y) := {
  faith : forall A B (f g : A ~> B), F :o f == F :o g -> f == g
}.

Class IsFull `(F : X --> Y) := {
  full : forall A B (f : F A ~> F B),
    exists (g : A ~> B), F :o g == f
}.

Class IsNattrans {X Y} {F G : X --> Y} (c : forall A, F A ~> G A) := {
  natural : forall A B (f : A ~> B),
    (c B) o (F :o f) == (G :o f) o (c A)
}.

Structure Nattrans {X Y} (F G : X --> Y) := {
  component :> forall A, F A ~> G A;
  ntprf :> IsNattrans component
}.
#[global] Existing Instance ntprf.

Notation "F ==> G" := (@Nattrans _ _ F G) : cat_scope.
Notation "[ ==>: C ]" := (@Build_Nattrans _ _ _ _ C _)
  (at level 0, C at level 99) : cat_scope.
Notation "[ 'nt' A => P ]" := [ ==>: fun A => P ]
  (at level 0, A binder, P at level 99) : cat_scope.

Lemma ntcomm X Y (F G : X --> Y) (a : F ==> G) A B (f : A ~> B)
  : (a B) o (F :o f) == (G :o f) o (a A).
Proof. apply ntprf. Qed.

Definition nt_eq {X Y} (F G : X --> Y) (a b : F ==> G) :=
  forall A, a A == b A.
#[global] Hint Unfold nt_eq : eq.
Program Canonical Structure NattransSetoid {X Y} (F G : X --> Y) :=
  [ _ | ==: @nt_eq _ _ F G ].
Next Obligation.
  split; try now intros a. intros a b c H H0 A.
  simpeq_all. now rewrite H.
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
  now rewrite E, E0.
Defined.
Notation "b |o| a" := (@Nattrans_vcomp _ _ _ _ _ a b)
  (at level 53, right associativity) : cat_scope.

Program Canonical Structure FunctorCat (X Y : Category) :=
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

Program Definition FunctorImId {X Y} {F F0 : X --> Y} (H : F == F0)
  (A : X) : F A ~> F0 A.
simpl in *. pose (H A A (1_A)).
destruct h.

Program Definition nt_revlconv {X Y} {F F0 : X --> Y} (H : F == F0)
  : F ==> F0.
destruct F as [F Fhom Fprf].
destruct F0 as [F0 Fhom0 Fprf0].
simpl in *. 
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