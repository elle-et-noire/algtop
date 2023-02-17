Generalizable All Variables.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Reversible Pattern Implicit.
Set Primitive Projections.
Set Universe Polymorphism.

Require Import ChoiceFacts.
Require Export Coq.Program.Basics Coq.Program.Tactics
  Coq.Setoids.Setoid Coq.Classes.Morphisms.
Require Import FunctionalExtensionality ProofIrrelevance.

Declare Scope cat_scope.
Open Scope cat_scope.

Obligation Tactic :=
  (try now intros x); (try now split; intros x); intros.

Class IsCategory (obj : Type) (hom : obj -> obj -> Type)
  (comp : forall {A B C}, hom A B -> hom B C -> hom A C)
  (id : forall A, hom A A) :=
{
  compA : forall A B C D (f : hom A B) (g : hom B C)
    (h : hom C D), comp (comp f g) h = comp f (comp g h);
  compf1 : forall A B (f : hom A B), comp (id A) f = f;
  comp1f : forall A B (f : hom A B), comp f (id B) = f
}.

Structure Category := {
  catobj :> Type;
  cathom : catobj -> catobj -> Type;
  homcomp : forall A B C,
    cathom A B -> cathom B C -> cathom A C;
  catid : forall A, cathom A A;

  catprf :> IsCategory homcomp catid
}.
#[global] Existing Instance catprf.

Notation "[ 'o:' comp , '1:' id ]" :=
  (@Build_Category _ _ comp id _)
  (at level 0, comp, id at level 99) : cat_scope.
Notation "[ 'comp' A B C f g => P , 'id' D => Q ]"
  := [ o: fun A B C f g => P, 1: fun D => Q ]
  (at level 0, A binder, B binder, C binder, D binder,
  f binder, g binder, P, Q at level 99) : cat_scope.
Notation "A ~[ X ]> B" := (@cathom X A B)
  (at level 90, no associativity) : cat_scope.
Notation "A ~> B" := (A ~[_]> B)
  (at level 90, no associativity) : cat_scope.
Notation "g 'o' f" := (@homcomp _ _ _ _ f g)
  (at level 60, right associativity) : cat_scope.
Notation "1_ A" := (@catid _ A)
  (at level 0, right associativity,
  format "1_ A") : cat_scope.

Definition IsIsopair (X : Category) (A B : X)
  (f : A ~> B) (g : B ~> A) := g o f = 1_A /\ f o g = 1_B.

Definition IsIsomorphism (X : Category) (A B : X)
  (f : A ~> B) := exists g, IsIsopair f g.

Definition IsIsomorphic (X : Category) (A B : X) :=
  exists (f : A ~> B) (g : B ~> A), IsIsopair f g.
Notation "A === B" := (@IsIsomorphic _ A B)
  (at level 70, no associativity) : cat_scope.

Program Definition OppCat (X : Category) :=
  [ comp (A : X) B C (f : B ~> A) (g : C ~> B) => f o g , id A => 1_A ].
Next Obligation.
  split; simpl; intuition.
  - now rewrite compA.
  - now rewrite comp1f.
  - now rewrite compf1.
Defined.
Notation "C ^op" := (@OppCat C)
  (at level 40, left associativity, format "C ^op") : cat_scope.

Class IsFunctor (X Y : Category) (fobj : X -> Y)
  (fhom : forall {A B}, (A ~> B) -> (fobj A ~> fobj B)) :=
{
  compFC : forall A B C (f : A ~> B) (g : B ~> C),
    fhom (g o f) = (fhom g) o (fhom f);
  idFC : forall A, fhom 1_A = 1_(fobj A)
}.

Structure Functor (X Y : Category) := {
  funobj :> X -> Y;
  funhom : forall A B, (A ~> B) -> (funobj A ~> funobj B);
  funprf :> IsFunctor funhom
}.
#[global] Existing Instance funprf.

Notation "X --> Y" := (@Functor X Y)
  (at level 55, right associativity) : cat_scope.
Notation "F ':o' f" := (@funhom _ _ F _ _ f)
  (at level 60, right associativity) : cat_scope.
Notation "[ 'obj:' F , 'hom:' Ff ]" :=
  (@Build_Functor _ _ F Ff _)
  (at level 0, F, Ff at level 99, no associativity) : cat_scope.
Notation "[ 'obj' A => FA , 'hom' B C f => Ff ]" :=
  [ obj: fun A => FA , hom: fun B C f => Ff ]
  (at level 0, A binder, B binder, C binder, f binder,
  FA, Ff at level 99, no associativity)
  : cat_scope.

Inductive hom_eq {X : Category} {A B : X} (f : A ~> B)
  : forall {C D}, C ~> D -> Prop :=
  hom_eqref : forall (g : A ~> B), f = g -> hom_eq f g.
Notation "f =H g" := (@hom_eq _ _ _ f _ _ g)
  (at level 70, no associativity) : cat_scope.

Axiom Functor_eq : forall X Y (F G : X --> Y),
  (forall A B (f : A ~> B), F :o f =H G :o f) -> F = G.

(* Lemma hom_eq_refl' {X : Category} {A B : X} (f g : A ~> B)
  : f =H g -> f = g.
Proof. intros H. 
pose (match H as p in (_ =H h) return (_ = h) with hom_eqref H0 => H0 end). case H. Qed.

Lemma Functor_eq X Y (F G : X --> Y)
  : (forall A B (f : A ~> B), F :o f =H G :o f) -> F = G.
Proof.
  intros H. destruct F, G. simpl in *.
  assert (funobj0 = funobj1). { apply functional_extensionality.
  intros x. now destruct (H x x 1_x). }
  destruct H0.
  assert (funhom0 = funhom1). { 
    apply functional_extensionality_dep. intros A.
    apply functional_extensionality_dep. intros B.
    apply functional_extensionality_dep. intros f.
    pose (H A B f).  case h.
  intros x. 
  }
  apply f_equal3.
  
  apply functional_extensionality_dep.
  
  destruct F, G, H. simpl in *.
  apply f_equal3. apply functional_extensionality_dep. *)

(* Type Cat *)

Program Definition TypeCat :=
  [ comp A B C (f : A -> B) (g : B -> C) => fun x => g (f x),
    id A => fun a => a ].

(* CAT *)

Program Definition Functor_comp {X Y Z : Category}
  : (X --> Y) -> (Y --> Z) -> (X --> Z) := fun F G =>
  [ obj A => G (F A), hom A B f => G :o (F :o f) ].
Next Obligation.
  split.
  - intros A B C f g. simpl. now rewrite !compFC.
  - intros A. simpl. now rewrite !idFC.
Defined.
Notation "G :o: F" := (@Functor_comp _ _ _ F G)
  (at level 54, right associativity) : cat_scope.

Program Canonical Structure CAT :=
  [ comp X Y Z (F : X --> Y) (G : Y --> Z) => G :o: F,
    id X => [ obj (A : X) => A, hom A B f => f ] ].
Next Obligation.
  split; intuition;
  apply Functor_eq; intros A0 B0 f0; now apply hom_eqref.
Defined.

Class IsFaithful `(F : X --> Y) := {
  faith : forall A B (f g : A ~> B),
    F :o f = F :o g -> f = g
}.

Class IsFull `(F : X --> Y) := {
  full : forall A B (f : F A ~> F B),
    exists (g : A ~> B), F :o g = f
}.

Class IsNattrans {X Y} {F G : X --> Y} (c : forall A, F A ~> G A) := {
  natural : forall A B (f : A ~> B),
    (c B) o (F :o f) = (G :o f) o (c A)
}.

Structure Nattrans {X Y} (F G : X --> Y) := {
  component :> forall A, F A ~> G A;
  ntprf :> IsNattrans component
}.
#[global] Existing Instance ntprf.

Notation "F ==> G" := (@Nattrans _ _ F G)
  (at level 55, right associativity) : cat_scope.
Notation "[ ==>: C ]" := (@Build_Nattrans _ _ _ _ C _)
  (at level 0, C at level 99) : cat_scope.
Notation "[ 'nt' A => P ]" := [ ==>: fun A => P ]
  (at level 0, A binder, P at level 99) : cat_scope.

Lemma nt_eq X Y (F G : X --> Y) (a b : F ==> G) :
  (forall A, a A = b A) -> a = b.
Proof.
  intros H. destruct a, b. simpl in *.
  assert (component0 = component1) as H0 by now apply functional_extensionality_dep.
  destruct H0. apply f_equal, proof_irrelevance.
Qed.

Program Definition Nattrans_vcomp {X Y} {F G H : X --> Y}
  (a : F ==> G) (b : G ==> H) : F ==> H :=
  [ nt A => (b A) o (a A) ].
Next Obligation.
  split; intros.
   now rewrite <-compA, natural, compA, natural, compA.
Defined.
Notation "b |o| a" := (@Nattrans_vcomp _ _ _ _ _ a b)
  (at level 53, right associativity) : cat_scope.

Program Canonical Structure FunctorCat (X Y : Category) :=
  [ comp (F : X --> Y) G H (a : F ==> G) (b : G ==> H)
    => b |o| a, id F => _ ].
Next Obligation.
  refine [ nt A => 1_(F A) ]. split.
  intros A B f. now rewrite compf1, comp1f.
Defined.
Next Obligation.
  split; intuition; apply nt_eq; intuition; simpl.
  - now rewrite compA.
  - now rewrite compf1.
  - now rewrite comp1f.
Defined.
Notation "[ X , Y ]" := (@FunctorCat X Y)
  (at level 0, X, Y at level 99) : cat_scope.

Lemma natiso_cmpiso X Y (F G : X --> Y) (a : F ==> G) :
  DependentFunctionalChoice ->
  (IsIsomorphism a <-> forall A, IsIsomorphism (a A)).
Proof.
  intros DFC. unfold IsIsomorphism, IsIsopair. split; simpl in *.
  - intros [g [E E0]] A. exists (g A). split.
  + assert (g A o a A = (g |o| a) A) as H by intuition.
    now rewrite H, E.
  + assert (a A o g A = (a |o| g) A) as H by intuition.
    now rewrite H, E0.
  - intros H.
    pose (DFC X (fun A => G A ~> F A) (fun A g => g o a A = 1_(F A) /\ a A o g = 1_(G A))).
    simpl in *. destruct (e H) as [g H0].
    assert (IsNattrans g).
    { split. intros. rewrite <-(compf1 (G :o f)),
      <-(proj2 (H0 A)), (compA (g A)), <-natural, !compA.
      apply f_equal2; intuition. rewrite <-(comp1f (F :o f)) at 2.
      apply f_equal2; intuition. now rewrite <-(proj1 (H0 B)). }
    exists (Build_Nattrans H1). split; apply nt_eq;
    intros A; simpl in *;
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

Definition Cat_equiv (X Y : Category) :=
  exists (F : X --> Y) (G : Y --> X)
    (eta : 1_X ==> G :o: F) (xi : F :o: G ==> 1_Y),
    IsEquivCat eta xi.

Program Definition Nattrans_hcomp {X Y Z} {F G : X --> Y} {F0 G0 : Y --> Z}
  (a : F ==> G) (b : F0 ==> G0) : F0 :o: F ==> G0 :o: G :=
  [ nt A => b (G A) o (F0 :o a A) ].
Next Obligation.
  split. intros A B f. simpl. rewrite !natural.
  rewrite <-!compA. rewrite !natural. rewrite compA.
  now rewrite <-compFC, !natural, compFC, compA.
Defined.
Notation "b =o= a" := (@Nattrans_hcomp _ _ _ _ _ _ _ a b)
  (at level 53, right associativity) : cat_scope.

Lemma Cat_equiv_equiv : Equivalence Cat_equiv.
Proof.
  split; unfold Cat_equiv.
  - intros X. exists 1_X, 1_X, 1_(1_X), 1_(1_X).
    split; exists 1_(1_X); split; try apply comp1f.
  - intros X Y [F [G [eta [xi [[eta0 [H H0]] [xi0 [H1 H2]]]]]]].
    exists G, F, xi0, eta0. split; [exists xi | exists eta]; now split.
  - intros X Y Z [F [G [eta [xi H]]]] [F0 [G0 [eta0 [xi0 H0]]]].
    destruct H as [[g [H H1]] [g0 [H2 H3]]].
    destruct H0 as [[h [H4 H5]] [h0 [H6 H7]]].
    exists (F0 :o: F), (G :o: G0).
    pose (1_G =o= eta0 =o= 1_F).
    rewrite comp1f in n. pose (n o eta). rewrite !compA, <-compA in c.
    exists c. pose (1_F0 =o= xi =o= 1_G0).
    rewrite comp1f in n0. pose (xi0 o n0). rewrite !compA, <-compA in c0.
    exists c0.

    split; unfold IsIsomorphism.
  + pose (1_G =o= h =o= 1_F). rewrite comp1f in n1.
    pose (g o n1). rewrite !compA, <-compA in c1. exists c1.
    split. rewrite <-H. unfold c.
Program Definition EquivCatSetoid :=
  [ ==: (X : Category) Y =>  ].
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
