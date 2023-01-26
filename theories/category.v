Generalizable All Variables.
Set Implicit Arguments.
Unset Strict Implicit.

Unset Printing Implicit Defensive.
Set Reversible Pattern Implicit.
Set Primitive Projections.
Set Universe Polymorphism.

Require Export setoid.

Declare Scope cat_scope.
Open Scope setoid_scope.
Open Scope cat_scope.

Class IsCategory (obj : Type) (hom : obj -> obj -> Setoid)
  (comp : forall {A B C}, hom A B -> hom B C -> hom A C)
  (id : forall A, hom A A) :=
{
  compcA : forall A B C D (f : hom A B) (g : hom B C) (h : hom C D),
    comp f (comp g h) == comp (comp f g) h;
  compc1 : forall A B (f : hom A B), comp (id A) f == f;
  comp1c : forall A B (f : hom A B), comp f (id B) == f;
}.

Structure Category := {
  catobj :> Type;
  cathom :> catobj -> catobj -> Setoid;
  catcomp : forall A B C, Dymap (cathom A B) (cathom B C) (cathom A C);
  catid : forall A, cathom A A;

  catprf :> IsCategory catcomp catid
}.
#[global] Existing Instance catprf.

Notation "[ O | '~>:' hom , 'o:' comp , '1:' id ]"
  := (@Build_Category O hom comp id _)
  (at level 0, O, hom, comp, id at level 99) : cat_scope.
Notation "A ~[ X ]> B" := (@cathom X A B)
  (at level 99, right associativity) : cat_scope.
Notation "A ~> B" := (A ~[_]> B)
  (at level 99, right associativity) : cat_scope.
Notation "g 'o' f" := (@catcomp _ _ _ _ f g)
  (at level 60, right associativity) : cat_scope.
Notation "1_ A" := (@catid _ A)
  (at level 0, A at level 99, no associativity,
  format "1_ A") : cat_scope.

Class IsInverse (C : Category) (A B : C) (f : A ~> B)
   (g : B ~> A) := {
  invcomp1 : g o f == 1_A;
  invcomp2 : f o g == 1_B
}.

Structure Isomorph (C : Category) (A B : C) := {
  orthohom : A ~> B;
  invhom : B ~> A;
  isoprf :> IsInverse orthohom invhom
}.
#[global] Existing Instance isoprf.

Program Definition OppCat (X : Category) :=
  [ _ | ~>: fun A B => X B A,
        o: fun A B C => dmap f g => f o g,
        1: fun A => 1_A ].
Next Obligation.
  intros f f0 H g g0 H0. now rewrite H, H0.
Defined.
Next Obligation.
  split; intuition; simpl.
  - now srewrite compcA.
  - now srewrite comp1c.
  - now srewrite compc1.
Defined.
Notation "C ^op" := (@OppCat C)
  (at level 40, left associativity, format "C ^op") : cat_scope.

Program Definition funcSetoid (X Y : Type) :=
  [ X -> Y | ==: fun f g => forall x, f x = g x ].
Next Obligation.
  split; intuition. intros f g h E E0 x. now rewrite E.
Defined.

Program Definition TypeCat :=
  [ _ | ~>: funcSetoid,
        o: fun A B C => dmap f g => fun x => g (f x),
        1: fun X x => x ].
Next Obligation.
  intros a a0 E b b0 E0 x. now rewrite E, E0.
Defined.
Next Obligation.
  split; intuition; now intros x.
Defined.

Class IsFunctor (X Y : Category) (fobj : X -> Y)
  (fhom : forall {A B}, (A ~> B) -> (fobj A ~> fobj B)) :=
{
  fhomcomp : forall {A B C} (f : A ~> B) (g : B ~> C),
    fhom (g o f) == fhom g o fhom f;
  fhom1 : forall {A}, fhom (1_A) == 1_(fobj A)
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

Notation "[ 'obj:' F | 'hom:' Ff ]" :=
  (@Build_Functor _ _ F Ff _)
  (at level 0, F, Ff at level 99, no associativity) : cat_scope.
Notation "[ 'obj' A => FA | 'hom' { B , C } f => Ff ]" :=
  [ obj: fun A => FA | hom: fun B C => map f => Ff ]
  (at level 0, A, FA, B, C, f, Ff at level 99, no associativity)
  : cat_scope.

Inductive hom_eq (X : Category) (A B : X) (f : A ~> B)
  : forall (C D : X), (C ~> D) -> Prop :=
  hom_eqref : forall (g : A ~> B), f == g -> hom_eq f g.
Notation "f =H g 'in' X" := (@hom_eq X _ _ f _ _ g)
  (at level 70, g at next level) : cat_scope.
Notation "f =H g" := (f =H g in _)
  (at level 70) : cat_scope.

Program Definition CatCat :=
  [ Category | ~>: fun X Y =>
     [ X --> Y | ==: fun F G => forall A B (f : A ~> B), F :o f =H G :o f],
               o: fun X Y Z => dmap F G =>
     [ obj A => G (F A) | hom {_, _} f => G :o F :o f ],
               1: fun X => [ obj A => A | hom {_, _} f => f ] ].
Next Obligation.
  split.
  - now intros F A B f.
  - intros F G H A B f. destruct (H A B f). now apply hom_eqref.
  - intros F G H E E0 A B f. destruct (E0 A B f). destruct (E A B f).
    apply hom_eqref. now rewrite <-H0.
Defined.
Next Obligation.
  intros f g E. now rewrite E.
Defined.
Next Obligation.
  destruct F as [Ff Fhom [Fcomp Fid]].
  destruct G as [Gf Ghom [Gcomp Gid]].
  split; simpl in *; intuition.
  - now rewrite Fcomp, Gcomp.
  - now rewrite Fid, Gid.
Defined.
Next Obligation.
  intros F F0 E G G0 E0 A B f. simpl in *.
  destruct (E A B f). destruct (E0 (F A) (F B) g).
  apply hom_eqref. now rewrite H.
Defined.
Next Obligation.
  split; simpl in *; intuition; now apply hom_eqref.
Defined. 
            
