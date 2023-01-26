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

Check transitive.
Check transitivity.

Lemma trans {X : Setoid} {a b c : X} : a == b -> b == c -> a == c.
Proof. intros H H0. now rewrite H. Defined.
Lemma mapimeq {X Y : Setoid} {m m0 : Map X Y} {a a0 b b0}
  : m a == m0 b -> a == a0 -> b == b0 -> m a0 == m0 b0.
Proof.
  intros E E0 E1. now rewrite <-E0, <-E1.
Defined.

Class IsCategory (obj hom : Setoid) (dom codom : Map hom obj)
  (comp : forall {f g}, codom f == dom g -> hom) (id : obj -> hom) :=
{
  comp_dom : forall f g (H : codom f == dom g), dom (comp H) == dom f;
  comp_cod : forall f g (H : codom f == dom g), codom (comp H) == codom g;
  comp_map : forall f f0 g g0 (E : f == f0) (E0 : g == g0) (H : codom f == dom g),
    comp H == comp (mapimeq H E E0);
  compcA : forall f g h (H : codom f == dom g) (H0 : codom g == dom h),
    @comp f (comp H0) (trans H ((proj1 sym)(comp_dom H0)))
    == @comp (comp H) h (trans (comp_cod H) H0);
  id_dom : forall A, dom (id A) == A;
  id_cod : forall A, codom (id A) == A;
  compc1 : forall f, comp (id_cod (dom f)) == f;
  comp1c : forall f, comp ((proj1 sym) (id_dom (codom f))) == f;
}.

Structure Category := {
  catobj :> Setoid;
  cathom : Setoid;
  dom : Map cathom catobj;
  cod : Map cathom catobj;
  catcomp : forall f g, cod f == dom g -> cathom;
  catid : Map catobj cathom;

  catprf :> IsCategory catcomp catid
}.
#[global] Existing Instance catprf.

Arguments dom {_}.
Arguments cod {_}.

Notation "[ 'o:' comp , '1:' id ]"
  := (@Build_Category _ _ _ _ comp id _)
  (at level 0, comp, id at level 99) : cat_scope.
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

Obligation Tactic := (try now intros x); intros; (try apply \ISE).

Program Definition catcompDC {X : Category} {A B C : X}
  : Dymap (A ~> B) (B ~> C) (A ~> C)
  := dmap f g => $[@catcomp _ ($f) ($g) _, _].
Next Obligation.
  destruct f as [f [Df Cf]]. destruct g as [g [Dg Cg]].
  simpl in *. now rewrite Dg.
Defined.
Next Obligation.
  destruct f as [f [Df Cf]]. destruct g as [g [Dg Cg]].
  split; simpl.
  - now rewrite comp_dom.
  - now rewrite comp_cod.
Defined.
Next Obligation.
  intros [f [Df Cf]] [f0 [Df0 Cf0]] E [g [Dg Cg]] [g0 [Dg0 Cg0]] E0.
  assert (cod f == dom g) by now rewrite Dg.
  (* pose (comp_map E E0 H). *)
  (* rewrite comp_map. *)
  simpeq_all.
  Check (trans_sym_co_inv_impl_morphism (Equivalence_PER (equal_equiv X)) 
  (dom g) B Dg Cf).
  Check (trans_sym_co_inv_impl_morphism (Equivalence_PER (equal_equiv X)) 
  (dom g0) B Dg0 Cf0).

  assert (catcomp (trans_sym_co_inv_impl_morphism (Equivalence_PER (equal_equiv X)) 
  (dom g) B Dg Cf) == catcomp H).
  
  simpl in *. simpeq_all. 
  pose (comp_map E E0 H). simpl.  unfold mapimeq in e.
  simpl in e. mapimeq  rewrite E.



Notation "g 'o' f" := (@catcomp _ _ _ _ f g)
  (at level 60, right associativity) : cat_scope.

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

Program Canonical Structure CatCat :=
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

Canonical Structure FunctorSetoid X Y := Eval simpl in (@cathom CatCat X Y).
Notation "[ 'Fun' X Y ]" := (@FunctorSetoid X Y) : cat_scope.

