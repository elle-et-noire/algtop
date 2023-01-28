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

Notation "p .1" := (fst p) (at level 5, left associativity, format "p .1").
Notation "p .2" := (snd p) (at level 5, left associativity, format "p .2").

Lemma trans {X : Setoid} {a b c : X} : a == b -> b == c -> a == c.
Proof. intros H H0. now rewrite H. Defined.
Lemma mapimeq {X Y : Setoid} {m m0 : Map X Y} {a a0 b b0}
  : m a == m0 b -> a == a0 -> b == b0 -> m a0 == m0 b0.
Proof.
  intros E E0 E1. now rewrite <-E0, <-E1.
Defined.

Program Definition composables {X Y : Setoid} (Cod Dom : Map X Y) :=
  [ p | Cod (fst p) == Dom (snd p) ].
Next Obligation.
  intros [x y] [x0 y0] [E E0]. split; intros H; simpl in *;
  now rewrite2 E; rewrite2 E0.
Defined.

Class IsCategory (obj hom : Setoid) (dom cod : Map hom obj)
  (comp : Map (composables cod dom) hom) (id : obj -> hom) :=
{
  comp_dom : forall p, dom (comp p) == dom ($p).1;
  comp_cod : forall p, cod (comp p) == cod ($p).2;
  compcA : forall p p0 (H : ($p).2 == ($p0).1) H0 H1,
    comp $[(($p).1, comp p0), H0] == comp $[(comp p, ($p0).2), H1];
  id_dom : forall A, dom (id A) == A;
  id_cod : forall A, cod (id A) == A;
  compc1 : forall f H, comp $[(id (dom f), f), H] == f;
  comp1c : forall f H, comp $[(f, (id (cod f))), H] == f;
}.

Structure Category := {
  catobj :> Setoid;
  cathom : Setoid;
  dom : Map cathom catobj;
  cod : Map cathom catobj;
  catcomp : Map (composables cod dom) cathom;
  catid : Map catobj cathom;

  catprf :> IsCategory catcomp catid
}.
#[global] Existing Instance catprf.

Arguments dom {_}.
Arguments cod {_}.

Notation "[ 'dom:' dom , 'cod:' cod , 'o:' comp , '1:' id ]"
  := (@Build_Category _ _ dom cod comp id _)
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

Lemma map_equal {X Y : Setoid} (f : Map X Y) x x0
  : x == x0 -> f x == f x0.
Proof. intros H. now rewrite H. Defined.

Program Definition catcompDC {X : Category} {A B C : X}
  : Dymap (A ~> B) (B ~> C) (A ~> C)
  := dmap f g => $[@catcomp _ $[($f, $g), _], _].
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
  simpeq_all. apply map_equal. split; now simpl.
Defined.

Lemma CDeq_pair {X : Category} {f g : cathom X}
  : cod f == dom g -> cod (f, g).1 == dom (f, g).2.
Proof. intuition. Defined.

Notation "g o[ 'by' H ] f" := (@catcomp _ $[(f, g), H])
  (at level 60, right associativity, format "g  o[ 'by'  H ]  f")
  : cat_scope.
Notation "g 'o' f" := (@catcompDC _ _ _ _ f g)
  (at level 60, right associativity) : cat_scope.


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
     o: map p => ($p).1 o[by _] ($p).2, 1: catid X ].
Next Obligation.
  destruct p as [[f g] H]. simpl in *. now symmetry.
Defined.
Next Obligation.
  intros [[f g] H] [[f0 g0] H0] [E E0]. simpeq_all.
  apply map_equal. split; now simpl.
Defined.
Next Obligation.
  split; intuition; simpl.
  - apply comp_cod.
  - apply comp_dom.
  - pose ( (compcA(IsCategory:=X))). simpl in e.
    destruct p as [[h g] Hp]. destruct p0 as [[g0 f] Hp0].
    simpl in *. pose (g, h) as p.
    assert (ensconf (composables cod dom) p) as H2 by now simpl.
    pose (f, g) as p0.
    assert (ensconf (composables cod dom) p0) as H3.
    { simpl. rewrite <-Hp0. now apply map_equal. }
    pose (@e $[p0, H3] $[p, H2]).
    unfold p, p0 in e0. simpl in e0.
    assert (g == g) by reflexivity. pose (e0 H4).
    assert (cod f == dom (h o[by H2] g)).
    { now rewrite comp_dom. }
    assert (cod (g o[by H3] f) == dom h).
    { now rewrite comp_cod. }
    pose (e1 H5 H6). rewrite ccompeq. rewrite e2.
    apply map_equal. split; try now simpl.
    apply map_equal. split; now simpl.
  - apply id_cod.
  - apply id_dom.
  - apply comp1c.
  - apply compc1.
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

