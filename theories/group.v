Generalizable All Variables.
Set Implicit Arguments.
Require Export setoid.

Declare Scope group_scope.
Open Scope setoid_scope.
Open Scope group_scope.

Definition Binop X := Binmap X X X.

Class Associative {X : Setoid} (op : X -> X -> X) := {
  assoc : forall x y z, op x (op y z) == op (op x y) z 
}.

Class LIdentical {X : Setoid} (op : X -> X -> X) e := {
  identl : forall x, op e x == x
}.

Class RIdentical {X : Setoid} (op : X -> X -> X) e := {
  identr : forall x, op x e == x
}.

Class Identical {X : Setoid} (op : X -> X -> X) e := {
  id_identl :> LIdentical op e;
  id_identr :> RIdentical op e
}.
#[global]
Existing Instances id_identl id_identr.

Class LInvertible {X : Setoid} (op : X -> X -> X) e (inv : X -> X) := {
  invl : forall x, op (inv x) x == e
}.

Class RInvertible {X : Setoid} (op : X -> X -> X) e (inv : X -> X) := {
  invr : forall x, op x (inv x) == e
}.

Class Invertible `{X : Setoid} (op : X -> X -> X) e (inv : X -> X) := {
  inv_invl :> LInvertible op e inv;
  inv_invr :> RInvertible op e inv
}.
#[global]
Existing Instances inv_invl inv_invr.

Class IsGroupS `(mul : Binop supp) (inv : Map supp supp) e :=
{
  assocg :> Associative mul;
  identrg :> RIdentical mul e;
  invrg :> RInvertible mul e inv
}.

Structure GroupS := {
  gcarrier :> Setoid;
  mulg : Binop gcarrier;
  invg : Map gcarrier gcarrier;
  idg : gcarrier;

  groupsprf :> IsGroupS mulg invg idg
}.
#[global]
Existing Instance groupsprf.

Arguments mulg {_}.
Arguments invg {_}.
Arguments idg {_}.

Notation "[ A | *: op , !: inv , 1: id ]" :=
  (@Build_GroupS A op inv id _)
  (at level 0, A, op, inv, id at level 99) : group_scope.
Notation "[ *: op , !: inv , 1: id ]" := [ _ | *: op, !: inv, 1: id]
  (at level 0, op, inv, id at level 99) : group_scope.
Notation "(  * 'in' G  )" := (@mulg G) : group_scope.
Notation "( * )" := ( * in _ ) : group_scope.
Notation "g * h 'in' G" := (@mulg G g h)
  (at level 40, h at next level, left associativity) : group_scope.
Notation "g * h" := (g * h in _) : group_scope.
Notation "1 'in' G" := (@idg G)
  (at level 0, G at level 99, no associativity) : group_scope.
Notation "1" := (1 in _) : group_scope.
Notation "(  ! 'in' G  ) " := (@invg G) : group_scope.
Notation "( ! )" := ( ! in _ ) : group_scope.
Notation "! g 'in' G" := (@invg G g)
  (at level 35, g at next level, right associativity) : group_scope.
Notation "! g" := ( ! g in _ )
  (at level 35, right associativity) : group_scope.

Definition conjg {G : GroupS} (g h : G) := !g * (h * g).
Notation "h ^ g" := (@conjg _ g h) : group_scope.

Lemma identlg {G} : LIdentical ( * in G ) 1.
Proof.
  split. intros x. rewrite <-identr. rewrite <-(invr (!x)) at 2.
  now rewrite assoc, <-(assoc 1), invr, identr,
    <-(invr x), <-assoc, invr, identr.
Qed.
#[global]
Existing Instance identlg.

Lemma invlg {G} : LInvertible ( * in G ) 1 ( ! ).
Proof.
  split. intros x. rewrite <-identr. rewrite <-(invr (!x)) at 1.
  now rewrite assoc, <-(assoc _ x), invr, identr, invr.
Qed.
#[global]
Existing Instance invlg.

Section GroupTheory.
  Context {G : GroupS}.
  Implicit Types x y g : G.
  Lemma mulgA : forall {x y z}, x * (y * z) == (x * y) * z.
  Proof. now destruct G as [a b c d [[e] f g]]. Qed.

  Lemma mulg1 : forall {x}, x * 1 == x.
  Proof. now destruct G as [a b c d [e [f] g]]. Qed.

  Lemma mulgV : forall {x}, x * !x == 1.
  Proof. now destruct G as [a b c d [e f [g]]]. Qed.

  Lemma mul1g : forall {x}, 1 * x == x.
  Proof. now destruct (@identlg G). Qed.

  Lemma mulVg : forall {x}, !x * x == 1.
  Proof. now destruct (@invlg G). Qed.

  Lemma mulgI {g x y} : x * g == y * g -> x == y.
  Proof.
    intros H. 
    now rewrite <-identr, <-(identr y), <-(invr g), 2!assoc, H.
  Qed.

  Lemma mulIg {g x y} : g * x == g * y -> x == y.
  Proof.
    intros H.
    now rewrite <-identl, <-(identl y), <-(invl g), <-2!assoc, H.
  Qed.
  
  Lemma mulTg {g x y} : g * x == y -> x == !g * y.
  Proof.
    intros H. apply (@mulIg g). now rewrite assoc, invr, identl.
  Qed.

  Lemma mulgT {g x y} : x * g == y -> x == y * !g.
  Proof.
    intros H. apply (@mulgI g). now rewrite <-assoc, invl, identr.
  Qed.

  Lemma invgK {x} : !!x == x.
  Proof. apply (@mulgI (!x)). now rewrite invl, invr. Qed.

  Lemma eq_invg_sym {x y} : !x == y -> x == !y.
  Proof. intros H. now rewrite <-H, invgK. Qed.
 
  Lemma invMg {x y} : !(x * y) == !y * !x.
  Proof.
    rewrite <-(identr (!x)). apply mulTg, mulTg.
    now rewrite assoc, invr.
  Qed.

  Lemma invg1 : !(1 in G) == 1.
  Proof.
    rewrite <-(identr (!1)). symmetry; apply mulTg, identl.
  Qed.
End GroupTheory.

Class IsHomomorph {G H : GroupS} (f : Map G H) := {
  morph : forall x y, f (x * y) == (f x) * (f y) in H
}.

Structure Homomorph (G H : GroupS) := {
  homfun :> Map G H;
  homprf :> IsHomomorph homfun
}.
#[global]
Existing Instance homprf.

Notation "'hom' 'on' f" := (@Build_Homomorph _ _ f _)
  (at level 200, no associativity).
Notation "'hom' 'by' f " := (hom on (map by f))
  (at level 200, no associativity).
Notation " 'hom' x => m " := (hom by fun x => m)
  (at level 200, x binder, no associativity) : group_scope.
Notation "G ~~> H" := (@Homomorph G H)
  (at level 99, no associativity) : group_scope.

Structure Isomorph (G H : GroupS) := {
  isofun :> Homomorph G H;
  isoprf :> Bijective isofun
}.
#[global]
Existing Instance isoprf.

Notation "'iso' 'on' f" := (@Build_Isomorph _ _ f _)
  (at level 200, no associativity) : group_scope.
Notation "'iso' x => m " := (iso on hom x => m)
  (at level 200, x binder, no associativity) : group_scope.
Notation "G <~> H" := (@Isomorph G H)
  (at level 95, no associativity) : group_scope.

Program Definition homcomp {G1 G2 G3} (f: G1 ~~> G2) (g: G2 ~~> G3)
  : G1 ~~> G3 := hom on (g o f).
Next Obligation. split. intros x y. simpl. now rewrite 2!morph. Defined.
Notation "g '<o~' f" := (homcomp f g)
  (at level 60, right associativity) : group_scope.

Program Definition isocomp {G1 G2 G3} (f: G1 <~> G2) (g: G2 <~> G3)
  : G1 <~> G3 := iso on (g <o~ f).
Next Obligation.
  split; split; simpl.
  - intros x y Heq. now apply inj, inj in Heq.
  - intros z. destruct (surj g z) as [y E1]. 
    destruct (surj f y) as [x E2]. exists x. now rewrite E1, E2.
Defined.
Notation "g '<o>' f" := (isocomp f g)
  (at level 60, right associativity) : group_scope.

Section HomTheory.
  Context `{f: Homomorph G H}.
  Lemma morph1 : f 1 == 1.
  Proof.
    apply (mulgI (g := f 1)). now rewrite <-morph, 2!identl.
  Qed.

  Lemma morphV : forall x, f (!x) == !(f x).
  Proof.
    intros x. rewrite <-(identr (!(f x))).
    apply mulTg. now rewrite <-morph, invr, morph1.
  Qed.
End HomTheory.

Lemma ensmul_assoc {G : GroupS} : Associative (imens2 ( * in G )).
Proof.
  split. intros A B C. split; intros [g1 [a [g2 [H [H1 H2]]]]]; simpl.
  + destruct H1 as [b [c [Bb [Cc E1]]]]. exists (a * b), c. split;
    (exists a, b || rewrite <-assoc, <- E1); intuition.
  + destruct H as [a0 [b [Aa0 [Bb E]]]]. exists a0, (b * g2).
    intuition; (exists b, g2 || rewrite assoc, <-E); intuition.
Qed.

Lemma ensmulg1 {G : GroupS} : RIdentical (imens2 ( * in G )) [ens 1].
Proof.
  split. intros A. split.
  + intros [a [a0 [i [Aa [I E]]]]]. simpl. now rewrite E, I, identr.
  + intros [a Aa]. exists a, 1. simpl. intuition. now rewrite identr.
Qed.


Class IsGroup {X : GroupS} (G : Ensemble X) := {
  fermM : forall {x y : G}, G (x * y);  
  fermV : forall {x : G}, G (!x);
  ferm1 : G 1
}.

Structure Group (X : GroupS) := {
  suppg :> Ensemble X;
  groupprf :> IsGroup suppg
}.
#[global]
Existing Instance groupprf.

Notation "<[  x  :  A  |  P  ]" := (@Build_Group A (map x => P))
  (x at level 99).
Notation "[  x  |  P  ]" := [x : _ | P]
  (x at level 99).


Close Scope group_scope.
Close Scope setoid_scope.