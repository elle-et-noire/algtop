Generalizable All Variables.
Set Implicit Arguments.
Require Export setoid.

Declare Scope group_scope.
Open Scope setoid_scope.
Open Scope group_scope.

Structure Bincarto (X Y Z : Setoid) := {
  bincfun :> X -> Y -> Z;
  bincproper :> Proper ((==) ==> (==) ==> (==)) bincfun
}.
#[global]
Existing Instance bincproper.

Structure Binop `(A : Ensemble X) := {
  binopfun :> Bincarto A A A
}.

Class Associative `{A : Ensemble X} (op : Binop A) := {
  assoc : forall x y z : A, op x (op y z) == op (op x y) z 
}.

Class LIdentical `{A : Ensemble X} (op : Binop A) e := {
  identl : forall x : A, op e x == x
}.

Class RIdentical `{A : Ensemble X} (op : Binop A) e := {
  identr : forall x : A, op x e == x
}.

Class Identical `{A : Ensemble X} (op : Binop A) e := {
  id_identl :> LIdentical op e;
  id_identr :> RIdentical op e
}.
#[global]
Existing Instances id_identl id_identr.

Class LInvertible `{A : Ensemble X} (op : Binop A) e (inv : Map A A) := {
  invl : forall x : A, op (inv x) x == e
}.

Class RInvertible `{A : Ensemble X} (op : Binop A) e (inv : Map A A) := {
  invr : forall x : A, op x (inv x) == e
}.

Class Invertible `{A : Ensemble X} (op : Binop A) e (inv : Map A A) := {
  inv_invl :> LInvertible op e inv;
  inv_invr :> RInvertible op e inv
}.
#[global]
Existing Instances inv_invl inv_invr.

Class IsGroup `{supp : Ensemble X} (mul : Binop supp) 
              (inv : Map supp supp) e :=
{
  assocg :> Associative mul;
  identrg :> RIdentical mul e;
  invrg :> RInvertible mul e inv
}.

Structure Group X := {
  suppg :> Ensemble X;
  mulg : Binop suppg;
  invg : Map suppg suppg;
  idg : suppg;

  groupprf :> IsGroup mulg invg idg
}.
#[global]
Existing Instance groupprf.

Arguments mulg {_} {_}.
Arguments invg {_} {_}.
Arguments idg {_} {_}.

Notation "[ A | *: op , !: inv , 1: id ]" :=
  (@Build_Group _ A op inv id _)
  (at level 0, A, op, inv, id at level 99) : group_scope.
Notation "[ *: op , !: inv , 1: id ]" := [ _ | *: op, !: inv, 1: id]
  (at level 0, op, inv, id at level 99) : group_scope.
Notation "(  * 'in' G  )" := (@mulg _ G) : group_scope.
Notation "( * )" := ( * in _ ) : group_scope.
Notation "g * h 'in' G" := (@mulg _ G g h)
  (at level 40, h at next level, left associativity) : group_scope.
Notation "g * h" := (g * h in _) : group_scope.
Notation "1 'in' G" := (@idg _ G)
  (at level 0, G at level 99, no associativity) : group_scope.
Notation "1" := (1 in _) : group_scope.
Notation "(  ! 'in' G  ) " := (@invg _ G) : group_scope.
Notation "( ! )" := ( ! in _ ) : group_scope.
Notation "! g 'in' G" := (@invg _ G g)
  (at level 35, g at next level, right associativity) : group_scope.
Notation "! g" := ( ! g in _ )
  (at level 35, right associativity) : group_scope.

Lemma identlg `{G : Group X} : LIdentical ( * in G ) 1.
Proof.
  split. intros x. rewrite <-identr. rewrite <-(invr (!x)) at 2.
  now rewrite assoc, <-(assoc 1), invr, identr,
    <-(invr x), <-assoc, invr, identr.
Qed.
#[global]
Existing Instance identlg.

Lemma invlg `{G : Group X} : LInvertible ( * in G ) 1 ( ! ).
Proof.
  split. intros x. rewrite <-identr. rewrite <-(invr (!x)) at 1.
  now rewrite assoc, <-(assoc _ x), invr, identr, invr.
Qed.
#[global]
Existing Instance invlg.

Section GroupTheory.
  Context `{G : Group X}.
  Implicit Types x y g : G.
  Lemma mulgA : forall {x y z}, x * (y * z) == (x * y) * z.
  Proof. now destruct G as [a b c d [[e] f g]]. Qed.

  Lemma mulg1 : forall {x}, x * 1 == x.
  Proof. now destruct G as [a b c d [e [f] g]]. Qed.

  Lemma mulgV : forall {x}, x * !x == 1.
  Proof. now destruct G as [a b c d [e f [g]]]. Qed.

  Lemma mul1g : forall {x}, 1 * x == x.
  Proof. now destruct (@identlg _ G). Qed.

  Lemma mulVg : forall {x}, !x * x == 1.
  Proof. now destruct (@invlg _ G). Qed.

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

Class IsHomomorph {X Y} {G : Group X} {H : Group Y} (f : Map G H) := {
  morph : forall x y : G, f (x * y) == (f x) * (f y) in H
}.

Structure Homomorph {X Y} (G : Group X) (H : Group Y) := {
  homfun :> Map G H;
  homprf :> IsHomomorph homfun
}.
#[global]
Existing Instance homprf.

Notation "'hom' 'on' f" := (@Build_Homomorph _ _ _ _ f _)
  (at level 200, no associativity).
Notation "'hom' 'by' f " := (hom on (map by f))
  (at level 200, no associativity).
Notation " 'hom' x => m " := (hom by fun x => m)
  (at level 200, x binder, no associativity) : group_scope.
Notation "G ~~> H" := (@Homomorph _ _ G H)
  (at level 99, no associativity) : group_scope.

Structure Isomorph {X Y} (G : Group X) (H : Group Y) := {
  isofun :> Homomorph G H;
  isoprf :> Bijective isofun
}.
#[global]
Existing Instance isoprf.

Notation "'iso' 'on' f" := (@Build_Isomorph _ _ _ _ f _)
  (at level 200, no associativity) : group_scope.
Notation "'iso' x => m " := (iso on hom x => m)
  (at level 200, x binder, no associativity) : group_scope.
Notation "G <~> H" := (@Isomorph _ _ G H)
  (at level 95, no associativity) : group_scope.

Program Definition homcomp {X Y Z} {G1 : Group X} {G2 : Group Y}
  {G3 : Group Z} (f: G1 ~~> G2) (g: G2 ~~> G3) : G1 ~~> G3
  := hom on (g o f).
Next Obligation. split. intros x y. simpl. now rewrite 2!morph. Defined.
Notation "g '<o~' f" := (homcomp f g)
  (at level 60, right associativity) : group_scope.

Program Definition isocomp {X Y Z} {G1 : Group X} {G2 : Group Y}
  {G3 : Group Z} (f: G1 <~> G2) (g: G2 <~> G3) : G1 <~> G3
  := iso on (g <o~ f).
Next Obligation.
  split; split; simpl.
  - intros x y Heq. now apply inj, inj, inj in Heq.
  - intros z. destruct (surj g z) as [y E1]. 
    destruct (surj f y) as [x E2]. exists x. now rewrite E1, E2.
Defined.
Notation "g '<o>' f" := (isocomp f g)
  (at level 60, right associativity) : group_scope.

Section HomTheory.
  Context {X Y} {G : Group X} {H : Group Y} {f: Homomorph G H}.
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

Class IsSubgof {X : Setoid} (G H : Group X) := {
  subsupp :> H <= G;
  fermM : forall {x y : G}, H x -> H y -> H (x * y);  
  fermV : forall {x : G}, H x -> H (!x);
  ferm1: H (1 in G)
}.

Notation "H '<~' G" := (IsSubgof G H)
  (at level 70, no associativity) : group_scope.

Definition conjg `{G : Group X} (g h : G) := g * h * !g.
Notation "h ^ g" := (@conjg _ _ g h) : group_scope.

Class IsNormalSubgroup {X} (G H : Group X) := {
  normal : forall {g h : G}, H h -> H (h ^ g)
}.



Close Scope group_scope.
Close Scope setoid_scope.