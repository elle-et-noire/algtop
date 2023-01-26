Generalizable All Variables.
Set Implicit Arguments.
Unset Strict Implicit.
Require Export setoid monoid group.

Declare Scope ring_scope.
Delimit Scope ring_scope with rng.
Open Scope setoid_scope.
Open Scope group_scope.
Open Scope ring_scope.

Class Distributive {X : Setoid} (add mul : X -> X -> X) := {
  distl : forall a b c, mul a (add b c) == add (mul a b) (mul a c);
  distr : forall a b c, mul (add a b) c == add (mul a c) (mul b c)
}.

Class IsRing `(add : Binop R) (opp : Ope R) (z : R)
  (mul : Binop R) (e : R) (U : {ens R}) (inv : Ope U) :=
{
  add_grp :> IsGroup add opp z;
  mul_mnd :> IsMonoid mul e;
  add_comm :> Commute add;
  distR :> Distributive add mul;
  invlmg : forall x : U, mul x (inv x) == e;
  mg_max : forall x : R, (exists y : R, mul x y == e) -> U x
}.
#[global] Existing Instances add_grp add_comm distR.

Structure Ring := {
  rcarrier :> Setoid;
  addr : Binop rcarrier;
  oppr : Ope rcarrier;
  idr0 : rcarrier;
  mulr : Binop rcarrier;
  idr1 : rcarrier;
  unitsr : {ens rcarrier};
  invmgr : Ope unitsr;

  ringprf :> IsRing addr oppr idr0 mulr idr1 invmgr
}.
#[global] Existing Instance ringprf.

Class IsCRing `(add : Binop R) (opp : Ope R) (z : R)
    (mul : Binop R) (e : R) (U : {ens R}) (inv : Ope U) := {
  cring_ring :> IsRing add opp z mul e inv;
  cring_comm :> Commute mul
}.
#[global] Existing Instances cring_ring cring_comm.

Structure CRing := {
  crcar :> Setoid;
  addcr : Binop crcar;
  oppcr : Ope crcar;
  cr0 : crcar;
  mulcr : Binop crcar;
  cr1 : crcar;
  unitscr : {ens crcar};
  invmgcr : Ope unitscr;

  cringprf :> IsCRing addcr oppcr cr0 mulcr cr1 invmgcr
}.
#[global] Existing Instance cringprf.

Arguments addcr {_}.
Arguments oppcr {_}.
Arguments mulcr {_}.
Arguments cr0 {_}.
Arguments cr1 {_}.

Notation "[ A | +: add , -: opp , 0: idz , *: mul , 1: id ]" :=
  (@Build_CRing A add opp idz mul id)
  (at level 0, A, add, opp, idz, mul, id at level 99) : ring_scope.
Notation "(  * 'in' A  )" := (@mulcr A) : ring_scope.
Notation "( * )" := ( * in _ ) : ring_scope.
Notation "a * b 'in' A" := (@mulcr A a b)
  (at level 40, b at next level, left associativity)
  : ring_scope.
Notation "a * b" := (a * b in _) : ring_scope.
Notation "1 'in' A" := (@cr1 A)
  (at level 0, A at level 99, no associativity) : ring_scope.
Notation "1" := (1 in _) : ring_scope.
Notation "(  ! 'in' A  ) " := (@invmgcr A) : ring_scope.
Notation "( ! )" := ( ! in _ ) : ring_scope.
Notation "! a 'in' A" := (@invmgcr A a)
  (at level 35, a at level 35, right associativity,
  format "! a  'in'  A") : ring_scope.
Notation "! a" := ( ! a in _ )
  (at level 35, right associativity,
  format "! a") : ring_scope.
Notation "(  + 'in' A  )" := (@addcr A) : ring_scope.
Notation "( + )" := ( + in _ ) : ring_scope.
Notation "a + b 'in' A" := (@addcr A a b)
  (at level 50, b at next level, left associativity)
  : ring_scope.
Notation "a + b" := (a + b in _) : ring_scope.
Notation "0 'in' A" := (@cr0 A)
  (at level 0, A at level 99, no associativity) : ring_scope.
Notation "0" := (0 in _) : ring_scope.
Notation "(  - 'in' A  ) " := (@oppcr A) : ring_scope.
Notation "( - )" := ( - in _ ) : ring_scope.
Notation "- a 'in' A" := (@oppcr A a)
  (at level 35, a at level 35, right associativity,
  format "- a  'in'  A") : ring_scope.
Notation "- a" := ( - a in _ )
  (at level 35, right associativity,
  format "- a") : ring_scope.
Notation "A ^*" := (@unitscr A)
  (at level 30, no associativity, format "A ^*") : ring_scope.

Program Canonical Structure Mulgroup (X : CRing) :=
  [ unitscr X | *: (dmap x y => $[x * y, _]),
          !: invmgcr X,
          1: $[1, _]  ].
Next Obligation.
  apply mg_max. exists (!x * !y).
  now rewrite assoc, <-(assoc ($x)),
  (commute ($y)), assoc, invlmg, identl, invlmg.
Defined.
Next Obligation.
  intros x x0 E y y0 E0. simpeq_all. now rewrite E, E0.
Defined.
Next Obligation.
  apply mg_max. exists 1. now rewrite identl.
Defined.
Next Obligation.
  split; split.
  - intros x y z. simpeq. now rewrite assoc.
  - intros x. simpeq. now rewrite identr.
  - intros x. simpeq. apply invlmg.
Defined.
Notation "A ^<*>" := (@Mulgroup A)
  (at level 30, no associativity, format "A ^<*>") : ring_scope.

Notation "$[ 1 'in' A ]" := ($[1, @Mulgroup_obligation_3 A])
  (at level 0) : ring_scope.

Class IsMorph {A B : CRing} (f : Map A B) := {
  morph_mul : forall x y, f (x * y) == (f x) * (f y);
  morph_add : forall x y, f (x + y) == (f x) + (f y);
  morph_1 : f 1 == 1
}.

Structure Morph (A B : CRing) := {
  homfun :> Map A B;
  homprf : IsMorph homfun
}.
#[global] Existing Instance homprf.

Notation "'hom' 'on' f" := (@Build_Morph _ _ f _)
  (at level 200, no associativity) : ring_scope.
Notation "'hom' 'by' f " := (hom on (map by f))
  (at level 200, no associativity) : ring_scope.
Notation " 'hom' x => m " := (hom by fun x => m)
  (at level 200, x binder, no associativity) : ring_scope.
Notation "G ~~> H" := (@Morph G H)
  (at level 99, no associativity) : ring_scope.

Structure Isomorph (A B : CRing) := {
  isofun :> Morph A B;
  isoprf : Bijective isofun
}.
#[global] Existing Instance isoprf.

Notation "'iso' 'on' f" := (@Build_Isomorph _ _ f _)
  (at level 200, no associativity) : ring_scope.
Notation "'iso' x => m " := (iso on hom x => m)
  (at level 200, x binder, no associativity) : ring_scope.
Notation "G <~> H" := (@Isomorph G H)
  (at level 95, no associativity) : ring_scope.

Program Definition homcomp {A B C} (f : A ~~> B)
  (g : B ~~> C) : A ~~> C := hom on (g o f).
Next Obligation.
  split; try intros x y; simpl;
  try now rewrite 2!morph_mul || rewrite 2!morph_add.
  now rewrite !morph_1.
Defined.
Notation "g '<o~' f" := (homcomp f g)
  (at level 60, right associativity) : ring_scope.

Program Definition isocomp {A B C} (f : A <~> B)
  (g : B <~> C) : A <~> C := iso on (g <o~ f).
Next Obligation.
  split; split; simpl.
  - intros x y Heq. now repeat apply inj in Heq.
  - intros z. destruct (surj g z) as [y E1]. 
    destruct (surj f y) as [x E2]. exists x. now rewrite E1, E2.
Defined.
Notation "g '<o>' f" := (isocomp f g)
  (at level 60, right associativity) : ring_scope.

Section RingTheory.
  Context {A : CRing}.
  Implicit Types x y r : A.
  Lemma mulcrr r {x y} : x == y -> x * r == y * r.
  Proof. intros H. now rewrite H. Qed.

  Lemma mulcrI (r : A^*) {x y} : (x * r == y * r) == (x == y).
  Proof. 
    split; intros H; [rewrite <-identr, <-(identr y),
      <-!(invlmg r), !assoc|]; now rewrite H.
  Qed.

  Lemma unit1 : $$[1 in A] == 1.
  Proof. now simpl. Qed.

  Definition addG := Build_Group (add_grp(IsRing:=cring_ring(IsCRing:=cringprf A))).
  Lemma oppcr0 : -(0 in A) == 0.
  Proof. apply (@invg1 addG). Qed.

  Lemma addcr0 x : x + 0 == x.
  Proof. apply (@mulg1 addG). Qed. 
End RingTheory.


Program Definition rhom_mghom `(f : A ~~> B) : (A^<*> ~~> B^<*>)%grp
  := (hom x => $[f x, _])%grp.
Next Obligation.
  apply mg_max. exists (f (!x)).
  now rewrite <-morph_mul, invlmg, morph_1.
Defined.
Next Obligation.
  intros x x0 E. simpeq. now rewrite E.
Defined.
Next Obligation.
  split. intros x x0. simpeq. now rewrite morph_mul.
Defined.

Class IsIdeal {A : CRing} (I : {ens A}) := {
  ferm_add : forall x y : I, I (x + -y);
  ferm_0 : I 0;
  ferm_mul : forall (a : A) (x : I), I (a * x)
}.

Structure Ideal (A : CRing) := {
  suppi :> {ens A};
  idlprf :> IsIdeal suppi
}.
#[global] Existing Instance idlprf.

Notation "(< I >)" := (@Build_Ideal _ I _)
  (at level 200, I at level 0, no associativity) : ring_scope.
Notation "{ 'idl' X }" := (@Ideal X)
  (at level 0, format "{ 'idl'  X }") : ring_scope.

Program Definition nullIdeal {A : CRing} := (<[ == 0]>).
Next Obligation.
  split.
  - intros [x H] [y H1]. simpl in *.
    now rewrite H, H1, oppcr0, addcr0.
  - now simpl.
  - intros a [x H]. simpl in *. rewrite H.

Class IsField (A : CRing) := {
  fld : forall a : A, a == 0 \/ A^* a
}.

Structure Field := {
  fcar :> CRing;
  fldprf : IsField fcar
}.


