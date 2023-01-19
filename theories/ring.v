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
    (mul : Binop R) (e : R) := {
  add_grp :> IsGroup add opp z;
  mul_mnd :> IsMonoid mul e;
  add_comm :> Commute add;
  distR :> Distributive add mul
}.
#[global] Existing Instances add_grp add_comm distR.

Structure Ring := {
  rcarrier :> Setoid;
  addr : Binop rcarrier;
  oppr : Ope rcarrier;
  idr0 : rcarrier;
  mulr : Binop rcarrier;
  idr1 : rcarrier;

  ringprf :> IsRing addr oppr idr1 mulr idr0
}.
#[global] Existing Instance ringprf.

Class IsCRing `(add : Binop R) (opp : Ope R) (z : R)
    (mul : Binop R) (e : R) := {
  cring_ring :> IsRing add opp z mul e;
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

  cringprf :> IsCRing addcr oppcr cr0 mulcr cr1
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
  (at level 35, a at next level, right associativity,
  format "- a  'in'  A") : ring_scope.
Notation "- a" := ( - a in _ )
  (at level 35, right associativity,
  format "- a") : ring_scope.

Class IsUnitsens {X : CRing} (A : {ens X}) (inv : Ope A) := {
  invlmg : forall x : A, x * (inv x) == 1;
  mg_max : forall x : X, (exists y : X, x * y == 1) -> A x
}.

Structure Unitsens (A : CRing) := {
  suppmg :> {ens A};
  invmg : Ope suppmg;

  mgprf :> IsUnitsens invmg
}.

Notation "A ^*" := (@Unitsens A)
  (at level 30, no associativity, format "A ^*") : ring_scope.

Program Canonical Structure Mulgroup `(U : A^*) :=
  [ suppmg U | *: (dmap (x : suppmg U) y => $[x * y, _]),
          !: invmg U,
          1: $[1, _]  ].
Next Obligation.
  destruct U. simpl in *. apply mg_max.
  exists (invmg0 x * invmg0 y). now rewrite assoc, <-(assoc ($x)),
  (commute ($y)), assoc, invlmg, identl, invlmg.
Defined.
Next Obligation.
  intros x x0 E y y0 E0. simpeq_all. now rewrite E, E0.
Defined.
Next Obligation.
  destruct U. apply mg_max. exists 1. now rewrite identl.
Defined.
Next Obligation.
  split; split.
  - intros x y z. simpeq. now rewrite assoc.
  - intros x. simpeq. now rewrite identr.
  - intros x. destruct U. simpeq. apply invlmg.
Defined.

Notation "A ^<*>" := (@Mulgroup A)
  (at level 30, no associativity, format "A ^<*>") : ring_scope.

Class IsMorph {A B : CRing} (f : Map A B) := {
  morph_mul : forall x y, f (x * y) == (f x) * (f y);
  morph_add : forall x y, f (x + y) == (f x) + (f y)
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
  split; intros x y; simpl;
  now rewrite 2!morph_mul || rewrite 2!morph_add.
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

Program Definition rhom_mghom `(f : A ~~> B) : (A^<*> ~~> B^<*>)%grp
  := (hom x => f x).




Close Scope ring_scope.
Declare Scope field_scope.
Open Scope field_scope.

Inductive FieldBase {U : Setoid} :=
| funit :> U -> FieldBase
| f0 : FieldBase.
Notation "{ 'fldb' U }" := (@FieldBase U)
  (at level 0, format "{ 'fldb'  U }") : field_scope.

Definition fieldb_eq {U} (a b : {fldb U}) :=
  match a, b with
  | funit a', funit b' => a' == b'
  | f0, f0 => True
  | _, _ => False
  end.
Program Canonical Structure FieldBaseSetoid
  {U : Setoid} := [ {fldb U} | ==: fieldb_eq ].
Next Obligation.
  split.
  - intros a. case a; now simpl.
  - intros a b E. case a, b; now simpl.
  - intros a b c E E0. case a, b, c; simpl in *; intuition.
    now rewrite E.
Defined.
Notation "[ 'fldb' U ]" := (@FieldBaseSetoid U)
  (at level 0, format "[ 'fldb'  U ]") : field_scope.
Program Canonical Structure funitM {U} : Map U [fldb U]
  := map x => funit x.

Program Definition inclmul {U} (mul : Binop U) : Binop [fldb U]
  := dmap a b => match a, b with
      | funit a', funit b' => (funitM o< mul) a' b'
      | _, _ => f0
      end.
Next Obligation.
  intros a a0 E b b0 E0. case a, a0, b, b0; intuition.
  simpl in *. now rewrite E, E0.
Defined.

Class IsField `(mul : Binop U) (inv : Ope U) (f1 : U)
  (add : Binop [fldb U]) (opp : Ope [fldb U]) := {
  fld_cring :> IsCRing add opp f0 (inclmul mul) f1;
  fldU_grp :> IsGroup mul inv f1
}.
#[global] Existing Instances fld_cring fldU_grp.

Structure Field := {
  fucar : Setoid;
  mulu : Binop fucar;
  invu : Ope fucar;
  f1 : fucar;
  addf : Binop {fldb fucar};
  oppf : Ope {fldb fucar};

  fldprf : IsField mulu invu f1 addf oppf
}.
#[global] Existing Instance fldprf.

Coercion fld_setoid F := [fldb (fucar F)].

