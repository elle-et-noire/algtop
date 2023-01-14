Generalizable All Variables.
Set Implicit Arguments.
Require Export setoid monoid group ZArith_base.

Declare Scope ring_scope.
Delimit Scope ring_scope with rng.
Open Scope setoid_scope.
Open Scope ring_scope.

Class Distributive {X : Setoid} (add mul : X -> X -> X) := {
  distl : forall a b c, mul a (add b c) == add (mul a b) (mul a c);
  distr : forall a b c, mul (add a b) c == add (mul a c) (mul b c)
}.

Class IsRing `(add : Binop R) (opp : Ope R) (z : R)
    (mul : Binop R) (e : R) := {
  add_grp :> IsGroup add opp z;
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
  idcr0 : crcar;
  mulcr : Binop crcar;
  idcr1 : crcar;

  cringprf :> IsCRing addcr oppcr idcr0 mulcr idcr1
}.

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

