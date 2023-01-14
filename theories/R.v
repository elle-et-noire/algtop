Generalizable All Variables.
Set Implicit Arguments.
Require Export setoid ring ZArith.

Declare Scope real_scope.
Delimit Scope real_scope with R.
Open Scope setoid_scope.
Open Scope ring_scope.
Open Scope real_scope.
Open Scope Z_scope.

Definition comparison_eq a b :=
  match a, b with
  | Eq, Eq => True
  | Lt, Lt => True
  | Gt, Gt => True
  | _, _ => False
  end.
#[global] Hint Unfold comparison_eq : eq.
Program Canonical Structure comparisonS :=
  [ ==: comparison_eq ].
Next Obligation.
  split; intros x; case x; try (intros y; case y);
  simpl; intuition.
Defined.

Class IsR (Rt : Field) (comp : Dymap Rt Rt comparison)
          (up : Rt -> Z) (IZR : Z -> Rt) :=
{
  Rlt_asym : forall a b : Rt, (comp a b == Lt) == (comp b a == Gt);
  Rlt_trans : Transitive (fun a b => comp a b == Lt);
  Radd_lt_compat : forall a b c : Rt, (comp b c == Lt) -> (comp (a + b) (a + c) == Lt);
  Rmul_lt_compat : forall (a : fucar Rt) (b c : Rt), (comp b c == Lt) -> (comp (a * b) (a * c) == Lt);
  archimed : forall a : Rt, IZR (up r) /\ IZR (up r) - r <= 1;
  complete : forall E : {ens Rt}, 
}.

Structure R := {
  rcar :> Field;
  compr : Dymap rcar rcar comparison;
  Rup : rcar -> Z

}.




Notation "$ x" := (proj1_sig x)
  (at level 35, right associativity, format "$ x") : real_scope.

Class IsR (Rt : Set) (R0 R1 : Rt) (Req Rlt : Rt -> Rt -> Prop)
          (Rplus Rmult : Rt -> Rt -> Rt) (Ropp : Rt -> Rt)
          (Rinv : {r : Rt | Rlt R0 r} -> {r : Rt | Rlt R0 r})
          (Rup : Rt -> Z) :=
{
  Req_equiv :> Equivalence Req;
  Rplus_comm : forall a b, Req (Rplus a b) (Rplus b a);
  Rplus_assoc : forall a b c, Req (Rplus a (Rplus b c)) (Rplus (Rplus a b) c);
  Rplus_opp_r : forall a, Req (Rplus a (Ropp a)) R0;
  Rplus_0_l : forall a, Req (Rplus R0 a) a;
  Rmult_comm : forall a b, Req (Rmult a b) (Rmult b a);
  Rmult_assoc : forall a b c, Req (Rmult a (Rmult b c)) (Rmult (Rmult a b) c);
  Rinv_l : forall a, Req (Rmult ($(Rinv a)) ($a)) R1;
  Rmult_1_l : forall a, Req (Rmult R1 a) a;
  mulRDr : forall a b c, Req (Rmult a (Rplus b c)) (Rplus (Rmult a b) (Rmult a c));

  Rtotord : forall a b, Rlt a b \/ Req a b \/ Rlt b a;
  Rlt_asym : forall a b, Rlt a b -> ~ Rlt b a; 
  Rlt_trans :> Transitive Rlt;
  Rplus_lt_compat_l : forall a b c, Rlt b c -> Rlt (Rplus a b) (Rplus a c);
  Rmult_lt_compat_l : forall a b c, Rlt a R0 -> Rlt b c -> Rlt (Rmult a b) (Rmult a c)

  archimed : 
}.



Structure R : Set := {
  Rcarrier :> Set;
  R0 : Rcarrier;
  R1 : Rcarrier;
  Req : Rcarrier -> Rcarrier -> Prop;
  Rlt : Rcarrier -> Rcarrier -> Prop;
  Rplus : Rcarrier -> Rcarrier -> Rcarrier;
  Rmult : Rcarrier -> Rcarrier -> Rcarrier;
  Ropp : Rcarrier -> Rcarrier;
  Rinv : {r : Rcarrier | Rlt R0 r} -> Rcarrier;
  Rup : Rcarrier -> Z
}.


(* RをInductiveに定義すると、四則演算で作れる数しか
   実数として認めないことになる *)
Inductive Runit : Set :=
| R1 : Runit
| Rinv : Runit -> Runit
| Rmulu : Runit -> Runit -> Runit
| 
.

Inductive R : Set :=
| R

Inductive R : Set :=
| R0 : R
| R1 : R
| Rplus : R -> R -> R
| Rmult : R -> R -> R
| Ropp : R -> R
| Rinv : {r : R | Rlt R0 r} -> R
with Rlt : R -> R -> Prop :=
| Rlt_trans : forall a b c, R_lt a b -> R_lt b c -> R_lt a c
| Rplus_lt_compat_l : forall a b c, R_lt b c -> R_lt (a + b) (a + c)
| Rmult_lt_compat_l : forall a b c, R_lt a R0 -> R_lt b c -> R_lt (a * b) (a * c)
.

Notation "a + b" := (Rplus a b) : real_scope.
Notation "a * b" := (Rmult a b) : real_scope.
Notation "- r" := (Ropp r) : real_scope.
Notation "/ r" := (Rinv r) : real_scope.

Inductive R_eq : R -> R -> Prop :=
| R_eq_refl : forall a, R_eq a a
| R_eq_sym : forall a b, R_eq a b -> R_eq b a
| R_eq_trans : forall a b c, R_eq a b -> R_eq b c -> R_eq a c
| Rplus_comm : forall a b, R_eq (a + b) (b + a)
| Rplus_assoc : forall a b c, R_eq (a + (b + c)) (a + b + c)
| Rplus_opp_r : forall a, R_eq (a + -a) R0
| Rplus_0_l : forall a, R_eq (R0 + a) a
| Rmult_comm : forall a b, R_eq (a * b) (b * a)
| Rmult_assoc : forall a b c, R_eq (a * (b * c)) (a * b * c)
| Rmult_1_l : forall a, R_eq (R1 * a) a
| mulRDr : forall a b c, R_eq (a * (b + c)) (a * b + a * c)
.



Inductive R_lt : R -> R -> Prop :=
(* | totord : forall a b, R_lt b a \/ R_eq a b \/ R_lt a b *)
(* | Rlt_asym : forall a b, (~ R_lt b a) -> R_lt a b *)
| Rlt_trans : forall a b c, R_lt a b -> R_lt b c -> R_lt a c
| Rplus_lt_compat_l : forall a b c, R_lt b c -> R_lt (a + b) (a + c)
| Rmult_lt_compat_l : forall a b c, R_lt a R0 -> R_lt b c -> R_lt (a * b) (a * c)
.