Generalizable All Variables.
Set Implicit Arguments.

Require Export Coq.Program.Basics Coq.Program.Tactics
  Coq.Setoids.Setoid Coq.Classes.Morphisms.

Declare Scope setoid_scope.
Open Scope setoid_scope.

Structure Setoid : Type := {
  scarrier :> Type;
  equal : relation scarrier;
  equal_equiv :> Equivalence equal
}.
#[global]
Existing Instance equal_equiv.

Notation "[  A  |  ==:  P  ]" := (@Build_Setoid A P _)
  (at level 0, A, P at level 99).
Notation "[  ==:  P  ]" := [_ | ==: P]
  (at level 0, P at level 99).

Notation "( == 'in' A )" := (equal A)
  (at level 0, format "( == 'in' A )").
Notation "(==)" := (== in _).
Notation "x == y 'in' A" := (equal A x y)
  (at level 70, y at next level, no associativity).
Notation "x == y" := (x == y in _)
  (at level 70, no associativity) : setoid_scope.

Program Definition PropSetoid := [ ==: iff ].
Canonical Structure PropSetoid.

Structure Carto (X Y : Setoid) : Type := {
  cartofun :> X -> Y;
  cartoprf :> Proper ((==) ==> (==)) cartofun
}.
#[global]
Existing Instance cartoprf.

Notation "'carto' 'by' f" := (@Build_Carto _ _ f _)
  (at level 200, no associativity).
Notation " 'carto' x => m " := (carto by fun x => m)
  (at level 200, x binder, no associativity).

Program Definition CartoSetoid (X Y : Setoid) :=
  [ Carto X Y | ==: ((==) ==> (==))%signature ].
Next Obligation.
  split.
  - intros f x y Heq. now rewrite Heq. 
  - intros f g Heq1 x y Heq2. now rewrite (Heq1 y x (symmetry Heq2)).
  - intros f g h Heq1 Heq2 x y Heq3. 
    now rewrite (Heq1 x y Heq3), <-(Heq2 x y Heq3), Heq3.
Defined.
Canonical Structure CartoSetoid.

Program Definition InducedSetoid {X : Type} {Y : Setoid} (f : X -> Y) :=
  [ X | ==: fun x1 x2 : X => f x1 == f x2].
Next Obligation.
  split; intuition. intros x y z Exy Eyz. now rewrite Exy.
Defined.

Program Definition indsetoid_carto {X : Type} {Y : Setoid} (f : X -> Y)
  : Carto (InducedSetoid f) Y := carto x => f x.
Next Obligation.
  now intros x1 x2 Ex12.
Defined.  

Inductive sigS `(P : Carto X Prop) : Type :=
  existS : forall x : X, P x -> sigS P.
Arguments existS {_} {_} {_} _.

Coercion sval `{P : Carto X Prop} (e : sigS P) :=
  match e with (@existS _ _ a b) => a end.

Definition sigSSetoid `(P : Carto X Prop) :=
  @InducedSetoid (sigS P) X sval.
Definition incluS `(P : Carto X Prop) : Carto (sigSSetoid P) X := 
  @indsetoid_carto (sigS P) X sval.
Canonical Structure sigSSetoid.

Structure Ensemble (X : Setoid) : Type := {
  ensconf :> Carto X Prop;
}.

Coercion ens_setoid `(A : Ensemble X) := sigSSetoid (ensconf A).

Notation "[  x  :  A  |  P  ]" := (@Build_Ensemble A (carto x => P))
  (x at level 99).
Notation "[  x  |  P  ]" := [x : _ | P]
  (x at level 99).

Class Included {X} (A B : Ensemble X) := {
  included : forall x : A, B x
}.
Notation "A '<=' B" := (@Included _ A B) : setoid_scope.

Lemma included_trans {X} : Transitive (@Included X).
Proof.
  intros A B C [LAB] [LBC]. split. intros x. apply (LBC (existS (LAB x))).
Qed.
#[global]
Existing Instance included_trans.

Definition enseq {X} (A B : Ensemble X) := A <= B /\ B <= A.
Program Definition EnsembleSetoid (X : Setoid) := [ ==: @enseq X].
Next Obligation.
  split.
  - intros A. split; split; now intros [x Ax].
  - intros A B [AB]. now split.
  - intros A B C [AB BA] [BC CB]. split.
    + apply (transitivity AB BC).
    + apply (transitivity CB BA).
Defined.
Canonical Structure EnsembleSetoid.

Program Definition trivEns (X : Setoid) := [ _ : X | True ].
Next Obligation.
  now intros x.
Defined.

Program Definition Image {X Y} (f : Carto X Y) (A : Ensemble X) :=
  [ y | exists a : A, y == f a ].
Next Obligation.
  intros x y Exy. split; intros [a Exfa]; exists a;
  try rewrite <-Exfa; try rewrite Exy; trivial; reflexivity.
Defined.

Program Definition Preimage {X Y} (f : Carto X Y) (B : Ensemble Y) :=
  [ x | B (f x) ].
Next Obligation.
  intros x y Exy. now rewrite Exy.
Defined.

Structure Map {X Y} (A : Ensemble X) (B : Ensemble Y) := {
  mapfun :> Carto A B;
}.

Definition MapSetoid {X Y} (A : Ensemble X) (B : Ensemble Y) :=
  InducedSetoid (@mapfun _ _ A B).

Class IsInjective {X Y} {A : Ensemble X} {B : Ensemble Y} (f : Map A B) := {
  inj : forall x y : A, f x == f y -> x == y
}.

Class IsSurjective {X Y} {A : Ensemble X} {B : Ensemble Y} (f : Map A B) := {
  surj : forall y : B, exists x : A, y == (f x)
}.

Class IsBijective {X Y} {A : Ensemble X} {B : Ensemble Y} (f: Map A B) := {
  bij_inj :> IsInjective f;
  bij_surj :> IsSurjective f
}.

Close Scope setoid_scope.






