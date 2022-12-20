Generalizable All Variables.
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

Class IsMap {X Y : Setoid} (f: X -> Y) := {
  mapproper:> Proper ((==) ==> (==)) f
}.

Structure Map (X Y:Setoid) : Type := {
  mapfun:> X -> Y;
  mapprf:> IsMap mapfun
}.
#[global]
Existing Instance mapprf.

Notation "'map' 'by' f" := (@Build_Map _ _ f _)
  (at level 100, no associativity) : setoid_scope.
Notation " 'map' x : X => m " := (map by fun (x:X) => m)
  (at level 100, x, X at next level, no associativity)
   : setoid_scope.
Notation " 'map' x => m " := (map x : _ => m)
  (at level 100, x at next level, no associativity) : setoid_scope.

Class IsEnsemble (X : Setoid) (conf : X -> Prop) := {
  confproper :> Proper ((==) ==> (==)) conf
}.

Structure Ensemble (X : Setoid) : Type := {
  ensconf :> Map X Prop;
}.

Notation "[  x  :  A  |  P  ]" := (@Build_Ensemble A (map x => P))
  (x at level 99).
Notation "[  x  |  P  ]" := [x : _ | P]
  (x at level 99).
Notation "'all' x : U , P" := (forall x, U x -> P)
  (at level 20, x at level 99).
Notation "'some' x : U , P" := (exists x, U x /\ P)
  (at level 20, x, U, P at level 99).

Class Included {X} (A B : Ensemble X) := {
  included : all x : A, B x
}.
Notation "A '<=' B" := (@Included _ A B) : setoid_scope.

Lemma included_trans {X} : Transitive (@Included X).
Proof. split. intros a xa. apply H0, H, xa. Qed.
#[global]
Existing Instance included_trans.

Definition enseq {X} (A B : Ensemble X) := A <= B /\ B <= A.
Program Definition EnsembleSetoid (X : Setoid) := [ ==: @enseq X].
Next Obligation.
  split.
  - intros A. split; split; now intros x Ax.
  - intros A B [AB]. now split.
  - intros A B C [AB BA] [BC CB]. split.
    + apply (transitivity AB BC).
    + apply (transitivity CB BA).
Defined.
Canonical Structure EnsembleSetoid.

Program Coercion trivEns {X : Setoid} := [ _ | True ].
Next Obligation.
  split. now intros x.
Defined.

Program Definition Image {X Y} (f : Map X Y) (A : Ensemble X) :=
  [ y | some a : A, y == f a ].
Next Obligation.
  split. intros x y Exy. split; intros [a [Aa Exfa]]; exists a; split;
  try rewrite <-Exfa; try rewrite Exy; trivial; reflexivity.
Defined.

Program Definition Preimage {X Y} (f : Map X Y) (B : Ensemble Y) :=
  [ x | B (f x) ].
Next Obligation.
  split. intros x y Exy. now apply mapproper, mapproper.
Defined.

Class IsCarto `(f : Map X Y) (A : Ensemble X) (B : Ensemble Y)  := {
  iminclu : Image f A <= B
}.

Close Scope setoid_scope.






