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

Notation "( == '@' A )" := (equal A)
  (at level 0, format "( == '@' A )").
Notation "(==)" := (== @ _).
Notation "x == y @ A" := (equal A x y)
  (at level 70, y at next level, no associativity).
Notation "x == y" := (x == y @ _)
  (at level 70, no associativity) : setoid_scope.

Program Definition PropSetoid := [ ==: iff ].
Canonical Structure PropSetoid.

Structure Map (X Y : Setoid) : Type := {
  mapfun :> X -> Y;
  mapprf :> Proper ((==) ==> (==)) mapfun
}.
#[global]
Existing Instance mapprf.

Notation "'map' 'by' f" := (@Build_Map _ _ f _)
  (at level 200, no associativity).
Notation "'map' x => m" := (map by fun x => m)
  (at level 200, x binder, no associativity).

Program Definition MapSetoid (X Y : Setoid) :=
  [ Map X Y | ==: ((==) ==> (==))%signature ].
Next Obligation.
  split.
  - intros f x y Heq. now apply mapprf.
  - intros f g Heq1 x y Heq2. now rewrite (Heq1 y x (symmetry Heq2)).
  - intros f g h Heq1 Heq2 x y Heq3. 
    now rewrite (Heq1 x y Heq3), <-(Heq2 x y Heq3), Heq3.
Defined.
Canonical Structure MapSetoid.

Program Definition InducedSetoid {X} {Y : Setoid} (f : X -> Y) :=
  [ X | ==: fun x1 x2 : X => f x1 == f x2].
Next Obligation.
  split; intuition. intros x y z Exy Eyz. now rewrite Exy.
Defined.

Program Definition indsetoid_map {X} {Y : Setoid} (f : X -> Y)
  : Map (InducedSetoid f) Y := map x => f x.
Next Obligation. now intros x1 x2 Ex12. Defined.

Inductive sigS `(P : Map X Prop) : Type :=
  existS : forall x : X, P x -> sigS P.
Arguments existS {_} {_} {_} _.

Coercion sval `{P : Map X Prop} (e : sigS P) :=
  match e with (@existS _ _ a b) => a end.

Definition sigSSetoid `(P : Map X Prop) :=
  @InducedSetoid (sigS P) X sval.
Definition incluS `{P : Map X Prop} : Map (sigSSetoid P) X := 
  @indsetoid_map (sigS P) X sval.
Canonical Structure sigSSetoid.

Lemma sval_ismap `{P : Map X Prop} : Proper ((==) ==> (==)) (@sval _ P).
Proof. now destruct (@incluS _ P). Qed.
#[global]
Existing Instance sval_ismap.

Structure Ensemble (X : Setoid) : Type := {
  ensconf :> Map X Prop;
}.

Coercion ens_setoid `(A : Ensemble X) := sigSSetoid (ensconf A).

Notation "[  x  :  A  |  P  ]" := (@Build_Ensemble A (map x => P))
  (x at level 99).
Notation "[  x  |  P  ]" := [x : _ | P]
  (x at level 99).

Class Included {X} (A B : Ensemble X) := {
  included : forall x : A, B x
}.
Notation "A '<=' B" := (@Included _ A B) : setoid_scope.

Lemma included_trans {X} : Transitive (@Included X).
Proof.
  intros A B C [LAB] [LBC]. split. intros x.
  apply (LBC (existS (LAB x))).
Qed.
#[global]
Existing Instance included_trans.

Program Definition inclumap {X} {A B : Ensemble X} (H : A <= B)
  : Map A B := map x => (@existS _ _ (sval x) _).
Next Obligation. apply H. Defined.
Next Obligation. now intros x y E. Defined.

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
Next Obligation. now intros x. Defined.

Program Definition imens {X Y} (f : Map X Y) (A : Ensemble X) :=
  [ y | exists a : A, y == f a ].
Next Obligation.
  intros x y Exy. split; intros [a Exfa]; exists a;
  try rewrite <-Exfa; try rewrite Exy; trivial; reflexivity.
Defined.

Program Definition preimens {X Y} (f : Map X Y) (B : Ensemble Y) :=
  [ x | B (f x) ].
Next Obligation. intros x y Exy. now rewrite Exy. Defined.

Class Injective {A B : Setoid} (f : A -> B) := {
  inj : forall x y : A, f x == f y -> x == y
}.

Class Surjective {A B : Setoid} (f : A -> B) := {
  surj : forall {y : B}, exists x : A, y == (f x)
}.
Arguments surj {_} {_} _ {_}.

Class Bijective {A B : Setoid} (f : A -> B) := {
  bij_inj :> Injective f;
  bij_surj :> Surjective f
}.
#[global]
Existing Instances bij_inj bij_surj.

Program Definition mapcomp {X Y Z} (f: Map X Y) (g: Map Y Z)
  : Map X Z := map x => g (f x).
Next Obligation. intros x y Heq. now rewrite Heq. Defined.
Notation "g 'o' f" := (@mapcomp _ _ _ f g)
  (at level 60, right associativity) : setoid_scope.

Lemma mapcomp_reduc : forall {X Y Z} {f g: Map Y Z} {h: Map X Y},
  Surjective h -> f o h == g o h -> f == g.
Proof.
  intros X Y Z f g h [Sh] Heq x y Heq1. rewrite Heq1.
  destruct (Sh y) as [x0 Heq2]. rewrite Heq2. now apply Heq.
Qed.

Lemma mapcomp_assoc {X Y Z W} {f: Map Z W} {g: Map Y Z} {h: Map X Y} :
  (f o g) o h == f o g o h.
Proof. intros x y Heq. now rewrite Heq. Qed.

Lemma sval_inj `{P : Map X Prop} : Injective (@sval _ P).
Proof. split; intuition. Qed.
#[global]
Existing Instance sval_inj.

Structure Binmap (X Y Z : Setoid) := {
  bmapfun :> X -> Y -> Z;
  bmapprf :> Proper ((==) ==> (==) ==> (==)) bmapfun
}.
#[global]
Existing Instance bmapprf.

Definition paireq {A B : Setoid} (ab1 ab2 : A * B) :=
  fst ab1 == fst ab2 /\ snd ab1 == snd ab2.
Program Definition PairSetoid (X Y : Setoid) :=
  [ X * Y | ==: paireq ].
Next Obligation.
  split.
  - intros p. split; now simpl.
  - intros p1 p2 [E1 E2]. now split.
  - intros p1 p2 p3 [E1 E2] [E3 E4]. split;
    now (rewrite E1 || rewrite E2).
Defined.
Canonical Structure PairSetoid.

Program Definition pairens {X Y} (A : Ensemble X) (B : Ensemble Y)
  := [ p : (X * Y)%type | A (fst p) /\ B (snd p) ].
Next Obligation.
  intros p1 p2 [E1 E2]. split; intros [Ap Bp]; split;
  now (rewrite <-E1 || rewrite <-E2 ||
    rewrite E1 || rewrite E2).
Defined.
Notation "[  A  ,  B  ]" := (@pairens _ _ A B)
  (at level 0, A, B at level 99, no associativity) : setoid_scope.

Program Definition bmap_pmap `(f : Binmap X Y Z)
  : Map (X * Y)%type Z := map p => f (fst p) (snd p).
Next Obligation.
  intros p1 p2 [E1 E2]. now rewrite E1, E2.
Defined.

Program Definition imens2 `(f : Binmap X Y Z) (A : Ensemble X)
  (B : Ensemble Y) :=  imens (bmap_pmap f) [A, B].

Close Scope setoid_scope.






