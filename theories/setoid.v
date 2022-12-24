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
#[global] Existing Instance equal_equiv.

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

Structure Map (X Y : Setoid) : Type := {
  mapfun :> X -> Y;
  mapprf :> Proper ((==) ==> (==)) mapfun
}.
#[global] Existing Instance mapprf.

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

Structure Binmap (X Y Z : Setoid) := {
  bmapfun :> X -> Y -> Z;
  bmapprf :> Proper ((==) ==> (==) ==> (==)) bmapfun
}.
#[global] Existing Instance bmapprf.

Notation "'bmap' 'by' f" := (@Build_Binmap _ _ _ f _)
  (at level 200, no associativity).
Notation "'bmap' x y => m" := (bmap by fun x y => m)
  (at level 200, x binder, y binder, no associativity).

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
Canonical Structure sigSSetoid.
Definition inclS `{P : Map X Prop} : Map (sigS P) X := 
  @indsetoid_map (sigS P) X sval.
Canonical Structure inclS.

Structure Ensemble (X : Setoid) : Type := {
  ensconf :> Map X Prop;
}.

Notation "[  x  :  A  |  P  ]" :=
  (@Build_Ensemble A (map x => P))
  (at level 0, x at level 99) : setoid_scope.
Notation "[  x  |  P  ]" := [ x : _ | P ]
  (at level 0, x at level 99) : setoid_scope.
Notation "[  x 'in' A | P  ]" := [ x | A x /\ P ]
  (at level 0, x at level 99) : setoid_scope.
Notation "[ | P  ]" := (@Build_Ensemble _ P)
  (at level 0, P at level 99) : setoid_scope.
Notation "{ 'ens' X }" := (Ensemble X)
  (at level 0, format "{ 'ens'  X }") : setoid_scope.

Coercion ens_setoid `(A : {ens X}) := sigSSetoid (ensconf A).

Definition subens {X} (A B : {ens X}) := forall x : A, B x.
Notation "A '<=' B" := (@subens _ A B) : setoid_scope.
Lemma subens_trans {X} : Transitive (@subens X).
Proof.
  intros A B C LAB LBC x. apply (LBC (existS (LAB x))).
Qed.
#[global] Existing Instance subens_trans.

Ltac trans P := apply (transitivity P). 

Program Definition inclmap {X} {A B : {ens X}} (H : A <= B)
  : Map A B := map x => (@existS _ _ (sval x) _).
Next Obligation. apply H. Defined.
Next Obligation. now intros x y E. Defined.

Definition enseq {X} (A B : {ens X}) := A <= B /\ B <= A.
Program Definition EnsembleSetoid (X : Setoid) := [ ==: @enseq X].
Next Obligation.
  split.
  - intros A. split; now intros [x Ax].
  - intros A B [AB]. now split.
  - intros A B C [AB BA] [BC CB]. split;
    now (trans AB || trans CB).
Defined.
Canonical Structure EnsembleSetoid.

Program Definition Subens {X : Setoid} := bmap by (@subens X).
Next Obligation.
  intros A B [E1 E2] C D [E3 E4]. split; intros Lt;
  (trans E2 || trans E1); now trans Lt.
Defined.
Canonical Structure Subens.

Program Definition ensTfor (X : Setoid) := [ _ : X | True ].
Next Obligation. now intros x. Defined.
Program Definition ens0 {X : Setoid} := [ _ : X | False ].
Next Obligation. now intros x. Defined.
Program Definition ens1 {X} a := [ x : X | x == a ].
Next Obligation. intros x y E. now rewrite E. Defined.
Program Definition ensU {X} (A B : {ens X}) := [ x : X | A x \/ B x ].
Next Obligation. intros x y E. now rewrite E. Defined.
Program Definition ensI {X} (A B : {ens X}) := [ x in A | B x ].
Next Obligation. intros x y E. now rewrite E. Defined.
Program Definition ensC {X} (A : {ens X}) := [ x | ~ A x ].
Next Obligation. intros x y E. now rewrite E. Defined.
Program Definition ensD {X} (A B : {ens X}) := [ x in A | ~ B x ].
Next Obligation. intros x y E. now rewrite E. Defined.
Program Definition powens {X} (A : {ens X}) := [ B | B <= A ].
Next Obligation. intros B C E. now rewrite E. Defined.

Notation "[ 'ens' a ]" := (ens1 a)
  (at level 0, a at level 99, format "[ 'ens'  a ]") : setoid_scope.
Notation "[ 'ens' a : T ]" := [ens (a : T)]
  (at level 0, a at level 99, format "[ 'ens'  a   :  T ]")
  : setoid_scope.
Notation "A :|: B" := (ensU A B) 
  (at level 50, left associativity): setoid_scope.
Notation "a |: A" := ([ens a] :|: A)
  (at level 50, left associativity) : setoid_scope.
Notation "[ 'ens' a1 ; a2 ; .. ; an ]" :=
  (ensU .. (a1 |: [ens a2]) .. [ens an])
  (at level 0, a1 at level 99,
   format "[ 'ens'  a1 ;  a2 ;  .. ;  an ]") : setoid_scope.
Notation "A :&: B" := (ensI A B)
  (at level 40, left associativity) : setoid_scope.
Notation "~: A" := (ensC A)
  (at level 35, right associativity) : setoid_scope.
Notation "[ 'ens' ~ a ]" := (~: [ens a])
  (at level 0, format "[ 'ens' ~  a ]") : setoid_scope.
Notation "A :\: B" := (ensD A B)
  (at level 50, left associativity) : setoid_scope.
Notation "A :\ a" := (A :\: [ens a])
  (at level 50, left associativity) : setoid_scope.

(* Definition inclsigS {X} {A B : {ens X}} (H : A <= B) (a : A) *)

Program Definition imens {X Y} (f : Map X Y) :=
  map (A : {ens X}) => [ y | exists (a : A), y == f a ].
Next Obligation.
  intros x y E. split; intros [a H]; exists a;
  now (rewrite <-E || rewrite E).
Defined.
Next Obligation.
  intros A B [L1 L2]. split; intros [y [a E]];
  now (exists (inclmap L1 a) || exists (inclmap L2 a)).
Defined.
Notation "f @: A" := (@imens _ _ f A)
  (at level 24, right associativity) : setoid_scope.

Program Definition preimens {X Y} (f : Map X Y) :=
  map (B : {ens Y}) => [ x | B (f x) ].
Next Obligation. intros x y Exy. now rewrite Exy. Defined.
Next Obligation.
  intros A B [L1 L2]. split; intros [x P]; simpl in P;
  (apply (L1 (existS P)) || apply (L2 (existS P))).
Defined.
Notation "f -@: B" := (@preimens _ _ f B)
  (at level 24, right associativity) : setoid_scope.

Class Injective {A B : Setoid} (f : A -> B) := {
  inj : forall x y, f x == f y -> x == y
}.

Class Surjective {A B : Setoid} (f : A -> B) := {
  surj : forall y, exists x, y == (f x)
}.
Arguments surj {_} {_} _ {_}.

Class Bijective {A B : Setoid} (f : A -> B) := {
  bij_inj :> Injective f;
  bij_surj :> Surjective f
}.
#[global] Existing Instances bij_inj bij_surj.

Program Definition mapcomp {X Y Z} (f : Map X Y) (g : Map Y Z)
  : Map X Z := map x => g (f x).
Next Obligation. intros x y Heq. now rewrite Heq. Defined.
Notation "g 'o' f" := (@mapcomp _ _ _ f g)
  (at level 60, right associativity) : setoid_scope.

Lemma mapcomp_reduc {X Y Z} {f g : Map Y Z} {h : Map X Y} :
  Surjective h -> f o h == g o h -> f == g.
Proof.
  intros [Sh] Heq x y Heq1. destruct (Sh y) as [x0 Heq2].
  rewrite Heq1, Heq2. now apply Heq.
Qed.

Lemma mapcomp_assoc {X Y Z W} {f : Map Z W} {g : Map Y Z}
  {h : Map X Y} : (f o g) o h == f o g o h.
Proof. intros x y Heq. now rewrite Heq. Qed.

Lemma sval_inj `{P : Map X Prop} : Injective (@sval _ P).
Proof. split; intuition. Qed.
#[global] Existing Instance sval_inj.

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

Definition pairin {X Y} (A : {ens X}) (B : {ens Y})
  (p : (X * Y)%type) := A (fst p) /\ B (snd p).
Program Definition pairens {X Y} (A : {ens X}) (B : {ens Y})
  := [ p : (X * Y)%type | pairin A B p ].
Next Obligation.
  intros p1 p2 [E1 E2]. split; intros [Ap Bp]; split;
  now (rewrite <-E1 || rewrite <-E2 ||
    rewrite E1 || rewrite E2).
Defined.
Notation "[  A  ,  B  ]" := (@pairens _ _ A B)
  (at level 0, A, B at level 99, no associativity)
  : setoid_scope.

Program Definition bmap_pmap `(f : Binmap X Y Z)
  : Map (X * Y)%type Z := map p => f (fst p) (snd p).
Next Obligation.
  intros p1 p2 [E1 E2]. now rewrite E1, E2.
Defined.

Program Definition imens2 `(f : Binmap X Y Z) :=
  bmap (A : {ens X}) (B : {ens Y})
  => [ z | exists (a : A) (b : B), z == f a b ].
Next Obligation.
  intros z1 z2 E. split; intros [a [b E1]];
  exists a, b; now (rewrite <-E || rewrite E).
Defined.
Next Obligation.
  intros A1 A2 [L1 L2] B1 B2 [L3 L4]. split;
  intros [z [a [b E]]]; now
  (exists (inclmap L1 a), (inclmap L3 b)
  || exists (inclmap L2 a), (inclmap L4 b)).
Defined.
Notation "f @2: ( A , B )" := (@imens2 _ _ _ f A B)
  (at level 24, right associativity) : setoid_scope.

Program Definition imens2' `(f : Binmap X Y Z) :=
  bmap A B => imens (bmap_pmap f) [A, B].
Next Obligation.
  intros A B [L1 L2] C D [L3 L4]. split;
  intros [z [[p [H1 H2]] E]];
  (pose (conj (L1 (existS H1)) (L3 (existS H2))) as H ||
  pose (conj (L2 (existS H1)) (L4 (existS H2))) as H);
  now exists (@existS _ (map p0 => pairin _ _ p0) p H).
Defined.

Notation "f ^~ y" := (fun x => f x y)
  (at level 10, y at level 8, no associativity, format "f ^~  y")
  : setoid_scope.
Notation "@^~ x" := (fun f => f x) 
  (at level 10, x at level 8, no associativity, format "@^~  x")
  : setoid_scope.

Close Scope setoid_scope.






