Generalizable All Variables.
Set Implicit Arguments.
Unset Strict Implicit.

Require Export Coq.Program.Basics Coq.Program.Tactics
  Coq.Setoids.Setoid Coq.Classes.Morphisms.

Ltac trans P := apply (transitivity P).
Ltac rewrite2 E := rewrite E || rewrite <-E.
Ltac rewrite2_in E H := (rewrite E in H) || (rewrite <-E in H).
Ltac simpeq := simpl; autounfold with eq; simpl.
Ltac simpeq_all := simpl in *; autounfold with eq in *; simpl in *.

Ltac sapply H :=
  let m := fresh "m" in
  pose H as m; simpl in m; apply m.

Ltac srewrite H :=
  let m := fresh "m" in
  pose H as m; simpl in m; rewrite m.

Declare Scope setoid_scope.
Open Scope setoid_scope.

Structure Setoid : Type := {
  scarrier :> Type;
  equal : relation scarrier;
  equal_equiv : Equivalence equal
}.
#[global] Existing Instance equal_equiv.

Notation "[  A  |  ==:  P  ]" := (@Build_Setoid A P _)
  (at level 0, A, P at level 99) : setoid_scope.
Notation "( == 'in' A )" := (@equal A)
  (at level 0, format "( == 'in' A )") : setoid_scope.
Notation "(==)" := (== in _) : setoid_scope.
Notation "x == y 'in' A" := (@equal A x y)
  (at level 70, y at next level, no associativity)
  : setoid_scope.
Notation "x == y" := (x == y in _)
  (at level 70, no associativity) : setoid_scope.

Canonical Structure PropSetoid := [ _ | ==: iff ].
Notation "'[Prop]'" := PropSetoid : setoid_scope.

Lemma sym {X : Setoid} {x y : X} : (x == y) == (y == x).
Proof. split; intros H; now symmetry. Defined.

Structure Map (X Y : Setoid) := {
  mapfun :> X -> Y;
  mapprf : Proper ((==) ==> (==)) mapfun
}.
#[global] Existing Instance mapprf.

Notation "'map' 'by' f" := (@Build_Map _ _ f _)
  (at level 200, no associativity).
Notation "'map' x => m" := (map by fun x => m)
  (at level 200, x binder, no associativity).

Definition map_eq {X Y} (f g : Map X Y)
  := ((==) ==> (==))%signature f g.
#[global] Hint Unfold map_eq : eq.
Program Canonical Structure MapSetoid (X Y : Setoid)
  := [ Map X Y | ==: map_eq ].
Next Obligation.
  split; intros f.
  - apply mapprf.
  - intros g H a b E. symmetry. now apply H.
  - intros g h H H0 a b E. rewrite (H _ _ E). now apply H0.
Defined.
Notation "X [>] Y" := (@MapSetoid X Y)
  (at level 99, no associativity) : setoid_scope.
Notation "{ 'pred' X }" := (Map X [Prop])
  (at level 0, format "{ 'pred'  X }") : setoid_scope.
Notation "[ 'pred' X ]" := (X [>] [Prop])
  (at level 0, format "[ 'pred'  X ]") : setoid_scope.

Structure Dymap (X Y Z : Setoid) := {
  dmapfun :> X -> Y -> Z;
  dmapprf : Proper ((==) ==> (==) ==> (==)) dmapfun
}.
#[global] Existing Instance dmapprf.

Notation "'dmap' 'by' f" := (@Build_Dymap _ _ _ f _)
  (at level 200, no associativity).
Notation "'dmap' x y => m" := (dmap by fun x y => m)
  (at level 200, x binder, y binder, no associativity).

Definition dymap_eq {X Y Z} (f g : Dymap X Y Z) :=
  ((==) ==> (==) ==> (==))%signature f g.
#[global] Hint Unfold dymap_eq : eq.
Program Canonical Structure DymapSetoid {X Y Z : Setoid} :=
  [ Dymap X Y Z | ==: dymap_eq ].
Next Obligation.
  split; intros f.
  - apply dmapprf.
  - intros g E x x0 Ex y y0 Ey. symmetry. now apply E.
  - intros g h E E0 x x0 Ex y y0 Ey.
    rewrite (E _ _ Ex _ _ Ey). now apply E0.
Defined.

Definition mcurry `(f : Dymap X Y Z) (x : X) := map by (f x).

Program Definition Comap {X Y : Setoid}
  := dmap (f : Map X Y) x => f x.
Next Obligation.
  intros f f0 Ef a a0 Ea. now apply Ef.
Defined.
Notation "< f , a >" := (Comap f a)
  (at level 0, f, a at level 0, no associativity,
  format "< f ,  a >") : setoid_scope.

Lemma map_comap `{f : Map X Y} {a : X} : f a == <f, a>.
Proof. reflexivity. Qed.

Program Definition InducedSetoid {X} {Y : Setoid} (f : X -> Y) :=
  [ X | ==: fun x1 x2 : X => f x1 == f x2].
Next Obligation.
  split; intuition. intros x y z Exy Eyz. now rewrite Exy.
Defined.
Notation "'\ISE'" := InducedSetoid_obligation_1 : setoid_scope.

Obligation Tactic := (try now intros x); intros; (try apply \ISE).

Structure Ensemble X := {
  ensconf :> {pred X}
}.

Notation "[  x  :  X  |  P  ]" :=
  (@Build_Ensemble _ (map (x : X) => P))
  (at level 0, x at level 99) : setoid_scope.
Notation "[  x  |  P  ]" := [ x : _ | P ]
  (at level 0, x at level 99) : setoid_scope.
Notation "'ens' 'by' P" := (@Build_Ensemble _ P)
  (at level 200, no associativity) : setoid_scope.
Notation "[  x 'in' A | P  ]" := [ x | A x /\ P ]
  (at level 0, x at level 99) : setoid_scope.
Notation "{ 'ens' X }" := (@Ensemble X)
  (at level 0, format "{ 'ens'  X }")
  : setoid_scope.

Definition ens_eq {X} (A B : {ens X}) :=
  ensconf A == ensconf B.
#[global] Hint Unfold ens_eq : eq.
Program Canonical Structure EnsembleSetoid X
  := [ {ens X} | ==: ens_eq ].
Notation "[ 'ens' X ]" := (@EnsembleSetoid X)
  (at level 0, format "[ 'ens'  X ]")
  : setoid_scope.
Program Canonical Structure ensconfM {X}
  : Map {ens X} [pred X] := map x => ensconf x.

Structure sigS `(P : {pred X}) := {
  sval :> X;
  _ : P sval
}.
Arguments Build_sigS {_} {_} {_} _.

Notation "$[ x , H ]" := (@Build_sigS _ _ x H)
  (at level 0, no associativity) : setoid_scope.
Notation "$[ x ]" := ($[x, _])
  (at level 0, no associativity, format "$[ x ]")
  : setoid_scope.
Notation "$ x" := (sval x)
  (at level 35, right associativity, format "$ x")
  : setoid_scope.

Definition sigS_eq `{P : {pred X}} (e0 e1 : sigS P)
  := e0 == e1.
#[global] Hint Unfold sigS_eq : eq.
Program Canonical Structure sigSSetoid `(P : {pred X}) :=
  [ sigS P | ==: sigS_eq ].
Notation "{ | P }" := (sigSSetoid P)
  (at level 0, no associativity, format "{  |  P }")
  : setoid_scope.
Program Canonical Structure inclS `{P : {pred X}}
  : Map { | P} X := map x => $x.

Lemma sigS_exists `{P : {pred X}} {Q : { |P} -> Prop}
  : (exists (x : X) (H : P x), Q $[_, H]) -> exists x : { |P}, Q x.
Proof. intros [x [HP HQ]]. now exists $[_, HP]. Defined.

Lemma forall_sigS `{P : {pred X}} {Q : { |P} -> Prop}
  : (forall x : { |P}, Q x) -> forall (x : X) (H : P x), Q $[_, H].
Proof. intros H x HP. apply H. Defined.

Ltac existsS T :=
  let H := fresh "H" in
  apply sigS_exists; exists T; simpl;
  match goal with
  | |- exists _ : ?P, _ => assert P as H
  end; [intuition | exists H].

Ltac sigapply H :=
  let m := fresh "m" in
  pose (forall_sigS H) as m; simpl in m;
  apply m; simpl.

Lemma val_sval `{P : {pred X}} {x : X} (H : P x)
  :  x == $$[x, H].
Proof. reflexivity. Qed.

Coercion ens_setoid `(A : {ens X}) := { | ensconf A}.

Program Definition subens {X} :=
  dmap (A : {ens X}) (B : {ens X}) => forall x : A, B x.
Next Obligation.
  intros A B E C D E0. split; intros H [x Hx];
  rewrite map_comap; rewrite2 E0; sigapply H;
  rewrite map_comap; now rewrite2 E.
Defined.
Notation "A '<=' B" := (@subens _ A B) : setoid_scope.

#[global]
Instance subens_trans {X} : Transitive (@subens X).
Proof.
  intros A B C LAB LBC x. apply (LBC $[_, LAB x]).
Qed.

Program Definition inclmap {X} {A B : {ens X}} (H : A <= B)
  : Map A B := map x => $[$x].

Definition ens_eq2 {X} (A B : {ens X}) := A <= B /\ B <= A.
Lemma enseq2_eq {X} (A B : {ens X}) : (ens_eq2 A B) == (A == B).
Proof.
  split.
  - intros [H H0] x y E. rewrite E. split;
    sigapply H || sigapply H0.
  - intros E. split; rewrite E; now intros [x H].
Defined.

Program Definition subens_ens {X} {A B : {ens X}}
  (_ : A <= B) : {ens B} := [ x : B | A x ].
Next Obligation.
  intros x y E. split; intros; now rewrite2 E.
Defined.

Definition disjoint {X} {A B : {ens X}}
  := forall x : X, ~ (A x /\ B x).
Notation "A :><: B" := (@disjoint _ A B)
  (at level 70, no associativity) : setoid_scope.

Program Definition ensTfor (X : Setoid) := [ _ : X | True ].
Program Definition ens0 {X : Setoid} := [ _ : X | False ].
Program Definition ens1 {X : Setoid} a := [ x : X | x == a ].
Next Obligation. intros x y E. now rewrite E. Defined.
Program Definition ensU {X} (A B : {ens X}) := [ x | A x \/ B x ].
Next Obligation. intros x y E. now rewrite E. Defined.
Program Definition ensI {X} (A B : {ens X}) := [ x in A | B x ].
Next Obligation. intros x y E. now rewrite E. Defined.
Program Definition ensC {X} (A : {ens X}) := [ x | ~ A x ].
Next Obligation. intros x y E. now rewrite E. Defined.
Program Definition ensD {X} (A B : {ens X}) := [ x in A | ~ B x ].
Next Obligation. intros x y E. now rewrite E. Defined.
Program Definition powens {X} (A : {ens X}) := [ B | B <= A ].
Next Obligation. intros B C E. now rewrite E. Defined.

Program Definition idTmap {X : Setoid} := map _ : X => True.
Definition inT {X : Setoid} (a : X) := @Build_sigS X idTmap a I.

Notation "\0" := (@ens0 _) : setoid_scope.
Notation "[ == a ]" := (ens1 a)
  (at level 0, a at level 99, format "[ ==  a ]") : setoid_scope.
Notation "[ == a : T ]" := [ == (a : T)]
  (at level 0, a at level 99, format "[ ==  a   :  T ]")
  : setoid_scope.
Notation "A :|: B" := (ensU A B) 
  (at level 50, left associativity): setoid_scope.
Notation "a |: A" := ([ == a] :|: A)
  (at level 50, left associativity) : setoid_scope.
Notation "[ == a1 ; a2 ; .. ; an ]" :=
  (ensU .. (a1 |: [ == a2]) .. [ == an])
  (at level 0, a1 at level 99,
   format "[ ==  a1 ;  a2 ;  .. ;  an ]") : setoid_scope.
Notation "A :&: B" := (ensI A B)
  (at level 40, left associativity) : setoid_scope.
Notation "~: A" := (ensC A)
  (at level 35, right associativity) : setoid_scope.
Notation "[ == ~ a ]" := (~: [ == a ])
  (at level 0, format "[ == ~  a ]") : setoid_scope.
Notation "A :\: B" := (ensD A B)
  (at level 50, left associativity) : setoid_scope.
Notation "A :\ a" := (A :\: [ == a ])
  (at level 50, left associativity) : setoid_scope.

Program Definition ensUInf `(S : {ens {ens X}}) :=
  [ x : X | exists U : S , ($U) x ].
Next Obligation.
  intros x y E. split; intros [U H]; exists U; now rewrite2 E.
Defined.

Program Definition ensIInf `(S : {ens {ens X}}) :=
  [ x : X | forall U : S, ($U) x ].
Next Obligation.
  intros x y E. split; intros H U; rewrite2 E; apply H.
Defined.

Program Definition imens {X Y} := dmap (f : Map X Y)
  (A : {ens X}) => [ y | exists (a : A), y == f a ].
Next Obligation.
  intros x y E. split; intros [a H]; exists a;
  now rewrite2 E.
Defined.
Next Obligation.
  intros f1 f2 Ef A1 A2 E. split; intros [[a Ha] E0]; simpl;
  existsS a; rewrite map_comap; (try now rewrite2 E);
  rewrite2 Ef; now rewrite2 H.
Defined.

Notation "f @: A" := (@imens _ _ f A)
  (at level 24, right associativity) : setoid_scope.

Program Definition preimens {X Y} := dmap (f : Map X Y)
  (B : {ens Y}) => [ x | B (f x) ].
Next Obligation. intros x y Exy. now rewrite Exy. Defined.
Next Obligation.
  intros f f0 Ef A A0 E x y H. split; intros H0; simpl in *;
  rewrite !map_comap; rewrite2 E; rewrite2 Ef; now rewrite2 H.
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

Program Definition dmmcomp1 {X Y Z W} (f : Dymap X Y Z)
  (g : Map W X) := dmap w y => f (g w) y.
Next Obligation.
  intros w1 w2 Ew y1 y2 Ey. now rewrite Ew, Ey.
Defined.
Notation "f 'o1' g" := (@dmmcomp1 _ _ _ _ f g)
  (at level 50, left associativity) : setoid_scope.

Program Definition dmmcomp2 {X Y Z W} (f : Dymap X Y Z)
  (g : Map W Y) := dmap x w => f x (g w).
Next Obligation.
  intros w1 w2 Ew y1 y2 Ey. now rewrite Ew, Ey.
Defined.
Notation "f 'o2' g" := (@dmmcomp2 _ _ _ _ f g)
  (at level 50, left associativity) : setoid_scope.

Program Definition mdmcomp {X Y Z W} (g : Map Z W)
  (f : Dymap X Y Z) := dmap x y => g (f x y).
Next Obligation.
  intros a b E c d E0. now rewrite E, E0.
Defined.
Notation "g o< f" := (@mdmcomp _ _ _ _ g f)
  (at level 60, right associativity) : setoid_scope.

Program Definition dmap21 {X Y Z} (f : Dymap X Y Z)
  := dmap y x => f x y.
Next Obligation.
  intros x1 x2 Ex y1 y2 Ey. now rewrite Ex, Ey.
Defined.
Notation "f ><" := (@dmap21 _ _ _ f)
  (at level 10, left associativity) : setoid_scope.

Lemma mapcomp_reduc {X Y Z} {f g : Map Y Z} {h : Map X Y} :
  Surjective h -> f o h == g o h -> f == g.
Proof.
  intros [Sh] Heq x y Heq1. destruct (Sh y) as [x0 Heq2].
  rewrite Heq1, Heq2. now apply Heq.
Qed.

Lemma mapcomp_assoc {X Y Z W} {f : Map Z W} {g : Map Y Z}
  {h : Map X Y} : (f o g) o h == f o g o h.
Proof. intros x y Heq. now rewrite Heq. Qed.

#[global]
Instance sval_inj `{P : {pred X}} : Injective (@sval _ P).
Proof. split; intuition. Qed.

Definition pair_eq {A B : Setoid} (ab1 ab2 : A * B) :=
  fst ab1 == fst ab2 /\ snd ab1 == snd ab2.
#[global] Hint Unfold pair_eq : eq.
Program Canonical Structure PairSetoid (X Y : Setoid) :=
  [ X * Y | ==: pair_eq ].
Next Obligation.
  split.
  - intros p. split; now simpl.
  - intros p1 p2 [E1 E2]. now split.
  - intros p1 p2 p3 [E1 E2] [E3 E4]. split;
    now rewrite E1 || rewrite E2.
Defined.

Program Definition pairens {X Y} (A : {ens X}) (B : {ens Y})
  : {ens (X * Y)%type} := [ p | A (fst p) /\ B (snd p) ].
Next Obligation.
  intros p1 p2 [E1 E2]. split; intros [Ap Bp]; split;
  try (now rewrite2 E1); now rewrite2 E2.
Defined.
Notation "{  A  ,  B  }" := (@pairens _ _ A B)
  (at level 0, A, B at level 99, no associativity)
  : setoid_scope.

Program Definition dmap_pmap `(f : Dymap X Y Z)
  : Map (X * Y)%type Z := map p => f (fst p) (snd p).
Next Obligation.
  intros p1 p2 [E1 E2]. now rewrite E1, E2.
Defined.

Program Definition imens2 `(f : Dymap X Y Z) :=
  dmap (A : {ens X}) (B : {ens Y})
  => [ z | exists (a : A) (b : B), z == f a b ].
Next Obligation.
  intros z1 z2 E. split; intros [a [b E1]];
  exists a, b; now rewrite2 E.
Defined.
Next Obligation.
  intros A A0 EA B B0 EB. split; intros [[a Aa] [[b Bb] E]];
  existsS a; try existsS b; (try now rewrite <-E);
  rewrite map_comap; (try now rewrite2 EA); now rewrite2 EB.
Defined.
Notation "f @2: ( A , B )" := (@imens2 _ _ _ f A B)
  (at level 24, right associativity) : setoid_scope.

Program Definition dmap_curry1_map `(f : Dymap X Y Z)
  := map (x : X) => map by f x.
Next Obligation. intros y1 y2 E. now rewrite E. Defined.
Next Obligation.
  intros x1 x2 E1 y1 y2 E2. simpl. now rewrite E1, E2.
Defined.

Program Definition dmap_curry2_map `(f : Dymap X Y Z)
  := map (y : Y) => map x => f x y.
Next Obligation. intros x1 x2 E. now rewrite E. Defined.
Next Obligation.
  intros y1 y2 E1 x1 x2 E2. simpl. now rewrite E1, E2.
Defined.

Notation "f '^m'" := (@dmap_curry1_map _ _ _ f)
  (at level 10, no associativity) : setoid_scope.
Notation "f ^~" := (@dmap_curry2_map _ _ _ f)
  (at level 10, no associativity) : setoid_scope.

Close Scope setoid_scope.
