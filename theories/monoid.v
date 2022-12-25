Generalizable All Variables.
Set Implicit Arguments.
Require Export setoid.

Declare Scope monoid_scope.
Delimit Scope monoid_scope with mnd.
Open Scope setoid_scope.
Open Scope monoid_scope.

Definition Binop X := Binmap X X X.

Class Associative {X : Setoid} (op : X -> X -> X) := {
  assoc : forall x y z, op x (op y z) == op (op x y) z 
}.

Class LIdentical {X : Setoid} (op : X -> X -> X) e := {
  identl : forall x, op e x == x
}.

Class RIdentical {X : Setoid} (op : X -> X -> X) e := {
  identr : forall x, op x e == x
}.

Class Identical {X : Setoid} (op : X -> X -> X) e := {
  id_identl :> LIdentical op e;
  id_identr :> RIdentical op e
}.
#[global] Existing Instances id_identl id_identr.

Class IsMonoidS `(mul : Binop supp) e :=
{
  assocm :> Associative mul;
  identrm :> Identical mul e;
}.

Structure MonoidS := {
  mcarrier :> Setoid;
  mulm : Binop mcarrier;
  idm : mcarrier;

  monoidsprf :> IsMonoidS mulm idm
}.
#[global] Existing Instance monoidsprf.

Arguments mulm {_}.
Arguments idm {_}.

Notation "[ A | *: op , 1: id ]" :=
  (@Build_MonoidS A op id _)
  (at level 0, A, op, id at level 99) : monoid_scope.
Notation "[ *: op , 1: id ]" := [ _ | *: op, 1: id]
  (at level 0, op, id at level 99) : monoid_scope.
Notation "(  * 'in' M  )" := (@mulm M) : monoid_scope.
Notation "( * )" := ( * in _ ) : monoid_scope.
Notation "g * h 'in' M" := (@mulm M g h)
  (at level 40, h at next level, left associativity)
  : monoid_scope.
Notation "g * h" := (g * h in _) : monoid_scope.
Notation "1 'in' M" := (@idm M)
  (at level 0, M at level 99, no associativity) : monoid_scope.
Notation "1" := (1 in _) : monoid_scope.

Section MonoidTheory.
  Context {M : MonoidS}.
  Implicit Types x y g : M.

  Lemma mulmA : forall {x y z}, x * (y * z) == (x * y) * z.
  Proof. now destruct M as [a b c [[e] f]]. Qed.

  Lemma mulm1 : forall {x}, x * 1 == x.
  Proof. now destruct M as [a b c [[e] [f [g]]]]. Qed.

  Lemma mul1m : forall {x}, 1 * x == x.
  Proof. now destruct M as [a b c [[e] [[f] g]]]. Qed.
End MonoidTheory.

Ltac existsS T :=
  apply sigS_exists; exists T; simpl.

Program Definition ensmulM {M : MonoidS} :=
  [ {ens M} | *: imens2 ( * in M ), 1: [ens 1] ].
Next Obligation.
  assert ((1 in M) == 1) as Eid. { reflexivity. } split; split.
  - intros A B C. split. 
  + intros [g1 [a [[g2 [b [c E1]]] E2]]].
    simpl in E2. simpl. existsS (a * b).
    assert (exists (a0 : A) (b0 : B), a * b == a0 * b0) as H.
    { now exists a, b. } exists H, c.
    now rewrite E2, E1, assoc.
  + intros [g1 [[g2 [a [b E1]]] [c E2]]]. simpl in E2. simpl.
    exists a. existsS (b * c).
    assert (exists (b0 : B) (c0 : C), b * c == b0 * c0) as H.
    { now exists b, c. } exists H. now rewrite E2, E1, assoc.
  - split. intros A. split. 
  + intros [g [[i I] [[a Aa] E]]]. simpl in I, E. simpl.
    now rewrite E, I, identl.
  + intros [a Aa]. simpl. exists (@existS _ (map x => x == 1) _ Eid).
    exists (existS Aa). simpl. now rewrite identl.
  - split. intros A. split.
  + intros [g [[a Aa] [[i I] E]]]. simpl in I, E. simpl.
    now rewrite E, I, identr.
  + intros [a Aa]. simpl. exists (existS Aa).
    exists (@existS _ (map x => x == 1) _ Eid). simpl.
    now rewrite identr.
Defined.
Canonical Structure ensmulM.

Close Scope monoid_scope.
Close Scope setoid_scope.