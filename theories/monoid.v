Generalizable All Variables.
Set Implicit Arguments.
Unset Strict Implicit.
Require Export setoid.

Declare Scope monoid_scope.
Delimit Scope monoid_scope with mnd.
Open Scope setoid_scope.
Open Scope monoid_scope.

Definition Ope X := Map X X.
Definition Binop X := Dymap X X X.

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

Class IsMonoid `(mul : Binop supp) e :=
{
  assocm :> Associative mul;
  identm :> Identical mul e;
}.
#[global] Existing Instances assocm identm.

Structure Monoid := {
  mcarrier :> Setoid;
  mulm : Binop mcarrier;
  idm : mcarrier;

  monoidsprf : IsMonoid mulm idm
}.
#[global] Existing Instance monoidsprf.

Arguments mulm {_}.
Arguments idm {_}.

Notation "[ A | *: op , 1: id ]" :=
  (@Build_Monoid A op id _)
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
  Context {M : Monoid}.
  Implicit Types x y g : M.

  Lemma mulmA : forall {x y z}, x * (y * z) == (x * y) * z.
  Proof. now destruct M as [a b c [[e] f]]. Qed.

  Lemma mulm1 : forall {x}, x * 1 == x.
  Proof. now destruct M as [a b c [[e] [f [g]]]]. Qed.

  Lemma mul1m : forall {x}, 1 * x == x.
  Proof. now destruct M as [a b c [[e] [[f] g]]]. Qed.
End MonoidTheory.

Ltac existsS T :=
  let H := fresh "H" in
  apply sigS_exists; exists T; simpl;
  match goal with
  | |- exists _ : ?P, _ => assert P as H
  end; [intuition |exists H].

Program Canonical Structure ensmulM {M : Monoid} :=
  [ {ens M} | *: imens2 ( * in M ), 1: [ == 1] ].
Next Obligation.
  split; split.
  - intros A B C. split.
  + intros [a [[m [b [c E]]] E0]].
    existsS (a * b); [now exists a, b | exists c].
    now rewrite <-assoc, <-E, <-E0.
  + intros [[m [a [b E]]] [c E0]]. 
    exists a. existsS (b * c). now exists b, c.
    now rewrite assoc, <-E, <-E0.
  - split. intros A. split. 
  + intros [[i I] [[a Aa] E]]. simpl in *.
    now rewrite <-H, E, I, mul1m.
  + intros Ay. existsS (1 in M).
    existsS y. now rewrite mul1m.
  - split. intros A. split.
  + intros [[a Aa] [[i I] E]]. simpl in *.
    now rewrite <-H, E, I, mulm1.
  + intros Ay. existsS y. 
    existsS (1 in M). now rewrite identr.
Defined.

Close Scope monoid_scope.
Close Scope setoid_scope.