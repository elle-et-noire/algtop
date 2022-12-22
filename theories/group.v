Generalizable All Variables.
Set Implicit Arguments.
Require Export setoid.

Declare Scope group_scope.
Open Scope setoid_scope.
Open Scope group_scope.

Structure Bincarto (X Y Z : Setoid) := {
  bincfun :> X -> Y -> Z;
  bincproper :> Proper ((==) ==> (==) ==> (==)) bincfun
}.
#[global]
Existing Instance bincproper.

Structure Binop `(A : Ensemble X) := {
  binopfun :> Bincarto A A A
}.

Class Associative `{A : Ensemble X} (op : Binop A) := {
  assoc :
    forall x y z : A, op x (op y z) == op (op x y) z 
}.

Class LIdentical `{A : Ensemble X} (op : Binop A) e := {
  identl : forall x : A, op e x == x
}.

Class RIdentical `{A : Ensemble X} (op : Binop A) e := {
  identr : forall x : A, op x e == x
}.

Class Identical `{A : Ensemble X} (op : Binop A) e := {
  id_identl :> LIdentical op e;
  id_identr :> RIdentical op e
}.
#[global]
Existing Instances id_identl id_identr.


Class LInvertible `{A : Ensemble X} (op : Binop A) e (inv : Map A A) := {
  invl : forall x : A, op (inv x) x == e
}.

Class RInvertible `{A : Ensemble X} (op : Binop A) e (inv : Map A A) := {
  invr : forall x : A, op x (inv x) == e
}.

Class Invertible `{A : Ensemble X} (op : Binop A) e (inv : Map A A) := {
  inv_invl :> LInvertible op e inv;
  inv_invr :> RInvertible op e inv
}.
#[global]
Existing Instances inv_invl inv_invr.


Class IsGroup `{supp : Ensemble X} (mul : Binop supp) 
              (inv : Map supp supp) e :=
{
  mulgA :> Associative mul;
  mulg1 :> RIdentical mul e;
  mulgV :> RInvertible mul e inv
}.

Structure Group X := {
  suppg :> Ensemble X;
  mulg : Binop suppg;
  invg : Map suppg suppg;
  idg : suppg;

  groupprf :> IsGroup mulg invg idg
}.
#[global]
Existing Instance groupprf.

Arguments mulg {_} {_}.
Arguments invg {_} {_}.
Arguments idg {_} {_}.

Notation "[ A | *: op , !: inv , 1: id ]" :=
  (@Build_Group _ A op inv id _)
  (at level 0, A, op, inv, id at level 99, no associativity) : group_scope.
Notation "[ *: op , !: inv , 1: id ]" := [ _ | *: op, !: inv, 1: id]
  (at level 0, op, inv, id at level 99, no associativity) : group_scope.
Notation "(  * 'in' G  )" := (@mulg _ G) : group_scope.
Notation "( * )" := ( * in _ ) : group_scope.
Notation "g * h 'in' G" := (@mulg _ G g h)
  (at level 40, h at next level, left associativity) : group_scope.
Notation "g * h" := (g * h in _) : group_scope.
Notation "1 'in' G" := (@idg _ G)
  (at level 0, G at level 99, no associativity) : group_scope.
Notation "1" := (1 in _) : group_scope.
Notation "(  ! 'in' G  ) " := (@invg _ G) : group_scope.
Notation "( ! )" := ( ! in _ ) : group_scope.
Notation "! g 'in' G" := (@invg _ G g)
  (at level 35, g at next level, right associativity) : group_scope.
Notation "! g" := ( ! g in _ )
  (at level 35, right associativity) : group_scope.

Lemma mul1g : forall `{G : Group X}, LIdentical ( * in G ) 1.
Proof.
  split. intros x.
  assert (1 * x == 1 * (x * 1)) as Heq0.
  { now rewrite identr. }
  assert (x * 1 == x * !x * !!x) as Heq1.
  { now rewrite <-(invr (!x)), assoc. }
  rewrite Heq0, Heq1, invr, assoc, identr.
  assert (1 == x * !x) as Heq2. { now rewrite invr. }
  now rewrite Heq2, <-assoc, invr, identr.
Qed.
#[global]
Existing Instance mul1g.