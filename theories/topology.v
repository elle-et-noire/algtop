Generalizable All Variables.
Set Implicit Arguments.
Require Export setoid.

Declare Scope topology_scope.
Open Scope setoid_scope.
Open Scope topology_scope.

Class IsTopology `(O : {ens {ens X}}) := {
  empty_open : O (@ens0 X);
  full_open : O (ensTfor X);
  inter_open : forall (A B : O), O ($A :&: $B);
  union_open : forall S, S <= O -> O (ensUInf S)
}.

Structure Topology (X : Setoid) := {
  open :> {ens {ens X}};
  topprf :> IsTopology open
}.
#[global] Existing Instance topprf.