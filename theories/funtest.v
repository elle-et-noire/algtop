From mathcomp Require Import all_ssreflect.

Lemma true_num (m : nat) (x y : m = m) : x = y.
Proof. exact: eq_irrelevance. Qed.

Inductive t: nat -> Set :=
| t_S: forall (n: nat), t (S n).

Goal forall (n: nat) (p: t (S n)), p = t_S n.
intros n p.
(* destruct p. *)
refine (match p with t_S n => _ end).
reflexivity.
Qed.


Definition fun_comp {X Y Z W}
  (f : X -> Y) (g : Z -> W) (H : Y = Z) : X -> W.
destruct H. refine (fun x => g (f x)). Defined.

Inductive fun_comp {X Y} (f : X -> Y) : forall {Z W}, (Z -> W) -> (X -> W) :=
  fun_comp_core : forall (g : Y -> W), fun

Lemma fun_comp_eq {X Y Z W} (f : X -> Y) (g : Z -> W) H H0
  : forall x, fun_comp f g H x = fun_comp f g H0 x.
Proof.
  intros x. destruct H.
  compute.
  refine (match H0 in (_ = Y0) return (Y = Y0) with eq_refl => _ end).
  destruct H0. Check eq_refl.
  pose (@eq_refl _ Y) as H0'.
  assert (H0 = H0').
  { destruct H0. }
  
  destruct H0.