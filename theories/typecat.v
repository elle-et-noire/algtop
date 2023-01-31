Generalizable All Variables.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Reversible Pattern Implicit.
Set Primitive Projections.
Set Universe Polymorphism.

Require Export setoid category.

Open Scope setoid_scope.
Open Scope cat_scope.


Unset Primitive Projections.
Unset Universe Polymorphism.
Definition TypeSetoid := [ Type | ==: eq ].

Program Definition funcSetoid (X Y : TypeSetoid) :=
  [ X -> Y | ==: fun f g => forall x, f x = g x ].
Next Obligation.
  split; intuition. intros f g h E E0 x. now rewrite E.
Defined.

Definition fun_funcSetoid {X Y} : (X -> Y) -> funcSetoid X Y
  := fun f => f.

Structure Carto := {
  cdom : TypeSetoid;
  ccod : TypeSetoid;
  cfun :> funcSetoid cdom ccod
}.

Inductive funcS_eq X Y (f : funcSetoid X Y) :
  forall Z W, funcSetoid Z W -> Prop :=
  funcS_eqref : forall g : funcSetoid X Y, f == g -> funcS_eq f g.

Program Canonical Structure CartoSetoid :=
  [ Carto | ==: fun F G => @funcS_eq (@cdom F) (@ccod F) (@cfun F) _ _ G ].
Next Obligation.
  split.
  - now intros [F].
  - intros [F] [G] [H]. split. intros x. now rewrite <-H0.
  - intros [F] [G] [H] [H0 H1] [H2 H3]. split. intros x.
    now rewrite <-H3, <-H1.
Defined.

Definition funcS_comp `(f : funcSetoid X Y) `(g : funcSetoid Z W)
  : Y == Z -> funcSetoid X W.
intros H. revert f g. case H. intros f g.
apply (fun_funcSetoid (fun x => g (f x))).
Defined.

Program Definition TypeCat :=
  [ dom: map F => cdom F, cod: map F => ccod F,
    o: map p => let (f,g,H) := p in (Build_Carto (funcS_comp (@cfun f) (@cfun g) H)),
    1: map X => (@Build_Carto X X (fun x => x)) ].
Next Obligation. now intros [d c f] [d0 c0 f0] [E H]. Defined.
Next Obligation. now intros [d c f] [d0 c0 f0] [E H]. Defined.
Next Obligation.
  intros [[df cf f] [dg cg g] H] [[df0 cf0 f0] [dg0 cg0 g0] H0] [E E0].
  simpl in *. destruct E, E0. inversion H. unfold eq in H. destruct H.
   split. revert f g g1 g0 H1 H0. destruct H2.
  (* destruct H0. *)
  simpl in *. intros x. unfold fun_funcSetoid.
  rewrite H1, H2. compute. destruct H0.
  revert cf f g H0 g1 H1 g0 H2. 
  intros cf f g H0. revert f g. destruct H0.
  H0. intros H. case_eq (cf = cf).
  unfold funcS_comp. simpl in *.
  compute.
  case_eq H0.

  destruct H0. split.
  simpl in *. intros x.
  revert f g H1 H2. case H.
  pose (H1 x). 
  unfold funcS_comp.
  simpl.
  revert f g E E0. case H. intros f g.
  revert f0 g0. case H0. intros f0 g0. simpl in *.
  unfold fun_funcSetoid. simpl in *. intros E E0. 
  inversion E. inversion E0. simpl in *.
  revert f g f0 g0 H H0 E E0 g2 H4 H3 H5 g3 H6 g4 H10 g5 H12.
  case H2, H8, H9, H7, H11. intuition. split. simpl in *. intros x.
  
  assumption.
  (* Check existT. *)
  case E. rewrite H12.
  case E.
  

  inversion E. inversion E0. simpl in *.
  revert f g f0 g0 H4 E E0 H6 H10 H12.
  case H, H0, H2, H3. case H9. case H11.
  intros f g f0 g0. intuition. split. simpl in *.
  intros x. 
  simpl in *. inversion E.
  split.
  inversion E. inversion E0. simpl in *. 
  split.
