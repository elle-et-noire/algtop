Generalizable All Variables.
Set Implicit Arguments.
Require Export setoid monoid.

Declare Scope group_scope.
Open Scope setoid_scope.
Open Scope monoid_scope.
Open Scope group_scope.

Obligation Tactic := program_simpl; (try apply \ISE); (try now intros x).

Class LInvertible {X : Setoid} (op : X -> X -> X) e (inv : X -> X) := {
  invl : forall x, op (inv x) x == e
}.

Class RInvertible {X : Setoid} (op : X -> X -> X) e (inv : X -> X) := {
  invr : forall x, op x (inv x) == e
}.

Class Invertible `{X : Setoid} (op : X -> X -> X) e (inv : X -> X) := {
  inv_invl :> LInvertible op e inv;
  inv_invr :> RInvertible op e inv
}.
#[global] Existing Instances inv_invl inv_invr.

Class IsGroupS `(mul : Binop supp) (inv : Map supp supp) e :=
{
  assocg :> Associative mul;
  identrg :> RIdentical mul e;
  invrg :> RInvertible mul e inv
}.

Structure GroupS := {
  gcarrier :> Setoid;
  mulg : Binop gcarrier;
  invg : Map gcarrier gcarrier;
  idg : gcarrier;

  groupsprf : IsGroupS mulg invg idg
}.
#[global] Existing Instance groupsprf.

Arguments mulg {_}.
Arguments invg {_}.
Arguments idg {_}.

Lemma identlg {G} : LIdentical (@mulg G) idg.
Proof.
  split. intros x. rewrite <-identr. rewrite <-(invr (invg x)) at 2.
  now rewrite assoc, <-(assoc idg), invr, identr,
    <-(invr x), <-assoc, invr, identr.
Qed.
#[global] Existing Instance identlg.

Program Coercion grps_mnds (G : GroupS) :=
  [ gcarrier G | *: mulg, 1: idg ].
Next Obligation.
  destruct G as [s mul inv id [A RI RV]]; split;
  intuition || split; intuition.
Defined.

Program Definition ensg_ensm {X : GroupS} (G : {ens X})
  : {ens grps_mnds X} := G.

Notation "[ A | *: op , !: inv , 1: id ]" :=
  (@Build_GroupS A op inv id _)
  (at level 0, A, op, inv, id at level 99) : group_scope.
Notation "[ *: op , !: inv , 1: id ]" := [ _ | *: op, !: inv, 1: id]
  (at level 0, op, inv, id at level 99) : group_scope.
Notation "(  * 'in' G  )" := (@mulg G) : group_scope.
Notation "( * )" := ( * in _ ) : group_scope.
Notation "g * h 'in' G" := (@mulg G g h)
  (at level 40, h at next level, left associativity) : group_scope.
Notation "g * h" := (g * h in _) : group_scope.
Notation "1 'in' G" := (@idg G)
  (at level 0, G at level 99, no associativity) : group_scope.
Notation "1" := (1 in _) : group_scope.
Notation "(  ! 'in' G  ) " := (@invg G) : group_scope.
Notation "( ! )" := ( ! in _ ) : group_scope.
Notation "! g 'in' G" := (@invg G g)
  (at level 35, g at next level, right associativity) : group_scope.
Notation "! g" := ( ! g in _ )
  (at level 35, right associativity) : group_scope.

Program Definition conjg {G : GroupS} := dmap (h : G) g => !g * (h * g).
Next Obligation.
  intros g1 g2 E1 h1 h2 E2. now rewrite E1, E2.
Defined. 
Notation "g ^ h" := (@conjg _ g h) : group_scope.

Lemma invlg {G} : LInvertible ( * in G ) 1 ( ! ).
Proof.
  split. intros x. rewrite <-identr. rewrite <-(invr (!x)) at 1.
  now rewrite assoc, <-(assoc _ x), invr, identr, invr.
Qed.
#[global] Existing Instance invlg.

Section GroupTheory.
  Context {G : GroupS}.
  Implicit Types x y g : G.
  Lemma mulgA : forall {x y z}, x * (y * z) == (x * y) * z.
  Proof. now destruct G as [a b c d [[e] f g]]. Qed.

  Lemma mulg1 : forall x, x * 1 == x.
  Proof. now destruct G as [a b c d [e [f] g]]. Qed.

  Lemma mulgV : forall x, x * !x == 1.
  Proof. now destruct G as [a b c d [e f [g]]]. Qed.

  Lemma mul1g : forall x, 1 * x == x.
  Proof. now destruct (@identlg G). Qed.

  Lemma mulVg : forall x, !x * x == 1.
  Proof. now destruct (@invlg G). Qed.

  Lemma mulgI g {x y} : x * g == y * g -> x == y.
  Proof.
    intros H.
    now rewrite <-identr, <-(identr y), <-(invr g), 2!assoc, H.
  Qed.

  Lemma mulIg g {x y} : g * x == g * y -> x == y.
  Proof.
    intros H.
    now rewrite <-identl, <-(identl y), <-(invl g), <-2!assoc, H.
  Qed.
  
  Lemma mulTg {g x y} : g * x == y -> x == !g * y.
  Proof.
    intros H. apply (@mulIg g). now rewrite assoc, invr, identl.
  Qed.

  Lemma mulgT {g x y} : x * g == y -> x == y * !g.
  Proof.
    intros H. apply (@mulgI g). now rewrite <-assoc, invl, identr.
  Qed.

  Lemma invgK x : !!x == x.
  Proof. apply (@mulgI (!x)). now rewrite invl, invr. Qed.

  Lemma eq_invg_sym {x y} : !x == y -> x == !y.
  Proof. intros H. now rewrite <-H, invgK. Qed.
 
  Lemma invMg {x y} : !(x * y) == !y * !x.
  Proof.
    rewrite <-(identr (!x)). apply mulTg, mulTg.
    now rewrite assoc, invr.
  Qed.

  Lemma invg1 : !(1 in G) == 1.
  Proof.
    rewrite <-(identr (!1)). symmetry; apply mulTg, identl.
  Qed.

  Lemma invg_inj {x y} : x * y == 1 -> y == !x.
  Proof.
    intros H. rewrite <-(identr (!x)). now apply mulTg.
  Qed.
End GroupTheory.

Class IsMorph {G H : GroupS} (f : Map G H) := {
  morph : forall x y, f (x * y) == (f x) * (f y) in H
}.

Structure Morph (G H : GroupS) := {
  homfun :> Map G H;
  homprf : IsMorph homfun
}.
#[global] Existing Instance homprf.

Definition morpheq {X Y} (f g : Morph X Y) :=
  homfun f == homfun g.
Program Canonical Structure MorphSetoid (X Y : GroupS) :=
  [ Morph X Y | ==: morpheq ].

Notation "'hom' 'on' f" := (@Build_Morph _ _ f _)
  (at level 200, no associativity).
Notation "'hom' 'by' f " := (hom on (map by f))
  (at level 200, no associativity).
Notation " 'hom' x => m " := (hom by fun x => m)
  (at level 200, x binder, no associativity) : group_scope.
Notation "G ~~> H" := (@Morph G H)
  (at level 99, no associativity) : group_scope.

Structure Isomorph (G H : GroupS) := {
  isofun :> Morph G H;
  isoprf : Bijective isofun
}.
#[global] Existing Instance isoprf.

Notation "'iso' 'on' f" := (@Build_Isomorph _ _ f _)
  (at level 200, no associativity) : group_scope.
Notation "'iso' x => m " := (iso on hom x => m)
  (at level 200, x binder, no associativity) : group_scope.
Notation "G <~> H" := (@Isomorph G H)
  (at level 95, no associativity) : group_scope.

Program Definition homcomp {G1 G2 G3} (f: G1 ~~> G2) (g: G2 ~~> G3)
  : G1 ~~> G3 := hom on (g o f).
Next Obligation. split. intros x y. simpl. now rewrite 2!morph. Defined.
Notation "g '<o~' f" := (homcomp f g)
  (at level 60, right associativity) : group_scope.

Program Definition isocomp {G1 G2 G3} (f: G1 <~> G2) (g: G2 <~> G3)
  : G1 <~> G3 := iso on (g <o~ f).
Next Obligation.
  split; split; simpl.
  - intros x y Heq. now repeat apply inj in Heq.
  - intros z. destruct (surj g z) as [y E1]. 
    destruct (surj f y) as [x E2]. exists x. now rewrite E1, E2.
Defined.
Notation "g '<o>' f" := (isocomp f g)
  (at level 60, right associativity) : group_scope.

Section HomTheory.
  Context `{f: Morph G H}.
  Lemma morph1 : f 1 == 1.
  Proof.
    apply (mulgI (f 1)). now rewrite <-morph, 2!identl.
  Qed.

  Lemma morphV : forall x, f (!x) == !(f x).
  Proof.
    intros x. rewrite <-(identr (!(f x))).
    apply mulTg. now rewrite <-morph, invr, morph1.
  Qed.
End HomTheory.

Class IsSubg {X : GroupS} (G : {ens X}) := {
  fermg : forall x y : G, G (x * !y);
  idgF : G 1
}.

Structure Subg (X : GroupS) := {
  suppg :> {ens X};
  groupprf : IsSubg suppg
}.
#[global] Existing Instance groupprf.

Notation "< G >" := (@Build_Subg _ G _)
  (at level 200, G at level 0, no associativity) : group_scope.
Notation "{ 'subg' X  }" := (Subg X) : group_scope.

Definition subg_eq {X} (G H : {subg X}) :=
  suppg G == suppg H.
Program Canonical Structure SubgSetoid (X : GroupS) :=
  [ {subg X} | ==: subg_eq ].

Program Canonical Structure suppgM {X : GroupS} 
  : Map {subg X} {ens X} := map x => suppg x.

Section GroupTheory.
  Context {X : GroupS} (G : {subg X}).
  Implicit Types x y : G.
  Lemma invgF x : G (!x).
  Proof.
    rewrite <-identl, (val_sval idgF). apply fermg.
  Qed.

  Lemma mulgF x y : G (x * y).
  Proof.
    rewrite <-(@invgK _ y), 2!(val_sval (invgF _)).
    apply fermg.
  Qed.
End GroupTheory.

Program Coercion grp_grpS `(G : {subg X}) : GroupS :=
  [ G | *: (dmap g h => (@existS _ _ (g * h) (mulgF _ _ _))),
        !: (map g => (@existS _ _ (!g) (invgF _ _))),
        1: (existS idgF) ].
Next Obligation.
  intros g g0 Eg h h0 Eh. unfold sigSeq in *. simpl in *.
  now rewrite Eg, Eh.
Defined.
Next Obligation.
  intros g g0 Eg. unfold sigSeq in *. simpl in *.
  now rewrite Eg.
Defined.
Next Obligation.
  split; split.
  - intros x y z. simpl. unfold sigSeq. simpl.
    now rewrite assoc.
  - intros x. simpl. unfold sigSeq. simpl.
    now rewrite identr.
  - intros x. simpl. unfold sigSeq. simpl.
    now rewrite invr.
Defined.  

Program Definition inclhom {X} {H G : {subg X}}
   (L : H <= G) : H ~~> G := hom on (inclmap L).
Next Obligation.
  split. intros x y. simpl. now unfold sigSeq.
Defined.

Definition conjugate {G : GroupS} :=
  dmap21 (dmmcomp1 imens ((@conjg G)^~)).
Notation "A :^ x" := (conjugate A x)
  (at level 35, right associativity) : group_scope.

Program Definition normaliser {G : GroupS} (A : {ens G})
  := [ x | A :^ x <= A ].
Next Obligation.
  intros x y E. split; intros H [g [a H0]];
  pose (forall_sigS H g) as H1; simpl in *;
  apply H1; exists a; now rewrite E || rewrite <-E.
Defined.

Class IsNormal `(N : {subg G}) := {
  normal : forall {g : G}, N :^ g <= N
}.
Structure Normalsg (X : GroupS) := {
  suppsg :> {subg X};
  nsgprf :> IsNormal suppsg
}.
#[global] Existing Instance nsgprf.

Notation "<| G" := (@Normalsg G)
  (at level 70, no associativity) : group_scope.
Notation "N <<| G" := (@Build_Normalsg G N _)
  (at level 70, no associativity) : group_scope.

Definition nsg_eq {X} (G H : <| X) :=
  suppsg G == suppsg H.
Program Canonical Structure NormalsgSetoid (X : GroupS) :=
  [ <| X | ==: nsg_eq ].

Program Canonical Structure suppsgM {X : GroupS}
  : Map (<| X) {subg X} := map x => suppsg x.

Lemma mulgN `{N : <| X} {n g : X} : N n -> N (n ^ g).
Proof.
  intros Nn. pose (forall_sigS (@normal X N N g) (n^g)).
  simpl in m. apply m. now existsS n.
Qed.

Program Definition imsubg {X Y : GroupS} :=
  dmap (f : Morph X Y) (G : {subg X}) => <(f @: G)>.
Next Obligation.
  split.
  - intros [y0 [g0 H0]] [y1 [g1 H1]]. existsS (g0 * !g1).
    apply fermg. now rewrite morph, morphV, H0, H1.
  - existsS (1 in X). apply idgF. now rewrite morph1.
Defined.
Next Obligation.
  intros f g H A B. now apply setoid.imens_obligation_2.
Defined.

Program Definition preimsubg {X Y : GroupS} :=
  dmap (f : Morph X Y) (H : {subg Y}) => <(f -@: H)>.
Next Obligation.
  split; simpl.
  - intros [x Hx] [y Hy]. simpl in *. rewrite morph, morphV.
    apply (mulgF H (existS Hx) (existS (invgF _ (existS Hy)))).
  - rewrite morph1. apply idgF.
Defined.
Next Obligation.
  intros f g H A B. now apply setoid.preimens_obligation_2.
Defined.

Program Definition preimnsg {X Y : GroupS} :=
  dmap (f : Morph X Y) (N : <| Y) => (preimsubg f N) <<| X.
Next Obligation.
  split. simpl. intros g [h [[a Ha] Hh]]. simpl in *.
  rewrite Hh, !morph, morphV. now apply mulgN.
Defined.
Next Obligation.
  intros f g H A B. now apply preimsubg_obligation_2.
Defined.

Program Definition idnsg {X : GroupS} := <[ens 1]> <<| X.
Next Obligation.
  split; simpl; try reflexivity. intros [a Ha] [b Hb].
  simpl in *. now rewrite Ha, Hb, identl, invg1.
Defined.
Next Obligation.
  split. intros g [a [[i Hi] HN]]. simpl in *. 
  now rewrite HN, Hi, identl, invl.
Defined.

Notation "< 1 >" := (idnsg) : group_scope.

Program Definition kernel {X Y : GroupS} :=
  map (f : Morph X Y) => preimnsg f <1>.
Next Obligation.
  intros f f0 Ef. split; intros [a Ha]; simpl in *;
  rewrite <-Ha; [symmetry|]; now apply Ef.
Defined.

Definition coset_eq `{G : {subg X}} (x y : X) :=
  G (x * !y).
Program Definition Coset `(G : {subg X}) :=
  [ X | ==: (@coset_eq _ G) ].
Next Obligation.
  split; unfold coset_eq.
  - intros x. rewrite invr. apply idgF.
  - intros x y H. pose (invgF _ (existS H)) as H0.
    simpl in H0. now rewrite invMg, invgK in H0.
  - intros x y z H1 H2.
    pose (mulgF _ (existS H1) (existS H2)) as H.
    simpl in H.
    now rewrite assoc, <-(assoc x), mulVg, mulg1 in H.
Defined.
Notation "X / G" := (@Coset X G) : group_scope.

Program Definition CosetGroup `(N : <| X) :=
  [ X / N | *: (dmap xN yN => xN * yN),
            !: (map xN => !xN),
            1: 1 ].
Next Obligation.
  intros x x0 Ex y y0 Ey. unfold coset_eq in *.
  rewrite invMg, assoc, <-(assoc x), <-(assoc).
  rewrite <-(mulg1 x), <-(mulVg x0), (assoc x), <-(assoc _ x0).
  pose (forall_sigS (mulgF _ (existS Ex))).
  simpl in m. apply m. pose (mulgN(g := !x0) Ey).
  simpl in m0. now rewrite invgK in m0.
Defined.
Next Obligation.
  intros x x0 E. unfold coset_eq in *.
   rewrite invgK.
  pose (invgF _ (existS E)). simpl in m.
  rewrite (invMg), invgK in m.
  pose (mulgN(g := x0) m). simpl in m0.
  now rewrite !(assoc), mulVg, mul1g in m0.
Defined.
Next Obligation.
  split; split; simpl; unfold coset_eq.
  - intros x y z. rewrite assoc, mulgV. apply idgF.
  - intros x. rewrite mulg1, mulgV. apply idgF.
  - intros x. rewrite mulgV, mul1g, invg1. apply idgF.
Defined.

Notation "X </> N" := (@CosetGroup X N)
  (at level 35, right associativity) : group_scope.

Close Scope group_scope.
Close Scope setoid_scope.