Generalizable All Variables.
Set Implicit Arguments.
Require Export setoid monoid.

Declare Scope group_scope.
Open Scope setoid_scope.
Open Scope monoid_scope.
Open Scope group_scope.

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

Class IsGroup `(mul : Binop supp) (inv : Ope supp) e :=
{
  assocg :> Associative mul;
  identrg :> RIdentical mul e;
  invrg :> RInvertible mul e inv
}.

Structure Group := {
  gcarrier :> Setoid;
  mulg : Binop gcarrier;
  invg : Ope gcarrier;
  idg : gcarrier;

  groupsprf : IsGroup mulg invg idg
}.
#[global] Existing Instance groupsprf.

Arguments mulg {_}.
Arguments invg {_}.
Arguments idg {_}.

Lemma identlg {G} : LIdentical (@mulg G) idg.
Proof.
  split. intros x. rewrite <-identr.
  rewrite <-(invr (invg x)) at 2.
  now rewrite assoc, <-(assoc idg), invr, identr,
    <-(invr x), <-assoc, invr, identr.
Qed.
#[global] Existing Instance identlg.

Program Coercion grps_mnds (G : Group) :=
  [ gcarrier G | *: mulg, 1: idg ].
Next Obligation.
  destruct G as [s mul inv id [A RI RV]]; split;
  [|split]; intuition.
Defined.

Program Definition ensg_ensm {X : Group} (G : {ens X})
  : {ens grps_mnds X} := G.

Notation "[ A | *: op , !: inv , 1: id ]" :=
  (@Build_Group A op inv id _)
  (at level 0, A, op, inv, id at level 99) : group_scope.
Notation "[ *: op , !: inv , 1: id ]"
  := [ _ | *: op, !: inv, 1: id]
  (at level 0, op, inv, id at level 99) : group_scope.
Notation "(  * 'in' G  )" := (@mulg G) : group_scope.
Notation "( * )" := ( * in _ ) : group_scope.
Notation "g * h 'in' G" := (@mulg G g h)
  (at level 40, h at next level, left associativity)
  : group_scope.
Notation "g * h" := (g * h in _) : group_scope.
Notation "1 'in' G" := (@idg G)
  (at level 0, G at level 99, no associativity) : group_scope.
Notation "1" := (1 in _) : group_scope.
Notation "(  ! 'in' G  ) " := (@invg G) : group_scope.
Notation "( ! )" := ( ! in _ ) : group_scope.
Notation "! g 'in' G" := (@invg G g)
  (at level 35, g at next level, right associativity,
  format "! g  'in'  G") : group_scope.
Notation "! g" := ( ! g in _ )
  (at level 35, right associativity,
  format "! g") : group_scope.

Program Definition conjg {G : Group} :=
  dmap (h : G) g => !g * (h * g).
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
  Context {G : Group}.
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

  Lemma mulgI g {x y} : (x == y) == (x * g == y * g).
  Proof.
    split; intros H; [|rewrite <-mulg1, <-(mulg1 y),
    <-(invr g), 2!assoc]; now rewrite H.
  Qed.

  Lemma mulIg g {x y} : (x == y) == (g * x == g * y).
  Proof.
    split; intros H; [|rewrite <-mul1g, <-(mul1g y),
    <-(invl g), <-2!assoc]; now rewrite H.
  Qed.

  Lemma mulTg {g x y} : (x == !g * y) == (g * x == y).
  Proof.
    split; intros H.
    - now rewrite H, assoc, mulgV, mul1g.
    - now rewrite <-H, assoc, mulVg, mul1g.
  Qed.

  Lemma mulgT {g x y} : (x == y * !g) == (x * g == y).
  Proof.
    split; intros H.
    - now rewrite H, <-assoc, mulVg, mulg1.
    - now rewrite <-H, <-assoc, mulgV, mulg1.
  Qed.

  Lemma invgK x : !!x == x.
  Proof. apply (@mulgI (!x)). now rewrite invl, invr. Qed.

  Lemma eq_invg_sym {x y} : (!x == y) == (x == !y).
  Proof.
    split; intros H; now rewrite2 H; rewrite invgK.
  Qed.

  Lemma invMg {x y} : !(x * y) == !y * !x.
  Proof.
    rewrite <-(identr (!x)). apply mulTg, mulTg.
    now rewrite assoc, invr.
  Qed.

  Lemma invg1 : !(1 in G) == 1.
  Proof.
    rewrite <-(identr (!1)). symmetry; apply mulTg, identl.
  Qed.

  Lemma invg_inj {x y} : (y == !x) == (x * y == 1).
  Proof.
    split; intros H.
    - now rewrite H, mulgV.
    - now rewrite <-(mulg1 (!x)), <-H, assoc, mulVg, mul1g.
  Qed.

  Lemma invJK x y : ((x ^ y) ^ !y) == x.
  Proof.
    simpl. now rewrite invgK, !assoc, 
      mulgV, mul1g, <-assoc, mulgV, mulg1.
  Qed. 
End GroupTheory.

Class IsMorph {G H : Group} (f : Map G H) := {
  morph : forall x y, f (x * y) == (f x) * (f y) in H
}.

Structure Morph (G H : Group) := {
  homfun :> Map G H;
  homprf : IsMorph homfun
}.
#[global] Existing Instance homprf.

Notation "'hom' 'on' f" := (@Build_Morph _ _ f _)
  (at level 200, no associativity).
Notation "'hom' 'by' f " := (hom on (map by f))
  (at level 200, no associativity).
Notation " 'hom' x => m " := (hom by fun x => m)
  (at level 200, x binder, no associativity) : group_scope.
Notation "G ~~> H" := (@Morph G H)
  (at level 99, no associativity) : group_scope.

Definition morpheq {X Y} (f g : Morph X Y) :=
  homfun f == homfun g.
Program Canonical Structure MorphSetoid (X Y : Group) :=
  [ Morph X Y | ==: morpheq ].
Notation "[ G ~> H ]" := (@MorphSetoid G H)
  (at level 0, G, H at level 99, no associativity) : group_scope.

Structure Isomorph (G H : Group) := {
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
    now rewrite (mulgI (f 1)), <-morph, 2!mul1g.
  Qed.

  Lemma morphV : forall x, f (!x) == !(f x).
  Proof.
    intros x. now rewrite <-(mulg1 (!f x)), mulTg,
     <-morph, invr, morph1.
  Qed.
End HomTheory.

Class IsSubg {X : Group} (G : {ens X}) := {
  fermg : forall x y : G, G (x * !y);
  idgF : G 1
}.

Structure Subg (X : Group) := {
  suppg :> {ens X};
  groupprf : IsSubg suppg
}.
#[global] Existing Instance groupprf.

Notation "< G >" := (@Build_Subg _ G _)
  (at level 200, G at level 0, no associativity) : group_scope.
Notation "{ 'subg' X }" := (@Subg X)
  (at level 0, format "{ 'subg'  X }") : group_scope.

Definition subg_eq {X} (G H : {subg X}) :=
  suppg G == suppg H.
Program Canonical Structure SubgSetoid (X : Group) :=
  [ {subg X} | ==: subg_eq ].
Notation "[ 'subg' X ]" := (@SubgSetoid X)
  (at level 0, format "[ 'subg'  X ]") : group_scope.
Program Canonical Structure suppgM {X : Group} 
  : Map {subg X} {ens X} := map x => suppg x.

Definition subgconf `(G : {subg X}) := fun x => (suppg G) x.

Section GroupTheory.
  Context {X : Group} {G : {subg X}}.
  Implicit Types x y : G.
  Lemma invgF x : G (!x).
  Proof.
    rewrite <-mul1g, (val_sval idgF). apply fermg.
  Qed.

  Lemma mulgF x y : G (x * y).
  Proof.
    rewrite <-(invgK y), 2!(val_sval (invgF _)).
    apply fermg.
  Qed.
End GroupTheory.

Program Coercion grp_grpS `(G : {subg X}) : Group :=
  [ G | *: (dmap g h => $[_, mulgF g h]),
        !: (map g => $[_, invgF g]),
        1: $[_, idgF] ].
Next Obligation.
  intros g g0 Eg h h0 Eh. simpeq. now rewrite Eg, Eh.
Defined.
Next Obligation.
  intros g g0 Eg. simpeq. now rewrite Eg.
Defined.
Next Obligation.
  split; split; intros; simpeq;
  now rewrite assoc || rewrite mulg1 || rewrite mulgV.
Defined.

Program Definition inclhom {X} {H G : {subg X}}
   (L : H <= G) : H ~~> G := hom on (inclmap L).
Next Obligation.
  split. intros x y. now simpeq.
Defined.

Program Canonical Structure IsSubgM {X : Group} :=
  map by (@IsSubg X).
Next Obligation.
  intros A A0 E. split; intros [C I]; split; simpl;
  try (now rewrite map_comap in I; rewrite2_in E I);
  intros [x Hx] [y Hy]; simpl; rewrite map_comap;
  rewrite map_comap in Hx; rewrite map_comap in Hy;
  [rewrite <-E in * | rewrite E in *];
  simpl in *; sapply (C $[_, Hx] $[_, Hy]).
Defined.

Program Definition subgTfor (X : Group) := <(ensTfor X)>.

Program Definition subgI {X} (H0 H1 : {subg X})
  := <(H0 :&: H1)>.
Next Obligation.
  split.
  - intros [x [H0x H1x]] [y [H0y H1y]]. split; simpl.
  + apply (fermg $[_, H0x] $[_, H0y]).
  + apply (fermg $[_, H1x] $[_, H1y]).
  - split; simpl; apply idgF.
Defined.

Lemma subgIInf_subg {X : Group} (S : {ens {ens X}}) :
  (forall U, S U -> @IsSubg X U) -> IsSubg (ensIInf S).
Proof.
  intros H. split.
  - intros [x Hx] [y Hy]. simpl in *.
    intros [U HU]. simpl. destruct (H U HU).
    sapply (fermg0 $[_, Hx $[_, HU]] $[_, Hy $[_, HU]]).
  - intros [U HU]. destruct (H $[_, HU]); now simpl.
Defined.

Program Definition generated {X : Group} (A : {ens X}) :=
  <(ensIInf [ B : {ens X} | IsSubg B /\ A <= B ])>.
Next Obligation.
  intros B B0 E. split; intros [H H0]; split;
  try rewrite map_comap; now rewrite2 E.
Defined.
Next Obligation.
  apply subgIInf_subg. now intros U [Usg AB].
Defined.

Lemma gensubg_eq_subg {X : Group} {A : {ens X}} : 
  IsSubg A -> A == generated A.
Proof.
  intros H a a0 E. rewrite E. split; intros H0.
  - intros U. destruct U. destruct m. 
    now pose (d $[_, H0]).
  - simpl in *. sapply (forall_sigS H0).
    split; intuition. now destruct x.
Qed.

Lemma gen_compat_lt {X : Group} {A B : {ens X}} :
  A <= B -> generated A <= generated B.
Proof.
  intros H a U. destruct U. simpl in *.
  destruct m. destruct a. simpl in *.
  sigapply m. split; intuition.
  apply (H1 (inclmap H x)).
Qed.

Definition conjugate {G : Group} :=
  dmap21 (imens o1 ((@conjg G)^~)).
Notation "A :^ x" := (conjugate A x)
  (at level 35, right associativity) : group_scope.

Program Definition normaliser {G : Group} (A : {ens G})
  := [ x | A :^ x <= A ].
Next Obligation.
  intros x y E. split; intros H [g [a H0]];
  sigapply H; exists a; now rewrite2 E.
Defined.

Class IsNormal `(N : {subg G}) := {
  normal : forall g : G, N :^ g <= N
}.

Structure Normalsg (X : Group) := {
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
Program Canonical Structure NormalsgSetoid
  (X : Group) := [ <| X | ==: nsg_eq ].
Notation "[ 'nsg' X ]" := (@NormalsgSetoid X)
  (at level 0, format "[ 'nsg'  X ]") : group_scope.
Program Canonical Structure suppsgM {X : Group}
  : Map (<| X) {subg X} := map x => suppsg x.

Lemma normalJF `{N : <| X} {n g : X} : N n -> N (n ^ g).
Proof.
  intros Nn. sigapply (normal(g := g)).
  now existsS n.
Qed.

Lemma normalVJF `{N : <|X} {n} g : N (n ^ g) -> N n.
Proof.
  intros Nng. rewrite <-(invJK _ g). now apply normalJF.
Qed. 

Program Definition imsubg {X Y : Group} :=
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

Notation "f <@> G" := (@imsubg _ _ f G)
  (at level 24, right associativity) : group_scope.

Program Definition preimsubg {X Y : Group} :=
  dmap (f : Morph X Y) (H : {subg Y}) => <(f -@: H)>.
Next Obligation.
  split; simpl.
  - intros [x Hx] [y Hy]. simpl in *. rewrite morph, morphV.
    apply (mulgF $[_, Hx] $[_, invgF $[_, Hy]]).
  - rewrite morph1. apply idgF.
Defined.
Next Obligation.
  intros f g H A B. now apply setoid.preimens_obligation_2.
Defined.

Notation "f <-@> G" := (@preimsubg _ _ f G)
  (at level 24, right associativity) : group_scope.

Program Definition preimnsg {X Y : Group} :=
  dmap (f : Morph X Y) (N : <| Y) => (preimsubg f N) <<| X.
Next Obligation.
  split. simpl. intros g [h [[a Ha] Hh]]. simpl in *.
  rewrite Hh, !morph, morphV. now apply normalJF.
Defined.
Next Obligation.
  intros f g H A B. now apply preimsubg_obligation_2.
Defined.

Program Definition idnsg {X : Group} := <[ == 1]> <<| X.
Next Obligation.
  split; simpl; try reflexivity. intros [a Ha] [b Hb].
  simpl in *. now rewrite Ha, Hb, identl, invg1.
Defined.
Next Obligation.
  split. intros g [a [[i Hi] HN]]. simpl in *. 
  now rewrite HN, Hi, identl, invl.
Defined.

Notation "<1>" := (idnsg) : group_scope.

Program Definition kernel {X Y : Group} :=
  map (f : Morph X Y) => preimnsg f <1>.
Next Obligation. intros f f0 Ef. now rewrite Ef. Defined.

Definition coset_eq `{G : {subg X}} (x y : X) :=
  G (x * !y).
#[global] Hint Unfold coset_eq : eq.
Program Definition Coset `(G : {subg X}) :=
  [ X | ==: @coset_eq _ G ].
Next Obligation.
  split; simpeq.
  - intros x. rewrite invr. apply idgF.
  - intros x y H. rewrite <-(invgK y), <-invMg.
    apply (invgF $[_, H]).
  - intros x y z H1 H2.
    rewrite <-(mulg1 x), <-(mulVg y), assoc, <-assoc.
    apply (mulgF $[_, H1] $[_, H2]).
Defined.
Notation "X / G" := (@Coset X G) : group_scope.

Program Definition projmap `{G : {subg X}} : Map X (X / G)
  := map x => x.
Next Obligation.
  intros x x0 E. simpeq. rewrite E, mulgV. apply idgF.
Defined.

Program Definition CosetGroup `(N : <| X) :=
  [ X / N | *: (dmap xN yN => xN * yN),
            !: (map xN => !xN),
            1: 1 ].
Next Obligation.
  intros x x0 Ex y y0 Ey. simpeq_all.
  rewrite invMg, assoc, <-(assoc x), <-(assoc).
  rewrite <-(mulg1 x), <-(mulVg x0), (assoc x), <-(assoc _ x0).
  sigapply (mulgF $[_, Ex]). rewrite <-(invgK x0) at 1.
  now apply normalJF.
Defined.
Next Obligation.
  intros x x0 E. simpeq_all. rewrite invgK.
  apply (normalVJF (!x0)). simpl.
  rewrite <-assoc, mulgV, mulg1, <-invMg.
  sapply (invgF $[_, E]).
Defined.
Next Obligation.
  split; split; simpeq; intros.
  - rewrite assoc, mulgV. apply idgF.
  - rewrite mulg1, mulgV. apply idgF.
  - rewrite mulgV, mul1g, invg1. apply idgF.
Defined.

Notation "X </> N" := (@CosetGroup X N)
  (at level 35, right associativity) : group_scope.

Program Definition projhom `{N : <| G} : G ~~> G </> N
  := hom on projmap.

Lemma projhom_surj `{N : <| G} : Surjective (@projhom _ N).
Proof.
  split. intros y. exists y. simpeq. rewrite mulgV. apply idgF.
Qed.
#[global] Existing Instance projhom_surj.

Lemma projhom_ker `{N : <| G} (g : G)
  : N g == (@projhom _ N g == 1).
Proof. simpeq. now rewrite invg1, mulg1. Qed.

Program Definition Iso1 `(f : G ~~> H) 
  : (G </> kernel f) <~> (f <@> subgTfor G)
  := iso x => $[f x, _].
Next Obligation. now existsS x. Defined.
Next Obligation.
  intros x x0 E. simpeq_all.
  now rewrite <-(invgK (f x0)), <-(mul1g (!! f x0)), mulgT,
  <-morphV, <-morph.
Defined.
Next Obligation.
  split. intros x y. simpeq. apply morph.
Defined.
Next Obligation.
  split; split.
  - intros x y E. simpeq_all.
    now rewrite morph, morphV, <-mulgT, mul1g, invgK.
  - intros [y [[x T] Hx]]. exists x. now simpeq_all.
Defined.

Program Definition commg {G : Group} : Binop G :=
  dmap (x : G) y => !x * x ^ y.
Next Obligation.
  intros x x0 E y y0 E0. now rewrite E, E0.
Defined.
Notation "[ g , h ]" := (@commg _ g h)
  (at level 0, g, h at level 99, format "[ g ,  h ]")
  : group_scope.

Program Definition commorig {G : Group} (A B : {ens G}) :=
  [ g : G | exists (a : A) (b : B), g == [a, b] ].
Next Obligation.
  intros C C0 E. simpeq_all. split; intros [a [b H]];
  exists a, b; now rewrite2 E.
Defined.

Definition commutator {G : Group} (A B : {ens G}) :=
  generated (commorig A B).
Notation "[: A , B :]" := (@commutator _ A B)
  (at level 0, A, B at level 99, format "[: A  ,  B :]")
  : group_scope. 

Program Definition derived (G : Group) := 
  [:subgTfor G, subgTfor G:] <<| G.
Next Obligation.
  split. intros g [h [[a H] E]] U. simpl. pose (H U).
  rewrite E. simpl. destruct U. destruct m0.
  pose (Usg := Build_Subg i). simpl in *. 
  pose (forall_sigS d). simpl in m0.
  assert (sval (!a * (!g * (a * g) ))).
  { apply m0. now exists (@Build_sigS _ idTmap a I)
  , (@Build_sigS _ idTmap g I). }
  pose (@mulgF _ Usg $[_, m] $[_, H0]). simpl in m1.
  now rewrite assoc, mulgV, mul1g in m1.
Defined.

Class Commute {X : Setoid} (op : X -> X -> X) := {
  commute : forall a b, op a b == op b a
}.

Definition IsCommgrp (G : Group) := Commute (@mulg G).

Lemma CG_commg1 {G : Group}
 : IsCommgrp G == (forall x y : G, [x, y] == 1).
Proof.
  split; intros H; simpl in *.
  - intros x y. rewrite sym, !mulTg, mulg1. now destruct H.
  - split. intros a b. pose (H b a) as H0.
    now rewrite sym, !mulTg, mulg1 in H0.
Qed.

Lemma quotDG_comm (G : Group) : IsCommgrp (G </> derived G).
Proof.
  split. intros a b.
  destruct (surj projhom a) as [a0 Ha].
  destruct (surj projhom b) as [b0 Hb].
  rewrite Ha, Hb, <-(invgK (_ * projhom a0)), <-(mulg1 (!!_)),
    mulTg, invMg, <-assoc, <-!morphV, <-!morph, <-projhom_ker.
  intros [U [H H0]]. sigapply H0. now exists (inT a0), (inT b0).
Defined.

Lemma hom_hold_comm `{f : G ~~> H} {x y : G}
  : f [x, y] == [f x, f y].
Proof. simpl. now rewrite !morph, !morphV. Qed.

Lemma quot_comm_NDG `(N : <| G) : 
  IsCommgrp (G </> N) -> derived G <= N.
Proof.
  intros H.
  assert (commorig (subgTfor G) (subgTfor G) <= N). {
    rewrite CG_commg1 in H.
    intros a. destruct a. destruct m. destruct e.
    simpl. rewrite e, projhom_ker.
    rewrite <-(H (projhom x) (projhom x0)).
    apply hom_hold_comm.
  } 
  rewrite (gensubg_eq_subg(A := N));
  [now apply gen_compat_lt | intuition].
Qed. 

Close Scope group_scope.
Close Scope setoid_scope.