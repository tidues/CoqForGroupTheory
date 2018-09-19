Add LoadPath "~/Dropbox/UB/2018Fall/MTH519/proofs/coqProof".
Load Operators.
Require Import ZArith.
Require Import ZArith.Znat.
Require Import PArith.Pnat.
Require Import PArith.

(*** start: basic algebraic structures ***)
Section Algebras.

Inductive IsSemigroup {A : Set}{mult : Op2 A} : Prop := isSemiG
{associative : Associative A mult}.

Inductive IsMonoid {A : Set}{e : A}{mult : Op2 A} : Prop := isMd
{isSemigroup : IsSemigroup (A:=A)(mult:=mult);
identity : Identity A mult e}.

Inductive IsGroup {A : Set}{e : A}{inv : Op1 A}{mult : Op2 A} : Prop := isG
{isMonoid : IsMonoid (A:=A) (e:=e) (mult:=mult);
inverse : Inverse A mult e inv}.

End Algebras.
(*** end: basic algebraic structures ***)


(*** start: group and its properties ***)
Module Type Group.
  
  Import Z.
  Import Nat2Z.
  Import Z2Nat.
  Import Pos.
  Import Pos2Nat.
  Import SuccNat2Pos.
  Import Pos2Z.

  (*** start: group definition ***)
  Parameter A : Set.
  Parameter e : A.
  Parameter mult : A -> A -> A.
  Parameter inv : A -> A.
  Axiom isGroup : IsGroup (A:=A) (e:=e) (inv:=inv) (mult:=mult).

  Definition inv_l : InverseL A mult e inv := proj1 (isGroup.(inverse)).
  Definition inv_r : InverseR A mult e inv := proj2 (isGroup.(inverse)).
  Definition id_l : IdentityL A mult e := proj1 isGroup.(isMonoid).(identity).
  Definition id_r : IdentityR A mult e := proj2 isGroup.(isMonoid).(identity).
  Definition asso : Associative A mult := isGroup.(isMonoid).(isSemigroup).(associative).
  
  Notation "a * b" := (mult a b).
  Notation "a '" := (inv a) (at level 20).
  (*** end: group definition ***)


  Hint Resolve inv_l inv_r id_l id_r asso : gsimpls.
  Hint Rewrite inv_l inv_r id_l id_r asso : gsimplw.


  (*** start: basic group properties ***)
  Lemma ainvinv : forall (a : A), (a ') ' = a.
  Proof.
    intros.
    pattern a at 2.
    rewrite <- (id_l a).
    rewrite <- (inv_l (a ')).
    autorewrite with gsimplw.
    trivial.
  Qed.

  Lemma einv : e ' = e.
  Proof.
    pattern e at 2.
    rewrite <- (inv_l e).
    rewrite (id_r (e ')).
    trivial.
  Qed.

  Lemma abinv : forall (a b : A), (a * b) ' = b ' * a '.
  Proof.
    intros.
    rewrite <- (id_r (b ' * a ')).
    rewrite <- (inv_r (a * b)).
    autorewrite with gsimplw.
    rewrite <- (asso (a ') a (b * (a * b) ')).
    rewrite (inv_l a).
    rewrite (id_l (b * (a * b) ')).
    rewrite <- (asso (b ') b ((a * b) ')).
    rewrite (inv_l b).
    rewrite (id_l ((a * b) ')).
    trivial.
  Qed.
  (*** end: basic group properties ***)


  (*** start: power representation of cyclic element ***)
  Fixpoint powh (a : A)(n : nat)(b : bool){struct n} : A :=
    match n with
    | O => e
    | S p => match b with 
             | true => a * (powh a p b)
             | false => a ' * (powh a p b)
             end
    end.

  Definition pow (a : A)(z : Z) : A :=
    match z with
    | Z0 => powh a 0 true
    | Zpos p => powh a (to_nat p) true
    | Zneg p => powh a (to_nat p) false
    end.
  (*** end: power representation of cyclic element ***)


  (*** start: a bunch of properties for power representation ***)
  Lemma powacomm : forall (a : A)(n : nat)(b : bool), 
      a * (powh a n b) = (powh a n b) * a.
  Proof.
    intros.
    case b.
    induction n.
    simpl.
    autorewrite with gsimplw; trivial.
    simpl.
    autorewrite with gsimplw.
    rewrite <- IHn.
    trivial.
    induction n.
    simpl.
    autorewrite with gsimplw; trivial.
    simpl.
    autorewrite with gsimplw.
    rewrite <- IHn.
    rewrite <- (asso (a ') a (powh a n false)).
    rewrite <- (asso a (a ') (powh a n false)).
    rewrite (inv_l a).
    rewrite (inv_r a).
    trivial.
  Qed.

  Lemma powa'comm : forall (a : A)(n : nat)(b : bool), 
    (a ') * (powh a n b) = (powh a n b) * (a ').
  Proof.
    intros.
    case b.
    induction n.
    simpl.
    autorewrite with gsimplw; trivial.
    simpl.
    autorewrite with gsimplw.
    rewrite <- IHn.
    rewrite <- (asso (a ') a (powh a n true)).
    rewrite <- (asso a (a ') (powh a n true)).
    rewrite (inv_l a).
    rewrite (inv_r a).
    trivial.
    induction n.
    simpl.
    autorewrite with gsimplw; trivial.
    simpl.
    autorewrite with gsimplw.
    rewrite <- IHn.
    trivial.
  Qed.

  Lemma powinv : forall (a : A)(z : Z), (pow a z) ' = pow a (-z).
  Proof.
    intros.
    induction z.
    simpl.
    apply einv.
    simpl.
    induction (to_nat p).
    simpl.
    apply einv.
    simpl.
    rewrite (abinv a (powh a n true)).
    rewrite IHn.
    rewrite (powa'comm a n false); trivial.
    simpl.
    induction (to_nat p).
    simpl.
    apply einv.
    simpl.
    rewrite (abinv (a ') (powh a n false)).
    rewrite IHn.
    rewrite (ainvinv a).
    rewrite (powacomm a n true); trivial.
  Qed.


  Hint Rewrite inj_add add_1_l Pos2Nat.inj_succ add_succ_l : posrewrite.

  Lemma powinv1 : forall (a : A)(z : Z), (pow a z) ' = pow (a ') z.
  Proof.
    intros.
    case z.
    simpl. apply einv.
    apply peano_ind.
    simpl. autorewrite with gsimplw. trivial.
    intros. simpl. autorewrite with posrewrite. simpl.
    simpl in H. rewrite (abinv a (powh a (to_nat p) true)).
    rewrite H. rewrite (powacomm (a ') (to_nat p) true). trivial.
    apply peano_ind.
    simpl. autorewrite with gsimplw. trivial.
    intros. simpl. autorewrite with posrewrite. simpl.
    rewrite (abinv (a ') (powh a (to_nat p) false)).
    rewrite (powa'comm (a ') (to_nat p) false).
    rewrite (ainvinv a).
    simpl in H. rewrite H. trivial.
  Qed.

  Lemma powinv2 : forall (a : A)(z : Z), pow a (-z) = pow (a ') z.
  Proof.
    intros.
    rewrite <- (powinv1 a z).
    rewrite (powinv a z). trivial.
  Qed.

  Lemma ppcomm : forall (a : A)(p p0 : positive),
    pow a (pos p) * pow a (pos p0) = pow a (pos p0) * pow a (pos p).
  Proof.
    intros.
    generalize p.
    apply peano_ind.
    simpl. rewrite (id_r a). rewrite (powacomm a (to_nat p0) true). trivial.
    intros. simpl. autorewrite with posrewrite. simpl.
    autorewrite with gsimplw.
    rewrite <- (asso (powh a (to_nat p0) true) a (powh a (to_nat p1) true)).
    rewrite <- (powacomm a (to_nat p0) true).
    rewrite (asso a (powh a (to_nat p0) true) (powh a (to_nat p1) true)).
    simpl in H.
    rewrite H.
    trivial.
  Qed.

  Lemma pncomm : forall (a : A)(p p0 : positive),
    pow a (pos p) * pow a (neg p0) = pow a (neg p0) * pow a (pos p).
  Proof.
    intros.
    generalize p.
    apply peano_ind.
    simpl. rewrite (id_r a). rewrite (powacomm a (to_nat p0) false). trivial.
    intros. simpl. autorewrite with posrewrite. simpl.
    autorewrite with gsimplw.
    rewrite <- (asso (powh a (to_nat p0) false) a (powh a (to_nat p1) true)).
    rewrite <- (powacomm a (to_nat p0) false).
    rewrite (asso a (powh a (to_nat p0) false) (powh a (to_nat p1) true)).
    simpl in H.
    rewrite H. trivial.
  Qed.

  Lemma powcomm : forall (a : A)(z1 z2 : Z),
    (pow a z1) * (pow a z2) = (pow a z2) * (pow a z1).
  Proof.
    intros.
    case z1.
    simpl. rewrite (id_l (pow a z2)). rewrite (id_r (pow a z2)). trivial.
    intros. case z2.
    simpl. rewrite (id_r (powh a (to_nat p) true)).
    rewrite (id_l (powh a (to_nat p) true)). trivial.
    intros. apply ppcomm.
    intros. apply pncomm.
    case z2.
    intros. simpl. rewrite (id_r (powh a (to_nat p) false)).
    rewrite (id_l (powh a (to_nat p) false)). trivial.
    intros. rewrite (pncomm a p p0). trivial.
    intros. rewrite <- (opp_pos p). rewrite <- (opp_pos p0).
    rewrite (powinv2 a (pos p0)). rewrite (powinv2 a (pos p)).
    rewrite (ppcomm (a ') p0 p). trivial.
  Qed.

  Lemma ppmult : forall (a : A)(p0 p : positive), 
    pow a (pos p0) * pow a (pos p) = pow a (pos p0 + pos p).
  Proof.
    intros.
    rewrite <- (inj_add p0 p).
    generalize p0.
    apply peano_ind.
    rewrite add_1_l.
    simpl.
    rewrite (Pos2Nat.inj_succ p).
    simpl. rewrite (id_r a). trivial.
    intros. rewrite (add_succ_l p1 p).
    simpl. rewrite (Pos2Nat.inj_succ p1). rewrite (Pos2Nat.inj_succ (p1 + p)).
    simpl. rewrite (asso a (powh a (to_nat p1) true) (powh a (to_nat p) true)).
    simpl in H. rewrite H. trivial.
  Qed.

  Lemma pnmult : forall (a : A)(p0 p : positive), 
    pow a (pos p0) * pow a (neg p) = pow a (pos p0 + neg p).
  Proof.
    intros. rewrite (add_pos_neg p0 p).
    generalize (pos_sub_discr p0 p).
    case (pos_sub p0 p).
    intros.
    rewrite H.
    simpl.
    generalize p.
    apply peano_ind.
    simpl. autorewrite with gsimplw. trivial.
    intros.
    rewrite (Pos2Nat.inj_succ p1).
    simpl. rewrite <- (asso (a * powh a (to_nat p1) true) (a ') (powh a (to_nat p1) false)).
    rewrite (asso a (powh a (to_nat p1) true) (a ')).
    rewrite <- (powa'comm a (to_nat p1) true).
    rewrite <- (asso a (a ') (powh a (to_nat p1) true)).
    rewrite (inv_r a). rewrite (id_l (powh a (to_nat p1) true)). trivial.
    intros. rewrite H. simpl.
    generalize p.
    apply peano_ind.
    rewrite add_1_l.
    rewrite (Pos2Nat.inj_succ p1).
    simpl. rewrite (id_r (a ')). rewrite (powacomm a (to_nat p1) true).
    rewrite (asso (powh a (to_nat p1) true) a (a ')). rewrite (inv_r a).
    auto with gsimpls.
    intros. autorewrite with posrewrite. simpl.
    autorewrite with gsimplw. 
    rewrite <- (asso (powh a (to_nat (p2 + p1)) true) (a ') (powh a (to_nat p2) false)).
    rewrite <- (powa'comm a (to_nat (p2 + p1)) true).
    rewrite (asso (a ') (powh a (to_nat (p2 + p1)) true) (powh a (to_nat p2) false)).
    rewrite H0. rewrite <- (asso a (a ') (powh a (to_nat p1) true)).
    rewrite (inv_r a). auto with gsimpls.
    intros. rewrite H. simpl.
    generalize p0.
    apply peano_ind.
    autorewrite with posrewrite. simpl. rewrite (id_r a).
    rewrite <- (asso a (a ') (powh a (to_nat p1) false)).
    rewrite (inv_r a). auto with gsimpls.
    intros. autorewrite with posrewrite. simpl.
    rewrite <- (asso (a * powh a (to_nat p2) true) (a ') (powh a (to_nat (p2 + p1)) false)).
    rewrite (asso a (powh a (to_nat p2) true) (a ')).
    rewrite <- (powa'comm a (to_nat p2) true).
    rewrite <- (asso a (a ') (powh a (to_nat p2) true)).
    rewrite (inv_r a). rewrite (id_l (powh a (to_nat p2) true)). apply H0.
  Qed.

  Lemma powmult : forall (a : A)(z1 z2 : Z), 
    (pow a z1) * (pow a z2) = (pow a (z1 + z2)).
  Proof.
    intros.
    case z1.
    simpl. rewrite (id_l (pow a z2)). trivial.
    case z2. simpl. intros. rewrite (id_r (powh a (to_nat p) true)). trivial.
    intros.
    apply ppmult.
    intros.
    apply pnmult.
    case z2.
    simpl. intros. rewrite (id_r (powh a (to_nat p) false)). trivial.
    intros. rewrite (powcomm a (neg p0) (pos p)).
    rewrite (Z.add_comm (neg p0) (pos p)).
    apply pnmult.
    intros. rewrite (add_neg_neg p0 p).
    rewrite <- (opp_pos p0). rewrite <-  (opp_pos p). rewrite <- (opp_pos (p0 + p)).
    rewrite (powinv2 a (pos p0)). rewrite (powinv2 a (pos p)).
    rewrite (powinv2 a (pos (p0 + p))).
    apply ppmult.
  Qed.

  Lemma powzofnat : forall (a : A) (n : nat),
    pow a (Z.of_nat n) = powh a n true.
  Proof.
    intros.
    case n.
    simpl. trivial.
    intros.
    simpl.
    rewrite (id_succ n0).
    simpl. trivial.
  Qed.
  (*** end: a bunch of properties for power representation ***)
End Group.
(*** end: group and its properties ***)



(* infinite version of pigeonhole principle is assumed, this can be proven with LEM law *)
Axiom pigeonhole : forall (n : nat)(A : Set),
  Finite n A -> forall (f : nat -> A), exists v1 : nat, exists v2 : nat,
  v1 < v2 /\ f v1 = f v2.



(*** start: main theorem ***)
Module GroupProps (G : Group).

Import G.

Theorem finiteOrd : forall (n : nat), Finite n A -> 
  forall (a : A), exists k : Z, (k > Z0)%Z /\ pow a k = e.

Proof.
  intros.
  generalize pigeonhole.
  intro Pn.
  assert (vs : exists v1 v2 : nat, v1 < v2 /\ powh a v1 true = powh a v2 true).
  apply (Pn n A H (fun x : nat => (powh a x true))).
  elim vs.
  intros v1 vs1.
  elim vs1.
  intros v2 vs2.
  destruct vs2.
  exists ((Z.of_nat v2) + (- (Z.of_nat v1)))%Z.
  split.
  omega.
  rewrite <- (powmult a (Z.of_nat v2) (- Z.of_nat v1)).
  rewrite (powzofnat a v2). rewrite <- (powinv a (Z.of_nat v1)). 
  rewrite (powzofnat a v1). 
  rewrite H1.
  rewrite (inv_r (powh a v2 true)). trivial.
Qed.

End GroupProps.
(*** end: main theorem ***)



(*******************************************************************)
(* begin: simplify the multiplication of groups, Not for the proof *)
(*        can be used in proofs by reflection on group             *)
(*******************************************************************)
Module PowerSimplifier (G : Group).
  Import G.
  
  (*** start: a type for encoding the group ***)
  Inductive GCode {a : A} : Set :=
    | ce : GCode 
    | ca : GCode
    | ca' : GCode
    | cmult : GCode -> GCode -> GCode.

  Notation " a1 *' a2 " := (cmult a1 a2) (at level 19).
  (*** end: a type for encoding the group ***)


  (*** start: decoding function ***)
  Fixpoint decode {a : A}(g : GCode (a:=a)) : A :=
    match g with
    | ce => e
    | ca => a
    | ca' => a '
    | g1 *' g2 => (decode g1) * (decode g2)
    end.
  (*** end: decoding function ***)


  (*** start: functions to simplfy the code of a group ***)
  Definition GSimpl_step {a : A} (g : GCode (a:=a)) : GCode (a:=a) :=
    match g with
    | ce => ce
    | ca => ca
    | ca' => ca'
    | ce *' g1 => g1
    | ca *' g1 => 
        match g1 with
        | ce => ca
        | ca' => ce
        | ca => ca *' ca
        | ce *' g2 => ca *' g2
        | ca' *' g2 => g2
        | ca *' g2 => ca *' (ca *' g2)
        | (h1 *' h2) *' g2 => (ca *' (h1 *' h2)) *' g2
        end
    | ca' *' g1 =>
        match g1 with
        | ce => ca'
        | ca' => ca' *' ca'
        | ca => ce
        | ce *' g2 => ca' *' g2
        | ca' *' g2 => ca' *' (ca' *' g2)
        | ca *' g2 => g2
        | (h1 *' h2) *' g2 => (ca' *' (h1 *' h2)) *' g2
        end
    | (h1 *' h2) *' g1 =>
        match g1 with
        | ce => h1 *' h2
        | _ => h1 *' (h2 *' g1)
        end
    end.
  
  Fixpoint GSimpl_sdev {a : A} (g : GCode (a:=a)) : GCode (a:=a) :=
    match g with
    | ce => ce
    | ca => ca
    | ca' => ca'
    | g1 *' g2 => GSimpl_step ((GSimpl_sdev g1) *' (GSimpl_sdev g2))
    end.

  Fixpoint GSimpl {a : A} (g : GCode (a:=a)) (n : nat) : GCode (a:=a) :=
    match n with
    | O => g
    | S p => GSimpl_sdev (GSimpl g p)
    end. 
  (*** end: functions to simplfy the code of a group ***)


  (*** start: prove the soundness of all operations in the code layer ***)
  Lemma GStep_sound : forall {a : A}(g : GCode(a:=a)),
    decode g = decode (GSimpl_step (a:=a) g).
  Proof.
    intros.
    case g.
    simpl; trivial.
    simpl; trivial.
    simpl; trivial.
    intros.
    case g0, g1; simpl; auto with gsimpls.
    case g1_1; simpl; autorewrite with gsimplw; auto with gsimpls.
    rewrite <- (asso a (a ') (decode g1_2)).
    rewrite (inv_r a). auto with gsimpls.
    case g1_1; simpl; autorewrite with gsimplw; auto with gsimpls.
    rewrite <- (asso (a ') a (decode g1_2)).
    rewrite (inv_l a). auto with gsimpls.
  Qed.
  
  Lemma GSdev_sound : forall {a : A}(g : GCode (a:=a)),
    decode g = decode (GSimpl_sdev (a:=a) g).
  Proof.
    intros.
    induction g.
    simpl; trivial.
    simpl; trivial.
    simpl; trivial.
    assert (forall g1 g2 : GCode (a:=a), GSimpl_sdev (g1 *' g2) = GSimpl_step (GSimpl_sdev g1 *' GSimpl_sdev g2)).
    intros.
    trivial.
    rewrite H.
    rewrite <- (GStep_sound (a:=a) (GSimpl_sdev g1 *' GSimpl_sdev g2)).
    assert (decode (GSimpl_sdev g1 *' GSimpl_sdev g2) = decode (GSimpl_sdev g1) * decode (GSimpl_sdev g2)).
    trivial.
    rewrite H0.
    rewrite <- IHg1.
    rewrite <- IHg2.
    trivial.
  Qed.

  Theorem GSimpl_sound : forall {a : A}(g : GCode (a:=a))(n : nat), 
    decode g = decode (GSimpl (a:=a) g n).
  Proof.
    intros.
    induction n.
    simpl.
    trivial.
    simpl.
    rewrite <- (GSdev_sound (a:=a) (GSimpl g n)).
    assumption.
  Qed.
  (*** end: prove the soundness of all operations in the code layer ***)

End PowerSimplifier.
(*******************************************************************)
(* end: simplify the multiplication of groups, Not for the proof   *)
(*      can be used in proofs by reflection on group               *)
(*******************************************************************)







(***

(*****************************************************************************************)
(* begin: define a morphism from powers to Z *)
(*****************************************************************************************)
  Inductive PowCode {a : A} : Set :=
    | pe : PowCode
    | pa : PowCode
    | pa' : PowCode
    | pmult : PowCode -> PowCode -> PowCode.

  (* encode function *)
  Fixpoint toPCodeh (a : A)(n : nat)(b : bool) : PowCode (a:=a) :=
    match n with
    | O => 
      match b with
      | true => pe
      | false => pe
      end
    | S m =>
      match b with
      | true => pmult pa (toPCodeh a m true)
      | false => pmult pa' (toPCodeh a m false)
      end
    end.

  (* decode function *)
  Fixpoint fromPCode {a : A}(p : PowCode (a:=a)) : A :=
    match p with
    | pe => e
    | pa => a
    | pa' => a '
    | pmult p1 p2 => fromPCode p1 * fromPCode p2
    end.

  (* morphism function to Z *)
  Fixpoint PCode2Z {a : A}(p : PowCode (a:=a)) : Z :=
    match p with
    | pe => 0
    | pa => 1
    | pa' => (- 1)
    | pmult p1 p2 => PCode2Z p1 + PCode2Z p2
    end.

  (* prove this morphism also map pmult to '+' *)
  Theorem pmult2plus : forall {a : A}(p q : PowCode (a:=a)), PCode2Z (pmult p q) = (PCode2Z p + PCode2Z q)%Z.
  Proof.
    intros.
    trivial.
  Qed.

  Definition toPCode (a : A)(z : Z) : PowCode (a:=a) :=
    match z with
    | Z0 => toPCodeh a O true
    | Zpos p => toPCodeh a (to_nat p) true
    | Zneg p => toPCodeh a (to_nat p) false
    end.



  Definition pow1 (a : A)(z : Z) : A := fromPCode (toPCode a z).

  Theorem toz : forall (a : A)(z : Z), PCode2Z (toPCode a z) = z.
  Proof.
    intros.
    case z.
    simpl. trivial.
    apply peano_ind.
    simpl. trivial.
    intros.
    simpl.
    rewrite (Pos2Nat.inj_succ p).
    rewrite (inj_succ p). 
    assert (toPCodeh a (S (to_nat p)) true = pmult pa (toPCodeh a (to_nat p) true)).
    trivial.
    rewrite H0.
    assert (toPCodeh a (to_nat p) true = toPCode a (pos p)).
    trivial.
    rewrite H1.
    assert (PCode2Z (pmult pa (toPCode a (pos p))) = (1 + PCode2Z (toPCode a (pos p)))%Z).
    trivial.
    rewrite H2.
    rewrite H.
    trivial.
    ring.
    apply peano_ind.
    simpl. trivial.
    intros.
    simpl.
    rewrite (Pos2Nat.inj_succ p).
    assert (toPCodeh a (S (to_nat p)) false = pmult pa' (toPCodeh a (to_nat p) false)).
    trivial.
    rewrite H0.
    assert (toPCodeh a (to_nat p) false = toPCode a (neg p)).
    trivial.
    rewrite H1.
    assert (PCode2Z (pmult pa' (toPCode a (neg p))) = ((- 1) + PCode2Z (toPCode a (neg p)))%Z).
    trivial.
    rewrite H2.
    rewrite H.
    rewrite (add_neg_neg 1 p).
    apply inj_neg_iff.
    apply add_1_l.
  Qed.
  
  Theorem topsym : forall (a : A) (p : positive),
    fromPCode (toPCode a (neg p)) = fromPCode (toPCode (a ') (pos p)).
  
  Proof.
    intro.
    apply peano_ind.
    simpl. trivial.
    intros.
    simpl.
    rewrite (Pos2Nat.inj_succ p).
    simpl.
    simpl in H.
    rewrite H.
    trivial.
  Qed.




  (* Prove toPCode preserve + *)
  Theorem prevplus : forall (a : A) (z1 z2 : Z), fromPCode (toPCode a (z1 + z2)) = fromPCode (toPCode a z1) * fromPCode (toPCode a z2).
  Proof.
    intros.
    case z1.
    simpl. rewrite (id_l (fromPCode (toPCode a z2))). trivial.
    case z2.
    simpl. intros. rewrite (id_r (fromPCode (toPCodeh a (to_nat p) true))). trivial.
    intros.
    rewrite <- (inj_add p0 p).
    simpl.
    generalize p0.
    apply peano_ind.
    rewrite add_1_l.
    rewrite (Pos2Nat.inj_succ p).
    simpl.
    rewrite (id_r a). trivial.
    intros.
    rewrite (add_succ_l p1 p).
    rewrite (Pos2Nat.inj_succ (p1+p)).
    rewrite (Pos2Nat.inj_succ (p1)).
    simpl.
    rewrite (asso a (fromPCode (toPCodeh a (to_nat p1) true)) (fromPCode (toPCodeh a (to_nat p) true))).
    rewrite H. trivial.
    intros.
    rewrite (add_pos_neg p0 p).
    generalize (pos_sub_discr p0 p).
    case (pos_sub p0 p).
    intros.
    simpl.
    rewrite H.
    generalize p.
    apply peano_ind.
    simpl.
    rewrite (id_r a).
    rewrite (id_r (a ')).
    rewrite (inv_r a). trivial.
    intros.
    rewrite (Pos2Nat.inj_succ (p1)).
    simpl.
    rewrite <- (asso (a * fromPCode (toPCodeh a (to_nat p1) true)) (a ') (fromPCode (toPCodeh a (to_nat p1) false))).
    rewrite (asso a (fromPCode (toPCodeh a (to_nat p1) true)) (a ')).
    

    generalize (pos_sub p0 p).
    case (pos_sub p0 p).
    simpl.
  




  Theorem zinv : forall (a : A) (p : PowCode (a:=a)), fromPCode (toPCode a (PCode2Z p)) = fromPCode p.
  Proof.
    intros.
    induction p.
    simpl. trivial.
    simpl. rewrite (id_r a). trivial.
    simpl. rewrite (id_r (a ')). trivial.
    simpl. 

  Theorem pow2plus : forall (a : A)(z1 z2 : Z), PCode2Z (pmult (toPCode a z1) (toPCode a z2)) = (z1 + z2)%Z.
  Proof.
    intros.
    rewrite (pmult2plus (a:=a) (toPCode a z1) (toPCode a z2)).
    rewrite (toz a z1).
    rewrite (toz a z2).
    trivial.
  Qed.
(*****************************************************************************************)
(* end: define a morphism from powers to Z *)
(*****************************************************************************************)

***)