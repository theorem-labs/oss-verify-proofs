(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnModel BnTree BnInv BgState BgInv.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require Import BnHeap.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgRepU Require Import BgRepDefs BgRep BgLayer.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.P Require Import Rnd.
Unset Lia Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma land64_small : forall x, 0 <= x < 18446744073709551616 -> Z.land x 18446744073709551615 = x.
Proof. intros x H. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. apply Z.mod_small. exact H. Qed.

(* [comment removed for export] *)
Lemma lxor_signbit63' : forall x, 0 <= x < 9223372036854775808 -> Z.lxor x 9223372036854775808 = x + 9223372036854775808.
Proof.
  intros x H. symmetry. apply Z.add_nocarry_lxor. apply Z.bits_inj'. intros k Hk.
  rewrite Z.land_spec, Z.bits_0. change 9223372036854775808 with (2 ^ 63). rewrite Z.pow2_bits_eqb by lia.
  destruct (Z.eqb_spec 63 k) as [<-|NE]; [|apply andb_false_r]. rewrite andb_true_r.
  destruct (Z.eq_dec x 0) as [->|NZ]; [apply Z.bits_0|]. apply Z.bits_above_log2; [lia|]. apply Z.log2_lt_pow2; lia.
Qed.

(* [comment removed for export] *)
Ltac to_implM :=
  lazymatch goal with |- impl ?segs _ (?c ?st) (epost ?E) ?ms =>
    lazymatch E with (fun p => ?Q (fst p) (snd p)) => change (implM segs c st Q ms) end end.

Lemma pl_of_bn : forall PL r p, pl_of PL r = Some p -> (r =? ROne)%nat = false -> mont_ref r = false -> pl_bn PL r = Some p.
Proof.
  intros PL r p H N1 NM. unfold pl_of in H. unfold mont_ref in NM. rewrite N1 in H.
  apply orb_false_iff in NM as [NM NNi]. apply orb_false_iff in NM as [NRR NN]. rewrite NRR, NN, NNi in H.
  destruct (r <? NFIX)%nat; cbn in H; [exact H| discriminate H].
Qed.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

(* [comment removed for export] *)
Lemma ref_at_ualign : forall s OW LB m (st : ST) PL EA r a,
  RHEAP s (OW ++ LB) m -> lib_parts st OW PL EA -> ref_at st OW PL r a -> r <> ROne -> 0 < a /\ a mod 8 = 0.
Proof.
  intros s OW LB m st PL EA r a HEAP (_ & WF & _ & (PB & _ & _) & _) HA NO.
  assert (X : forall p A n, In (p, A, n) OW -> 0 < A /\ A mod 16 = 0).
  { intros p A n Hin. pose proof (RH_range _ _ _ _ _ _ _ HEAP Hin) as (R0 & R16 & _). split; assumption. }
  unfold ref_at in HA. revert HA. destruct (r <? NFIX)%nat eqn:LT; intros HA.
  - destruct HA as (p & Hp & <-). pose proof (PB r p (proj1 (Nat.ltb_lt _ _) LT) Hp) as OK.
    assert (N1 : (r =? ROne)%nat = false) by (apply Nat.eqb_neq; exact NO).
    destruct (mont_ref r) eqn:EM.
    + unfold mont_ref in EM. rewrite !orb_true_iff in EM.
      destruct EM as [[EM|EM]|EM];
        apply Nat.eqb_eq in EM; subst r;
        cbv [pl_of ROne RMontRR RMontN RMontNi Nat.eqb] in Hp;
        destruct (pl_mont PL) as [[am qm]|]; try discriminate Hp; injection Hp as <-;
        destruct OK as (n & Hin & _); destruct (X _ _ _ Hin) as (P & Q); cbn [place_addr];
        split; try lia; clear - Q; Z.div_mod_to_equations; lia.
    + pose proof (pl_of_bn PL r p Hp N1 EM) as Hb. destruct WF as (W1 & _ & _). pose proof (W1 r p Hb) as (_ & _ & _ & K).
      destruct p as [a0 q off|a0|a0 d|a0]; cbn [place_addr].
      * subst off. destruct OK as (n & Hin & _). replace (a0 - 0) with a0 in Hin by lia. destruct (X _ _ _ Hin) as (P & Q).
        split; [exact P|]. clear - Q. Z.div_mod_to_equations. lia.
      * destruct K as (K1 & K2). split; assumption.
      * destruct K as (K1 & _ & _ & K4 & _). split; assumption.
      * destruct K.
  - cbv zeta in HA. destruct HA as (q & H & _ & Hin & ->). destruct (X _ _ _ Hin) as (P & Q).
    split; [lia|]. clear - Q. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma block_ualign : forall s OW LB m p A n, RHEAP s (OW ++ LB) m -> In (p, A, n) OW -> 0 < A /\ A mod 8 = 0.
Proof.
  intros s OW LB m p A n HEAP Hin. pose proof (RH_range _ _ _ _ _ _ _ HEAP Hin) as (R0 & R16 & _). split; [exact R0|].
  clear - R16. Z.div_mod_to_equations. lia.
Qed.

Lemma bn_arr_ualign : forall s OW LB m (st : ST) PL EA r D (b : BN),
  RHEAP s (OW ++ LB) m -> lib_parts st OW PL EA -> bn_arr m OW (pl_of PL r) D b -> (0 < bn_dmax b)%nat -> 0 < D /\ D mod 8 = 0.
Proof.
  intros s OW LB m st PL EA r D b HEAP (_ & WF & _) ARR NZ.
  assert (NE : bn_buf b <> []) by (intros E; unfold bn_dmax in NZ; rewrite E in NZ; cbn in NZ; lia).
  unfold bn_arr in ARR. destruct (bn_d b) as [p|].
  - exact (block_ualign _ _ _ _ _ _ _ HEAP (proj1 ARR)).
  - destruct (pl_of PL r) as [[a0 q off|a0|a0 d|a0]|] eqn:Ep; try (destruct ARR as [_ E]; contradiction).
    + destruct ARR as (-> & _ & _).
      assert (N1 : (r =? ROne)%nat = false) by (destruct (r =? ROne)%nat eqn:E; [|reflexivity]; unfold pl_of in Ep; rewrite E in Ep; discriminate).
      assert (NM : mont_ref r = false).
      { unfold pl_of in Ep. rewrite N1 in Ep. unfold mont_ref.
        destruct (r =? RMontRR)%nat; [destruct (pl_mont PL) as [[]|]; discriminate|].
        destruct (r =? RMontN)%nat; [destruct (pl_mont PL) as [[]|]; discriminate|].
        destruct (r =? RMontNi)%nat; [destruct (pl_mont PL) as [[]|]; discriminate|]. reflexivity. }
      destruct WF as (W1 & _ & _). destruct (W1 r _ (pl_of_bn PL r _ Ep N1 NM)) as (_ & _ & _ & _ & K2 & _ & _ & K5).
      split; assumption.
    + destruct ARR as (-> & _). unfold DATA_ONE. split; [lia| reflexivity].
Qed.

End WithCeiling0.
