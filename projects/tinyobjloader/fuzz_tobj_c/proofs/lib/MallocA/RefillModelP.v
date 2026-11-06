(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "of_nat"; "mul"; "lt"; "sub"; "div"; "to_nat"; "ltb"; "pow"; "@Corelib.Init.Logic"; "and"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModelP.P"; "newZ"; "faP"; "@Corelib.Init.Datatypes"; "length"; "bool"; "list"; "app"; "nat"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "kUserMapSize"; "kFreeArrayMapSize"; "@Corelib.Lists.ListDef"; "nth"; "firstn"; "skipn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "cs_free_array"; "class_state"; "cs_mapped_user"; "cs_allocated_user"; "cs_cache"; "cs_mapped_free_array"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel"; "populate_cs"; "refill_cs"; "cls_pure"; "kchunks"; "needs_populate"; "new_ids"; "take_cs"; "@Corelib.Init.Peano"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCredit"; "FACAP"; "MUCAP"; "@Stdlib.Lists.List"; "In"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model PrimCredit PrimCreditLaws RefillModel.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section P.
Variables (c : Z) (cs : class_state) (out : list Z).
Hypothesis Hc : 1 <= c <= 30.
Hypothesis HP : ltac2:(tb__ "0|0|
S22Vc;Vcs;Vout;A3").
Hypothesis Hc0 : cs_cache cs = [].
Hypothesis HNP : ltac2:(tb__ "0|0|
S5S3SfS0S1aVcs;A1A2A1S23Vc;A1A2").
Hypothesis Hroom : ltac2:(tb__ "0|0|
S2S1S1cVcs;A1S15A2S29Vc;A1A2").

Let S : Z := Size c.
Let au : Z := cs_allocated_user cs.
Let mu : Z := cs_mapped_user cs.
Let mfa : Z := cs_mapped_free_array cs.
Let fa : list Z := cs_free_array cs.
Let k : Z := kchunks c.
Definition newZ : Z := ltac2:(tb__ "0|0|
S7S6S1Vmu;S15A2Vau;A2VS;A2").
Definition faP : list Z := ltac2:(tb__ "0|0|
S12S0Vfa;S25Vau;VS;S8SdA1A3A3").

Lemma P_needs : ltac2:(tb__ "0|0|
ScS10S24Vc;Vcs;A2S14A3").
Proof. unfold needs_populate. apply Z.ltb_lt. exact HNP. Qed.

Lemma P_refill_cs : ltac2:(tb__ "0|0|
ScS1bS21Vc;Vcs;A2S26S8Vk;A1S20Vc;Vcs;A2A2A3").
Proof. unfold refill_cs. rewrite P_needs. reflexivity. Qed.

Lemma P_new : ltac2:(tb__ "0|3|
SbSbS2Z4SdA2S2SdZ2001A2A2SbSbS2S7S15VS;A2M0SdA2S2SdS1G0Z1A2A2A2SbS2S1Vau;S4SdVS;A2A2M1S1Vmu;S15A2M2A2SbS5G2S1G1VS;A2A2S2Vk;SdA2A2A2A2A2").
Proof.
  destruct HP as (P1 & P2 & P3 & P4 & P4' & P5 & P6 & P7 & P8 & P9 & P10 & P11).
  destruct (cap_facts c Hc) as (HS & HS16 & _). destruct (kchunks_facts c Hc) as (K1 & K2 & K3). fold S in HS, HS16, K3. fold au mu in P2, P8. fold S in P8. fold k in K1, K3.
  unfold newZ, kUserMapSize in *.
  pose proof (Z.div_mod (mu + 2 ^ 18 - au) S ltac:(lia)) as DM. pose proof (Z.mod_pos_bound (mu + 2 ^ 18 - au) S ltac:(lia)) as MB.
  pose proof (Z.div_mod (2 ^ 18) S ltac:(lia)) as DM2. pose proof (Z.mod_pos_bound (2 ^ 18) S ltac:(lia)) as MB2.
  set (n := (mu + 2 ^ 18 - au) / S) in *. set (q := 2 ^ 18 / S) in *.
  assert (Hq : 4 <= q <= 8192) by (unfold q; split; [apply Z.div_le_lower_bound; lia | apply Z.div_le_upper_bound; lia]).
  assert (N1 : q <= n) by (unfold n, q; apply Z.div_le_mono; lia).
  assert (N2 : n <= q + 1).
  { unfold n. replace (mu + 2 ^ 18 - au) with (2 ^ 18 + (mu - au)) by lia.
    assert (X : (2 ^ 18 + (mu - au)) / S <= (2 ^ 18 + 1 * S) / S) by (apply Z.div_le_mono; lia). rewrite Z.div_add in X by lia. exact X. }
  split; [lia|]. split; [lia|]. split; [nia|]. split; [nia|].
  assert (k <= q) by (unfold q; apply Z.div_le_lower_bound; lia). lia.
Qed.

Lemma P_fa : ltac2:(tb__ "0|0|
ScS11S0A1S1aS20Vc;Vcs;A2A1SeA3").
Proof. unfold populate_cs, faP, newZ. cbn [cs_free_array]. reflexivity. Qed.

Lemma P_faP_len : ltac2:(tb__ "0|0|
ScS0S3SfS0SeA2A1S1S3SfS0Vfa;A2A1SdA2A3").
Proof. unfold faP. rewrite length_app, new_ids_length, Nat2Z.inj_add. destruct P_new as (N & _). rewrite Z2Nat.id by lia. reflexivity. Qed.

Lemma P_fields : ltac2:(tb__ "0|5|
S21Vc;Vcs;A2S1bSbScS11S0A1M0S1eR1A1M1S19S0S8S6S3SfS0SeA2A1Vk;A2A1M2SeA3A3SbScS0S3SfS0G1A2A1Vk;A3SbScS0S3SfS0S1aR1A1M3A2A1S6S1S3SfS0Vfa;A2A1SdA2M4Vk;A2A3SbScG0G3S18S0G2SeA3A3SbScS0S1dR1A1S1Vau;S4SdVS;A2A2A3SbScS0S1cR1A1S1Vmu;S15A2A3ScS0S1fR1A1S10S0L_;S9Vmfa;S4Z4G4A2A2S1Vmfa;S16A2Vmfa;X10x2A3A2A2A2A2A2A2TcsR;").
Proof.
  intros csR. unfold csR. rewrite P_refill_cs.
  destruct (kchunks_facts c Hc) as (K1 & _). fold k in K1. destruct P_new as (N4 & _ & _ & _ & KN).
  pose proof P_faP_len as LP.
  destruct (populate_pure c cs out Hc HP Hroom) as (_ & EMU & _ & _ & EMF & _). cbn zeta in EMU, EMF.
  unfold take_cs. cbn [cs_cache cs_free_array cs_allocated_user cs_mapped_user cs_mapped_free_array]. rewrite P_fa.
  assert (EN : (length faP - Z.to_nat k)%nat = Z.to_nat (Z.of_nat (length faP) - k)) by lia.
  rewrite EN.
  split; [reflexivity|]. split; [rewrite length_skipn; lia|]. split; [rewrite firstn_length_le by lia; lia|]. split; [reflexivity|].
  split.
  { unfold populate_cs. cbn [cs_allocated_user]. fold au mu S. fold newZ. rewrite Z2Nat.id by lia. reflexivity. }
  split; [exact EMU|].

  assert (EDEF : cs_mapped_free_array (populate_cs c cs)
                 = if mfa <? 4 * Z.of_nat (length faP) then round_up (4 * Z.of_nat (length faP)) kFreeArrayMapSize else mfa) by reflexivity.
  rewrite LP in EDEF. rewrite EDEF.
  destruct (mfa <? 4 * (Z.of_nat (length fa) + newZ)) eqn:E; [|reflexivity].
  apply Z.ltb_lt in E. rewrite EDEF in EMF. destruct EMF as [X|X]; [|exact X].

  exfalso. unfold round_up, kFreeArrayMapSize in X. fold mfa in X.
  pose proof (Z.div_mod (4 * (Z.of_nat (length fa) + newZ) + 2 ^ 18 - 1) (2 ^ 18) ltac:(lia)) as DM.
  pose proof (Z.mod_pos_bound (4 * (Z.of_nat (length fa) + newZ) + 2 ^ 18 - 1) (2 ^ 18) ltac:(lia)) as MB. lia.
Qed.

Lemma P_famap : ltac2:(tb__ "0|3|
S5Vmfa;S4Z4S1S3SfS0Vfa;A2A1SdA2A2M0A2SbScS0S4S7S1G0Z3ffffA2Z40000M1A2G1A2S1Vmfa;G1A2M2A3S2G2S28Vc;A1A2A2F_;").
Proof.
  intros E. pose proof P_faP_len as LP.
  destruct (populate_pure c cs out Hc HP Hroom) as (_ & _ & _ & _ & EMF & HFC). cbn zeta in EMF, HFC.
  assert (EDEF : cs_mapped_free_array (populate_cs c cs)
                 = if mfa <? 4 * Z.of_nat (length faP) then round_up (4 * Z.of_nat (length faP)) kFreeArrayMapSize else mfa) by reflexivity.
  rewrite LP in EDEF. replace (mfa <? 4 * (Z.of_nat (length fa) + newZ)) with true in EDEF by (symmetry; apply Z.ltb_lt; exact E).
  rewrite EDEF in EMF, HFC. unfold round_up, kFreeArrayMapSize in EMF, HFC. fold mfa in EMF. change (2 ^ 18) with 262144 in EMF, HFC.
  replace (4 * (Z.of_nat (length fa) + newZ) + 262144 - 1) with (4 * (Z.of_nat (length fa) + newZ) + 262143) in EMF, HFC by lia.
  destruct EMF as [X|X].
  - exfalso. pose proof (Z.div_mod (4 * (Z.of_nat (length fa) + newZ) + 262143) 262144 ltac:(lia)) as DM.
    pose proof (Z.mod_pos_bound (4 * (Z.of_nat (length fa) + newZ) + 262143) 262144 ltac:(lia)) as MB. lia.
  - split; [exact X | rewrite X in HFC; exact HFC].
Qed.

Lemma P_ids : ltac2:(tb__ "0|0|
S0S2aS0R1SeA3SbS2Z0R2A2S5R2SaZ2Z1cA2A2A2F_;Fx;").
Proof.
  intros x Hx. destruct (populate_pure c cs out Hc HP Hroom) as (HP' & EMU & _). cbn zeta in HP', EMU.
  destruct HP' as (_ & Q2 & _ & _ & _ & _ & Q6 & _ & _ & _ & Q10 & _).
  destruct (Q6 x ltac:(rewrite P_fa; apply in_or_app; left; exact Hx)) as (X1 & _ & X3).
  destruct (cap_facts c Hc) as (HS & _ & MCU & _). unfold kUserSpaceSize, kRegionSize, kFreeArraySize in MCU. lia.
Qed.

Lemma P_nth_old : ltac2:(tb__ "0|1|
S13S27R1SfS0Vfa;A2A2ScS0S17S0R2SeZ0M0A4S17S0R2Vfa;G0A4A3F_;Fi;").
Proof. intros i Hi. unfold faP. apply app_nth1. exact Hi. Qed.
Lemma P_nth_new : ltac2:(tb__ "0|1|
S0SbS2Z0M0R1A2S5R1SdA2A2ScS0S17S0S8S6S6S1S3SfS0Vfa;A2A1SdA2Z1A2R2A2A1SeG0A4S7S1Vau;S4R2VS;A2A2Z10A2A3F_;Fj;").
Proof.
  intros j Hj. unfold faP. rewrite app_nth2 by lia.
  replace (Z.to_nat (Z.of_nat (length fa) + newZ - 1 - j) - length fa)%nat with (Z.to_nat (newZ - 1 - j)) by lia.
  apply nth_error_nth. rewrite new_ids_nth by lia. f_equal. f_equal. rewrite !Z2Nat.id by lia. f_equal. lia.
Qed.
End P.
