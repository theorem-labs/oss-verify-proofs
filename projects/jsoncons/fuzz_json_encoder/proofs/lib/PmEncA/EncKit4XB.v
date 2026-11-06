(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA LibIface FPSteps L5Defs L5Core.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmHeapIfaceA PmLibDefs PmLibSpecs PmEncSpecs PmLibDefsA PmLibSpecsA PmEncSpecsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmEncA Require Import EncKitXB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module EK4A.
Import PMES.
Section K.
Variable L : asan_layout.
Variable CL : Z.
Variable onmax : Z.
Hypothesis KPM : 0 <= hl_k_per_malloc L.
Hypothesis BLIN : 0 <= hl_b_lin L.
Hypothesis BOV : 0 <= hl_b_overhead L.

Lemma kv_pow : forall k, 0 <= k <= 10 -> Z.log2 (32768 / (32 * 2 ^ k)) = 10 - k.
Proof.
  intros k Hk. replace 32768 with (2 ^ (10 - k) * (32 * 2 ^ k)).
  - rewrite Z.div_mul by (pose proof (Z.pow_pos_nonneg 2 k); lia). apply Z.log2_pow2. lia.
  - replace (2 ^ (10 - k) * (32 * 2 ^ k)) with (32 * (2 ^ (10 - k) * 2 ^ k)) by lia. rewrite <- Z.pow_add_r by lia. replace (10 - k + k) with 10 by lia. reflexivity.
Qed.

Lemma push_credit : forall cr (g : eghost) kx bx (es : estate) b capb,
  EKA.clok CL onmax -> PMESA.ecreditA L CL cr g kx bx -> g_scap g = capb -> 32 * depth es = capb -> 0 <= depth es < MAX_DEPTH ->
  ((capb = 0 /\ b = 0) \/ (exists k, 0 <= k <= 10 /\ capb = 32 * 2 ^ k)) ->
  acredit_ok L cr (Z.max 32 (2 * capb)) /\ 32 <= Z.max 32 (2 * capb) <= onmax /\
  (exists k', 0 <= k' <= 10 /\ Z.max 32 (2 * capb) = 32 * 2 ^ k') /\
  forall g', g_rep g' = g_rep g -> g_scap g' = Z.max 32 (2 * capb) -> PMESA.ecreditA L CL (adebit L cr (Z.max 32 (2 * capb))) g' kx bx.
Proof.
  intros cr g kx bx es b capb (C1 & C2 & C3 & C4) (E1 & E2 & E3 & E4) Hsc Hfull Hd T5.
  unfold MAX_DEPTH in Hd.
  (* [comment removed for export] *)
  assert (KK : exists k', 0 <= k' <= 10 /\ Z.max 32 (2 * capb) = 32 * 2 ^ k' /\ kv_st (Z.max 32 (2 * capb)) = kv_st capb - 1 /\
               Z.max 0 (65536 - 2 * capb) - Z.max 0 (65536 - 2 * Z.max 32 (2 * capb)) >= Z.max 32 (2 * capb)).
  { destruct T5 as [[C0 _]|(k & Hk & Ck)].
    - exists 0. rewrite C0. cbn. repeat split; lia.
    - assert (P1 : 1 <= 2 ^ k) by (pose proof (Z.pow_pos_nonneg 2 k); lia).
      assert (Hk9 : k <= 9).
      { destruct (Z.eq_dec k 10) as [->|]; [|lia]. exfalso. rewrite Ck in Hfull. change (2 ^ 10) with 1024 in Hfull. lia. }
      assert (P9 : 2 ^ k <= 512) by (change 512 with (2 ^ 9); apply Z.pow_le_mono_r; lia).
      exists (k + 1). rewrite Ck. replace (Z.max 32 (2 * (32 * 2 ^ k))) with (32 * 2 ^ (k + 1)) by (rewrite Z.pow_add_r, Z.pow_1_r by lia; nia).
      split; [lia|]. split; [reflexivity|].
      unfold kv_st. destruct (Z.eqb_spec (32 * 2 ^ (k + 1)) 0); [rewrite Z.pow_add_r, Z.pow_1_r in e by lia; nia|]. destruct (Z.eqb_spec (32 * 2 ^ k) 0); [nia|].
      rewrite !kv_pow by lia. rewrite Z.pow_add_r, Z.pow_1_r by lia. split; [lia|]. nia. }
  destruct KK as (k' & Hk' & EQ & KV & BD).
  assert (P1' : 1 <= 2 ^ k') by (pose proof (Z.pow_pos_nonneg 2 k'); lia).
  assert (P10 : 2 ^ k' <= 1024) by (change 1024 with (2 ^ 10); apply Z.pow_le_mono_r; lia).
  assert (KT1 : 1 <= kv_st capb).
  { unfold kv_st. destruct (Z.eqb_spec capb 0); [lia|]. destruct T5 as [[C0 _]|(k & Hk & Ck)]; [lia|].
    assert (Hk9 : k <= 9) by (destruct (Z.eq_dec k 10) as [->|]; [exfalso; rewrite Ck in Hfull; change (2 ^ 10) with 1024 in Hfull; lia | lia]).
    rewrite Ck, kv_pow by lia. lia. }
  pose proof (EKA.kv_s2_pos (g_rep g)) as KS. pose proof (EKA.kv_st_nonneg (Z.max 32 (2 * capb))) as KT0.
  unfold PMESA.ecreditA, PMESA.kenc, PMESA.benc, PMESA.bpot_st in E2, E4 |- *. rewrite Hsc in E2, E4.
  first [pose proof (EKA.bpot_s2_nonneg L CL BLIN BOV (g_rep g)) as BS0 | pose proof (EKA.bpot_s2_nonneg L CL KPM BLIN (g_rep g)) as BS0 | pose proof (EKA.bpot_s2_nonneg L CL BLIN (g_rep g)) as BS0].
  pose proof (Z.le_max_l 0 (65536 - 2 * Z.max 32 (2 * capb))) as M0.
  split; [|split; [rewrite EQ; split; [nia | lia] | split; [exists k'; exact (conj Hk' EQ)|]]].
  - unfold acredit_ok. split; [nia|]. nia.
  - intros g' Hrep Hsc'. unfold PMESA.ecreditA, PMESA.kenc, PMESA.benc, PMESA.bpot_st, adebit. cbn [fst snd]. rewrite Hrep, Hsc', KV.
    split; [exact E1|]. split; [nia|]. split; [exact E3|]. nia.
Qed.
End K.
End EK4A.
