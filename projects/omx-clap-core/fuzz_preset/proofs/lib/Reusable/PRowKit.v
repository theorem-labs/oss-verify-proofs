(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset, the image-free kit of c-libc-stdio's runtime-row lanes (preset's
   po_asan_memcpy_cf / po_memcpy_icpt_cf / po_asan_memset_cf / po_memset_icpt_cf / po_memcmp_cf / po_bcmp_cf restated
   as YGcallMxmn.v's _xm texts over the generic ARx).
   rule 24: proves no function (kind: segment lemma).

   THE KEEP. Every _xm text ends in `MN.memnorm segs mem -> MN.memnorm segs mem'` (MN = YAkMemnorm). The donor walks
   (preset's cgif-relocated A/AE2q, AE31, AE2r, AE32 and the Reusable twins) reach the end memory through one tail
   lemma (mc_tail and its twins) that holds the RAW facts the keep needs: the end memory equals the entry memory off
   the destination range [d, d + n) and off the scratch window [lo, hi) below sp (MEQ1 / M2out / MEQ3), every
   window byte is present at entry (ecall_pre's stack presence), and every destination byte is writable_at the
   restricted entry memory (dest_ok). prk_memnorm_keep turns these into the keep; no phase of the walk is re-run.
   prk_memnorm_keep_win is the same without a destination (a walk that writes only its window).

   WHY NOT YGcallMxmn.memnorm_new_wview: the proof below is that lemma's argument specialised to the two ranges, written
   over YAkMemnorm only. YGcallMxmn.v's Require closure contains YCbq.v -> YM04.v, which redefines YM03.lf_lia_orig
   (YM04.v:36), and the donor walks' closure (A/AE30.v, A/AE6k.v, Reusable/YE30.v, Reusable/YE6k.v) does not: a walk
   copy that Required this kit would run its lia calls under a different lia than the donor's. This file's closure is
   YAkMemnorm.v, YK04.v, YP09.v and YG0n.v (and their closures), all inside the donors' closure but YAkMemnorm.v.

   Numerals: 64 (WORD: bit width), 0 (DERIVED: the empty destination of prk_memnorm_keep_win). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YP09 YG0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
Open Scope Z_scope.

Module MN := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YAkMemnorm.

(* A byte absent from the entry memory, written by the run: it lies in [d, d + n), where it is writable_at the
   restricted entry memory, so it lies in a writable segment (as YGcallMxmn.ak_wview_not_ro / ak_wview_absent_seg). *)
Lemma prk_memnorm_keep : forall segs (H : word -> bool) (mem mem' : word -> option byte) d n lo hi,
  MN.memnorm segs mem ->
  (forall z : word, ~ (d <= bv_unsigned z < d + n) -> ~ (lo <= bv_unsigned z < hi) -> mem' z = mem z) ->
  (forall a, lo <= a < hi -> apresent H mem a) ->
  (forall a, d <= a < d + n -> writable_at segs (mrestrict H mem) a) ->
  MN.memnorm segs mem'.
Proof.
intros segs H mem mem' d n lo hi (Hi & Ht) Hfr Hwin Hdst.
(* every byte of mem' is a byte of mem, or a byte of [d, d + n) that mem lacks and wview defines *)
assert (NEW : forall (z : word) b, mem' z = Some b ->
  (exists b0, mem z = Some b0) \/ (mem z = None /\ wview segs mem z <> None)).
{ intros z b Ez. destruct (mem z) as [b0|] eqn:E0; [left; exists b0; reflexivity|]. right. split; [reflexivity|].
  destruct (Z_le_dec d (bv_unsigned z)) as [D1|D1];
  [destruct (Z_lt_dec (bv_unsigned z) (d + n)) as [D2|D2]|].
  - pose proof (Hdst (bv_unsigned z) (conj D1 D2)) as Hw. unfold writable_at in Hw. rewrite Z_to_bv_bv_unsigned in Hw.
    assert (Er : mrestrict H mem z = mem z) by (unfold mrestrict; rewrite E0; destruct (H z); reflexivity).
    assert (Ew : wview segs (mrestrict H mem) z = wview segs mem z) by (unfold wview; rewrite Er; reflexivity).
    rewrite Ew in Hw. exact Hw.
  - assert (ND : ~ (d <= bv_unsigned z < d + n)) by lia.
    destruct (Z_le_dec lo (bv_unsigned z)) as [W1|W1]; [destruct (Z_lt_dec (bv_unsigned z) hi) as [W2|W2]|].
    + destruct (Hwin (bv_unsigned z) (conj W1 W2)) as [_ [b0 Hb0]]. rewrite Z_to_bv_bv_unsigned, E0 in Hb0. discriminate.
    + rewrite (Hfr z ND ltac:(lia)), E0 in Ez. discriminate.
    + rewrite (Hfr z ND ltac:(lia)), E0 in Ez. discriminate.
  - assert (ND : ~ (d <= bv_unsigned z < d + n)) by lia.
    destruct (Z_le_dec lo (bv_unsigned z)) as [W1|W1]; [destruct (Z_lt_dec (bv_unsigned z) hi) as [W2|W2]|].
    + destruct (Hwin (bv_unsigned z) (conj W1 W2)) as [_ [b0 Hb0]]. rewrite Z_to_bv_bv_unsigned, E0 in Hb0. discriminate.
    + rewrite (Hfr z ND ltac:(lia)), E0 in Ez. discriminate.
    + rewrite (Hfr z ND ltac:(lia)), E0 in Ez. discriminate. }
split.
- intros z b Ez. destruct (NEW z b Ez) as [[b0 E0] | [E0 Hw]]; [exact (Hi z b0 E0)|].
  unfold MN.ro_addr. unfold wview in Hw. rewrite E0 in Hw.
  destruct (find_segment segs (bv_unsigned z) 1) as [sg|]; [|reflexivity].
  destruct (seg_writable sg); [reflexivity|]. exfalso. apply Hw. reflexivity.
- intros z b Ez. destruct (NEW z b Ez) as [[b0 E0] | [E0 Hw]]; [exact (Ht z b0 E0)|].
  left. unfold wview in Hw. rewrite E0 in Hw.
  destruct (find_segment segs (bv_unsigned z) 1); [discriminate|]. exfalso. apply Hw. reflexivity.
Qed.

(* the same for a run that writes only its window [lo, hi) *)
Lemma prk_memnorm_keep_win : forall segs (H : word -> bool) (mem mem' : word -> option byte) lo hi,
  MN.memnorm segs mem ->
  (forall z : word, ~ (lo <= bv_unsigned z < hi) -> mem' z = mem z) ->
  (forall a, lo <= a < hi -> apresent H mem a) ->
  MN.memnorm segs mem'.
Proof.
intros segs H mem mem' lo hi HMN Hfr Hwin.
apply (prk_memnorm_keep segs H mem mem' 0 0 lo hi HMN).
- intros z _ Hz. exact (Hfr z Hz).
- exact Hwin.
- intros a Ha. lia.
Qed.
