(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: copied from proofs/omx-clap-core/fuzz_preset/lib/Reusable/YAkMemnormWb.v, with its module paths changed. *)
(* Theorem Labs, 2026-10: fuzz_preset, route R1 (a Theorem Labs lane, lane MnPrefix): memnorm (YAkMemnorm.memnorm) kept across a
   kernel read into a window, the one overlay change on the path from main to the driver loop head that is neither a
   runner segment nor a call site (port/mnloop-prefix-leaves.md §5): the read node of rd_step_pos_cf
   (lib/A/PresetRdcfA.v:205-206, B: lib/AU/PresetRdcfB.v:216-217) leaves the overlay `wbytes mem (Z_to_bv 64 a) bs`
   (srr_read_win, lib/A/AD25.v:98, post :111; B: lib/Reusable/YD25.v:102).
   rule 24: no function proved. rule 24: proves no function (kind: segment lemma).

   - memnorm_wbytes: YK0h.wbytes, one YAkMemnorm.memnorm_upd per byte; each written byte has wview defined in every
     overlay (the form seg_win_wview gives: the window is in writable segments).
   - memnorm_read_win: the read node's overlay, from the read lemma's own window premise
     seg_win_check segs a 65536 = true (srr_read_win's premise; at RS_LO it is proj2 rs_win_check).
   Generic in segs, so the A image and the B image use this one file. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK00 YK0h.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YL0b YAkMemnorm.
Import ListNotations.
Open Scope Z_scope.

Lemma memnorm_wbytes : forall segs bs m (addr : word),
  YAkMemnorm.memnorm segs m ->
  bv_unsigned addr + Z.of_nat (length bs) < 2 ^ 64 ->
  (forall (m' : word -> option byte) i, 0 <= i < Z.of_nat (length bs) ->
     wview segs m' (Z_to_bv 64 (bv_unsigned addr + i)) <> None) ->
  YAkMemnorm.memnorm segs (wbytes m addr bs).
Proof.
  intros segs. induction bs as [|b bs IH]; intros m addr Hm Hw Hv; [exact Hm|].
  cbn [wbytes length] in *. pose proof (u64_range addr) as Ra.
  apply IH.
  - apply YAkMemnorm.memnorm_upd; [exact Hm|].
    pose proof (Hv m 0 ltac:(lia)) as H0. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in H0. exact H0.
  - rewrite u_add1 by lia. lia.
  - intros m' i Hi. rewrite u_add1 by lia.
    replace (bv_unsigned addr + 1 + i) with (bv_unsigned addr + (1 + i)) by lia. apply Hv. lia.
Qed.

Lemma memnorm_read_win : forall segs m (a : Z) bs,
  YAkMemnorm.memnorm segs m ->
  YL0b.seg_win_check segs a (Z.to_nat 65536) = true -> 0 <= a -> a + 65536 < 2 ^ 64 ->
  Z.of_nat (length bs) <= 65536 ->
  YAkMemnorm.memnorm segs (wbytes m (Z_to_bv 64 a) bs).
Proof.
  intros segs m a bs Hm Hck Ha Han Hlen.
  assert (Hau : bv_unsigned (Z_to_bv 64 a) = a) by (apply u64_lit; lia).
  apply memnorm_wbytes; [exact Hm | rewrite Hau; lia |].
  intros m' i Hi. rewrite Hau. apply (YL0b.seg_win_wview segs a 65536 m' (a + i) Hck); lia.
Qed.

Print Assumptions memnorm_wbytes.
Print Assumptions memnorm_read_win.
