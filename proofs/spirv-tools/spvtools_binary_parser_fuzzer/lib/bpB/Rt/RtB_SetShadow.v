(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Bs0Gc.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BBytes BZBridge BacX BSFModel BSysStep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsWalk B_memset RtB_Iface.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Section HCW.
  Context {HCEIL : HeapCeil}.

Lemma rw_cells_CB0_any_ss : forall m a, 0 <= a <= 2^64 -> rw_cells asegs m a [CB 0 []].
Proof.
  intros m a Ha. split; [split|].
  - cbn. exact (conj eq_refl I).
  - split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
  - split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
Qed.

Section S00.
  Lemma set_shadow_00_ok : set_shadow_stmt 0x00 ASET_SHADOW_00.
  Proof.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m sa n junk.
    intros Ha0 Ha1 Hn DST MI AC. subst a0 a1. unfold ASET_SHADOW_00.
    pose proof (ACONST_memsetp m AC) as [G1 G2]. unfold AGOT_MEMSETP, AMEMSETP_CELL, AREAL_MEMSET, wz in G1, G2.
    pose proof (rw_cells_bound _ _ _ _ DST) as B. cbn [cells_size csize Nat.add] in B. rewrite Nat.add_0_r, Z2Nat.id in B by lia.
    assert (SA : 0 <= sa < 2^64 \/ (sa = 2^64 /\ n = 0)) by lia.
    zstep. zstep. zstep. zstep. zstep. zstep.
    destruct SA as [SA|[Esa En]].
    - eapply evt_mono.
      { eapply memset_spec; [| exact MI]. rewrite !unsigned_lit by lia. exact DST. }
      intros ms' PO. unfold memset_post in PO. unfold set_shadow_post.
      destruct PO as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & m' & E & MU & WM & MI' & RC).
      rewrite !unsigned_lit in MU, RC by lia.
      exists x0, x1, x2, (Z_to_bv 64 sa), x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, m'.
      split; [exact E|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|].
      unfold poison_bytes, b8. change (0 mod 256) with 0 in RC. exact RC.
    - subst sa n. eapply evt_mono.
      { eapply (memset_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ []); [| exact MI].
        replace (bv_unsigned (Z_to_bv 64 (2 ^ 64))) with 0 by (vm_compute; reflexivity).
        rewrite unsigned_lit by lia. apply rw_cells_CB0_any_ss. lia. }
      intros ms' PO. unfold memset_post in PO. unfold set_shadow_post.
      destruct PO as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & m' & E & MU & WM & MI' & RC).
      replace (bv_unsigned (Z_to_bv 64 (2 ^ 64))) with 0 in MU by (vm_compute; reflexivity).
      rewrite !unsigned_lit in MU by lia.
      exists x0, x1, x2, (Z_to_bv 64 (2 ^ 64)), x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, m'.
      split; [exact E|]. split.
      { eapply munch_weaken; [| exact MU]. unfold sub_fp. cbn [outside]. intros x Hx. lia. }
      split; [exact WM|]. split; [exact MI'|].
      apply rw_cells_CB0_any_ss. lia.
  Qed.
End S00.

Section Sf8.
  Lemma set_shadow_f8_ok : set_shadow_stmt 0xf8 ASET_SHADOW_F8.
  Proof.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m sa n junk.
    intros Ha0 Ha1 Hn DST MI AC. subst a0 a1. unfold ASET_SHADOW_F8.
    pose proof (ACONST_memsetp m AC) as [G1 G2]. unfold AGOT_MEMSETP, AMEMSETP_CELL, AREAL_MEMSET, wz in G1, G2.
    pose proof (rw_cells_bound _ _ _ _ DST) as B. cbn [cells_size csize Nat.add] in B. rewrite Nat.add_0_r, Z2Nat.id in B by lia.
    assert (SA : 0 <= sa < 2^64 \/ (sa = 2^64 /\ n = 0)) by lia.
    zstep. zstep. zstep. zstep. zstep. zstep.
    destruct SA as [SA|[Esa En]].
    - eapply evt_mono.
      { eapply memset_spec; [| exact MI]. rewrite !unsigned_lit by lia. exact DST. }
      intros ms' PO. unfold memset_post in PO. unfold set_shadow_post.
      destruct PO as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & m' & E & MU & WM & MI' & RC).
      rewrite !unsigned_lit in MU, RC by lia.
      exists x0, x1, x2, (Z_to_bv 64 sa), x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, m'.
      split; [exact E|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|].
      unfold poison_bytes, b8. change (248 mod 256) with 248 in RC. exact RC.
    - subst sa n. eapply evt_mono.
      { eapply (memset_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ []); [| exact MI].
        replace (bv_unsigned (Z_to_bv 64 (2 ^ 64))) with 0 by (vm_compute; reflexivity).
        rewrite unsigned_lit by lia. apply rw_cells_CB0_any_ss. lia. }
      intros ms' PO. unfold memset_post in PO. unfold set_shadow_post.
      destruct PO as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & m' & E & MU & WM & MI' & RC).
      replace (bv_unsigned (Z_to_bv 64 (2 ^ 64))) with 0 in MU by (vm_compute; reflexivity).
      rewrite !unsigned_lit in MU by lia.
      exists x0, x1, x2, (Z_to_bv 64 (2 ^ 64)), x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, m'.
      split; [exact E|]. split.
      { eapply munch_weaken; [| exact MU]. unfold sub_fp. cbn [outside]. intros x Hx. lia. }
      split; [exact WM|]. split; [exact MI'|].
      apply rw_cells_CB0_any_ss. lia.
  Qed.
End Sf8.

End HCW.
