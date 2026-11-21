(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Lib Require Import Arr Bytes ZBridge Tac InitMem StoreFast.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Spec Require Import AsanCtrl.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.BothW Require Import BImg RtCells ABase ABytes AMalloc_iface AUri_kit.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AKit U2AArr U2AStore InfAGlue InfPure InfPure_w7 InfPure_w7d InfPure_w7e InfPure_w7f InfPure_w7h InfAGlue_w7 InfAGlue_w7b.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import U2AObj.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U1B Require Import U2BObj U2BClient U2BIface InfBBase InfBKit InfBTables InfB_w7base InfB_w7tab InfB_w7tab16 InfB_w7pull InfB_w7ltab InfB_w7lenr InfB_len13S InfB_len2 InfB_len4 InfB_len5 InfB_len5b InfB_len3 InfB_len1 InfB_lenx InfB_lenFS InfB_len6 InfB_len_ InfB_lenF InfB_distx InfB_dist6 InfB_match3.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U1B Require Import U2BIface_fit2_draft.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U1B Require Import U2BKit U2BKit_p04 InfBTraps.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load_hyp :=
  match goal with
  | |- context [ov_read_bytes ?segs ?m ?a ?n] => match goal with HR : ov_read_bytes segs m a n = Some _ |- _ => rewrite HR end
  end; load_post.
Local Ltac solve_load ::= first [ solve_load_hyp | solve_load_sh0 | solve_load_shlit | solve_load_base | solve_load_image ].
Local Ltac acc_hint_hyp := lazymatch goal with |- acc_in ?R ?x => match goal with HA : acc_in R x |- _ => exact HA end end.
Local Ltac acc_hint ::= first [ acc_hint_hyp | acc_hint_sh ].
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= farr_store_extra m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= farr_call_extra segs W m m' MU WM.
Local Ltac ub_is_trap pc ::= ub_in_traps inf_traps pc.

Section CANSEC1. Context {rc : runConstT}.
Section T.
  Variable AI : AMallocIface.
  Variable rng_fs : alayout -> footprint -> Prop.
  Notation GARMG Lb X :=
    (forall L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh cx ly,
       garm_stmtA cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh Lb X).
  Notation ARMG Lb X :=
    (forall L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh, rng_fs L RNG -> atmost1_c2 LB -> tp = Z_to_bv 64 ATP ->
     forall cx ly, l_SP ly + 16 < al_top L -> rng RNG (l_lo ly) (al_top L - l_lo ly) ->
     arm_stmtA cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh Lb X).
  Lemma HMATCH : GARMG 0x91f8c MATCH.
  Proof. intros. apply match_garm. Qed.
  Hypothesis IFAST : inflate_fast_stmtA.
  Lemma HFAST : forall L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh cx ly,
    LFAST_STMT AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh cx ly.
  Proof. intros. apply lfast. exact IFAST. Qed.

  Lemma g_DISTEXT : GARMG 0x8e3a0 DISTEXT.
  Proof. intros. apply distx_garm. apply HMATCH. Qed.
  Lemma g_DIST : GARMG 0x91a10 DIST.
  Proof. intros. apply dist_garm. apply HMATCH. Qed.
  Lemma g_LENEXT : GARMG 0x8e3c0 LENEXT.
  Proof. intros. apply lenx_garm. apply g_DIST. Qed.
  Lemma g_LEN : GARMG 0x913c0 LEN.
  Proof. intros. apply len_garm; [apply g_DIST| apply HFAST]. Qed.
  Lemma g_LEN_ : GARMG 0x913a4 LEN_.
  Proof. intros. apply len__garm. apply g_LEN. Qed.

  Theorem A_MATCH : ARMG 0x91f8c MATCH.   Proof. intros. apply garm_arm. apply HMATCH. Qed.
  Theorem A_DISTEXT : ARMG 0x8e3a0 DISTEXT. Proof. intros. apply garm_arm. apply g_DISTEXT. Qed.
  Theorem A_DIST : ARMG 0x91a10 DIST.     Proof. intros. apply garm_arm. apply g_DIST. Qed.
  Theorem A_LENEXT : ARMG 0x8e3c0 LENEXT. Proof. intros. apply garm_arm. apply g_LENEXT. Qed.
  Theorem A_LEN : ARMG 0x913c0 LEN.       Proof. intros. apply garm_arm. apply g_LEN. Qed.
  Theorem A_LEN_ : ARMG 0x913a4 LEN_.     Proof. intros. apply garm_arm. apply g_LEN_. Qed.
End T.
End CANSEC1.
