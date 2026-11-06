(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import FseNCount.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Arr Bytes ZBridge.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AImg ABase RtCells AF_fse_iface.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import FseWalkKitF.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_orc_old ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_k12.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.slia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.slia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.flia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.flia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange_nonneg ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_nonneg_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.solve_load ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.solve_load_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.word_eq_tac_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common.FseWalkKit.simpl_arr_sizes_fwk_k12.
(* [comment removed for export] *)

Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Section CANSEC1. Context {rc : runConstT}.
#[using="Type"] Lemma fse_iserror_proofA : fse_iserror_stmtA.
Proof.
intros until c. intros Hc ->. unfold AFSE_ISERROR.
zstep. zstep. zstep.
replace (Z.lxor (Z.b2z (c <? 18446744073709551497)) 1) with (Z.b2z (2^64 - 119 <=? c))
by (destruct (Z.ltb_spec c 18446744073709551497); destruct (Z.leb_spec (2^64 - 119) c); cbn; try reflexivity; lia).
apply evtF_done. reflexivity.
Qed.
#[using="Type"] Lemma fse_wbound_proofA : fse_wbound_stmtA.
Proof.
intros until tl. intros Hm Ht -> ->. unfold AFSE_WBOUND.
zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0090>10519033705.4011160981067.4811556852459.4029782203372.4042549348910.4945876098888.4059851873178.4968684349068.407606134511.39 00000300400700800<00=00A00B00FS1BFS1BSS2HmSS2HtSS2Hm".
if_cases K; zify_cond K.
- zstep. zstep. apply evtF_done. unfold fse_wbound_postA, write_bound, FSE_NCOUNTBOUND.
rewrite (proj2 (Z.eqb_eq msv 0) K). eexists. reflexivity.
- do 5 zstep. zstep.
assert (B : 0 <= (msv + 1) * tl + 6 < 4294967296) by nia.
rewrite (Z.mod_small ((msv + 1) * tl + 6) 18446744073709551616) by lia.
rewrite wrap32_small by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
rewrite FseWalkKit.swrap32_small by lia.
apply evtF_done. unfold fse_wbound_postA, write_bound, FSE_NCOUNTBOUND.
rewrite (proj2 (Z.eqb_neq msv 0) K). eexists.
replace ((msv + 1) * tl + 4 + 2) with ((msv + 1) * tl + 6) by lia.
replace (((msv + 1) * tl + 6) / 8 + 1 + 2) with (((msv + 1) * tl + 6) / 8 + 3) by lia.
reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC1.
