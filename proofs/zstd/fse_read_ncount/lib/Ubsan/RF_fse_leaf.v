(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Spec Require Import FseNCount.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Common Require Import FseWalkKit.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import UImgX RF_fse_iface.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Lemma fse_iserror_proof : fse_iserror_stmt.
Proof.
intros until c. intros Hc ->. unfold PFSE_ISERROR.
zstep. zstep. zstep.
replace (Z.lxor (Z.b2z (c <? 18446744073709551497)) 1) with (Z.b2z (2^64 - 119 <=? c))
by (destruct (Z.ltb_spec c 18446744073709551497); destruct (Z.leb_spec (2^64 - 119) c); cbn; try reflexivity; lia).
apply evt_done. reflexivity.
Qed.
Lemma fse_wbound_proof : fse_wbound_stmt.
Proof.
intros until tl. intros Hm Ht -> ->. unfold PFSE_WBOUND.
zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0090>10519033705.3811160981067.4621778203464.4529782203372.3842549348910.4745876098888.3859851873178.4768684349068.387606134511.37 00000300400D00E00I00J00N00O00SS1BFS2Hm2Ht1K1B1H2H0SS2HmSS2HtSS2Hm".
if_cases K; zify_cond K.
- do 5 zstep. zstep.
assert (B : 0 <= (msv + 1) * tl + 6 < 4294967296) by nia.
rewrite (Z.mod_small _ 18446744073709551616) by lia.
rewrite wrap32_small by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
rewrite swrap32_small by (Z.div_mod_to_equations; lia).
apply evt_done. unfold fse_wbound_post, write_bound, FSE_NCOUNTBOUND.
rewrite (proj2 (Z.eqb_neq msv 0) K). eexists.
replace ((msv + 1) * tl + 4 + 2) with ((msv + 1) * tl + 6) by lia.
replace (((msv + 1) * tl + 6) / 8 + 1 + 2) with (((msv + 1) * tl + 6) / 8 + 3) by lia.
reflexivity.
- zstep. zstep. apply evt_done. unfold fse_wbound_post, write_bound, FSE_NCOUNTBOUND.
rewrite (proj2 (Z.eqb_eq msv 0) K). eexists. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
