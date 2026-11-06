(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import StrFun.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import Shadow StepF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import BImg RtCells Stdio_kit Strnlen_iface I_strnlen.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_orc_old ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_k12.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.slia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.slia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.flia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.flia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange_nonneg ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_nonneg_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.solve_load ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.solve_load_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.word_eq_tac_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes_k12.
(* [comment removed for export] *)

Open Scope Z_scope.
Section CANSEC1. Context {rc : runConstT}.
#[using="Type"] Lemma hitlen0_strnlen_rl : forall n buf, hitlen 0 n buf = strnlen_rl n buf.
Proof. reflexivity. Qed.
#[using="Type"] Theorem strnlen_a_proof : strnlen_a_stmt.
Proof.
unfold strnlen_a_stmt. intros RNG r. intros until lo.
intros -> -> PPOS Hn BUF OK MI ST LO KLO SEPB ENV RC IR RL40 RI RSTK RB RR.
pose proof (rclean_shclean _ _ RC) as (U & HULL & W & AB). unfold hull64 in HULL. unfold inreg in IR. unfold rrng in RR.
Local Ltac2 Set LiaHints.tbl := fun () => "00<0>11670946544.7712578215384.7713908435495.6213991325197.7717944380038.7722700267513.992425070162.60 2427413826.61 33283298842.7739234347908.7753086975564.7761929570482.7600000F00J00K00T00Y00\00`00d00e00i00m011S4PPOS2IR4HULL3RL03AB2S2IRSS2IR4HULLS3RL0S1HS2HnS2HnFS2IRS2LOS2Hn".
pose proof (strnlen_rl_res n buf ltac:(lia)) as RLR.
assert (RL0 : 0 <= strnlen_rl n buf).
{ unfold strnlen_rl. destruct (find_byte 0 (firstn (Z.to_nat n) buf)); lia. }
destruct ENV as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14).
assert (UP : bv_unsigned (Z_to_bv 64 P) = P).
{ apply unsigned_lit. pose proof AB as [AB1 AB2]. unfold KLOW, KHIGH, KEND in AB2. lia. }
assert (UN : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
unfold STRNLEN_I_DEPTH in LO.
eapply evtF_mono.
{ eapply (strnlen_i_spec RNG ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc m lo buf (r_rlo r) (r_rhi r)); rewrite ?UP, ?UN, ?hitlen0_strnlen_rl; try assumption; try lia.
- eapply app_blk_sub; [exact AB | lia | lia | lia].
- eapply unpoisoned_sub; [exact U | lia | lia]. }
cbv beta. intros ms' PO. unfold strnlen_i_post in PO. unfold strnlen_a_post, STRNLEN_I_DEPTH. rewrite ?UP, ?UN in PO.
destruct PO as (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m' & -> & MU & WM & MI' & ST' & BUF').
do 15 eexists. split; [reflexivity|]. split; [| repeat (split; [assumption|]); assumption].
eapply munch_weaken; [| exact MU]. unfold sub_fp. cbn [outside]. intros. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC1.
