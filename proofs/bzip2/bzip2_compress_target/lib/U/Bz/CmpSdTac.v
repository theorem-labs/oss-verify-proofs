(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Tac WalkLib.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require ZBridge.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge.Bytes OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.StoreFast.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzTac2. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzCStream BzCState BzCMtf BzArrD CmpMem. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut CmpCutSD. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzSepTac.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilTac.
Import ListNotations. Open Scope Z_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

(* [comment removed for export] *)
Ltac cbn_est_in H :=
  cbn [e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos
       e_nInUse e_inUse e_unseqToSeq e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF e_mtfFreq e_selector e_selectorMtf
       e_len e_code e_rfreq e_len_pack est_set_bw] in H.
Ltac cbn_est :=
  cbn [e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos
       e_nInUse e_inUse e_unseqToSeq e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF e_mtfFreq e_selector e_selectorMtf
       e_len e_code e_rfreq e_len_pack est_set_bw].

Ltac openCX3 CX SEP USP1 :=
  let H := fresh "CXL" in pose proof CX as H; bz_ceil; bz_params; unfold cctx_ok, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE, CEIL in H; cbv zeta in H;
  let U := fresh "USPL" in pose proof USP1 as U; bz_ceil; bz_params; unfold CEIL in U;
  cps_destruct H as (?XE0 & ?XE1 & ?XA10 & ?XA11 & ?XA20 & ?XA21 & ?XF0 & ?XF1 & ?Xb0 & ?Xb1 & ?Xf0 & ?Xf1 & ?ME & ?MA1 & ?MA2 & ?MF & ?Mb & ?Mf & ?LJ & ?LJb);
  let S := fresh "SP" in pose proof SEP as S; unfold cctx_sep, apart, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE in S; cbv zeta in S;
  cps_destruct S as (?AEA1 & ?AEA2 & _ & _ & _ & ?AA12 & _); hide_disj.

Ltac openMS3 Gmtf Gbs Gzb H :=
  let EH1 := ident:(EH1) in let EH2 := ident:(EH2) in let SLO := ident:(SLO) in let SHI := ident:(SHI) in let MU := ident:(MU) in cps_destruct H as (?EH1 & ?EH2 & ?AR2 & ?AR1 & ?INU & ?SLM & ?SEL & ?LEN & ?COD & ?SLO & ?SHI & ?I16 & ?MI & ?MU & ?WM);
  unfold sdW3 in MU;
  unfold EHEAD1, EHEAD2 in EH1, EH2; cbn_est_in EH1; cbn_est_in EH2;
  rewrite Gbs, Gmtf in EH2; rewrite Gzb, Gmtf in EH1; unfold sd_lo3 in SLO; unfold sd_hi3 in SHI.

Ltac closeMS3 Gmtf Gbs Gzb :=
  split; [|split; [| repeat (split; [eassumption|]); eassumption]];
  [ unfold EHEAD1; cbn_est; rewrite Gzb, Gmtf; eassumption
  | unfold EHEAD2; cbn_est; rewrite Gbs, Gmtf; eassumption ].

(* [comment removed for export] *)
(* [comment removed for export] *)
