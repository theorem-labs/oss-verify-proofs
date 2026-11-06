(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0 SegsB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzTac2 BzArr BzCMem BzCStream BzCState BzCBlock BzArrD CmpMem CmpCut CmpFsKit0 AsanKit AsanCut AsanCutB0.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpCut6.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Export A0_cmp_cbV.
Local Open Scope Z_scope.

Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.
(* [comment removed for export] *)
Definition cbenv_ok (X : cbenv) : Prop :=
  let usp := bv_unsigned (ce_sp X) in let cx := ce_cx X in
  cctx_ok cx /\ cctx_sep cx /\
  0x62b000 <= c_E cx /\ 0x62b000 <= c_A1 cx /\ 0x62b000 <= c_A2 cx /\ 0x62b000 <= c_FT cx /\
  CEILv <= ce_lo X /\ ce_lo X + 512 <= usp /\ usp < 18446744073709551616 /\ usp mod 16 = 0.
End ACeilS1.

(* [comment removed for export] *)
Ltac cbenv_open XOK :=
  let H := fresh "XL" in
  pose proof XOK as H; unfold cbenv_ok, CEILv in H; cbv zeta in H;
  cps_destruct H as (?CX & ?SEP & ?XEi & ?XA1i & ?XA2i & ?XFTi & ?XLO & ?XST & ?XSP & ?ALS).
