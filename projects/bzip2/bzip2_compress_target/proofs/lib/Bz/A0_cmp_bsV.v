(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzArrD BzCSortM CmpMem BzCLemmasMs CmpMsKit AsanKit AsanCut A0_cmp_msV A0_cmp_msW.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.
Definition msenv_ok1 (X : msenv) : Prop :=
  let usp := bv_unsigned (me_sp X) in
  0 < me_E X /\ me_E X + 55768 <= CEILm /\
  0 < me_A1 X /\ me_A1 X + ARR1_SIZE <= CEILm /\
  0 < me_A2 X /\ me_A2 X + ARR2_SIZE <= CEILm /\
  0 < me_FT X /\ me_FT X + 262148 <= CEILm /\
  CEILm <= me_lo X /\ me_lo X + 8192 <= usp /\ usp < 18446744073709551616 /\
  me_E X = 16 * me_qE X /\ me_A1 X = 16 * me_q1 X /\ me_A2 X = 16 * me_q2 X /\ me_FT X = 16 * me_qF X /\ usp = 16 * me_qsp X /\
  1 <= me_n X <= (NBLOCKMAX + 19) /\
  zbok (me_a1 X) /\ zbok (me_a2 X) /\ (forall i, 0 <= zget (me_ft X) i < 4294967296).
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma amenv_sepx_of1 : forall X Y, msenv_ok1 X -> amenv_ok X Y -> amenv_sep X Y -> amenv_sepx X Y.
Proof.
  intros X Y XOK YOK YSEP.
  unfold amenv_ok, CEILm in YOK. cbv zeta in YOK.
  unfold amenv_sep, apartm in YSEP. unfold amenv_sepx, apartm.
  destruct YOK as (_ & _ & _ & _ & ? & ? & ? & ? & ? & ? & ? & ? & ? & _).
  destruct YSEP as (S0 & S1 & S2 & S3).
  repeat split; lia.
Qed.
Lemma amenv_shx_of1 : forall X Y SHF, msenv_ok1 X -> amenv_ok X Y -> amenv_shf Y SHF -> amenv_offsh X Y -> amenv_shx X Y SHF.
Proof.
  intros X Y SHF XOK YOK (_ & SL & SH) YOFF. pose proof alloc_ceiling_range as ACR.
  unfold msenv_ok1, CEILm in XOK. cbv zeta in XOK. unfold amenv_ok, CEILm in YOK. cbv zeta in YOK.
  unfold amenv_offsh, SH_LO, SH_HI in YOFF. unfold SH_LO, SH_HI in SL, SH. unfold amenv_shx, apartm, SH_HI.
  destruct XOK as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & _).
  destruct YOK as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & _).
  destruct YOFF as (O1 & O2 & O3 & O4).
  repeat split; lia.
Qed.
End ACeilS1.

(* [comment removed for export] *)
Ltac msenv_open1 XOK :=
  let H := fresh "XL" in
  pose proof XOK as H; unfold msenv_ok1, CEILm in H; cbv zeta in H;
  let A1OK := fresh "A1OK" in let A2OK := fresh "A2OK" in let FTOK := fresh "FTOK" in
  cps_destruct H as (?XEl & ?XEh & ?XA1l & ?XA1h & ?XA2l & ?XA2h & ?XFl & ?XFh & ?XLO & ?XLOF & ?XSP & ?ALE & ?AL1 & ?AL2 & ?ALF & ?ALS
              & ?LNB & A1OK & A2OK & FTOK).
