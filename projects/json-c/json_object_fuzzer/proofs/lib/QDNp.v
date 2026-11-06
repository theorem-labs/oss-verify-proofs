(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.json_c.json_object_fuzzer.images Require AsanUbsan.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QyaF QXVi QWTC Q85Z Qo8J QND5 Qt8n QWtD QqZL QDlz QOTP Q1LT QEdo Qz8O Q0qZ QCoy QKY2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.json_c.json_object_fuzzer.images.AsanUbsan.
Import QyaF QXVi.
Import QWTC Q85Z.Mq1 Qo8J.Mq0 QND5.
Import Qt8n QWtD QqZL.Mq2 QDlz QOTP Q1LT.
Import QqZL.Mq1 QEdo.Mq3.
Import Qz8O.Mq1 Q0qZ.Mq5 QCoy.Mqd QKY2.
Import QWTC.
Local Instance asanimg_fx : QWTC.FPState := QWTC.fx0.
Import ListNotations.
Open Scope Z_scope.

Lemma istrncpy_clob_sub : forall r, In r istrncpy_clob -> In (AX2.ridx r) AP.caller_saved.
Proof.
intros r H. unfold istrncpy_clob in H. cbn [In] in H.
repeat (destruct H as [<-|H]; [cbn; tauto|]). destruct H.
Qed.

Lemma asan_istrncpy_spec : APSX.istrncpy_spec JOB6SEGS (AP.x_istrncpy BJO6) (AP.x_sealed BJO6).
Proof.
intros mem0 dst regs ret Hnone Hst Hnw Hdisj Hret R1 R10 R11 R12.
destruct (asan_istrncpy_sealed mem0 dst (seg_rom JOB6SEGS) regs ret Hnone Hst Hnw Hdisj Hret R1 R10 R11 R12)
as (regs' & Hms & Hag).
exists regs'. split; [|split].
- replace APSX.SEALED_BYTES with strncpy_sealed_bytes by reflexivity.
replace (Z_to_bv 64 (AP.x_istrncpy BJO6)) with asan_istrncpy_entry by (apply bv_eq; reflexivity). exact Hms.
- eapply kept_ok_of_regs_agree; [apply istrncpy_clob_sub | exact Hag].
- rewrite <- R10. apply Hag. unfold istrncpy_clob. cbn. intros [H|[H|[H|[H|[H|[]]]]]]; discriminate.
Qed.

Lemma asan_popfree_spec' : popfree_spec JOB6SEGS (AP.x_popfree BJO6).
Proof. exact asan_popfree_spec. Qed.

Section AsanNodes.
Variable nx0 : nat.
Variable LIMIT : Z.
Variable USP : Z.
Hypothesis NX0_ge : APS.nx0_ge nx0.
Variable SINV : AX2.env -> (word -> option byte) -> Prop.
Variable argH : AX2.env -> word -> bool.
Hypothesis argH_high : forall E (a : word), argH E a = true -> AP.CEIL <= bv_unsigned a.
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
Variable FS0 : Fs.Fs.

#[local] Notation XSTMT := (APS.x_stmt JOB6SEGS BJO6 nx0 LIMIT USP SINV argH FS0).

Theorem asan_node_x_sound_XIMemset : XSTMT AP.XIMemset.
Proof. eapply APSX.node_x_sound_XIMemset; try eassumption; try apply asan_segs_wr; try apply asan_wx; try apply asan_in_hull;
try apply asan_res_len; try apply asan_hull_ok. apply asan_fill_spec_imemset. Qed.
Theorem asan_node_x_sound_XMemset : XSTMT AP.XMemset.
Proof. eapply APSX.node_x_sound_XMemset; try eassumption; try apply asan_segs_wr; try apply asan_wx; try apply asan_in_hull;
try apply asan_res_len; try apply asan_hull_ok. apply asan_fill_spec_memset. Qed.
Theorem asan_node_x_sound_XIMemcpy : XSTMT AP.XIMemcpy.
Proof. eapply APSX.node_x_sound_XIMemcpy; try eassumption; try apply asan_segs_wr; try apply asan_wx; try apply asan_in_hull;
try apply asan_res_len; try apply asan_hull_ok. apply asan_copy_spec_imemcpy. Qed.
Theorem asan_node_x_sound_XMemcpy : XSTMT AP.XMemcpy.
Proof. eapply APSX.node_x_sound_XMemcpy; try eassumption; try apply asan_segs_wr; try apply asan_wx; try apply asan_in_hull;
try apply asan_res_len; try apply asan_hull_ok. apply asan_copy_spec_memcpy. Qed.
Theorem asan_node_x_sound_XMemIsZero : XSTMT AP.XMemIsZero.
Proof. eapply APSX.node_x_sound_XMemIsZero; try eassumption; try apply asan_segs_wr; try apply asan_wx; try apply asan_in_hull;
try apply asan_res_len; try apply asan_hull_ok. apply asan_miz_spec. Qed.
Theorem asan_node_x_sound_XIStrncpy : XSTMT AP.XIStrncpy.
Proof. eapply APSX.node_x_sound_XIStrncpy; try eassumption; try apply asan_segs_wr; try apply asan_wx; try apply asan_in_hull;
try apply asan_res_len; try apply asan_hull_ok. apply asan_istrncpy_spec. Qed.
Theorem asan_node_x_sound_XPopFree : XSTMT AP.XPopFree.
Proof. eapply APSX.node_x_sound_XPopFree; try eassumption; try apply asan_segs_wr; try apply asan_wx; try apply asan_in_hull;
try apply asan_res_len; try apply asan_hull_ok. apply asan_popfree_spec'. Qed.
End AsanNodes.
End Mq0.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.json_c.json_object_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCoy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCoy. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLPb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLPb.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWTC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWTC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q85Z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q85Z.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qo8J.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qo8J.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QND5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QND5.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qt8n.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qt8n. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWtD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWtD. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QqZL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QqZL.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDlz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDlz. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOTP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QOTP. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1LT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1LT.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QqZL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QqZL.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEdo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEdo.Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qz8O.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qz8O.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0qZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0qZ.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCoy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCoy.Mq6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDRB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDRB.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWTC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWTC.
Local Instance asanimg_fx : QWTC.FPState := QWTC.fx0.
Import ListNotations.
Open Scope Z_scope.

Lemma istrncpy_clob_sub : forall r, In r istrncpy_clob -> In (AX2.ridx r) AP.caller_saved.
Proof.
intros r H. unfold istrncpy_clob in H. cbn [In] in H.
repeat (destruct H as [<-|H]; [cbn; tauto|]). destruct H.
Qed.

Lemma asan_istrncpy_spec : APSX.istrncpy_spec JO6SEGS (AP.x_istrncpy AJO6) (AP.x_sealed AJO6).
Proof.
intros mem0 dst regs ret Hnone Hst Hnw Hdisj Hret R1 R10 R11 R12.
destruct (asan_istrncpy_sealed mem0 dst (seg_rom JO6SEGS) regs ret Hnone Hst Hnw Hdisj Hret R1 R10 R11 R12)
as (regs' & Hms & Hag).
exists regs'. split; [|split].
- replace APSX.SEALED_BYTES with strncpy_sealed_bytes by reflexivity.
replace (Z_to_bv 64 (AP.x_istrncpy AJO6)) with asan_istrncpy_entry by (apply bv_eq; reflexivity). exact Hms.
- eapply kept_ok_of_regs_agree; [apply istrncpy_clob_sub | exact Hag].
- rewrite <- R10. apply Hag. unfold istrncpy_clob. cbn. intros [H|[H|[H|[H|[H|[]]]]]]; discriminate.
Qed.

Lemma asan_popfree_spec' : popfree_spec JO6SEGS (AP.x_popfree AJO6).
Proof. exact asan_popfree_spec. Qed.

Section AsanNodes.
Variable nx0 : nat.
Variable LIMIT : Z.
Variable USP : Z.
Hypothesis NX0_ge : APS.nx0_ge nx0.
Variable SINV : AX2.env -> (word -> option byte) -> Prop.
Variable argH : AX2.env -> word -> bool.
Hypothesis argH_high : forall E (a : word), argH E a = true -> AP.CEIL <= bv_unsigned a.
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
Variable FS0 : Fs.Fs.

#[local] Notation XSTMT := (APS.x_stmt JO6SEGS AJO6 nx0 LIMIT USP SINV argH FS0).

Theorem asan_node_x_sound_XIMemset : XSTMT AP.XIMemset.
Proof. eapply APSX.node_x_sound_XIMemset; try eassumption; try apply asan_segs_wr; try apply asan_wx; try apply asan_in_hull;
try apply asan_res_len; try apply asan_hull_ok. apply asan_fill_spec_imemset. Qed.
Theorem asan_node_x_sound_XMemset : XSTMT AP.XMemset.
Proof. eapply APSX.node_x_sound_XMemset; try eassumption; try apply asan_segs_wr; try apply asan_wx; try apply asan_in_hull;
try apply asan_res_len; try apply asan_hull_ok. apply asan_fill_spec_memset. Qed.
Theorem asan_node_x_sound_XIMemcpy : XSTMT AP.XIMemcpy.
Proof. eapply APSX.node_x_sound_XIMemcpy; try eassumption; try apply asan_segs_wr; try apply asan_wx; try apply asan_in_hull;
try apply asan_res_len; try apply asan_hull_ok. apply asan_copy_spec_imemcpy. Qed.
Theorem asan_node_x_sound_XMemcpy : XSTMT AP.XMemcpy.
Proof. eapply APSX.node_x_sound_XMemcpy; try eassumption; try apply asan_segs_wr; try apply asan_wx; try apply asan_in_hull;
try apply asan_res_len; try apply asan_hull_ok. apply asan_copy_spec_memcpy. Qed.
Theorem asan_node_x_sound_XMemIsZero : XSTMT AP.XMemIsZero.
Proof. eapply APSX.node_x_sound_XMemIsZero; try eassumption; try apply asan_segs_wr; try apply asan_wx; try apply asan_in_hull;
try apply asan_res_len; try apply asan_hull_ok. apply asan_miz_spec. Qed.
Theorem asan_node_x_sound_XIStrncpy : XSTMT AP.XIStrncpy.
Proof. eapply APSX.node_x_sound_XIStrncpy; try eassumption; try apply asan_segs_wr; try apply asan_wx; try apply asan_in_hull;
try apply asan_res_len; try apply asan_hull_ok. apply asan_istrncpy_spec. Qed.
Theorem asan_node_x_sound_XPopFree : XSTMT AP.XPopFree.
Proof. eapply APSX.node_x_sound_XPopFree; try eassumption; try apply asan_segs_wr; try apply asan_wx; try apply asan_in_hull;
try apply asan_res_len; try apply asan_hull_ok. apply asan_popfree_spec'. Qed.
End AsanNodes.
