(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.json_c.json_object_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsn5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsn5.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlES.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6sh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7z8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKTr.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWTC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWTC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QND5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QND5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsSk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsSk. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qt8n.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qt8n. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWtD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWtD. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDlz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDlz. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOTP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QOTP. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1LT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1LT. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpvH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpvH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCoy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCoy. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLPb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLPb. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QY73.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QY73. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q72M.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q72M. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDRB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDRB.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qo4M.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qo4M. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QrQA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QrQA. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLJz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLJz. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFop.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QFop. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q92D.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q92D.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QVyC.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDw3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNwL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import AP. Import APS.
Open Scope Z_scope.
Import QDw3(aentry, mkAE) QNwL(rlay, mkRL, ghost, tag_at).

Definition pg (E : env) (v : nat) : Z := 4096 * bv_unsigned (ev E v).

Definition X_main (E : env) : rlay := mkRL (pg E 237) (pg E 238) (pg E 478) (pg E 479) (pg E 330).

Definition st_main (E : env) : Z := 32768 * bv_unsigned (ev E 0) + 4096 * bv_unsigned (ev E 10).

Definition LA_main (w : bool) (E : env) : Q6sh.ALay := QVyC.LA_J (SB E) (PRES E) (PARR E) (objs_of w E) (atopE E).

Definition RE_main (sp : word) (w : bool) (E : env) : aentry := mkAE (bv_unsigned sp) (st_main E) (pg E 406) (LA_main w E).

Definition G_main : ghost := fun _ => [].
Lemma G_main_tag : forall c i, tag_at G_main c i = None.
Proof. intros c i. unfold tag_at, G_main. destruct (i <? 0); [reflexivity|]. destruct (Z.to_nat i); reflexivity. Qed.

Definition guard_main (E : env) : word := ev E 45.

Definition band_main (E : env) (RANGE : 0x7fff7f800000 <= atopE E <= 0x7fffff800000) : Band := mkBand (atopE E) RANGE (guard_main E).

Definition at_main_stmt (P : forall {BAND : Band}, word -> bool -> env -> (word -> option byte) -> Prop) : Prop :=
forall (sp : word) (rdraw : EntryDraw) (brk0 : word) (argv envp : list (list byte)) (fs : Fs.Fs) (uid hw : word)
(E : env) (R : bvmap 5 word) (FULL : word -> option byte) (mo : Model),
valid_sp sp -> valid_argv argv -> valid_envp envp -> entry_stack_fits sp argv envp ->
forall (w : bool) (ch : acs), HSCLASS_S w ch ->
cs_ok JO6SEGS AJO6 QVWI.Mq0.LIMIT (bv_unsigned sp) (SINV0 JO6PH sp rdraw brk0 argv envp uid hw) (argH0 JO6PH sp rdraw argv envp uid hw) fs E ch R FULL mo ->
forall BAND : Band, band_lo = atopE E -> band_guard = guard_main E ->
@P BAND sp w E (view (LV_J E) mo FULL).
