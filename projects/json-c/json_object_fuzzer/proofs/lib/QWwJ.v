(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch's ProcInput: at_main_stmt quantifies over the launch's whole input with QpvH.launch_ok in place of entry_stack_fits, and SINV0 and argH0 at it; the main-entry states' variable numbers renumbered for the states the build computes, by the map read off the new start-up run). *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.json_c.json_object_fuzzer.images Require Import AsanUbsan.
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
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QyaF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QyaF. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXVi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXVi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQjP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQjP. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJQc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJQc. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKY2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKY2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXDj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXDj. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q45h.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q45h. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOTx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QOTx. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q25t.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q25t. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHqi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHqi.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qi08.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWRO. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFQR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import AP. Import APS.
Open Scope Z_scope.
Import QWRO(aentry, mkAE) QFQR(rlay, mkRL, ghost, tag_at).

Definition pg (E : env) (v : nat) : Z := 4096 * bv_unsigned (ev E v).

Definition X_main (E : env) : rlay := mkRL (pg E 241) (pg E 242) (pg E 484) (pg E 485) (pg E 336).

Definition st_main (E : env) : Z := 32768 * bv_unsigned (ev E 0) + 4096 * bv_unsigned (ev E 10).

Definition LA_main (w : bool) (E : env) : Q6sh.ALay := Qi08.LA_J (SB E) (PRES E) (PARR E) (objs_of w E) (atopE E).

Definition RE_main (sp : word) (w : bool) (E : env) : aentry := mkAE (bv_unsigned sp) (st_main E) (pg E 412) (LA_main w E).

Definition G_main : ghost := fun _ => [].
Lemma G_main_tag : forall c i, tag_at G_main c i = None.
Proof. intros c i. unfold tag_at, G_main. destruct (i <? 0); [reflexivity|]. destruct (Z.to_nat i); reflexivity. Qed.

Definition guard_main (E : env) : word := ev E 49.

Definition band_main (E : env) (RANGE : 0x7fff7f800000 <= atopE E <= 0x7fffff800000) : Band := mkBand (atopE E) RANGE (guard_main E).

Definition at_main_stmt (P : forall {BAND : Band}, word -> bool -> env -> (word -> option byte) -> Prop) : Prop :=
forall (sp : word) (rdraw : EntryDraw) (brk0 : word) (argv envp : list (list byte)) (fs : Fs.Fs) (uid hw : word) (apc : N) (mbase : word) (ifs : Fs.Fs) (stdin : InputStream) (gid : word) (groups : list word) (net : NetQueue) (nofile sigmask : word) (abort_terminal : bool) (urnd : InputStream) (tmp : Fs.Fs) (kb : KernelBuild) (execfn : list byte) (rdr sgd sgt : bool)
(E : env) (R : bvmap 5 word) (FULL : word -> option byte) (mo : Model),
valid_sp sp -> valid_argv argv -> valid_envp envp -> QpvH.launch_ok sp brk0 mbase rdraw (QpvH.inp argv envp ifs stdin uid gid hw groups net nofile sigmask abort_terminal urnd tmp kb execfn rdr sgd sgt) ->
forall (w : bool) (ch : acs), HSCLASS_S w ch ->
cs_ok JOB6SEGS BJO6 QVWI.Mq0.LIMIT (bv_unsigned sp) (SINV0 JOB6PH apc sp rdraw brk0 mbase argv envp ifs stdin uid gid hw groups net nofile sigmask abort_terminal urnd tmp kb execfn rdr sgd sgt) (argH0 sp rdraw argv envp kb execfn) fs E ch R FULL mo ->
forall BAND : Band, band_lo = atopE E -> band_guard = guard_main E ->
@P BAND sp w E (view (LV_J E) mo FULL).
