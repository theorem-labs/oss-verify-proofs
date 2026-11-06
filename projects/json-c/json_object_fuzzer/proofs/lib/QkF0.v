(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.json_c.json_object_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEQM.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJyS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJyS. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsRG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsRG.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qnhz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qnhz.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9ox.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9ox.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBxa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBxa.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qn1e.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qn1e. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSpR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSpR.Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qdbv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qdbv. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWQV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWQV.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1oC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1oC.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1zM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1zM. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmsF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmsF.Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKNz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKNz.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QC8c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QC8c.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPZI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPZI.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qjk3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qjk3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmAj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmAj. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qdkw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qdkw.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYot.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYot. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q3dw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q3dw.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qqqm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qqqm. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDH9.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDH9. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Hp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Hp.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7J3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDH9.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDH9.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QtkK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QtkK. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBap.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBap. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QtkK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QtkK.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBap.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBap.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTWd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTWd.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTWd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTWd. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWOb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWOb. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBRj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBRj.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Section Main.
Context {fF : FPF} {fC : FPC}.
Context {AMB : Amb}.
Context {SL : SrcLim}.
Variable sp0 : word.
Variables a0s path : list byte.
Variable envv : list (list byte).
Variable tid : word.
Variable regs0 : bvmap 5 word.
Variable mem0 : word -> option byte.
Variable brk : word.
Variable mbase : word.
Variable fs0 : Fs.
Variable stdin0 : InputStream.
Hypothesis Hva : valid_argv [a0s; path].
Hypothesis Hve : valid_envp envv.
Hypothesis Hvsp : valid_sp sp0.
Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
Hypothesis ME : main_entry sp0 [a0s; path] envv tid regs0 mem0.
Hypothesis Hbrk : valid_brk RSEGS brk.
Hypothesis Hpne : path <> [].
Hypothesis Hplen : (length path <= 4095)%nat.
Hypothesis FRM0 : QCcH.frm0 fC.
Hypothesis ASP : a_sp = sp0.
Hypothesis Hfit : entry_stack_fits sp0 [a0s; path] envv.
Notation usp0 := (bv_unsigned sp0).
Notation pp := (bv_unsigned (p1 sp0 a0s path envv)).
Notation model0 := (Q1zM.model0 sp0 a0s path envv tid brk mbase fs0 stdin0).

#[using="ASP"] Lemma usp0_ceil : alloc_ceiling = usp0 - 8388608.
Proof. change (@alloc_ceiling amb_rc) with (bv_unsigned a_sp - 8388608)%Z. rewrite ASP. reflexivity. Qed.
#[using="path Hplen ASP"] Lemma usp0_above : alloc_ceiling < usp0.
Proof. rewrite usp0_ceil. lia. Qed.

Let HKA := open_err_branch_cannot_open sp0 a0s path envv tid regs0 mem0 brk mbase fs0 stdin0 Hva Hve Hvsp ME Hfit.
Let HIx : heap_iface S4L := S4_heap usp0 usp0_above.

Hypothesis TGT : target_stmt S4L HIx 0x20e60 hglob_P.

#[using="Type"] Lemma fds0_1 : fd_lookup Q1zM.fds0 (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)).
Proof. reflexivity. Qed.
#[using="Type"] Lemma fds0_2 : fd_lookup Q1zM.fds0 (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).
Proof. reflexivity. Qed.

#[using="Hva Hve Hvsp Htid ME Hbrk Hpne Hplen FRM0 ASP Hfit HKA HIx TGT"] Theorem drv_main_file : forall data,
path <> QBxa.Mq5.dot_path -> fs_lookup fs0 path = Some data ->
realizes RSEGS (mkCfg (mkst regs0 (Z_to_bv 64 0x209c0) mem0 (seg_rom RSEGS)) model0)
(t_alt2 (t_die (msg_cannot_open path) fs0) (t_opened data fs0)).
Proof.
intros data NDOT FS.
apply (open_seg sp0 a0s path envv tid regs0 mem0 brk mbase fs0 stdin0 Hva Hve Hvsp Htid ME Hpne Hplen HKA);
[| intros E; exfalso; exact (NDOT E)| intros _; exists data; exact FS].
intros _ fdata FS'.
apply (conv_open_ok sp0 a0s path envv tid regs0 mem0 brk mbase fs0 stdin0 Hva Hve Hvsp Htid ME Hbrk Hplen FRM0 ASP).
unfold Q1zM.fds1g.
apply (read_entry_ok usp0 (bv_unsigned tid) (p1 sp0 a0s path envv) path data fs0 Q1zM.fds0 fds0_2
(leaf_oom usp0 pp (bv_unsigned tid) path) (leaf_refused usp0 pp (bv_unsigned tid) path) FS).
apply (hdr_ok usp0 (bv_unsigned tid) (p1 sp0 a0s path envv) path data fs0 Q1zM.fds0 fds0_2).
- exact (trun_ok usp0 (bv_unsigned tid) (p1 sp0 a0s path envv) path data fs0 Q1zM.fds0 fds0_1 usp0_above usp0_ceil TGT (printf1_ok usp0) (printfk_ok usp0)).
- exact (hdr_leaf_ok usp0 (bv_unsigned tid) (p1 sp0 a0s path envv) path).
Qed.

#[using="Hva Hve Hvsp Htid ME Hbrk Hpne Hplen FRM0 ASP Hfit HKA"] Theorem drv_main_dir :
path = QBxa.Mq5.dot_path ->
realizes RSEGS (mkCfg (mkst regs0 (Z_to_bv 64 0x209c0) mem0 (seg_rom RSEGS)) model0)
(t_alt2 (t_die (msg_cannot_open path) fs0) (t_opened_dir path fs0)).
Proof.
intros DOT.
apply (open_seg sp0 a0s path envv tid regs0 mem0 brk mbase fs0 stdin0 Hva Hve Hvsp Htid ME Hpne Hplen HKA);
[intros N; exfalso; exact (N DOT)| | intros N; exfalso; exact (N DOT)].
intros _.
apply (conv_open_ok sp0 a0s path envv tid regs0 mem0 brk mbase fs0 stdin0 Hva Hve Hvsp Htid ME Hbrk Hplen FRM0 ASP).
unfold Q1zM.fds1g.
apply (read_entry_dir usp0 (bv_unsigned tid) (p1 sp0 a0s path envv) path fs0 Q1zM.fds0 fds0_2 DOT
(leaf_oom usp0 pp (bv_unsigned tid) path) (leaf_readerr usp0 pp (bv_unsigned tid) path)).
Qed.
End Main.

