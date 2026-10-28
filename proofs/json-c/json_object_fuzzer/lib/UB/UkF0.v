(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.json_c.json_object_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJyS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJyS. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QsRG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsRG.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qnhz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qnhz.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q9ox.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9ox.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QBxa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBxa.Mq5. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qn1e.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qn1e. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QSpR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSpR.Mq1.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Udbv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Udbv. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UWQV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UWQV.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U1oC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U1oC.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U1zM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U1zM. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UmsF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UmsF.Mq1.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UKNz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UKNz.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UC8c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UC8c.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UPZI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UPZI.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Ujk3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ujk3.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UmAj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UmAj. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Udkw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Udkw.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UYot.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UYot. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q3dw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q3dw.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uqqm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uqqm. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UDH9.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UDH9. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U5Hp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U5Hp.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U7J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U7J3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UDH9.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UDH9.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UtkK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UtkK. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UBap.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UBap. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UtkK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UtkK.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UBap.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UBap.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UTWd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UTWd.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UTWd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UTWd. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UWOb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UWOb. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UBRj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UBRj.
Import ListNotations. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
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
Notation model0 := (U1zM.model0 sp0 a0s path envv tid brk mbase fs0 stdin0).

#[using="ASP"] Lemma usp0_ceil : alloc_ceiling = usp0 - 8388608.
Proof. change (@alloc_ceiling amb_rc) with (bv_unsigned a_sp - 8388608)%Z. rewrite ASP. reflexivity. Qed.
#[using="path Hplen ASP"] Lemma usp0_above : alloc_ceiling < usp0.
Proof. rewrite usp0_ceil. lia. Qed.

Let HKA := open_err_branch_cannot_open sp0 a0s path envv tid regs0 mem0 brk mbase fs0 stdin0 Hva Hve Hvsp ME Hfit.
Let HIx : heap_iface S4L := S4_heap usp0 usp0_above.

Hypothesis TGT : target_stmt S4L HIx 0x21024 hglob_P.

#[using="Type"] Lemma fds0_1 : fd_lookup U1zM.fds0 (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)).
Proof. reflexivity. Qed.
#[using="Type"] Lemma fds0_2 : fd_lookup U1zM.fds0 (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).
Proof. reflexivity. Qed.

#[using="Hva Hve Hvsp Htid ME Hbrk Hpne Hplen FRM0 ASP Hfit HKA HIx TGT"] Theorem drv_main_file : forall data,
path <> QBxa.Mq5.dot_path -> fs_lookup fs0 path = Some data ->
realizes RSEGS (mkCfg (mkst regs0 (Z_to_bv 64 0x20b84) mem0 (seg_rom RSEGS)) model0)
(t_alt2 (t_die (msg_cannot_open path) fs0) (t_opened data fs0)).
Proof.
intros data NDOT FS.
apply (open_seg sp0 a0s path envv tid regs0 mem0 brk mbase fs0 stdin0 Hva Hve Hvsp Htid ME Hpne Hplen HKA);
[| intros E; exfalso; exact (NDOT E)| intros _; exists data; exact FS].
intros _ fdata FS'.
apply (conv_open_ok sp0 a0s path envv tid regs0 mem0 brk mbase fs0 stdin0 Hva Hve Hvsp Htid ME Hbrk Hplen FRM0 ASP).
unfold U1zM.fds1g.
apply (read_entry_ok usp0 (bv_unsigned tid) (p1 sp0 a0s path envv) path data fs0 U1zM.fds0 fds0_2
(leaf_oom usp0 pp (bv_unsigned tid) path) (leaf_refused usp0 pp (bv_unsigned tid) path) FS).
apply (hdr_ok usp0 (bv_unsigned tid) (p1 sp0 a0s path envv) path data fs0 U1zM.fds0 fds0_2).
- exact (trun_ok usp0 (bv_unsigned tid) (p1 sp0 a0s path envv) path data fs0 U1zM.fds0 fds0_1 usp0_above usp0_ceil TGT (printf1_ok usp0) (printfk_ok usp0)).
- exact (hdr_leaf_ok usp0 (bv_unsigned tid) (p1 sp0 a0s path envv) path).
Qed.

#[using="Hva Hve Hvsp Htid ME Hbrk Hpne Hplen FRM0 ASP Hfit HKA"] Theorem drv_main_dir :
path = QBxa.Mq5.dot_path ->
realizes RSEGS (mkCfg (mkst regs0 (Z_to_bv 64 0x20b84) mem0 (seg_rom RSEGS)) model0)
(t_alt2 (t_die (msg_cannot_open path) fs0) (t_opened_dir path fs0)).
Proof.
intros DOT.
apply (open_seg sp0 a0s path envv tid regs0 mem0 brk mbase fs0 stdin0 Hva Hve Hvsp Htid ME Hpne Hplen HKA);
[intros N; exfalso; exact (N DOT)| | intros N; exfalso; exact (N DOT)].
intros _.
apply (conv_open_ok sp0 a0s path envv tid regs0 mem0 brk mbase fs0 stdin0 Hva Hve Hvsp Htid ME Hbrk Hplen FRM0 ASP).
unfold U1zM.fds1g.
apply (read_entry_dir usp0 (bv_unsigned tid) (p1 sp0 a0s path envv) path fs0 U1zM.fds0 fds0_2 DOT
(leaf_oom usp0 pp (bv_unsigned tid) path) (leaf_readerr usp0 pp (bv_unsigned tid) path)).
Qed.
End Main.

