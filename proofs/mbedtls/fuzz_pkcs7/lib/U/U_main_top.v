(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AEvt AStep HeapIface HeapRz RegsExt Shape.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_layout U_heap.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import RunConsts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Cells Step.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import Amb.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Spec TopContract SInv.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Frame.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_startup U_main_entry U_main_open U_main_skel U_main_cut U_main_file U_main_body U_cutheap.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
#[local] Existing Instance PropExec.fx0.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_main_top () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HST"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "RocqVerifyHarness.AgentSubmission.U.U_layout.U_layout"; "RocqVerifyHarness.AgentSubmission.U.U_heap.U_HI"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HEAP"; "Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"].


(* [comment removed for export] *)
Definition heap_at_cut {LM : Lim} (DRV : nat -> hst -> Model -> Prop) (NS : hst -> Prop) : Prop :=
  forall (AMB : Amb) (sp0 : word) (a0s path : list byte) (envv : list (list byte)) (tid : word) (rd : EntryDraw)
         (regs0 : bvmap 5 word) (mem0 : word -> option byte) (brk mbase : word) (fs0 : Fs) (stdin0 : InputStream)
         (M : word -> option byte) (fd3 : FdEntry),
    valid_argv [a0s; path] -> valid_envp envv -> valid_sp sp0 -> (0 < bv_unsigned tid < 2 ^ 22)%Z ->
    main_entry sp0 [a0s; path] envv tid rd regs0 mem0 -> valid_brk Ubsan.M.loaded_segments brk ->
    cut_mem sp0 a0s path envv mem0 M ->
    exists h, HEAP usegs (U_layout sp0) (U_HI sp0) h [] M (model1g sp0 tid brk mbase fs0 stdin0 fd3)
              /\ heap_top usegs (U_layout sp0) (U_HI sp0) h = bv_unsigned sp0
              /\ DRV 14%nat h (model1g sp0 tid brk mbase fs0 stdin0 fd3) /\ NS h.

(* [comment removed for export] *)
Definition heap_init_full {LM : Lim} (DRV : nat -> hst -> Model -> Prop) (NS : hst -> Prop) : Prop :=
  forall (AMB : Amb) (sp0 : word) (rc : rconsts) (m : mem) (tid brk mbase : word) (fs0 : Fs) (stdin0 : InputStream) (fd3 : FdEntry) (top : Z),
    U_heap_init_hyps sp0 rc m (model1g sp0 tid brk mbase fs0 stdin0 fd3) top ->
    exists h, HEAP usegs (U_layout sp0) (U_HI sp0) h [] m (model1g sp0 tid brk mbase fs0 stdin0 fd3)
              /\ heap_top usegs (U_layout sp0) (U_HI sp0) h = top
              /\ DRV 14%nat h (model1g sp0 tid brk mbase fs0 stdin0 fd3) /\ NS h.

(* [comment removed for export] *)
Lemma heap_at_cut_of_init {LM : Lim} : forall DRV NS, heap_init_full DRV NS -> heap_at_cut DRV NS.
Proof.
  intros DRV NS HI AMB sp0 a0s path envv tid rd regs0 mem0 brk mbase fs0 stdin0 M fd3 Hva Hve Hvsp Htid ME Hbrk CM.
  eapply HI. eapply cut_heap_init_hyps; eauto.
Qed.

(* [comment removed for export] *)
Lemma HEAP_P_HI : forall sp0 h LB m mo, HEAP usegs (U_layout sp0) (U_HI sp0) h LB m mo = PHEAP sp0 h LB m mo.
Proof. reflexivity. Qed.
Lemma heap_top_P_HI : forall sp0 h, heap_top usegs (U_layout sp0) (U_HI sp0) h = h_top h.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma U_HSTAT : ltac2:(CDefT.buildp (gd_tbl_P_main_top ()) "Psp0,(0.&40.)Ph,(1.$2.(3.R1.)(4.R1.))PLB,(5.$6.)Pm,P,(0.&40.)(7.(0.&8.))Pmo,$8.P,(9.$2.(3.R5.)(4.R5.)R4.R3.R2.R1.)(:.(;.$2.R3.+7=353.(<.$=.(>.(?.&8.=))(10.$=.)))(:.(11.(0.&40.)Lg,(0.&40.)(;.$2.R4.+7=330.(<.$=.(12.R1.)(10.$=.))))(;.$2.R3.+4;<=8.(<.$=.(12.(?.&40.+7=330.))(10.$=.)))))")
(* [comment removed for export] *).
Proof.
  intros sp0 h LB m mo HH. ddestruct (U_heap_statics sp0 h LB m mo HH) as (A & B & C & _).
  split; [exact A|]. split; [eexists; exact B| exact C].
Qed.

Section Top.
  Context {LM : Lim}.   (* [comment removed for export] *)
  Variable DRV : nat -> hst -> Model -> Prop.
  Variable NS : hst -> Prop.
  Hypothesis MRZ : forall sp0, malloc_rz_stmt usegs (U_layout sp0) (U_HI sp0) DRV NS.
  Hypothesis FREEC : forall sp0, free_c_stmt usegs (U_layout sp0) (U_HI sp0) DRV.
  Hypothesis DRVMO : forall sp0, drv_mo_stmt usegs (U_layout sp0) (U_HI sp0) DRV.
  Variable SI : forall sp0 : word, sinv (U_layout sp0).
  Hypothesis SIFP : forall (sp0 : word) (a : Z), ~ outside (si_fp (SI sp0)) a -> 0x5cf90 <= a < 0x5cff8.
  Hypothesis FUZZ : forall sp0 : word, fuzz_entry_stmt usegs (U_layout sp0) (U_HI sp0) (SI sp0) 0x1d6ec.
  Hypothesis HINIT : heap_at_cut DRV NS.

  #[using="DRV NS MRZ FREEC DRVMO SI SIFP FUZZ HINIT"] Theorem U_file_kont : file_kont_stmt_c.
  Proof.
    intros AMB sp0 a0s path envv tid rd regs0 mem0 brk mbase fs0 stdin0 fdata Hva Hve Hvsp Htid ME Hbrk Hf Hne Hnd Hlen.
    eapply (file_kont_core sp0 a0s path envv tid rd regs0 mem0 brk mbase fs0 stdin0 Hvsp Htid ME (U_HI sp0) (U_HSTAT sp0) DRV NS (MRZ sp0) (FREEC sp0) (DRVMO sp0));
      [ | exact Hf |].
    - intros M fd3 CM. eapply HINIT; eauto.
    - eapply after_loop; eauto. apply U_HSTAT.
  Qed.

  #[using="DRV NS MRZ HINIT"] Theorem U_dir_kont : dir_kont_stmt_c.
  Proof.
    intros AMB sp0 a0s envv tid rd regs0 mem0 brk mbase fs0 stdin0 Hva Hve Hvsp Htid ME Hbrk.
    eapply (dir_kont sp0 a0s dot_path envv tid rd regs0 mem0 brk mbase fs0 stdin0 Hva Hve Hvsp Htid ME (U_HI sp0) (U_HSTAT sp0) DRV NS (MRZ sp0)); [| reflexivity].
    intros M fd3 CM. eapply HINIT; eauto.
  Qed.

  (* [comment removed for export] *)
  #[using="DRV NS MRZ FREEC DRVMO SI SIFP FUZZ HINIT"] Theorem U_realizes_spec_drv {AMB : Amb} : forall sp brk mbase (rd : EntryDraw) (inp : ProcInput),
    valid_sp sp -> valid_brk usegs' brk ->
    valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) ->
    entry_stack_fits sp (in_argv inp) (in_envp inp) ->       (* [comment removed for export] *)
    realizes usegs' (init_config usegs' upc uph sp brk mbase rd LIM inp) (spec (in_argv inp) (in_fs inp)).
  Proof. apply U_realizes_spec_c; [apply U_file_kont | apply U_dir_kont]. Qed.
End Top.
