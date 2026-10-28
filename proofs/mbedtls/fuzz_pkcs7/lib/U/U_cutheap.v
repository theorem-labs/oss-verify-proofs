(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AEvt AStep HeapIface HeapRz RegsExt Shape Cells Mem Step.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_layout U_heap.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import Amb CatExec CatSim SeqExec StoreOk StreamSim StepTac MemSplit StartupAux ArgvEnv Layout SymExec SymExec2 SymExec2Sound SymDriveX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Spec.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_exit_base U_startup_defs U_startup U_startup_facts U_main_entry U_main_open U_main_cut U_cutkit U_tailkit.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import RunConsts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.
Open Scope Z_scope.
Set Printing Width 200.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_cutheap () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.nat"; "Stdlib.ZArith.BinInt.Z.le"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.bool"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.store_ok"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "Corelib.Init.Datatypes.true"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.rdn"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.csize"; "Corelib.Init.Datatypes.Some"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cbytes"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell_wf"; "Corelib.Init.Logic.or"; "Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Heap.RunConsts.mkRC"; "RocqVerifyHarness.AgentSubmission.U.U_startup_defs.secret_w"; "RocqVerifyHarness.AgentSubmission.U.U_startup_defs.canary_w"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.u64_range"; "LinuxProcessSemantics.LinuxProcessSem.State.FdEntry"; "RocqVerifyHarness.AgentSubmission.U.U_main_cut.cut_mem"; "RocqVerifyHarness.AgentSubmission.U.U_heap.U_heap_init_hyps"; "CutHeap.cut_rc"; "RocqVerifyHarness.AgentSubmission.U.U_main_open.model1g"].


Lemma ref_wseg_48 : wseg_ok usegs (0x4b000 : word) 4096%nat = true.
Proof. vm_compute. reflexivity. Qed.
Lemma store_ok_data48 : ltac2:(CDefT.buildp (gd_tbl_P_cutheap ()) "Pm,P,(0.&40.)(1.(0.&8.))Pa,(0.&40.)Pn,$2.P,(3.+4;000.(4.&40.R2.))P,(3.(5.(4.&40.R3.)(6.R2.))+4<000.)(7.$8.(9.$:.R5.R4.R3.)$;.)")
(* [comment removed for export] *).
Proof.
  intros m a n Hlo Hhi.
  eapply (store_ok_window usegs m (0x4b000 : word) a 4096%nat n 0x4b000 0x4c000);
    [reflexivity | reflexivity | lia | exact ref_wseg_48 | exact Hlo | exact Hhi].
Qed.

(* [comment removed for export] *)
Lemma rw_cell_of_rdn : ltac2:(CDefT.buildp (gd_tbl_P_cutheap ()) "Pm,P,(0.&40.)(1.(0.&8.))Pa,$<.Pc,$=.P,(7.(1.(>.(0.&8.)))(?.$:.R3.(10.&40.R2.)(11.R1.))(12.(>.(0.&8.))(13.R1.)))P,(14.R2.)P,(15.(16.(3.+4;000.R4.)(3.(5.R4.(6.(11.R3.)))+4<000.))(16.(3.+4<000.R4.)(3.(5.R4.(6.(11.R3.)))+7>000.)))(17.$:.R6.R5.(18.$=.R4.(19.$=.)))")
(* [comment removed for export] *).
Proof.
  intros m a c RD WF Hr. split.
  - split; [cbn; split; [exact WF | exact I] |]. cbn [cells_bytes]. rewrite app_nil_r.
    apply (bytes_at_of_rdn m (cbytes c) a); rewrite ?(cbytes_length c WF); [exact RD | lia | lia].
  - cbn [cells_size Nat.add]. rewrite Nat.add_0_r. split; [lia|]. split; [lia|]. intros i Hi.
    assert (SO : store_ok usegs m (Z_to_bv 64 a) (csize c) = true).
    { destruct Hr as [Hr|Hr]; [apply store_ok_data48 | apply store_ok_data]; rewrite u_small by lia; lia. }
    pose proof (store_ok_wview usegs m (Z_to_bv 64 a) (csize c) (Z.to_nat i) SO ltac:(lia)) as W.
    unfold wa. rewrite u_small in W by lia. replace (a + Z.of_nat (Z.to_nat i)) with (a + i) in W by lia. exact W.
Qed.

Section CutHeap.
  Context {AMB : Amb}.
  Context {LM : Lim}.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable tid : word.
  Variable rd : EntryDraw.            (* [comment removed for export] *)
  Variable regs0 : bvmap 5 word.
  Variable mem0 : word -> option byte.
  Variables (brk mbase : word) (fs0 : Fs) (stdin0 : InputStream).
  Hypothesis Hva : valid_argv [a0s; path].
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 [a0s; path] envv tid rd regs0 mem0.
  Hypothesis Hbrk : valid_brk usegs brk.

  Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).

  (* [comment removed for export] *)
  Definition cut_rc : rconsts := ltac2:(CDefT.buildp (gd_tbl_P_cutheap ()) "(1:.(4.&40.(1;.Vrd,))(4.&40.(1<.Vrd,))(1=.(1;.Vrd,))(1=.(1<.Vrd,)))")
(* [comment removed for export] *).

  #[using="regs0 Hva Hve Hvsp Htid ME Hbrk SPlo SPhi"] Theorem cut_heap_init_hyps : ltac2:(CDefT.buildp (gd_tbl_P_cutheap ()) "PM,P,(0.&40.)(1.(0.&8.))Pfd3,$1>.P,(1?.Vsp0,Va0s,Vpath,Venvv,Vmem0,R2.)(20.Vsp0,$21.R3.(22.VAMB,VLM,Vsp0,Vtid,Vbrk,Vmbase,Vfs0,Vstdin0,R2.)(4.&40.Vsp0,))")
(* [comment removed for export] *).
  Proof.
    intros M fd3 CM. pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof (u64_range tid) as Htr.
    pose proof (cut_tail_mem sp0 a0s path envv tid rd regs0 mem0 Hvsp Htid ME M CM) as TM.
    destruct TM as [W RO GOT DA CO TI TR LO CA NL SI OF].
    assert (BE : forall a : Z, (0 <= a < 0x7e000)%Z -> M (Z_to_bv 64 a) = mem0 (Z_to_bv 64 a)).
    { intros a Ha. apply (cm_below _ _ _ _ _ _ CM). rewrite u_small by lia. lia. }
    assert (RD : forall (a : Z) (n : nat), (0 <= a)%Z -> (a + Z.of_nat n <= 0x7e000)%Z ->
                 rdn usegs M (Z_to_bv 64 a) n = rdn usegs mem0 (Z_to_bv 64 a) n).
    { intros a n Ha Hn. apply rdn_agree. intros j Hj. rewrite u_small by lia. apply BE. lia. }
    assert (AB : forall a : Z, bv_unsigned sp0 <= a < 2 ^ 64 -> M (Z_to_bv 64 a) = mem0 (Z_to_bv 64 a)).
    { intros a Ha. apply (cm_above _ _ _ _ _ _ CM). rewrite u_small by lia. lia. }
    assert (RDA : forall (a : Z) (n : nat), bv_unsigned sp0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
                 rdn usegs M (Z_to_bv 64 a) n = rdn usegs mem0 (Z_to_bv 64 a) n).
    { intros a n Ha Hn. apply rdn_agree. intros j Hj. rewrite u_small by lia. apply AB. lia. }
    destruct (auxvp_u sp0 a0s path envv rd Hva Hve Hvsp) as [Hau Hab].
    ddestruct (rnd_u sp0 a0s path envv rd Hva Hve Hvsp) as (Hr1 & Hr2 & Hr3 & Hr4).
    set (auxvp0 := auxvp sp0 a0s path envv) in *. set (rnd0 := rnd sp0 a0s path envv) in *.
    pose proof (u64_range auxvp0) as Hapr. pose proof (u64_range rnd0) as Hrr.
    split.
    - (* [comment removed for export] *) intros a Ha. rewrite <- (Z_to_bv_bv_unsigned a). apply (cut_clear sp0 a0s path envv tid rd regs0 mem0 Hvsp ME M CM); lia.
    - (* [comment removed for export] *) apply rw_cell_of_rdn; [exact NL | exact I | cbn; lia].
    - (* [comment removed for export] *) apply rw_cell_of_rdn; [| exact I | cbn; lia]. cbn [csize cbytes].
      rewrite RD by (cbn; lia). rewrite (main_entry_rdn_data sp0 [a0s; path] envv tid rd regs0 mem0 ME) by (rewrite stack_max_size_val, u_small by lia; cbn; lia).
      apply (D_main_pagesize sp0 [a0s; path] envv tid rd Hva).
    - (* [comment removed for export] *)
      eapply (rauxv_ok_intro sp0 cut_rc M (bv_unsigned sp0) (bv_unsigned auxvp0) (bv_unsigned rnd0)
                (bv_unsigned (nth 1 (auxv_words RPH rnd0 a_uid a_hwcap) (Z_to_bv 64 0)))
                (bv_unsigned (nth 3 (auxv_words RPH rnd0 a_uid a_hwcap) (Z_to_bv 64 0)))
                (bv_unsigned (nth 5 (auxv_words RPH rnd0 a_uid a_hwcap) (Z_to_bv 64 0)))
                (bv_unsigned a_hwcap)
                (bv_unsigned (nth 9 (auxv_words RPH rnd0 a_uid a_hwcap) (Z_to_bv 64 0)))
                (bv_unsigned a_uid) (bv_unsigned a_uid) 0); try lia.
      + rewrite RD by (cbn; lia). rewrite (main_entry_rdn_data sp0 [a0s; path] envv tid rd regs0 mem0 ME) by (rewrite stack_max_size_val, u_small by lia; cbn; lia).
        rewrite Z_to_bv_bv_unsigned. apply (D_main_auxvp sp0 a0s path envv tid rd Hvsp).
      + intros i v Hi.
        destruct (Nat.lt_ge_cases i 20) as [Hi20|Hge]; [| rewrite (proj2 (nth_error_None _ _)) in Hi by (cbn; lia); discriminate].
        rewrite RDA by lia.
        rewrite (auxv_word_at sp0 a0s path envv tid rd regs0 mem0 Hva Hve Hvsp ME i Hi20). do 2 f_equal.
        unfold auxv_words, auxv_entries. cbn [flat_map fst snd app nth] in Hi |- *.
        do 20 (destruct i as [|i]; [cbn [nth_error] in Hi; injection Hi as <-; first [rewrite Z_to_bv_bv_unsigned; reflexivity | apply bv_eq; vm_compute; reflexivity] |]).
        exfalso. clear - Hi20. lia.
      + (* [comment removed for export] *) rewrite RDA by lia. cbn [rc_secret cut_rc]. rewrite Z_to_bv_bv_unsigned.
        exact (main_entry_secret sp0 a0s path envv tid rd regs0 mem0 Hva Hve Hvsp ME).
      + rewrite (U_alloc_ceiling_eq sp0 Hvsp). lia.
      + pose proof (u64_range (nth 1 (auxv_words RPH rnd0 a_uid a_hwcap) (Z_to_bv 64 0))). lia.
      + pose proof (u64_range (nth 3 (auxv_words RPH rnd0 a_uid a_hwcap) (Z_to_bv 64 0))). lia.
      + pose proof (u64_range (nth 5 (auxv_words RPH rnd0 a_uid a_hwcap) (Z_to_bv 64 0))). lia.
      + pose proof (u64_range a_hwcap). lia.
      + pose proof (u64_range (nth 9 (auxv_words RPH rnd0 a_uid a_hwcap) (Z_to_bv 64 0))). lia.
      + pose proof (u64_range a_uid). lia.
      + pose proof (u64_range a_uid). lia.
    - (* [comment removed for export] *) apply rw_cell_of_rdn; [exact GOT | exact I | cbn; lia].
    - (* [comment removed for export] *)
      apply rw_cell_of_rdn; [| exact I | cbn; lia]. cbn [csize rc_canary cut_rc]. rewrite Z_to_bv_bv_unsigned.
      rewrite RD by (cbn; lia). rewrite (main_entry_guard sp0 [a0s; path] envv tid rd Hlo regs0 mem0 ME). rewrite <- canary_store. reflexivity.
    - (* [comment removed for export] *)
      exists (Z_to_bv 64 0). apply rw_cell_of_rdn; [| exact I | cbn; lia]. cbn [csize cbytes].
      rewrite RD by (cbn; lia). rewrite (mem0_img_rdn sp0 a0s path envv tid rd regs0 mem0 Hvsp ME) by (vm_compute; reflexivity).
      vm_compute. reflexivity.
    - exact (cut_mem_inv sp0 a0s path envv tid rd regs0 mem0 Hvsp ME M CM).
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - exact Hbrk.
    - (* [comment removed for export] *) reflexivity.
    - exact Hvsp.
  Qed.
End CutHeap.
