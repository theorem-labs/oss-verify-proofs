(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import
  PropExec ShapeAlg SpinAlg AgentLib AxSymExec3 AxSymExec3Sound AxSymRun3
  AsanPlanCore AsanPlan AsanPlanSound. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BBoot Require Import AsanCertDefs AsanPlanImages. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import AsanInit. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BBoot Require Import AsanStartup AsanMainEntry. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import PlanCut.
  From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BBoot Require Import StartupPlanAsan StartupHSAsan StartupHScutAsan StartupPiecesAsan MainEntryPlanAsan MainEntryHSAsan MainEntryHScutAsan MainEntryPiecesAsan
  AsanStartupCertP1 AsanStartupCertP2 AsanStartupCertP3A AsanStartupCertP3B AsanStartupCertP3C MainEntryCertAsanR0 MainEntryCertAsanA1 MainEntryCertAsanA2 MainEntryCertAsanA3 MainEntryCertAsanA4 MainEntryCertAsanA5 MainEntryCertAsanB1 MainEntryCertAsanB2 MainEntryCertAsanB3 MainEntryCertAsanB4 MainEntryCertAsanB5.
  From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import AsanMainEntryKit. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BBoot Require Import AsanMainEntryFacts.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import AP. Import APS.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_AsanBoot () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.ABoot.SpinAlg.srealizes"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanCertDefs.ASEGS"; "LinuxProcessSemantics.LinuxProcessSem.Run.init_config"; "RocqVerifyHarness.ProcessOversight.Tgt_fuzz_pkcs7_both.M.init_pc"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanPlanImages.APH"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanInit.LIMIT"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanInit.inp"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanInit.E0"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanPlanSound.APS.holes_stmt"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanPlan.AP.BOTH"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanCertDefs.ALIMIT"; "RocqVerifyHarness.AgentSubmission.BBoot.MainEntryHSAsan.HS_main"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanInit.SINV0"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanInit.argH0"; "Corelib.Init.Datatypes.nat"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.ABoot.AxSymExec3.AX2.env"; "Corelib.Init.Peano.lt"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanPlan.AP.NX0"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.ABoot.AxSymExec3.AX2.ev"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.main_entry_A"; "LinuxProcessSemantics.LinuxProcessSem.Fs.Fs"; "LinuxProcessSemantics.LinuxProcessSem.State.m_fs"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanPlanSound.APS.cfg_of"; "LinuxProcessSemantics.LinuxProcessSem.StackLayout.EntryDraw"; "LinuxProcessSemantics.LinuxProcessSem.State.ProcInput"; "LinuxProcessSemantics.LinuxProcessSem.Run.valid_sp"; "LinuxProcessSemantics.LinuxProcessSem.Run.valid_brk"; "LinuxProcessSemantics.LinuxProcessSem.Run.valid_argv"; "LinuxProcessSemantics.LinuxProcessSem.State.in_argv"; "LinuxProcessSemantics.LinuxProcessSem.Run.valid_envp"; "LinuxProcessSemantics.LinuxProcessSem.State.in_envp"; "LinuxProcessSemantics.LinuxProcessSem.Run.entry_stack_fits"; "LinuxProcessSemantics.LinuxProcessSem.Run.valid_id"; "LinuxProcessSemantics.LinuxProcessSem.State.in_uid"; "Corelib.Init.Datatypes.bool"; "LinuxProcessSemantics.LinuxProcessSem.State.in_abort_terminal"; "Corelib.Init.Datatypes.false"; "LinuxProcessSemantics.LinuxProcessSem.State.VaSize"; "LinuxProcessSemantics.LinuxProcessSem.State.in_va_size"; "LinuxProcessSemantics.LinuxProcessSem.State.Sv48"; "RocqVerifyHarness.AgentSubmission.ABoot.ShapeAlg.TSet"; "RocqVerifyHarness.AgentSubmission.ABoot.AxSymRun3.env_agree"; "Corelib.Init.Datatypes.nil"; "LinuxProcessSemantics.LinuxProcessSem.State.event"; "LinuxProcessSemantics.LinuxProcessSem.State.in_hwcap"; "LinuxProcessSemantics.LinuxProcessSem.State.in_fs"].


(* [comment removed for export] *)
Lemma IT0_ok : itab_sound ASEGS IT0.
Proof. unfold IT0. apply APS.mk_itab_ranges_sound. Qed.
Lemma IT1_ok : itab_sound ASEGS IT1.
Proof. unfold IT1. apply APS.mk_itab_ranges_sound. Qed.

Lemma HS_asan_only0 : forall h ch, HS_asan h = Some ch -> ch = HS_asan_0.
Proof. intros [|h] ch H; cbn [HS_asan] in H; [injection H as <-; reflexivity | discriminate H]. Qed.
Lemma HNX1 : (NX0 <= NX1)%nat.
Proof. unfold NX0, NX1. lia. Qed.
Lemma HS_main_pc : forall h ch, HS_main h = Some ch -> pc ch = 0x970e0.
Proof.
  intros h ch Hh. destruct h as [|[|[|h]]]; cbn [HS_main] in Hh; try discriminate Hh; injection Hh as <-; reflexivity.
Qed.

Section Boot.
  Variable sp brk0 mbase : word.
  Variable rdraw : EntryDraw.
  Variable argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variable stdin : InputStream.
  Variables uid gid hw : word.
  Variable groups : list word.
  Variable net : NetQueue.
  Variables nofile sigmask : word.   (* [comment removed for export] *)
  Variable urandom : InputStream.   (* [comment removed for export] *)
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk ASEGS brk0.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Hypothesis Huid : valid_id uid.
  #[local] Notation SINV := (SINV0 APH sp rdraw brk0 argv envp uid hw).
  #[local] Notation argH := (argH0 APH sp rdraw argv envp uid hw).
  #[local] Notation E0a := (E0 APH sp rdraw brk0 argv envp uid hw).
  #[local] Notation SP0 := (bv_unsigned sp).

  Variable MAIN : env -> Fs.Fs -> TSet.
  Hypothesis MAIN_agree : forall E E' fs', env_agree NX0 E E' -> MAIN E fs' = MAIN E' fs'.
  Hypothesis MAIN_nil : forall E fs', MAIN E fs' [].

  (* [comment removed for export] *)
  Lemma su_P1_holes : only_holes su_P1_shape = true.  Proof. vm_compute. reflexivity. Qed.
  Lemma su_P1_hole : has_hole_all su_P1_shape = true.  Proof. vm_compute. reflexivity. Qed.
  Lemma su_P2_holes : only_holes su_P2_shape = true.  Proof. vm_compute. reflexivity. Qed.
  Lemma su_P2_hole : has_hole_all su_P2_shape = true.  Proof. vm_compute. reflexivity. Qed.
  Lemma su_P3A_holes : only_holes su_P3A_shape = true.  Proof. vm_compute. reflexivity. Qed.
  Lemma su_P3A_hole : has_hole_all su_P3A_shape = true.  Proof. vm_compute. reflexivity. Qed.
  Lemma su_P3B_holes : only_holes su_P3B_shape = true.  Proof. vm_compute. reflexivity. Qed.
  Lemma su_P3B_hole : has_hole_all su_P3B_shape = true.  Proof. vm_compute. reflexivity. Qed.
  Lemma su_P3C_holes : only_holes su_P3C_shape = true.  Proof. vm_compute. reflexivity. Qed.
  Lemma su_P3C_hole : has_hole_all su_P3C_shape = true.  Proof. vm_compute. reflexivity. Qed.
  Lemma me_R0_holes : only_holes me_R0_shape = true.  Proof. vm_compute. reflexivity. Qed.
  Lemma me_R0_hole : has_hole_all me_R0_shape = true.  Proof. vm_compute. reflexivity. Qed.
  Lemma me_A1_holes : only_holes me_A1_shape = true.  Proof. vm_compute. reflexivity. Qed.
  Lemma me_A1_hole : has_hole_all me_A1_shape = true.  Proof. vm_compute. reflexivity. Qed.
  Lemma me_A2_holes : only_holes me_A2_shape = true.  Proof. vm_compute. reflexivity. Qed.
  Lemma me_A2_hole : has_hole_all me_A2_shape = true.  Proof. vm_compute. reflexivity. Qed.
  Lemma me_A3_holes : only_holes me_A3_shape = true.  Proof. vm_compute. reflexivity. Qed.
  Lemma me_A3_hole : has_hole_all me_A3_shape = true.  Proof. vm_compute. reflexivity. Qed.
  Lemma me_A4_holes : only_holes me_A4_shape = true.  Proof. vm_compute. reflexivity. Qed.
  Lemma me_A4_hole : has_hole_all me_A4_shape = true.  Proof. vm_compute. reflexivity. Qed.
  Lemma me_A5_holes : only_holes me_A5_shape = true.  Proof. vm_compute. reflexivity. Qed.
  Lemma me_A5_hole : has_hole_all me_A5_shape = true.  Proof. vm_compute. reflexivity. Qed.
  Lemma me_B1_holes : only_holes me_B1_shape = true.  Proof. vm_compute. reflexivity. Qed.
  Lemma me_B1_hole : has_hole_all me_B1_shape = true.  Proof. vm_compute. reflexivity. Qed.
  Lemma me_B2_holes : only_holes me_B2_shape = true.  Proof. vm_compute. reflexivity. Qed.
  Lemma me_B2_hole : has_hole_all me_B2_shape = true.  Proof. vm_compute. reflexivity. Qed.
  Lemma me_B3_holes : only_holes me_B3_shape = true.  Proof. vm_compute. reflexivity. Qed.
  Lemma me_B3_hole : has_hole_all me_B3_shape = true.  Proof. vm_compute. reflexivity. Qed.
  Lemma me_B4_holes : only_holes me_B4_shape = true.  Proof. vm_compute. reflexivity. Qed.
  Lemma me_B4_hole : has_hole_all me_B4_shape = true.  Proof. vm_compute. reflexivity. Qed.
  Lemma me_B5_holes : only_holes me_B5_shape = true.  Proof. vm_compute. reflexivity. Qed.
  Lemma me_B5_hole : has_hole_all me_B5_shape = true.  Proof. vm_compute. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma su_P1_guard : spin_guarded su_P1_plan = true.  Proof. vm_compute. reflexivity. Qed.
  Lemma su_P2_guard : spin_guarded su_P2_plan = true.  Proof. vm_compute. reflexivity. Qed.
  Lemma su_P3A_guard : spin_guarded su_P3A_plan = true.  Proof. vm_compute. reflexivity. Qed.
  Lemma su_P3B_guard : spin_guarded su_P3B_plan = true.  Proof. vm_compute. reflexivity. Qed.
  Lemma su_P3C_guard : spin_guarded su_P3C_plan = true.  Proof. vm_compute. reflexivity. Qed.
  Lemma me_R0_guard : spin_guarded me_R0_plan = true.  Proof. vm_compute. reflexivity. Qed.
  Lemma me_A1_guard : spin_guarded me_A1_plan = true.  Proof. vm_compute. reflexivity. Qed.
  Lemma me_A2_guard : spin_guarded me_A2_plan = true.  Proof. vm_compute. reflexivity. Qed.
  Lemma me_A3_guard : spin_guarded me_A3_plan = true.  Proof. vm_compute. reflexivity. Qed.
  Lemma me_A4_guard : spin_guarded me_A4_plan = true.  Proof. vm_compute. reflexivity. Qed.
  Lemma me_A5_guard : spin_guarded me_A5_plan = true.  Proof. vm_compute. reflexivity. Qed.
  Lemma me_B1_guard : spin_guarded me_B1_plan = true.  Proof. vm_compute. reflexivity. Qed.
  Lemma me_B2_guard : spin_guarded me_B2_plan = true.  Proof. vm_compute. reflexivity. Qed.
  Lemma me_B3_guard : spin_guarded me_B3_plan = true.  Proof. vm_compute. reflexivity. Qed.
  Lemma me_B4_guard : spin_guarded me_B4_plan = true.  Proof. vm_compute. reflexivity. Qed.
  Lemma me_B5_guard : spin_guarded me_B5_plan = true.  Proof. vm_compute. reflexivity. Qed.

  Section Chain.
    (* [comment removed for export] *)
    Hypothesis MS : holes_stmt ASEGS BOTH ALIMIT HS_main SP0 SINV argH (fun _ => MAIN) fs.
    #[local] Notation FROM := (from_state sp brk0 rdraw argv envp fs uid hw MAIN).
    Let PS := piece_sound sp brk0 rdraw argv envp fs uid hw Hsp Hva Hve Hfit MAIN MAIN_agree MAIN_nil.
    Let TH := hs_tab_holes sp brk0 rdraw argv envp fs uid hw MAIN.
    Lemma F_HS_s2c_1013 : FROM HS_s2c_1013.
    Proof. exact (PS NX1 HNX1 IT1 IT1_ok HS_main HS_s2c_1013 me_A5_plan me_A5_shape me_A5_cert me_A5_guard me_A5_holes me_A5_hole MS). Qed.
    Lemma T_me_A4 : holes_stmt ASEGS BOTH ALIMIT me_A4_tab SP0 SINV argH (fun _ => MAIN) fs.
    Proof. unfold me_A4_tab. apply TH. intros h cs Hin. cbn [In] in Hin. destruct Hin as [H|[]]; injection H as <- <-; [exact F_HS_s2c_1013]. Qed.
    Lemma F_HS_s2c_1012 : FROM HS_s2c_1012.
    Proof. exact (PS NX1 HNX1 IT1 IT1_ok me_A4_tab HS_s2c_1012 me_A4_plan me_A4_shape me_A4_cert me_A4_guard me_A4_holes me_A4_hole T_me_A4). Qed.
    Lemma T_me_A3 : holes_stmt ASEGS BOTH ALIMIT me_A3_tab SP0 SINV argH (fun _ => MAIN) fs.
    Proof. unfold me_A3_tab. apply TH. intros h cs Hin. cbn [In] in Hin. destruct Hin as [H|[]]; injection H as <- <-; [exact F_HS_s2c_1012]. Qed.
    Lemma F_HS_s2c_1011 : FROM HS_s2c_1011.
    Proof. exact (PS NX1 HNX1 IT1 IT1_ok me_A3_tab HS_s2c_1011 me_A3_plan me_A3_shape me_A3_cert me_A3_guard me_A3_holes me_A3_hole T_me_A3). Qed.
    Lemma T_me_A2 : holes_stmt ASEGS BOTH ALIMIT me_A2_tab SP0 SINV argH (fun _ => MAIN) fs.
    Proof. unfold me_A2_tab. apply TH. intros h cs Hin. cbn [In] in Hin. destruct Hin as [H|[]]; injection H as <- <-; [exact F_HS_s2c_1011]. Qed.
    Lemma F_HS_s2c_1010 : FROM HS_s2c_1010.
    Proof. exact (PS NX1 HNX1 IT1 IT1_ok me_A2_tab HS_s2c_1010 me_A2_plan me_A2_shape me_A2_cert me_A2_guard me_A2_holes me_A2_hole T_me_A2). Qed.
    Lemma T_me_A1 : holes_stmt ASEGS BOTH ALIMIT me_A1_tab SP0 SINV argH (fun _ => MAIN) fs.
    Proof. unfold me_A1_tab. apply TH. intros h cs Hin. cbn [In] in Hin. destruct Hin as [H|[]]; injection H as <- <-; [exact F_HS_s2c_1010]. Qed.
    Lemma F_HS_s2c_1000 : FROM HS_s2c_1000.
    Proof. exact (PS NX1 HNX1 IT1 IT1_ok me_A1_tab HS_s2c_1000 me_A1_plan me_A1_shape me_A1_cert me_A1_guard me_A1_holes me_A1_hole T_me_A1). Qed.
    Lemma F_HS_s2c_1023 : FROM HS_s2c_1023.
    Proof. exact (PS NX1 HNX1 IT1 IT1_ok HS_main HS_s2c_1023 me_B5_plan me_B5_shape me_B5_cert me_B5_guard me_B5_holes me_B5_hole MS). Qed.
    Lemma T_me_B4 : holes_stmt ASEGS BOTH ALIMIT me_B4_tab SP0 SINV argH (fun _ => MAIN) fs.
    Proof. unfold me_B4_tab. apply TH. intros h cs Hin. cbn [In] in Hin. destruct Hin as [H|[]]; injection H as <- <-; [exact F_HS_s2c_1023]. Qed.
    Lemma F_HS_s2c_1022 : FROM HS_s2c_1022.
    Proof. exact (PS NX1 HNX1 IT1 IT1_ok me_B4_tab HS_s2c_1022 me_B4_plan me_B4_shape me_B4_cert me_B4_guard me_B4_holes me_B4_hole T_me_B4). Qed.
    Lemma T_me_B3 : holes_stmt ASEGS BOTH ALIMIT me_B3_tab SP0 SINV argH (fun _ => MAIN) fs.
    Proof. unfold me_B3_tab. apply TH. intros h cs Hin. cbn [In] in Hin. destruct Hin as [H|[]]; injection H as <- <-; [exact F_HS_s2c_1022]. Qed.
    Lemma F_HS_s2c_1021 : FROM HS_s2c_1021.
    Proof. exact (PS NX1 HNX1 IT1 IT1_ok me_B3_tab HS_s2c_1021 me_B3_plan me_B3_shape me_B3_cert me_B3_guard me_B3_holes me_B3_hole T_me_B3). Qed.
    Lemma T_me_B2 : holes_stmt ASEGS BOTH ALIMIT me_B2_tab SP0 SINV argH (fun _ => MAIN) fs.
    Proof. unfold me_B2_tab. apply TH. intros h cs Hin. cbn [In] in Hin. destruct Hin as [H|[]]; injection H as <- <-; [exact F_HS_s2c_1021]. Qed.
    Lemma F_HS_s2c_1020 : FROM HS_s2c_1020.
    Proof. exact (PS NX1 HNX1 IT1 IT1_ok me_B2_tab HS_s2c_1020 me_B2_plan me_B2_shape me_B2_cert me_B2_guard me_B2_holes me_B2_hole T_me_B2). Qed.
    Lemma T_me_B1 : holes_stmt ASEGS BOTH ALIMIT me_B1_tab SP0 SINV argH (fun _ => MAIN) fs.
    Proof. unfold me_B1_tab. apply TH. intros h cs Hin. cbn [In] in Hin. destruct Hin as [H|[]]; injection H as <- <-; [exact F_HS_s2c_1020]. Qed.
    Lemma F_HS_s2c_1001 : FROM HS_s2c_1001.
    Proof. exact (PS NX1 HNX1 IT1 IT1_ok me_B1_tab HS_s2c_1001 me_B1_plan me_B1_shape me_B1_cert me_B1_guard me_B1_holes me_B1_hole T_me_B1). Qed.
    Lemma T_me_R0 : holes_stmt ASEGS BOTH ALIMIT me_R0_tab SP0 SINV argH (fun _ => MAIN) fs.
    Proof. unfold me_R0_tab. apply TH. intros h cs Hin. cbn [In] in Hin. destruct Hin as [H|[H|[]]]; injection H as <- <-; [exact F_HS_s2c_1000 | exact F_HS_s2c_1001]. Qed.
    Lemma F_HS_asan_0 : FROM HS_asan_0.
    Proof. exact (PS NX1 HNX1 IT1 IT1_ok me_R0_tab HS_asan_0 me_R0_plan me_R0_shape me_R0_cert me_R0_guard me_R0_holes me_R0_hole T_me_R0). Qed.
    (* [comment removed for export] *)
    Lemma T_HS_asan : holes_stmt ASEGS BOTH ALIMIT HS_asan SP0 SINV argH (fun _ => MAIN) fs.
    Proof. exact (hs_const_holes sp brk0 rdraw argv envp fs uid hw MAIN HS_asan HS_asan_0 HS_asan_only0 F_HS_asan_0). Qed.
    Lemma F_HS_s1c_1001 : FROM HS_s1c_1001.
    Proof. exact (PS NX0 (le_n NX0) IT0 IT0_ok HS_asan HS_s1c_1001 su_P3A_plan su_P3A_shape su_P3A_cert su_P3A_guard su_P3A_holes su_P3A_hole T_HS_asan). Qed.
    Lemma F_HS_s1c_1002 : FROM HS_s1c_1002.
    Proof. exact (PS NX0 (le_n NX0) IT0 IT0_ok HS_asan HS_s1c_1002 su_P3B_plan su_P3B_shape su_P3B_cert su_P3B_guard su_P3B_holes su_P3B_hole T_HS_asan). Qed.
    Lemma F_HS_s1c_1003 : FROM HS_s1c_1003.
    Proof. exact (PS NX0 (le_n NX0) IT0 IT0_ok HS_asan HS_s1c_1003 su_P3C_plan su_P3C_shape su_P3C_cert su_P3C_guard su_P3C_holes su_P3C_hole T_HS_asan). Qed.
    Lemma T_su_P2 : holes_stmt ASEGS BOTH ALIMIT su_P2_tab SP0 SINV argH (fun _ => MAIN) fs.
    Proof. unfold su_P2_tab. apply TH. intros h cs Hin. cbn [In] in Hin. destruct Hin as [H|[H|[H|[]]]]; injection H as <- <-; [exact F_HS_s1c_1001 | exact F_HS_s1c_1002 | exact F_HS_s1c_1003]. Qed.
    Lemma F_HS_s1c_1000 : FROM HS_s1c_1000.
    Proof. exact (PS NX0 (le_n NX0) IT0 IT0_ok su_P2_tab HS_s1c_1000 su_P2_plan su_P2_shape su_P2_cert su_P2_guard su_P2_holes su_P2_hole T_su_P2). Qed.
    Lemma T_su_P1 : holes_stmt ASEGS BOTH ALIMIT su_P1_tab SP0 SINV argH (fun _ => MAIN) fs.
    Proof. unfold su_P1_tab. apply TH. intros h cs Hin. cbn [In] in Hin. destruct Hin as [H|[]]; injection H as <- <-; [exact F_HS_s1c_1000]. Qed.
    (* [comment removed for export] *)
    Theorem boot_chain : ltac2:(CDefT.buildp (gd_tbl_AsanBoot ()) "(0.$1.(2.$1.$3.$4.Vsp,Vbrk0,Vmbase,Vrdraw,$5.(6.Vargv,Venvp,Vfs,Vstdin,Vuid,Vgid,Vhw,Vgroups,Vnet,Vnofile,Vsigmask,Vurandom,))A2.VMAIN,(7.$4.Vsp,Vrdraw,Vbrk0,Vargv,Venvp,Vuid,Vhw,)Vfs,)")
(* [comment removed for export] *).
    Proof.
      exact (asan_boot1 sp brk0 mbase rdraw argv envp fs stdin uid gid hw groups net nofile sigmask urandom Hsp Hbrk Hva Hve Hfit Huid
               IT0 IT0_ok su_P1_tab su_P1_plan su_P1_shape su_P1_cert su_P1_guard su_P1_holes su_P1_hole MAIN MAIN_agree MAIN_nil T_su_P1).
    Qed.
  End Chain.

  (* [comment removed for export] *)
  Theorem asan_boot_closed : ltac2:(CDefT.buildp (gd_tbl_AsanBoot ()) "P,(8.$1.$9.$:.$;.(<.&40.Vsp,)(=.$4.Vsp,Vrdraw,Vbrk0,Vargv,Venvp,Vuid,Vhw,)(>.$4.Vsp,Vrdraw,Vargv,Venvp,Vuid,Vhw,)L,$?.VMAIN,Vfs,)(0.$1.(2.$1.$3.$4.Vsp,Vbrk0,Vmbase,Vrdraw,$5.(6.Vargv,Venvp,Vfs,Vstdin,Vuid,Vgid,Vhw,Vgroups,Vnet,Vnofile,Vsigmask,Vurandom,))A2.VMAIN,(7.$4.Vsp,Vrdraw,Vbrk0,Vargv,Venvp,Vuid,Vhw,)Vfs,)")
(* [comment removed for export] *).
  Proof. intros MS. exact (boot_chain MS). Qed.

  (* [comment removed for export] *)
  Hypothesis MAIN_entry : ltac2:(CDefT.buildp (gd_tbl_AsanBoot ()) "PR,(10.&5.(11.&40.))Pmem,P,(11.&40.)(12.(11.&8.))Pmd,$13.PE,$14.P,Pn,$?.P,(15.R1.$16.)(17.(11.&40.)(18.R3.R2.)(18.(7.$4.Vsp,Vrdraw,Vbrk0,Vargv,Venvp,Vuid,Vhw,)R2.))P,(19.Vsp,Vbrk0,Vrdraw,Vargv,Venvp,Vfs,Vuid,Vhw,R5.R4.R3.)P,(17.$1:.(1;.R4.)Vfs,)(0.$1.(1<.$1.R7.+970>0.R6.R5.)A2.VMAIN,R4.Vfs,)")
(* [comment removed for export] *).

  Theorem asan_boot_entry : ltac2:(CDefT.buildp (gd_tbl_AsanBoot ()) "(0.$1.(2.$1.$3.$4.Vsp,Vbrk0,Vmbase,Vrdraw,$5.(6.Vargv,Venvp,Vfs,Vstdin,Vuid,Vgid,Vhw,Vgroups,Vnet,Vnofile,Vsigmask,Vurandom,))A2.VMAIN,(7.$4.Vsp,Vrdraw,Vbrk0,Vargv,Venvp,Vuid,Vhw,)Vfs,)")
(* [comment removed for export] *).
  Proof.
    apply asan_boot_closed.
    intros h ch Hh E R FULL md HC.
    rewrite (HS_main_pc h ch Hh).
    pose proof (co_fs _ _ _ _ _ _ _ _ _ _ _ _ HC) as Hfs. rewrite Hfs.
    apply (MAIN_entry R FULL md E).
    - exact (proj1 (co_sinv _ _ _ _ _ _ _ _ _ _ _ _ HC)).
    - exact (hs_main_entry_A sp brk0 rdraw argv envp fs uid hw Hsp Hva h ch E R FULL md Hh HC).
    - exact Hfs.
  Qed.
End Boot.

(* [comment removed for export] *)
Theorem asan_boot_entry_inp : ltac2:(CDefT.buildp (gd_tbl_AsanBoot ()) "Psp,(11.&40.)Pbrk0,(11.&40.)Pmbase,(11.&40.)Prdraw,$1=.Pinp,$1>.P,(1?.R5.)P,(20.$1.R5.)P,(21.(22.R3.))P,(23.(24.R4.))P,(25.R9.(22.R5.)(24.R5.))P,(26.(27.R6.))P,(17.$28.(29.R7.)$2:.)P,(17.$2;.(2<.R8.)$2=.)PMAIN,P,$14.P,$1:.$2>.P,PE,$14.PE',$14.Pfs',$1:.P,(2?.$16.R3.R2.)(17.$2>.A2.R5.R4.R2.A2.R5.R3.R2.)P,PE,$14.Pfs',$1:.A3.R4.R2.R1.(30.$31.)P,PR,(10.&5.(11.&40.))Pmem,P,(11.&40.)(12.(11.&8.))Pmd,$13.PE,$14.P,Pn,$?.P,(15.R1.$16.)(17.(11.&40.)(18.R3.R2.)(18.(7.$4.R16.R13.R15.(22.R12.)(24.R12.)(27.R12.)(32.R12.))R2.))P,(19.R15.R14.R12.(22.R11.)(24.R11.)(33.R11.)(27.R11.)(32.R11.)R5.R4.R3.)P,(17.$1:.(1;.R4.)(33.R12.))(0.$1.(1<.$1.R7.+970>0.R6.R5.)A2.R:.R4.(33.R13.))(0.$1.(2.$1.$3.$4.R11.R10.R?.R>.$5.R=.)A2.R4.(7.$4.R11.R>.R10.(22.R=.)(24.R=.)(27.R=.)(32.R=.))(33.R=.))")
(* [comment removed for export] *).
Proof.
  intros sp brk0 mbase rdraw [argv envp ifs stdin uid gid groups net nofile sigmask hw ab va ur tm]
         Hsp Hbrk Hva Hve Hfit Huid Hab Hvs MAIN MAIN_agree MAIN_nil MAIN_entry.
  cbn [in_abort_terminal in_va_size] in Hab, Hvs. subst ab va.
  exact (asan_boot_entry sp brk0 mbase rdraw argv envp (fs_seed_tmp ifs tm) stdin uid gid hw groups net nofile sigmask ur
           Hsp Hbrk Hva Hve Hfit Huid MAIN MAIN_agree MAIN_nil MAIN_entry).
Qed.

(* [comment removed for export] *)
Lemma init_pc_is_entry : Z.of_N AsanUbsan.M.init_pc = a_entry BOTH.
Proof. reflexivity. Qed.
Lemma APH_is_phdrs : APH = AsanUbsan.M.phdrs.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
