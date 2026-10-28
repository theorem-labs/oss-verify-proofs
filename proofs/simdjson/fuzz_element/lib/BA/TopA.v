(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.simdjson.fuzz_element.images Require Import Asan.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import MState Mem Frame Cells Step Arr Exec ImageA RzCPS Cfg.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim Canon Stdio Prog.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface2. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import D_iface D_defs. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import I_iodefs X_xdefs D_client.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import PropExec.
Local Instance topa2_fx : PropExec.FPState := PropExec.fx0.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg SpinAlg AsanAcct AxSymExec3 AxSymExec3Sound
  AsanPlanCore AsanPlan AsanPlanSound AsanPlanImages AsanInit AsanTablesA AsanStartup.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import HandoffKit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import HandoffStart HandoffImage HandoffArgv HandoffCLX HandoffA RT_state RT_rep RT_init RT_init_mem HandoffG1 HandoffRT TopA_iodefs TopA_io TopA_start.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib Require Import TopLevel Obligations ProofBase TopLevelA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import ProgDetIface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Image Stage.
From OssFuzzTheorems.simdjson.fuzz_element.images Require Import Plain.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP.
Open Scope Z_scope.

#[local] Existing Instance OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A.Shadow.GWf.
Definition hs_all_ok (ch : acs) : bool :=
  (Z.eqb (pc ch) a_main && hs_start_ok ch && hs_rt_ok ASAN_A ch && hs_g1_ok ch)%bool.

Lemma asan_segtop : img_hi ASAN_A = SEGTOP_A.
Proof. reflexivity. Qed.
Lemma asan_shoff : shadow_off ASAN_A = SHB.
Proof. reflexivity. Qed.
Lemma asan_lim : AsanInit.LIMIT = VMLIMIT.
Proof. reflexivity. Qed.

Section Cert.

  Variable IT0 : itab.
  Hypothesis IT0_ok : itab_sound ASEGS IT0.
  Variable HS_asan : nat -> option acs.
  Variable startup_plan : plan.
  Variable startup_shape : shape.
  Variables KC0 BFUEL FUEL : nat.
  Hypothesis startup_cert :
    check ASEGS IT0 ASAN_A NX0 AsanInit.LIMIT XN0 XE0 XB0 HS_asan KC0 BFUEL FUEL None asan_a_init startup_plan = COk startup_shape.
  Hypothesis Hshape : holes_only startup_shape = true.
  Hypothesis HS_ok : forall h ch, HS_asan h = Some ch -> hs_all_ok ch = true.

  Variable CL : client_B.
  Hypothesis HS_cl : forall h ch, HS_asan h = Some ch -> cl_hs_ok CL ch = true.

  Hypothesis RC : rt_contracts2 RTA.
  Hypothesis IOC : forall Σ m, ART RTA Σ m -> io_consts m.

  Lemma topA_holes : forall (sp : word) (rdraw : EntryDraw) (brk0 : word) (argv envp : list (list byte)) (uid hw : word) (fs : Fs.Fs),
    valid_sp sp -> valid_argv argv -> valid_envp envp -> entry_stack_fits sp argv envp ->
    APS.holes_stmt ASEGS ASAN_A NX0 AsanInit.LIMIT HS_asan (SINV0 APH sp rdraw brk0 argv envp uid hw) (argH0 APH sp rdraw argv envp uid hw)
               (fun _ _ fs' => canonT (argv_Z argv) fs') fs.
  Proof using HS_ok HS_cl RC IOC.
    intros sp rdraw brk0 argv envp uid hw fs Hsp Hva Hve Hfit.
    intros h ch Hh E R FULL model HC.
    pose proof (HS_ok h ch Hh) as HT. unfold hs_all_ok in HT.
    apply andb_prop in HT as [HT HTL]. apply andb_prop in HT as [HT HTR]. apply andb_prop in HT as [Hpc HTS].
    apply Z.eqb_eq in Hpc. rewrite Hpc. cbv beta. rewrite (APS.co_fs _ _ _ _ _ _ _ _ _ _ _ _ HC).
    exact (hs_hole_rt ASAN_A NX0 AsanInit.LIMIT fs APH sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit asan_in_hull asan_hull_ok
             asan_segtop asan_shoff asan_lim E ch R FULL model HC HTS HTR HTL (cl_LIB CL)
             (cl_hs CL ASAN_A NX0 AsanInit.LIMIT _ _ fs asan_in_hull asan_hull_ok (argH0_high APH sp rdraw argv envp uid hw Hsp Hva)
                E ch R FULL model HC _ (ri_HA' ASAN_A E ch model) (HS_cl h ch Hh))
             (canonT (argv_Z argv) fs) (main_rta CL RC IOC argv fs Hva)).
  Qed.

  Theorem s3s_A_of : S3s_stmt_e Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs.
  Proof using IT0_ok startup_cert Hshape HS_ok HS_cl RC IOC.
    intros en inp Hve Hvi.
    exact (asan_startup_gen IT0 IT0_ok HS_asan startup_plan startup_shape KC0 BFUEL FUEL startup_cert Hshape
             (fun argv fs => canonT (argv_Z argv) fs) (fun argv fs => canonT_nil (argv_Z argv) fs) topA_holes en inp Hve Hvi).
  Qed.

  Theorem base_asan_of_cert :
    impl_P_stmt ->
    prog_no_enomem_stmt Image.psegs Stage.pstage Plain.M.init_pc Plain.M.phdrs source_alloc_limit ->
    strong_universal_error_free_T_scfg ACFG
      (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs)
      (mkImage Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs).
  Proof using IT0_ok startup_cert Hshape HS_ok HS_cl RC IOC.
    intros HP Hne. exact (error_free_of_S3s _ _ _ HP Hne (S3s_of_e _ _ _ s3s_A_of)).
  Qed.
End Cert.
