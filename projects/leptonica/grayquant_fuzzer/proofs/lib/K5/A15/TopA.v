(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.leptonica.grayquant_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import MState Mem Frame Cells Step Arr Exec.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import ImageA.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import RzCPS.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Spec Require Import Prelim Canon Stdio Prog.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import Layout.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import RT_iface D_iface D_defs D_libiface I_iodefs X_xdefs.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AS Require Import PropExec.
Local Instance topa2_fx : PropExec.FPState := PropExec.fx0.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AS Require Import ShapeAlg SpinAlg AsanAcct AxSymExec3 AxSymExec3Sound AsanPlanCore AsanPlan AsanPlanSound.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AS15 Require Import AsanPlanImages.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AS Require Import AsanInit.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AS15 Require Import AsanTablesA AsanStartup.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AG Require Import HandoffKit.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import HandoffStart HandoffImage HandoffArgv HandoffCLX HandoffA RT_state RT_rep RT_init RT_init_mem HandoffRT HandoffLIB TopA_iodefs TopA_io TopA_start.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Top Require Import TopLevelA.
Import ListNotations.
Import AX2. Import AX2S. Import AP.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition hs_all_ok (ch : acs) : bool :=
  (Z.eqb (pc ch) a_main && hs_start_ok ch && hs_rt_ok ASAN_A ch && hs_lib_ok ch)%bool.

(* [comment removed for export] *)
Lemma asan_segtop : img_hi ASAN_A = SEGTOP_A.
Proof. reflexivity. Qed.
Lemma asan_shoff : shadow_off ASAN_A = SHB.
Proof. reflexivity. Qed.
Lemma asan_lim : AsanInit.LIMIT = VMLIMIT.
Proof. reflexivity. Qed.

Section Cert.
  (* [comment removed for export] *)
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

  (* [comment removed for export] *)
  Hypothesis FUZZ : fuzz_one_cps RTA LIB_A.   (* [comment removed for export] *)
  Hypothesis RC : rt_contracts RTA.
  Hypothesis IOC : forall Σ m, ART RTA Σ m -> io_consts m.

  (* [comment removed for export] *)
  Lemma topA_holes : forall (sp : word) (rdraw : EntryDraw) (brk0 : word) (argv envp : list (list byte)) (uid hw : word) (fs : Fs.Fs),
    valid_sp sp -> valid_argv argv -> valid_envp envp -> entry_stack_fits sp argv envp ->
    APS.holes_stmt ASEGS ASAN_A NX0 AsanInit.LIMIT HS_asan (SINV0 APH sp rdraw brk0 argv envp uid hw) (argH0 APH sp rdraw argv envp uid hw)
               (fun _ _ fs' => canonT (argv_Z argv) fs') fs.
  Proof using HS_ok FUZZ RC IOC.
    intros sp rdraw brk0 argv envp uid hw fs Hsp Hva Hve Hfit.
    intros h ch Hh E R FULL model HC.
    pose proof (HS_ok h ch Hh) as HT. unfold hs_all_ok in HT.
    apply andb_prop in HT as [HT HTL]. apply andb_prop in HT as [HT HTR]. apply andb_prop in HT as [Hpc HTS].
    apply Z.eqb_eq in Hpc. rewrite Hpc. cbv beta. rewrite (APS.co_fs _ _ _ _ _ _ _ _ _ _ _ _ HC).
    exact (hs_hole_rt ASAN_A NX0 AsanInit.LIMIT fs APH sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit asan_in_hull asan_hull_ok
             asan_segtop asan_shoff asan_lim E ch R FULL model HC HTS HTR LIB_A
             (hs_lib ASAN_A NX0 AsanInit.LIMIT _ _ fs asan_in_hull asan_hull_ok (argH0_high APH sp rdraw argv envp uid hw Hsp Hva)
                E ch R FULL model HC HTL)
             (canonT (argv_Z argv) fs) (main_rta FUZZ RC IOC argv fs Hva)).
  Qed.

  (* [comment removed for export] *)
  Theorem s3s_A_of : S3s_stmt Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs.
  Proof using IT0_ok startup_cert Hshape HS_ok FUZZ RC IOC.
    intros en inp Hve Hvi.
    exact (asan_startup_gen IT0 IT0_ok HS_asan startup_plan startup_shape KC0 BFUEL FUEL startup_cert Hshape
             (fun argv fs => canonT (argv_Z argv) fs) (fun argv fs => canonT_nil (argv_Z argv) fs) topA_holes en inp Hve Hvi).
  Qed.

  (* [comment removed for export] *)
End Cert.
