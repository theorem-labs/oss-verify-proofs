(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the top level over the launch input ProcInput and the CONFIG_RSEQ flag). *)
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.bzip2.bzip2_compress_target.images Require AsanUbsan.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require MState Mem Frame Cells Step Arr Exec ImageA RzCPS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Spec Require Prelim Canon Stdio Prog.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Layout RT_iface D_iface D_defs I_iodefs X_xdefs D_libiface L_libA.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require ShapeAlg SpinAlg AsanAcct AxSymExec3 AxSymExec3Sound AsanPlanCore AsanPlan AsanPlanSound AsanPlanImagesB AsanInit AsanTablesB AsanStartupB.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require HandoffKit.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require HandoffStart HandoffImage HandoffArgv HandoffCLX HandoffA RT_state RT_rep RT_init RT_init_mem HandoffRT HandoffLIB TopA_iodefs TopA_io TopA_start.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K Require TopLevelA.
Module TwinB__.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.bzip2.bzip2_compress_target.images Require Import AsanUbsan.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import MState Mem Frame Cells Step Arr Exec ImageA RzCPS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Spec Require Import Prelim Canon Stdio Prog.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Shadow.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.Layout.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_iface.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_iface.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.I_iodefs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.X_xdefs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_libiface.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_libA.TwinB__.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Instance topa2_fx : PropExec.FPState := PropExec.fx0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import ShapeAlg SpinAlg AsanAcct AxSymExec3 AxSymExec3Sound
  AsanPlanCore AsanPlan AsanPlanSound AsanPlanImagesB AsanInit AsanTablesB AsanStartupB.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import HandoffKit.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.HandoffStart.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.HandoffImage.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.HandoffArgv.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.HandoffCLX.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.HandoffA.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_state.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_rep.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_init.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_init_mem.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.HandoffRT.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.HandoffLIB.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.TopA_iodefs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.TopA_io.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.TopA_start.TwinB__.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K Require Import TopLevelA.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP.
Open Scope Z_scope.

(* [comment removed for export] *)
(* #108: per value of the plan's CONFIG_RSEQ flag [r] (through [hs_start_ok r]) *)
Definition hs_all_ok (r : Z) (ch : acs) : bool :=
  (Z.eqb (pc ch) a_main && hs_start_ok r ch && hs_rt_ok ASAN_B ch && hs_lib_ok ch)%bool.

(* [comment removed for export] *)
Lemma asan_segtop : img_hi ASAN_B = SEGTOP_A.
Proof. reflexivity. Qed.
Lemma asan_shoff : shadow_off ASAN_B = SHB.
Proof. reflexivity. Qed.
Lemma asan_lim : AsanInit.LIMIT = VMLIMIT.
Proof. reflexivity. Qed.

Section Cert.
  (* [comment removed for export] *)
  Variable IT0 : itab.
  Hypothesis IT0_ok : itab_sound ASEGS IT0.
  (** #108: tables, plan and shape per value of the plan's flag; one certificate per build
      ([TopA_start.asan_startup_gen]) *)
  Variable HS_both : Z -> nat -> option acs.
  Variable startup_plan : Z -> plan.
  Variable startup_shape : Z -> shape.
  Variables KC0 BFUEL FUEL : nat.
  Hypothesis startup_cert : forall b : bool,
    check ASEGS IT0 ASAN_B NX0 AsanInit.LIMIT (rseq_z b) XN0 XE0 XB0 (HS_both (rseq_z b)) KC0 BFUEL FUEL None
          (asan_b_init (rseq_z b)) (startup_plan (rseq_z b)) = COk (startup_shape (rseq_z b)).
  Hypothesis Hshape : forall b : bool, holes_only (startup_shape (rseq_z b)) = true.
  Hypothesis HS_ok : forall r h ch, HS_both r h = Some ch -> hs_all_ok r ch = true.

  (* [comment removed for export] *)
  Hypothesis RC : rt_contracts RTA.
  Hypothesis IOC : forall Σ m, ART RTA Σ m -> io_consts m.
  (* [comment removed for export] *)
  Hypothesis FUZZ : fuzz_one_cps RTA LIB_A.

  (* [comment removed for export] *)
  Lemma topA_holes : forall (sp : word) (rdraw : EntryDraw) (brk0 mbase : word) (inp : ProcInput),
    valid_sp sp -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_launch inp ->
    entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) inp ->
    APS.holes_stmt ASEGS ASAN_B NX0 AsanInit.LIMIT (HS_both (rseq_z (kb_rseq (in_kernel inp))))
               (SINV0 APH AsanUbsan.M.init_pc sp rdraw brk0 mbase inp) (argH0 sp rdraw inp)
               (fun _ _ fs' => canonT (argv_Z (in_argv inp)) fs') (in_fs inp).
  Proof using HS_ok RC IOC FUZZ.
    intros sp rdraw brk0 mbase inp Hsp Hva Hve Hvl Hlau.
    intros h ch Hh E R FULL model HC.
    pose proof (HS_ok _ h ch Hh) as HT. unfold hs_all_ok in HT.
    apply andb_prop in HT as [HT HTL]. apply andb_prop in HT as [HT HTR]. apply andb_prop in HT as [Hpc HTS].
    apply Z.eqb_eq in Hpc. rewrite Hpc. cbv beta. rewrite (APS.co_fs _ _ _ _ _ _ _ _ _ _ _ _ HC).
    exact (hs_hole_rt ASAN_B NX0 AsanInit.LIMIT (in_fs inp) APH AsanUbsan.M.init_pc sp rdraw brk0 mbase inp Hsp Hva Hve Hvl Hlau
             asan_in_hull asan_hull_ok asan_segtop asan_shoff asan_lim E ch R FULL model HC HTS HTR LIB_A
             (hs_lib ASAN_B NX0 AsanInit.LIMIT _ _ (in_fs inp) asan_in_hull asan_hull_ok
                (argH0_high AsanUbsan.M.init_pc sp rdraw inp Hsp Hva) E ch R FULL model HC HTL)
             (canonT (argv_Z (in_argv inp)) (in_fs inp)) (main_rta RC IOC FUZZ (in_argv inp) (in_fs inp) Hva)).
  Qed.

  (* [comment removed for export] *)
  Theorem s3s_A_of : S3s_stmt AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs.
  Proof using IT0_ok startup_cert Hshape HS_ok RC IOC FUZZ.
    intros en inp Hve Hvi.
    exact (asan_startup_gen IT0 IT0_ok HS_both startup_plan startup_shape KC0 BFUEL FUEL startup_cert Hshape
             (fun argv fs => canonT (argv_Z argv) fs) (fun argv fs => canonT_nil (argv_Z argv) fs) topA_holes en inp Hve Hvi).
  Qed.

  (* [comment removed for export] *)
End Cert.
End TwinB__.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.bzip2.bzip2_compress_target.images Require Import Asan.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import MState Mem Frame Cells Step Arr Exec ImageA RzCPS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Spec Require Import Prelim Canon Stdio Prog.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Layout Shadow RT_iface D_iface D_defs I_iodefs X_xdefs D_libiface L_libA.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Instance topa2_fx : PropExec.FPState := PropExec.fx0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import ShapeAlg SpinAlg AsanAcct AxSymExec3 AxSymExec3Sound
  AsanPlanCore AsanPlan AsanPlanSound AsanPlanImages AsanInit AsanTablesA AsanStartup.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import HandoffKit HandoffStart HandoffImage HandoffArgv HandoffCLX HandoffA
  RT_state RT_rep RT_init RT_init_mem HandoffRT HandoffLIB TopA_iodefs TopA_io TopA_start.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K Require Import TopLevelA.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP.
Open Scope Z_scope.

(* [comment removed for export] *)
(* #108: per value of the plan's CONFIG_RSEQ flag [r] (see the twin above) *)
Definition hs_all_ok (r : Z) (ch : acs) : bool :=
  (Z.eqb (pc ch) a_main && hs_start_ok r ch && hs_rt_ok ASAN_A ch && hs_lib_ok ch)%bool.

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
  Variable HS_asan : Z -> nat -> option acs.
  Variable startup_plan : Z -> plan.
  Variable startup_shape : Z -> shape.
  Variables KC0 BFUEL FUEL : nat.
  Hypothesis startup_cert : forall b : bool,
    check ASEGS IT0 ASAN_A NX0 AsanInit.LIMIT (rseq_z b) XN0 XE0 XB0 (HS_asan (rseq_z b)) KC0 BFUEL FUEL None
          (asan_a_init (rseq_z b)) (startup_plan (rseq_z b)) = COk (startup_shape (rseq_z b)).
  Hypothesis Hshape : forall b : bool, holes_only (startup_shape (rseq_z b)) = true.
  Hypothesis HS_ok : forall r h ch, HS_asan r h = Some ch -> hs_all_ok r ch = true.

  (* [comment removed for export] *)
  Hypothesis RC : rt_contracts RTA.
  Hypothesis IOC : forall Σ m, ART RTA Σ m -> io_consts m.
  (* [comment removed for export] *)
  Hypothesis FUZZ : fuzz_one_cps RTA LIB_A.

  (* [comment removed for export] *)
  Lemma topA_holes : forall (sp : word) (rdraw : EntryDraw) (brk0 mbase : word) (inp : ProcInput),
    valid_sp sp -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_launch inp ->
    entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) inp ->
    APS.holes_stmt ASEGS ASAN_A NX0 AsanInit.LIMIT (HS_asan (rseq_z (kb_rseq (in_kernel inp))))
               (SINV0 APH Asan.M.init_pc sp rdraw brk0 mbase inp) (argH0 sp rdraw inp)
               (fun _ _ fs' => canonT (argv_Z (in_argv inp)) fs') (in_fs inp).
  Proof using HS_ok RC IOC FUZZ.
    intros sp rdraw brk0 mbase inp Hsp Hva Hve Hvl Hlau.
    intros h ch Hh E R FULL model HC.
    pose proof (HS_ok _ h ch Hh) as HT. unfold hs_all_ok in HT.
    apply andb_prop in HT as [HT HTL]. apply andb_prop in HT as [HT HTR]. apply andb_prop in HT as [Hpc HTS].
    apply Z.eqb_eq in Hpc. rewrite Hpc. cbv beta. rewrite (APS.co_fs _ _ _ _ _ _ _ _ _ _ _ _ HC).
    exact (hs_hole_rt ASAN_A NX0 AsanInit.LIMIT (in_fs inp) APH Asan.M.init_pc sp rdraw brk0 mbase inp Hsp Hva Hve Hvl Hlau
             asan_in_hull asan_hull_ok asan_segtop asan_shoff asan_lim E ch R FULL model HC HTS HTR LIB_A
             (hs_lib ASAN_A NX0 AsanInit.LIMIT _ _ (in_fs inp) asan_in_hull asan_hull_ok
                (argH0_high Asan.M.init_pc sp rdraw inp Hsp Hva) E ch R FULL model HC HTL)
             (canonT (argv_Z (in_argv inp)) (in_fs inp)) (main_rta RC IOC FUZZ (in_argv inp) (in_fs inp) Hva)).
  Qed.

  (* [comment removed for export] *)
  Theorem s3s_A_of : S3s_stmt Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs.
  Proof using IT0_ok startup_cert Hshape HS_ok RC IOC FUZZ.
    intros en inp Hve Hvi.
    exact (asan_startup_gen IT0 IT0_ok HS_asan startup_plan startup_shape KC0 BFUEL FUEL startup_cert Hshape
             (fun argv fs => canonT (argv_Z argv) fs) (fun argv fs => canonT_nil (argv_Z argv) fs) topA_holes en inp Hve Hvi).
  Qed.

  (* [comment removed for export] *)
End Cert.
