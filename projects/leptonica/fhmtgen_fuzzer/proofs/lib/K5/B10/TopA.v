(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the start-up certificate per CONFIG_RSEQ value; topA_holes over the launch's ProcInput and its launch facts, with argH0_high given the entry pc; s3s_A_of lifted to the run's segment list (the image plus the vDSO pair) by the RUNSEG premise, which the new lemma topA_runseg discharges through SRomStable.srun_init; PropExec qualified as K5.AS.PropExec where a twin module shadows it). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.leptonica.fhmtgen_fuzzer.images Require Import AsanUbsan.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import MState Mem Frame Cells Step Arr Exec.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.B10 Require Import ImageA.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import RzCPS.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Spec Require Import Prelim Canon Stdio Prog.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.B10 Require Import Layout.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.B10 Require Import RT_iface D_iface D_defs D_libiface I_iodefs X_xdefs.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AS Require Import PropExec.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Cfg Require SRomStable.
Local Instance topa2_fx : K5.AS.PropExec.FPState := K5.AS.PropExec.fx0.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AS Require Import ShapeAlg SpinAlg AsanAcct AxSymExec3 AxSymExec3Sound AsanPlanCore AsanPlan AsanPlanSound.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.ASB10 Require Import AsanPlanImages.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AS Require Import AsanInit.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.ASB10 Require Import AsanTablesA AsanStartup.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AG Require Import HandoffKit.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.B10 Require Import HandoffStart HandoffImage HandoffArgv HandoffCLX HandoffA RT_state RT_rep RT_init RT_init_mem HandoffRT HandoffLIB TopA_iodefs TopA_io TopA_start.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Top Require Import TopLevelA.
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
  (* one certificate and one hand-off table per CONFIG_RSEQ value [b] ([TopA_start]) *)
  Variable HS_asan : bool -> nat -> option acs.
  Variable startup_plan : bool -> plan.
  Variable startup_shape : bool -> shape.
  Variables KC0 BFUEL FUEL : nat.
  Hypothesis startup_cert : forall b,
    check ASEGS IT0 ASAN_A NX0 AsanInit.LIMIT XN0 XE0 XB0 (HS_asan b) KC0 BFUEL FUEL None (asan_a_init (rseq_z b)) (startup_plan b)
    = COk (startup_shape b).
  Hypothesis Hshape : forall b, holes_only (startup_shape b) = true.
  Hypothesis HS_ok : forall b h ch, HS_asan b h = Some ch -> hs_all_ok ch = true.

  (* [comment removed for export] *)
  Hypothesis FUZZ : fuzz_one_cps RTA LIB_A.   (* [comment removed for export] *)
  Hypothesis RC : rt_contracts RTA.
  Hypothesis IOC : forall Σ m, ART RTA Σ m -> io_consts m.

  (* [comment removed for export] *)
  Lemma topA_holes : forall (b : bool) (sp : word) (rdraw : EntryDraw) (brk0 mbase : word) (inp : ProcInput),
    valid_sp sp -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_launch inp ->
    entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) inp ->
    APS.holes_stmt ASEGS ASAN_A NX0 AsanInit.LIMIT (HS_asan b) (SINV0 APH AsanUbsan.M.init_pc sp rdraw brk0 mbase inp) (argH0 sp rdraw inp)
               (fun _ _ fs' => canonT (argv_Z (in_argv inp)) fs') (in_fs inp).
  Proof using HS_ok FUZZ RC IOC.
    intros b sp rdraw brk0 mbase inp Hsp Hva Hve Hlaunch Hlau.
    intros h ch Hh E R FULL model HC.
    pose proof (HS_ok b h ch Hh) as HT. unfold hs_all_ok in HT.
    apply andb_prop in HT as [HT HTL]. apply andb_prop in HT as [HT HTR]. apply andb_prop in HT as [Hpc HTS].
    apply Z.eqb_eq in Hpc. rewrite Hpc. cbv beta. rewrite (APS.co_fs _ _ _ _ _ _ _ _ _ _ _ _ HC).
    assert (AH : forall E (a : word), argH0 sp rdraw inp E a = true -> CEIL <= bv_unsigned a)
      (* [argH0_high] is closed over [Section Init]'s entry pc [apc : N], which its conclusion does not
         mention, so the pc is given here *)
      by (intros E1 a H; eapply (argH0_high AsanUbsan.M.init_pc); eassumption).
    exact (hs_hole_rt ASAN_A NX0 AsanInit.LIMIT (in_fs inp) APH AsanUbsan.M.init_pc sp rdraw brk0 mbase inp
             Hsp Hva Hve Hlaunch Hlau asan_in_hull asan_hull_ok
             asan_segtop asan_shoff asan_lim E ch R FULL model HC HTS HTR LIB_A
             (hs_lib ASAN_A NX0 AsanInit.LIMIT _ _ (in_fs inp) asan_in_hull asan_hull_ok AH E ch R FULL model HC HTL)
             (canonT (argv_Z (in_argv inp)) (in_fs inp)) (main_rta FUZZ RC IOC (in_argv inp) (in_fs inp) Hva)).
  Qed.

  (* the kernel is NOT pinned: [asan_startup_gen] takes the kernel of record from
     [Run.valid_input] itself.  The premise WAS [KERNEL : forall inp, valid_input inp ->
     in_kernel inp = default_kernel], which [kb_rseq = false] refutes. *)
  (* LPS 08b1429: the run is against [Run.run_segments]; the walk above is over
     the image's own segments.  The lift (the vDSO pair is r--, and the walk's
     reads stay off it) is the run-segments bridge of recipes/run-segments.md. *)
  Hypothesis RUNSEG : forall en inp T,
    valid_entry (mkImage ASEGS AsanUbsan.M.init_pc APH) en inp -> valid_input inp ->
    srealizes ASEGS (init_config ASEGS AsanUbsan.M.init_pc APH (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en)
                                 target_alloc_limit inp) T ->
    srealizes (run_segments ASEGS inp (en_sp en) (en_mmap_base en))
              (init_config (run_segments ASEGS inp (en_sp en) (en_mmap_base en)) AsanUbsan.M.init_pc APH
                           (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en) target_alloc_limit inp) T.

  Theorem s3s_A_of : S3s_stmt AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs.
  Proof using IT0_ok startup_cert Hshape HS_ok FUZZ RC IOC RUNSEG.
    intros en inp Hve Hvi.
    apply (RUNSEG en inp _ Hve Hvi).
    exact (asan_startup_gen IT0 IT0_ok HS_asan startup_plan startup_shape KC0 BFUEL FUEL startup_cert Hshape
             (fun argv fs => canonT (argv_Z argv) fs) (fun argv fs => canonT_nil (argv_Z argv) fs) topA_holes en inp Hve Hvi).
  Qed.

  (* [comment removed for export] *)
End Cert.

(* LPS 08b1429: [RUNSEG] (the walk over the image's own segments, lifted to the run's segment list
   and start) is the shared lift [SRomStable.srun_init] (Common/Cfg/SRomStable.v, G3's file;
   recipes/run-segments.md "srealizes variant").  The image has no vDSO text segment. *)
Lemma topA_runseg : forall en inp T,
  valid_entry (mkImage ASEGS AsanUbsan.M.init_pc APH) en inp -> valid_input inp ->
  srealizes ASEGS (init_config ASEGS AsanUbsan.M.init_pc APH (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en)
                               target_alloc_limit inp) T ->
  srealizes (run_segments ASEGS inp (en_sp en) (en_mmap_base en))
            (init_config (run_segments ASEGS inp (en_sp en) (en_mmap_base en)) AsanUbsan.M.init_pc APH
                         (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en) target_alloc_limit inp) T.
Proof.
  intros en inp T _ _ H.
  exact (SRomStable.srun_init ASEGS inp (en_sp en) (en_mmap_base en) _ _ _ _ _ _ eq_refl H).
Qed.
