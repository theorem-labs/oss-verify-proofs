(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: the hand-off is stated over the run's whole launch input, with the hand-off table, plan and result shape read at its CONFIG_RSEQ flag and one certificate per flag value, and passes the table's bounds on the vDSO tail of the reserved list to the runtime hand-off; taken in part from projects/simdjson/fuzz_ondemand/proofs/lib/A/TopA.v, lines 28-32, 40-44, 50-63, 71-88, 106-107. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.simdjson.fuzz_implementations.images Require Import Asan.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import MState Mem Frame Cells Step Arr Exec ImageA RzCPS Cfg.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim Canon Stdio Prog.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.A Require Import Layout Shadow RT_iface RT_iface2 D_iface D_defs I_iodefs X_xdefs Imp_libifaceA Imp_handoffA.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.AS Require Import PropExec.
Local Instance topa2_fx : PropExec.FPState := PropExec.fx0.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg SpinAlg AsanAcct AxSymExec3 AxSymExec3Sound
  AsanPlanCore AsanPlan AsanPlanSound AsanPlanImages AsanInit AsanTablesA AsanStartup.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.A Require Import HandoffKit HandoffStart HandoffImage HandoffArgv HandoffCLX HandoffA
  RT_state RT_rep RT_init RT_init_mem HandoffG1 HandoffRT TopA_iodefs TopA_start.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib Require Import TopLevel Obligations ProofBase TopLevelA.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import ProgDetIface.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Image Stage.
From OSSVerify.simdjson.fuzz_implementations.images Require Import Plain.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP.
Open Scope Z_scope.

#[local] Existing Instance OSSVerify.Proofs.simdjson.fuzz_implementations.lib.A.Shadow.GWf.
(* [r] is the launch's CONFIG_RSEQ bit.  [hs_start_ok] and [hs_g1_ok] carry it
   because the revision's auxv vector is rseq-dependent, so the argv and stack
   window they check move with the flag. *)
Definition hs_all_ok (r : Z) (ch : acs) : bool :=
  (Z.eqb (pc ch) a_main && hs_start_ok r ch && hs_rt_ok ASAN_A ch && hs_g1_ok r ch)%bool.

Lemma asan_segtop : img_hi ASAN_A = SEGTOP_A.
Proof. reflexivity. Qed.
Lemma asan_shoff : shadow_off ASAN_A = SHB.
Proof. reflexivity. Qed.
Lemma asan_lim : AsanInit.LIMIT = VMLIMIT.
Proof. reflexivity. Qed.
(* The vDSO tail bounds RT_init.ri_artm reads off the table: two intervals, 20 pages. *)
Lemma asan_nresx : (n_resx ASAN_A <= 2)%nat.
Proof. cbn. lia. Qed.
Lemma asan_resxb : resx_bytes ASAN_A <= 81920.
Proof. unfold resx_bytes. cbn. lia. Qed.

Section Cert.

  Variable IT0 : itab.
  Hypothesis IT0_ok : itab_sound ASEGS IT0.
  (* ONE CHAIN PER CONFIG_RSEQ VALUE (A/TopA_start.v): the hand-off table, the plan and
     the result shape are read at the run's own [rseq_z (kb_rseq (in_kernel inp))]; the
     hand-off states move with [AUXSZ r = 432 + 32 * r], so one table cannot serve both. *)
  Variable HS_asan : Z -> nat -> option acs.
  Variable startup_plan : Z -> plan.
  Variable startup_shape : Z -> shape.
  Variables KC0 BFUEL FUEL : nat.
  (* ONE CERTIFICATE PER CLOSED [rseq_z b], joined by the [forall b] wrapper --
     the type [AS/AsanStartupCert.v]'s [startup_cert] proves. *)
  Hypothesis startup_cert : forall b : bool,
    check ASEGS IT0 ASAN_A NX0 AsanInit.LIMIT (rseq_z b) XN0 XE0 XB0 (HS_asan (rseq_z b)) KC0 BFUEL FUEL None
          (asan_a_init (rseq_z b)) (startup_plan (rseq_z b)) = COk (startup_shape (rseq_z b)).
  Hypothesis Hshape : forall b : bool, holes_only (startup_shape (rseq_z b)) = true.
  Hypothesis HS_ok : forall (b : bool) h ch, HS_asan (rseq_z b) h = Some ch -> hs_all_ok (rseq_z b) ch = true.

  Hypothesis HS_cl : forall (b : bool) h ch, HS_asan (rseq_z b) h = Some ch -> hs_imp_ok ch = true.

  Hypothesis MAIN : forall argv fs, valid_argv argv -> forall c, START RTA OUT_repA ERR_repA XENVA (imp_libA None) argv fs c -> realizes asegs c (canonT (argv_Z argv) fs).

  (* LPS 727298f3: the launch is the run's whole input [inp] (AS/AsanInit.v Section Init),
     and the hand-off table and checks are read at its own CONFIG_RSEQ flag. *)
  Lemma topA_holes : forall (sp : word) (rdraw : EntryDraw) (brk0 mbase : word) (inp : ProcInput),
    valid_sp sp -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> entry_stack_fits sp (in_argv inp) (in_envp inp) ->
    valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) inp ->
    APS.holes_stmt ASEGS ASAN_A NX0 AsanInit.LIMIT (HS_asan (rseq_z (kb_rseq (in_kernel inp))))
      (SINV0 ASAN_A APH sp rdraw brk0 mbase inp) (argH0 sp rdraw inp)
      (fun _ _ fs' => canonT (argv_Z (in_argv inp)) fs') (in_fs inp).
  Proof using HS_ok HS_cl MAIN.
    intros sp rdraw brk0 mbase inp Hsp Hva Hve Hfit Hlaunch Hlau h ch Hh E R FULL model HC.
    pose proof (HS_ok (kb_rseq (in_kernel inp)) h ch Hh) as HT. unfold hs_all_ok in HT.
    apply andb_prop in HT as [HT HTL]. apply andb_prop in HT as [HT HTR]. apply andb_prop in HT as [Hpc HTS].
    apply Z.eqb_eq in Hpc. rewrite Hpc. cbv beta. rewrite (APS.co_fs _ _ _ _ _ _ _ _ _ _ _ _ HC).
    exact (hs_hole_rt ASAN_A NX0 AsanInit.LIMIT (in_fs inp) APH sp rdraw brk0 mbase inp Hsp Hva Hve Hfit Hlaunch Hlau
             asan_in_hull asan_hull_ok asan_segtop asan_shoff asan_lim asan_nresx asan_resxb E ch R FULL model HC HTS HTR HTL (imp_libA None)
             (hs_imp_gen ASAN_A NX0 AsanInit.LIMIT _ _ (in_fs inp) asan_in_hull asan_hull_ok
                (hrt_argH_high sp rdraw brk0 mbase inp Hsp Hva Hve Hfit Hlaunch Hlau)
                E ch R FULL model HC _ (ri_HA' ASAN_A E ch model) (HS_cl (kb_rseq (in_kernel inp)) h ch Hh))
             (canonT (argv_Z (in_argv inp)) (in_fs inp)) (MAIN (in_argv inp) (in_fs inp) Hva)).
  Qed.

  Theorem s3s_A_of : S3s_stmt_e Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs.
  Proof using IT0_ok startup_cert Hshape HS_ok HS_cl MAIN.
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
  Proof using IT0_ok startup_cert Hshape HS_ok HS_cl MAIN.
    intros HP Hne.
    exact (error_free_of_S3s Asan.M.loaded_segments _ _ ltac:(repeat constructor) HP Hne (S3s_of_e _ _ _ s3s_A_of)).
  Qed.
End Cert.
