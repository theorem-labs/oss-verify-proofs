(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch stated over the run's whole input; the start-up per CONFIG_RSEQ value and the new auxv layout). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.simdjson.fuzz_atpointer.images Require Import AsanUbsan.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import MState Mem Frame Cells Step Arr Exec ImageA RzCPS Cfg.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Spec Require Import Prelim Canon Stdio Prog.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.B Require Import Layout Zks Zkt Z81 D_defs Zbv Z11v Z7w.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.AS Require Import Zg2.
Local Instance topa2_fx : Zg2.FPState := Zg2.fx0.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.AS Require Import Zp7 Z10a Z1b Z78 Z7a
  Z2z Z2y Z33 Z31 Z1s Z3h Z3e.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.A Require Import Zbe.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.B Require Import Zbg Zbd Zba Zbb Zb9 Zm2 RT_rep Zku Zkw Zbc Zbf Z11d Z11c Z11e.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib Require Import TopLevel Obligations ProofBase TopLevelA.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Spec Require Import Zfv.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Image Stage.
From OSSVerify.simdjson.fuzz_atpointer.images Require Import Plain.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP.
Open Scope Z_scope.

(* [r] is the launch's CONFIG_RSEQ bit.  [hs_start_ok] and [hs_g1_ok] carry it
   because the revision's auxv vector is rseq-dependent, so the argv and stack
   window they check move with the flag. *)
Definition hs_all_ok (r : Z) (ch : acs) : bool :=
  (Z.eqb (pc ch) a_main && hs_start_ok r ch && hs_rt_ok ASAN_B ch && hs_g1_ok r ch)%bool.

Lemma asan_segtop : img_hi ASAN_B = SEGTOP_A.
Proof. reflexivity. Qed.
Lemma asan_shoff : shadow_off ASAN_B = SHB.
Proof. reflexivity. Qed.
Lemma asan_lim : Z1s.LIMIT = VMLIMIT.
Proof. reflexivity. Qed.

Section Cert.

  Variable IT0 : itab.
  Hypothesis IT0_ok : itab_sound ASEGS IT0.
  (* ONE CHAIN PER CONFIG_RSEQ VALUE, as B/Z11e.v states it: the hand-off table and the plan are
     read at the run's own [rseq_z (kb_rseq (in_kernel inp))]. *)
  Variable HS_both : Z -> nat -> option acs.
  Variable startup_plan : Z -> plan.
  Variable startup_shape : shape.
  Variables KC0 BFUEL FUEL : nat.
  (* ONE CERTIFICATE PER CLOSED [rseq_z b], joined by the [forall b] wrapper -- the type
     [AS/Z7d.v]'s [startup_cert] proves.  The flag is not pinned: [topA_holes] meets the
     run's [inp] and reads the tables at its own flag. *)
  Hypothesis startup_cert : forall b : bool,
    check ASEGS IT0 ASAN_B NX0 Z1s.LIMIT (rseq_z b) XN0 XE0 XB0 (HS_both (rseq_z b)) KC0 BFUEL FUEL None
          (asan_b_init (rseq_z b)) (startup_plan (rseq_z b)) = COk startup_shape.
  Hypothesis Hshape : holes_only startup_shape = true.
  Hypothesis HS_ok : forall (b : bool) h ch, HS_both (rseq_z b) h = Some ch -> hs_all_ok (rseq_z b) ch = true.

  Variable CL : client_B.
  Hypothesis HS_cl : forall (b : bool) h ch, HS_both (rseq_z b) h = Some ch -> cl_hs_ok CL ch = true.

  Hypothesis RC : rt_contracts2 RTA.
  Hypothesis IOC : forall Σ m, ART RTA Σ m -> io_consts m.

  Lemma topA_holes : forall (sp : word) (rdraw : EntryDraw) (brk0 mbase : word) (inp : ProcInput),
    valid_sp sp -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
    entry_stack_fits sp (in_argv inp) (in_envp inp) ->
    valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) inp ->
    APS.holes_stmt ASEGS ASAN_B NX0 Z1s.LIMIT (HS_both (rseq_z (kb_rseq (in_kernel inp))))
               (SINV0 ASAN_B APH sp rdraw brk0 mbase inp) (argH0 sp rdraw inp)
               (fun _ _ fs' => canonT (argv_Z (in_argv inp)) fs') (in_fs inp).
  Proof using HS_ok HS_cl RC IOC.
    intros sp rdraw brk0 mbase inp Hsp Hva Hve Hfit Hlaunch Hlau.
    intros h ch Hh E R FULL model HC.
    (* the hand-off state is checked at the run's own flag *)
    pose proof (HS_ok (kb_rseq (in_kernel inp)) h ch Hh) as HT. unfold hs_all_ok in HT.
    apply andb_prop in HT as [HT HTL]. apply andb_prop in HT as [HT HTR]. apply andb_prop in HT as [Hpc HTS].
    apply Z.eqb_eq in Hpc. rewrite Hpc. cbv beta. rewrite (APS.co_fs _ _ _ _ _ _ _ _ _ _ _ _ HC).
    assert (AH : forall E (a : word), argH0 sp rdraw inp E a = true -> CEIL <= bv_unsigned a)
      by (intros E1 a Ha; eapply argH0_high; eassumption).
    pose proof (cl_hs CL ASAN_B NX0 Z1s.LIMIT _ _ _ asan_in_hull asan_hull_ok AH E ch R FULL model HC _
                  (ri_HA' ASAN_B E ch model) (HS_cl _ h ch Hh)) as HLIB.
    pose proof (main_rta CL RC IOC (in_argv inp) (in_fs inp) Hva) as HMAIN.
    pose proof asan_in_hull as HIN. pose proof asan_hull_ok as HOK. pose proof asan_segtop as HST.
    pose proof asan_shoff as HSO. pose proof asan_lim as HLM.
    eapply hs_hole_rt with (A := ASAN_B) (nx0 := NX0) (LIMIT := Z1s.LIMIT) (fs := in_fs inp) (ph := APH) (sp := sp)
      (rdraw := rdraw) (brk0 := brk0) (mbase := mbase) (inp := inp) (E := E) (ch := ch) (R := R) (FULL := FULL)
      (model := model) (LIB := cl_LIB CL); assumption.
  Qed.

  Theorem s3s_A_of : S3s_stmt_e AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs.
  Proof using IT0_ok startup_cert Hshape HS_ok HS_cl RC IOC.
    intros en inp Hve Hvi.
    exact (asan_startup_gen IT0 IT0_ok HS_both startup_plan startup_shape KC0 BFUEL FUEL startup_cert Hshape
             (fun argv fs => canonT (argv_Z argv) fs) (fun argv fs => canonT_nil (argv_Z argv) fs) topA_holes en inp Hve Hvi).
  Qed.

  Theorem base_asan_of_cert :
    impl_P_stmt ->
    prog_no_enomem_stmt Image.psegs Stage.pstage Plain.M.init_pc Plain.M.phdrs source_alloc_limit ->
    strong_universal_error_free_T_scfg ACFG
      (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs)
      (mkImage AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs).
  Proof using IT0_ok startup_cert Hshape HS_ok HS_cl RC IOC.
    intros HP Hne.
    exact (error_free_of_S3s AsanUbsan.M.loaded_segments _ _ ltac:(repeat constructor) HP Hne (S3s_of_e _ _ _ s3s_A_of)).
  Qed.
End Cert.
