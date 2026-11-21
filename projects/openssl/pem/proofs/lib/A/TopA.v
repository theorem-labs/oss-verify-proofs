(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the input's kernel build and exec file name; the start-up facts stated over the launch's ProcInput; the run's segment list with the vDSO/vvar pair; the launch premises; the stack-depot count's variable in the computed main hand-off). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.openssl.pem.images Require Import Asan.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import MState Mem Frame Cells Step Arr Exec ImageA RzCPS.
From OSSVerify.Proofs.openssl.pem.lib.Common.Cfg Require SRomStable.
From OSSVerify.Proofs.openssl.pem.lib.Spec Require Import Prelim Canon Stdio Prog CanonSpec.
From OSSVerify.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OSSVerify.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_iface D_defs D_libiface D_libiface_pem I_iodefs X_xdefs.
From OSSVerify.Proofs.openssl.pem.lib.Common Require Import PropExec ShapeAlg SpinAlg AsanAcct AxSymExec3 AxSymExec3Sound
  AsanPlanCore AsanPlan AsanPlanSound AsanInit.
From OSSVerify.Proofs.openssl.pem.lib.Start Require Import AsanChain A_PlanImage A_Atable A_Chain.
From OSSVerify.Proofs.openssl.pem.lib.A Require Import HandoffKit HandoffSplit.
From OSSVerify.Proofs.openssl.pem.lib.A Require Import HandoffStart HandoffImage HandoffArgv HandoffCLX HandoffA RT_state RT_rep RT_census RT_init RT_init_mem HandoffRT HandoffLIB.
From OSSVerify.Proofs.openssl.pem.lib Require Import ClaVerdict Spec.
From OSSVerify.Proofs.openssl.pem.lib.Top Require Import TopBridge.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition hs_all_ok (ch : acs) : bool :=
  (Z.eqb (pc ch) a_main && hs_start_ok ch && hs_rt_ok A_T ch && hs_latch_ok ch)%bool.

(* [comment removed for export] *)
Lemma A_t_segtop : img_hi A_T = SEGTOP_A. Proof. reflexivity. Qed.
Lemma A_t_seglo : img_lo A_T = SEGLO. Proof. reflexivity. Qed.
Lemma A_t_shoff : shadow_off A_T = SHB. Proof. reflexivity. Qed.
Lemma A_lim : AsanInit.LIMIT = VMLIMIT. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition V_F : nat := 48.

Lemma pc_inst : forall inv J e, pc (inst inv J e) = pc inv.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma spec_nil : forall argv fs, Spec.spec argv fs [].
Proof. intros argv fs. apply (proj1 (canon_spec_eq argv fs [])). apply canonT_nil. Qed.

(* [comment removed for export] *)
Definition cli_okA (C : cli_sigA) : Prop :=
  lib0_at_main (ca_test C) (ca_lib0 C)
  /\ ca_test C (inst A_HSm V_F (ELit 2)) = true /\ ca_test C (inst A_HSm V_F (ELit 3)) = true
  /\ lib0_local_d (ca_lib0 C) /\ lib_local_d (ca_lib C)
  /\ fuzz_init_cps RTA (ca_lib0 C) (ca_lib C) (ca_sites C) (ca_calls C) /\ fuzz_one_cps RTA (ca_lib C) (ca_sites C) (ca_calls C)
  /\ cg_has CENSUS (ca_sites C) (ca_calls C).

Section Top.
  (* [comment removed for export] *)
  Variable C : cli_sigA.
  Hypothesis HC0 : lib0_at_main (ca_test C) (ca_lib0 C).
  (* [comment removed for export] *)
  Hypothesis HS2_ok : hs_all_ok (inst A_HSm V_F (ELit 2)) = true.
  Hypothesis HS3_ok : hs_all_ok (inst A_HSm V_F (ELit 3)) = true.
  Hypothesis HT2_ok : ca_test C (inst A_HSm V_F (ELit 2)) = true.
  Hypothesis HT3_ok : ca_test C (inst A_HSm V_F (ELit 3)) = true.
  (* [comment removed for export] *)
  Hypothesis HF : fact_ok (kn A_HSm) (KRange (EVar V_F) 2 (2 + 1)) = true.
  Hypothesis Hlog : s_log (a_ss A_HSm) = [].
  (* [comment removed for export] *)
  Hypothesis MAIN : forall argv fs, valid_argv argv ->
    forall c, START RTA OUT_repA ERR_repA (XENVA false) (LIBpre C) CENSUS argv fs c -> realizes asegs c (canonT (argv_Z argv) fs).   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma topA_hole_lit : forall ch, hs_all_ok ch = true -> ca_test C ch = true ->
    forall (sp : word) (rdraw : EntryDraw) (brk0 mbase : word) (inp : ProcInput),
    valid_sp sp -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_launch inp ->
    entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) inp ->
    forall E R FULL model,
      APS.cs_ok A_SEGS A_T AsanInit.LIMIT (SINV0 A_PH Asan.M.init_pc sp rdraw brk0 mbase inp) (argH0 sp rdraw inp) (bv_unsigned sp)
                (in_fs inp) E ch R FULL model ->
      srealizes A_SEGS (APS.cfg_of A_SEGS R (pc ch) FULL model) (Spec.spec (in_argv inp) (m_fs model)).
  Proof using HC0 MAIN.
    intros ch HT HTC sp rdraw brk0 mbase inp Hsp Hva Hve Hlaunch Hlau E R FULL model HC.
    set (argv := in_argv inp) in *. set (fs := in_fs inp) in *.
    unfold hs_all_ok in HT.
    apply andb_prop in HT as [HT HTL]. apply andb_prop in HT as [HT HTR]. apply andb_prop in HT as [Hpc HTS].
    apply Z.eqb_eq in Hpc. rewrite Hpc. rewrite (APS.co_fs _ _ _ _ _ _ _ _ _ _ _ _ HC).
    assert (AHH : forall E (a : word), argH0 sp rdraw inp E a = true -> CEIL <= bv_unsigned a /\ bv_unsigned sp <= bv_unsigned a)
      (* MEASURED by a probe build: [eapply argH0_high] leaves five goals
         [eassumption] cannot close -- (list Segment), atable, PhdrInfo, N, Z, i.e.
         AsanInit's [segs], [A], [ph], [apc], [LIM].  Unlike A/HandoffA.v, this Section
         has no Variable of those types for [eassumption] to find, so pass all ten in
         AsanInit's Section order (AsanInit.v:84-95). *)
      by (intros E1 a H;
          eapply (argH0_high A_SEGS A_T A_PH Asan.M.init_pc sp rdraw brk0 mbase inp AsanInit.LIMIT);
          eassumption).
    pose proof (hs_libpre A_T AsanInit.LIMIT _ _ _ fs A_t_in_hull A_t_hull_ok AHH A_t_segtop A_t_seglo E ch R FULL model HC C HC0 HTL HTC) as HLB.
    pose proof A_t_in_hull as Hin0. pose proof A_t_hull_ok as Hhull0. pose proof A_t_segtop as Hst0.
    pose proof A_t_seglo as Hsl0. pose proof A_t_shoff as Hsh0. pose proof A_lim as Hlim0.
    eapply hs_hole_rt; try eassumption.
    intros c HS. apply (rz_conseq asegs c _ _ (MAIN argv fs Hva c HS)). exact (canon_spec_eq argv fs).
  Qed.

  (* [comment removed for export] *)
  Lemma topA_holes : forall (sp : word) (rdraw : EntryDraw) (brk0 mbase : word) (inp : ProcInput),
    valid_sp sp -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_launch inp ->
    entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) inp ->
    APS.holes_stmt A_SEGS A_T AsanInit.LIMIT (HS_one A_HSm) (SINV0 A_PH Asan.M.init_pc sp rdraw brk0 mbase inp) (argH0 sp rdraw inp)
                   (bv_unsigned sp) (fun _ _ fs' => Spec.spec (in_argv inp) fs') (in_fs inp).
  Proof using HC0 HS2_ok HS3_ok HT2_ok HT3_ok HF Hlog MAIN.
    intros sp rdraw brk0 mbase inp Hsp Hva Hve Hlaunch Hlau h ch Hh E R FULL model HC.
    unfold HS_one in Hh. destruct (Nat.eqb h 0); [|discriminate Hh]. injection Hh as <-. cbv beta.
    destruct (cs_ok_split2 A_SEGS A_T AsanInit.LIMIT _ _ _ (in_fs inp) A_HSm V_F 2 HF Hlog E R FULL model HC) as [H2|H3].
    - rewrite <- (pc_inst A_HSm V_F (ELit 2)).
      exact (topA_hole_lit _ HS2_ok HT2_ok sp rdraw brk0 mbase inp Hsp Hva Hve Hlaunch Hlau E R FULL model H2).
    - rewrite <- (pc_inst A_HSm V_F (ELit (2 + 1))).
      exact (topA_hole_lit _ HS3_ok HT3_ok sp rdraw brk0 mbase inp Hsp Hva Hve Hlaunch Hlau E R FULL model H3).
  Qed.

  (* [comment removed for export] *)
  Theorem topA_realizes :
    image_realizes Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs target_alloc_limit Spec.spec.
  Proof using HC0 HS2_ok HS3_ok HT2_ok HT3_ok HF Hlog MAIN.
    (* LPS 08b1429: the run reads the image against [run_segments]; [SRomStable.srun_init] lifts the
       start-up chain's walk over the image's own segments (the image carries no vDSO, [eq_refl]). *)
    intros sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask urnd kern execfn sd
           Hsp Hbrk Hmb Hva Hve Hfit Huid _ _ Hlau Hlaunch.
    set (inp := InpRec.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd kern execfn sd) in *.
    apply SRomStable.srun_init; [reflexivity|].
    exact (A_startup_main sp rdraw brk0 mbase inp Hsp Hbrk Hmb Hva Hve Huid Hlaunch eq_refl Hlau
             (fun _ _ fs' => Spec.spec (in_argv inp) fs') (fun _ _ _ _ _ => eq_refl) (fun _ _ fs' => spec_nil (in_argv inp) fs')
             (topA_holes sp rdraw brk0 mbase inp Hsp Hva Hve Hlaunch Hlau)).
  Qed.
End Top.
