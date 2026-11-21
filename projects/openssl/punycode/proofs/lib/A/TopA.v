(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the hand-off lemmas take the run's whole ProcInput with the mmap base and the launch's premises, the run's SIGPIPE flag is quantified, the start-up walk is lifted to the run's segments, and the stack-depot split reads its variable and range [0, 1] from the hand-off table computed in the build). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.openssl.punycode.images Require Import Asan.
From OSSVerify.Proofs.openssl.punycode.lib.Lib Require Import MState Mem Frame Cells Step Arr Exec ImageA RzCPS.
From OSSVerify.Proofs.openssl.punycode.lib.Common.Cfg Require SRomStable.
From OSSVerify.Proofs.openssl.punycode.lib.Spec Require Import Prelim Canon Stdio Prog CanonSpec.
From OSSVerify.Proofs.openssl.punycode.lib.A Require Import Layout Shadow RT_iface D_iface D_defs I_iodefs X_xdefs Fz_defs.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import PropExec ShapeAlg SpinAlg AsanAcct AxSymExec3 AxSymExec3Sound
  AsanPlanCore AsanPlan AsanPlanSound AsanInit.
From OSSVerify.Proofs.openssl.punycode.lib.Start Require Import AsanChain A_PlanImage A_Atable A_Chain.
From OSSVerify.Proofs.openssl.punycode.lib.A Require Import HandoffKit HandoffStart HandoffImage HandoffArgv HandoffCLX HandoffA
  RT_state RT_rep RT_init RT_init_mem HandoffRT HandoffLIB HandoffSplit.
From OSSVerify.Proofs.openssl.punycode.lib Require Import ClaVerdict Spec.
From OSSVerify.Proofs.openssl.punycode.lib.Top Require Import TopBridge.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition hs_all_ok (ch : acs) : bool :=
  (Z.eqb (pc ch) a_main && hs_start_ok ch && hs_rt_ok A_T ch && hs_lib_ok ch)%bool.

(* [comment removed for export] *)
Lemma A_t_segtop : img_hi A_T = SEGTOP_A. Proof. reflexivity. Qed.
Lemma A_t_seglo : img_lo A_T = SEGLO. Proof. reflexivity. Qed.
Lemma A_t_shoff : shadow_off A_T = SHB. Proof. reflexivity. Qed.
Lemma A_lim : AsanInit.LIMIT = VMLIMIT. Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* the hand-off table computed in the build (Start/A_Chain.v) holds the ASan stack-depot count as [EVar V_F + 2]
   with [V_F] in [0, 1] (Start/PlanCoGen.v's [pc_join] at level 3) *)
Definition V_F : nat := 48.

Lemma pc_inst : forall inv J e, pc (inst inv J e) = pc inv.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma spec_nil : forall argv fs, Spec.spec argv fs [].
Proof. intros argv fs. apply (proj1 (canon_spec_eq argv fs [])). apply canonT_nil. Qed.

Section Top.
  (* [comment removed for export] *)
  Hypothesis HS2_ok : hs_all_ok (inst A_HSm V_F (ELit 0)) = true.
  Hypothesis HS3_ok : hs_all_ok (inst A_HSm V_F (ELit 1)) = true.
  (* [comment removed for export] *)
  Hypothesis HF : fact_ok (kn A_HSm) (KRange (EVar V_F) 0 (0 + 1)) = true.
  Hypothesis Hlog : s_log (a_ss A_HSm) = [].
  (* [comment removed for export] *)
  Hypothesis MAIN : forall argv fs, valid_argv argv ->
    forall c, START RTA OUT_repA ERR_repA XENVA LIB_A argv fs c -> realizes asegs c (canonT (argv_Z argv) fs).

  (* [comment removed for export] *)
  Lemma topA_hole_lit : forall ch, hs_all_ok ch = true ->
    forall (sp : word) (rdraw : EntryDraw) (brk0 mbase : word) (inp : ProcInput),
    valid_sp sp -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_launch inp ->
    entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) inp ->
    forall E R FULL model,
      APS.cs_ok A_SEGS A_T AsanInit.LIMIT (SINV0 A_PH Asan.M.init_pc sp rdraw brk0 mbase inp) (argH0 sp rdraw inp) (bv_unsigned sp)
                (in_fs inp) E ch R FULL model ->
      srealizes A_SEGS (APS.cfg_of A_SEGS R (pc ch) FULL model) (Spec.spec (in_argv inp) (m_fs model)).
  Proof using MAIN.
    intros ch HT sp rdraw brk0 mbase inp Hsp Hva Hve Hlaunch Hlau E R FULL model HC.
    set (argv := in_argv inp) in *. set (fs := in_fs inp) in *.
    unfold hs_all_ok in HT.
    apply andb_prop in HT as [HT HTL]. apply andb_prop in HT as [HT HTR]. apply andb_prop in HT as [Hpc HTS].
    apply Z.eqb_eq in Hpc. rewrite Hpc. rewrite (APS.co_fs _ _ _ _ _ _ _ _ _ _ _ _ HC).
    assert (AHH : forall E (a : word), argH0 sp rdraw inp E a = true -> CEIL <= bv_unsigned a /\ bv_unsigned sp <= bv_unsigned a)
      by (intros E1 a H; eapply argH0_high; try eassumption;
          first [exact A_SEGS | exact A_T | exact A_PH | exact Asan.M.init_pc | exact AsanInit.LIMIT]).
    pose proof (hs_lib A_T AsanInit.LIMIT _ _ _ fs A_t_in_hull A_t_hull_ok AHH E ch R FULL model HC HTL) as HLB.
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
  Proof using HS2_ok HS3_ok HF Hlog MAIN.
    intros sp rdraw brk0 mbase inp Hsp Hva Hve Hlaunch Hlau h ch Hh E R FULL model HC.
    unfold HS_one in Hh. destruct (Nat.eqb h 0); [|discriminate Hh]. injection Hh as <-. cbv beta.
    destruct (cs_ok_split2 A_SEGS A_T AsanInit.LIMIT _ _ _ (in_fs inp) A_HSm V_F 0 HF Hlog E R FULL model HC) as [H2|H3].
    - rewrite <- (pc_inst A_HSm V_F (ELit 0)).
      exact (topA_hole_lit _ HS2_ok sp rdraw brk0 mbase inp Hsp Hva Hve Hlaunch Hlau E R FULL model H2).
    - rewrite <- (pc_inst A_HSm V_F (ELit (0 + 1))).
      exact (topA_hole_lit _ HS3_ok sp rdraw brk0 mbase inp Hsp Hva Hve Hlaunch Hlau E R FULL model H3).
  Qed.

  (* [comment removed for export] *)
  Theorem topA_realizes :
    image_realizes Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs target_alloc_limit Spec.spec.
  Proof using HS2_ok HS3_ok HF Hlog MAIN.
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
