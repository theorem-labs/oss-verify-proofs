(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.openssl.punycode.images Require Import AsanUbsan.
From OSSVerify.Proofs.openssl.punycode.lib.Lib Require Import MState Mem Frame Cells Step Arr Exec ImageA RzCPS.
From OSSVerify.Proofs.openssl.punycode.lib.Spec Require Import Prelim Canon Stdio Prog CanonSpec.
From OSSVerify.Proofs.openssl.punycode.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.punycode.lib.B Require Import Layout RT_iface D_iface D_defs I_iodefs X_xdefs Fz_defs.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import PropExec ShapeAlg SpinAlg AsanAcct AxSymExec3 AxSymExec3Sound
  AsanPlanCore AsanPlan AsanPlanSound AsanInit.
From OSSVerify.Proofs.openssl.punycode.lib.Start Require Import AsanChain B_PlanImage B_Atable B_Chain.
From OSSVerify.Proofs.openssl.punycode.lib.A Require Import HandoffKit HandoffSplit.
From OSSVerify.Proofs.openssl.punycode.lib.B Require Import HandoffStart HandoffImage HandoffArgv HandoffCLX HandoffA RT_state RT_rep RT_init RT_init_mem HandoffRT HandoffLIB.
From OSSVerify.Proofs.openssl.punycode.lib Require Import ClaVerdict Spec.
From OSSVerify.Proofs.openssl.punycode.lib.Top Require Import TopBridge.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition hs_all_ok (ch : acs) : bool :=
  (Z.eqb (pc ch) a_main && hs_start_ok ch && hs_rt_ok B_T ch && hs_lib_ok ch)%bool.

(* [comment removed for export] *)
Lemma B_t_segtop : img_hi B_T = SEGTOP_A. Proof. reflexivity. Qed.
Lemma B_t_seglo : img_lo B_T = SEGLO. Proof. reflexivity. Qed.
Lemma B_t_shoff : shadow_off B_T = SHB. Proof. reflexivity. Qed.
Lemma A_lim : AsanInit.LIMIT = VMLIMIT. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition V_F : nat := 45.

Lemma pc_inst : forall inv J e, pc (inst inv J e) = pc inv.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma spec_nil : forall argv fs, Spec.spec argv fs [].
Proof. intros argv fs. apply (proj1 (canon_spec_eq argv fs [])). apply canonT_nil. Qed.

Section Top.
  (* [comment removed for export] *)
  Hypothesis HS2_ok : hs_all_ok (inst B_HSm V_F (ELit 2)) = true.
  Hypothesis HS3_ok : hs_all_ok (inst B_HSm V_F (ELit 3)) = true.
  (* [comment removed for export] *)
  Hypothesis HF : fact_ok (kn B_HSm) (KRange (EVar V_F) 2 (2 + 1)) = true.
  Hypothesis Hlog : s_log (a_ss B_HSm) = [].
  (* [comment removed for export] *)
  Hypothesis MAIN : forall argv fs, valid_argv argv ->
    forall c, START RTA OUT_repA ERR_repA XENVA LIB_A argv fs c -> realizes bsegs c (canonT (argv_Z argv) fs).

  (* [comment removed for export] *)
  Lemma topA_hole_lit : forall ch, hs_all_ok ch = true ->
    forall (sp : word) (rdraw : EntryDraw) (brk0 : word) (argv envp : list (list byte)) (uid hw : word) (fs : Fs.Fs),
    valid_sp sp -> valid_argv argv -> valid_envp envp -> entry_stack_fits sp argv envp ->
    forall E R FULL model,
      APS.cs_ok B_SEGS B_T AsanInit.LIMIT (SINV0 B_PH sp rdraw brk0 argv envp uid hw) (argH0 B_PH sp rdraw argv envp uid hw) (bv_unsigned sp)
                fs E ch R FULL model ->
      srealizes B_SEGS (APS.cfg_of B_SEGS R (pc ch) FULL model) (Spec.spec argv (m_fs model)).
  Proof using MAIN.
    intros ch HT sp rdraw brk0 argv envp uid hw fs Hsp Hva Hve Hfit E R FULL model HC.
    unfold hs_all_ok in HT.
    apply andb_prop in HT as [HT HTL]. apply andb_prop in HT as [HT HTR]. apply andb_prop in HT as [Hpc HTS].
    apply Z.eqb_eq in Hpc. rewrite Hpc. rewrite (APS.co_fs _ _ _ _ _ _ _ _ _ _ _ _ HC).
    apply (hs_hole_rt B_T AsanInit.LIMIT fs B_PH sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit B_t_in_hull B_t_hull_ok
             B_t_segtop B_t_seglo B_t_shoff A_lim E ch R FULL model HC HTS HTR LIB_A
             (hs_lib B_T AsanInit.LIMIT _ _ _ fs B_t_in_hull B_t_hull_ok (hsa_argH_high B_PH sp rdraw argv envp uid hw Hsp Hva)
                E ch R FULL model HC HTL)).
    intros c HS. apply (rz_conseq bsegs c _ _ (MAIN argv fs Hva c HS)). exact (canon_spec_eq argv fs).
  Qed.

  (* [comment removed for export] *)
  Lemma topA_holes : forall (sp : word) (rdraw : EntryDraw) (brk0 : word) (argv envp : list (list byte)) (uid hw : word) (fs : Fs.Fs),
    valid_sp sp -> valid_argv argv -> valid_envp envp -> entry_stack_fits sp argv envp ->
    APS.holes_stmt B_SEGS B_T AsanInit.LIMIT (HS_one B_HSm) (SINV0 B_PH sp rdraw brk0 argv envp uid hw) (argH0 B_PH sp rdraw argv envp uid hw)
                   (bv_unsigned sp) (fun _ _ fs' => Spec.spec argv fs') fs.
  Proof using HS2_ok HS3_ok HF Hlog MAIN.
    intros sp rdraw brk0 argv envp uid hw fs Hsp Hva Hve Hfit h ch Hh E R FULL model HC.
    unfold HS_one in Hh. destruct (Nat.eqb h 0); [|discriminate Hh]. injection Hh as <-. cbv beta.
    destruct (cs_ok_split2 B_SEGS B_T AsanInit.LIMIT _ _ _ fs B_HSm V_F 2 HF Hlog E R FULL model HC) as [H2|H3].
    - rewrite <- (pc_inst B_HSm V_F (ELit 2)).
      exact (topA_hole_lit _ HS2_ok sp rdraw brk0 argv envp uid hw fs Hsp Hva Hve Hfit E R FULL model H2).
    - rewrite <- (pc_inst B_HSm V_F (ELit (2 + 1))).
      exact (topA_hole_lit _ HS3_ok sp rdraw brk0 argv envp uid hw fs Hsp Hva Hve Hfit E R FULL model H3).
  Qed.

  (* [comment removed for export] *)
  Theorem topA_realizes :
    image_realizes AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs target_alloc_limit Spec.spec.
  Proof using HS2_ok HS3_ok HF Hlog MAIN.
    (* [comment removed for export] *)
    intros sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask urnd Hsp Hbrk Hmb Hva Hve Hfit Huid _ _.
    exact (B_startup_main sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask urnd Hsp Hbrk Hmb Hva Hve Hfit Huid
             (fun _ _ fs' => Spec.spec argv fs') (fun _ _ _ _ _ => eq_refl) (fun _ _ fs' => spec_nil argv fs')
             (topA_holes sp rdraw brk0 argv envp uid hw fs Hsp Hva Hve Hfit)).
  Qed.
End Top.
