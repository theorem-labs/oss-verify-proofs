(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run Fs StackLayout.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import MState Mem Frame Cells Step Arr Exec ImageA RzCPS.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim Canon Stdio.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_iface D_defs I_iodefs X_xdefs.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import PropExec ShapeAlg SpinAlg AsanAcct AxSymExec3 AxSymExec3Sound AsanPlanCore AsanPlan AsanPlanSound AsanInit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import HandoffKit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import HandoffStart HandoffImage HandoffArgv HandoffCLX HandoffA RT_state RT_rep RT_census RT_init RT_init_mem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Start Require AsanRegModel AsanGshModel A_RegConsts A_Gsh.      (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP.
Open Scope Z_scope.

(* [comment removed for export] *)
#[local] Existing Instance A_Gsh.A_BLOBS.

Lemma SINV0_blob : forall (ph : PhdrInfo) (sp : word) (rdraw : EntryDraw) (brk0 : word) (argv envp : list (list byte)) (uid hw : word) E0 M0,
  SINV0 ph sp rdraw brk0 argv envp uid hw E0 M0 ->
  forall j lo hi, nth_error A_Gsh.A_HULLS j = Some (lo, hi) ->
  eb E0 (K_GSH0 + j)%nat = map (Z_to_bv 8) (AsanGshModel.GSM.gsh_list (AsanRegModel.RGM.c_lay A_RegConsts.A_RGC) A_Gsh.A_GTAB lo hi).
Proof.
  intros ph sp rdraw brk0 argv envp uid hw E0 M0 [_ [_ HB]] j lo hi Hn. rewrite HB. unfold AsanInit.E0. cbn [eb].
  destruct (Nat.eqb_spec (K_GSH0 + j) K_RND) as [X|_]; [exfalso; unfold K_GSH0, K_RND in X; lia|].
  exact (A_Gsh.A_BLOBS_hull j lo hi Hn).
Qed.

Section StartRT.
Variables (A : atable) (LIMIT : Z) (fs : Fs).
Variables (ph : PhdrInfo) (sp : word) (rdraw : EntryDraw) (brk0 : word) (argv envp : list (list byte)) (uid hw : word).
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv argv.
Hypothesis Hve : valid_envp envp.
Hypothesis Hfit : entry_stack_fits sp argv envp.
Hypothesis SEGS_in_hull : forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment asegs (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : APS.hull_ok A.
Hypothesis Hsegtop : img_hi A = SEGTOP_A.
Hypothesis Hseglo : img_lo A = SEGLO.
Hypothesis Hshoff : shadow_off A = SHB.
Hypothesis Hlim : LIMIT = VMLIMIT.

#[local] Notation SINV := (SINV0 ph sp rdraw brk0 argv envp uid hw).
#[local] Notation argH := (argH0 ph sp rdraw argv envp uid hw).
#[local] Notation usp := (bv_unsigned sp).

Variables (E : env) (ch : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis HC : APS.cs_ok asegs A LIMIT SINV argH usp fs E ch R FULL model.
Hypothesis HT : hs_start_ok ch = true.
Hypothesis HTR : hs_rt_ok A ch = true.

Variable LIB : mem -> Prop.
#[local] Notation Σ0 := (sigma0 A E ch model).
Hypothesis HLIB : LIB (mH FULL model (rtA_allow Σ0)).

Theorem hs_start_rt : START RTA OUT_repA ERR_repA (XENVA false) LIB CENSUS argv fs (canon_cfg asegs R a_main FULL model).
Proof.
  pose proof (hsa_argH_high ph sp rdraw argv envp uid hw Hsp Hva) as AH.
  destruct (rt_init_glue A LIMIT SINV argH usp fs SEGS_in_hull HULL_ok AH Hsegtop Hshoff Hlim E ch R FULL model HC HTR (hsa_isp sp Hsp)
              (SINV0_pgsp ph sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit)
              (SINV0_blob ph sp rdraw brk0 argv envp uid hw))
    as (Hallow & Hawf & Hminv & Hartm & Hsp0 & Hart & Hsig).
  pose proof (hsa_sp0 A LIMIT fs ph sp rdraw brk0 argv envp uid hw E ch R FULL model HC) as Husp.
  rewrite Husp in Hsp0, Hsig.
  exact (hs_start A LIMIT fs ph sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit SEGS_in_hull HULL_ok Hsegtop Hseglo E ch R FULL model HC HT
           RTA LIB Σ0 CENSUS Hallow Hawf Hminv Hartm Hsp0 Hart Hsig HLIB).
Qed.

(* [comment removed for export] *)
Theorem hs_hole_rt : forall T,
  (forall c, START RTA OUT_repA ERR_repA (XENVA false) LIB CENSUS argv fs c -> realizes asegs c T) ->
  srealizes asegs (APS.cfg_of asegs R a_main FULL model) T.
Proof.
  intros T Hmain. unfold APS.cfg_of. apply hole_of_canon. apply Hmain. exact hs_start_rt.
Qed.

End StartRT.
