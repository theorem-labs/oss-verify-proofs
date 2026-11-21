(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the hand-off over the launch input ProcInput and the CONFIG_RSEQ flag). *)
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Monad Specs Run Fs StackLayout.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require MState Mem Frame Cells Step Arr Exec ImageA RzCPS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Spec Require Prelim Canon Stdio.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Layout RT_iface D_iface D_defs I_iodefs X_xdefs.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require PropExec ShapeAlg SpinAlg AsanAcct AxSymExec3 AxSymExec3Sound AsanPlanCore AsanPlan AsanPlanSound AsanInit.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require HandoffKit.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require HandoffStart HandoffImage HandoffArgv HandoffCLX HandoffA RT_state RT_rep RT_init RT_init_mem.
Module TwinB__.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run Fs StackLayout.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import MState Mem Frame Cells Step Arr Exec ImageA RzCPS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Spec Require Import Prelim Canon Stdio.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Shadow.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.Layout.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_iface.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_iface.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.I_iodefs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.X_xdefs.TwinB__.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import PropExec ShapeAlg SpinAlg AsanAcct AxSymExec3 AxSymExec3Sound AsanPlanCore AsanPlan AsanPlanSound AsanInit.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import HandoffKit.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.HandoffStart.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.HandoffImage.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.HandoffArgv.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.HandoffCLX.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.HandoffA.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_state.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_rep.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_init.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_init_mem.TwinB__.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP.
Open Scope Z_scope.

Local Instance hrt_fx : PropExec.FPState := PropExec.fx0.

Section StartRT.
Variables (A : atable) (nx0 : nat) (LIMIT : Z) (fs : Fs).
Variables (ph : PhdrInfo) (apc : N) (sp : word) (rdraw : EntryDraw) (brk0 mbase : word) (inp : ProcInput).
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv (in_argv inp).
Hypothesis Hve : valid_envp (in_envp inp).
Hypothesis Hlaunch : valid_launch inp.
Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) inp.
Hypothesis SEGS_in_hull : forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment bsegs (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : APS.hull_ok A.
Hypothesis Hsegtop : img_hi A = SEGTOP_A.
Hypothesis Hshoff : shadow_off A = SHB.
Hypothesis Hlim : LIMIT = VMLIMIT.

#[local] Notation SINV := (SINV0 ph apc sp rdraw brk0 mbase inp).
#[local] Notation argH := (argH0 sp rdraw inp).
#[local] Notation argv := (in_argv inp).
#[local] Notation RZ := (rseq_z (kb_rseq (in_kernel inp))).

Variables (E : env) (ch : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis HC : APS.cs_ok bsegs A nx0 LIMIT SINV argH fs E ch R FULL model.
Hypothesis HT : hs_start_ok RZ ch = true.
Hypothesis HTR : hs_rt_ok A ch = true.

Variable LIB : mem -> Prop.
#[local] Notation Σ0 := (sigma0 A E ch model).
Hypothesis HLIB : LIB (mH FULL model (rtA_allow Σ0)).

Theorem hs_start_rt : START RTA OUT_repA ERR_repA XENVA LIB argv fs (canon_cfg bsegs R a_main FULL model).
Proof.
  pose proof (argH0_high apc sp rdraw inp Hsp Hva) as AH.
  destruct (rt_init_glue A nx0 LIMIT SINV argH fs SEGS_in_hull HULL_ok AH Hsegtop Hshoff Hlim E ch R FULL model HC HTR)
    as (Hallow & Hawf & Hminv & Hartm & Hsp0 & Hart & Hsig).
  assert (Husp : bv_unsigned (vm_init_sp (m_vmmaps model)) = bv_unsigned sp).
  { destruct (APS.cs_isp _ _ _ _ _ _ _ _ _ _ _ _ HC) as [I1 _]. rewrite I1.
    exact (SINV0_sp ph apc sp rdraw brk0 mbase inp Hsp Hva Hve Hlau E FULL (APS.co_sinv _ _ _ _ _ _ _ _ _ _ _ _ HC)). }
  rewrite Husp in Hsp0, Hsig.
  eapply hs_start; eassumption.
Qed.

(* [comment removed for export] *)
Theorem hs_hole_rt : forall T,
  (forall c, START RTA OUT_repA ERR_repA XENVA LIB argv fs c -> realizes bsegs c T) ->
  srealizes bsegs (APS.cfg_of bsegs R a_main FULL model) T.
Proof.
  intros T Hmain. unfold APS.cfg_of. apply hole_of_canon. apply Hmain. exact hs_start_rt.
Qed.

End StartRT.
End TwinB__.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run Fs StackLayout.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import MState Mem Frame Cells Step Arr Exec ImageA RzCPS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Spec Require Import Prelim Canon Stdio.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Layout Shadow RT_iface D_iface D_defs I_iodefs X_xdefs.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import PropExec ShapeAlg SpinAlg AsanAcct AxSymExec3 AxSymExec3Sound AsanPlanCore AsanPlan AsanPlanSound AsanInit.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import HandoffKit HandoffStart HandoffImage HandoffArgv HandoffCLX HandoffA
  RT_state RT_rep RT_init RT_init_mem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP.
Open Scope Z_scope.

Local Instance hrt_fx : PropExec.FPState := PropExec.fx0.

Section StartRT.
Variables (A : atable) (nx0 : nat) (LIMIT : Z) (fs : Fs).
Variables (ph : PhdrInfo) (apc : N) (sp : word) (rdraw : EntryDraw) (brk0 mbase : word) (inp : ProcInput).
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv (in_argv inp).
Hypothesis Hve : valid_envp (in_envp inp).
Hypothesis Hlaunch : valid_launch inp.
Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) inp.
Hypothesis SEGS_in_hull : forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment asegs (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : APS.hull_ok A.
Hypothesis Hsegtop : img_hi A = SEGTOP_A.
Hypothesis Hshoff : shadow_off A = SHB.
Hypothesis Hlim : LIMIT = VMLIMIT.

#[local] Notation SINV := (SINV0 ph apc sp rdraw brk0 mbase inp).
#[local] Notation argH := (argH0 sp rdraw inp).
#[local] Notation argv := (in_argv inp).
#[local] Notation RZ := (rseq_z (kb_rseq (in_kernel inp))).

Variables (E : env) (ch : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis HC : APS.cs_ok asegs A nx0 LIMIT SINV argH fs E ch R FULL model.
Hypothesis HT : hs_start_ok RZ ch = true.
Hypothesis HTR : hs_rt_ok A ch = true.

Variable LIB : mem -> Prop.
#[local] Notation Σ0 := (sigma0 A E ch model).
Hypothesis HLIB : LIB (mH FULL model (rtA_allow Σ0)).

Theorem hs_start_rt : START RTA OUT_repA ERR_repA XENVA LIB argv fs (canon_cfg asegs R a_main FULL model).
Proof.
  pose proof (argH0_high apc sp rdraw inp Hsp Hva) as AH.
  destruct (rt_init_glue A nx0 LIMIT SINV argH fs SEGS_in_hull HULL_ok AH Hsegtop Hshoff Hlim E ch R FULL model HC HTR)
    as (Hallow & Hawf & Hminv & Hartm & Hsp0 & Hart & Hsig).
  assert (Husp : bv_unsigned (vm_init_sp (m_vmmaps model)) = bv_unsigned sp).
  { destruct (APS.cs_isp _ _ _ _ _ _ _ _ _ _ _ _ HC) as [I1 _]. rewrite I1.
    exact (SINV0_sp ph apc sp rdraw brk0 mbase inp Hsp Hva Hve Hlau E FULL (APS.co_sinv _ _ _ _ _ _ _ _ _ _ _ _ HC)). }
  rewrite Husp in Hsp0, Hsig.
  eapply hs_start; eassumption.
Qed.

(* [comment removed for export] *)
Theorem hs_hole_rt : forall T,
  (forall c, START RTA OUT_repA ERR_repA XENVA LIB argv fs c -> realizes asegs c T) ->
  srealizes asegs (APS.cfg_of asegs R a_main FULL model) T.
Proof.
  intros T Hmain. unfold APS.cfg_of. apply hole_of_canon. apply Hmain. exact hs_start_rt.
Qed.

End StartRT.
