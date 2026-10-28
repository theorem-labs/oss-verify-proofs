(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run Fs StackLayout.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import MState Mem Frame Cells Step Arr Exec ImageA RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Spec Require Import Prelim Canon Stdio.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout RT_iface D_iface D_defs I_iodefs X_xdefs.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require Import PropExec ShapeAlg SpinAlg AsanAcct AxSymExec3 AxSymExec3Sound AsanPlanCore AsanPlan AsanPlanSound AsanInit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import HandoffKit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import HandoffStart HandoffImage HandoffArgv HandoffCLX HandoffA RT_state RT_rep RT_init RT_init_mem HandoffG1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP.
Open Scope Z_scope.

Local Instance hrt_fx : PropExec.FPState := PropExec.fx0.

#[local] Existing Instance OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A.Shadow.GWf.
Section StartRT.
Variables (A : atable) (nx0 : nat) (LIMIT : Z) (fs : Fs).
Variables (ph : PhdrInfo) (sp : word) (rdraw : EntryDraw) (brk0 : word) (argv envp : list (list byte)) (uid hw : word).
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv argv.
Hypothesis Hve : valid_envp envp.
Hypothesis Hfit : entry_stack_fits sp argv envp.
Hypothesis SEGS_in_hull : forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment bsegs (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : APS.hull_ok A.
Hypothesis Hsegtop : img_hi A = SEGTOP_A.
Hypothesis Hshoff : shadow_off A = SHB.
Hypothesis Hlim : LIMIT = VMLIMIT.

#[local] Notation SINV := (SINV0 ph sp rdraw brk0 argv envp uid hw).
#[local] Notation argH := (argH0 ph sp rdraw argv envp uid hw).

Variables (E : env) (ch : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis HC : APS.cs_ok bsegs A nx0 LIMIT SINV argH fs E ch R FULL model.
Hypothesis HT : hs_start_ok ch = true.
Hypothesis HTR : hs_rt_ok A ch = true.

Hypothesis HG1 : hs_g1_ok ch = true.

Variable LIB : mem -> Prop.
#[local] Notation Σ0 := (sigma0 A E ch model).
Hypothesis HLIB : LIB (mH FULL model (rtA_allow Σ0)).

Theorem hs_start_rt : START RTA OUT_repA ERR_repA XENVA LIB argv fs (canon_cfg bsegs R a_main FULL model).
Proof.
  pose proof (hsa_argH_high ph sp rdraw argv envp uid hw Hsp Hva) as AH.
  pose proof HG1 as HG1'. unfold hs_g1_ok in HG1'. apply andb_prop in HG1' as [G1S G1D].
  pose proof (ri_HA' A E ch model) as HALLOW.
  assert (HSTKWIN : forall top, top mod 4096 = 0 -> top < bv_unsigned (vm_init_sp (m_vmmaps model)) - 0xa0 + 4096 ->
            stk bsegs (mH FULL model (rtA_allow (sigma0 A E ch model))) (bv_unsigned (vm_init_sp (m_vmmaps model)) - 0x800000) top).
  { intros top Ht1 Ht2. rewrite (hsa_sp0 A nx0 LIMIT fs ph sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit E ch R FULL model HC) in Ht2 |- *.
    exact (hg_stkwin A nx0 LIMIT fs ph sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit SEGS_in_hull HULL_ok E ch R FULL model HC _ HALLOW G1S top Ht1 Ht2). }
  pose proof (hg_depz A nx0 LIMIT SINV argH fs SEGS_in_hull HULL_ok AH E ch R FULL model HC _ HALLOW G1D) as HDEPZ.
  destruct (rt_init_glue A nx0 LIMIT SINV argH fs SEGS_in_hull HULL_ok AH Hsegtop Hshoff Hlim E ch R FULL model HC HTR HSTKWIN HDEPZ)
    as (Hallow & Hawf & Hminv & Hartm & Hsp0 & Hart & Hsig).
  pose proof (hsa_sp0 A nx0 LIMIT fs ph sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit E ch R FULL model HC) as Husp.
  rewrite Husp in Hsp0, Hsig.
  exact (hs_start A nx0 LIMIT fs ph sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit SEGS_in_hull HULL_ok Hsegtop E ch R FULL model HC HT
           RTA LIB Σ0 Hallow Hawf Hminv Hartm Hsp0 Hart Hsig HLIB).
Qed.

Theorem hs_hole_rt : forall T,
  (forall c, START RTA OUT_repA ERR_repA XENVA LIB argv fs c -> realizes bsegs c T) ->
  srealizes bsegs (APS.cfg_of bsegs R a_main FULL model) T.
Proof.
  intros T Hmain. unfold APS.cfg_of. apply hole_of_canon. apply Hmain. exact hs_start_rt.
Qed.

End StartRT.
