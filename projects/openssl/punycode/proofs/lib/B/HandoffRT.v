(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch is the run's whole ProcInput, with the mmap base and the image entry; the hand-off lemmas are applied by unification; argH0_high's unread Section variables are supplied from this Section). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run Fs StackLayout.
From OSSVerify.Proofs.openssl.punycode.lib.Lib Require Import MState Mem Frame Cells Step Arr Exec ImageA RzCPS.
From OSSVerify.Proofs.openssl.punycode.lib.Spec Require Import Prelim Canon Stdio.
From OSSVerify.Proofs.openssl.punycode.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.punycode.lib.B Require Import Layout RT_iface D_iface D_defs I_iodefs X_xdefs.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import PropExec ShapeAlg SpinAlg AsanAcct AxSymExec3 AxSymExec3Sound AsanPlanCore AsanPlan AsanPlanSound AsanInit.
From OSSVerify.Proofs.openssl.punycode.lib.A Require Import HandoffKit.
From OSSVerify.Proofs.openssl.punycode.lib.B Require Import HandoffStart HandoffImage HandoffArgv HandoffCLX HandoffA RT_state RT_rep RT_init RT_init_mem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP.
Open Scope Z_scope.

Section StartRT.
Variables (A : atable) (LIMIT : Z) (fs : Fs).
Variables (ph : PhdrInfo) (apc : N) (sp : word) (rdraw : EntryDraw) (brk0 mbase : word) (inp : ProcInput).
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv (in_argv inp).
Hypothesis Hve : valid_envp (in_envp inp).
Hypothesis Hlaunch : valid_launch inp.
Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) inp.
Hypothesis SEGS_in_hull : forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment bsegs (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : APS.hull_ok A.
Hypothesis Hsegtop : img_hi A = SEGTOP_A.
Hypothesis Hseglo : img_lo A = SEGLO.
Hypothesis Hshoff : shadow_off A = SHB.
Hypothesis Hlim : LIMIT = VMLIMIT.

#[local] Notation SINV := (SINV0 ph apc sp rdraw brk0 mbase inp).
#[local] Notation argH := (argH0 sp rdraw inp).
#[local] Notation argv := (in_argv inp).
#[local] Notation usp := (bv_unsigned sp).

Variables (E : env) (ch : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis HC : APS.cs_ok bsegs A LIMIT SINV argH usp fs E ch R FULL model.
Hypothesis HT : hs_start_ok ch = true.
Hypothesis HTR : hs_rt_ok A ch = true.

Variable LIB : mem -> Prop.
#[local] Notation Σ0 := (sigma0 A E ch model).
Hypothesis HLIB : LIB (mH FULL model (rtA_allow Σ0)).

Theorem hs_start_rt : START RTA OUT_repA ERR_repA XENVA LIB argv fs (canon_cfg bsegs R a_main FULL model).
Proof.
  assert (AH : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a /\ bv_unsigned sp <= bv_unsigned a)
    by (intros E1 a H; eapply argH0_high; try eassumption;
        first [exact bsegs | exact A | exact ph | exact apc | exact LIMIT]).
  destruct (rt_init_glue A LIMIT SINV argH usp fs SEGS_in_hull HULL_ok AH Hsegtop Hshoff Hlim E ch R FULL model HC HTR (hsa_isp sp Hsp)
              ltac:(intros E1 M1 HS1; eapply SINV0_pgsp; eassumption))
    as (Hallow & Hawf & Hminv & Hartm & Hsp0 & Hart & Hsig).
  assert (Husp : bv_unsigned (vm_init_sp (m_vmmaps model)) = bv_unsigned sp) by (eapply hsa_sp0; eassumption).
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
