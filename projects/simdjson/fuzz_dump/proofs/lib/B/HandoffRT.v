(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: the hand-off to the main phase takes the run's whole launch input and reads its CONFIG_RSEQ flag off the kernel build, the start's stack window is the 0x5D0000-byte span the start state guarantees below sp instead of 8 MiB, and the table's bounds on the vDSO tail of the reserved list are premises; taken in part from projects/simdjson/fuzz_ondemand/proofs/lib/B/HandoffRT.v, lines 24-29, 34-35, 42-53, 61-69, 74-78, 87-111. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run Fs StackLayout.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Lib Require Import MState Mem Frame Cells Step Arr Exec ImageA RzCPS.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Spec Require Import Prelim Canon Stdio.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout RT_iface D_iface D_defs I_iodefs X_xdefs.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.AS Require Import PropExec ShapeAlg SpinAlg AsanAcct AxSymExec3 AxSymExec3Sound AsanPlanCore AsanPlan AsanPlanSound AsanInit.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.A Require Import HandoffKit.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.B Require Import HandoffStart HandoffImage HandoffArgv HandoffCLX HandoffA RT_state RT_rep RT_init RT_init_mem HandoffG1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP.
Open Scope Z_scope.

Local Instance hrt_fx : PropExec.FPState := PropExec.fx0.

#[local] Existing Instance OSSVerify.Proofs.simdjson.fuzz_dump.lib.A.Shadow.GWf.
Section StartRT.
Variables (A : atable) (nx0 : nat) (LIMIT : Z) (fs : Fs).
(* LPS 727298f3: the launch, as AS/AsanInit.v's Section Init names it: the run's
   whole input [inp]; [fs] is the checker's filesystem (A/HandoffA.v takes the
   launch the same way). *)
Variables (ph : PhdrInfo) (sp : word) (rdraw : EntryDraw) (brk0 mbase : word) (inp : ProcInput).
#[local] Notation argv := (in_argv inp).
#[local] Notation envp := (in_envp inp).
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv argv.
Hypothesis Hve : valid_envp envp.
Hypothesis Hfit : entry_stack_fits sp argv envp.
Hypothesis Hlaunch : valid_launch inp.
Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) inp.
Hypothesis SEGS_in_hull : forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment bsegs (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : APS.hull_ok A.
Hypothesis Hsegtop : img_hi A = SEGTOP_A.
Hypothesis Hshoff : shadow_off A = SHB.
Hypothesis Hnresx : (AsanPlanCore.APC.n_resx A <= 2)%nat.
Hypothesis Hresxb : AsanPlanCore.APC.resx_bytes A <= 81920.
Hypothesis Hlim : LIMIT = VMLIMIT.

#[local] Notation SINV := (SINV0 A ph sp rdraw brk0 mbase inp).
#[local] Notation argH := (argH0 sp rdraw inp).

Variables (E : env) (ch : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis HC : APS.cs_ok bsegs A nx0 LIMIT SINV argH fs E ch R FULL model.
(* the launch's CONFIG_RSEQ flag, read off the kernel build: never pinned; the
   hand-off checks [hs_start_ok] and [hs_g1_ok] are read at it *)
#[local] Notation RZ := (rseq_z (kb_rseq (in_kernel inp))).
Hypothesis HT : hs_start_ok RZ ch = true.
Hypothesis HTR : hs_rt_ok A ch = true.

Hypothesis HG1 : hs_g1_ok RZ ch = true.

Variable LIB : mem -> Prop.
#[local] Notation Σ0 := (sigma0 A E ch model).
Hypothesis HLIB : LIB (mH FULL model (rtA_allow Σ0)).

Theorem hs_start_rt : START RTA OUT_repA ERR_repA XENVA LIB argv fs (canon_cfg bsegs R a_main FULL model).
Proof.
  assert (AH : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a) by (intros E1 a H; eapply argH0_high; eassumption).
  pose proof HG1 as HG1'. unfold hs_g1_ok in HG1'. apply andb_prop in HG1' as [G1S G1D].
  pose proof (ri_HA' A E ch model) as HALLOW.
  assert (Husp : bv_unsigned (vm_init_sp (m_vmmaps model)) = bv_unsigned sp) by (eapply hsa_sp0; eassumption).
  (* LPS 727298f3: the window starts [STACK_SPAN] below sp (A/HandoffG1.v [hg_stkwin]) *)
  assert (HSTKWIN : forall top, top mod 4096 = 0 -> top < bv_unsigned (vm_init_sp (m_vmmaps model)) - 0xa0 + 4096 ->
            stk bsegs (mH FULL model (rtA_allow (sigma0 A E ch model))) (bv_unsigned (vm_init_sp (m_vmmaps model)) - STACK_SPAN) top).
  { intros top Ht1 Ht2. rewrite Husp in Ht2 |- *. rewrite STACK_SPAN_val.
    eapply hg_stkwin; first [exact G1S | exact Ht1 | exact Ht2 | exact HALLOW | eassumption]. }
  pose proof (hg_depz A nx0 LIMIT SINV argH fs SEGS_in_hull HULL_ok AH E ch R FULL model HC _ HALLOW G1D) as HDEPZ.
  destruct (rt_init_glue A nx0 LIMIT SINV argH fs SEGS_in_hull HULL_ok AH Hsegtop Hshoff Hnresx Hresxb Hlim E ch R FULL model HC HTR HSTKWIN HDEPZ)
    as (Hallow & Hawf & Hminv & Hartm & Hsp0 & Hart & Hsig).
  rewrite Husp in Hsp0, Hsig.
  eapply hs_start with (RT := RTA) (Σ := Σ0);
    first [exact HT | exact Hallow | exact Hawf | exact Hminv | exact Hartm | exact Hsp0 | exact Hart | exact Hsig | exact HLIB | eassumption].
Qed.

Theorem hs_hole_rt_s : forall T,
  (forall c, START RTA OUT_repA ERR_repA XENVA LIB argv fs c -> realizes bsegs c T) ->
  srealizes bsegs (APS.cfg_of bsegs R a_main FULL model) T.
Proof.
  intros T Hmain. unfold APS.cfg_of. apply hole_of_canon. apply Hmain. exact hs_start_rt.
Qed.

End StartRT.

(* The hand-off hole at LPS 727298f3, with every launch premise named so that a
   caller ([TopA_start.T_holes]) can apply it positionally: the section above
   discharges only the premises its proof happens to use. *)
Theorem hs_hole_rt : forall (A : atable) (nx0 : nat) (LIMIT : Z) (fs : Fs)
    (ph : PhdrInfo) (sp : word) (rdraw : EntryDraw) (brk0 mbase : word) (inp : ProcInput),
  valid_sp sp -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> entry_stack_fits sp (in_argv inp) (in_envp inp) ->
  valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) inp ->
  (forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment bsegs (bv_unsigned a) 1 = None) ->
  APS.hull_ok A -> img_hi A = SEGTOP_A -> shadow_off A = SHB -> LIMIT = VMLIMIT ->
  (AsanPlanCore.APC.n_resx A <= 2)%nat -> AsanPlanCore.APC.resx_bytes A <= 81920 ->
  forall (E : env) (ch : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model),
  APS.cs_ok bsegs A nx0 LIMIT (SINV0 A ph sp rdraw brk0 mbase inp) (argH0 sp rdraw inp) fs E ch R FULL model ->
  hs_start_ok (rseq_z (kb_rseq (in_kernel inp))) ch = true -> hs_rt_ok A ch = true ->
  hs_g1_ok (rseq_z (kb_rseq (in_kernel inp))) ch = true ->
  forall LIB : mem -> Prop, LIB (mH FULL model (rtA_allow (sigma0 A E ch model))) ->
  forall T, (forall c, START RTA OUT_repA ERR_repA XENVA LIB (in_argv inp) fs c -> realizes bsegs c T) ->
  srealizes bsegs (APS.cfg_of bsegs R a_main FULL model) T.
Proof. intros. eapply hs_hole_rt_s; eassumption. Qed.

(* [AsanInit.argH0_high] with the launch premises named, for [TopA_start.T_holes]'s
   callers ([cl_hs]'s [argH_high] slot). *)
Lemma hrt_argH_high : forall (sp : word) (rdraw : EntryDraw) (brk0 mbase : word) (inp : ProcInput),
  valid_sp sp -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> entry_stack_fits sp (in_argv inp) (in_envp inp) ->
  valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) inp ->
  forall (E : env) (a : word), argH0 sp rdraw inp E a = true -> CEIL <= bv_unsigned a.
Proof. intros. eapply argH0_high; eassumption. Qed.
