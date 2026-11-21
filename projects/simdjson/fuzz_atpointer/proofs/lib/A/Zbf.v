(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the stack floor raised to the 0x5D0000 bytes below sp that the launch guarantees ([STACK_GAP]); the launch stated over the run's whole input; the start-up per CONFIG_RSEQ value and the new auxv layout). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run Fs StackLayout.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import MState Mem Frame Cells Step Arr Exec ImageA RzCPS.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Spec Require Import Prelim Canon Stdio.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.A Require Import Layout Shadow Zks Z81 D_defs Zbv Z11v.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.AS Require Import Zg2 Zp7 Z10a Z1b Z78 Z7a Z2z Z2y Z33 Z1s.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.A Require Import Zbe Zbg Zbd Zba Zbb Zb9
  Zm2 RT_rep Zku Zkw Zbc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP.
Open Scope Z_scope.

Local Instance hrt_fx : Zg2.FPState := Zg2.fx0.

Section StartRT.
Variables (A : atable) (nx0 : nat) (LIMIT : Z) (fs : Fs).
(* LPS 727298f3: the launch, as AS/Z1s.v's Section Init names it: the run's whole input [inp] *)
Variables (ph : PhdrInfo) (sp : word) (rdraw : EntryDraw) (brk0 mbase : word) (inp : ProcInput).
#[local] Notation argv := (in_argv inp).
#[local] Notation envp := (in_envp inp).
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv argv.
Hypothesis Hve : valid_envp envp.
Hypothesis Hfit : entry_stack_fits sp argv envp.
Hypothesis Hlaunch : valid_launch inp.
Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) inp.
Hypothesis SEGS_in_hull : forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment asegs (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : APS.hull_ok A.
Hypothesis Hsegtop : img_hi A = SEGTOP_A.
Hypothesis Hshoff : shadow_off A = SHB.
Hypothesis Hlim : LIMIT = VMLIMIT.

#[local] Notation SINV := (SINV0 A ph sp rdraw brk0 mbase inp).
#[local] Notation argH := (argH0 sp rdraw inp).

Variables (E : env) (ch : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis HC : APS.cs_ok asegs A nx0 LIMIT SINV argH fs E ch R FULL model.
(* the launch's CONFIG_RSEQ flag, read off the kernel build: never pinned *)
#[local] Notation RZ := (rseq_z (kb_rseq (in_kernel inp))).
Hypothesis HT : hs_start_ok RZ ch = true.
Hypothesis HTR : hs_rt_ok A ch = true.

Hypothesis HG1 : hs_g1_ok RZ ch = true.

Variable LIB : mem -> Prop.
#[local] Notation Σ0 := (sigma0 A E ch model).
Hypothesis HLIB : LIB (mH FULL model (rtA_allow Σ0)).

Theorem hs_start_rt : START RTA OUT_repA ERR_repA XENVA LIB argv fs (canon_cfg asegs R a_main FULL model).
Proof.
  assert (AH : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a) by (intros E1 a H; eapply argH0_high; eassumption).
  pose proof HG1 as HG1'. unfold hs_g1_ok in HG1'. apply andb_prop in HG1' as [G1S G1D].
  pose proof (ri_HA' A E ch model) as HALLOW.
  assert (Husp : bv_unsigned (vm_init_sp (m_vmmaps model)) = bv_unsigned sp).
  { destruct (APS.cs_isp _ _ _ _ _ _ _ _ _ _ _ _ HC) as [I1 _]. rewrite I1.
    eapply SINV0_sp; first [exact (APS.co_sinv _ _ _ _ _ _ _ _ _ _ _ _ HC) | eassumption]. }
  (* the stack the hand-off state claims, [STACK_SPAN] below sp, in the runtime's floor form *)
  assert (HSTKWIN : forall top, top mod 4096 = 0 -> top < bv_unsigned (vm_init_sp (m_vmmaps model)) - 0xa0 + 4096 ->
            stk asegs (mH FULL model (rtA_allow (sigma0 A E ch model))) (bv_unsigned (vm_init_sp (m_vmmaps model)) - 0x800000 + STACK_GAP) top).
  { intros top Ht1 Ht2. rewrite Husp in Ht2 |- *.
    replace (bv_unsigned sp - 0x800000 + STACK_GAP) with (bv_unsigned sp - STACK_SPAN) by lia.
    eapply hg_stkwin with (A := A) (nx0 := nx0) (LIMIT := LIMIT) (FS0 := fs) (ph := ph) (sp := sp) (rdraw := rdraw)
      (brk0 := brk0) (mbase := mbase) (inp := inp) (E := E) (ch := ch) (R := R) (FULL := FULL) (model := model)
      (A' := rtA_allow (sigma0 A E ch model)); assumption. }
  pose proof (hg_depz A nx0 LIMIT SINV argH fs SEGS_in_hull HULL_ok AH E ch R FULL model HC _ HALLOW G1D) as HDEPZ.
  destruct (rt_init_glue A nx0 LIMIT SINV argH fs SEGS_in_hull HULL_ok AH Hsegtop Hshoff Hlim E ch R FULL model HC HTR HSTKWIN HDEPZ)
    as (Hallow & Hawf & Hminv & Hartm & Hsp0 & Hart & Hsig).
  rewrite Husp in Hsp0, Hsig.
  eapply hs_start with (A := A) (nx0 := nx0) (LIMIT := LIMIT) (fs := fs) (ph := ph) (sp := sp) (rdraw := rdraw)
    (brk0 := brk0) (mbase := mbase) (inp := inp) (E := E) (ch := ch) (R := R) (FULL := FULL) (model := model)
    (RT := RTA) (LIB := LIB) (Σ := Σ0); assumption.
Qed.

Theorem hs_hole_rt : forall T,
  (forall c, START RTA OUT_repA ERR_repA XENVA LIB argv fs c -> realizes asegs c T) ->
  srealizes asegs (APS.cfg_of asegs R a_main FULL model) T.
Proof.
  intros T Hmain. unfold APS.cfg_of. apply hole_of_canon. apply Hmain. exact hs_start_rt.
Qed.

End StartRT.
