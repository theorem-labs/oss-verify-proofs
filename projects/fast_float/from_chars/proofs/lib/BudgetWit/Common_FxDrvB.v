(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* Modified by Theorem Labs, 2026-11: made from Common/FxDrv.v: the R-typed declarations restated over the budget carrier, with twin modules imported last. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the model's fetch_failure cases). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec StoreOk ShapeSet RealizesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound FxMem FxRgs FxFacts FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxLoop FxPlan FxImg.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Sem Decode DecodeC.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import StoreOk FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxDrv.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxImg OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv.FxGrow.
Import ListNotations.
From OSSVerify.Proofs.fast_float.from_chars.lib.BudgetWit Require Import Rzb.

Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Open Scope Z_scope.
Section Drv.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
#[using="Type"] Lemma isteps_of_fx : forall ms ms', FxStep.isteps segs ms ms' -> RealizesCfg.isteps segs ms ms'.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros ms ms' H. induction H as [ms | ms ms1 ms2 Hsvc Hst _ IH];
    [apply RealizesCfg.ist_refl | eapply RealizesCfg.ist_step; eassumption].
Qed.
#[using="Type"] Lemma step_rom : forall ms ms', RiscvSemantics.step segs ms = MachineOk ms' -> ms_rom ms' = ms_rom ms.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros ms ms' H. unfold RiscvSemantics.step, RiscvSemantics.step_accesses in H.
  assert (Hd : forall w, drop_access_report (decode_exec_accesses segs ms w) = MachineOk ms' -> ms_rom ms' = ms_rom ms).
  { intros w Hw. unfold decode_exec_accesses in Hw. destruct (is_ecall w).
    - cbn in Hw. injection Hw as <-. reflexivity.
    - destruct (decode_any w) as [[i isz]|]; [|destruct (is_defined_illegal w); discriminate].
      destruct (interp_eff_accesses _ _) as [report| |]; try discriminate.
      destruct report as [[c m'] acc]. cbn in Hw. injection Hw as <-. reflexivity. }
  destruct (fetch_word segs (ms_pc ms)) as [w|]; [exact (Hd w H)|].
  destruct (fetch_word_ov segs (ms_mem ms) (ms_pc ms)) as [w|]; [exact (Hd w H)|].
  destruct (fetch_tail_any segs (ms_mem ms) (ms_pc ms)) as [w|]; [exact (Hd w H)|].
  unfold fetch_failure in H.
  repeat match type of H with context [if ?b then _ else _] => destruct b end; discriminate.
Qed.
#[using="Type"] Lemma fx_rom : forall ms ms', FxStep.isteps segs ms ms' -> ms_rom ms' = ms_rom ms.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros ms ms' H. induction H as [ms | ms ms1 ms2 Hsvc Hst _ IH]; [reflexivity|].
  rewrite IH. exact (step_rom _ _ Hst).
Qed.
#[using="Type"] Theorem rzb_fx_explore_frame : forall t img fuel stops (S : sst) (LEAVES : list sst) E ms model T,
  tbl_ok segs t -> img_ok segs img ->
  fx_explore t img fuel stops S [] = LEAVES ->
  sden segs E S ms -> bases_wf (s_next S) (s_rgs S) = true -> m_halted model = None -> m_vm_lazy model = [] ->
  (forall L E' ms', In L LEAVES -> sden segs E' L ms' -> agree (s_next S) E E' -> ms_rom ms' = ms_rom ms ->
      (forall x, outside E (s_rgs S) x -> ms_mem ms' x = ms_mem ms x) ->
      Rzb.rzb segs cfg (mkCfg ms' model) T) ->
  Rzb.rzb segs cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros t img fuel stops S LEAVES E ms model T Ht Himg HL Hden Hwf Hh Hl Hk.
  destruct (explore_frame segs t img fuel stops S [] E ms Ht Himg Hden Hwf) as (L & ms' & E' & HIn & Hst & Hd' & Ha & Hfr & _).
  rewrite HL in HIn.
  eapply Rzb.rzb_isteps; [exact Hh | exact Hl | apply isteps_of_fx; exact Hst |].
  apply (Hk L E' ms' HIn Hd' Ha (fx_rom _ _ Hst) Hfr).
Qed.
#[using="Type"] Theorem rzb_fx_seg : forall t img fuel stops (S : sst) (LEAVES : list sst) (P : sst) E0 mem0 E ms model T,
  tbl_ok segs t -> img_ok segs img ->
  fx_explore t img fuel stops S [] = LEAVES ->
  sden segs E S ms -> bases_wf (s_next S) (s_rgs S) = true ->
  shape (s_rgs S) = shape (s_rgs P) -> bases_wf (s_next P) (s_rgs P) = true -> agree (s_next P) E0 E ->
  (forall x, outside E0 (s_rgs P) x -> ms_mem ms x = mem0 x) ->
  m_halted model = None -> m_vm_lazy model = [] ->
  (forall L E' ms', In L LEAVES -> sden segs E' L ms' -> agree (s_next S) E E' -> ms_rom ms' = ms_rom ms ->
      (forall x, outside E0 (s_rgs P) x -> ms_mem ms' x = mem0 x) ->
      Rzb.rzb segs cfg (mkCfg ms' model) T) ->
  Rzb.rzb segs cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros t img fuel stops S LEAVES P E0 mem0 E ms model T Ht Himg HL Hden Hwf Hsh HwfP Ha0 Hmf Hh Hl Hk.
  apply (rzb_fx_explore_frame t img fuel stops S LEAVES E ms model T Ht Himg HL Hden Hwf Hh Hl).
  intros L E' ms' HIn Hd' Ha' Hrom Hfr. apply (Hk L E' ms' HIn Hd' Ha' Hrom).
  intros x Hx. rewrite Hfr; [exact (Hmf x Hx)|].
  apply (outside_shape E (s_rgs P) (s_rgs S) x Hsh). apply (outside_agree (s_next P) E0 E (s_rgs P) x HwfP Ha0). exact Hx.
Qed.
End Drv.
