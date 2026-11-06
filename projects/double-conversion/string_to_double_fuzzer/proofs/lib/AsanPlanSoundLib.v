(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SpinAlg AgentLib.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AsanAcct AsanAcctShape BackingAlgebra AxSymExec3 AxSymExec3Sound AxSymRun3
  AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2 AX2S AP APS APSX.
Open Scope Z_scope.

Section Lib.
Context {fx : FPState}.            (* [comment removed for export] *)
Variable SEGS : list Segment.
Variable A : atable.
Variable nx0 : nat.
Variable LIMIT : Z.
Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : hull_ok A.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Variable LINV : (word -> option byte) -> Prop.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis argH_top : forall E M (a : word), SINV E M -> argH E a = true -> bv_unsigned (edenot E e_sp0) <= bv_unsigned a.   (* [comment removed for export] *)
Hypothesis nx0_ge : APS.nx0_ok nx0.                                                                       (* [comment removed for export] *)
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
Hypothesis LINV_frame : forall M M' : word -> option byte, (forall a : word, in_lfp A (bv_unsigned a) = true -> M' a = M a) -> LINV M -> LINV M'.
Hypothesis LFP_hull : forall z, in_lfp A z = true -> img_lo A <= z < img_hi A.
Variable FS0 : Fs.Fs.

#[local] Notation CSOK := (cs_ok SEGS A LIMIT SINV argH LINV FS0).
#[local] Notation HID := (hid A argH).
#[local] Notation MR := (Mr A argH).

(* [comment removed for export] *)
Lemma hid_lfp : forall E cs model (a : word), in_lfp A (bv_unsigned a) = true -> HID E cs model a = false.
Proof.
  intros E cs model a Ha. apply (hid_hull A HULL_ok argH argH_high).
  pose proof (LFP_hull _ Ha) as [H1 H2]. unfold in_hull. apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.

(* [comment removed for export] *)
Lemma Mr_lfp : forall E cs model FULL (a : word), in_lfp A (bv_unsigned a) = true -> MR E cs model FULL a = FULL a.
Proof. intros E cs model FULL a Ha. unfold Mr, mrestrict. rewrite (hid_lfp E cs model a Ha). reflexivity. Qed.

(* [comment removed for export] *)
Lemma LINV_Mr : forall E cs model FULL, LINV FULL -> LINV (MR E cs model FULL).
Proof. intros E cs model FULL HL. eapply LINV_frame; [|exact HL]. intros a Ha. apply Mr_lfp. exact Ha. Qed.

(* [comment removed for export] *)
Lemma cs_ok_frameL : forall E cs R FULL model ss' R' FULL' model',
  CSOK E cs R FULL model ->
  same_but_materialized model model' ->
  MInv (allowA A E cs) model' ->
  regs_ok E (s_regs ss') R' -> s_log ss' = [] ->
  know_ok SEGS E (MR E cs model FULL') (s_know ss') ->
  (forall a, HID E cs model a = true -> FULL' a = FULL a) ->
  LINV FULL' ->
  CSOK E (with_ss cs ss') R' FULL' model'.
Proof.
  intros E cs R FULL model ss' R' FULL' model' HC Hs Hinv HR HL HK Hhid HLINV.
  pose proof (same_but_materialized_frame _ _ Hs) as Hfr.
  assert (Evm : m_vmmaps model' = m_vmmaps model) by apply Hfr.
  assert (Elz : m_vm_lazy model' = m_vm_lazy model) by apply Hfr.
  destruct HC. constructor; cbn [with_ss a_ss a_maps a_totsz a_ylo a_eager a_vis a_abytes a_brk a_fd a_tidset kn];
    rewrite ?Evm, ?Elz; try assumption.
  - unfold Mr. rewrite (hid_same A argH _ _ _ _ Hs). exact HK.
  - replace (m_halted model') with (m_halted model) by (symmetry; apply Hfr). assumption.
  - unfold fds_ok in *. replace (m_fds model') with (m_fds model) by (symmetry; apply Hfr).
    replace (m_fs model') with (m_fs model) by (symmetry; apply Hfr). assumption.
  - replace (m_fs model') with (m_fs model) by (symmetry; apply Hfr). assumption.
  - intros Ht. replace (m_tid model') with (m_tid model) by (symmetry; apply Hfr). auto.
  - unfold model_ivs_wf in *. rewrite Evm, Elz. assumption.
  - replace (eager_used model') with (eager_used model) by (symmetry; apply Hfr). assumption.
  - intros a Hh. rewrite (hid_same A argH _ _ _ _ Hs) in Hh. rewrite (Hhid a Hh). auto.
  - eapply SINV_frame; [|eassumption]. intros a Ha. apply Hhid. unfold hid. rewrite Ha. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma call_core_lib : forall (fx' : FPState) cs E E' R FULL model T (ret : Z) sr2 k' nx2 regs' MR',
  CSOK E cs R FULL model ->
  fresh_ok nx0 cs = true ->
  env_agree (nxt cs) E E' ->
  msteps SEGS (mkst (fx:=fx) R (Z_to_bv 64 (pc cs)) (MR E cs model FULL) (seg_rom SEGS))
              (mkst (fx:=fx') regs' (Z_to_bv 64 ret) MR' (seg_rom SEGS)) ->
  regs_ok E' sr2 regs' ->
  know_ok SEGS E' MR' k' ->
  LINV MR' ->
  (forall R' FULL' model',
      CSOK E' (with_ss cs (mk_ss ret sr2 k' nx2)) R' FULL' model' -> m_fs model' = m_fs model ->
      srealizes SEGS (cfg_of (fx:=fx') SEGS R' ret FULL' model') T) ->
  srealizes SEGS (cfg_of (fx:=fx) SEGS R (pc cs) FULL model) T.
Proof.
  intros fx' cs E E' R FULL model T ret sr2 k' nx2 regs' MR' HC Hfresh Hag Hms HR' HK' HLINV Hk.
  destruct (w_fresh_ok_parts nx0 cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  set (H := HID E cs model).
  unfold cfg_of.
  apply (srz_msteps_restricted_T SEGS H
           (w_H_off_segments_cs SEGS A SEGS_in_hull HULL_ok argH argH_high E cs model) SEGS_wx (allowA A E cs)
           (mkst (fx:=fx) R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS)) (mkst (fx:=fx') regs' (Z_to_bv 64 ret) MR' (seg_rom SEGS)) model T
           (w_lazy_cover_cs SEGS A nx0 LIMIT HULL_ok SINV argH LINV FS0 E cs R FULL model HC)
           (w_A_wf_allowA A nx0 E cs)
           (co_minv _ _ _ _ _ _ _ _ _ _ _ _ HC) (co_halt _ _ _ _ _ _ _ _ _ _ _ _ HC)).
  - rewrite restrict_mkst. exact Hms.
  - intros model' Hinv' Hsame Hclean.
    set (FULL' := munrestrict H FULL MR').
    change (unrestrict H (ms_mem (mkst (fx:=fx) R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS))) (mkst (fx:=fx') regs' (Z_to_bv 64 ret) MR' (seg_rom SEGS)))
      with (mkst (fx:=fx') regs' (Z_to_bv 64 ret) FULL' (seg_rom SEGS)).
    apply (Hk regs' FULL' model').
    + pose proof (w_cs_ok_agree SEGS A nx0 LIMIT SINV argH LINV argH_agree nx0_ge SINV_agree FS0 E E' cs R FULL model Hag Hfresh HC) as HC1.
      pose proof (w_hid_agree A nx0 argH argH_agree (nxt cs) E E' cs model Hag Fle Fallow) as HH.
      eapply (cs_ok_frameL E' cs R FULL model _ regs' FULL' model' HC1 Hsame).
      * rewrite (allowA_agree A (nxt cs) E E' cs Hag Fallow). exact Hinv'.
      * exact HR'.
      * reflexivity.
      * cbn [s_know mk_ss]. unfold Mr. rewrite HH.
        fold H. unfold FULL'. rewrite (mrestrict_munrestrict_clean H FULL MR') by (intros a Ha; exact (Hclean a Ha)).
        exact HK'.
      * intros a Ha. rewrite HH in Ha.
        unfold FULL', munrestrict. fold H in Ha. rewrite Ha. reflexivity.
      * (* [comment removed for export] *)
        eapply LINV_frame; [|exact HLINV]. intros a Ha. unfold FULL', munrestrict.
        unfold H. rewrite (hid_lfp E cs model a Ha). reflexivity.
    + apply (same_but_materialized_frame _ _ Hsame).
Qed.

(* [comment removed for export] *)
Lemma call_node_lib_sound : forall (fx' : FPState) cs cs' E R FULL model T (ret : Z) rv k' regs' MR',
  CSOK E cs R FULL model ->
  after_call nx0 cs ret rv k' = Some cs' ->
  msteps SEGS (mkst (fx:=fx) R (Z_to_bv 64 (pc cs)) (MR E cs model FULL) (seg_rom SEGS))
              (mkst (fx:=fx') regs' (Z_to_bv 64 ret) MR' (seg_rom SEGS)) ->
  kept_ok R regs' ->
  match rv with Some e => getr regs' (Z_to_bv 5 10) = edenot E e | None => True end ->
  know_ok SEGS E MR' k' ->
  LINV MR' ->
  (forall E' R' FULL' model',
      env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> CSOK E' cs' R' FULL' model' -> m_fs model' = m_fs model ->
      srealizes SEGS (cfg_of (fx:=fx') SEGS R' (pc cs') FULL' model') T) ->
  srealizes SEGS (cfg_of (fx:=fx) SEGS R (pc cs) FULL model) T.
Proof.
  intros fx' cs cs' E R FULL model T ret rv k' regs' MR' HC Hac Hms Hkept Hrv HK' HLINV Hk.
  unfold after_call in Hac.
  match type of Hac with context [if ?c then _ else _] => destruct c eqn:Hc; [|discriminate] end.
  apply andb_prop in Hc as [Hc Hrvv]. apply andb_prop in Hc as [Hfresh Hkv].
  injection Hac as <-.
  destruct (w_fresh_ok_parts nx0 cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  set (E' := ext_call E (nxt cs) regs').
  pose proof (ext_call_agree E (nxt cs) regs') as Hag. fold E' in Hag.
  eapply (call_core_lib fx' cs E E' R FULL model T ret _ k' _ regs' MR' HC Hfresh Hag Hms).
  - apply (regs_after_call E _ R regs' (nxt cs) rv (co_regs _ _ _ _ _ _ _ _ _ _ _ _ HC) Fsr Hkept).
    destruct rv as [e|]; [split; [exact Hrvv | exact Hrv] | exact I].
  - eapply know_ok_agree'; [exact Hag | exact Hkv | exact HK'].
  - exact HLINV.
  - intros R' FULL' model' HC' Hfs. apply (Hk E' R' FULL' model'); [| exact HC' | exact Hfs].
    split; [eapply w_env_agree_le; [exact Hag | exact Fle] | exact Hag].
Qed.
End Lib.
