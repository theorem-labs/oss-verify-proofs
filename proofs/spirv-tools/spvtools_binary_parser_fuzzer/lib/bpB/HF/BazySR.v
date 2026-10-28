(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import Bcfg BPropExec BCatSim BShapeAlg BReach BazyRestrict BazyRestrictRun BazyRestrictAlg.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BExec BMState BMem.
Import ListNotations.
Open Scope bv_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Section WithSegs.
Variable segs : list Segment.
Context {fx : DFP}.
Context {SC : StepCfg}.

Lemma msteps_of_cj : forall ms ms',
  BExec.msteps segs ms ms' -> msteps segs ms ms'.
Proof.
  intros ms ms' H. induction H as [ms | ms ms1 ms2 [Hsvc Hstep] _ IH].
  - apply mst_refl.
  - eapply mst_step; [exact Hsvc | exact Hstep | exact IH].
Qed.

Lemma msteps_to_cj : forall ms ms',
  msteps segs ms ms' -> BExec.msteps segs ms ms'.
Proof.
  intros ms ms' H. induction H as [ms | ms ms1 ms2 Hsvc Hstep _ IH].
  - apply BExec.msteps_refl.
  - eapply BExec.msteps_cons; [split; [exact Hsvc | exact Hstep] | exact IH].
Qed.

Lemma evt_cj_iff : forall (P : machine_state -> Prop) ms,
  BExec.evt segs P ms <-> exists ms', msteps segs ms ms' /\ P ms'.
Proof.
  intros P ms. split; intros (ms' & H & HP); exists ms'; split; auto using msteps_of_cj, msteps_to_cj.
Qed.

Lemma restrict_MS : forall L S R F pc fc rv m ro,
  restrict L S (BMState.MS R F pc fc rv m ro) = BMState.MS R F pc fc rv (restrict_mem L S m) ro.
Proof. reflexivity. Qed.

Lemma restrict_svc : forall L S ms, ms_svc_pending (restrict L S ms) = ms_svc_pending ms.
Proof. reflexivity. Qed.

Definition hidden_zero_on (L S Zr : list (word * word)) (msF : machine_state) : Prop :=
  forall a, hiddenb L S a = true -> in_rangesb a Zr = true -> ms_mem msF a = Some (Z_to_bv 8 0).

Definition rsub (A B : list (word * word)) : Prop :=
  forall x, in_rangesb x A = true -> in_rangesb x B = true.

Lemma rsub_cons_r : forall A r B, rsub A B -> rsub A (r :: B).
Proof. intros A r B H x Hx. rewrite in_rangesb_cons, (H x Hx). apply orb_true_r. Qed.
Lemma rsub_cons_2 : forall r A B, rsub A B -> rsub (r :: A) (r :: B).
Proof.
  intros r A B H x Hx. rewrite in_rangesb_cons in *.
  destruct (zin_rangeb (bv_unsigned x) r); [reflexivity|]. cbn in *. apply H, Hx.
Qed.

Record lzok (L S Zr : list (word * word)) (c : config) : Prop := {
  lzok_ranges : lazy_ranges_okb segs L = true;
  lzok_inv    : lazy_inv L S (cfg_model c);
  lzok_halted : m_halted (cfg_model c) = None;
  lzok_zero   : hidden_zero_on L S Zr (cfg_ms c);
  lzok_SZr    : rsub S Zr;
  lzok_ZrL    : rsub Zr L;
  lzok_LM     : rsub L (vm_maps (m_vmmaps (cfg_model c)))
}.

Definition hid_same (L S : list (word * word)) (msF msF' : machine_state) : Prop :=
  forall a, hiddenb L S a = true -> ms_mem msF' a = ms_mem msF a.

Lemma hid_same_refl : forall L S msF, hid_same L S msF msF.
Proof. intros L S msF a _. reflexivity. Qed.

Lemma hid_same_trans : forall L S m1 m2 m3,
  hid_same L S m1 m2 -> hid_same L S m2 m3 -> hid_same L S m1 m3.
Proof. intros L S m1 m2 m3 H12 H23 a Ha. rewrite (H23 a Ha). apply H12. exact Ha. Qed.

Lemma hid_same_unrestrict : forall L S msF ms1,
  hid_same L S msF (unrestrict_to L S msF ms1).
Proof.
  intros L S msF ms1 a Ha. unfold unrestrict_to.
  exact (unrestrict_by_hidden (hiddenb L S) msF ms1 a Ha).
Qed.

Lemma hidden_zero_on_frame : forall L S Zr msF msF',
  hidden_zero_on L S Zr msF -> hid_same L S msF msF' -> hidden_zero_on L S Zr msF'.
Proof. intros L S Zr msF msF' HZ Hs a Ha Hz. rewrite (Hs a Ha). exact (HZ a Ha Hz). Qed.

Lemma lzok_lifted : forall L S Zr msF mo msF' mo',
  lzok L S Zr (mkCfg msF mo) ->
  lazy_inv L S mo' -> same_but_materialized mo mo' -> hid_same L S msF msF' ->
  lzok L S Zr (mkCfg msF' mo').
Proof.
  intros L S Zr msF mo msF' mo' [HL Hinv Hh HZ HSZ HZL HLM] Hinv' Hsame Hs. split; cbn in *.
  - exact HL.
  - exact Hinv'.
  - rewrite (same_but_materialized_halted _ _ Hsame). exact Hh.
  - eapply hidden_zero_on_frame; eassumption.
  - exact HSZ.
  - exact HZL.
  - rewrite (same_but_materialized_vmmaps _ _ Hsame). exact HLM.
Qed.

Lemma sreach_dsteps : forall c c' (Q : config -> Prop),
  dsteps segs c c' -> sreach segs Q c' -> sreach segs Q c.
Proof.
  intros c c' Q H; induction H as [c | ms model ms' model' c3 Hh Hsvc Hacc H IH]; intros HQ; [exact HQ|].
  eapply sreach_silent1; [apply node_account; [exact Hh | exact Hsvc | exact Hacc] | apply IH; exact HQ].
Qed.

Section WithLazy.
Variables L S Zr : list (word * word).

Theorem sreach_msteps_lazy : forall msF ms1 mo (Q : config -> Prop),
  lzok L S Zr (mkCfg msF mo) ->
  msteps segs (restrict L S msF) ms1 ->
  (forall msF' mo', lzok L S Zr (mkCfg msF' mo') ->
                    same_but_materialized mo mo' ->
                    restrict L S msF' = ms1 ->
                    hid_same L S msF msF' ->
                    sreach segs Q (mkCfg msF' mo')) ->
  sreach segs Q (mkCfg msF mo).
Proof.
  intros msF ms1 mo Q Hok Hms Hk.
  destruct (msteps_restrict segs L S (lzok_ranges _ _ _ _ Hok) msF ms1 mo (lzok_inv _ _ _ _ Hok) (lzok_halted _ _ _ _ Hok) Hms)
    as (mo' & Hd & Hinv' & Hsame & Hh' & Hr).
  eapply sreach_dsteps; [exact Hd|].
  apply Hk; [| exact Hsame | exact Hr | apply hid_same_unrestrict].
  eapply lzok_lifted; [exact Hok | exact Hinv' | exact Hsame | apply hid_same_unrestrict].
Qed.

Theorem evt_sreach_lazy : forall (P : machine_state -> Prop) msF mo,
  lzok L S Zr (mkCfg msF mo) ->
  BExec.evt segs P (restrict L S msF) ->
  sreach segs (fun c => P (restrict L S (cfg_ms c))
                     /\ lzok L S Zr c
                     /\ same_but_materialized mo (cfg_model c)
                     /\ hid_same L S msF (cfg_ms c))
         (mkCfg msF mo).
Proof.
  intros P msF mo Hok Hevt. apply evt_cj_iff in Hevt. destruct Hevt as (ms1 & Hms & HP).
  eapply sreach_msteps_lazy; [exact Hok | exact Hms |].
  intros msF' mo' Hok' Hsame Hr Hs. apply sr_done. cbn. rewrite Hr. auto.
Qed.

Theorem evt_sreach_lazy_k : forall (P : machine_state -> Prop) msF mo (Q : config -> Prop),
  lzok L S Zr (mkCfg msF mo) ->
  BExec.evt segs P (restrict L S msF) ->
  (forall msF' mo', lzok L S Zr (mkCfg msF' mo') ->
                    same_but_materialized mo mo' ->
                    hid_same L S msF msF' ->
                    P (restrict L S msF') ->
                    sreach segs Q (mkCfg msF' mo')) ->
  sreach segs Q (mkCfg msF mo).
Proof.
  intros P msF mo Q Hok Hevt Hk.
  eapply sreach_seq; [exact (evt_sreach_lazy P msF mo Hok Hevt)|].
  intros [msF' mo'] (HP & Hok' & Hsame & Hs). cbn in HP, Hok', Hsame, Hs.
  apply Hk; assumption.
Qed.

Corollary evt_sreach_lazy_at : forall (P : machine_state -> Prop) msF ms mo (Q : config -> Prop),
  lzok L S Zr (mkCfg msF mo) ->
  restrict L S msF = ms ->
  BExec.evt segs P ms ->
  (forall msF' mo', lzok L S Zr (mkCfg msF' mo') ->
                    same_but_materialized mo mo' ->
                    hid_same L S msF msF' ->
                    P (restrict L S msF') ->
                    sreach segs Q (mkCfg msF' mo')) ->
  sreach segs Q (mkCfg msF mo).
Proof. intros P msF ms mo Q Hok <- Hevt Hk. eapply evt_sreach_lazy_k; eassumption. Qed.

Theorem lzok_open_window : forall W msF mo,
  lzok L S Zr (mkCfg msF mo) ->
  (forall a, zin_rangeb (bv_unsigned a) W = true -> in_rangesb a Zr = true) ->
  (eager_used mo + pages_total (W :: S) * page_size <= vm_limit (m_vmmaps mo))%Z ->
  lzok L (W :: S) Zr (mkCfg msF mo)
  /\ restrict L (W :: S) msF
     = with_mem (restrict L S msF)
         (fun a => if zin_rangeb (bv_unsigned a) W && hiddenb L S a
                   then Some (Z_to_bv 8 0) else ms_mem (restrict L S msF) a).
Proof.
  intros W msF mo [HL Hinv Hh HZ HSZ HZL HLM] HW Hb. cbn in *. split.
  - split; cbn; [exact HL | apply lazy_inv_open_window; assumption | exact Hh | | | exact HZL | exact HLM].
    + intros a Ha Hz. apply HZ; [| exact Hz]. eapply hiddenb_mono_cons. exact Ha.
    + intros x Hx. rewrite in_rangesb_cons in Hx. apply orb_true_iff in Hx.
      destruct Hx as [Hx | Hx]; [apply HW; exact Hx | apply HSZ; exact Hx].
  - rewrite (restrict_open_window_eq L W S msF).
    match goal with |- with_mem ?x ?f = with_mem ?y ?g => replace g with f; [reflexivity|] end.
    apply functional_extensionality. intros a.
    destruct (zin_rangeb (bv_unsigned a) W) eqn:EW; cbn [andb]; [|reflexivity].
    destruct (hiddenb L S a) eqn:Eh.
    + apply HZ; [exact Eh | apply HW; exact EW].
    + unfold restrict_mem_by. rewrite Eh. reflexivity.
Qed.

End WithLazy.

Lemma lzok_vm_frame : forall L S Zr msF mo msF' mo',
  lzok L S Zr (mkCfg msF mo) ->
  m_vm mo' = m_vm mo -> m_halted mo' = None -> hid_same L S msF msF' ->
  lzok L S Zr (mkCfg msF' mo').
Proof.
  intros L S Zr msF mo msF' mo' [HL Hinv Hh HZ HSZ HZL HLM] Evm Hh' Hs. split; cbn in *.
  - exact HL.
  - eapply lazy_inv_vm_frame; [exact Evm | exact Hinv].
  - exact Hh'.
  - eapply hidden_zero_on_frame; eassumption.
  - exact HSZ.
  - exact HZL.
  - unfold m_vmmaps in *. rewrite Evm. exact HLM.
Qed.

Lemma lzok_backing_used_le : forall L S Zr c,
  lzok L S Zr c ->
  (vm_backing_used (cfg_model c) <= eager_used (cfg_model c) + pages_total S * page_size)%Z.
Proof.
  intros L S Zr c [_ [Hl Hnd Hincl Hb] _ _ _ _ _]. rewrite vm_backing_used_split.
  rewrite <- all_pages_length.
  pose proof (NoDup_incl_length Hnd Hincl) as Hlen. unfold page_size. nia.
Qed.

End WithSegs.

Arguments lzok segs L S Zr c : clear implicits.
Arguments lzok_ranges {segs L S Zr c}.
Arguments lzok_inv {segs L S Zr c}.
Arguments lzok_halted {segs L S Zr c}.
Arguments lzok_zero {segs L S Zr c}.
Arguments lzok_SZr {segs L S Zr c}.
Arguments lzok_ZrL {segs L S Zr c}.
Arguments lzok_LM {segs L S Zr c}.
Arguments hidden_zero_on L S Zr msF : clear implicits.
Arguments hid_same L S msF msF' : clear implicits.
