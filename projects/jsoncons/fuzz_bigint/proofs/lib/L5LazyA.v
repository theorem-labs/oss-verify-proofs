(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatSim ShapeAlg SpinAlg AsanAcct AsanAcctShape HeapIface HeapIfaceA L5Defs.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module L5LZ.
Section WithSegs.
Variable segs : list Segment.
Context {SCFG_P : ScfgP}.

(* [comment removed for export] *)
Lemma restrict_mkst (fx : FPState) H R pc M :
  restrict H (@mkst fx R pc M (seg_rom segs)) = @mkst fx R pc (mrestrict H M) (seg_rom segs).
Proof. reflexivity. Qed.
Lemma unrestrict_mkst (fx fx' : FPState) H R pc M R' pc' M' :
  unrestrict H (ms_mem (@mkst fx R pc M (seg_rom segs))) (@mkst fx' R' pc' M' (seg_rom segs))
  = @mkst fx' R' pc' (munrestrict H M M') (seg_rom segs).
Proof. reflexivity. Qed.


(* [comment removed for export] *)
Lemma mrestrict_of_munrestrict H M M' :
  (forall a, H a = true -> M' a = None) -> mrestrict H (munrestrict H M M') = M'.
Proof.
  intros Hc. apply functional_extensionality. intros a. unfold mrestrict, munrestrict.
  destruct (H a) eqn:E. symmetry; apply Hc; exact E. reflexivity.
Qed.
Lemma munrestrict_hidden H M M' a : H a = true -> munrestrict H M M' a = M a.
Proof. intros E. unfold munrestrict. rewrite E. reflexivity. Qed.
Lemma munrestrict_visible H M M' a : H a = false -> munrestrict H M M' a = M' a.
Proof. intros E. unfold munrestrict. rewrite E. reflexivity. Qed.
Lemma mrestrict_visible' H M a : H a = false -> mrestrict H M a = M a.
Proof. intros E. unfold mrestrict. rewrite E. reflexivity. Qed.
(* [comment removed for export] *)
Lemma mrestrict_agree_on (H H' : word -> bool) (M M' : word -> option byte) (P : Z -> Prop) :
  (forall a, P a -> H (Z_to_bv 64 a) = false /\ H' (Z_to_bv 64 a) = false) ->
  (forall a, P a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
  forall a, P a -> mrestrict H' M' (Z_to_bv 64 a) = mrestrict H M (Z_to_bv 64 a).
Proof.
  intros HV HM a Ha. destruct (HV a Ha) as [E E']. unfold mrestrict. rewrite E, E'. apply HM. exact Ha.
Qed.

(* [comment removed for export] *)
Theorem cps_of_msteps_lazy (H : word -> bool) (A : list (Z * Z))
        (fx fx' : FPState) R pc M R' pc' (M1v : word -> option byte) (model : Model) K :
  H_off_segments segs H -> wx_segs_nowrap segs ->
  lazy_cover H (m_vm_lazy model) A -> A_wf A -> MInv A model -> m_halted model = None ->
  msteps segs (@mkst fx R pc (mrestrict H M) (seg_rom segs)) (@mkst fx' R' pc' M1v (seg_rom segs)) ->
  (forall model', MInv A model' -> same_but_materialized model model' ->
       (forall a, H a = true -> M1v a = None) ->
       srealizes segs SCFG (mkCfg (@mkst fx' R' pc' (munrestrict H M M1v) (seg_rom segs)) model') K) ->
  srealizes segs SCFG (mkCfg (@mkst fx R pc M (seg_rom segs)) model) K.
Proof.
  intros HH Hwx HL HA HI Hh MS HK.
  rewrite <- (restrict_mkst fx H R pc M) in MS.
  apply (srz_msteps_restricted_T segs SCFG H HH Hwx A _ _ model K HL HA HI Hh MS).
  intros model' HI' HS HC. rewrite (unrestrict_mkst fx fx') . apply (HK model' HI' HS).
  intros a Ha. exact (HC a Ha).
Qed.

(* [comment removed for export] *)
Lemma lazy_cover_ahid A model : lazy_cover (ahid A model) (m_vm_lazy model) A.
Proof. unfold ahid. apply lazy_cover_mkH. intros r Hr; exact Hr. Qed.

(* [comment removed for export] *)
Lemma H_off_segments_ahid A model top :
  segs_below_b segs top = true ->
  (forall w : word, page_in_ranges (page_base w) (m_vm_lazy model) = true -> top <= bv_unsigned w) ->
  H_off_segments segs (ahid A model).
Proof.
  intros Hb Hhi a Ha. unfold ahid, mkH in Ha. apply andb_prop in Ha as [Hp _].
  apply (find_segment1_none_above segs top). exact Hb. apply Hhi. exact Hp.
Qed.

(* [comment removed for export] *)
Lemma sbm_halted m m' : same_but_materialized m m' -> m_halted m' = m_halted m.
Proof. intros ->. destruct m as [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.
Lemma sbm_lazy m m' : same_but_materialized m m' -> m_vm_lazy m' = m_vm_lazy m.
Proof. intros ->. destruct m as [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.
Lemma sbm_vmmaps m m' : same_but_materialized m m' -> m_vmmaps m' = m_vmmaps m.
Proof. intros ->. destruct m as [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.
Lemma sbm_ahid A m m' : same_but_materialized m m' -> ahid A m' = ahid A m.
Proof. intros Hs. unfold ahid. rewrite (sbm_lazy m m' Hs). reflexivity. Qed.
Lemma sbm_model_rt m m' : same_but_materialized m m' -> model_rt m m'.
Proof. intros ->. destruct m as [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.
Lemma model_rt_trans m1 m2 m3 : model_rt m1 m2 -> model_rt m2 m3 -> model_rt m1 m3.
Proof. unfold model_rt. intros -> ->. destruct m1; reflexivity. Qed.
Lemma model_rt_halted m m' : model_rt m m' -> m_halted m' = m_halted m.
Proof. intros ->. destruct m; reflexivity. Qed.

End WithSegs.
End L5LZ.
