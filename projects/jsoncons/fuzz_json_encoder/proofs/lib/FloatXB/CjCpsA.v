(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatSim ShapeAlg SpinAlg AsanAcct AsanAcctShape.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import MState Mem Exec.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Bridge Require Import BrRegs BrBase BrXfer.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section BridgeA.
Context {fx : FPState}.
Variable segs : list Segment.
Variable scfg : SpuriousCfg.
Variable H : word -> bool.
Hypothesis HH : H_off_segments segs H.
Hypothesis Hwx : wx_segs_nowrap segs.

(* [comment removed for export] *)
Lemma cj_evt_srzA : forall (R : bvmap 5 word) (pc : word) (M rom : word -> option byte) (A : list (Z * Z)) (model : Model) (K : TSet)
    (Q : machine_state -> Prop),
  lazy_cover H (m_vm_lazy model) A -> A_wf A -> MInv A model -> m_halted model = None ->
  evt segs Q (MS (canon_regs R) (@fp_regs fx) pc (@fp_csr fx) None (mrestrict H M) rom) ->
  (forall ms1 ms1', Q ms1 -> ms_eqv ms1 ms1' ->
     forall model', MInv A model' -> same_but_materialized model model' -> hclean H ms1' ->
       srealizes segs scfg (mkCfg (unrestrict H M ms1') model') K) ->
  srealizes segs scfg (mkCfg (@mkst fx R pc M rom) model) K.
Proof.
  intros R pc M rom A model K Q HL HA HI Hh E C.
  destruct (evt_eqv_transfer segs _ _ _ (mkst_eqv_canon (fx := fx) R pc (mrestrict H M) rom) E) as (ms1 & ms1' & HQ & Heqv1 & Hms).
  apply (srz_msteps_restricted_T segs scfg H HH Hwx A (@mkst fx R pc M rom) ms1' model K HL HA HI Hh); [exact Hms|].
  intros model' HI' HS HC. exact (C ms1 ms1' HQ Heqv1 model' HI' HS HC).
Qed.

(* [comment removed for export] *)
Lemma cj_evt_rzA : forall (R : bvmap 5 word) (pc : word) (M rom : word -> option byte) (A : list (Z * Z)) (model : Model) (K : TSet)
    (Q : machine_state -> Prop),
  lazy_cover H (m_vm_lazy model) A -> A_wf A -> MInv A model -> m_halted model = None ->
  evt segs Q (MS (canon_regs R) (@fp_regs fx) pc (@fp_csr fx) None (mrestrict H M) rom) ->
  (forall ms1 ms1', Q ms1 -> ms_eqv ms1 ms1' ->
     forall model', MInv A model' -> same_but_materialized model model' -> hclean H ms1' ->
       realizes segs scfg (mkCfg (unrestrict H M ms1') model') K) ->
  realizes segs scfg (mkCfg (@mkst fx R pc M rom) model) K.
Proof.
  intros R pc M rom A model K Q HL HA HI Hh E C.
  destruct (evt_eqv_transfer segs _ _ _ (mkst_eqv_canon (fx := fx) R pc (mrestrict H M) rom) E) as (ms1 & ms1' & HQ & Heqv1 & Hms).
  apply (rz_msteps_restricted_T segs scfg H HH Hwx A (@mkst fx R pc M rom) ms1' model K HL HA HI Hh); [exact Hms|].
  intros model' HI' HS HC. exact (C ms1 ms1' HQ Heqv1 model' HI' HS HC).
Qed.

End BridgeA.
