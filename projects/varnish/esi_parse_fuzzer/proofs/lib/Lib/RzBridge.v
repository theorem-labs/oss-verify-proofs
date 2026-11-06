(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Exec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require ShapeAlg CatSim PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import BWorld.

Module RzEvt.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import CatSim ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import PropExec MState Mem Exec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import BWorld.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Section WithSegs.
Variable segs : list Segment.
Context {BW : BWorld}.

Lemma msteps_cjson_hw : forall ms ms',
  Exec.msteps segs ms ms' -> CatSim.msteps segs ms ms'.
Proof.
  intros ms ms' H. induction H as [ms | ms ms1 ms2 [Hsvc Hstep] Hrest IH].
  - apply mst_refl.
  - eapply mst_step; [exact Hsvc | exact Hstep | exact IH].
Qed.

Lemma rz_evt : forall (Q : machine_state -> Prop) ms md T,
  evt segs Q ms ->
  m_halted md = None -> m_vm_lazy md = [] ->
  (forall ms', Q ms' -> realizes segs (mkCfg ms' md) T) ->
  realizes segs (mkCfg ms md) T.
Proof.
  intros Q ms md T (ms' & Hrun & HQ) Hh Hlazy K.
  eapply rz_msteps; [exact Hh | exact Hlazy | apply msteps_cjson_hw; exact Hrun | apply K; exact HQ].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

End WithSegs.
End RzEvt.


Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Section WithSegs.
Variable segs : list Segment.
Context {BW : BWorld}.

(* [comment removed for export] *)

Lemma msteps_to_cat : forall ms ms',
  Exec.msteps segs ms ms' -> CatSim.msteps segs ms ms'.
Proof.
  intros ms ms' H; induction H as [ms | ms ms1 ms2 [Hsvc Hst] Hms IH].
  - apply CatSim.mst_refl.
  - eapply CatSim.mst_step; [exact Hsvc | exact Hst | exact IH].
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma mkst_MS : forall R pc m ro,
  PropExec.mkst R pc m ro = MS R bvmap_empty pc (Z_to_bv 32 0) None m ro.
Proof. intros; reflexivity. Qed.

(* [comment removed for export] *)

Lemma rz_msteps' : forall ms ms' model T,
  m_halted model = None -> m_vm_lazy model = [] ->
  Exec.msteps segs ms ms' ->
  ShapeAlg.realizes segs (mkCfg ms' model) T ->
  ShapeAlg.realizes segs (mkCfg ms model) T.
Proof.
  intros ms ms' model T Hh Hl Hms Hc.
  eapply ShapeAlg.rz_msteps; [exact Hh | exact Hl | apply msteps_to_cat; exact Hms | exact Hc].
Qed.

(* [comment removed for export] *)
Lemma rz_evt : forall (Q : machine_state -> Prop) ms model T,
  evt segs Q ms ->
  m_halted model = None -> m_vm_lazy model = [] ->
  (forall ms', Q ms' -> ShapeAlg.realizes segs (mkCfg ms' model) T) ->
  ShapeAlg.realizes segs (mkCfg ms model) T.
Proof.
  intros Q ms model T (ms' & Hms & HQ) Hh Hl K.
  eapply rz_msteps'; [exact Hh | exact Hl | exact Hms | apply K; exact HQ].
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition cps (Pre : machine_state -> Model -> Prop)
               (Post : machine_state -> Model -> machine_state -> Model -> Prop) : Prop :=
  forall ms md (T : ShapeAlg.TSet),
    Pre ms md ->
    (forall ms' md', Post ms md ms' md' -> ShapeAlg.realizes segs (mkCfg ms' md') T) ->
    ShapeAlg.realizes segs (mkCfg ms md) T.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
Definition rz_at (md : Model) (T : ShapeAlg.TSet) : machine_state -> Prop :=
  fun ms => ShapeAlg.realizes segs (mkCfg ms md) T.

Lemma rz_go : forall ms md T,
  m_halted md = None -> m_vm_lazy md = [] ->
  evt segs (rz_at md T) ms ->
  ShapeAlg.realizes segs (mkCfg ms md) T.
Proof.
  intros ms md T Hh Hl Hev. eapply rz_evt; [exact Hev | exact Hh | exact Hl |].
  intros ms' HQ. exact HQ.
Qed.

Lemma rz_stop : forall ms md T,
  ShapeAlg.realizes segs (mkCfg ms md) T -> evt segs (rz_at md T) ms.
Proof. intros ms md T H. apply evt_done. exact H. Qed.

End WithSegs.

Arguments cps segs {BW} Pre Post /.
Arguments rz_at segs {BW} md T /.

