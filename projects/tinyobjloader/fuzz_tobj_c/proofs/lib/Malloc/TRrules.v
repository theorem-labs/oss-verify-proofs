(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "ok_frame"; "@Corelib.Init.Logic"; "and"; "eq"; "or"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@Corelib.Init.Datatypes"; "list"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRrules.WithSegs"; "TRrules"; "pinK"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundR SymFrame SymSummary SymComplete.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import WalkLink WalkReab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section WithSegs.
Variable segs : list Segment.

Record TRrules (TR : assn -> assn -> Prop) (K : list event -> Model -> Prop) : Prop := {

  tr_run : forall (rhoB : valuation) (cuts : list Z) (fuel : nat) (S : sstate) (leaves : list leaf) (Q : assn) (rho' : valuation),
    ss_lenient S = false -> (200 <= ss_next S)%positive ->
    sym_run segs fuel cuts S true = Some leaves -> agrees rhoB rho' ->
    (forall Lf rho'' w, In Lf leaves -> agrees rhoB rho'' -> SymSoundR.SP segs K (lf_state Lf) rho'' w -> Q w) ->
    TR (SymSoundR.SP segs K S rho') Q;
  tr_refl : forall P : assn, TR P P;
  tr_seq : forall P R Q : assn, TR P R -> TR R Q -> TR P Q;
  tr_ex : forall (A : Type) (P : A -> assn) (Q : assn), (forall a, TR (P a) Q) -> TR (fun w => exists a, P a w) Q;
  tr_pure : forall (X0 : Prop) (P Q : assn), (X0 -> TR P Q) -> TR (fun w => X0 /\ P w) Q;
  tr_conseq : forall (P P' Q Q' : assn), (forall w, P' w -> P w) -> (forall w, Q w -> Q' w) -> TR P Q -> TR P' Q';
  tr_pointwise : forall (R Q : assn), (forall w, R w -> TR (fun w' => w' = w) Q) -> TR R Q
}.

Theorem TRrules_triple (ok : world -> Prop) (K : list event -> Model -> Prop) : ltac2:(tb__ "0|0|
S0Vsegs;Vok;VK;A3S9S7Vsegs;Vok;A2VK;A2F_;").
Proof using .
  intros HK. split.
  - intros rhoB cuts fuel S leaves Q rho' Hl Hn Hrun Hag HQ. exact (seg_run segs rhoB ok K HK cuts fuel S leaves Q rho' Hl Hn Hrun Hag HQ).
  - intros P. apply triple_refl.
  - intros P R Q H1 H2. eapply triple_seq; [exact H1 | exact H2].
  - intros A P Q H. apply triple_ex. exact H.
  - intros X0 P Q H. apply triple_pure. exact H.
  - intros P P' Q Q' HP HQ H. eapply triple_conseq; [exact HP | exact HQ | exact H].
  - intros R Q H n Hg w Hw. exact (H w Hw n Hg w eq_refl).
Qed.

Theorem TRrules_etriple (K : list event -> Model -> Prop) : TRrules (etriple segs) K.
Proof using .
  split.
  - intros rhoB cuts fuel S leaves Q rho' Hl Hn Hrun Hag HQ w Hw.
    destruct (sym_run_complete segs fuel cuts S leaves K rho' w Hl Hrun Hw) as (Lf & rho'' & w' & Hin & Hst & Hab & HSP).
    exists w'. split; [exact Hst|]. apply (HQ Lf rho'' w' Hin); [|exact HSP].
    eapply agrees_below; [exact Hag | exact Hab | exact Hn].
  - intros P. apply etriple_refl.
  - intros P R Q H1 H2. eapply etriple_seq; [exact H1 | exact H2].
  - intros A P Q H. apply etriple_ex. exact H.
  - intros X0 P Q H. apply etriple_pure. exact H.
  - intros P P' Q Q' HP HQ H. eapply etriple_conseq; [exact HP | exact HQ | exact H].
  - intros R Q H w Hw. destruct (H w Hw w eq_refl) as (w' & Hs & HQ'). exists w'. split; assumption.
Qed.

Lemma tr_disj TR K (H : TRrules TR K) (P1 P2 Q : assn) : ltac2:(tb__ "0|0|
VTR;VP1;VQ;A2VTR;VP2;VQ;A2VTR;S8S3VP1;R1A1VP2;R1A1A2Lw;VQ;A2F_;F_;").
Proof using .
  intros H1 H2. apply (tr_pointwise TR K H). intros w [Hw|Hw].
  - eapply (tr_conseq TR K H); [| intros w' Hq; exact Hq | exact H1]. intros w' ->. exact Hw.
  - eapply (tr_conseq TR K H); [| intros w' Hq; exact Hq | exact H2]. intros w' ->. exact Hw.
Qed.

Definition pinK (Kc : list event -> Model -> Prop) (tr : list event) (md : Model) : list event -> Model -> Prop := ltac2:(tb__ "0|1|
S6S5A1M0S4S1VKc;R2R1A2S1S2G0R2Vtr;A3S2S4R1Vmd;A3A2A2Lmd';Ltr';").
Lemma ok_frame_pinK (ok : world -> Prop) Kc tr md : ltac2:(tb__ "0|0|
S0Vsegs;Vok;VKc;A3S0Vsegs;Vok;SaVKc;Vtr;Vmd;A3A3F_;").
Proof using . intros H tr0 ms0 md0 ms0' (HK0 & _ & _). exact (H tr0 ms0 md0 ms0' HK0). Qed.
End WithSegs.
