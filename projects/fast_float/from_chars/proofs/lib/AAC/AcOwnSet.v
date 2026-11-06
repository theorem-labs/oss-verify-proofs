(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec FxLin FxCore FxSound FxMem FxStep FxSubst FxDrv.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxBacking FxChDen.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require Import AcConv AcDenW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section OwnSet.
Variable segs : list Segment.
Variable LIMIT : Z.
Variable model0 : Model.

#[using="Type"] Theorem den_own_set : forall mem0 mem0' E S M ms model own',
  DEN segs LIMIT model0 mem0 E S M ms model ->
  forallb (fun p => lwf (s_next S) (fst p) && lwf (s_next S) (snd p))%bool own' = true ->
  (forall w, frz_pt E M w -> mem0' (Z_to_bv 64 w) = mem0 (Z_to_bv 64 w)) ->
  (forall w, own_pt E M w -> own_pt E (with_own M own') w) ->
  (forall w, own_pt E (with_own M own') w ->
     Hof E M model (Z_to_bv 64 w) = false /\ (outside E (s_rgs S) (Z_to_bv 64 w) -> ms_mem ms (Z_to_bv 64 w) = mem0' (Z_to_bv 64 w))) ->
  DEN segs LIMIT model0 mem0' E S (with_own M own') ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros mem0 mem0' E S M ms model own' Hd Hwo Hf Hsub Hnew.
  destruct Hd as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  constructor; cbn [with_own sm_maps sm_allow sm_zr sm_tid sm_brk sm_sbrk sm_sp sm_frz sm_own]; try assumption.
  - unfold sm_wf in Hwf |- *. unfold with_own. cbn [sm_maps sm_allow sm_zr sm_tid sm_brk sm_sbrk sm_sp sm_frz sm_own].
    apply andb_prop in Hwf as [Hwf _]. rewrite Hwf. exact Hwo.
  - intros w Hw Hout Hno Hnb. apply (Hzr w Hw Hout); [|exact Hnb]. intros Ho. apply Hno. exact (Hsub w Ho).
  - intros q Hq w Hw. destruct (Hfrz q Hq w Hw) as (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|].
    rewrite H3. symmetry. apply Hf. exists q. split; [exact Hq | exact Hw].
  - intros q Hq w Hw. apply Hnew. exists q. split; [exact Hq | exact Hw].
Qed.
End OwnSet.
