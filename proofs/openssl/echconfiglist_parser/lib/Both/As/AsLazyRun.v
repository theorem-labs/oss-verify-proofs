(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk SimInv ExitSim ShapeAlg SReach Frame
  LazyRestrict LazyRestrictRun LazyRestrictAlg LazySR.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section WithSegs.
Variable segs : list Segment.
Variables L S Zr : list (word * word).

Theorem rz_msteps_lazy : forall msF ms1 mo T,
  lzok segs L S Zr (mkCfg msF mo) ->
  msteps segs (restrict L S msF) ms1 ->
  (forall msF' mo',
     lzok segs L S Zr (mkCfg msF' mo') ->
     same_but_materialized mo mo' ->
     hid_same L S msF msF' ->
     restrict L S msF' = ms1 ->
     realizes segs (mkCfg msF' mo') T) ->
  realizes segs (mkCfg msF mo) T.
Proof.
  intros msF ms1 mo T Hok Hms Hcont.
  destruct (msteps_restrict segs L S (lzok_ranges Hok) msF _ mo (lzok_inv Hok) (lzok_halted Hok) Hms)
    as (mo' & Hd & Hinv' & Hsame & Hh' & Hrestr).
  eapply rz_dsteps; [exact Hd|].
  apply Hcont; [| exact Hsame | apply hid_same_unrestrict | exact Hrestr].
  eapply lzok_lifted; [exact Hok | exact Hinv' | exact Hsame | apply hid_same_unrestrict].
Qed.

(* [comment removed for export] *)
Corollary rz_msteps_lazy_mkst : forall msF regs pc mem rom regs' pc' mem' mo T,
  lzok segs L S Zr (mkCfg msF mo) ->
  restrict L S msF = mkst regs pc mem rom ->
  msteps segs (mkst regs pc mem rom) (mkst regs' pc' mem' rom) ->
  (forall msF' mo',
     lzok segs L S Zr (mkCfg msF' mo') ->
     same_but_materialized mo mo' ->
     hid_same L S msF msF' ->
     restrict L S msF' = mkst regs' pc' mem' rom ->
     realizes segs (mkCfg msF' mo') T) ->
  realizes segs (mkCfg msF mo) T.
Proof.
  intros msF regs pc mem rom regs' pc' mem' mo T Hok Hr Hms Hcont.
  eapply rz_msteps_lazy; [exact Hok | rewrite Hr; exact Hms | exact Hcont].
Qed.
End WithSegs.
