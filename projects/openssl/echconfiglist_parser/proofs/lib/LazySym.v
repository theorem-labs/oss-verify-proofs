(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import
  Scfg PropExec CatExec CatSim SeqExec StoreOk SimInv ExitSim ShapeAlg SReach SymExec Frame SymExec2 SymExec2Sound SymRun SymDrive
  LazyRestrict LazyRestrictRun LazyRestrictAlg LazySR.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)

Section WithSegs.
Variable segs : list Segment.
(* [comment removed for export] *)
Context {SC : StepCfg}.
Variables L S Zr : list (word * word).

(* [comment removed for export] *)
Theorem rz_run_lazy : forall fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2
                         E M rom R msF model T,
  sym_exec segs fuel true stops scr (SS pc sr [] kn nx) [] = (ss', scs, scr') ->
  carry (s_log ss') kn [] = (kn', scs2, hs2) ->
  regs_ok E sr R -> know_ok segs E M kn ->
  scs_denot segs M E scs -> scs_denot segs M E scs2 ->
  lzok segs L S Zr (mkCfg msF model) ->
  restrict L S msF = mkst R (Z_to_bv 64 pc) M rom ->
  (forall R' M' msF' model', regs_ok E (s_regs ss') R' -> know_ok segs E M' kn' ->
     M' = mem_denot E M (s_log ss') ->
     lzok segs L S Zr (mkCfg msF' model') ->
     same_but_materialized model model' ->
     hid_same L S msF msF' ->
     restrict L S msF' = mkst R' (Z_to_bv 64 (s_pc ss')) M' rom ->
     realizes segs (mkCfg msF' model') T) ->
  realizes segs (mkCfg msF model) T.
Proof.
  intros fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2 E M rom R msF model T
         Hex Hc HR HK Hsc Hsc2 Hok Hr Hcont.
  destruct (run_sound segs fuel stops scr pc sr kn nx ss' scs scr' E M rom R Hex HR HK Hsc)
    as (R' & HR' & Hlf & Hms).
  rewrite <- Hr in Hms.
  destruct (msteps_restrict segs L S (lzok_ranges Hok) msF _ model (lzok_inv Hok) (lzok_halted Hok) Hms)
    as (model' & Hd & Hinv' & Hsame & Hh' & Hrestr).
  eapply rz_dsteps; [exact Hd|].
  apply (Hcont R' (mem_denot E M (s_log ss')) _ model' HR'); [| reflexivity | | exact Hsame | apply hid_same_unrestrict | exact Hrestr].
  - eapply carry_after; eassumption.
  - eapply lzok_lifted; [exact Hok | exact Hinv' | exact Hsame | apply hid_same_unrestrict].
Qed.

(* [comment removed for export] *)
Theorem sreach_run_lazy : forall fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2
                         E M rom R msF model (Q : config -> Prop),
  sym_exec segs fuel true stops scr (SS pc sr [] kn nx) [] = (ss', scs, scr') ->
  carry (s_log ss') kn [] = (kn', scs2, hs2) ->
  regs_ok E sr R -> know_ok segs E M kn ->
  scs_denot segs M E scs -> scs_denot segs M E scs2 ->
  lzok segs L S Zr (mkCfg msF model) ->
  restrict L S msF = mkst R (Z_to_bv 64 pc) M rom ->
  (forall R' M' msF' model', regs_ok E (s_regs ss') R' -> know_ok segs E M' kn' ->
     M' = mem_denot E M (s_log ss') ->
     lzok segs L S Zr (mkCfg msF' model') ->
     same_but_materialized model model' ->
     hid_same L S msF msF' ->
     restrict L S msF' = mkst R' (Z_to_bv 64 (s_pc ss')) M' rom ->
     sreach segs Q (mkCfg msF' model')) ->
  sreach segs Q (mkCfg msF model).
Proof.
  intros fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2 E M rom R msF model Q
         Hex Hc HR HK Hsc Hsc2 Hok Hr Hcont.
  destruct (run_sound segs fuel stops scr pc sr kn nx ss' scs scr' E M rom R Hex HR HK Hsc)
    as (R' & HR' & Hlf & Hms).
  rewrite <- Hr in Hms.
  eapply sreach_msteps_lazy; [exact Hok | exact Hms |].
  intros msF' mo' Hok' Hsame Hrestr Hhs.
  apply (Hcont R' (mem_denot E M (s_log ss')) _ mo' HR'); [| reflexivity | exact Hok' | exact Hsame | exact Hhs | exact Hrestr].
  eapply carry_after; eassumption.
Qed.

End WithSegs.
