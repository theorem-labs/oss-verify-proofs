(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require ShapeAlg.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import SpinAlgCfg MasterCfg.
Unset Nia Cache.  (* [comment removed for export] *)
Import ListNotations.
Unset Lia Cache.

Module IS := OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.ShapeAlg.

Lemma info_CFG_eq : IS.CFG = CFG.
Proof. reflexivity. Qed.

Lemma info_realizes_src_real : forall segs c (T : IS.TSet), IS.realizes segs c T -> src_real segs c T.
Proof.
  intros segs c T H. split; [exact (IS.realizes_obs_iff segs c T H) | exact (IS.realizes_no_error segs c T H)].
Qed.

(* [comment removed for export] *)
Lemma srealizes_cfg_of_info_realizes : forall segs c (T : IS.TSet), IS.realizes segs c T -> srealizes_cfg segs c T.
Proof.
  intros segs c T H.
  induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq].
  - exact (srz_cfg_node segs c I evs nx T i0 Hnode IH).
  - exact (srz_cfg_halt segs c Hh).
  - exact (srz_cfg_conseq segs c T T' IH Heq).
Qed.

(* [comment removed for export] *)
Theorem info_asan_base :
  forall (lim_source lim_target : Z) (src tgt : Image) (S : ProcInput -> IS.TSet) (TT : ProcInput -> list event -> Prop),
  (forall en_source inp, valid_entry src en_source inp -> valid_input inp ->
     match src, en_source with
     | mkImage segs pc ph, mkEntry sp brk0 mbase rnd =>
         IS.realizes segs (init_config segs pc ph sp brk0 mbase rnd lim_source inp) (S inp)
     end) ->
  (forall en_target inp, valid_entry tgt en_target inp -> valid_input inp ->
     match tgt, en_target with
     | mkImage segs pc ph, mkEntry sp brk0 mbase rnd =>
         srealizes_cfg segs (init_config segs pc ph sp brk0 mbase rnd lim_target inp) (TT inp)
     end) ->
  (forall inp tr, S inp tr <-> TT inp tr) ->
  strong_universal_error_free_T_scfg_budgets CFG lim_source lim_target src tgt.
Proof.
  intros lim_source lim_target src tgt S TT HS HT Heq.
  apply (cfg_universal_error_free_budgets lim_source lim_target src tgt S TT); [| exact HT | exact Heq].
  intros en_source inp Hen Hv. specialize (HS en_source inp Hen Hv).
  destruct src as [segs pc ph], en_source as [sp brk0 mbase rnd].
  exact (info_realizes_src_real _ _ _ HS).
Qed.
