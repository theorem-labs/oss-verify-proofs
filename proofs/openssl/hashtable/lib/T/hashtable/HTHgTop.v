(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit FinInput Classifier.
From OssFuzzTheorems.openssl.hashtable.images Require Import Plain.
From OssFuzzTheorems.openssl.hashtable.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import ShapeAlg ShapeEF Spec ClaVerdict.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require ShapeCfg ConeCfg.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require H0Lim HULim.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Abbreviation PSEGS := Plain.M.loaded_segments.
Abbreviation PPC := Plain.M.init_pc.
Abbreviation PPH := Plain.M.phdrs.
Abbreviation USEGS := Ubsan.M.loaded_segments.
Abbreviation UPC := Ubsan.M.init_pc.
Abbreviation UPH := Ubsan.M.phdrs.
Definition P0 : Image := mkImage PSEGS PPC PPH.
Definition U0 : Image := mkImage USEGS UPC UPH.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition h0_acc_stmt : Prop :=
  forall lim, (H0Lim.LIM <= lim)%Z ->
  forall sp brk mbase rnd (inp : ProcInput),
    valid_sp sp -> valid_brk PSEGS brk -> valid_mmap_base mbase ->
    entry_stack_fits sp (in_argv inp) (in_envp inp) ->
    valid_input inp ->
    drv_verdict (in_argv inp) (in_fs inp) = true ->
    ShapeCfg.realizes_cfg ConeCfg.CFG PSEGS (init_config PSEGS PPC PPH sp brk mbase rnd lim inp) (spec (in_argv inp) (in_fs inp)).

Definition hu_acc_stmt : Prop :=
  forall lim, (HULim.LIM <= lim)%Z ->
  forall sp brk mbase rnd (inp : ProcInput),
    valid_sp sp -> valid_brk USEGS brk -> valid_mmap_base mbase ->
    entry_stack_fits sp (in_argv inp) (in_envp inp) ->
    valid_input inp ->
    drv_verdict (in_argv inp) (in_fs inp) = true ->
    ShapeCfg.realizes_cfg ConeCfg.CFG USEGS (init_config USEGS UPC UPH sp brk mbase rnd lim inp) (spec (in_argv inp) (in_fs inp)).

Theorem hg_piece : h0_acc_stmt -> hu_acc_stmt ->
  forall f, valid_fin_input f -> cla_verdict f = true -> good_input_s ConeCfg.CFG P0 U0 (to_proc_input f).
Proof.     (* [comment removed for export] *)
  intros HP HU f Hv Hc. apply ShapeCfg.shape_cfg_good_input_s.
  intros [ssp sbrk smb srnd] [tsp tbrk tmb trnd] Hens Hent.
  pose proof (valid_input_va_size _ Hv) as Hsv48.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hens. rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hent.
  destruct Hens as (Hssp & Hsbrk & Hsmb & Hsfit). destruct Hent as (Htsp & Htbrk & Htmb & Htfit).
  exists (spec (in_argv (to_proc_input f)) (in_fs (to_proc_input f))). split.
  - apply (HP source_alloc_limit H0Lim.LIM_le_source); assumption.
  - apply (HU target_alloc_limit HULim.LIM_le_target); assumption.
Qed.
