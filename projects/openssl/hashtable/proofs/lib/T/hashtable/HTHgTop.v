(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the start-up statements carry the launch premise [entry_launch_ok_va], and each run's segments and start state come from [RomStable.run_init]). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit FinInput Classifier.
From OSSVerify.openssl.hashtable.images Require Import Plain.
From OSSVerify.openssl.hashtable.images Require Import Ubsan.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import ShapeAlg ShapeEF Spec ClaVerdict.
From OSSVerify.Proofs.openssl.hashtable.lib Require ShapeCfg ConeCfg.   (* [comment removed for export] *)
From OSSVerify.Proofs.openssl.hashtable.lib Require H0Lim HULim.   (* [comment removed for export] *)
From OSSVerify.Proofs.openssl.hashtable.lib Require RomStable.
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
    (* LPS 75d69e00: [ref_startup] reads the launch window.  The 5th conjunct of
       [valid_entry_sv48] (Run.v:3747-3756) supplies it at every discharge site, under that
       site's own [in_va_size inp = Sv48] from [valid_input_va_size] -- so this is carried,
       never assumed. *)
    entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp ->
    valid_input inp ->
    drv_verdict (in_argv inp) (in_fs inp) = true ->
    ShapeCfg.realizes_cfg ConeCfg.CFG PSEGS (init_config PSEGS PPC PPH sp brk mbase rnd lim inp) (spec (in_argv inp) (in_fs inp)).

Definition hu_acc_stmt : Prop :=
  forall lim, (HULim.LIM <= lim)%Z ->
  forall sp brk mbase rnd (inp : ProcInput),
    valid_sp sp -> valid_brk USEGS brk -> valid_mmap_base mbase ->
    entry_stack_fits sp (in_argv inp) (in_envp inp) ->
    entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp ->
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
  destruct Hens as (Hssp & Hsbrk & Hsmb & Hsfit & Hslau). destruct Hent as (Htsp & Htbrk & Htmb & Htfit & Htlau).
  exists (spec (in_argv (to_proc_input f)) (in_fs (to_proc_input f))). split.
  - change (image_run_segments P0 (mkEntry ssp sbrk smb srnd) (to_proc_input f))
      with (run_segments PSEGS (to_proc_input f) ssp smb).
    change (ShapeCfg.init_cfg P0 source_alloc_limit (mkEntry ssp sbrk smb srnd) (to_proc_input f))
      with (init_config (run_segments PSEGS (to_proc_input f) ssp smb) PPC PPH ssp sbrk smb srnd
              source_alloc_limit (to_proc_input f)).
    apply RomStable.run_init; [reflexivity|].
    apply (HP source_alloc_limit H0Lim.LIM_le_source); assumption.
  - change (image_run_segments U0 (mkEntry tsp tbrk tmb trnd) (to_proc_input f))
      with (run_segments USEGS (to_proc_input f) tsp tmb).
    change (ShapeCfg.init_cfg U0 target_alloc_limit (mkEntry tsp tbrk tmb trnd) (to_proc_input f))
      with (init_config (run_segments USEGS (to_proc_input f) tsp tmb) UPC UPH tsp tbrk tmb trnd
              target_alloc_limit (to_proc_input f)).
    apply RomStable.run_init; [reflexivity|].
    apply (HU target_alloc_limit HULim.LIM_le_target); assumption.
Qed.
