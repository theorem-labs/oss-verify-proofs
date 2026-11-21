(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from QHdY.v (drv_start_spec_lim, its argc <> 2 arms): the start-up walk continued by the usage walk over BudgetWit.QRjHB.realizes, and the budget premise it gives. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch premises valid_launch and entry_launch_ok_va; the channel-reader premise in_channel_reader; the hand-off model's vDSO layer dropped for the binary's segments, which have no vDSO text; the walk over run_segments, lifted by QRjHBRom.rz_run_init; the input facts read from valid_input_abort). *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.json_c.json_object_fuzzer.images Require Import Plain.
From OSSVerify.json_c.json_object_fuzzer Require Images.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsRG QJyS QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.BudgetWit Require QRjHB QRjHBRom QFOHB QmsFB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import QsRG.Mq0 QJyS QRjHB.
Import ListNotations.
Open Scope Z_scope.

#[local] Existing Instance fp0F.
#[local] Existing Instance fp0C.

(** * The usage path of the plain build, over the budget-checked relation

    [QHdY.drv_start_spec_lim] proves [QRjH.realizes] for the plain build's
    initial configuration: the start-up walk [QFOH.Mq1.ref_startup], continued
    at [main] by [QHdY.drv_main_spec], whose arms for an argv of length 0, 1 or
    at least 3 are the usage walk [QmsF.ref_usage_w].  [usage_realizes] is the
    same composition for an argv whose length is not 2, over
    [BudgetWit.QRjHB.realizes]: [BudgetWit.QFOHB.Mq1.ref_startup] continued by
    [BudgetWit.QmsFB.ref_usage_w].  It holds at every limit: neither walk uses
    one.  At LPS 727298f3 the start-up reads the launch ([valid_launch], the
    Sv48 [entry_launch_ok_va]), the usage line's writev to fd 2 needs a reader
    at the far end ([in_channel_reader]), its hand-off model carries the launch's vDSO
    layer, which [BudgetWit.QRjHBRom.rz_with_vdso_no_text] drops (the binary's
    segments have no vDSO text), and the run is read over [run_segments]:
    [BudgetWit.QRjHBRom.rz_run_init] lifts the walk to the run's start before
    [QRjHB.rz_never_refused_cfg] turns it into the budget premise for every
    spurious-failure configuration ([usage_never_refused]), and
    [QRjHB.rz_never_refused] for the unconfigured run
    ([usage_never_refused_run]). *)

(** The start model's two layers commute (QHdY.v's [with_tid_with_vdso]). *)
Lemma with_tid_with_vdso : forall t v m, with_tid t (with_vdso v m) = with_vdso v (with_tid t m).
Proof. intros t v []. reflexivity. Qed.

Theorem usage_realizes : forall (lim : Z) (sp brk mbase : word) (rnd : EntryDraw) (inp : ProcInput),
  valid_sp sp -> valid_brk Plain.M.loaded_segments brk ->
  valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
  entry_stack_fits sp (in_argv inp) (in_envp inp) ->
  (* LPS 727298f3: the launch (valid_input_abort's valid_launch, valid_entry's fifth conjunct) *)
  valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp ->
  (* LPS 727298f3: the far end of the standard channels reads (valid_input_abort's in_channel_reader) *)
  in_channel_reader inp = true ->
  (length (in_argv inp) <> 2)%nat ->
  exists T, realizes Plain.M.loaded_segments
    (init_config Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs sp brk mbase rnd lim inp) T.
Proof.
intros lim sp brk mbase rnd inp Hsp Hbrk Hva Hve Hfit Hvl Hlau Hrdr Hargc.
eexists.
apply (QFOHB.Mq1.ref_startup sp brk mbase rnd lim inp _ Hsp);
  [exact Hbrk| exact Hva| exact Hve| exact Hvl| exact Hlau|].
intros tid regs mem Htid ME.
(* the hand-off model carries the launch's vDSO layer; the usage walk is over the binary's segments,
   which have no vDSO text, so the layer is dropped (as QHdY.drv_start_spec_lim) *)
unfold init_config. cbn [cfg_model].
rewrite with_tid_with_vdso.
refine (QRjHBRom.rz_with_vdso_no_text Plain.M.loaded_segments eq_refl
  (mkCfg (mkst regs (0x209c0 : word) mem (seg_rom Plain.M.loaded_segments))
    (with_tid tid (init_model (segments_reserved Plain.M.loaded_segments) brk mbase sp lim inp)))
  _ _ _).
rewrite <- (init_model_C_of inp rnd sp Hsp).
apply (QmsFB.ref_usage_w sp (in_argv inp) (in_envp inp) tid regs mem brk mbase (in_fs inp) (in_stdin inp)
         lim Hva Hve Hsp Htid inp (0x20874 : word) ME); [exact Hargc | exact Hfit | exact Hrdr].
Qed.

(** On every valid entry of the plain build and every input whose argv has
    not two entries, no configuration of the run is refused by the budget,
    whatever the spurious-failure configuration and the limit.  Stated for
    the abort-modelled inputs the agreement statements quantify over. *)
Theorem usage_never_refused : forall en inp,
  valid_entry OSSVerify.json_c.json_object_fuzzer.Images.plain en inp -> valid_input_abort inp ->
  (length (in_argv inp) <> 2)%nat ->
  forall (cfg : SpuriousCfg) (lim : Z),
  ~ run_scfg_budget_refused cfg OSSVerify.json_c.json_object_fuzzer.Images.plain lim en inp.
Proof.
intros [sp brk mbase rnd] inp Hen Hinp Hlen cfg lim.
pose proof (valid_input_abort_va_size _ Hinp) as Hsz.
destruct (valid_input_either_of_valid_input_abort _ Hinp)
  as (Hva & Hve & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hvl & Hrdr & _).
pose proof (proj1 (valid_entry_sv48 _ _ _ Hsz) Hen) as Hv.
unfold OSSVerify.json_c.json_object_fuzzer.Images.plain in Hv. cbv beta iota in Hv.
destruct Hv as (Hsp & Hbrk & _ & Hfit & Hlau).
destruct (usage_realizes lim sp brk mbase rnd inp Hsp Hbrk Hva Hve Hfit Hvl Hlau Hrdr Hlen) as [T HT].
(* LPS 727298f3: the run is read over [run_segments]; the walk lifts to the run's start *)
exact (rz_never_refused_cfg (run_segments Plain.M.loaded_segments inp sp mbase) cfg _ _
         (QRjHBRom.rz_run_init Plain.M.loaded_segments inp sp mbase _ _ _ _ _ _ eq_refl HT)).
Qed.

(** The same for the unconfigured run ([Run.run_budget_refused]). *)
Theorem usage_never_refused_run : forall en inp,
  valid_entry OSSVerify.json_c.json_object_fuzzer.Images.plain en inp -> valid_input_abort inp ->
  (length (in_argv inp) <> 2)%nat ->
  forall (lim : Z),
  ~ run_budget_refused OSSVerify.json_c.json_object_fuzzer.Images.plain lim en inp.
Proof.
intros [sp brk mbase rnd] inp Hen Hinp Hlen lim.
pose proof (valid_input_abort_va_size _ Hinp) as Hsz.
destruct (valid_input_either_of_valid_input_abort _ Hinp)
  as (Hva & Hve & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hvl & Hrdr & _).
pose proof (proj1 (valid_entry_sv48 _ _ _ Hsz) Hen) as Hv.
unfold OSSVerify.json_c.json_object_fuzzer.Images.plain in Hv. cbv beta iota in Hv.
destruct Hv as (Hsp & Hbrk & _ & Hfit & Hlau).
destruct (usage_realizes lim sp brk mbase rnd inp Hsp Hbrk Hva Hve Hfit Hvl Hlau Hrdr Hlen) as [T HT].
exact (rz_never_refused (run_segments Plain.M.loaded_segments inp sp mbase) _ _
         (QRjHBRom.rz_run_init Plain.M.loaded_segments inp sp mbase _ _ _ _ _ _ eq_refl HT)).
Qed.
