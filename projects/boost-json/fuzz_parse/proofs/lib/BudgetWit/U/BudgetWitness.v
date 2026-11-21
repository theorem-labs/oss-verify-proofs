(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from BudgetWit/BudgetWitness.v for the ubsan build: U/RefStartup.v's ref_startup and the argc <> 2 branch of U/MainTop.v's main_realizes, over BudgetWit.Rzb.realizes; adds the budget-premise witness for the ubsan build and the lemma that applies the released proof of the one statement whose budget premise is on the ubsan build. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: the launch premises valid_launch, entry_launch_ok_va and the channel reader; the usage walk lifted to the run over run_segments, its read-only backing and its vDSO layer, with the entry fact over the canonical input; changed usage_realizes, usage_never_refused, ubsan_witness_entry. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.Core Require Premises.
From OSSVerify.Core Require Images.
From OSSVerify.boost_json.fuzz_parse Require Images Statements.
From OSSVerify.boost_json.fuzz_parse.images Require Import Ubsan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import Amb PropExec Scfg ShapeAlg Spec.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.U Require Import MainDefs RefStartup.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Theorems.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.BudgetWit.Rzb OSSVerify.Proofs.boost_json.fuzz_parse.lib.BudgetWit.U.RStB OSSVerify.Proofs.boost_json.fuzz_parse.lib.BudgetWit.U.MTB.
From LinuxProcessSemantics.LinuxProcessSem Require VdsoCommute VdsoCommuteSys.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Common.Cfg Require RomBase RomStable.
Import ListNotations.
Unset Lia Cache.
Open Scope Z_scope.

(** * boost-json / fuzz_parse: the budget premise on the ubsan build holds together with the other premises

    One statement of [Statements] carries a budget premise on the ubsan build,
    [~ run_scfg_budget_refused cfg Images.ubsan lim en inp]: [ubsan_halts]
    ([halts_within_budget]), at [forced_only_cfg] and [Budgets.Standard.lim_source].
    A theorem whose premises never hold together proves nothing.
    [OSSVerify.Core.Premises] gives the entry and input premises for every
    well-formed image and leaves the budget premise, which reads the run; this
    file gives it for this build, for every configuration and every limit.

    The input is [Premises.witness_input false]: one empty argument (so argc = 1),
    no environment, an empty file system.  With argc <> 2 the driver's [main]
    writes its usage line to fd 2 and exits with status 2.  On that path the
    program makes three kinds of system call: set_tid_address (96) in musl's
    start-up, writev (66) for the line, exit or exit_group (93, 94).  None is an
    allocation call (brk 214, mremap 216, mmap 222, mprotect 226), so no
    configuration the run reaches is refused by the budget.  This shows the budget
    premise satisfiable on the usage path, not yet on an input that reaches
    [LLVMFuzzerTestOneInput].

    The proof is the released proof of that path on the ubsan build
    ([U.RefStartup.ref_startup], then [U.MainTop.ref_usage], the argc <> 2 branch
    of [U.MainTop.main_realizes]) restated over [BudgetWit.Rzb.realizes], the
    carrier the plain witness uses ([BudgetWit.Rzb] says why [ShapeAlg.realizes]
    itself cannot carry the fact).  [usage_realizes] is that walk;
    [Rzb.realizes_never_refused_cfg] turns it into the budget premise, for every
    spurious-failure configuration and every limit ([usage_never_refused]).
    [ubsan_halts_not_vacuous] gives the premises of [ubsan_halts] at one input to
    the released proof of that statement (the term its
    [proofs/ubsan_halts/Proof.v] is), so the statement's conclusion holds at a
    point that meets all its premises, with no hypothesis left. *)

(** The ubsan build's start-up ([U.RStB.ref_startup]), then [main]'s usage path
    ([U.MTB.ref_usage]), over [Rzb.realizes].  LPS 727298f3: the run walks
    [run_segments] (the binary's segments with the run's vDSO pair), and the
    start-up hands off at main with the run's backing and vDSO layer; the usage walk
    over the binary's own segments is lifted to it as U/RefTop.v
    [ref_realizes_spec_at] lifts the main phase ([Rzb.realizes_run_segments],
    [Rzb.realizes_wrom], [Rzb.realizes_with_vdso_no_text]).  The model is then
    [U.MainDefs.model0] at the input [mkProcInputC] rebuilds from [amb_of inp] by
    computation, and the entry fact is rebuilt over that input field by field. *)
Lemma usage_realizes : forall sp brk mbase (rnd : EntryDraw) lim inp,
  valid_sp sp -> valid_brk Ubsan.M.loaded_segments brk ->
  valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
  entry_stack_fits sp (in_argv inp) (in_envp inp) ->
  valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp ->
  in_channel_reader inp = true ->
  (length (in_argv inp) <> 2)%nat ->
  Rzb.realizes (run_segments Ubsan.M.loaded_segments inp sp mbase)
      (init_config (run_segments Ubsan.M.loaded_segments inp sp mbase) Ubsan.M.init_pc Ubsan.M.phdrs
         sp brk mbase rnd lim inp)
      (t_die (msg_usage (hd [] (in_argv inp))) (in_fs inp)).
Proof.
  intros sp brk mbase rnd lim inp Hsp Hbrk Hva Hve Hfit Hvl Hlau Hrdr Hlen.
  apply (U.RStB.ref_startup sp brk mbase rnd lim inp _ Hsp Hbrk Hva Hve Hvl Hlau).
  intros tid regs mem Htid ME.
  rewrite RomStable.segments_reserved_run_segments.
  rewrite VdsoCommute.with_tid_with_vdso.
  assert (Hvi : vdso_image Ubsan.M.loaded_segments = None) by (vm_compute; reflexivity).
  apply (Rzb.realizes_run_segments Ubsan.M.loaded_segments inp sp mbase _ _ Hvi).
  lazymatch goal with |- Rzb.realizes _ (mkCfg (@mkst ?f ?r ?pc ?m _) ?M) ?T =>
    change (Rzb.realizes Ubsan.M.loaded_segments
              (RomBase.cwrom (mkCfg (@mkst f r pc m (seg_rom Ubsan.M.loaded_segments)) M)
                 (RomStable.seg_rom1 (run_segments Ubsan.M.loaded_segments inp sp mbase))) T) end.
  apply (Rzb.realizes_wrom Ubsan.M.loaded_segments Hvi);
    [| exact (RomStable.rom_ext_run_segments Ubsan.M.loaded_segments inp sp mbase)].
  lazymatch goal with |- Rzb.realizes ?s (mkCfg ?ms (with_vdso ?v ?m)) ?T =>
    change (Rzb.realizes s (VdsoCommuteSys.cfg_with_vdso v (mkCfg ms m)) T) end.
  apply (Rzb.realizes_with_vdso_no_text Ubsan.M.loaded_segments ltac:(vm_compute; reflexivity)).
  match goal with |- Rzb.realizes _ (mkCfg (mkst _ ?pc _ _) _) _ =>
    replace pc with (Z_to_bv 64 0x46fe4 : word) by (apply bv_eq; reflexivity) end.
  change (with_tid tid (init_model (segments_reserved Ubsan.M.loaded_segments) brk mbase sp lim inp))
    with (OSSVerify.Proofs.boost_json.fuzz_parse.lib.U.MainDefs.model0 tid brk mbase sp lim
            (@mkProcInputC (amb_of inp) (in_argv inp) (in_envp inp) (in_fs inp) (in_stdin inp))).
  assert (ME' : @main_entry (amb_of inp)
                  (@mkProcInputC (amb_of inp) (in_argv inp) (in_envp inp) (in_fs inp) (in_stdin inp))
                  mbase (Z_to_bv 64 290456) sp rnd tid regs mem)
    by (destruct ME; constructor; assumption).
  assert (Hvl' : valid_launch
                   (@mkProcInputC (amb_of inp) (in_argv inp) (in_envp inp) (in_fs inp) (in_stdin inp)))
    by exact Hvl.
  assert (Hlau' : entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd)
                    (@mkProcInputC (amb_of inp) (in_argv inp) (in_envp inp) (in_fs inp) (in_stdin inp)))
    by exact Hlau.
  assert (Hrdr' : in_channel_reader
                    (@mkProcInputC (amb_of inp) (in_argv inp) (in_envp inp) (in_fs inp) (in_stdin inp)) = true)
    by exact Hrdr.
  eapply U.MTB.ref_usage; eassumption.
Qed.

(** On every valid entry of the ubsan build and every input with valid argv and
    envp, the launch's own clauses and a reader on the channel, whose argv has not
    two entries, no configuration of the run is refused by the budget, whatever the
    spurious-failure configuration and whatever the limit. *)
Theorem usage_never_refused : forall en inp,
  valid_entry OSSVerify.boost_json.fuzz_parse.Images.ubsan en inp ->
  in_va_size inp = Sv48 ->
  valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
  valid_launch inp -> in_channel_reader inp = true ->
  (length (in_argv inp) <> 2)%nat ->
  forall (cfg : SpuriousCfg) (lim : Z),
  ~ run_scfg_budget_refused cfg OSSVerify.boost_json.fuzz_parse.Images.ubsan lim en inp.
Proof.
  intros [sp brk mbase rnd] inp Hen Hv Hva Hve Hvl Hrdr Hlen cfg lim.
  unfold OSSVerify.boost_json.fuzz_parse.Images.ubsan in Hen.
  rewrite (valid_entry_sv48 _ _ _ Hv) in Hen.
  destruct Hen as (Hsp & Hbrk & _ & Hfit & Hlau).
  exact (realizes_never_refused_cfg (run_segments Ubsan.M.loaded_segments inp sp mbase) cfg _ _
           (usage_realizes sp brk mbase rnd lim inp Hsp Hbrk Hva Hve Hfit Hvl Hlau Hrdr Hlen)).
Qed.

(** An entry of the ubsan build at [Premises.witness_input b], the entry
    [Premises.valid_input_entry] or [Premises.valid_input_abort_entry] gives for
    it, at which the budget refuses nothing, whatever the configuration and the
    limit. *)
Lemma ubsan_witness_entry : forall b, exists en,
  valid_entry OSSVerify.boost_json.fuzz_parse.Images.ubsan en (Premises.witness_input b) /\
  forall (cfg : SpuriousCfg) (lim : Z),
  ~ run_scfg_budget_refused cfg OSSVerify.boost_json.fuzz_parse.Images.ubsan lim en (Premises.witness_input b).
Proof.
  intros b.
  assert (Hen : exists en, valid_entry OSSVerify.boost_json.fuzz_parse.Images.ubsan en (Premises.witness_input b)).
  { destruct b.
    - exact (Premises.valid_input_abort_entry _ _ OSSVerify.boost_json.fuzz_parse.Images.ubsan_wf
               Premises.witness_valid_input_abort).
    - exact (Premises.valid_input_entry _ _ OSSVerify.boost_json.fuzz_parse.Images.ubsan_wf
               Premises.witness_valid_input). }
  destruct Hen as [en Hen]. exists en. split; [exact Hen |].
  (* the launch clauses and the reader are [Premises.witness_valid_input(_abort)]'s; each premise
     of [usage_never_refused] is closed from those clauses, whatever their number *)
  intros cfg lim. destruct b;
    [ pose proof Premises.witness_valid_input_abort as Hv; unfold valid_input_abort in Hv
    | pose proof Premises.witness_valid_input as Hv; unfold valid_input in Hv ];
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    apply (usage_never_refused en _ Hen); first [ reflexivity | assumption | (cbn; discriminate) ].
Qed.

(** [ubsan_halts]'s three premises hold together: at [Premises.witness_input false]
    and the entry [Premises.valid_input_entry] gives for it. *)
Theorem ubsan_budget_witness :
  exists en inp, valid_entry OSSVerify.boost_json.fuzz_parse.Images.ubsan en inp /\ valid_input inp /\
  ~ run_scfg_budget_refused forced_only_cfg OSSVerify.boost_json.fuzz_parse.Images.ubsan
      Budgets.Standard.lim_source en inp.
Proof.
  destruct (ubsan_witness_entry false) as (en & Hen & Hnr).
  exists en, (Premises.witness_input false).
  split; [exact Hen | split; [exact Premises.witness_valid_input | apply Hnr]].
Qed.

(** [Statements.ubsan_halts], which the released
    [Theorems.halts_allowed_boost_json_halts_ubsan] proves, at an entry and an
    input that meet all three of its premises: its conclusion holds there with no
    hypothesis left. *)
Theorem ubsan_halts_not_vacuous :
  exists en inp, valid_entry OSSVerify.boost_json.fuzz_parse.Images.ubsan en inp /\ valid_input inp /\
  ~ run_scfg_budget_refused forced_only_cfg OSSVerify.boost_json.fuzz_parse.Images.ubsan
      Budgets.Standard.lim_source en inp /\
  must_exit_in_scfg forced_only_cfg Exits.ok_or_refused OSSVerify.boost_json.fuzz_parse.Images.ubsan
      Budgets.Standard.lim_source en inp.
Proof.
  destruct ubsan_budget_witness as (en & inp & Hen & Hinp & Hnr).
  exists en, inp. split; [exact Hen | split; [exact Hinp | split; [exact Hnr |]]].
  exact ((OSSVerify.Proofs.boost_json.fuzz_parse.lib.Theorems.halts_allowed_boost_json_halts_ubsan
            : OSSVerify.boost_json.fuzz_parse.Statements.ubsan_halts) en inp Hen Hinp Hnr).
Qed.
