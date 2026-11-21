(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from UTop.v's plain_realizes_lim with the argc <> 2 branch of plain_main in place of the whole main phase, over BudgetWit.Rzb.rzb; adds the budget-premise witness for the UBSan build and the lemma that applies the released proof of ubsan_halts. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch's ProcInput; the launch premises valid_launch and entry_launch_ok_va; the channel-reader premise of writev; the run's segment list run_segments; RomBase.sys_rob at the system-call nodes; the launch's reservations with the vDSO pair; the conjuncts of valid_input_either). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.Core Require Premises.
From OSSVerify.fast_float.from_chars Require Images Statements.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import DriverCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require RomBase RomStable PropExec.
From OSSVerify.Proofs.fast_float.from_chars.lib Require Import Spec.
From OSSVerify.Proofs.fast_float.from_chars.lib Require Theorems.
From OSSVerify.Proofs.fast_float.from_chars.lib.BudgetWit Require Import Rzb UbStartupRzB UUsageB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(** * fast_float / from_chars: the budget premise on the UBSan build holds together with the other premises

    One statement of [Statements] carries a budget premise on the UBSan build:
    [ubsan_halts] ([halts_within_budget]), at [forced_only_cfg] and
    [Budgets.Standard.lim_source], [~ run_scfg_budget_refused forced_only_cfg
    Images.ubsan lim en inp].  This file gives that premise for the UBSan build
    on the argc <> 2 usage path, for every configuration and every limit, the
    way [BudgetWitness] does for the plain build: the input is
    [Premises.witness_input false] (one empty argument, so argc = 1), the
    driver writes its usage line to fd 2 and exits with status 2, and the
    system calls on that path are set_tid_address (96), writev (66) and exit or
    exit_group (93, 94), none of them an allocation call.  This shows the budget
    premise satisfiable on the usage path, not yet on an input that reaches
    [LLVMFuzzerTestOneInput].

    The proof is the released UBSan proof of that path
    ([UbStartupRz.ub_startup_rz], then [UUsage.usage_path], as
    [UTop.plain_realizes_lim] composes them) restated over [BudgetWit.Rzb.rzb]
    ([UbStartupRzB], [UUsageB] and the files they import).  The carrier
    [BudgetWit.Rzb] and the image-independent node lemmas ([Common_*B]) are the
    plain witness's, shared: they are stated for every segment list. *)

(** [UTop.plain_realizes_lim] with the argc <> 2 branch of [UTop.plain_main]
    in place of the whole main phase, over [Rzb.rzb]: start-up
    ([UbStartupRzB.ub_startup_rz_b]), then [main]'s usage path
    ([UUsageB.usage_path_b]), for every limit.  LPS 727298f3: the usage path is lifted to
    the run's segment list at the entry of [main] ([Rzb.rzb_lift_run]), as in
    [BudgetWitness.usage_rzb]. *)
Lemma ub_usage_rzb : forall sp brk mbase (rnd : EntryDraw) lim inp,
  valid_sp sp -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
  valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp ->
  in_channel_reader inp = true ->
  entry_stack_fits sp (in_argv inp) (in_envp inp) ->
  (length (in_argv inp) <> 2)%nat ->
  Rzb.rzb (run_segments Ubsan.M.loaded_segments inp sp mbase) DCFG
    (init_config (run_segments Ubsan.M.loaded_segments inp sp mbase) Ubsan.M.init_pc Ubsan.M.phdrs
       sp brk mbase rnd lim inp)
    (t_die (msg_usage (nth 0 (in_argv inp) [])) (in_fs inp)).
Proof.
  intros sp brk mbase rnd lim inp Hsp Hva Hve Hvl Hlau Hrdi Hfit Hlen.
  apply (UbStartupRzB.ub_startup_rz_b DCFG _ sp brk mbase rnd lim inp Hsp Hva Hve Hvl Hlau).
  intros tid regs mem Htid ME.
  rewrite RomStable.init_model_run_segments.
  set (md := with_tid tid (cfg_model (init_config Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs
                                        sp brk mbase rnd lim inp))).
  lazymatch goal with
  | |- Rzb.rzb _ _ (mkCfg (@PropExec.mkst ?fx ?r ?p ?m _) _) ?T =>
      change (Rzb.rzb (run_segments Ubsan.M.loaded_segments inp sp mbase) DCFG
                (mkCfg (RomBase.wrom (@PropExec.mkst fx r p m (PropExec.seg_rom Ubsan.M.loaded_segments))
                         (RomStable.seg_rom1 (run_segments Ubsan.M.loaded_segments inp sp mbase))) md) T)
  end.
  apply Rzb.rzb_lift_run; [reflexivity | reflexivity |].
  set (md0 := with_tid tid (init_model (segments_reserved Ubsan.M.loaded_segments) brk mbase sp lim inp)).
  assert (Hfs : m_fs md = in_fs inp)
    by (change (m_fs md) with (m_fs md0); unfold md0; rewrite m_fs_with_tid, m_fs_init_model; reflexivity).
  rewrite <- Hfs.
  replace (0x228cc%bv : word) with (Z_to_bv 64 0x228cc) by (apply bv_eq; reflexivity).
  apply (UUsageB.usage_path_b inp mbase (0x22780 : word) sp brk tid rnd regs mem md
           Hsp Hva Hve Hvl Hlau Hfit ltac:(unfold PID_MAX_ENVELOPE in Htid; lia) ME Hlen).
  - change (m_halted md) with (m_halted md0). unfold md0. rewrite m_halted_with_tid, m_halted_init_model. reflexivity.
  - reflexivity.
  - change (m_fds md) with (m_fds md0). unfold md0. rewrite m_fds_with_tid, m_fds_init_model. vm_compute. reflexivity.
  - transitivity (in_channel_reader inp); [reflexivity | exact Hrdi].
Qed.

(** On every valid entry of the UBSan build and every input [valid_input_either] admits
    whose argv has not two entries, no configuration of the run is refused by the budget,
    whatever the spurious-failure configuration and whatever the limit. *)
Theorem ub_usage_never_refused : forall en inp,
  valid_entry OSSVerify.fast_float.from_chars.Images.ubsan en inp ->
  valid_input_either inp ->
  (length (in_argv inp) <> 2)%nat ->
  forall (cfg : SpuriousCfg) (lim : Z),
  ~ run_scfg_budget_refused cfg OSSVerify.fast_float.from_chars.Images.ubsan lim en inp.
Proof.
  intros [sp brk mbase rnd] inp Hen Hinp Hlen cfg lim Hr.
  (* the conjuncts of [valid_input_either] by type, as [UTop.plain_realizes_lim] takes them *)
  assert (Hrdi : in_channel_reader inp = true)
    by (clear - Hinp; red in Hinp; repeat match goal with H : _ /\ _ |- _ => destruct H end; assumption).
  assert (Hva : valid_argv (in_argv inp))
    by (clear - Hinp; red in Hinp; repeat match goal with H : _ /\ _ |- _ => destruct H end; assumption).
  assert (Hve : valid_envp (in_envp inp))
    by (clear - Hinp; red in Hinp; repeat match goal with H : _ /\ _ |- _ => destruct H end; assumption).
  assert (Hvl : valid_launch inp)
    by (clear - Hinp; red in Hinp; repeat match goal with H : _ /\ _ |- _ => destruct H end; assumption).
  assert (Hv : in_va_size inp = Sv48)
    by (clear - Hinp; red in Hinp; repeat match goal with H : _ /\ _ |- _ => destruct H end; assumption).
  unfold OSSVerify.fast_float.from_chars.Images.ubsan in Hen, Hr.
  apply (valid_entry_sv48 _ _ _ Hv) in Hen.
  destruct Hen as (Hsp & Hbrk & _ & Hfit & Hlau).
  exact (Rzb.rzb_never_refused (run_segments Ubsan.M.loaded_segments inp sp mbase) DCFG Rzb.alloc_only_off _ _
           (ub_usage_rzb sp brk mbase rnd lim inp Hsp Hva Hve Hvl Hlau Hrdi Hfit Hlen)
           (run_scfg_budget_refused_sub cfg _ lim _ inp Hr)).
Qed.

(** [ubsan_halts]'s three premises hold together: at [Premises.witness_input false]
    and the entry [Premises.valid_input_entry] gives for it. *)
Theorem ubsan_budget_witness :
  exists en inp, valid_entry OSSVerify.fast_float.from_chars.Images.ubsan en inp /\ valid_input inp /\
  ~ run_scfg_budget_refused forced_only_cfg OSSVerify.fast_float.from_chars.Images.ubsan
      Budgets.Standard.lim_source en inp.
Proof.
  destruct (Premises.valid_input_entry _ _ OSSVerify.fast_float.from_chars.Images.ubsan_wf
              Premises.witness_valid_input) as [en Hen].
  exists en, (Premises.witness_input false).
  split; [exact Hen | split; [exact Premises.witness_valid_input |]].
  apply (ub_usage_never_refused en _ Hen); [| cbn; discriminate].
  exact (valid_input_either_of_valid_input _ Premises.witness_valid_input).
Qed.

(** [Statements.ubsan_halts], which the released
    [Theorems.halts_allowed_fast_float_from_chars_halts_ubsan] proves, at an
    entry and an input that meet all three of its premises: its conclusion
    holds there with no hypothesis left. *)
Theorem ubsan_halts_not_vacuous :
  exists en inp, valid_entry OSSVerify.fast_float.from_chars.Images.ubsan en inp /\ valid_input inp /\
  ~ run_scfg_budget_refused forced_only_cfg OSSVerify.fast_float.from_chars.Images.ubsan
      Budgets.Standard.lim_source en inp /\
  must_exit_in_scfg forced_only_cfg Exits.ok_or_refused OSSVerify.fast_float.from_chars.Images.ubsan
      Budgets.Standard.lim_source en inp.
Proof.
  destruct ubsan_budget_witness as (en & inp & Hen & Hinp & Hnr).
  exists en, inp. split; [exact Hen | split; [exact Hinp | split; [exact Hnr |]]].
  exact ((OSSVerify.Proofs.fast_float.from_chars.lib.Theorems.halts_allowed_fast_float_from_chars_halts_ubsan
            : OSSVerify.fast_float.from_chars.Statements.ubsan_halts) en inp Hen Hinp Hnr).
Qed.
