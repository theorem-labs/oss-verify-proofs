(* SPDX-License-Identifier: MIT *)
(* Theorem Labs, 2026-11 (LPS 727298f3): walks over a binary's own segments, lifted to the run's
   start, for [StoreOk.ShapeAlg.realizes] and for the budget carrier [BudgetWit.Rzb.RzbAlg.rzb].

   At LPS 727298f3 [run_scfg] reads a binary against [run_segments segs inp sp mb]
   = [segs ++ vdso_segments ..], from [init_config (run_segments ..) ..].  That configuration
   differs from [init_config segs ..] in ONE field: the read-only backing [ms_rom], which also
   reads the vDSO text (Run.v, [init_machine_state]).  [segments_reserved] drops the pair (a
   kernel map), so the model is the same.

   No machine step reads [ms_rom].  Only a system call reads it, through [sys_input]'s
   [in_mem] := [ms_read_byte].  So a walk transfers to a larger backing when, at each of its
   nodes, the system call's specification does not change when [in_mem] gains bytes
   ([RomBase.sys_rob], the third conjunct of [ShapeAlg.node_ok]).

   Part 1: a change of the backing ([realizes_wrom], [rzb_wrom]).  Part 2, the run's segment
   list, is [Common/RunSegs.v] ([realizes_run_segments]; [rzb_run_segments] here).  Part 3: the
   run's own start ([run_init], [rzb_run_init]). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase MemImageType RiscvSemantics StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CfgStep.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RomBase.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RunSegs.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BudgetWit.Rzb.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CfgStep.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RomBase.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RunSegs.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(** [vdso_image segs = None] for a concrete binary segment list: none of its segments is the
    vDSO text ([vdso_text_seg] finds the first one tagged as such). *)
Ltac vdso_none :=
  first [ reflexivity | unfold vdso_image, vdso_text_seg; vm_compute; reflexivity ].

(** * Part 1: a change of the read-only backing *)

Definition rep_wrom (x : machine_result (access_report machine_state)) (r : word -> option byte)
    : machine_result (access_report machine_state) :=
  match x with
  | MachineOk rep => MachineOk (@mkAccessReport machine_state (wrom (@access_value _ rep) r) (@accessed_ranges _ rep))
  | MachineFault => MachineFault
  | MachineUnmodeled => MachineUnmodeled
  end.

Section Seg.
Variable segs : list Segment.

Lemma decode_exec_accesses_wrom : forall st w r,
  decode_exec_accesses segs (wrom st r) w = rep_wrom (decode_exec_accesses segs st w) r.
Proof.
  intros st w r. unfold decode_exec_accesses.
  destruct (is_ecall w); [reflexivity|].
  destruct (decode_any w) as [[i isz]|]; [| destruct (is_defined_illegal w); reflexivity].
  assert (E1 : ms_regs (wrom st r) = ms_regs st) by reflexivity.
  assert (E2 : ms_fregs (wrom st r) = ms_fregs st) by reflexivity.
  assert (E3 : ms_pc_val (wrom st r) = ms_pc_val st) by reflexivity.
  assert (E4 : ms_fcsr (wrom st r) = ms_fcsr st) by reflexivity.
  assert (E5 : ms_resv (wrom st r) = ms_resv st) by reflexivity.
  assert (E6 : ms_mem (wrom st r) = ms_mem st) by reflexivity.
  rewrite ?E1, ?E2, ?E3, ?E4, ?E5, ?E6.
  destruct (interp_eff_accesses segs _ (ms_mem st)) as [rep| |]; [|reflexivity|reflexivity].
  destruct rep as [[c m'] acc]. reflexivity.
Qed.

Lemma step_accesses_wrom : forall st r,
  step_accesses segs (wrom st r) = rep_wrom (step_accesses segs st) r.
Proof.
  intros st r. unfold step_accesses.
  assert (Ep : ms_pc (wrom st r) = ms_pc st) by reflexivity.
  assert (Em : ms_mem (wrom st r) = ms_mem st) by reflexivity.
  rewrite ?Ep, ?Em.
  destruct (fetch_word segs (ms_pc st)) as [w|]; [apply decode_exec_accesses_wrom|].
  destruct (fetch_word_ov segs (ms_mem st) (ms_pc st)) as [w|]; [apply decode_exec_accesses_wrom|].
  destruct (fetch_tail_any segs (ms_mem st) (ms_pc st)) as [w|]; [apply decode_exec_accesses_wrom|].
  destruct (fetch_failure segs (ms_mem st) (ms_pc st)) eqn:Ef; [|reflexivity|reflexivity].
  exfalso. revert Ef. unfold fetch_failure. cbv zeta.
  repeat match goal with |- context [if ?b then _ else _] => destruct b end;
    intro Ef; discriminate Ef.
Qed.

Lemma mi_account_step_wrom : forall ms model r,
  mi_account_step segs (wrom ms r) model
  = match mi_account_step segs ms model with
    | MachineOk (ms', m') => MachineOk (wrom ms' r, m')
    | MachineFault => MachineFault
    | MachineUnmodeled => MachineUnmodeled
    end.
Proof.
  intros ms model r. unfold mi_account_step. rewrite step_accesses_wrom.
  destruct (step_accesses segs ms) as [rep| |]; cbn [rep_wrom access_value accessed_ranges];
    [|reflexivity|reflexivity].
  destruct (materialize_model_accesses model (@accessed_ranges _ rep)); reflexivity.
Qed.

Lemma mi_account_step_rom : forall ms model ms' m',
  mi_account_step segs ms model = MachineOk (ms', m') -> ms_rom ms' = ms_rom ms.
Proof.
  intros ms model ms' m' H.
  pose proof (mi_account_step_wrom ms model (ms_rom ms)) as E.
  rewrite wrom_eta, H in E. injection E as E. rewrite E. reflexivity.
Qed.

Lemma apply_effect_wrom : forall ms eff r,
  advance_past_svc (apply_effect (wrom ms r) eff) = wrom (advance_past_svc (apply_effect ms eff)) r.
Proof. reflexivity. Qed.

(** The refusal filter reads the syscall number and the specification, not [in_mem]'s bytes. *)
Lemma spurious_wrom : forall ms r x8 m eff,
  (forall o, syscall_spec (sys_input segs (wrom ms r) x8) m o <-> syscall_spec (sys_input segs ms x8) m o) ->
  spurious_refusal_cfg kit_cfg (sys_input segs (wrom ms r) x8) m eff
  <-> spurious_refusal_cfg kit_cfg (sys_input segs ms x8) m eff.
Proof.
  intros ms r x8 m eff Hs. unfold spurious_refusal_cfg.
  change (injected_family_off kit_cfg (sys_input segs (wrom ms r) x8)) with (injected_family_off kit_cfg (sys_input segs ms x8)).
  change (refusal_b (sys_input segs (wrom ms r) x8)) with (refusal_b (sys_input segs ms x8)).
  split; intros (H1 & H2 & eff' & m' & evs' & H3 & H4); (split; [exact H1|]); (split; [exact H2|]);
    exists eff', m', evs'; (split; [apply Hs; exact H3 | exact H4]).
Qed.

Lemma nspur_to_wrom : forall ms r x8 m eff,
  (forall o, syscall_spec (sys_input segs (wrom ms r) x8) m o <-> syscall_spec (sys_input segs ms x8) m o) ->
  ~ spurious_refusal_cfg kit_cfg (sys_input segs ms x8) m eff ->
  ~ spurious_refusal_cfg kit_cfg (sys_input segs (wrom ms r) x8) m eff.
Proof. intros ms r x8 m eff Hs Hn Hp. apply Hn. apply (spurious_wrom ms r x8 m eff Hs). exact Hp. Qed.

Lemma nspur_of_wrom : forall ms r x8 m eff,
  (forall o, syscall_spec (sys_input segs (wrom ms r) x8) m o <-> syscall_spec (sys_input segs ms x8) m o) ->
  ~ spurious_refusal_cfg kit_cfg (sys_input segs (wrom ms r) x8) m eff ->
  ~ spurious_refusal_cfg kit_cfg (sys_input segs ms x8) m eff.
Proof. intros ms r x8 m eff Hs Hn Hp. apply Hn. apply (spurious_wrom ms r x8 m eff Hs). exact Hp. Qed.

(** The node at the larger backing is robust too: the larger backing's own extensions are the
    original's. *)
Lemma sys_rob_wrom : forall c r, sys_rob segs c -> rom_ext (ms_rom (cfg_ms c)) r -> sys_rob segs (cwrom c r).
Proof.
  intros [ms m] r Hrob Hr r2 x8 Hr2 Hs o. unfold cwrom in *. cbn [cfg_ms cfg_model] in *.
  change (wrom (wrom ms r) r2) with (wrom ms r2).
  change (ms_svc_pending (wrom ms r)) with (ms_svc_pending ms) in Hs.
  change (ms_rom (wrom ms r)) with r in Hr2.
  cbn [cfg_ms cfg_model] in Hrob.
  rewrite (Hrob r2 x8 (rom_ext_trans _ _ _ Hr Hr2) Hs o).
  symmetry. exact (Hrob r x8 Hr Hs o).
Qed.

Hypothesis Hvi : vdso_image segs = None.

Lemma vdso_entry_fn_none_seg : forall pc, vdso_entry_fn segs pc = None.
Proof. intros pc. unfold vdso_entry_fn. rewrite Hvi. reflexivity. Qed.

Lemma sstep_cfg_next_rom : forall c e c',
  sstep_cfg segs kit_cfg c e (SNext c') -> ms_rom (cfg_ms c') = ms_rom (cfg_ms c).
Proof.
  intros c e c' H. inversion H; subst; cbn [cfg_ms]; try reflexivity.
  all: first [ eapply mi_account_step_rom; eassumption
             | exfalso; rewrite vdso_entry_fn_none_seg in *; discriminate ].
Qed.

Lemma node_rom : forall c I evs nx, node_ok segs c I evs nx ->
  forall i, ms_rom (cfg_ms (nx i)) = ms_rom (cfg_ms c).
Proof. intros c I evs nx [Hc _] i. exact (sstep_cfg_next_rom _ _ _ (Hc i)). Qed.

(** Forward: a step from [c] is a step from [c] with a larger backing. *)
Lemma sstep_wrom_fwd : forall c e c' r,
  sys_rob segs c -> rom_ext (ms_rom (cfg_ms c)) r ->
  sstep_cfg segs kit_cfg c e (SNext c') -> sstep_cfg segs kit_cfg (cwrom c r) e (SNext (cwrom c' r)).
Proof.
  intros [ms model] e c' r Hrob Hr H. unfold cwrom. cbn [cfg_ms cfg_model] in *.
  inversion H; subst; cbn [cfg_ms cfg_model].
  - apply sstep_cfg_instr; [assumption | assumption |].
    rewrite mi_account_step_wrom.
    match goal with Hm : mi_account_step _ _ _ = MachineOk _ |- _ => rewrite Hm end. reflexivity.
  - exfalso. rewrite vdso_entry_fn_none_seg in *. discriminate.
  - rewrite <- apply_effect_wrom.
    assert (Hs : forall o, syscall_spec (sys_input segs (wrom ms r) x8) model o <-> syscall_spec (sys_input segs ms x8) model o)
      by (intros o; exact (Hrob r x8 Hr ltac:(assumption) o)).
    eapply sstep_cfg_syscall; [eassumption | eassumption | apply Hs; eassumption
                               | apply (nspur_to_wrom _ _ _ _ _ Hs); assumption | eassumption | eassumption].
  - assert (Hs : forall o, syscall_spec (sys_input segs (wrom ms r) x8) model o <-> syscall_spec (sys_input segs ms x8) model o)
      by (intros o; exact (Hrob r x8 Hr ltac:(assumption) o)).
    eapply sstep_cfg_exit; [eassumption | eassumption | apply Hs; eassumption | eassumption | eassumption].
  - assert (Hs : forall o, syscall_spec (sys_input segs (wrom ms r) x8) model o <-> syscall_spec (sys_input segs ms x8) model o)
      by (intros o; exact (Hrob r x8 Hr ltac:(assumption) o)).
    eapply sstep_cfg_killed; [eassumption | eassumption | apply Hs; eassumption | eassumption].
Qed.

(** Backward: every step from the larger backing is one from [c], mapped. *)
Lemma sstep_wrom_back : forall c e st r,
  sys_rob segs c -> rom_ext (ms_rom (cfg_ms c)) r ->
  sstep_cfg segs kit_cfg (cwrom c r) e st ->
  exists st0, sstep_cfg segs kit_cfg c e st0
         /\ st = match st0 with SNext c0 => SNext (cwrom c0 r) | SError => SError end.
Proof.
  intros [ms model] e st r Hrob Hr H. unfold cwrom in H. cbn [cfg_ms cfg_model] in *.
  assert (Hs : forall x8, ms_svc_pending ms = Some x8 ->
            forall o, syscall_spec (sys_input segs (wrom ms r) x8) model o <-> syscall_spec (sys_input segs ms x8) model o)
    by (intros x8 Hx o; exact (Hrob r x8 Hr Hx o)).
  remember (wrom ms r) as ms2 eqn:E2.
  inversion H; subst.
  - match goal with Hm : mi_account_step _ (wrom ms r) _ = MachineOk (?a, ?b) |- _ =>
      rewrite mi_account_step_wrom in Hm;
      destruct (mi_account_step segs ms model) as [[ms1 m1]| |] eqn:Em; try discriminate Hm;
      injection Hm as <- <- end.
    exists (SNext (mkCfg ms1 m1)). split; [apply sstep_cfg_instr; assumption | reflexivity].
  - match goal with Hm : mi_account_step _ (wrom ms r) _ = MachineFault |- _ =>
      rewrite mi_account_step_wrom in Hm;
      destruct (mi_account_step segs ms model) as [[ms1 m1]| |] eqn:Em; try discriminate Hm end.
    exists SError. split; [apply sstep_cfg_instr_fault; assumption | reflexivity].
  - match goal with Hm : mi_account_step _ (wrom ms r) _ = MachineUnmodeled |- _ =>
      rewrite mi_account_step_wrom in Hm;
      destruct (mi_account_step segs ms model) as [[ms1 m1]| |] eqn:Em; try discriminate Hm end.
    exists SError. split; [apply sstep_cfg_instr_unmodeled; assumption | reflexivity].
  - exfalso. rewrite vdso_entry_fn_none_seg in *. discriminate.
  - exfalso. rewrite vdso_entry_fn_none_seg in *. discriminate.
  - exfalso. rewrite vdso_entry_fn_none_seg in *. discriminate.
  - exists (SNext (mkCfg (advance_past_svc (apply_effect ms eff)) model'')).
    split; [| reflexivity].
    pose proof (Hs x8 ltac:(assumption)) as Hx.
    eapply sstep_cfg_syscall; [eassumption | eassumption | apply Hx; eassumption
                               | apply (nspur_of_wrom _ _ _ _ _ Hx); assumption | eassumption | eassumption].
  - exists SError. split; [| reflexivity].
    pose proof (Hs x8 ltac:(assumption)) as Hx.
    eapply sstep_cfg_syscall_materialization_fault; [eassumption | eassumption | apply Hx; eassumption
                               | apply (nspur_of_wrom _ _ _ _ _ Hx); assumption | eassumption | eassumption].
  - exists (SNext (mkCfg ms model')). split; [| reflexivity].
    pose proof (Hs x8 ltac:(assumption)) as Hx.
    eapply sstep_cfg_exit; [eassumption | eassumption | apply Hx; eassumption | eassumption | eassumption].
  - exists (SNext (mkCfg ms model')). split; [| reflexivity].
    pose proof (Hs x8 ltac:(assumption)) as Hx.
    eapply sstep_cfg_killed; [eassumption | eassumption | apply Hx; eassumption | eassumption].
  - exists SError. split; [| reflexivity].
    pose proof (Hs x8 ltac:(assumption)) as Hx.
    eapply sstep_cfg_syscall_unmodeled; [eassumption | eassumption | apply Hx; eassumption].
Qed.

Lemma node_wrom : forall c I evs nx r,
  node_ok segs c I evs nx -> rom_ext (ms_rom (cfg_ms c)) r ->
  node_ok segs (cwrom c r) I evs (fun i => cwrom (nx i) r).
Proof.
  intros c I evs nx r [Hc [Hb Hrob]] Hr. split; [|split].
  - intros i. exact (sstep_wrom_fwd c (evs i) (nx i) r Hrob Hr (Hc i)).
  - intros e st Hst.
    destruct (sstep_wrom_back c e st r Hrob Hr Hst) as (st0 & H0 & ->).
    destruct (Hb e st0 H0) as (i & -> & ->). exists i. split; reflexivity.
  - exact (sys_rob_wrom c r Hrob Hr).
Qed.

Theorem realizes_wrom : forall c T, realizes segs c T ->
  forall r, rom_ext (ms_rom (cfg_ms c)) r -> realizes segs (cwrom c r) T.
Proof.
  intros c T H; induction H as [c I evs nx T i0 Hn Hc IH | c Hh | c T T' H IH Heq]; intros r Hr.
  - apply (rz_node segs (cwrom c r) I evs (fun i => cwrom (nx i) r) T i0).
    + exact (node_wrom c I evs nx r Hn Hr).
    + intros i. apply IH. rewrite (node_rom c I evs nx Hn i). exact Hr.
  - apply rz_halt. exact Hh.
  - eapply rz_conseq; [apply IH; exact Hr | exact Heq].
Qed.

(** The same for the budget carrier: its extra premise [grant_ok] reads only the pending
    system call's number, which the backing does not touch. *)
Theorem rzb_wrom : forall c T, BudgetWit.Rzb.RzbAlg.rzb segs c T ->
  forall r, rom_ext (ms_rom (cfg_ms c)) r -> BudgetWit.Rzb.RzbAlg.rzb segs (cwrom c r) T.
Proof.
  intros c T H; induction H as [c I evs nx T i0 Hn Hg Hc IH | c Hh | c T T' H IH Heq]; intros r Hr.
  - apply (BudgetWit.Rzb.RzbAlg.rzb_node segs (cwrom c r) I evs (fun i => cwrom (nx i) r) T i0).
    + exact (node_wrom c I evs nx r Hn Hr).
    + exact Hg.
    + intros i. apply IH. rewrite (node_rom c I evs nx Hn i). exact Hr.
  - apply BudgetWit.Rzb.RzbAlg.rzb_halt. exact Hh.
  - eapply BudgetWit.Rzb.RzbAlg.rzb_conseq; [apply IH; exact Hr | exact Heq].
Qed.

End Seg.

(** * Part 2 for the budget carrier: the run's segment list ([Common/RunSegs.v]) *)

Section RzbTail.
  Variables segs tail : list Segment.
  Hypothesis Hnx : forall s, In s tail -> seg_executable s = false.
  Hypothesis Hnw : forall s, In s tail -> seg_writable s = false.
  Hypothesis Hvi : vdso_image segs = None.

  Theorem rzb_app_tail : forall c T, BudgetWit.Rzb.RzbAlg.rzb segs c T -> BudgetWit.Rzb.RzbAlg.rzb (segs ++ tail) c T.
  Proof.
    intros c T H; induction H as [c I evs nx T i0 Hn Hg Hc IH | c Hh | c T T' H IH Heq].
    - apply (BudgetWit.Rzb.RzbAlg.rzb_node (segs ++ tail) c I evs nx T i0); [| exact Hg | exact IH].
      eapply node_ok_app_tail; eassumption.
    - exact (BudgetWit.Rzb.RzbAlg.rzb_halt (segs ++ tail) c Hh).
    - exact (BudgetWit.Rzb.RzbAlg.rzb_conseq (segs ++ tail) c T T' IH Heq).
  Qed.
End RzbTail.

Theorem rzb_run_segments : forall segs inp (sp mb : word) c T,
  vdso_image segs = None ->
  BudgetWit.Rzb.RzbAlg.rzb segs c T -> BudgetWit.Rzb.RzbAlg.rzb (run_segments segs inp sp mb) c T.
Proof.
  intros segs inp sp mb c T Hvi H. unfold run_segments.
  apply rzb_app_tail;
    [ intros s Hs; exact (vdso_segments_nx _ _ _ s Hs)
    | intros s Hs; exact (vdso_segments_nw _ _ _ s Hs)
    | exact Hvi | exact H ].
Qed.

(** * Part 3: the run's own start *)

Definition seg_rom1 (segs : list Segment) : word -> option byte :=
  fun addr => match memory_read segs addr 1 with Some (b :: _) => Some b | _ => None end.

Lemma rom_ext_run_segments : forall segs inp (sp mb : word),
  rom_ext (seg_rom1 segs) (seg_rom1 (run_segments segs inp sp mb)).
Proof.
  intros segs inp sp mb a b. unfold seg_rom1, run_segments.
  destruct (memory_read segs a 1) as [bs|] eqn:E; [|intro H; discriminate H].
  rewrite (memory_read_app_nx segs _ _ _ _ E). intro H; exact H.
Qed.

(** The run's start configuration is the binary's with the run's backing. *)
Lemma init_config_run_segments : forall segs inp (sp mb : word) pc ph brk rnd lim,
  init_config (run_segments segs inp sp mb) pc ph sp brk mb rnd lim inp
  = cwrom (init_config segs pc ph sp brk mb rnd lim inp) (seg_rom1 (run_segments segs inp sp mb)).
Proof.
  intros segs inp sp mb pc ph brk rnd lim. unfold init_config, cwrom.
  cbn [cfg_ms cfg_model]. rewrite segments_reserved_run_segments. reflexivity.
Qed.

Lemma init_config_rom : forall segs inp (sp : word) mb pc ph brk rnd lim,
  ms_rom (cfg_ms (init_config segs pc ph sp brk mb rnd lim inp)) = seg_rom1 segs.
Proof. reflexivity. Qed.

(** A walk over the binary's own segments is one over the run's, from the run's start. *)
Theorem run_init : forall segs inp (sp mb : word) pc ph brk rnd lim T,
  vdso_image segs = None ->
  realizes segs (init_config segs pc ph sp brk mb rnd lim inp) T ->
  realizes (run_segments segs inp sp mb)
    (init_config (run_segments segs inp sp mb) pc ph sp brk mb rnd lim inp) T.
Proof.
  intros segs inp sp mb pc ph brk rnd lim T Hvi H.
  rewrite init_config_run_segments.
  apply realizes_run_segments; [exact Hvi|].
  apply (realizes_wrom segs Hvi); [exact H|].
  rewrite init_config_rom. apply rom_ext_run_segments.
Qed.

(** ... and for the budget carrier. *)
Theorem rzb_run_init : forall segs inp (sp mb : word) pc ph brk rnd lim T,
  vdso_image segs = None ->
  BudgetWit.Rzb.RzbAlg.rzb segs (init_config segs pc ph sp brk mb rnd lim inp) T ->
  BudgetWit.Rzb.RzbAlg.rzb (run_segments segs inp sp mb)
    (init_config (run_segments segs inp sp mb) pc ph sp brk mb rnd lim inp) T.
Proof.
  intros segs inp sp mb pc ph brk rnd lim T Hvi H.
  rewrite init_config_run_segments.
  apply rzb_run_segments; [exact Hvi|].
  apply (rzb_wrom segs Hvi); [exact H|].
  rewrite init_config_rom. apply rom_ext_run_segments.
Qed.
