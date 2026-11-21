(* SPDX-License-Identifier: MIT *)
(* Theorem Labs, 2026-11 (LPS 08b1429): walks over a binary's own segments, lifted to the run.
   openssl/hashtable's Common/Cfg/RomStable.v, restated over this tree's [ShapeAlg.realizes]
   (filter [kit_cfg]), whose node constructor [rz_node] carries [RomBase.sys_rob].

   At 08b1429 a run reads a binary against [run_segments segs inp sp mb]
   = [segs ++ vdso_segments ..], from [init_config (run_segments ..) ..].  That configuration
   differs from [init_config segs ..] in ONE field: the read-only backing [ms_rom], which now
   also reads the vDSO pair.  [segments_reserved] drops the pair (a kernel map), so the model is
   the same, and the memory image does not read the segment list.

   No machine step reads [ms_rom]; only a system call does, through [sys_input]'s [in_mem].
   Part 1 ([realizes_wrom]) moves a walk to a larger backing, using each node's [sys_rob];
   Part 2 ([realizes_run_segments]) moves it to the run's segment list; Part 3 ([run_init])
   composes them at the run's start. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase MemImageType RiscvSemantics StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import DecodeC.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Import CfgStep ShapeAlg.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Cfg Require Import RomBase.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

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
  node_ok segs c I evs nx -> sys_rob segs c -> rom_ext (ms_rom (cfg_ms c)) r ->
  node_ok segs (cwrom c r) I evs (fun i => cwrom (nx i) r).
Proof.
  intros c I evs nx r [Hc Hb] Hrob Hr. split.
  - intros i. exact (sstep_wrom_fwd c (evs i) (nx i) r Hrob Hr (Hc i)).
  - intros e st Hst.
    destruct (sstep_wrom_back c e st r Hrob Hr Hst) as (st0 & H0 & ->).
    destruct (Hb e st0 H0) as (i & -> & ->). exists i. split; reflexivity.
Qed.

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

Theorem realizes_wrom : forall c T, realizes segs c T ->
  forall r, rom_ext (ms_rom (cfg_ms c)) r -> realizes segs (cwrom c r) T.
Proof.
  intros c T H; induction H as [c I evs nx T i0 Hn Hrob Hc IH | c Hh | c T T' H IH Heq]; intros r Hr.
  - apply (rz_node segs (cwrom c r) I evs (fun i => cwrom (nx i) r) T i0).
    + exact (node_wrom c I evs nx r Hn Hrob Hr).
    + exact (sys_rob_wrom c r Hrob Hr).
    + intros i. apply IH. rewrite (node_rom c I evs nx Hn i). exact Hr.
  - apply rz_halt. exact Hh.
  - eapply rz_conseq; [apply IH; exact Hr | exact Heq].
Qed.
End Seg.

(** * Part 2: the run's segment list (the bridge of glaze's Common/RunSegs.v, over [ShapeAlg.realizes]) *)

Lemma find_segment_app : forall segs tail addr n,
  find_segment (segs ++ tail) addr n
  = match find_segment segs addr n with
    | Some s => Some s
    | None => find_segment tail addr n
    end.
Proof.
  induction segs as [|seg rest IH]; intros tail addr n; [reflexivity|].
  cbn [find_segment app].
  destruct (Z.leb (Z.of_N (seg_base seg)) addr
            && Z.leb (addr + n) (Z.of_N (seg_base seg) + Z.of_N (seg_size seg)))%bool;
    [reflexivity | apply IH].
Qed.

Lemma find_segment_in : forall segs addr n s,
  find_segment segs addr n = Some s -> In s segs.
Proof.
  induction segs as [|seg rest IH]; intros addr n s H; [discriminate H|].
  cbn [find_segment] in H.
  destruct (Z.leb (Z.of_N (seg_base seg)) addr
            && Z.leb (addr + n) (Z.of_N (seg_base seg) + Z.of_N (seg_size seg)))%bool.
  - injection H as <-. left. reflexivity.
  - right. exact (IH _ _ _ H).
Qed.

Section AppTail.
  Variables segs tail : list Segment.
  Hypothesis Hnx : forall s, In s tail -> seg_executable s = false.
  Hypothesis Hnw : forall s, In s tail -> seg_writable s = false.

  Lemma code_read_app_nx : forall a n,
    code_read (segs ++ tail) a n = code_read segs a n.
  Proof.
    intros a n. unfold code_read. rewrite find_segment_app.
    destruct (find_segment segs (bv_unsigned a) (Z.of_N n)) as [s|]; [reflexivity|].
    destruct (find_segment tail (bv_unsigned a) (Z.of_N n)) as [s|] eqn:E; [|reflexivity].
    rewrite (Hnx s (find_segment_in _ _ _ _ E)). reflexivity.
  Qed.

  Lemma code_read_ov_app_nx : forall m a n,
    code_read_ov (segs ++ tail) m a n = code_read_ov segs m a n.
  Proof.
    intros m a n. unfold code_read_ov. rewrite find_segment_app.
    destruct (find_segment segs (bv_unsigned a) (Z.of_N n)) as [s|]; [reflexivity|].
    destruct (find_segment tail (bv_unsigned a) (Z.of_N n)) as [s|] eqn:E; [|reflexivity].
    rewrite (Hnx s (find_segment_in _ _ _ _ E)). reflexivity.
  Qed.

  Lemma fetch_word_app_nx : forall a,
    fetch_word (segs ++ tail) a = fetch_word segs a.
  Proof. intros a. unfold fetch_word. rewrite code_read_app_nx. reflexivity. Qed.

  Lemma fetch_word_ov_app_nx : forall m a,
    fetch_word_ov (segs ++ tail) m a = fetch_word_ov segs m a.
  Proof. intros m a. unfold fetch_word_ov. rewrite code_read_ov_app_nx. reflexivity. Qed.

  Lemma fetch_half_any_app_nx : forall m a,
    fetch_half_any (segs ++ tail) m a = fetch_half_any segs m a.
  Proof.
    intros m a. unfold fetch_half_any, fetch_half, fetch_half_ov.
    rewrite code_read_app_nx, code_read_ov_app_nx. reflexivity.
  Qed.

  Lemma fetch_tail_any_app_nx : forall m a,
    fetch_tail_any (segs ++ tail) m a = fetch_tail_any segs m a.
  Proof.
    intros m a. unfold fetch_tail_any. rewrite !fetch_half_any_app_nx. reflexivity.
  Qed.

  Lemma memory_read_app_nx : forall a n bs,
    memory_read segs a n = Some bs -> memory_read (segs ++ tail) a n = Some bs.
  Proof.
    intros a n bs. unfold memory_read. rewrite find_segment_app.
    destruct (find_segment segs (bv_unsigned a) (Z.of_N n)) as [s|];
      [intro H; exact H | intro H; discriminate H].
  Qed.

  Lemma ov_read_bytes_app_nx : forall n m a bs,
    ov_read_bytes segs m a n = Some bs -> ov_read_bytes (segs ++ tail) m a n = Some bs.
  Proof.
    induction n as [|n IH]; intros m a bs; cbn [ov_read_bytes]; [intro H; exact H|].
    destruct (m a) as [b|].
    - destruct (ov_read_bytes segs m (a + 1) n) as [rest|] eqn:E; [|intro H; discriminate H].
      rewrite (IH _ _ _ E). intro H; exact H.
    - destruct (memory_read segs a 1) as [[|b rest0]|] eqn:Em;
        [intro H; discriminate H | | intro H; discriminate H].
      rewrite (memory_read_app_nx _ _ _ Em).
      destruct (ov_read_bytes segs m (a + 1) n) as [rest|] eqn:E; [|intro H; discriminate H].
      rewrite (IH _ _ _ E). intro H; exact H.
  Qed.

  Lemma wview_app_nw : forall m a, wview (segs ++ tail) m a = wview segs m a.
  Proof.
    intros m a. unfold wview. destruct (m a) as [b|]; [reflexivity|].
    rewrite find_segment_app.
    destruct (find_segment segs (bv_unsigned a) 1) as [s|]; [reflexivity|].
    destruct (find_segment tail (bv_unsigned a) 1) as [s|] eqn:E; [|reflexivity].
    rewrite (Hnw s (find_segment_in _ _ _ _ E)). reflexivity.
  Qed.

  Lemma store_ok_app_nw : forall n m a,
    store_ok (segs ++ tail) m a n = store_ok segs m a n.
  Proof.
    induction n as [|n IH]; intros m a; cbn [store_ok]; [reflexivity|].
    rewrite wview_app_nw. destruct (wview segs m a); [apply IH | reflexivity].
  Qed.

  Lemma interp_eff_accesses_app_nx : forall t m r,
    interp_eff_accesses segs t m = MachineOk r ->
    interp_eff_accesses (segs ++ tail) t m = MachineOk r.
  Proof.
    induction t as [c|c|c|c|c|c|n a k IH|n a v k IH]; intros m r;
      cbn [interp_eff_accesses]; try (intro H; exact H).
    - destruct (ov_read_bytes segs m a (width_bytes n)) as [bs|] eqn:E.
      + rewrite (ov_read_bytes_app_nx _ _ _ _ E).
        match goal with
        | |- context [interp_eff_accesses segs ?t' ?m'] =>
            destruct (interp_eff_accesses segs t' m') as [rep| |] eqn:E2;
              [| intro H; discriminate H | intro H; discriminate H]
        end.
        rewrite (IH _ _ _ E2). intro H; exact H.
      + destruct (range_meets_vvar segs a (width_bytes n)); intro H; discriminate H.
    - rewrite store_ok_app_nw.
      destruct (store_ok segs m a (width_bytes n)) eqn:E; [|intro H; discriminate H].
      match goal with
      | |- context [interp_eff_accesses segs k ?m'] =>
          destruct (interp_eff_accesses segs k m') as [rep| |] eqn:E2;
            [| intro H; discriminate H | intro H; discriminate H]
      end.
      rewrite (IH _ _ E2). intro H; exact H.
  Qed.

  Lemma decode_exec_accesses_app_nx : forall st w rep,
    decode_exec_accesses segs st w = MachineOk rep ->
    decode_exec_accesses (segs ++ tail) st w = MachineOk rep.
  Proof.
    intros st w rep. unfold decode_exec_accesses.
    destruct (is_ecall w); [intro H; exact H|].
    destruct (decode_any w) as [[i isz]|]; [|intro H; exact H].
    match goal with
    | |- context [interp_eff_accesses segs ?t ?m] =>
        destruct (interp_eff_accesses segs t m) as [r| |] eqn:E;
          [rewrite (interp_eff_accesses_app_nx _ _ _ E); intro H; exact H
          | intro H; discriminate H | intro H; discriminate H]
    end.
  Qed.

  Lemma step_accesses_app_nx : forall st rep,
    step_accesses segs st = MachineOk rep ->
    step_accesses (segs ++ tail) st = MachineOk rep.
  Proof.
    intros st rep. unfold step_accesses.
    rewrite fetch_word_app_nx, fetch_word_ov_app_nx, fetch_tail_any_app_nx.
    destruct (fetch_word segs (ms_pc st)) as [w|]; [apply decode_exec_accesses_app_nx|].
    destruct (fetch_word_ov segs (ms_mem st) (ms_pc st)) as [w|];
      [apply decode_exec_accesses_app_nx|].
    destruct (fetch_tail_any segs (ms_mem st) (ms_pc st)) as [w|];
      [apply decode_exec_accesses_app_nx|].
    destruct (fetch_failure segs (ms_mem st) (ms_pc st)) eqn:Ef;
      [| intro H; discriminate H | intro H; discriminate H].
    exfalso. revert Ef. unfold fetch_failure. cbv zeta.
    repeat match goal with |- context [if ?b then _ else _] => destruct b end;
      intro Ef; discriminate Ef.
  Qed.

  Lemma mi_account_step_app_nx : forall ms model r,
    mi_account_step segs ms model = MachineOk r ->
    mi_account_step (segs ++ tail) ms model = MachineOk r.
  Proof.
    intros ms model r. unfold mi_account_step.
    destruct (step_accesses segs ms) as [rep| |] eqn:E;
      [rewrite (step_accesses_app_nx _ _ E); intro H; exact H
      | intro H; discriminate H | intro H; discriminate H].
  Qed.

  Lemma sys_input_app_nw : forall ms x8,
    sys_input (segs ++ tail) ms x8 = sys_input segs ms x8.
  Proof.
    intros ms x8. unfold sys_input. f_equal.
    apply functional_extensionality. intro a. unfold ms_writable_byte. apply wview_app_nw.
  Qed.

  Hypothesis Hvi : vdso_image segs = None.

  Lemma vdso_entry_fn_none : forall pc, vdso_entry_fn segs pc = None.
  Proof. intros pc. unfold vdso_entry_fn. rewrite Hvi. reflexivity. Qed.

  
  Lemma sstep_cfg_app_next : forall c e c',
    sstep_cfg segs kit_cfg c e (SNext c') -> sstep_cfg (segs ++ tail) kit_cfg c e (SNext c').
  Proof.
    intros c e c' H. inversion H; subst.
    - eapply sstep_cfg_instr; [assumption | assumption |].
      apply mi_account_step_app_nx. assumption.
    - exfalso. rewrite vdso_entry_fn_none in *. discriminate.
    - eapply sstep_cfg_syscall; rewrite ?sys_input_app_nw; eassumption.
    - eapply sstep_cfg_exit; rewrite ?sys_input_app_nw; eassumption.
    - eapply sstep_cfg_killed; rewrite ?sys_input_app_nw; eassumption.
  Qed.

  Lemma sstep_cfg_app_back : forall ms model e st,
    (ms_svc_pending ms = None -> exists r, mi_account_step segs ms model = MachineOk r) ->
    sstep_cfg (segs ++ tail) kit_cfg (mkCfg ms model) e st ->
    sstep_cfg segs kit_cfg (mkCfg ms model) e st.
  Proof.
    intros ms model e st Hok H. inversion H; subst.
    - destruct (Hok ltac:(assumption)) as (r & Hr).
      pose proof (mi_account_step_app_nx _ _ _ Hr) as Hr'.
      match goal with Hb : mi_account_step (_ ++ _) _ _ = MachineOk _ |- _ =>
        rewrite Hr' in Hb; injection Hb as Hb'; subst r end.
      eapply sstep_cfg_instr; eassumption.
    - exfalso. destruct (Hok ltac:(assumption)) as (r & Hr).
      pose proof (mi_account_step_app_nx _ _ _ Hr) as Hr'. congruence.
    - exfalso. destruct (Hok ltac:(assumption)) as (r & Hr).
      pose proof (mi_account_step_app_nx _ _ _ Hr) as Hr'. congruence.
    - exfalso. destruct (Hok ltac:(assumption)) as (r & Hr).
      pose proof (mi_account_step_app_nx _ _ _ Hr) as Hr'. congruence.
    - exfalso. destruct (Hok ltac:(assumption)) as (r & Hr).
      pose proof (mi_account_step_app_nx _ _ _ Hr) as Hr'. congruence.
    - exfalso. destruct (Hok ltac:(assumption)) as (r & Hr).
      pose proof (mi_account_step_app_nx _ _ _ Hr) as Hr'. congruence.
    - rewrite sys_input_app_nw in *. eapply sstep_cfg_syscall; eassumption.
    - rewrite sys_input_app_nw in *. eapply sstep_cfg_syscall_materialization_fault; eassumption.
    - rewrite sys_input_app_nw in *. eapply sstep_cfg_exit; eassumption.
    - rewrite sys_input_app_nw in *. eapply sstep_cfg_killed; eassumption.
    - rewrite sys_input_app_nw in *. eapply sstep_cfg_syscall_unmodeled; eassumption.
  Qed.

  Lemma node_ok_app_tail : forall c (I : Type) evs nx (i0 : I),
    node_ok segs c I evs nx -> node_ok (segs ++ tail) c I evs nx.
  Proof.
    intros [ms model] I evs nx i0 [Hc Hs]. split.
    - intros i. apply sstep_cfg_app_next. exact (Hc i).
    - intros e st Hb. apply Hs. apply (sstep_cfg_app_back ms model e st); [| exact Hb].
      intros Hsvc. pose proof (Hc i0) as H0. inversion H0; subst.
      + eexists. eassumption.
      + exfalso. rewrite vdso_entry_fn_none in *. discriminate.
      + congruence.
      + congruence.
      + congruence.
  Qed.

  (* the input is the same over both lists ([sys_input_app_nw]), so robustness carries over *)
  Lemma sys_rob_app_tail : forall c, sys_rob segs c -> sys_rob (segs ++ tail) c.
  Proof.
    intros c H r x8 Hr Hs o. rewrite !sys_input_app_nw. exact (H r x8 Hr Hs o).
  Qed.

  Theorem realizes_app_tail : forall c T,
    realizes segs c T -> realizes (segs ++ tail) c T.
  Proof.
    intros c T H; induction H as [c I evs nx T i0 Hnode Hrob Hcont IH | c Hh | c T T' H IH Heq].
    - exact (rz_node (segs ++ tail) c I evs nx T i0 (node_ok_app_tail c I evs nx i0 Hnode)
               (sys_rob_app_tail c Hrob) IH).
    - exact (rz_halt (segs ++ tail) c Hh).
    - exact (rz_conseq (segs ++ tail) c T T' IH Heq).
  Qed.
End AppTail.

Section VdsoPair.
  Local Transparent vdso_segments.

  Lemma vdso_segments_nx : forall kb (sp mbase : word) s,
    In s (vdso_segments kb sp mbase) -> seg_executable s = false.
  Proof.
    intros kb sp mbase s H. unfold vdso_segments in H. cbv zeta in H.
    match type of H with In _ (if ?b then _ else _) => destruct b end;
      [destruct H|].
    destruct H as [<-|[<-|[]]]; reflexivity.
  Qed.

  Lemma vdso_segments_nw : forall kb (sp mbase : word) s,
    In s (vdso_segments kb sp mbase) -> seg_writable s = false.
  Proof.
    intros kb sp mbase s H. unfold vdso_segments in H. cbv zeta in H.
    match type of H with In _ (if ?b then _ else _) => destruct b end;
      [destruct H|].
    destruct H as [<-|[<-|[]]]; reflexivity.
  Qed.

  Lemma segments_reserved_vdso : forall kb (sp mbase : word),
    segments_reserved (vdso_segments kb sp mbase) = [].
  Proof.
    intros kb sp mbase. unfold vdso_segments. cbv zeta.
    match goal with |- segments_reserved (if ?b then _ else _) = _ => destruct b end;
      reflexivity.
  Qed.
End VdsoPair.

(* [segments_reserved]'s [filter] is stdpp's (through BvBase): by induction and conversion. *)
Lemma segments_reserved_app : forall a b,
  segments_reserved (a ++ b) = segments_reserved a ++ segments_reserved b.
Proof.
  intros a b. unfold segments_reserved.
  induction a as [|s a IH]; [reflexivity|].
  cbn [app]. destruct s as [sb ssz sp sby sk]. destruct sk;
    match goal with
    | |- context [?s0 :: a ++ b] =>
        first [ exact IH | exact (f_equal (cons (segment_reservation s0)) IH) ]
    end.
Qed.

Lemma segments_reserved_run_segments : forall segs inp (sp mb : word),
  segments_reserved (run_segments segs inp sp mb) = segments_reserved segs.
Proof.
  intros segs inp sp mb. unfold run_segments.
  rewrite segments_reserved_app, segments_reserved_vdso, app_nil_r. reflexivity.
Qed.

Theorem realizes_run_segments : forall segs inp (sp mb : word) c T,
  vdso_image segs = None ->
  realizes segs c T -> realizes (run_segments segs inp sp mb) c T.
Proof.
  intros segs inp sp mb c T Hvi H. unfold run_segments.
  apply realizes_app_tail;
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

(** The supplier-walk bridge: a walk over the binary's own segments is a derivation of the run's
    statement from the run's start. *)
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
