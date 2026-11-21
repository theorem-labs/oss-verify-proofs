(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch's ProcInput; the channel-reader premise of writev; the SIGPIPE answer of a write to a reader-gone channel; the run's segment list run_segments; RomBase.sys_rob at the system-call nodes; the vDSO run state; the launch's reservations with the vDSO pair). *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Vdso Run OmniRun.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Fs.ReadWrite.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require SimInv.

Module ExitSim.
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Vdso Run OmniRun.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import SimInv.

Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition is_exit_no (no : word) : Prop :=
  bv_unsigned no = 93%Z \/ bv_unsigned no = 94%Z.

Lemma syscall_spec_exit : forall i m o,
  is_exit_no (in_sysno i) ->
  syscall_spec i m o <-> exit_spec (in_arg i 0) i m o.
Proof.
  intros i m o [E|E]; unfold syscall_spec, dispatch; rewrite E; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma exit_dispatch_ok : forall i m,
  is_exit_no (in_sysno i) ->
  syscall_spec i m
    (Ok (mkEffect (Z_to_bv 64 0) [] [])
        (with_halted (bv_and (in_arg i 0) (Z_to_bv 64 255)) m) []).
Proof.
  intros i m Hno. apply (proj2 (syscall_spec_exit i m _ Hno)).
  unfold exit_spec, set_halted, ret_only, modify, bind, pure. cbn.
  eexists tt, (with_halted (bv_and (in_arg i 0) (Z_to_bv 64 255)) m),
    [], []. repeat split; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma exit_dispatch_ok_inv : forall i m eff m' evs,
  is_exit_no (in_sysno i) ->
  syscall_spec i m (Ok eff m' evs) ->
  eff = mkEffect (Z_to_bv 64 0) [] [] /\
  m' = with_halted (bv_and (in_arg i 0) (Z_to_bv 64 255)) m /\ evs = [].
Proof.
  intros i m eff m' evs Hno Hspec.
  apply (proj1 (syscall_spec_exit i m _ Hno)) in Hspec.
  unfold exit_spec, set_halted, ret_only, modify, bind, pure in Hspec. cbn in Hspec.
  sys_destruct. rewrite app_nil_l in *. repeat split; congruence.
Qed.

(* [comment removed for export] *)
Lemma exit_dispatch_no_unmodeled : forall i m,
  is_exit_no (in_sysno i) -> ~ syscall_spec i m Unmodeled.
Proof.
  intros i m Hno Hspec.
  apply (proj1 (syscall_spec_exit i m _ Hno)) in Hspec.
  unfold exit_spec, set_halted, ret_only, modify, bind, pure in Hspec. cbn in Hspec.
  sys_destruct.
Qed.

(* [comment removed for export] *)
Lemma in_arg0_sys_input : forall segs ms x8,
  in_arg (sys_input segs ms x8) 0 = ms_gpr ms 0.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma in_sysno_sys_input : forall segs ms x8,
  in_sysno (sys_input segs ms x8) = x8.
Proof. reflexivity. Qed.

Section WithSegs.
Variable segs : list Segment.
Variable code : word.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive to_exit : machine_state -> Prop :=
| te_here : forall ms x8,
    ms_svc_pending ms = Some x8 ->
    is_exit_no x8 ->
    ms_gpr ms 0 = code ->
    to_exit ms
| te_step : forall ms ms',
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    to_exit ms' ->
    to_exit ms.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint sim_c (fuel : nat) (ms : machine_state) : bool :=
  match fuel with
  | O => false
  | S fuel' =>
    match ms_svc_pending ms with
    | Some x8 => ((bv_unsigned x8 =? 93)%Z || (bv_unsigned x8 =? 94)%Z)
                 && bv_eqb (ms_gpr ms 0) code
    | None =>
      match RiscvSemantics.step segs ms with
      | MachineOk ms' => sim_c fuel' ms'
      | MachineFault | MachineUnmodeled => false
      end
    end
  end.

Lemma sim_c_to_exit : forall fuel ms, sim_c fuel ms = true -> to_exit ms.
Proof.
  induction fuel as [|fuel IH]; intros ms H; [discriminate|].
  cbn in H. destruct (ms_svc_pending ms) as [x8|] eqn:Hsvc.
  - apply andb_true_iff in H as [Hx8 Hgpr].
    apply bv_eqb_eq in Hgpr.
    eapply te_here; eauto.
    apply orb_true_iff in Hx8. destruct Hx8 as [H|H]; apply Z.eqb_eq in H;
      [left|right]; exact H.
  - destruct (RiscvSemantics.step segs ms) as [ms'| |] eqn:Hstep;
      [|discriminate|discriminate].
    eapply te_step; eauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma sim_step : forall fuel ms ms',
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  sim_c fuel ms' = true ->
  sim_c (S fuel) ms = true.
Proof.
  intros fuel ms ms' Hsvc Hstep Hrec.
  cbn [sim_c]. rewrite Hsvc. cbv beta iota. rewrite Hstep. exact Hrec.
Qed.

(* [comment removed for export] *)
Lemma sim_c_exit_now : forall fuel ms x8,
  ms_svc_pending ms = Some x8 ->
  ((bv_unsigned x8 =? 93)%Z || (bv_unsigned x8 =? 94)%Z) = true ->
  bv_eqb (ms_gpr ms 0) code = true ->
  sim_c (S fuel) ms = true.
Proof.
  intros fuel ms x8 Hsvc Hx8 Hcode.
  cbn [sim_c]. rewrite Hsvc. cbv beta iota. rewrite Hx8. cbn [andb]. exact Hcode.
Qed.

(* [comment removed for export] *)
Lemma sim_ecall_exit : forall fuel ms,
  ms_svc_pending ms = None ->
  fetch_word segs (ms_pc ms) = Some 0x73 ->
  ((bv_unsigned (ms_reg ms 17) =? 93)%Z || (bv_unsigned (ms_reg ms 17) =? 94)%Z) = true ->
  bv_eqb (ms_gpr ms 0) code = true ->
  sim_c (S (S fuel)) ms = true.
Proof.
  intros fuel ms Hsvc Hfetch Hcheck Hcode.
  set (ms1 := {| ms_regs := ms_regs ms; ms_fregs := ms_fregs ms; ms_pc_val := ms_pc_val ms;
                 ms_svc_pending := Some (ms_reg ms 17); ms_resv := ms_resv ms; ms_fcsr := ms_fcsr ms;
                 ms_mem := ms_mem ms; ms_rom := ms_rom ms |}).
  apply (sim_step (S fuel) ms ms1 Hsvc).
  - change (drop_access_report (step_accesses segs ms) = MachineOk ms1).
    unfold step_accesses. rewrite Hfetch. unfold ms1. reflexivity.
  - apply (sim_c_exit_now fuel ms1 (ms_reg ms 17)).
    + subst ms1. reflexivity.
    + exact Hcheck.
    + exact Hcode.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma sstep_instr_inv : forall ms model ms' evs st,
  m_vm_lazy model = [] ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  sstep segs (mkCfg ms model) evs st ->
  evs = [] /\ st = SNext (mkCfg ms' model).
Proof.
  intros ms model ms' evs st Hlazy Hsvc Hstep Hss.
  inversion Hss; subst.
  - (* sstep_instr *)
    match goal with H : mi_account_step segs ms model = MachineOk _ |- _ =>
      rewrite (mi_account_step_no_lazy segs ms model Hlazy) in H;
      rewrite Hstep in H; inversion H; subst end.
    split; reflexivity.
  - (* sstep_instr_fault *)
    match goal with H : mi_account_step segs ms model = MachineFault |- _ =>
      rewrite (mi_account_step_no_lazy segs ms model Hlazy) in H;
      rewrite Hstep in H; discriminate end.
  - (* sstep_instr_unmodeled *)
    match goal with H : mi_account_step segs ms model = MachineUnmodeled |- _ =>
      rewrite (mi_account_step_no_lazy segs ms model Hlazy) in H;
      rewrite Hstep in H; discriminate end.
  - (* sstep_vdso_call: its first premise is the same [MachineUnmodeled] *)
    match goal with H : mi_account_step segs ms model = MachineUnmodeled |- _ =>
      rewrite (mi_account_step_no_lazy segs ms model Hlazy) in H;
      rewrite Hstep in H; discriminate end.
  - (* sstep_vdso_materialization_fault *)
    match goal with H : mi_account_step segs ms model = MachineUnmodeled |- _ =>
      rewrite (mi_account_step_no_lazy segs ms model Hlazy) in H;
      rewrite Hstep in H; discriminate end.
  - (* sstep_vdso_unmodeled *)
    match goal with H : mi_account_step segs ms model = MachineUnmodeled |- _ =>
      rewrite (mi_account_step_no_lazy segs ms model Hlazy) in H;
      rewrite Hstep in H; discriminate end.
  - (* sstep_syscall *) congruence.
  - (* sstep_syscall_materialization_fault *) congruence.
  - (* sstep_exit *) congruence.
  - (* sstep_killed *) congruence.
  - (* sstep_syscall_unmodeled *) congruence.
Qed.

(* [comment removed for export] *)
Lemma sstep_exit_inv : forall ms model x8 evs st,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  is_exit_no x8 ->
  sstep segs (mkCfg ms model) evs st ->
  evs = [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)] /\
  st = SNext (mkCfg ms (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model)).
Proof.
  intros ms model x8 evs st Hh Hsvc Hx8 Hss.
  inversion Hss; subst; try congruence.
  - (* [comment removed for export] *)
    (* [comment removed for export] *)
    autorewrite with model in *.
    exfalso.
    match goal with
    | H3 : syscall_spec (sys_input segs ms ?x) model (Ok _ ?model' _),
      H2 : ms_svc_pending ms = Some ?x,
      H6 : m_halted ?model' = None |- _ =>
      assert (Hxe : is_exit_no (in_sysno (sys_input segs ms x)))
        by (rewrite in_sysno_sys_input; replace x with x8 by congruence; exact Hx8);
      apply (exit_dispatch_ok_inv _ _ _ _ _ Hxe) in H3;
      destruct H3 as (_ & Hm & _); rewrite Hm in H6;
      autorewrite with model in H6; discriminate
    end.
  - (* [comment removed for export] *)
    autorewrite with model in *.
    exfalso.
    match goal with
    | H3 : syscall_spec (sys_input segs ms ?x) model (Ok _ ?model' _),
      H2 : ms_svc_pending ms = Some ?x,
      H6 : m_halted ?model' = None |- _ =>
      assert (Hxe : is_exit_no (in_sysno (sys_input segs ms x)))
        by (rewrite in_sysno_sys_input; replace x with x8 by congruence; exact Hx8);
      apply (exit_dispatch_ok_inv _ _ _ _ _ Hxe) in H3;
      destruct H3 as (_ & Hm & _); rewrite Hm in H6;
      autorewrite with model in H6; discriminate
    end.
  - (* [comment removed for export] *)
    autorewrite with model in *.
    match goal with
    | H3 : syscall_spec (sys_input segs ms ?x) model (Ok _ ?model' ?evs0),
      H2 : ms_svc_pending ms = Some ?x,
      H6 : m_halted ?model' = Some ?code |- _ =>
      assert (Hxe : is_exit_no (in_sysno (sys_input segs ms x)))
        by (rewrite in_sysno_sys_input; replace x with x8 by congruence; exact Hx8);
      apply (exit_dispatch_ok_inv _ _ _ _ _ Hxe) in H3;
      destruct H3 as (Heff & Hm & Hevs);
      rewrite in_arg0_sys_input in Hm;
      subst evs0 model';
      assert (Hcode : code = bv_and (ms_gpr ms 0) (Z_to_bv 64 255))
        by (autorewrite with model in H6; congruence);
      subst code
    end.
    cbn. split; reflexivity.
  - (* [comment removed for export] *)
    exfalso.
    match goal with
    | H3 : syscall_spec (sys_input segs ms ?x) model (Ok _ ?model' _),
      H2 : ms_svc_pending ms = Some ?x,
      H6 : m_killed ?model' = Some _ |- _ =>
      assert (Hxe : is_exit_no (in_sysno (sys_input segs ms x)))
        by (rewrite in_sysno_sys_input; replace x with x8 by congruence; exact Hx8);
      apply (exit_dispatch_ok_inv _ _ _ _ _ Hxe) in H3;
      destruct H3 as (_ & Hm & _); rewrite Hm in H6;
      autorewrite with model in H6; discriminate
    end.
  - (* [comment removed for export] *)
    exfalso.
    match goal with
    | H3 : syscall_spec (sys_input segs ms ?x) model Unmodeled,
      H2 : ms_svc_pending ms = Some ?x |- _ =>
      eapply exit_dispatch_no_unmodeled; [| exact H3];
      rewrite in_sysno_sys_input; replace x with x8 by congruence; exact Hx8
    end.
Qed.

(* [comment removed for export] *)
Lemma star_halted_nil : forall c tr c',
  m_halted (cfg_model c) <> None -> star segs c tr c' -> tr = [] /\ c' = c.
Proof.
  intros c tr c' Hh Hstar. inversion Hstar as [|c1 evs c2 tr2 c3 Hss Hstar2]; subst.
  - split; reflexivity.
  - exfalso. destruct c as [ms model]. cbn in Hh.
    inversion Hss; subst; cbn in Hh; congruence.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition exit_post (fs : Fs.Fs) : post :=
  fun tr o => tr = [ExitEv (bv_and code (Z_to_bv 64 255)) fs]
              /\ exits_with (bv_and code (Z_to_bv 64 255)) tr o.

Lemma to_exit_exec : forall ms model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  to_exit ms ->
  OmniRun.exec segs (mkCfg ms model) (exit_post (m_fs model)).
Proof.
  intros ms model Hh Hlazy Hte.
  induction Hte as [ms x8 Hsvc Hx8 Hgpr | ms ms' Hsvc Hstep Hte IH].
  - (* [comment removed for export] *)
    apply (exec_step_only segs _ _
             [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)]
             (mkCfg ms (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model))).
    + replace [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)]
        with ([] ++ [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))
                       (m_fs (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model))])
        by (cbn; reflexivity).
      apply (sstep_exit segs ms model x8 (mkEffect (Z_to_bv 64 0) [] [])
               (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model) []
               (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))).
      * exact Hh.
      * exact Hsvc.
      * apply (exit_dispatch_ok (sys_input segs ms x8) model).
        rewrite in_sysno_sys_input. exact Hx8.
      * cbn. reflexivity.
      * apply m_killed_with_halted.
    + intros evs st Hss. exact (sstep_exit_inv ms model x8 evs st Hh Hsvc Hx8 Hss).
    + apply exec_halt.
      * cbn. rewrite m_halted_with_halted. discriminate.
      * unfold exit_post. cbn beta. rewrite app_nil_r, Hgpr. split; [reflexivity |].
        cbn [exits_with cfg_model]. split;
          [ rewrite m_halted_with_halted; reflexivity
          | apply m_killed_with_halted ].
  - (* [comment removed for export] *)
    apply (exec_step_only segs _ _ [] (mkCfg ms' model)).
    + apply (sstep_instr segs ms model ms' model); [exact Hh | exact Hsvc |].
      rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
    + intros evs st Hss. exact (sstep_instr_inv ms model ms' evs st Hlazy Hsvc Hstep Hss).
    + eapply exec_conseq; [exact IH |]. intros tr o H. cbn [app]. exact H.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma to_exit_star_only : forall ms model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  to_exit ms ->
  forall tr c, star segs (mkCfg ms model) tr c ->
    tr = [] \/ tr = [ExitEv (bv_and code (Z_to_bv 64 255)) (m_fs model)].
Proof.
  intros ms model Hh Hlazy Hte tr c Hstar.
  destruct (exec_realizes _ _ _ (exec_star _ _ _ _ _ (to_exit_exec ms model Hh Hlazy Hte) Hstar))
    as (tr' & o & _ & HQ).
  unfold exit_post in HQ. cbn beta in HQ. destruct HQ as (Heq & _).
  destruct (app_eq_unit _ _ Heq) as [(-> & _) | (-> & _)]; [left | right]; reflexivity.
Qed.

Lemma to_exit_star_admits : forall ms model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  to_exit ms ->
  exists c, star segs (mkCfg ms model)
              [ExitEv (bv_and code (Z_to_bv 64 255)) (m_fs model)] c.
Proof.
  intros ms model Hh Hlazy Hte.
  destruct (exec_realizes _ _ _ (to_exit_exec ms model Hh Hlazy Hte))
    as (tr & [c' | c'] & Hm & Heq & Hx); [| destruct Hx].
  subst tr. destruct (mexec_halt_star _ _ _ _ Hm c' eq_refl) as (Hstar & _).
  exists c'. exact Hstar.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition on_path (c : config) : Prop :=
  (m_halted (cfg_model c) = None /\ m_vm_lazy (cfg_model c) = [] /\
   to_exit (cfg_ms c))
  \/ m_halted (cfg_model c) <> None.

Lemma on_path_step : forall c evs c',
  on_path c -> sstep segs c evs (SNext c') -> on_path c'.
Proof.
  intros [ms model] evs [ms' model'] Hop Hss.
  unfold on_path in *; cbn in Hop |- *.
  destruct Hop as [[Hh [Hlazy Hte]] | Hh].
  - destruct Hte as [ms0 x8 Hsvc Hx8 Hgpr | ms0 ms0' Hsvc Hstep Hte].
    + (* [comment removed for export] *)
      destruct (sstep_exit_inv ms0 model x8 evs (SNext (mkCfg ms' model'))
                  Hh Hsvc Hx8 Hss) as [_ Hc'].
      inversion Hc'; subst. right. cbn. discriminate.
    + (* [comment removed for export] *)
      destruct (sstep_instr_inv ms0 model ms0' evs (SNext (mkCfg ms' model'))
                  Hlazy Hsvc Hstep Hss) as [_ Hc'].
      inversion Hc'; subst. left. repeat split; assumption.
  - (* [comment removed for export] *)
    exfalso. inversion Hss; subst; cbn in Hh; congruence.
Qed.

Lemma on_path_no_error : forall c evs, on_path c -> ~ sstep segs c evs SError.
Proof.
  intros [ms model] evs Hop Hss.
  unfold on_path in *; cbn in Hop.
  destruct Hop as [[Hh [Hlazy Hte]] | Hh].
  - destruct Hte as [ms0 x8 Hsvc Hx8 Hgpr | ms0 ms0' Hsvc Hstep Hte].
    + destruct (sstep_exit_inv ms0 model x8 evs SError Hh Hsvc Hx8 Hss) as [_ Hc'].
      discriminate.
    + destruct (sstep_instr_inv ms0 model ms0' evs SError Hlazy Hsvc Hstep Hss) as [_ Hc'].
      discriminate.
  - inversion Hss; subst; cbn in Hh; congruence.
Qed.

Lemma star_on_path : forall c tr c',
  on_path c -> star segs c tr c' -> on_path c'.
Proof. exact (star_inv segs on_path on_path_step). Qed.

Lemma to_exit_no_error : forall ms model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  to_exit ms ->
  ~ reaches_error segs (mkCfg ms model).
Proof.
  intros ms model Hh Hlazy Hte. apply exec_no_error.
  eapply exec_conseq; [exact (to_exit_exec ms model Hh Hlazy Hte) |].
  intros tr o (_ & Hx). exact (exits_with_never_errors _ _ _ Hx).
Qed.

End WithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition overlay_argc_bytes (sp : word) (argc : nat)
    (base_mem : word -> option byte) : word -> option byte :=
  let bytes := word_le8 (nat_to_word argc) in
  fun addr =>
    if (bv_unsigned addr =? bv_unsigned sp)%Z then nth_error bytes 0
    else if (bv_unsigned addr =? bv_unsigned sp + 1)%Z then nth_error bytes 1
    else if (bv_unsigned addr =? bv_unsigned sp + 2)%Z then nth_error bytes 2
    else if (bv_unsigned addr =? bv_unsigned sp + 3)%Z then nth_error bytes 3
    else if (bv_unsigned addr =? bv_unsigned sp + 4)%Z then nth_error bytes 4
    else if (bv_unsigned addr =? bv_unsigned sp + 5)%Z then nth_error bytes 5
    else if (bv_unsigned addr =? bv_unsigned sp + 6)%Z then nth_error bytes 6
    else if (bv_unsigned addr =? bv_unsigned sp + 7)%Z then nth_error bytes 7
    else base_mem addr.

Lemma stm_at (sp : word) (bytes : list byte) (addr : word) (i : nat) :
  (i < length bytes)%nat ->
  bv_unsigned addr = (bv_unsigned sp + Z.of_nat i)%Z ->
  stack_to_mem sp bytes addr = nth_error bytes i.
Proof.
  intros Hi Haddr. unfold stack_to_mem. rewrite Haddr. cbv beta zeta.
  destruct (Z.leb (bv_unsigned sp) (bv_unsigned sp + Z.of_nat i)) eqn:E1.
  2: { apply Z.leb_gt in E1; lia. }
  replace (bv_unsigned sp + Z.of_nat i - bv_unsigned sp)%Z with (Z.of_nat i) by lia.
  destruct (Z.ltb (Z.of_nat i) (Z.of_nat (length bytes))) eqn:E2.
  - rewrite Nat2Z.id. reflexivity.
  - apply Z.ltb_ge in E2. lia.
Qed.

Lemma word_le8_length : forall v, length (word_le8 v) = 8%nat.
Proof. intro v. reflexivity. Qed.

(* [comment removed for export] *)
Lemma build_stack_starts_with_argc :
  forall inp mbase ph entry (sp : word) draw,
  exists rest,
    entry_stack_image inp mbase ph entry sp draw =
    word_le8 (nat_to_word (length (in_argv inp))) ++ rest.
Proof.
  intros inp mbase ph entry sp draw.
  unfold entry_stack_image, build_stack_bytes, len_word, nat_to_word.
  cbv zeta.
  destruct (string_addrs _ (in_argv inp)) as [? ?].
  destruct (string_addrs _ (in_envp inp)) as [? ?].
  eexists. exact (eq_sym (app_assoc _ _ _)).
Qed.

Lemma build_stack_min_length : forall inp mbase ph entry (sp : word) draw,
  (8 <= length (entry_stack_image inp mbase ph entry sp draw))%nat.
Proof.
  intros inp mbase ph entry sp draw.
  destruct (build_stack_starts_with_argc inp mbase ph entry sp draw)
    as [rest Hr].
  rewrite Hr, length_app, word_le8_length. lia.
Qed.

(* [comment removed for export] *)
Lemma init_first8 :
  forall segs init_pc ph init_sp mbase init_rnd inp addr i, (i < 8)%nat ->
  bv_unsigned addr = (bv_unsigned init_sp + Z.of_nat i)%Z ->
  ms_mem (init_machine_state segs init_pc ph init_sp mbase init_rnd inp) addr =
  nth_error (word_le8 (nat_to_word (length (in_argv inp)))) i.
Proof.
  intros segs init_pc ph init_sp mbase init_rnd inp addr i Hi Haddr.
  assert (Hstk : stack_to_mem init_sp
                   (entry_stack_image inp mbase ph
                      (Z_to_bv 64 (Z.of_N init_pc)) init_sp init_rnd) addr
                 = nth_error (word_le8 (nat_to_word (length (in_argv inp)))) i).
  { rewrite (stm_at init_sp _ addr i);
      [ | pose proof (build_stack_min_length inp mbase ph
                        (Z_to_bv 64 (Z.of_N init_pc)) init_sp init_rnd); lia
        | exact Haddr ].
    destruct (build_stack_starts_with_argc inp mbase ph
                (Z_to_bv 64 (Z.of_N init_pc)) init_sp init_rnd) as [rest Hr].
    rewrite Hr. apply nth_error_app1. rewrite word_le8_length. lia. }
  change (ms_mem (init_machine_state segs init_pc ph init_sp mbase init_rnd inp)
            addr)
    with (match stack_to_mem init_sp
                  (entry_stack_image inp mbase ph
                     (Z_to_bv 64 (Z.of_N init_pc)) init_sp init_rnd) addr with
          | Some b => Some b
          | None =>
              if andb (Z.leb (stack_window_lo (in_kernel inp) mbase init_rnd)
                             (bv_unsigned addr))
                      (Z.ltb (bv_unsigned addr) (bv_unsigned init_sp))
              then Some (Z_to_bv 8 0) else None
          end).
  rewrite Hstk.
  destruct (nth_error (word_le8 (nat_to_word (length (in_argv inp)))) i) eqn:E;
    [reflexivity|].
  apply nth_error_None in E. rewrite word_le8_length in E. lia.
Qed.

Lemma actual_mem_is_overlay :
  forall segs init_pc ph init_sp mbase init_rnd inp,
  ms_mem (init_machine_state segs init_pc ph init_sp mbase init_rnd inp) =
  overlay_argc_bytes init_sp (length (in_argv inp))
    (ms_mem (init_machine_state segs init_pc ph init_sp mbase init_rnd inp)).
Proof.
  intros segs init_pc ph init_sp mbase init_rnd inp.
  apply functional_extensionality. intro addr.
  unfold overlay_argc_bytes.
  destruct ((bv_unsigned addr =? bv_unsigned init_sp)%Z) eqn:E0;
    [ apply Z.eqb_eq in E0;
      apply (init_first8 segs init_pc ph init_sp mbase init_rnd inp addr 0); lia | ].
  destruct ((bv_unsigned addr =? bv_unsigned init_sp + 1)%Z) eqn:E1;
    [ apply Z.eqb_eq in E1;
      apply (init_first8 segs init_pc ph init_sp mbase init_rnd inp addr 1); lia | ].
  destruct ((bv_unsigned addr =? bv_unsigned init_sp + 2)%Z) eqn:E2;
    [ apply Z.eqb_eq in E2;
      apply (init_first8 segs init_pc ph init_sp mbase init_rnd inp addr 2); lia | ].
  destruct ((bv_unsigned addr =? bv_unsigned init_sp + 3)%Z) eqn:E3;
    [ apply Z.eqb_eq in E3;
      apply (init_first8 segs init_pc ph init_sp mbase init_rnd inp addr 3); lia | ].
  destruct ((bv_unsigned addr =? bv_unsigned init_sp + 4)%Z) eqn:E4;
    [ apply Z.eqb_eq in E4;
      apply (init_first8 segs init_pc ph init_sp mbase init_rnd inp addr 4); lia | ].
  destruct ((bv_unsigned addr =? bv_unsigned init_sp + 5)%Z) eqn:E5;
    [ apply Z.eqb_eq in E5;
      apply (init_first8 segs init_pc ph init_sp mbase init_rnd inp addr 5); lia | ].
  destruct ((bv_unsigned addr =? bv_unsigned init_sp + 6)%Z) eqn:E6;
    [ apply Z.eqb_eq in E6;
      apply (init_first8 segs init_pc ph init_sp mbase init_rnd inp addr 6); lia | ].
  destruct ((bv_unsigned addr =? bv_unsigned init_sp + 7)%Z) eqn:E7;
    [ apply Z.eqb_eq in E7;
      apply (init_first8 segs init_pc ph init_sp mbase init_rnd inp addr 7); lia | ].
  reflexivity.
Qed.

Lemma machine_state_eta : forall ms : machine_state,
  ms = {| ms_regs := ms_regs ms; ms_fregs := ms_fregs ms; ms_pc_val := ms_pc_val ms;
          ms_svc_pending := ms_svc_pending ms; ms_resv := ms_resv ms; ms_fcsr := ms_fcsr ms;
          ms_mem := ms_mem ms; ms_rom := ms_rom ms |}.
Proof. intros []; reflexivity. Qed.

(* [comment removed for export] *)
Definition enum_state (segs : list Segment) (init_pc : N) (ph : PhdrInfo)
    (init_sp mbase : word) (init_rnd : EntryDraw) (inp : ProcInput)
    (argc : nat) (base : word -> option byte) : machine_state :=
  {| ms_regs       := ms_regs (init_machine_state segs init_pc ph init_sp mbase init_rnd inp);
     ms_fregs      := ms_fregs (init_machine_state segs init_pc ph init_sp mbase init_rnd inp);
     ms_pc_val     := ms_pc_val (init_machine_state segs init_pc ph init_sp mbase init_rnd inp);
     ms_svc_pending := ms_svc_pending (init_machine_state segs init_pc ph init_sp mbase init_rnd inp);
     ms_resv       := ms_resv (init_machine_state segs init_pc ph init_sp mbase init_rnd inp);
     ms_fcsr       := ms_fcsr (init_machine_state segs init_pc ph init_sp mbase init_rnd inp);
     ms_mem        := overlay_argc_bytes init_sp argc base;
     ms_rom        := ms_rom (init_machine_state segs init_pc ph init_sp mbase init_rnd inp) |}.

(* [comment removed for export] *)
Lemma init_eq_enum_state :
  forall segs init_pc ph init_sp mbase init_rnd inp,
  init_machine_state segs init_pc ph init_sp mbase init_rnd inp =
  enum_state segs init_pc ph init_sp mbase init_rnd inp
    (length (in_argv inp))
    (ms_mem (init_machine_state segs init_pc ph init_sp mbase init_rnd inp)).
Proof.
  intros segs init_pc ph init_sp mbase init_rnd inp. unfold enum_state.
  rewrite (machine_state_eta
             (init_machine_state segs init_pc ph init_sp mbase init_rnd inp)) at 1.
  f_equal; try reflexivity. apply actual_mem_is_overlay.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma exit_omni_run : forall segs pc ph sp brk0 mb rnd lim code inp F,
  sim_c (run_segments segs inp sp mb) code F (init_machine_state (run_segments segs inp sp mb) pc ph sp mb rnd inp) = true ->
  omni_run (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp
    (exit_post code (in_fs inp)).
Proof.
  intros segs pc ph sp brk0 mb rnd lim code inp F Hsim.
  cbn [omni_run]. unfold init_config.
  exact (to_exit_exec (run_segments segs inp sp mb) code
           (init_machine_state (run_segments segs inp sp mb) pc ph sp mb rnd inp)
           (with_vdso (vdso_run_init (ed_vdso rnd))
              (init_model (segments_reserved (run_segments segs inp sp mb)) brk0 mb sp lim inp))
           eq_refl eq_refl (sim_c_to_exit (run_segments segs inp sp mb) code F _ Hsim)).
Qed.

Lemma exit_obs_iff : forall segs pc ph sp brk0 mb rnd lim code inp F,
  sim_c (run_segments segs inp sp mb) code F (init_machine_state (run_segments segs inp sp mb) pc ph sp mb rnd inp) = true ->
  forall tr, obs_trace (run_segments segs inp sp mb) (init_config (run_segments segs inp sp mb) pc ph sp brk0 mb rnd lim inp) tr
             <-> is_prefix tr [ExitEv (bv_and code (Z_to_bv 64 255)) (in_fs inp)].
Proof.
  intros segs pc ph sp brk0 mb rnd lim code inp F Hsim tr.
  apply exec_obs_iff.
  eapply exec_conseq; [exact (exit_omni_run segs pc ph sp brk0 mb rnd lim code inp F Hsim) |].
  intros tr' o (Heq & Hx). split; [exact Heq | exact (exits_with_never_errors _ _ _ Hx)].
Qed.

Lemma exit_no_error_run : forall segs pc ph sp brk0 mb rnd lim code inp F,
  sim_c (run_segments segs inp sp mb) code F (init_machine_state (run_segments segs inp sp mb) pc ph sp mb rnd inp) = true ->
  ~ reaches_error (run_segments segs inp sp mb) (init_config (run_segments segs inp sp mb) pc ph sp brk0 mb rnd lim inp).
Proof.
  intros segs pc ph sp brk0 mb rnd lim code inp F Hsim. apply exec_no_error.
  eapply exec_conseq; [exact (exit_omni_run segs pc ph sp brk0 mb rnd lim code inp F Hsim) |].
  intros tr o (_ & Hx). exact (exits_with_never_errors _ _ _ Hx).
Qed.

(* [comment removed for export] *)
Lemma exit_must_exit_with : forall segs pc ph sp brk0 mb rnd lim code inp F,
  sim_c (run_segments segs inp sp mb) code F (init_machine_state (run_segments segs inp sp mb) pc ph sp mb rnd inp) = true ->
  must_exit_with (bv_and code (Z_to_bv 64 255)) (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp.
Proof.
  intros segs pc ph sp brk0 mb rnd lim code inp F Hsim. apply must_exit_with_iff.
  eapply exec_conseq; [exact (exit_omni_run segs pc ph sp brk0 mb rnd lim code inp F Hsim) |].
  intros tr o (_ & Hx). exact Hx.
Qed.

Lemma exit_omni_run_code_unique : forall segs pc ph sp brk0 mb rnd lim code inp F code',
  sim_c (run_segments segs inp sp mb) code F (init_machine_state (run_segments segs inp sp mb) pc ph sp mb rnd inp) = true ->
  omni_run (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp (exits_with code') ->
  code' = bv_and code (Z_to_bv 64 255).
Proof.
  intros segs pc ph sp brk0 mb rnd lim code inp F code' Hsim Hex.
  pose proof (exit_omni_run segs pc ph sp brk0 mb rnd lim code inp F Hsim) as Hrun.
  cbn [omni_run] in Hrun, Hex.
  destruct (exec_realizes _ _ _ Hrun) as (tr & [c' | c'] & Hm & _ & Hx); [| destruct Hx].
  pose proof (exec_sound _ _ _ Hex _ _ Hm) as Hx'.
  cbn [exits_with] in Hx, Hx'. destruct Hx as (Hx & _). destruct Hx' as (Hx' & _).
  rewrite Hx in Hx'. injection Hx' as Hx'. symmetry. exact Hx'.
Qed.

(* [comment removed for export] *)
Lemma exit_omni_strong_equiv :
  forall source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd code inp FR FA,
  sim_c (run_segments source_segs inp rsp rmb) code FR
    (init_machine_state (run_segments source_segs inp rsp rmb) rpc rph rsp rmb rrnd inp) = true ->
  sim_c (run_segments target_segs inp asp amb) code FA
    (init_machine_state (run_segments target_segs inp asp amb) apc aph asp amb arnd inp) = true ->
  omni_strong_equiv (mkImage source_segs rpc rph) (mkImage target_segs apc aph)
                    (mkEntry rsp rbrk rmb rrnd) (mkEntry asp abrk amb arnd) inp.
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd code inp FR FA
    Hsource Htarget.
  split.
  { cbn [image_run_segments img_segments en_sp en_mmap_base].
    eapply coexec_conseq;
      [apply exec_coexec;
       exact (exit_omni_run source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit code inp FR Hsource) |].
    intros tr o (_ & Hx).
    exact (never_errors_covered _ _ _ (exits_with_never_errors _ _ _ Hx)). }
  right. split.
  - apply trace_equiv_iff_omni. intro tr. cbn.
    rewrite (exit_obs_iff source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit code inp FR Hsource tr).
    rewrite (exit_obs_iff target_segs apc aph asp abrk amb arnd target_alloc_limit code inp FA Htarget tr).
    reflexivity.
  - apply bh_errors_iff. cbn.
    apply (exit_no_error_run target_segs apc aph asp abrk amb arnd target_alloc_limit code inp FA Htarget).
Qed.

(* [comment removed for export] *)
Lemma exit_strong_equiv :
  forall source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim code inp FR FA,
  sim_c (run_segments source_segs inp rsp rmb) code FR
    (init_machine_state (run_segments source_segs inp rsp rmb) rpc rph rsp rmb rrnd inp) = true ->
  sim_c (run_segments target_segs inp asp amb) code FA
    (init_machine_state (run_segments target_segs inp asp amb) apc aph asp amb arnd inp) = true ->
  Equivalence.modeled (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
  /\ Equivalence.equiv (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
                       (run (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp).
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim code inp FR FA
    Hsource Htarget.
  split.
  { apply no_error_run_modeled.
    apply (exit_no_error_run source_segs rpc rph rsp rbrk rmb rrnd rlim code inp FR Hsource). }
  right. split.
  - intro tr. cbn.
    rewrite (exit_obs_iff source_segs rpc rph rsp rbrk rmb rrnd rlim code inp FR Hsource tr).
    rewrite (exit_obs_iff target_segs apc aph asp abrk amb arnd alim code inp FA Htarget tr).
    reflexivity.
  - cbn. apply (exit_no_error_run target_segs apc aph asp abrk amb arnd alim code inp FA Htarget).
Qed.
End ExitSim.

Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.SimInv OSSVerify.Proofs.fast_float.from_chars.lib.Common.CatSim.ExitSim.

Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma read_aux_read_byte : forall ms k a,
  read_bytes_aux (ms_read_byte ms) a k = ms_read_bytes_aux ms a k.
Proof.
  intros ms. induction k as [|k IH]; intro a; [reflexivity|].
  cbn [read_bytes_aux ms_read_bytes_aux].
  destruct (ms_read_byte ms a) as [b|]; [rewrite IH|]; reflexivity.
Qed.

Lemma read_bytes_map_read_byte : forall ms a len,
  read_bytes_map (ms_read_byte ms) a len = ms_read_bytes ms a len.
Proof. intros. rewrite read_bytes_map_eq. unfold ms_read_bytes.
  apply read_aux_read_byte. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma apply_effect_no_write : forall ms r,
  apply_effect ms (mkEffect r [] []) = set_gpr0 ms r.
Proof.
  intros ms r. unfold apply_effect, set_gpr0.
  cbn [eff_ret eff_writes eff_zeros apply_zeros apply_writes].
  reflexivity.
Qed.

Lemma apply_effect_copyins_no_write : forall ms r copyins,
  apply_effect ms (with_copyins copyins (mkEffect r [] [])) = set_gpr0 ms r.
Proof.
  intros ms r copyins. unfold with_copyins, apply_effect, set_gpr0.
  cbn [eff_ret eff_writes eff_zeros eff_unmaps eff_copies
       apply_unmaps apply_zeros apply_copies apply_writes].
  reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma in_sysno_sys_input64 : forall segs ms x8,
  in_sysno (sys_input segs ms x8) = x8.
Proof. reflexivity. Qed.
Lemma in_arg0_sys_input64 : forall segs ms x8,
  in_arg (sys_input segs ms x8) 0 = ms_gpr ms 0.
Proof. reflexivity. Qed.
Lemma in_arg1_sys_input64 : forall segs ms x8,
  in_arg (sys_input segs ms x8) 1 = ms_gpr ms 1.
Proof. reflexivity. Qed.
Lemma in_arg2_sys_input64 : forall segs ms x8,
  in_arg (sys_input segs ms x8) 2 = ms_gpr ms 2.
Proof. reflexivity. Qed.
Lemma in_mem_sys_input : forall segs ms x8,
  in_mem (sys_input segs ms x8) = ms_read_byte ms.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma syscall_spec_write : forall segs ms x8 model o,
  bv_unsigned x8 = 64%Z ->
  (syscall_spec (sys_input segs ms x8) model o
   <-> write_spec (fd32 (ms_gpr ms 0)) (ms_gpr ms 1) (ms_gpr ms 2)
         (sys_input segs ms x8) model o).
Proof.
  intros segs ms x8 model o Hno.
  unfold syscall_spec, dispatch.
  change (in_sysno (sys_input segs ms x8)) with x8.
  rewrite Hno. reflexivity.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition fd1chan (model : Model) : Prop :=
  fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1))
  /\ m_channel_reader model = true.

(* [comment removed for export] *)
Definition buf_modeled (b : list byte) : Prop :=
  (Z.of_nat (length b) <= rw_bytes_max)%Z.

Definition bufs_modeled (bufs : list (list byte)) : Prop :=
  Forall buf_modeled bufs.

(* [comment removed for export] *)
Lemma bufs_modeled_single : forall b, buf_modeled b -> bufs_modeled [b].
Proof. intros b H. apply Forall_cons; [exact H | apply Forall_nil]. Qed.

(* [comment removed for export] *)
Lemma buf_modeled_nil : buf_modeled [].
Proof. unfold buf_modeled. cbn. unfold rw_bytes_max. lia. Qed.

Lemma buf_modeled_skipn : forall n (b : list byte),
  buf_modeled b -> buf_modeled (skipn n b).
Proof.
  intros n b H. unfold buf_modeled in *. rewrite length_skipn. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma write1_check_n : forall segs ms x8 model buf n,
  fd1chan model ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = Z_to_bv 64 1 ->
  ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
  (* THE RANGE [vfs_write]'s [access_ok] ACCEPTS.  The channel arm asks it
     on the named count before it reads the source, so a delivery is
     admissible only there: without this premise the lemma was true of a
     walk that wrapped at 2^64 and is false of one that does not, exactly
     where the buffer leaves the user address space ([buf + count] past
     [State.TASK_SIZE]; [Uaccess.access_okb_intro] gives it from that
     inequality).  A repair of a statement that had become false, not a
     weakening *)
  access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
  buf_modeled buf ->
  (1 <= n)%nat -> (n <= length buf)%nat ->
  check_write (sys_input segs ms x8)
    (fd32 (ms_gpr ms 0)) (ms_gpr ms 1) (ms_gpr ms 2)
    (with_copyins [(ms_gpr ms 1, n)]
      (mkEffect (len_word (firstn n buf)) [] [])) model
    = CheckOk model (map (WriteEv (Z_to_bv 64 1)) (firstn n buf)).
Proof.
  intros segs ms x8 model buf n Hfd Hno Hg Hr Hok Hcnt Hn1 Hn2.
  unfold fd1chan in Hfd. destruct Hfd as [Hfd Hrdr].
  assert (Hrb : read_bytes_map (in_mem (sys_input segs ms x8))
                  (ms_gpr ms 1) (ms_gpr ms 2) = Some buf).
  { rewrite in_mem_sys_input, read_bytes_map_read_byte. exact Hr. }
  pose proof (read_bytes_map_length _ _ _ _ Hrb) as Hlen.
  pose proof (word_unsigned_range (ms_gpr ms 2)) as Hcr.
  assert (Hcw : (bv_unsigned (ms_gpr ms 2) <= rw_bytes_max)%Z)
    by (unfold buf_modeled in Hcnt; lia).
  assert (Hmc : negb (modeled_rw_range (ms_gpr ms 1) (ms_gpr ms 2)) = false)
    by (apply rw_range_in_range; exact Hcw).
  unfold check_write.
  rewrite Hg; norm_fd32; rewrite Hfd.
  change (w_is0 (Z_to_bv 64 1)) with false. cbv beta iota.
  rewrite Hmc. cbv beta iota.
  assert (Hc : w_is0 (ms_gpr ms 2) = false) by (apply w_is0_pos; lia).
  rewrite Hc. cbv beta iota. cbv zeta.
  rewrite Hok. cbn [negb]. cbv beta iota.
  rewrite Hrdr. change (negb true) with false. cbv beta iota.
  rewrite (write_source_of_rw _ _ _ Hcw), (readable_bytes_full _ _ _ _ Hrb).
  assert (Hg0 : Nat.eqb (length buf) 0 = false) by (apply Nat.eqb_neq; lia).
  rewrite Hg0. cbv beta iota. unfold with_copyins; cbn.
  assert (Hlenf : Z.of_nat (length (firstn n buf)) = Z.of_nat n)
    by (rewrite length_firstn; lia).
  assert (Hru : bv_unsigned (len_word (firstn n buf)) = Z.of_nat n).
  { rewrite (len_word_unsigned (firstn n buf));
      [exact Hlenf | rewrite Hlenf; lia]. }
  rewrite ?Hru.
  assert (Hg1 : (1 <=? Z.of_nat n)%Z = true) by (apply Z.leb_le; lia).
  assert (Hg2 : (Z.of_nat n <=? Z.of_nat (length buf))%Z = true)
    by (apply Z.leb_le; lia).
  rewrite ?Hg1, ?Hg2. cbn [andb].
  rewrite ?Nat2Z.id, bv_eqb_refl, Nat.eqb_refl. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma write1_ok_n : forall segs ms x8 model buf n,
  fd1chan model ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = Z_to_bv 64 1 ->
  ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
  (* see [write1_check_n] *)
  access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
  buf_modeled buf ->
  (1 <= n)%nat -> (n <= length buf)%nat ->
  syscall_spec (sys_input segs ms x8) model
    (Ok (with_copyins [(ms_gpr ms 1, n)]
          (mkEffect (len_word (firstn n buf)) [] [])) model
        (map (WriteEv (Z_to_bv 64 1)) (firstn n buf))).
Proof.
  intros segs ms x8 model buf n Hfd Hno Hg Hr Hok Hcnt Hn1 Hn2.
  apply (proj2 (syscall_spec_write _ _ _ _ _ Hno)).
  apply check_write_sound_ok. apply write1_check_n; assumption.
Qed.

(* [comment removed for export] *)
Lemma write1_ok_inv : forall segs ms x8 model eff model' evs buf,
  fd1chan model ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = Z_to_bv 64 1 ->
  ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
  access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
  (1 <= length buf)%nat ->
  syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
  exists n, (1 <= n)%nat /\ (n <= length buf)%nat /\
    eff = with_copyins [(ms_gpr ms 1, n)]
            (mkEffect (len_word (firstn n buf)) [] []) /\ model' = model /\
    evs = map (WriteEv (Z_to_bv 64 1)) (firstn n buf).
Proof.
  intros segs ms x8 model eff model' evs buf Hfd Hno Hg Hr Hok Hnb Hspec.
  unfold fd1chan in Hfd. destruct Hfd as [Hfd Hrdr].
  assert (Hrb : read_bytes_map (in_mem (sys_input segs ms x8))
                  (ms_gpr ms 1) (ms_gpr ms 2) = Some buf).
  { rewrite in_mem_sys_input, read_bytes_map_read_byte. exact Hr. }
  pose proof (read_bytes_map_length _ _ _ _ Hrb) as Hlen.
  apply (proj1 (syscall_spec_write _ _ _ _ _ Hno)) in Hspec.
  apply check_write_complete_ok in Hspec.
  unfold check_write in Hspec.
  rewrite Hg in Hspec; norm_fd32; rewrite Hfd in Hspec.
  change (w_is0 (Z_to_bv 64 1)) with false in Hspec. cbv beta iota in Hspec.
  (* being handed [Ok] already rules the transfer-size guard out: had it
     fired, the checker would have answered [CheckUnmodeled] *)
  destruct (negb (modeled_rw_range (ms_gpr ms 1) (ms_gpr ms 2)));
    cbv beta iota in Hspec; [discriminate|].
  assert (Hc : w_is0 (ms_gpr ms 2) = false) by (apply w_is0_pos; lia).
  rewrite Hc in Hspec. cbv beta iota zeta in Hspec.
  rewrite Hok in Hspec. cbn [negb] in Hspec. cbv beta iota in Hspec.
  rewrite Hrdr in Hspec. change (negb true) with false in Hspec.
  cbv beta iota in Hspec.
  (* the source the transfer sees is the CLAMPED prefix of the range the
     call named -- [buf] itself for every count under [MAX_RW_COUNT], and
     a prefix of it above, which the gate above admits at an in-range
     buffer *)
  rewrite (write_source_prefix _ _ _ _ Hrb) in Hspec.
  pose proof (rw_count_clamp_range (ms_gpr ms 2)) as Hcl.
  set (c := Z.to_nat (rw_count_clamp (ms_gpr ms 2))) in *.
  assert (Hcpos : (1 <= c)%nat)
    by (unfold c, rw_count_clamp, MAX_RW_COUNT in *; lia).
  assert (Hfl : length (firstn c buf) = Nat.min c (length buf))
    by apply length_firstn.
  assert (Hg0 : Nat.eqb (length (firstn c buf)) 0 = false)
    by (rewrite Hfl; apply Nat.eqb_neq; lia).
  rewrite Hg0 in Hspec. cbv beta iota in Hspec.
  destruct eff as [ret ws zs us cs copyins]; destruct ws as [|? ?];
    destruct zs as [|? ?]; destruct us as [|? ?];
      destruct cs as [|? ?]; try discriminate.
  destruct ((1 <=? bv_unsigned ret)%Z
            && (bv_unsigned ret <=? Z.of_nat (length (firstn c buf)))%Z) eqn:Hgr;
    [|discriminate].
  destruct (access_ranges_eqb copyins [(ms_gpr ms 1, Z.to_nat (bv_unsigned ret))])
    eqn:Hreads; [|discriminate].
  inversion Hspec; clear Hspec; subst.
  apply andb_true_iff in Hgr as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2.
  rewrite Hfl in H2.
  apply access_ranges_eqb_eq in Hreads. subst copyins.
  exists (Z.to_nat (bv_unsigned ret)).
  assert (Hff : firstn (Z.to_nat (bv_unsigned ret)) (firstn c buf)
                = firstn (Z.to_nat (bv_unsigned ret)) buf)
    by (rewrite firstn_firstn; f_equal; lia).
  rewrite Hff.
  assert (Hlw : len_word (firstn (Z.to_nat (bv_unsigned ret)) buf) = ret)
    by (apply len_word_firstn_ret; lia).
  rewrite Hlw. repeat split; try reflexivity; lia.
Qed.

(* [comment removed for export] *)
Lemma write1_no_unmodeled : forall segs ms x8 model buf,
  fd1chan model ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = Z_to_bv 64 1 ->
  ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
  buf_modeled buf ->
  (* a zero [count] is genuinely unmodeled when the range verdict is
     unclear (see [access_ok_zero] in the write spec), so the nonempty
     buffer is load-bearing here, not just convenient *)
  (1 <= length buf)%nat ->
  ~ syscall_spec (sys_input segs ms x8) model Unmodeled.
Proof.
  intros segs ms x8 model buf Hfd Hno Hg Hr Hcnt Hnb Hspec.
  unfold fd1chan in Hfd. destruct Hfd as [Hfd Hrdr].
  assert (Hrb : read_bytes_map (in_mem (sys_input segs ms x8))
                  (ms_gpr ms 1) (ms_gpr ms 2) = Some buf).
  { rewrite in_mem_sys_input, read_bytes_map_read_byte. exact Hr. }
  pose proof (read_bytes_map_length _ _ _ _ Hrb) as Hlen.
  assert (Hcw : (bv_unsigned (ms_gpr ms 2) <= rw_bytes_max)%Z)
    by (unfold buf_modeled in Hcnt; lia).
  assert (Hmc : negb (modeled_rw_range (ms_gpr ms 1) (ms_gpr ms 2)) = false)
    by (apply rw_range_in_range; exact Hcw).
  apply (proj1 (syscall_spec_write _ _ _ _ _ Hno)) in Hspec.
  apply (check_write_complete_unmodeled _ _ _ _ _ (mkEffect (Z_to_bv 64 0) [] []))
    in Hspec.
  unfold check_write in Hspec.
  rewrite Hg in Hspec; norm_fd32; rewrite Hfd in Hspec.
  change (w_is0 (Z_to_bv 64 1)) with false in Hspec. cbv beta iota in Hspec.
  rewrite Hmc in Hspec. cbv beta iota in Hspec.
  destruct (w_is0 (ms_gpr ms 2)) eqn:Hc; try rewrite Hc in Hspec.
  { exfalso.
    assert (Hc0 : w_is0 (ms_gpr ms 2) = false) by (apply w_is0_pos; lia).
    congruence. }
  (* [vfs_write]'s [access_ok]: a refused range is -EFAULT, an answer *)
  destruct (negb (access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)))).
  { now apply check_ret_only_no_unmodeled in Hspec. }
  rewrite Hrdr in Hspec. change (negb true) with false in Hspec.
  cbv beta iota in Hspec.
  rewrite (write_source_of_rw _ _ _ Hcw), (readable_bytes_full _ _ _ _ Hrb)
    in Hspec.
  destruct (length buf =? 0)%nat eqn:Hz; try rewrite Hz in Hspec.
  { now apply check_ret_only_no_unmodeled in Hspec. }
  discriminate Hspec.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition fd1dead (model : Model) : Prop :=
  fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1))
  /\ m_channel_reader model = false
  /\ m_sigpipe_default model = true
  /\ m_sigpipe_terminal model = true
  /\ sigpipe_blocked (m_sigmask model) = false.

(* [comment removed for export] *)
Lemma write1_dead_check : forall segs ms x8 model eff,
  fd1dead model ->
  ms_gpr ms 0 = Z_to_bv 64 1 ->
  access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
  w_is0 (ms_gpr ms 2) = false ->
  check_write (sys_input segs ms x8)
    (fd32 (ms_gpr ms 0)) (ms_gpr ms 1) (ms_gpr ms 2) eff model
  = check_ret_only eff (errno_ret EPIPE)
      (with_killed (Z_to_bv 64 SIGPIPE) model) [].
Proof.
  intros segs ms x8 model eff (Hfd & Hrdr & Hdef & Hterm & Hmask) Hg Hok Hc.
  unfold check_write.
  rewrite Hg; norm_fd32; rewrite Hfd.
  change (w_is0 (Z_to_bv 64 1)) with false. cbv beta iota.
  rewrite (rw_range_of_access_ok _ _ Hok). cbv beta iota.
  rewrite Hc. cbv beta iota.
  rewrite Hrdr. change (negb false) with true. cbv beta iota.
  rewrite Hok. change (negb true) with false. cbv beta iota.
  unfold check_sigpipe_write, sigpipe_declines, raise_sigpipe.
  rewrite Hdef, Hterm, Hmask. reflexivity.
Qed.

Lemma write1_dead_ok : forall segs ms x8 model,
  fd1dead model ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = Z_to_bv 64 1 ->
  access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
  w_is0 (ms_gpr ms 2) = false ->
  syscall_spec (sys_input segs ms x8) model
    (Ok (mkEffect (errno_ret EPIPE) [] [])
        (with_killed (Z_to_bv 64 SIGPIPE) model) []).
Proof.
  intros segs ms x8 model Hd Hno Hg Hok Hc.
  apply (proj2 (syscall_spec_write _ _ _ _ _ Hno)).
  apply check_write_sound_ok.
  rewrite (write1_dead_check segs ms x8 model _ Hd Hg Hok Hc).
  apply check_ret_only_ok_iff. split; [reflexivity | split; reflexivity].
Qed.

(* [comment removed for export] *)
Lemma write1_dead_ok_inv : forall segs ms x8 model eff model' evs,
  fd1dead model ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = Z_to_bv 64 1 ->
  access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
  w_is0 (ms_gpr ms 2) = false ->
  syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
  eff = mkEffect (errno_ret EPIPE) [] []
  /\ model' = with_killed (Z_to_bv 64 SIGPIPE) model /\ evs = [].
Proof.
  intros segs ms x8 model eff model' evs Hd Hno Hg Hok Hc Hspec.
  apply (proj1 (syscall_spec_write _ _ _ _ _ Hno)) in Hspec.
  apply check_write_complete_ok in Hspec.
  rewrite (write1_dead_check segs ms x8 model eff Hd Hg Hok Hc) in Hspec.
  apply check_ret_only_ok_iff in Hspec. exact Hspec.
Qed.

Lemma write1_dead_no_unmodeled : forall segs ms x8 model,
  fd1dead model ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = Z_to_bv 64 1 ->
  access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
  w_is0 (ms_gpr ms 2) = false ->
  ~ syscall_spec (sys_input segs ms x8) model Unmodeled.
Proof.
  intros segs ms x8 model Hd Hno Hg Hok Hc Hspec.
  apply (proj1 (syscall_spec_write _ _ _ _ _ Hno)) in Hspec.
  apply (check_write_complete_unmodeled _ _ _ _ _ (mkEffect (Z_to_bv 64 0) [] []))
    in Hspec.
  rewrite (write1_dead_check segs ms x8 model _ Hd Hg Hok Hc) in Hspec.
  exact (check_ret_only_no_unmodeled _ _ _ _ Hspec).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma is_prefix_app_mono {A} : forall (l a b : list A),
  is_prefix a b -> is_prefix (l ++ a) (l ++ b).
Proof.
  induction l as [|x l IH]; intros a b H; cbn; [exact H | split; [reflexivity | apply IH; exact H]].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint wevents_ch (ch : word) (bufs : list (list byte)) : list event :=
  match bufs with
  | [] => []
  | buf :: rest => map (WriteEv ch) buf ++ wevents_ch ch rest
  end.

Inductive wpick (ch : word) : list (list byte) -> list event -> Prop :=
| wp_nil : wpick ch [] []
| wp_cons : forall buf bufs n tr,
    (1 <= n)%nat -> (n <= length buf)%nat ->
    wpick ch bufs tr ->
    wpick ch (buf :: bufs) (map (WriteEv ch) (firstn n buf) ++ tr).

(* [comment removed for export] *)
Lemma wpick_wevents : forall ch bufs,
  Forall (fun b => (1 <= length b)%nat) bufs ->
  wpick ch bufs (wevents_ch ch bufs).
Proof.
  intros ch bufs H; induction H as [|b bs Hb Hbs IH].
  - apply wp_nil.
  - cbn [wevents_ch].
    pose proof (wp_cons ch b bs (length b) _ Hb (Nat.le_refl _) IH) as Hc.
    rewrite firstn_all in Hc. exact Hc.
Qed.

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive to_wexit : machine_state -> list (list byte) -> word -> Prop :=
| tw_exit : forall ms x8,
    ms_svc_pending ms = Some x8 ->
    is_exit_no x8 ->
    to_wexit ms [] (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))
| tw_write : forall ms x8 buf bufs code,
    ms_svc_pending ms = Some x8 ->
    bv_unsigned x8 = 64%Z ->
    ms_gpr ms 0 = Z_to_bv 64 1 ->
    ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
    (* [comment removed for export] *)
    access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
    (1 <= length buf)%nat ->
    (forall n, (1 <= n)%nat -> (n <= length buf)%nat ->
       to_wexit (advance_past_svc (set_gpr0 ms (len_word (firstn n buf)))) bufs code) ->
    to_wexit ms (buf :: bufs) code
| tw_step : forall ms ms' bufs code,
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    to_wexit ms' bufs code ->
    to_wexit ms bufs code.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive msteps : machine_state -> machine_state -> Prop :=
| mst_refl : forall ms, msteps ms ms
| mst_step : forall ms ms' ms'',
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    msteps ms' ms'' ->
    msteps ms ms''.

Lemma msteps_one : forall ms ms',
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  msteps ms ms'.
Proof. intros ms ms' Hsvc Hstep. eapply mst_step; [exact Hsvc | exact Hstep | apply mst_refl]. Qed.

Lemma msteps_trans : forall ms ms' ms'',
  msteps ms ms' -> msteps ms' ms'' -> msteps ms ms''.
Proof.
  intros ms ms' ms'' H; induction H; [auto|].
  intro H2. eapply mst_step; eauto.
Qed.

Lemma msteps_to_wexit : forall ms ms' bufs code,
  msteps ms ms' -> to_wexit ms' bufs code -> to_wexit ms bufs code.
Proof.
  intros ms ms' bufs code H; induction H; [auto|].
  intro Hw. eapply tw_step; eauto.
Qed.

(* [comment removed for export] *)
Lemma to_wexit_bufs_nonempty : forall ms bufs code,
  to_wexit ms bufs code ->
  Forall (fun b => (1 <= length b)%nat) bufs.
Proof.
  intros ms bufs code H;
    induction H as
      [ms x8 Hsvc Hx8
      | ms x8 buf bufs code Hsvc Hno Hg Hr Hok Hnb Hcont IH
      | ms ms' bufs code Hsvc Hstep Hte IH].
  - constructor.
  - constructor; [exact Hnb | apply (IH (length buf)); lia].
  - exact IH.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma sstep_write_next_inv : forall ms model x8 buf evs c',
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fd1chan model ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = Z_to_bv 64 1 ->
  ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
  (* see [write1_check_n]: on a refused range the step is the -EFAULT *)
  access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
  (1 <= length buf)%nat ->
  sstep segs (mkCfg ms model) evs (SNext c') ->
  exists n, (1 <= n)%nat /\ (n <= length buf)%nat /\
    evs = map (WriteEv (Z_to_bv 64 1)) (firstn n buf) /\
    c' = mkCfg (advance_past_svc (set_gpr0 ms (len_word (firstn n buf)))) model.
Proof.
  intros ms model x8 buf evs c' Hh Hlazy Hfd Hsvc Hno Hg Hr Hok Hnb Hss.
  inversion Hss; subst; try congruence.
  - (* sstep_syscall *)
    match goal with
    | H2 : ms_svc_pending ms = Some ?x, H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0) |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (write1_ok_inv segs ms x8 model eff model' evs0 buf Hfd Hno Hg Hr Hok Hnb H3)
        as (n & Hn1 & Hn2 & Heff & Hm & Hevs);
      subst eff model' evs0; exists n
    end.
    match goal with
    | Hmat : materialize_model_accesses model _ = Some ?model'' |- _ =>
        rewrite (materialize_model_accesses_no_lazy model _ Hlazy) in Hmat;
        inversion Hmat; subst model''
    end.
    rewrite apply_effect_copyins_no_write. repeat split; auto.
  - (* sstep_exit : model' halted, but write leaves model unchanged *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      H6 : m_halted ?model' = Some ?code |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (write1_ok_inv segs ms x8 model eff model' evs0 buf Hfd Hno Hg Hr Hok Hnb H3)
        as (n & _ & _ & _ & Hm & _);
      subst model'; rewrite Hh in H6; discriminate
    end.
  - (* sstep_killed : the same, through [State.m_killed_of_m_halted_none] *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      H6 : m_killed ?model' = Some ?sig |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (write1_ok_inv segs ms x8 model eff model' evs0 buf Hfd Hno Hg Hr Hok Hnb H3)
        as (n & _ & _ & _ & Hm & _);
      subst model'; rewrite (m_killed_of_m_halted_none model Hh) in H6;
      discriminate
    end.
Qed.

Lemma sstep_write_inv : forall ms model x8 buf evs st,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fd1chan model ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = Z_to_bv 64 1 ->
  ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
  access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
  buf_modeled buf ->
  (1 <= length buf)%nat ->
  sstep segs (mkCfg ms model) evs st ->
  exists n, (1 <= n)%nat /\ (n <= length buf)%nat /\
    evs = map (WriteEv (Z_to_bv 64 1)) (firstn n buf) /\
    st = SNext (mkCfg (advance_past_svc (set_gpr0 ms (len_word (firstn n buf)))) model).
Proof.
  intros ms model x8 buf evs st Hh Hlazy Hfd Hsvc Hno Hg Hr Hok Hcnt Hnb Hss.
  destruct st as [c'|].
  - destruct (sstep_write_next_inv ms model x8 buf evs c'
                Hh Hlazy Hfd Hsvc Hno Hg Hr Hok Hnb Hss) as (n & Hn1 & Hn2 & Hevs & Hc').
    exists n. repeat split; [exact Hn1 | exact Hn2 | exact Hevs | now rewrite Hc'].
  - (* SError: only [sstep_syscall_unmodeled] reaches it, and the write
       is modeled *)
    exfalso. inversion Hss; subst; try congruence.
    + match goal with
      | H2 : ms_svc_pending ms = Some ?x,
        H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
        Hmat : materialize_model_accesses ?model' _ = None |- _ =>
        assert (Hx : x = x8) by congruence; subst x;
        destruct (write1_ok_inv segs ms x8 model eff model' evs0 buf
                    Hfd Hno Hg Hr Hok Hnb H3)
          as (n & _ & _ & _ & Hm & _);
        subst model'; rewrite (materialize_model_accesses_no_lazy model _ Hlazy) in Hmat;
        discriminate
      end.
    + match goal with
      | H2 : ms_svc_pending ms = Some ?x,
        H3 : syscall_spec (sys_input segs ms ?x) model Unmodeled |- _ =>
        assert (Hx : x = x8) by congruence; subst x;
        apply (write1_no_unmodeled segs ms x8 model buf Hfd Hno Hg Hr Hcnt Hnb H3)
      end.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint wevents (bufs : list (list byte)) : list event :=
  match bufs with
  | [] => []
  | buf :: rest => map (WriteEv (Z_to_bv 64 1)) buf ++ wevents rest
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition wexit_post (bufs : list (list byte)) (code : word) (fs : Fs.Fs) : post :=
  fun tr o =>
    (exists full, wpick (Z_to_bv 64 1) bufs full /\ tr = full ++ [ExitEv code fs])
    /\ exits_with code tr o.

(* [comment removed for export] *)
Definition wexit_ready (bufs : list (list byte)) (model : Model) : Prop :=
  bufs = [] \/ fd1chan model.

Lemma to_wexit_exec : forall ms bufs code,
  to_wexit ms bufs code ->
  forall model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  wexit_ready bufs model ->
  bufs_modeled bufs ->
  OmniRun.exec segs (mkCfg ms model) (wexit_post bufs code (m_fs model)).
Proof.
  intros ms bufs code Hte.
  induction Hte as
    [ms x8 Hsvc Hx8
    | ms x8 buf bufs code Hsvc Hno Hg Hr Hok Hnb Hcont IH
    | ms ms' bufs code Hsvc Hstep Hte IH];
    intros model Hh Hlazy Hfd Hbm.
  - (* tw_exit: the one transition is the exit *)
    apply (exec_step_only segs _ _
             [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)]
             (mkCfg ms (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model))).
    + replace [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)]
        with ([] ++ [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))
                       (m_fs (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model))])
        by (cbn; reflexivity).
      apply (sstep_exit segs ms model x8 (mkEffect (Z_to_bv 64 0) [] [])
               (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model) []
               (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))).
      * exact Hh.
      * exact Hsvc.
      * apply (exit_dispatch_ok (sys_input segs ms x8) model).
        rewrite in_sysno_sys_input. exact Hx8.
      * cbn. reflexivity.
      * apply m_killed_with_halted.
    + intros evs st Hss. exact (sstep_exit_inv segs ms model x8 evs st Hh Hsvc Hx8 Hss).
    + apply exec_halt.
      * cbn. rewrite m_halted_with_halted. discriminate.
      * unfold wexit_post. cbn beta. rewrite app_nil_r. split.
        -- exists []. split; [apply wp_nil | reflexivity].
        -- cbn [exits_with cfg_model]. split;
          [ rewrite m_halted_with_halted; reflexivity
          | apply m_killed_with_halted ].
  - (* tw_write: every delivered length is a successor, each covered by the IH *)
    destruct Hfd as [Hnil | Hfd]; [discriminate Hnil |].
    apply Forall_cons_iff in Hbm as [Hb Hbs].
    apply exec_step; [exact Hh | | |].
    + (* progress: full delivery *)
      eexists; eexists.
      apply (sstep_syscall segs ms model x8
               (with_copyins [(ms_gpr ms 1, length buf)]
                  (mkEffect (len_word (firstn (length buf) buf)) [] [])) model model
               (map (WriteEv (Z_to_bv 64 1)) (firstn (length buf) buf))).
      * exact Hh.
      * exact Hsvc.
      * apply write1_ok_n; try assumption. apply Nat.le_refl.
      * exact Hh.
      * rewrite (materialize_model_accesses_no_lazy model _ Hlazy). reflexivity.
    + intros evs Hss.
      destruct (sstep_write_inv ms model x8 buf evs SError
                  Hh Hlazy Hfd Hsvc Hno Hg Hr Hok Hb Hnb Hss) as (n & _ & _ & _ & Habs).
      discriminate Habs.
    + intros evs c' Hss.
      destruct (sstep_write_inv ms model x8 buf evs (SNext c')
                  Hh Hlazy Hfd Hsvc Hno Hg Hr Hok Hb Hnb Hss) as (n & Hn1 & Hn2 & -> & Hc').
      injection Hc' as ->.
      eapply exec_conseq; [exact (IH n Hn1 Hn2 model Hh Hlazy (or_intror Hfd) Hbs) |].
      intros tr o ((full & Hpick & ->) & Hx). split.
      * exists (map (WriteEv (Z_to_bv 64 1)) (firstn n buf) ++ full).
        split; [apply wp_cons; assumption | apply app_assoc].
      * exact Hx.
  - (* tw_step: one silent instruction *)
    apply (exec_step_only segs _ _ [] (mkCfg ms' model)).
    + apply (sstep_instr segs ms model ms' model); [exact Hh | exact Hsvc |].
      rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
    + intros evs st Hss. exact (sstep_instr_inv segs ms model ms' evs st Hlazy Hsvc Hstep Hss).
    + eapply exec_conseq; [exact (IH model Hh Hlazy Hfd Hbm) |].
      intros tr o H. cbn [app]. exact H.
Qed.

Lemma to_wexit_star_admits : forall ms bufs code,
  to_wexit ms bufs code ->
  forall model full,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  wexit_ready bufs model ->
  bufs_modeled bufs ->
  wpick (Z_to_bv 64 1) bufs full ->
  exists c, star segs (mkCfg ms model) (full ++ [ExitEv code (m_fs model)]) c.
Proof.
  intros ms bufs code Hte.
  induction Hte as
    [ms x8 Hsvc Hx8
    | ms x8 buf bufs code Hsvc Hno Hg Hr Hok Hnb Hcont IH
    | ms ms' bufs code Hsvc Hstep Hte IH];
    intros model full Hh Hlazy Hfd Hbm Hpick.
  - (* tw_exit *)
    inversion Hpick; subst. cbn [app].
    exists (mkCfg ms (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model)).
    apply star_one.
    replace [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)]
      with ([] ++ [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))
                     (m_fs (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model))])
      by (cbn; reflexivity).
    apply (sstep_exit segs ms model x8 (mkEffect (Z_to_bv 64 0) [] [])
             (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model) []
             (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))).
    + exact Hh.
    + exact Hsvc.
    + apply (exit_dispatch_ok (sys_input segs ms x8) model).
      rewrite in_sysno_sys_input. exact Hx8.
    + cbn. reflexivity.
    + apply m_killed_with_halted.
  - (* tw_write *)
    destruct Hfd as [Hnil | Hfd]; [discriminate Hnil |].
    apply Forall_cons_iff in Hbm as [Hb Hbs].
    inversion Hpick as [|buf' bufs' n tr Hn1 Hn2 Hpick']; subst.
    destruct (IH n Hn1 Hn2 model tr Hh Hlazy (or_intror Hfd) Hbs Hpick') as [c Hstar].
    exists c. rewrite <- app_assoc.
    eapply star_step; [| exact Hstar].
    rewrite <- (apply_effect_copyins_no_write ms
                  (len_word (firstn n buf)) [(ms_gpr ms 1, n)]).
    apply (sstep_syscall segs ms model x8
             (with_copyins [(ms_gpr ms 1, n)]
                (mkEffect (len_word (firstn n buf)) [] [])) model model
             (map (WriteEv (Z_to_bv 64 1)) (firstn n buf))).
    + exact Hh.
    + exact Hsvc.
    + apply write1_ok_n; assumption.
    + exact Hh.
    + rewrite (materialize_model_accesses_no_lazy model _ Hlazy). reflexivity.
  - (* tw_step *)
    destruct (IH model full Hh Hlazy Hfd Hbm Hpick) as [c Hstar].
    exists c.
    replace (full ++ [ExitEv code (m_fs model)])
      with ([] ++ (full ++ [ExitEv code (m_fs model)])) by reflexivity.
    eapply star_step; [| exact Hstar].
    apply (sstep_instr segs ms model ms' model); [exact Hh | exact Hsvc |].
    rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
Qed.

Lemma to_wexit_star_only : forall ms bufs code,
  to_wexit ms bufs code ->
  forall model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  wexit_ready bufs model ->
  bufs_modeled bufs ->
  forall tr c, star segs (mkCfg ms model) tr c ->
    exists full, wpick (Z_to_bv 64 1) bufs full /\
      is_prefix tr (full ++ [ExitEv code (m_fs model)]).
Proof.
  intros ms bufs code Hte model Hh Hlazy Hfd Hbm tr c Hstar.
  destruct (exec_realizes _ _ _
              (exec_star _ _ _ _ _ (to_wexit_exec ms bufs code Hte model Hh Hlazy Hfd Hbm) Hstar))
    as (tr' & o & _ & HQ).
  unfold wexit_post in HQ. cbn beta in HQ. destruct HQ as ((full & Hpick & Heq) & _).
  exists full. split; [exact Hpick |]. rewrite <- Heq. apply is_prefix_app.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma to_wexit_no_error : forall ms model bufs code,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  wexit_ready bufs model ->
  to_wexit ms bufs code ->
  bufs_modeled bufs ->
  ~ reaches_error segs (mkCfg ms model).
Proof.
  intros ms model bufs code Hh Hlazy Hfd Hte Hbm. apply exec_no_error.
  eapply exec_conseq; [exact (to_wexit_exec ms bufs code Hte model Hh Hlazy Hfd Hbm) |].
  intros tr o (_ & Hx). exact (exits_with_never_errors _ _ _ Hx).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive wfirst_ok : machine_state -> Prop :=
| wfo_write : forall ms x8,
    ms_svc_pending ms = Some x8 ->
    access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
    wfirst_ok ms
| wfo_step : forall ms ms',
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    wfirst_ok ms' ->
    wfirst_ok ms.

Lemma msteps_wfirst_ok : forall ms ms',
  msteps ms ms' -> wfirst_ok ms' -> wfirst_ok ms.
Proof.
  intros ms ms' H; induction H; [auto|].
  intro Hw. eapply wfo_step; eauto.
Qed.

(* [comment removed for export] *)
Definition wkill_post (fs : Fs.Fs) : post :=
  fun tr o =>
    tr = [KillEv (Z_to_bv 64 SIGPIPE) fs]
    /\ match o with
       | OHalt c => m_killed (cfg_model c) = Some (Z_to_bv 64 SIGPIPE)
       | OError _ => False
       end.

(* [comment removed for export] *)
Lemma sstep_write_dead_inv : forall ms model x8 evs st,
  m_halted model = None ->
  fd1dead model ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = Z_to_bv 64 1 ->
  access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
  w_is0 (ms_gpr ms 2) = false ->
  sstep segs (mkCfg ms model) evs st ->
  evs = [KillEv (Z_to_bv 64 SIGPIPE) (m_fs model)]
  /\ st = SNext (mkCfg ms (with_killed (Z_to_bv 64 SIGPIPE) model)).
Proof.
  intros ms model x8 evs st Hh Hd Hsvc Hno Hg Hok Hc Hss.
  inversion Hss; subst; try congruence.
  all: match goal with
       | H2 : ms_svc_pending ?m = Some ?x,
         H3 : syscall_spec (sys_input segs ?m ?x) _ _ |- _ =>
           try (assert (Hx : x = x8) by congruence; subst x)
       end.
  all: match goal with
       | H3 : syscall_spec (sys_input segs ?m ?x) ?mo Unmodeled |- _ =>
           exfalso; exact (write1_dead_no_unmodeled segs m x mo Hd Hno Hg Hok Hc H3)
       | H3 : syscall_spec (sys_input segs ?m ?x) ?mo (Ok ?eff ?model' ?evs0) |- _ =>
           destruct (write1_dead_ok_inv segs m x mo eff model' evs0
                       Hd Hno Hg Hok Hc H3) as (-> & -> & ->)
       end.
  all: rewrite ?m_halted_with_killed, ?m_killed_with_killed in *;
       try discriminate.
  match goal with
  | H : Some _ = Some ?sig |- _ => injection H as Hsig; subst sig
  end.
  split; reflexivity.
Qed.

Lemma to_wexit_kill_exec : forall ms bufs code,
  to_wexit ms bufs code ->
  bufs <> [] ->
  wfirst_ok ms ->
  forall model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fd1dead model ->
  OmniRun.exec segs (mkCfg ms model) (wkill_post (m_fs model)).
Proof.
  intros ms bufs code Hte.
  induction Hte as
    [ms x8 Hsvc Hx8
    | ms x8 buf bufs code Hsvc Hno Hg Hr _ Hnb Hcont IH
    | ms ms' bufs code Hsvc Hstep Hte IH];
    intros Hne Hfo model Hh Hlazy Hd.
  - exfalso. exact (Hne eq_refl).
  - (* [comment removed for export] *)
    assert (Hok : access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true).
    { inversion Hfo; subst; [assumption | congruence]. }
    assert (Hrb : read_bytes_map (in_mem (sys_input segs ms x8))
                    (ms_gpr ms 1) (ms_gpr ms 2) = Some buf).
    { rewrite in_mem_sys_input, read_bytes_map_read_byte. exact Hr. }
    pose proof (read_bytes_map_length _ _ _ _ Hrb) as Hlen.
    assert (Hc : w_is0 (ms_gpr ms 2) = false) by (apply w_is0_pos; lia).
    apply (exec_step_only segs _ _ [KillEv (Z_to_bv 64 SIGPIPE) (m_fs model)]
             (mkCfg ms (with_killed (Z_to_bv 64 SIGPIPE) model))).
    + replace [KillEv (Z_to_bv 64 SIGPIPE) (m_fs model)]
        with ([] ++ [KillEv (Z_to_bv 64 SIGPIPE)
                       (m_fs (with_killed (Z_to_bv 64 SIGPIPE) model))])
        by reflexivity.
      apply (sstep_killed segs ms model x8 (mkEffect (errno_ret EPIPE) [] [])
               (with_killed (Z_to_bv 64 SIGPIPE) model) [] (Z_to_bv 64 SIGPIPE)).
      * exact Hh.
      * exact Hsvc.
      * exact (write1_dead_ok segs ms x8 model Hd Hno Hg Hok Hc).
      * apply m_killed_with_killed.
    + intros evs st Hss.
      exact (sstep_write_dead_inv ms model x8 evs st Hh Hd Hsvc Hno Hg Hok Hc Hss).
    + apply exec_halt.
      * cbn [cfg_model]. rewrite m_halted_with_killed. discriminate.
      * cbv beta. unfold wkill_post.
        split; [rewrite app_nil_r; reflexivity |].
        cbn [cfg_model]. apply m_killed_with_killed.
  - (* [comment removed for export] *)
    assert (Hfo' : wfirst_ok ms').
    { inversion Hfo; subst; [congruence |].
      match goal with
      | Hs : RiscvSemantics.step segs ms = MachineOk ?m2, Hw : wfirst_ok ?m2 |- _ =>
          rewrite Hstep in Hs; injection Hs as Hm2; subst m2; exact Hw
      end. }
    apply (exec_step_only segs _ _ [] (mkCfg ms' model)).
    + apply (sstep_instr segs ms model ms' model); [exact Hh | exact Hsvc |].
      rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
    + intros evs st Hss. exact (sstep_instr_inv segs ms model ms' evs st Hlazy Hsvc Hstep Hss).
    + eapply exec_conseq; [exact (IH Hne Hfo' model Hh Hlazy Hd) |].
      intros tr o H. cbn [app]. exact H.
Qed.

Lemma to_wexit_kill_obs_iff : forall ms bufs code model,
  to_wexit ms bufs code -> bufs <> [] -> wfirst_ok ms ->
  m_halted model = None -> m_vm_lazy model = [] -> fd1dead model ->
  forall tr, obs_trace segs (mkCfg ms model) tr
             <-> is_prefix tr [KillEv (Z_to_bv 64 SIGPIPE) (m_fs model)].
Proof.
  intros ms bufs code model Hte Hne Hfo Hh Hlazy Hd.
  apply exec_obs_iff.
  eapply exec_conseq;
    [exact (to_wexit_kill_exec ms bufs code Hte Hne Hfo model Hh Hlazy Hd) |].
  intros tr o (Htr & Ho). split; [exact Htr |].
  destruct o; [exact (fun h => h) | destruct Ho].
Qed.

Lemma to_wexit_kill_no_error : forall ms bufs code model,
  to_wexit ms bufs code -> bufs <> [] -> wfirst_ok ms ->
  m_halted model = None -> m_vm_lazy model = [] -> fd1dead model ->
  ~ reaches_error segs (mkCfg ms model).
Proof.
  intros ms bufs code model Hte Hne Hfo Hh Hlazy Hd. apply exec_no_error.
  eapply exec_conseq;
    [exact (to_wexit_kill_exec ms bufs code Hte Hne Hfo model Hh Hlazy Hd) |].
  intros tr o (_ & Ho). destruct o; [exact (fun h => h) | destruct Ho].
Qed.

End WithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition wexit_launch (bufs : list (list byte)) (inp : ProcInput) : Prop :=
  bufs = [] \/ in_channel_reader inp = true.

Lemma init_model_fd1chan : forall reserved brk0 mb sp lim inp,
  in_channel_reader inp = true ->
  fd1chan (init_model reserved brk0 mb sp lim inp).
Proof. intros reserved brk0 mb sp lim inp Hr. split; [reflexivity | exact Hr]. Qed.

Lemma init_model_wexit_ready : forall reserved brk0 mb sp lim inp bufs,
  wexit_launch bufs inp ->
  wexit_ready bufs (init_model reserved brk0 mb sp lim inp).
Proof.
  intros reserved brk0 mb sp lim inp bufs [Hnil | Hr];
    [left; exact Hnil | right; apply init_model_fd1chan; exact Hr].
Qed.

(* [comment removed for export] *)
Lemma wexit_ready_with_vdso : forall v m bufs,
  wexit_ready bufs m -> wexit_ready bufs (with_vdso v m).
Proof. intros v m bufs [Hnil | Hr]; [left; exact Hnil | right; exact Hr]. Qed.

(* [comment removed for export] *)
Lemma fd1dead_with_vdso : forall v m, fd1dead m -> fd1dead (with_vdso v m).
Proof. intros v m H; exact H. Qed.

(* [comment removed for export] *)
Definition sigpipe_fatal (inp : ProcInput) : Prop :=
  in_sigpipe_default inp = true /\ in_sigpipe_terminal inp = true
  /\ sigpipe_blocked (in_sigmask inp) = false.

Lemma init_model_fd1dead : forall reserved brk0 mb sp lim inp,
  in_channel_reader inp = false ->
  sigpipe_fatal inp ->
  fd1dead (init_model reserved brk0 mb sp lim inp).
Proof.
  intros reserved brk0 mb sp lim inp Hr (Hd & Ht & Hm).
  split; [reflexivity | split; [exact Hr | split; [exact Hd | split; [exact Ht | exact Hm]]]].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma cat_omni_run_te : forall segs pc ph sp brk0 mb rnd lim inp bufs code,
  to_wexit (run_segments segs inp sp mb) (init_machine_state (run_segments segs inp sp mb) pc ph sp mb rnd inp) bufs code ->
  bufs_modeled bufs ->
  wexit_launch bufs inp ->
  omni_run (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp
    (wexit_post bufs code (in_fs inp)).
Proof.
  intros segs pc ph sp brk0 mb rnd lim inp bufs code Hte Hbm Hl.
  cbn [omni_run]. unfold init_config.
  exact (to_wexit_exec (run_segments segs inp sp mb) _ bufs code Hte
           (with_vdso (vdso_run_init (ed_vdso rnd))
              (init_model (segments_reserved (run_segments segs inp sp mb)) brk0 mb sp lim inp))
           eq_refl eq_refl
           (wexit_ready_with_vdso _ _ _
              (init_model_wexit_ready
                 (segments_reserved (run_segments segs inp sp mb)) brk0 mb sp
                 lim inp bufs Hl)) Hbm).
Qed.

Lemma cat_obs_iff_te : forall segs pc ph sp brk0 mb rnd lim inp bufs code,
  to_wexit (run_segments segs inp sp mb) (init_machine_state (run_segments segs inp sp mb) pc ph sp mb rnd inp) bufs code ->
  bufs_modeled bufs ->
  wexit_launch bufs inp ->
  forall tr, obs_trace (run_segments segs inp sp mb) (init_config (run_segments segs inp sp mb) pc ph sp brk0 mb rnd lim inp) tr
             <-> exists full, wpick (Z_to_bv 64 1) bufs full /\
                 is_prefix tr (full ++ [ExitEv code (in_fs inp)]).
Proof.
  intros segs pc ph sp brk0 mb rnd lim inp bufs code Hte Hbm Hl tr.
  set (fs0 := in_fs inp) in *.
  unfold init_config in *.
  set (ms := init_machine_state (run_segments segs inp sp mb) pc ph sp mb rnd inp) in *.
  assert (Hh : m_halted (with_vdso (vdso_run_init (ed_vdso rnd))
              (init_model (segments_reserved (run_segments segs inp sp mb)) brk0 mb sp lim inp)) = None) by reflexivity.
  assert (Hlazy : m_vm_lazy (with_vdso (vdso_run_init (ed_vdso rnd))
              (init_model (segments_reserved (run_segments segs inp sp mb)) brk0 mb sp lim inp)) = []) by reflexivity.
  assert (Hfd : wexit_ready bufs (with_vdso (vdso_run_init (ed_vdso rnd))
              (init_model (segments_reserved (run_segments segs inp sp mb)) brk0 mb sp lim inp)))
    by (apply wexit_ready_with_vdso;
        apply init_model_wexit_ready; exact Hl).
  assert (Hfs : m_fs (with_vdso (vdso_run_init (ed_vdso rnd))
              (init_model (segments_reserved (run_segments segs inp sp mb)) brk0 mb sp lim inp)) = fs0) by reflexivity.
  split.
  - intros (tr' & c & Hstar & Hp).
    destruct (to_wexit_star_only (run_segments segs inp sp mb) ms bufs code Hte _ Hh Hlazy Hfd Hbm tr' c Hstar)
      as (full & Hw & Hpref).
    rewrite Hfs in Hpref.
    exists full. split; [exact Hw|].
    eapply is_prefix_trans; eauto.
  - intros (full & Hw & Hp).
    destruct (to_wexit_star_admits (run_segments segs inp sp mb) ms bufs code Hte _ full Hh Hlazy Hfd Hbm Hw)
      as [c Hstar].
    rewrite Hfs in Hstar.
    exists (full ++ [ExitEv code fs0]), c. split; assumption.
Qed.

Lemma cat_no_error_run_te : forall segs pc ph sp brk0 mb rnd lim inp bufs code,
  to_wexit (run_segments segs inp sp mb) (init_machine_state (run_segments segs inp sp mb) pc ph sp mb rnd inp) bufs code ->
  bufs_modeled bufs ->
  wexit_launch bufs inp ->
  ~ reaches_error (run_segments segs inp sp mb) (init_config (run_segments segs inp sp mb) pc ph sp brk0 mb rnd lim inp).
Proof.
  intros segs pc ph sp brk0 mb rnd lim inp bufs code Hte Hbm Hl. apply exec_no_error.
  eapply exec_conseq; [exact (cat_omni_run_te segs pc ph sp brk0 mb rnd lim inp bufs code Hte Hbm Hl) |].
  intros tr o (_ & Hx). exact (exits_with_never_errors _ _ _ Hx).
Qed.

(* [comment removed for export] *)
Lemma cat_must_exit_with_te : forall segs pc ph sp brk0 mb rnd lim inp bufs code,
  to_wexit (run_segments segs inp sp mb) (init_machine_state (run_segments segs inp sp mb) pc ph sp mb rnd inp) bufs code ->
  bufs_modeled bufs ->
  wexit_launch bufs inp ->
  must_exit_with code (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp.
Proof.
  intros segs pc ph sp brk0 mb rnd lim inp bufs code Hte Hbm Hl. apply must_exit_with_iff.
  eapply exec_conseq; [exact (cat_omni_run_te segs pc ph sp brk0 mb rnd lim inp bufs code Hte Hbm Hl) |].
  intros tr o (_ & Hx). exact Hx.
Qed.

Lemma cat_omni_run_te_code_unique : forall segs pc ph sp brk0 mb rnd lim inp bufs code code',
  to_wexit (run_segments segs inp sp mb) (init_machine_state (run_segments segs inp sp mb) pc ph sp mb rnd inp) bufs code ->
  bufs_modeled bufs ->
  wexit_launch bufs inp ->
  omni_run (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp (exits_with code') ->
  code' = code.
Proof.
  intros segs pc ph sp brk0 mb rnd lim inp bufs code code' Hte Hbm Hl Hex.
  pose proof (cat_omni_run_te segs pc ph sp brk0 mb rnd lim inp bufs code Hte Hbm Hl) as Hrun.
  cbn [omni_run] in Hrun, Hex.
  destruct (exec_realizes _ _ _ Hrun) as (tr & [c' | c'] & Hm & _ & Hx); [| destruct Hx].
  pose proof (exec_sound _ _ _ Hex _ _ Hm) as Hx'.
  cbn [exits_with] in Hx, Hx'. destruct Hx as (Hx & _). destruct Hx' as (Hx' & _).
  rewrite Hx in Hx'. injection Hx' as Hx'. symmetry. exact Hx'.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma cat_kill_omni_run_te : forall segs pc ph sp brk0 mb rnd lim inp bufs code,
  to_wexit (run_segments segs inp sp mb)
    (init_machine_state (run_segments segs inp sp mb) pc ph sp mb rnd inp)
    bufs code ->
  bufs <> [] ->
  wfirst_ok (run_segments segs inp sp mb)
    (init_machine_state (run_segments segs inp sp mb) pc ph sp mb rnd inp) ->
  in_channel_reader inp = false ->
  sigpipe_fatal inp ->
  omni_run (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp
    (wkill_post (in_fs inp)).
Proof.
  intros segs pc ph sp brk0 mb rnd lim inp bufs code Hte Hne Hfo Hr Hm.
  cbn [omni_run]. unfold init_config.
  exact (to_wexit_kill_exec (run_segments segs inp sp mb) _ bufs code Hte Hne Hfo
           (with_vdso (vdso_run_init (ed_vdso rnd))
              (init_model (segments_reserved (run_segments segs inp sp mb)) brk0 mb sp lim inp))
           eq_refl eq_refl
           (fd1dead_with_vdso _ _
              (init_model_fd1dead
                 (segments_reserved (run_segments segs inp sp mb)) brk0 mb sp
                 lim inp Hr Hm))).
Qed.

Lemma cat_kill_obs_iff_te : forall segs pc ph sp brk0 mb rnd lim inp bufs code,
  to_wexit (run_segments segs inp sp mb)
    (init_machine_state (run_segments segs inp sp mb) pc ph sp mb rnd inp)
    bufs code ->
  bufs <> [] ->
  wfirst_ok (run_segments segs inp sp mb)
    (init_machine_state (run_segments segs inp sp mb) pc ph sp mb rnd inp) ->
  in_channel_reader inp = false ->
  sigpipe_fatal inp ->
  forall tr, obs_trace (run_segments segs inp sp mb)
               (init_config (run_segments segs inp sp mb) pc ph sp brk0 mb rnd lim inp) tr
             <-> is_prefix tr [KillEv (Z_to_bv 64 SIGPIPE) (in_fs inp)].
Proof.
  intros segs pc ph sp brk0 mb rnd lim inp bufs code Hte Hne Hfo Hr Hm tr.
  unfold init_config.
  exact (to_wexit_kill_obs_iff (run_segments segs inp sp mb) _ bufs code
           (with_vdso (vdso_run_init (ed_vdso rnd))
              (init_model (segments_reserved (run_segments segs inp sp mb)) brk0 mb sp lim inp))
           Hte Hne Hfo eq_refl eq_refl
           (fd1dead_with_vdso _ _
              (init_model_fd1dead
                 (segments_reserved (run_segments segs inp sp mb)) brk0 mb sp
                 lim inp Hr Hm)) tr).
Qed.

Lemma cat_kill_no_error_run_te : forall segs pc ph sp brk0 mb rnd lim inp bufs code,
  to_wexit (run_segments segs inp sp mb)
    (init_machine_state (run_segments segs inp sp mb) pc ph sp mb rnd inp)
    bufs code ->
  bufs <> [] ->
  wfirst_ok (run_segments segs inp sp mb)
    (init_machine_state (run_segments segs inp sp mb) pc ph sp mb rnd inp) ->
  in_channel_reader inp = false ->
  sigpipe_fatal inp ->
  ~ reaches_error (run_segments segs inp sp mb)
      (init_config (run_segments segs inp sp mb) pc ph sp brk0 mb rnd lim inp).
Proof.
  intros segs pc ph sp brk0 mb rnd lim inp bufs code Hte Hne Hfo Hr Hm.
  unfold init_config.
  exact (to_wexit_kill_no_error (run_segments segs inp sp mb) _ bufs code
           (with_vdso (vdso_run_init (ed_vdso rnd))
              (init_model (segments_reserved (run_segments segs inp sp mb)) brk0 mb sp lim inp))
           Hte Hne Hfo eq_refl eq_refl
           (fd1dead_with_vdso _ _
              (init_model_fd1dead
                 (segments_reserved (run_segments segs inp sp mb)) brk0 mb sp
                 lim inp Hr Hm))).
Qed.

(* [comment removed for export] *)
Definition cat_launch (source_segs : list Segment) (ms_source : machine_state)
    (target_segs : list Segment) (ms_target : machine_state)
    (bufs : list (list byte)) (inp : ProcInput) : Prop :=
  wexit_launch bufs inp
  \/ (sigpipe_fatal inp
      /\ wfirst_ok source_segs ms_source /\ wfirst_ok target_segs ms_target).

Lemma cat_launch_cases : forall source_segs ms_source target_segs ms_target bufs inp,
  cat_launch source_segs ms_source target_segs ms_target bufs inp ->
  wexit_launch bufs inp
  \/ (bufs <> [] /\ in_channel_reader inp = false
      /\ sigpipe_fatal inp
      /\ wfirst_ok source_segs ms_source /\ wfirst_ok target_segs ms_target).
Proof.
  intros source_segs ms_source target_segs ms_target bufs inp
    [Hw | (Hm & Hfs & Hft)]; [left; exact Hw |].
  destruct bufs as [| b bs]; [left; left; reflexivity |].
  destruct (in_channel_reader inp) eqn:Hr; [left; right; exact Hr |].
  right. split; [discriminate |].
  split; [reflexivity | split; [exact Hm | split; [exact Hfs | exact Hft]]].
Qed.

(* [comment removed for export] *)
Lemma cat_omni_strong_equiv_te :
  forall source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd bufs code inp,
  to_wexit (run_segments source_segs inp rsp rmb)
    (init_machine_state (run_segments source_segs inp rsp rmb) rpc rph rsp rmb rrnd inp) bufs code ->
  to_wexit (run_segments target_segs inp asp amb)
    (init_machine_state (run_segments target_segs inp asp amb) apc aph asp amb arnd inp) bufs code ->
  bufs_modeled bufs ->
  cat_launch (run_segments source_segs inp rsp rmb)
             (init_machine_state (run_segments source_segs inp rsp rmb) rpc rph rsp rmb rrnd inp)
             (run_segments target_segs inp asp amb)
             (init_machine_state (run_segments target_segs inp asp amb) apc aph asp amb arnd inp)
             bufs inp ->
  omni_strong_equiv (mkImage source_segs rpc rph) (mkImage target_segs apc aph)
                    (mkEntry rsp rbrk rmb rrnd) (mkEntry asp abrk amb arnd) inp.
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd bufs code inp
    Hsource Htarget Hbm Hl.
  destruct (cat_launch_cases _ _ _ _ _ _ Hl) as [Hw | (Hne & Hr & Hm & Hfs & Hft)].
  - (* a reader, or no write: both runs exit after the same deliveries *)
    split.
    { cbn [img_segments].
      eapply coexec_conseq;
        [apply exec_coexec;
         exact (cat_omni_run_te source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit inp bufs code Hsource Hbm Hw) |].
      intros tr o (_ & Hx).
      exact (never_errors_covered _ _ _ (exits_with_never_errors _ _ _ Hx)). }
    right. split.
    + apply trace_equiv_iff_omni. intro tr. cbn.
      rewrite (cat_obs_iff_te source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit inp bufs code Hsource Hbm Hw tr).
      rewrite (cat_obs_iff_te target_segs apc aph asp abrk amb arnd target_alloc_limit inp bufs code Htarget Hbm Hw tr).
      reflexivity.
    + apply bh_errors_iff. cbn.
      apply (cat_no_error_run_te target_segs apc aph asp abrk amb arnd target_alloc_limit inp bufs code Htarget Hbm Hw).
  - (* no reader, signal 13 open: both runs die at their first write *)
    split.
    { cbn [img_segments].
      eapply coexec_conseq;
        [apply exec_coexec;
         exact (cat_kill_omni_run_te source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit inp bufs code
                  Hsource Hne Hfs Hr Hm) |].
      intros tr o (_ & Ho). apply never_errors_covered.
      destruct o; [exact (fun h => h) | destruct Ho]. }
    right. split.
    + apply trace_equiv_iff_omni. intro tr. cbn.
      rewrite (cat_kill_obs_iff_te source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit inp bufs code
                 Hsource Hne Hfs Hr Hm tr).
      rewrite (cat_kill_obs_iff_te target_segs apc aph asp abrk amb arnd target_alloc_limit inp bufs code
                 Htarget Hne Hft Hr Hm tr).
      reflexivity.
    + apply bh_errors_iff. cbn.
      apply (cat_kill_no_error_run_te target_segs apc aph asp abrk amb arnd target_alloc_limit inp bufs code
               Htarget Hne Hft Hr Hm).
Qed.

(* [comment removed for export] *)
Lemma cat_strong_equiv_te :
  forall source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim bufs code inp,
  to_wexit (run_segments source_segs inp rsp rmb)
    (init_machine_state (run_segments source_segs inp rsp rmb) rpc rph rsp rmb rrnd inp) bufs code ->
  to_wexit (run_segments target_segs inp asp amb)
    (init_machine_state (run_segments target_segs inp asp amb) apc aph asp amb arnd inp) bufs code ->
  bufs_modeled bufs ->
  cat_launch (run_segments source_segs inp rsp rmb)
             (init_machine_state (run_segments source_segs inp rsp rmb) rpc rph rsp rmb rrnd inp)
             (run_segments target_segs inp asp amb)
             (init_machine_state (run_segments target_segs inp asp amb) apc aph asp amb arnd inp)
             bufs inp ->
  Equivalence.modeled (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
  /\ Equivalence.equiv (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
                       (run (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp).
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim bufs code inp
    Hsource Htarget Hbm Hl.
  destruct (cat_launch_cases _ _ _ _ _ _ Hl) as [Hw | (Hne & Hr & Hm & Hfs & Hft)].
  - split.
    { apply no_error_run_modeled.
      apply (cat_no_error_run_te source_segs rpc rph rsp rbrk rmb rrnd rlim inp bufs code Hsource Hbm Hw). }
    right. split.
    + intro tr. cbn.
      rewrite (cat_obs_iff_te source_segs rpc rph rsp rbrk rmb rrnd rlim inp bufs code Hsource Hbm Hw tr).
      rewrite (cat_obs_iff_te target_segs apc aph asp abrk amb arnd alim inp bufs code Htarget Hbm Hw tr).
      reflexivity.
    + cbn. apply (cat_no_error_run_te target_segs apc aph asp abrk amb arnd alim inp bufs code Htarget Hbm Hw).
  - split.
    { apply no_error_run_modeled.
      apply (cat_kill_no_error_run_te source_segs rpc rph rsp rbrk rmb rrnd rlim inp bufs code
               Hsource Hne Hfs Hr Hm). }
    right. split.
    + intro tr. cbn.
      rewrite (cat_kill_obs_iff_te source_segs rpc rph rsp rbrk rmb rrnd rlim inp bufs code
                 Hsource Hne Hfs Hr Hm tr).
      rewrite (cat_kill_obs_iff_te target_segs apc aph asp abrk amb arnd alim inp bufs code
                 Htarget Hne Hft Hr Hm tr).
      reflexivity.
    + cbn. apply (cat_kill_no_error_run_te target_segs apc aph asp abrk amb arnd alim inp bufs code
                    Htarget Hne Hft Hr Hm).
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition fdchan (fd ch : word) (model : Model) : Prop :=
  fd_lookup (m_fds model) fd = Some (FdChannel ch) /\ w_is0 ch = false
  /\ m_channel_reader model = true.

Lemma fd1chan_fdchan : forall model,
  fd1chan model -> fdchan (Z_to_bv 64 1) (Z_to_bv 64 1) model.
Proof.
  intros model [H Hr]. split; [exact H | split; [reflexivity | exact Hr]].
Qed.

Lemma init_model_fdchan2 : forall reserved brk0 mb sp lim inp,
  in_channel_reader inp = true ->
  fdchan (Z_to_bv 64 2) (Z_to_bv 64 2) (init_model reserved brk0 mb sp lim inp).
Proof.
  intros reserved brk0 mb sp lim inp Hr.
  split; [reflexivity | split; [reflexivity | exact Hr]].
Qed.

Lemma write_ch_check_n : forall segs ms x8 model fd ch buf n,
  fdchan fd ch model ->
  fd32 fd = fd ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = fd ->
  ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
  (* see [write1_check_n] *)
  access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
  buf_modeled buf ->
  (1 <= n)%nat -> (n <= length buf)%nat ->
  check_write (sys_input segs ms x8)
    (fd32 (ms_gpr ms 0)) (ms_gpr ms 1) (ms_gpr ms 2)
    (with_copyins [(ms_gpr ms 1, n)]
      (mkEffect (len_word (firstn n buf)) [] [])) model
    = CheckOk model (map (WriteEv ch) (firstn n buf)).
Proof.
  intros segs ms x8 model fd ch buf n [Hfd [Hch Hrdr]] H32 Hno Hg Hr Hok Hcnt Hn1 Hn2.
  assert (Hrb : read_bytes_map (in_mem (sys_input segs ms x8))
                  (ms_gpr ms 1) (ms_gpr ms 2) = Some buf).
  { rewrite in_mem_sys_input, read_bytes_map_read_byte. exact Hr. }
  pose proof (read_bytes_map_length _ _ _ _ Hrb) as Hlen.
  pose proof (word_unsigned_range (ms_gpr ms 2)) as Hcr.
  assert (Hcw : (bv_unsigned (ms_gpr ms 2) <= rw_bytes_max)%Z)
    by (unfold buf_modeled in Hcnt; lia).
  assert (Hmc : negb (modeled_rw_range (ms_gpr ms 1) (ms_gpr ms 2)) = false)
    by (apply rw_range_in_range; exact Hcw).
  unfold check_write.
  rewrite Hg, H32, Hfd, Hch. cbv beta iota.
  rewrite Hmc. cbv beta iota.
  assert (Hc : w_is0 (ms_gpr ms 2) = false) by (apply w_is0_pos; lia).
  rewrite Hc. cbv beta iota. cbv zeta.
  rewrite Hok. cbn [negb]. cbv beta iota.
  rewrite Hrdr. change (negb true) with false. cbv beta iota.
  rewrite (write_source_of_rw _ _ _ Hcw), (readable_bytes_full _ _ _ _ Hrb).
  assert (Hg0 : Nat.eqb (length buf) 0 = false) by (apply Nat.eqb_neq; lia).
  rewrite Hg0. cbv beta iota. unfold with_copyins; cbn.
  assert (Hlenf : Z.of_nat (length (firstn n buf)) = Z.of_nat n)
    by (rewrite length_firstn; lia).
  assert (Hru : bv_unsigned (len_word (firstn n buf)) = Z.of_nat n).
  { rewrite (len_word_unsigned (firstn n buf));
      [exact Hlenf | rewrite Hlenf; lia]. }
  rewrite ?Hru.
  assert (Hg1 : (1 <=? Z.of_nat n)%Z = true) by (apply Z.leb_le; lia).
  assert (Hg2 : (Z.of_nat n <=? Z.of_nat (length buf))%Z = true)
    by (apply Z.leb_le; lia).
  rewrite ?Hg1, ?Hg2. cbn [andb].
  rewrite ?Nat2Z.id, bv_eqb_refl, Nat.eqb_refl. reflexivity.
Qed.

Lemma write_ch_ok_n : forall segs ms x8 model fd ch buf n,
  fdchan fd ch model -> fd32 fd = fd ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = fd ->
  ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
  access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
  buf_modeled buf ->
  (1 <= n)%nat -> (n <= length buf)%nat ->
  syscall_spec (sys_input segs ms x8) model
    (Ok (with_copyins [(ms_gpr ms 1, n)]
          (mkEffect (len_word (firstn n buf)) [] [])) model
        (map (WriteEv ch) (firstn n buf))).
Proof.
  intros segs ms x8 model fd ch buf n Hfdc H32 Hno Hg Hr Hok Hcnt Hn1 Hn2.
  apply (proj2 (syscall_spec_write _ _ _ _ _ Hno)).
  apply check_write_sound_ok. eapply write_ch_check_n; eassumption.
Qed.

Lemma write_ch_ok_inv : forall segs ms x8 model fd ch eff model' evs buf,
  fdchan fd ch model -> fd32 fd = fd ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = fd ->
  ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
  (* see [write1_ok_inv] *)
  access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
  (1 <= length buf)%nat ->
  syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
  exists n, (1 <= n)%nat /\ (n <= length buf)%nat /\
    eff = with_copyins [(ms_gpr ms 1, n)]
            (mkEffect (len_word (firstn n buf)) [] []) /\ model' = model /\
    evs = map (WriteEv ch) (firstn n buf).
Proof.
  intros segs ms x8 model fd ch eff model' evs buf Hfdc H32 Hno Hg Hr Hok Hnb Hspec.
  destruct Hfdc as [Hfd [Hch Hrdr]].
  assert (Hrb : read_bytes_map (in_mem (sys_input segs ms x8))
                  (ms_gpr ms 1) (ms_gpr ms 2) = Some buf).
  { rewrite in_mem_sys_input, read_bytes_map_read_byte. exact Hr. }
  pose proof (read_bytes_map_length _ _ _ _ Hrb) as Hlen.
  apply (proj1 (syscall_spec_write _ _ _ _ _ Hno)) in Hspec.
  apply check_write_complete_ok in Hspec.
  unfold check_write in Hspec.
  rewrite Hg, H32, Hfd, Hch in Hspec. cbv beta iota in Hspec.
  (* see [write1_ok_inv]: [Ok] rules the guard out *)
  destruct (negb (modeled_rw_range (ms_gpr ms 1) (ms_gpr ms 2)));
    cbv beta iota in Hspec; [discriminate|].
  assert (Hc : w_is0 (ms_gpr ms 2) = false) by (apply w_is0_pos; lia).
  rewrite Hc in Hspec. cbv beta iota zeta in Hspec.
  rewrite Hok in Hspec. cbn [negb] in Hspec. cbv beta iota in Hspec.
  rewrite Hrdr in Hspec. change (negb true) with false in Hspec.
  cbv beta iota in Hspec.
  (* the source the transfer sees is the CLAMPED prefix of the range the
     call named -- [buf] itself for every count under [MAX_RW_COUNT], and
     a prefix of it above, which the gate above admits at an in-range
     buffer *)
  rewrite (write_source_prefix _ _ _ _ Hrb) in Hspec.
  pose proof (rw_count_clamp_range (ms_gpr ms 2)) as Hcl.
  set (c := Z.to_nat (rw_count_clamp (ms_gpr ms 2))) in *.
  assert (Hcpos : (1 <= c)%nat)
    by (unfold c, rw_count_clamp, MAX_RW_COUNT in *; lia).
  assert (Hfl : length (firstn c buf) = Nat.min c (length buf))
    by apply length_firstn.
  assert (Hg0 : Nat.eqb (length (firstn c buf)) 0 = false)
    by (rewrite Hfl; apply Nat.eqb_neq; lia).
  rewrite Hg0 in Hspec. cbv beta iota in Hspec.
  destruct eff as [ret ws zs us cs copyins]; destruct ws as [|? ?];
    destruct zs as [|? ?]; destruct us as [|? ?];
      destruct cs as [|? ?]; try discriminate.
  destruct ((1 <=? bv_unsigned ret)%Z
            && (bv_unsigned ret <=? Z.of_nat (length (firstn c buf)))%Z) eqn:Hgr;
    [|discriminate].
  destruct (access_ranges_eqb copyins [(ms_gpr ms 1, Z.to_nat (bv_unsigned ret))])
    eqn:Hreads; [|discriminate].
  inversion Hspec; clear Hspec; subst.
  apply andb_true_iff in Hgr as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2.
  rewrite Hfl in H2.
  apply access_ranges_eqb_eq in Hreads. subst copyins.
  exists (Z.to_nat (bv_unsigned ret)).
  assert (Hff : firstn (Z.to_nat (bv_unsigned ret)) (firstn c buf)
                = firstn (Z.to_nat (bv_unsigned ret)) buf)
    by (rewrite firstn_firstn; f_equal; lia).
  rewrite Hff.
  assert (Hlw : len_word (firstn (Z.to_nat (bv_unsigned ret)) buf) = ret)
    by (apply len_word_firstn_ret; lia).
  rewrite Hlw. repeat split; try reflexivity; lia.
Qed.

Lemma write_ch_no_unmodeled : forall segs ms x8 model fd ch buf,
  fdchan fd ch model -> fd32 fd = fd ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = fd ->
  ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
  buf_modeled buf ->
  (* see [write1_no_unmodeled]: a zero [count] is genuinely unmodeled *)
  (1 <= length buf)%nat ->
  ~ syscall_spec (sys_input segs ms x8) model Unmodeled.
Proof.
  intros segs ms x8 model fd ch buf [Hfd [Hch Hrdr]] H32 Hno Hg Hr Hcnt Hnb Hspec.
  assert (Hrb : read_bytes_map (in_mem (sys_input segs ms x8))
                  (ms_gpr ms 1) (ms_gpr ms 2) = Some buf).
  { rewrite in_mem_sys_input, read_bytes_map_read_byte. exact Hr. }
  pose proof (read_bytes_map_length _ _ _ _ Hrb) as Hlen.
  assert (Hcw : (bv_unsigned (ms_gpr ms 2) <= rw_bytes_max)%Z)
    by (unfold buf_modeled in Hcnt; lia).
  assert (Hmc : negb (modeled_rw_range (ms_gpr ms 1) (ms_gpr ms 2)) = false)
    by (apply rw_range_in_range; exact Hcw).
  apply (proj1 (syscall_spec_write _ _ _ _ _ Hno)) in Hspec.
  apply (check_write_complete_unmodeled _ _ _ _ _ (mkEffect (Z_to_bv 64 0) [] []))
    in Hspec.
  unfold check_write in Hspec.
  rewrite Hg, H32, Hfd, Hch in Hspec. cbv beta iota in Hspec.
  rewrite Hmc in Hspec. cbv beta iota in Hspec.
  destruct (w_is0 (ms_gpr ms 2)) eqn:Hc; try rewrite Hc in Hspec.
  { exfalso.
    assert (Hc0 : w_is0 (ms_gpr ms 2) = false) by (apply w_is0_pos; lia).
    congruence. }
  (* [vfs_write]'s [access_ok]: a refused range is -EFAULT, an answer *)
  destruct (negb (access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)))).
  { now apply check_ret_only_no_unmodeled in Hspec. }
  rewrite Hrdr in Hspec. change (negb true) with false in Hspec.
  cbv beta iota in Hspec.
  rewrite (write_source_of_rw _ _ _ Hcw), (readable_bytes_full _ _ _ _ Hrb)
    in Hspec.
  destruct (length buf =? 0)%nat eqn:Hz; try rewrite Hz in Hspec.
  { now apply check_ret_only_no_unmodeled in Hspec. }
  discriminate Hspec.
Qed.

Section WithSegsCh.
Variable segs : list Segment.
Variable fd ch : word.

(* [comment removed for export] *)
Inductive to_wexit_ch : machine_state -> list (list byte) -> word -> Prop :=
| twc_exit : forall ms x8,
    ms_svc_pending ms = Some x8 ->
    is_exit_no x8 ->
    to_wexit_ch ms [] (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))
| twc_write : forall ms x8 buf bufs code,
    ms_svc_pending ms = Some x8 ->
    bv_unsigned x8 = 64%Z ->
    ms_gpr ms 0 = fd ->
    ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
    access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
    (1 <= length buf)%nat ->
    (forall n, (1 <= n)%nat -> (n <= length buf)%nat ->
       to_wexit_ch (advance_past_svc (set_gpr0 ms (len_word (firstn n buf)))) bufs code) ->
    to_wexit_ch ms (buf :: bufs) code
| twc_step : forall ms ms' bufs code,
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    to_wexit_ch ms' bufs code ->
    to_wexit_ch ms bufs code.

Lemma msteps_to_wexit_ch : forall ms ms' bufs code,
  msteps segs ms ms' -> to_wexit_ch ms' bufs code -> to_wexit_ch ms bufs code.
Proof.
  intros ms ms' bufs code H; induction H; [auto|].
  intro Hw. eapply twc_step; eauto.
Qed.

Hypothesis Hfd32 : fd32 fd = fd.

Lemma sstep_write_ch_inv : forall ms model x8 buf evs st,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fdchan fd ch model ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = fd ->
  ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
  access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
  buf_modeled buf ->
  (1 <= length buf)%nat ->
  sstep segs (mkCfg ms model) evs st ->
  exists n, (1 <= n)%nat /\ (n <= length buf)%nat /\
    evs = map (WriteEv ch) (firstn n buf) /\
    st = SNext (mkCfg (advance_past_svc (set_gpr0 ms (len_word (firstn n buf)))) model).
Proof.
  intros ms model x8 buf evs st Hh Hlazy Hfdc Hsvc Hno Hg Hr Hok Hcnt Hnb Hss.
  revert Hg Hfdc. inversion Hss; subst; intros Hg Hfdc; try congruence.
  - match goal with
    | H2 : ms_svc_pending ms = Some ?x, H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0) |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (write_ch_ok_inv segs ms x8 model fd ch eff model' evs0 buf Hfdc Hfd32 Hno Hg Hr Hok Hnb H3)
        as (n & Hn1 & Hn2 & Heff & Hm & Hevs);
      subst eff model' evs0; exists n
    end.
    match goal with
    | Hmat : materialize_model_accesses model _ = Some ?model'' |- _ =>
        rewrite (materialize_model_accesses_no_lazy model _ Hlazy) in Hmat;
        inversion Hmat; subst model''
    end.
    rewrite apply_effect_copyins_no_write. repeat split; auto.
  - exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      Hmat : materialize_model_accesses ?model' _ = None |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (write_ch_ok_inv segs ms x8 model fd ch eff model' evs0 buf
                  Hfdc Hfd32 Hno Hg Hr Hok Hnb H3)
        as (n & _ & _ & _ & Hm & _);
      subst model'; rewrite (materialize_model_accesses_no_lazy model _ Hlazy) in Hmat;
      discriminate
    end.
  - exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      H6 : m_halted ?model' = Some ?code |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (write_ch_ok_inv segs ms x8 model fd ch eff model' evs0 buf Hfdc Hfd32 Hno Hg Hr Hok Hnb H3)
        as (n & _ & _ & _ & Hm & _);
      subst model'; rewrite Hh in H6; discriminate
    end.
  - (* sstep_killed: the write arm hands back the model it was given, and
       a running model is not a killed one *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      H6 : m_killed ?model' = Some ?sig |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (write_ch_ok_inv segs ms x8 model fd ch eff model' evs0 buf Hfdc Hfd32 Hno Hg Hr Hok Hnb H3)
        as (n & _ & _ & _ & Hm & _);
      subst model'; rewrite (m_killed_of_m_halted_none model Hh) in H6;
      discriminate
    end.
  - exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x, H3 : syscall_spec (sys_input segs ms ?x) model Unmodeled |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      apply (write_ch_no_unmodeled segs ms x8 model fd ch buf Hfdc Hfd32 Hno Hg Hr Hcnt Hnb H3)
    end.
Qed.

End WithSegsCh.

(* [comment removed for export] *)
Lemma to_wexit_ch_1 : forall segs ms bufs code,
  to_wexit segs ms bufs code ->
  to_wexit_ch segs (Z_to_bv 64 1) ms bufs code.
Proof.
  intros segs ms bufs code H; induction H.
  - eapply twc_exit; eassumption.
  - eapply twc_write; eassumption.
  - eapply twc_step; eassumption.
Qed.

Lemma wevents_ch_1 : forall bufs, wevents_ch (Z_to_bv 64 1) bufs = wevents bufs.
Proof.
  induction bufs as [|b bs IH]; cbn [wevents_ch wevents]; [reflexivity|].
  rewrite IH. reflexivity.
Qed.
