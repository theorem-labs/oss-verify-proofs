(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: the step's new vDSO, materialisation-fault and unmodeled arms, the SIGPIPE kill of a first write with no reader, and the launch facts. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Vdso Run OmniRun.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Fs.ReadWrite.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require SimInv.

Module ExitSim.
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Vdso Run OmniRun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Import SimInv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)

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
    [], []. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity.
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
  sys_destruct. rewrite app_nil_l in *. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; congruence.
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
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition exit_post (fs : Fs.Fs) : post :=
  fun tr o => tr = [ExitEv (bv_and code (Z_to_bv 64 255)) fs]
              /\ exits_with (bv_and code (Z_to_bv 64 255)) tr o.

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
Definition on_path (c : config) : Prop :=
  (m_halted (cfg_model c) = None /\ m_vm_lazy (cfg_model c) = [] /\
   to_exit (cfg_ms c))
  \/ m_halted (cfg_model c) <> None.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

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

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

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
End ExitSim.

Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.SimInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.CatSim.ExitSim.

Import ListNotations.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

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

Lemma apply_effect_no_write : forall ms r,
  apply_effect ms (mkEffect r [] []) = set_gpr0 ms r.
Proof.
  intros ms r. unfold apply_effect, set_gpr0.
  cbn [eff_ret eff_writes eff_zeros apply_zeros apply_writes].
  reflexivity.
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

Definition fd1dead (model : Model) : Prop :=
  fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1))
  /\ m_channel_reader model = false
  /\ m_sigpipe_default model = true
  /\ m_sigpipe_terminal model = true
  /\ sigpipe_blocked (m_sigmask model) = false.

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
(* [comment removed for export] *)

(* [comment removed for export] *)

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
(* [comment removed for export] *)

Section WithSegs.
Variable segs : list Segment.

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

Lemma in_mem_sys_input : forall segs ms x8,
  in_mem (sys_input segs ms x8) = ms_read_byte ms.
Proof. reflexivity. Qed.

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

Definition wexit_launch (bufs : list (list byte)) (inp : ProcInput) : Prop :=
  bufs = [] \/ in_channel_reader inp = true.

Lemma init_model_fd1chan : forall reserved brk0 mb sp lim inp,
  in_channel_reader inp = true ->
  fd1chan (init_model reserved brk0 mb sp lim inp).
Proof. intros reserved brk0 mb sp lim inp Hr. split; [reflexivity | exact Hr]. Qed.

Lemma fd1dead_with_vdso : forall v m, fd1dead m -> fd1dead (with_vdso v m).
Proof. intros v m H; exact H. Qed.
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
    (* the range [vfs_write]'s [access_ok] accepts; see [write1_check_n] *)
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

Inductive msteps : machine_state -> machine_state -> Prop :=
| mst_refl : forall ms, msteps ms ms
| mst_step : forall ms ms' ms'',
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    msteps ms' ms'' ->
    msteps ms ms''.

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

Fixpoint wevents (bufs : list (list byte)) : list event :=
  match bufs with
  | [] => []
  | buf :: rest => map (WriteEv (Z_to_bv 64 1)) buf ++ wevents rest
  end.

Definition wexit_post (bufs : list (list byte)) (code : word) (fs : Fs.Fs) : post :=
  fun tr o =>
    (exists full, wpick (Z_to_bv 64 1) bufs full /\ tr = full ++ [ExitEv code fs])
    /\ exits_with code tr o.

Definition wexit_ready (bufs : list (list byte)) (model : Model) : Prop :=
  bufs = [] \/ fd1chan model.

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

Definition wkill_post (fs : Fs.Fs) : post :=
  fun tr o =>
    tr = [KillEv (Z_to_bv 64 SIGPIPE) fs]
    /\ match o with
       | OHalt c => m_killed (cfg_model c) = Some (Z_to_bv 64 SIGPIPE)
       | OError _ => False
       end.

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
  - (* the first write: signal 13 kills the process *)
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
  - (* a silent instruction: the first write is still ahead *)
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

Lemma init_model_wexit_ready : forall reserved brk0 mb sp lim inp bufs,
  wexit_launch bufs inp ->
  wexit_ready bufs (init_model reserved brk0 mb sp lim inp).
Proof.
  intros reserved brk0 mb sp lim inp bufs [Hnil | Hr];
    [left; exact Hnil | right; apply init_model_fd1chan; exact Hr].
Qed.

Lemma wexit_ready_with_vdso : forall v m bufs,
  wexit_ready bufs m -> wexit_ready bufs (with_vdso v m).
Proof. intros v m bufs [Hnil | Hr]; [left; exact Hnil | right; exact Hr]. Qed.

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

(* [comment removed for export] *)
Definition fdchan (fd ch : word) (model : Model) : Prop :=
  fd_lookup (m_fds model) fd = Some (FdChannel ch) /\ w_is0 ch = false
  /\ m_channel_reader model = true.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

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

(* [comment removed for export] *)

Hypothesis Hfd32 : fd32 fd = fd.

(* [comment removed for export] *)

End WithSegsCh.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
