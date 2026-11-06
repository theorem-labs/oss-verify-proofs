(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi Syscall Uaccess Dispatch SyscallTable.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import ReadWrite Open.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel Require Import Exit Fork.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition injected_sysnos : list Z := map ia_no injected_table.

Lemma lookup_injected_none : forall t n,
  existsb (Z.eqb n) (map ia_no t) = false -> lookup_injected t n = None.
Proof.
  induction t as [|a r IH]; intros n H; [reflexivity|].
  cbn [map existsb] in H. apply Bool.orb_false_elim in H as [H1 H2].
  cbn [lookup_injected]. rewrite Z.eqb_sym in H1. rewrite H1. apply IH. exact H2.
Qed.

Lemma injected_arm_outside : forall n,
  existsb (Z.eqb n) injected_sysnos = false -> injected_arm n = None.
Proof. intros n H. unfold injected_arm. apply lookup_injected_none. exact H. Qed.

Lemma spurious_refusal_cfg_outside : forall cfg i m eff,
  existsb (Z.eqb (bv_unsigned (in_sysno i))) injected_sysnos = false ->
  ~ spurious_refusal_cfg cfg i m eff.
Proof.
  intros cfg i m eff Hout. apply spurious_refusal_family_on.
  unfold injected_family_off. rewrite (injected_arm_outside _ Hout). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma spurious_refusal_cfg_sysno : forall cfg i m eff (n : Z),
  bv_unsigned (in_sysno i) = n ->
  existsb (Z.eqb n) injected_sysnos = false ->
  ~ spurious_refusal_cfg cfg i m eff.
Proof. intros cfg i m eff n <- H. exact (spurious_refusal_cfg_outside cfg i m eff H). Qed.

(* [comment removed for export] *)
Example filter_free_read : forall cfg i m eff,
  bv_unsigned (in_sysno i) = 63%Z -> ~ spurious_refusal_cfg cfg i m eff.
Proof. intros cfg i m eff H. exact (spurious_refusal_cfg_sysno cfg i m eff 63 H eq_refl). Qed.

(* [comment removed for export] *)
Lemma forced_only_arm : forall i m eff a,
  injected_arm (bv_unsigned (in_sysno i)) = Some a ->
  bv_unsigned (in_sysno i) <> 214%Z ->
  spurious_refusal_cfg forced_only_cfg i m eff <->
  (ret_in_errnos (ia_errnos a) (eff_ret eff) = true
   /\ exists eff' m' evs', syscall_spec i m (Ok eff' m' evs')
                           /\ ret_in_errnos (ia_errnos a) (eff_ret eff') = false).
Proof.
  intros i m eff a Ha Hnb.
  assert (Hr : forall r, refusal_b i m r = ret_in_errnos (ia_errnos a) r).
  { intros r. unfold refusal_b. replace (bv_unsigned (in_sysno i) =? 214)%Z with false
      by (symmetry; apply Z.eqb_neq; exact Hnb). rewrite Ha. reflexivity. }
  unfold spurious_refusal_cfg. rewrite !Hr. split.
  - intros (_ & H1 & (e' & m' & v' & Hs & H2)). split; [exact H1|]. exists e', m', v'.
    rewrite <- Hr. split; assumption.
  - intros (H1 & (e' & m' & v' & Hs & H2)). split.
    + unfold injected_family_off. rewrite Ha. destruct (ia_family a); reflexivity.
    + split; [exact H1|]. exists e', m', v'. rewrite Hr. split; assumption.
Qed.

(* [comment removed for export] *)
Lemma injected_arm_openat : injected_arm 56 = Some (mkInjectedArm 56 FamFs openat_errnos).
Proof. reflexivity. Qed.

Lemma forced_only_openat : forall i m eff,
  bv_unsigned (in_sysno i) = 56%Z ->
  spurious_refusal_cfg forced_only_cfg i m eff <->
  (ret_in_errnos openat_errnos (eff_ret eff) = true
   /\ exists eff' m' evs', syscall_spec i m (Ok eff' m' evs')
                           /\ ret_in_errnos openat_errnos (eff_ret eff') = false).
Proof.
  intros i m eff Hn.
  exact (forced_only_arm i m eff (mkInjectedArm 56 FamFs openat_errnos)
           ltac:(rewrite Hn; reflexivity) ltac:(rewrite Hn; discriminate)).
Qed.

Lemma ret_in_errnos_errno : forall es e, In e es -> ret_in_errnos es (errno_ret e) = true.
Proof.
  intros es e Hin. unfold ret_in_errnos. apply existsb_exists. exists e. split; [exact Hin|].
  apply bv_eqb_eq. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma forced_only_openat_errno_spurious : forall i m eff e,
  bv_unsigned (in_sysno i) = 56%Z ->
  In e openat_errnos -> eff_ret eff = errno_ret e ->
  (exists eff' m' evs', syscall_spec i m (Ok eff' m' evs')
                        /\ ret_in_errnos openat_errnos (eff_ret eff') = false) ->
  spurious_refusal_cfg forced_only_cfg i m eff.
Proof.
  intros i m eff e Hn He Hret Hw. apply (forced_only_openat i m eff Hn).
  rewrite Hret, (ret_in_errnos_errno _ _ He). split; [reflexivity | exact Hw].
Qed.

(* [comment removed for export] *)
Lemma openat_nonerrno_admitted : forall cfg i m eff,
  bv_unsigned (in_sysno i) = 56%Z ->
  ret_in_errnos openat_errnos (eff_ret eff) = false ->
  ~ spurious_refusal_cfg cfg i m eff.
Proof.
  intros cfg i m eff Hn Hr. apply spurious_refusal_not_refusal.
  unfold refusal_b. rewrite Hn. cbn [Z.eqb Pos.eqb]. rewrite injected_arm_openat. exact Hr.
Qed.

Lemma forced_only_openat_admitted : forall i m eff,
  bv_unsigned (in_sysno i) = 56%Z ->
  ret_in_errnos openat_errnos (eff_ret eff) = false ->
  ~ spurious_refusal_cfg forced_only_cfg i m eff.
Proof. intros i m eff. apply openat_nonerrno_admitted. Qed.

(* [comment removed for export] *)
Lemma ret_in_errnos_openat_ENOENT : ret_in_errnos openat_errnos (errno_ret ENOENT) = false.
Proof. reflexivity. Qed.
Lemma ret_in_errnos_openat_ENAMETOOLONG : ret_in_errnos openat_errnos (errno_ret ENAMETOOLONG) = false.
Proof. reflexivity. Qed.
Lemma ret_in_errnos_openat_ENOTDIR : ret_in_errnos openat_errnos (errno_ret ENOTDIR) = false.
Proof. reflexivity. Qed.

Lemma ret_in_errnos_small : forall es (r : Z),
  Forall (fun e => 0 < e < 4096)%Z es ->
  (0 <= r < 2 ^ 63)%Z ->
  ret_in_errnos es (Z_to_bv 64 r) = false.
Proof.
  intros es r Hes Hr. unfold ret_in_errnos.
  induction Hes as [|e es He Hes IH]; [reflexivity|]. cbn [existsb]. rewrite IH.
  rewrite Bool.orb_false_r. apply Bool.not_true_iff_false. intros Heq.
  apply bv_eqb_eq in Heq. apply (f_equal bv_unsigned) in Heq.
  unfold errno_ret in Heq. rewrite !Z_to_bv_unsigned in Heq.
  unfold bv_wrap, bv_modulus in Heq. cbn [Z.of_N] in Heq.
  rewrite Z.mod_small in Heq by lia.
  rewrite <- (Z.mod_add _ 1) in Heq by lia. rewrite Z.mod_small in Heq by lia. lia.
Qed.

Lemma openat_errnos_small : Forall (fun e => 0 < e < 4096)%Z openat_errnos.
Proof. repeat constructor. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac sys_unfold :=
  unfold record_copyins, with_copyins,
    err_ret, ret_only, errno_from,
    set_fds, set_vmmaps, forget_vm_range,
    set_stdin, set_fs, set_halted, set_tid,
    get_model, get_fds, get_vmmaps, modify, input, sysno, arg,
    bind, pure, choose, alt, unmodeled, emit in *.

Lemma Ok_inj {A} : forall (x x' : A) m m' e e',
  Ok x m e = Ok x' m' e' -> x = x' /\ m = m' /\ e = e'.
Proof. intros x x' m m' e e' H. injection H. auto. Qed.

Ltac inv_sys :=
  repeat first
  [ progress subst
  | match goal with
    | H : exists _, _ |- _ => destruct H
    | H : _ /\ _ |- _ => destruct H
    | H : Ok _ _ _ = Ok _ _ _ |- _ => apply Ok_inj in H; destruct H as (? & ? & ?); subst
    | H : Ok _ _ _ = Unmodeled |- _ => discriminate H
    | H : Unmodeled = Ok _ _ _ |- _ => discriminate H
    | H : Some _ = Some _ |- _ => injection H as H; subst
    | H : Some _ = None |- _ => discriminate H
    | H : None = Some _ |- _ => discriminate H
    | H : False |- _ => contradiction
    | H : true = false |- _ => discriminate H
    | H : false = true |- _ => discriminate H
    | H : _ \/ _ |- _ => destruct H
    end
  | progress cbv beta zeta in * ].

(* [comment removed for export] *)
Lemma syscall_spec_56 : forall i m o, bv_unsigned (in_sysno i) = 56%Z ->
  syscall_spec i m o <-> openat_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m o.
Proof. intros i m o E; unfold syscall_spec, dispatch; rewrite E; reflexivity. Qed.
Lemma syscall_spec_62 : forall i m o, bv_unsigned (in_sysno i) = 62%Z ->
  syscall_spec i m o <-> lseek_spec (fd32 (in_arg i 0)) (in_arg i 1) (whence32 (in_arg i 2)) i m o.
Proof. intros i m o E; unfold syscall_spec, dispatch; rewrite E; reflexivity. Qed.
Lemma syscall_spec_63 : forall i m o, bv_unsigned (in_sysno i) = 63%Z ->
  syscall_spec i m o <-> read_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m o.
Proof. intros i m o E; unfold syscall_spec, dispatch; rewrite E; reflexivity. Qed.
Lemma syscall_spec_64 : forall i m o, bv_unsigned (in_sysno i) = 64%Z ->
  syscall_spec i m o <-> write_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m o.
Proof. intros i m o E; unfold syscall_spec, dispatch; rewrite E; reflexivity. Qed.
Lemma syscall_spec_exit : forall i m o,
  bv_unsigned (in_sysno i) = 93%Z \/ bv_unsigned (in_sysno i) = 94%Z ->
  syscall_spec i m o <-> exit_spec (in_arg i 0) i m o.
Proof. intros i m o [E|E]; unfold syscall_spec, dispatch; rewrite E; reflexivity. Qed.
Lemma syscall_spec_96 : forall i m o, bv_unsigned (in_sysno i) = 96%Z ->
  syscall_spec i m o <-> set_tid_address_spec i m o.
Proof. intros i m o E; unfold syscall_spec, dispatch; rewrite E; reflexivity. Qed.
Lemma syscall_spec_214 : forall i m o, bv_unsigned (in_sysno i) = 214%Z ->
  syscall_spec i m o <-> Mmap.brk_spec (in_arg i 0) i m o.
Proof. intros i m o E; unfold syscall_spec, dispatch; rewrite E; reflexivity. Qed.
Lemma syscall_spec_222 : forall i m o, bv_unsigned (in_sysno i) = 222%Z ->
  syscall_spec i m o <->
  Mmap.mmap_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) i m o.
Proof. intros i m o E; unfold syscall_spec, dispatch; rewrite E; reflexivity. Qed.

(* [comment removed for export] *)
Lemma exit_outcome : forall code i m o,
  exit_spec code i m o <->
  o = Ok (mkEffect (Z_to_bv 64 0) [] []) (with_halted (bv_and code (Z_to_bv 64 255)) m) [].
Proof.
  intros code i m o. unfold exit_spec. sys_unfold. split.
  - destruct o as [x m' evs|]; intros H; inv_sys. rewrite app_nil_r. reflexivity.
  - intros ->. eexists _, _, _, _. split; [reflexivity|]. split; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma set_tid_fresh_outcome : forall i m o,
  m_tid m = None ->
  set_tid_address_spec i m o <->
  exists t, (0 < bv_unsigned t < PID_MAX_ENVELOPE)%Z /\ o = Ok (mkEffect t [] []) (with_tid t m) [].
Proof.
  intros i m o Htid. unfold set_tid_address_spec. sys_unfold. split.
  - destruct o as [x m' evs|]; intros H; inv_sys; rewrite Htid in *; inv_sys.
    eexists; split; [split; eassumption|reflexivity].
  - intros (t & Ht & ->). eexists _, _, _, _. split; [reflexivity|]. rewrite Htid.
    split; [|reflexivity]. eexists _, _, _, _. split; [exists t; split; [exact Ht|reflexivity]|].
    split; [|reflexivity]. eexists _, _, _, _. repeat split; reflexivity.
Qed.

Lemma set_tid_known_outcome : forall i m o t,
  m_tid m = Some t ->
  set_tid_address_spec i m o <-> o = Ok (mkEffect t [] []) m [].
Proof.
  intros i m o t Htid. unfold set_tid_address_spec. sys_unfold. split.
  - destruct o as [x m' evs|]; intros H; inv_sys; rewrite Htid in *; inv_sys. reflexivity.
  - intros ->. eexists _, _, _, _. split; [reflexivity|]. rewrite Htid. split; reflexivity.
Qed.
