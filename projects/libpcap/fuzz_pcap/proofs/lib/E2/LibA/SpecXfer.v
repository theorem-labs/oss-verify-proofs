(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Prelude Uaccess Dispatch.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition WB (lz : list (word * word)) (mat : list word) (m : Model) : Model := with_vm_backing lz mat m.

Definition cmap (f : Model -> Model) (r : check_result) : check_result :=
  match r with CheckOk m evs => CheckOk (f m) evs | CheckReject => CheckReject | CheckUnmodeled => CheckUnmodeled end.

(* [comment removed for export] *)
Ltac head_of t := lazymatch t with ?f _ => head_of f | _ => t end.

Section Xfer.
Variables (lz : list (word * word)) (mat : list word).
Local Notation F := (WB lz mat).

Ltac norm_proj m :=
  change (m_fds (F m)) with (m_fds m) in *; change (m_fs (F m)) with (m_fs m) in *;
  change (m_pipes (F m)) with (m_pipes m) in *; change (m_stdin (F m)) with (m_stdin m) in *;
  change (m_halted (F m)) with (m_halted m) in *; change (m_tid (F m)) with (m_tid m) in *;
  change (m_net (F m)) with (m_net m) in *; change (m_conn_ix (F m)) with (m_conn_ix m) in *;
  change (m_urandom (F m)) with (m_urandom m) in *.   (* [comment removed for export] *)

Ltac destr_one :=
  match goal with
  | |- context [match ?x with _ => _ end] =>
      lazymatch type of x with
      | check_result => let h := head_of x in progress unfold h
      | _ => lazymatch x with
             | context [WB] => fail
             | _ => destruct x eqn:?
             end
      end
  end.

Ltac xfer_loop m := repeat first [ progress norm_proj m | destr_one ].

Ltac xfer_main h m :=
  intros; unfold h; xfer_loop m;
  unfold check_ret_only_copyins, check_copyins_after, check_copyin_prefix, check_copyins, check_access_ok_zero, check_efault_or,
         check_ret_only, cmap;
  try unfold check_read_urandom;   (* [comment removed for export] *)
  xfer_loop m; try reflexivity.

#[using="Type"] Lemma check_read_WB : forall i fd buf cnt eff m,
  check_read i fd buf cnt eff (F m) = cmap F (check_read i fd buf cnt eff m).
Proof. xfer_main @check_read m. Qed.

#[using="Type"] Lemma check_write_WB : forall i fd buf cnt eff m,
  check_write i fd buf cnt eff (F m) = cmap F (check_write i fd buf cnt eff m).
Proof. xfer_main @check_write m. Qed.

#[using="Type"] Lemma check_readv_WB : forall i fd iov cnt eff m,
  check_readv i fd iov cnt eff (F m) = cmap F (check_readv i fd iov cnt eff m).
Proof. xfer_main @check_readv m. Qed.

#[using="Type"] Lemma check_writev_WB : forall i fd iov cnt eff m,
  check_writev i fd iov cnt eff (F m) = cmap F (check_writev i fd iov cnt eff m).
Proof. xfer_main @check_writev m. Qed.

#[using="Type"] Lemma check_close_WB : forall fd eff m,
  check_close fd eff (F m) = cmap F (check_close fd eff m).
Proof. xfer_main @check_close m. Qed.

#[using="Type"] Lemma check_ioctl_WB : forall fd cmd eff m,
  check_ioctl fd cmd eff (F m) = cmap F (check_ioctl fd cmd eff m).
Proof. xfer_main @check_ioctl m. Qed.

#[using="Type"] Lemma check_lseek_WB : forall fd off wh eff m,
  check_lseek fd off wh eff (F m) = cmap F (check_lseek fd off wh eff m).
Proof. xfer_main @check_lseek m. Qed.

#[using="Type"] Lemma check_exit_WB : forall code eff m,
  check_exit code eff (F m) = cmap F (check_exit code eff m).
Proof. xfer_main @check_exit m. Qed.

#[using="Type"] Lemma check_unlinkat_WB : forall i dfd path flags eff m,
  check_unlinkat i dfd path flags eff (F m) = cmap F (check_unlinkat i dfd path flags eff m).
Proof. xfer_main @check_unlinkat m. Qed.

#[using="Type"] Lemma check_openat_WB : forall i dfd path flags eff m,
  check_openat i dfd path flags eff (F m) = cmap F (check_openat i dfd path flags eff m).
Proof. xfer_main @check_openat m. Qed.

(* [comment removed for export] *)

Definition fs_sysno (k : Z) : bool :=
  (k =? 29) || (k =? 35) || (k =? 56) || (k =? 57) || (k =? 62) || (k =? 63) || (k =? 64) || (k =? 65) || (k =? 66) || (k =? 93) || (k =? 94).

#[using="Type"] Lemma check_syscall_WB : forall i eff m,
  fs_sysno (bv_unsigned (in_sysno i)) = true ->
  check_syscall i eff (F m) = cmap F (check_syscall i eff m).
Proof.
  intros i eff m H. unfold check_syscall. unfold fs_sysno in H.
  repeat (apply orb_prop in H as [H|H]); apply Z.eqb_eq in H; rewrite H.
  - change (lookup_ca checked_table 29) with (Some arm_ioctl). cbv beta iota. rewrite !ca_check_arm_ioctl. apply check_ioctl_WB.
  - change (lookup_ca checked_table 35) with (Some arm_unlinkat). cbv beta iota. rewrite !ca_check_arm_unlinkat. apply check_unlinkat_WB.
  - change (lookup_ca checked_table 56) with (Some arm_openat). cbv beta iota. rewrite !ca_check_arm_openat. apply check_openat_WB.
  - change (lookup_ca checked_table 57) with (Some arm_close). cbv beta iota. rewrite !ca_check_arm_close. apply check_close_WB.
  - change (lookup_ca checked_table 62) with (Some arm_lseek). cbv beta iota. rewrite !ca_check_arm_lseek. apply check_lseek_WB.
  - change (lookup_ca checked_table 63) with (Some arm_read). cbv beta iota. rewrite !ca_check_arm_read. apply check_read_WB.
  - change (lookup_ca checked_table 64) with (Some arm_write). cbv beta iota. rewrite !ca_check_arm_write. apply check_write_WB.
  - change (lookup_ca checked_table 65) with (Some arm_readv). cbv beta iota. rewrite !ca_check_arm_readv. apply check_readv_WB.
  - change (lookup_ca checked_table 66) with (Some arm_writev). cbv beta iota. rewrite !ca_check_arm_writev. apply check_writev_WB.
  - change (lookup_ca checked_table 93) with (Some arm_exit). cbv beta iota. rewrite !ca_check_arm_exit. apply check_exit_WB.
  - change (lookup_ca checked_table 94) with (Some arm_exit_group). cbv beta iota. rewrite !ca_check_arm_exit_group. apply check_exit_WB.
Qed.

#[using="Type"] Lemma spec_WB_ok : forall i eff m mX evs,
  fs_sysno (bv_unsigned (in_sysno i)) = true ->
  (syscall_spec i (F m) (Ok eff mX evs) <-> exists m', syscall_spec i m (Ok eff m' evs) /\ mX = F m').
Proof.
  intros i eff m mX evs H. rewrite <- check_syscall_ok_iff, (check_syscall_WB i eff m H). split.
  - destruct (check_syscall i eff m) as [m' evs'| |] eqn:E; cbn [cmap]; intros E'; try discriminate.
    injection E' as <- <-. exists m'. split; [apply check_syscall_ok_iff; exact E| reflexivity].
  - intros (m' & Hs & ->). apply check_syscall_ok_iff in Hs. rewrite Hs. reflexivity.
Qed.

#[using="Type"] Lemma spec_WB_unmodeled : forall i m,
  fs_sysno (bv_unsigned (in_sysno i)) = true ->
  (syscall_spec i (F m) Unmodeled <-> syscall_spec i m Unmodeled).
Proof.
  intros i m H. rewrite <- !(check_syscall_err_iff i (mkEffect (Z_to_bv 64 0) [] [])), (check_syscall_WB i _ m H).
  destruct (check_syscall i _ m); cbn [cmap]; split; intros E; try discriminate E; reflexivity.
Qed.

End Xfer.
