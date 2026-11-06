(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Export
  Prelude Uaccess Fs.ReadWrite Fs.Ioctl Mm.Mmap Mm.Mprotect Kernel.Exit Kernel.Fork.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Export Fs.Open.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope sys_scope.

Definition check_syscall (i : SyscallInput) (eff : SyscallEffect) (m : Model) : check_result :=
  match bv_unsigned (in_sysno i) with
  | 29%Z => check_ioctl (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) eff m
  | 56%Z => check_openat i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m
  | 57%Z => check_close (fd32 (in_arg i 0)) eff m
  | 63%Z => check_read i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m
  | 64%Z => check_write i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m
  | 66%Z => check_writev i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m
  | 93%Z => check_exit (in_arg i 0) eff m
  | 94%Z => check_exit (in_arg i 0) eff m
  | 96%Z => check_set_tid_address eff m
  | 214%Z => check_brk (in_arg i 0) eff m
  | 215%Z => check_munmap (in_arg i 0) (in_arg i 1) eff m
  | 222%Z => check_mmap (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) eff m
  | 226%Z => check_mprotect (in_arg i 0) (in_arg i 1) (in_arg i 2) eff m
  | _ => CheckUnmodeled
  end.

Definition lite_no (n : Z) : bool :=
  match n with
  | 29%Z | 56%Z | 57%Z | 63%Z | 64%Z | 66%Z | 93%Z | 94%Z | 96%Z | 214%Z | 215%Z | 222%Z | 226%Z => true
  | _ => false
  end.

Lemma check_syscall_unlisted : forall i eff m, lite_no (bv_unsigned (in_sysno i)) = false -> check_syscall i eff m = CheckUnmodeled.
Proof.
  intros i eff m H. unfold check_syscall. unfold lite_no in H.
  destruct (bv_unsigned (in_sysno i)) as [|p|p]; [reflexivity| |reflexivity].
  repeat (destruct p as [p|p|]; try discriminate H; try reflexivity).
Qed.

Lemma lite_of_not_unmodeled : forall i eff m, check_syscall i eff m <> CheckUnmodeled -> lite_no (bv_unsigned (in_sysno i)) = true.
Proof.
  intros i eff m H. destruct (lite_no (bv_unsigned (in_sysno i))) eqn:E; [reflexivity|].
  exfalso. apply H. apply check_syscall_unlisted. exact E.
Qed.

Lemma chk_at_29 : forall i eff m, bv_unsigned (in_sysno i) = 29%Z -> check_syscall i eff m = check_ioctl (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.
Lemma spec_at_29 : forall i m o, bv_unsigned (in_sysno i) = 29%Z -> syscall_spec i m o = ioctl_spec (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) i m o.
Proof. intros i m o H. unfold syscall_spec, dispatch. rewrite H. reflexivity. Qed.

Lemma chk_at_56 : forall i eff m, bv_unsigned (in_sysno i) = 56%Z -> check_syscall i eff m = check_openat i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.
Lemma spec_at_56 : forall i m o, bv_unsigned (in_sysno i) = 56%Z -> syscall_spec i m o = openat_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m o.
Proof. intros i m o H. unfold syscall_spec, dispatch. rewrite H. reflexivity. Qed.

Lemma chk_at_57 : forall i eff m, bv_unsigned (in_sysno i) = 57%Z -> check_syscall i eff m = check_close (fd32 (in_arg i 0)) eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.
Lemma spec_at_57 : forall i m o, bv_unsigned (in_sysno i) = 57%Z -> syscall_spec i m o = close_spec (fd32 (in_arg i 0)) i m o.
Proof. intros i m o H. unfold syscall_spec, dispatch. rewrite H. reflexivity. Qed.

Lemma chk_at_63 : forall i eff m, bv_unsigned (in_sysno i) = 63%Z -> check_syscall i eff m = check_read i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.
Lemma spec_at_63 : forall i m o, bv_unsigned (in_sysno i) = 63%Z -> syscall_spec i m o = read_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m o.
Proof. intros i m o H. unfold syscall_spec, dispatch. rewrite H. reflexivity. Qed.

Lemma chk_at_64 : forall i eff m, bv_unsigned (in_sysno i) = 64%Z -> check_syscall i eff m = check_write i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.
Lemma spec_at_64 : forall i m o, bv_unsigned (in_sysno i) = 64%Z -> syscall_spec i m o = write_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m o.
Proof. intros i m o H. unfold syscall_spec, dispatch. rewrite H. reflexivity. Qed.

Lemma chk_at_66 : forall i eff m, bv_unsigned (in_sysno i) = 66%Z -> check_syscall i eff m = check_writev i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.
Lemma spec_at_66 : forall i m o, bv_unsigned (in_sysno i) = 66%Z -> syscall_spec i m o = writev_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m o.
Proof. intros i m o H. unfold syscall_spec, dispatch. rewrite H. reflexivity. Qed.

Lemma chk_at_93 : forall i eff m, bv_unsigned (in_sysno i) = 93%Z -> check_syscall i eff m = check_exit (in_arg i 0) eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.
Lemma spec_at_93 : forall i m o, bv_unsigned (in_sysno i) = 93%Z -> syscall_spec i m o = exit_spec (in_arg i 0) i m o.
Proof. intros i m o H. unfold syscall_spec, dispatch. rewrite H. reflexivity. Qed.

Lemma chk_at_94 : forall i eff m, bv_unsigned (in_sysno i) = 94%Z -> check_syscall i eff m = check_exit (in_arg i 0) eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.
Lemma spec_at_94 : forall i m o, bv_unsigned (in_sysno i) = 94%Z -> syscall_spec i m o = exit_spec (in_arg i 0) i m o.
Proof. intros i m o H. unfold syscall_spec, dispatch. rewrite H. reflexivity. Qed.

Lemma chk_at_96 : forall i eff m, bv_unsigned (in_sysno i) = 96%Z -> check_syscall i eff m = check_set_tid_address eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.
Lemma spec_at_96 : forall i m o, bv_unsigned (in_sysno i) = 96%Z -> syscall_spec i m o = set_tid_address_spec i m o.
Proof. intros i m o H. unfold syscall_spec, dispatch. rewrite H. reflexivity. Qed.

Lemma chk_at_214 : forall i eff m, bv_unsigned (in_sysno i) = 214%Z -> check_syscall i eff m = check_brk (in_arg i 0) eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.
Lemma spec_at_214 : forall i m o, bv_unsigned (in_sysno i) = 214%Z -> syscall_spec i m o = brk_spec (in_arg i 0) i m o.
Proof. intros i m o H. unfold syscall_spec, dispatch. rewrite H. reflexivity. Qed.

Lemma chk_at_215 : forall i eff m, bv_unsigned (in_sysno i) = 215%Z -> check_syscall i eff m = check_munmap (in_arg i 0) (in_arg i 1) eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.
Lemma spec_at_215 : forall i m o, bv_unsigned (in_sysno i) = 215%Z -> syscall_spec i m o = munmap_spec (in_arg i 0) (in_arg i 1) i m o.
Proof. intros i m o H. unfold syscall_spec, dispatch. rewrite H. reflexivity. Qed.

Lemma chk_at_222 : forall i eff m, bv_unsigned (in_sysno i) = 222%Z -> check_syscall i eff m = check_mmap (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.
Lemma spec_at_222 : forall i m o, bv_unsigned (in_sysno i) = 222%Z -> syscall_spec i m o = mmap_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) i m o.
Proof. intros i m o H. unfold syscall_spec, dispatch. rewrite H. reflexivity. Qed.

Lemma chk_at_226 : forall i eff m, bv_unsigned (in_sysno i) = 226%Z -> check_syscall i eff m = check_mprotect (in_arg i 0) (in_arg i 1) (in_arg i 2) eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.
Lemma spec_at_226 : forall i m o, bv_unsigned (in_sysno i) = 226%Z -> syscall_spec i m o = mprotect_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) i m o.
Proof. intros i m o H. unfold syscall_spec, dispatch. rewrite H. reflexivity. Qed.

Lemma lite_cases : forall n, lite_no n = true -> n = 29%Z \/ n = 56%Z \/ n = 57%Z \/ n = 63%Z \/ n = 64%Z \/ n = 66%Z \/ n = 93%Z \/ n = 94%Z \/ n = 96%Z \/ n = 214%Z \/ n = 215%Z \/ n = 222%Z \/ n = 226%Z.
Proof.
  intros n H. unfold lite_no in H.
  destruct n as [|p|p]; try discriminate H.
  repeat (destruct p as [p|p|]; try discriminate H); lia.
Qed.

Theorem check_syscall_sound_ok : forall i eff m m' evs,
  check_syscall i eff m = CheckOk m' evs -> syscall_spec i m (Ok eff m' evs).
Proof.
  intros i eff m m' evs Hc.
  assert (Hl : lite_no (bv_unsigned (in_sysno i)) = true) by (apply (lite_of_not_unmodeled i eff m); rewrite Hc; discriminate).
  destruct (lite_cases _ Hl) as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]]]].
  - rewrite (chk_at_29 _ _ _ H) in *; rewrite (spec_at_29 _ _ _ H) in *; eauto using check_ioctl_sound_ok.
  - rewrite (chk_at_56 _ _ _ H) in *; rewrite (spec_at_56 _ _ _ H) in *; eauto using check_openat_sound_ok.
  - rewrite (chk_at_57 _ _ _ H) in *; rewrite (spec_at_57 _ _ _ H) in *; eauto using check_close_sound_ok.
  - rewrite (chk_at_63 _ _ _ H) in *; rewrite (spec_at_63 _ _ _ H) in *; eauto using check_read_sound_ok.
  - rewrite (chk_at_64 _ _ _ H) in *; rewrite (spec_at_64 _ _ _ H) in *; eauto using check_write_sound_ok.
  - rewrite (chk_at_66 _ _ _ H) in *; rewrite (spec_at_66 _ _ _ H) in *; eauto using check_writev_sound_ok.
  - rewrite (chk_at_93 _ _ _ H) in *; rewrite (spec_at_93 _ _ _ H) in *; eauto using check_exit_sound_ok.
  - rewrite (chk_at_94 _ _ _ H) in *; rewrite (spec_at_94 _ _ _ H) in *; eauto using check_exit_sound_ok.
  - rewrite (chk_at_96 _ _ _ H) in *; rewrite (spec_at_96 _ _ _ H) in *; eauto using check_set_tid_address_sound_ok.
  - rewrite (chk_at_214 _ _ _ H) in *; rewrite (spec_at_214 _ _ _ H) in *; eauto using check_brk_sound_ok.
  - rewrite (chk_at_215 _ _ _ H) in *; rewrite (spec_at_215 _ _ _ H) in *; eauto using check_munmap_sound_ok.
  - rewrite (chk_at_222 _ _ _ H) in *; rewrite (spec_at_222 _ _ _ H) in *; eauto using check_mmap_sound_ok.
  - rewrite (chk_at_226 _ _ _ H) in *; rewrite (spec_at_226 _ _ _ H) in *; eauto using check_mprotect_sound_ok.
Qed.

Theorem check_syscall_sound_unmodeled : forall i eff m,
  lite_no (bv_unsigned (in_sysno i)) = true -> check_syscall i eff m = CheckUnmodeled -> syscall_spec i m Unmodeled.
Proof.
  intros i eff m Hl Hc.
  destruct (lite_cases _ Hl) as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]]]].
  - rewrite (chk_at_29 _ _ _ H) in *; rewrite (spec_at_29 _ _ _ H) in *; eauto using check_ioctl_sound_unmodeled.
  - rewrite (chk_at_56 _ _ _ H) in *; rewrite (spec_at_56 _ _ _ H) in *; eauto using check_openat_sound_unmodeled.
  - rewrite (chk_at_57 _ _ _ H) in *; rewrite (spec_at_57 _ _ _ H) in *; eauto using check_close_sound_unmodeled.
  - rewrite (chk_at_63 _ _ _ H) in *; rewrite (spec_at_63 _ _ _ H) in *; eauto using check_read_sound_unmodeled.
  - rewrite (chk_at_64 _ _ _ H) in *; rewrite (spec_at_64 _ _ _ H) in *; eauto using check_write_sound_unmodeled.
  - rewrite (chk_at_66 _ _ _ H) in *; rewrite (spec_at_66 _ _ _ H) in *; eauto using check_writev_sound_unmodeled.
  - rewrite (chk_at_93 _ _ _ H) in *; rewrite (spec_at_93 _ _ _ H) in *; eauto using check_exit_sound_unmodeled.
  - rewrite (chk_at_94 _ _ _ H) in *; rewrite (spec_at_94 _ _ _ H) in *; eauto using check_exit_sound_unmodeled.
  - rewrite (chk_at_96 _ _ _ H) in *; rewrite (spec_at_96 _ _ _ H) in *; eauto using check_set_tid_address_sound_unmodeled.
  - rewrite (chk_at_214 _ _ _ H) in *; rewrite (spec_at_214 _ _ _ H) in *; eauto using check_brk_sound_unmodeled.
  - rewrite (chk_at_215 _ _ _ H) in *; rewrite (spec_at_215 _ _ _ H) in *; eauto using check_munmap_sound_unmodeled.
  - rewrite (chk_at_222 _ _ _ H) in *; rewrite (spec_at_222 _ _ _ H) in *; eauto using check_mmap_sound_unmodeled.
  - rewrite (chk_at_226 _ _ _ H) in *; rewrite (spec_at_226 _ _ _ H) in *; eauto using check_mprotect_sound_unmodeled.
Qed.

Theorem check_syscall_complete_ok : forall i eff m m' evs,
  lite_no (bv_unsigned (in_sysno i)) = true -> syscall_spec i m (Ok eff m' evs) -> check_syscall i eff m = CheckOk m' evs.
Proof.
  intros i eff m m' evs Hl Hs.
  destruct (lite_cases _ Hl) as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]]]].
  - rewrite (chk_at_29 _ _ _ H) in *; rewrite (spec_at_29 _ _ _ H) in *; eauto using check_ioctl_complete_ok.
  - rewrite (chk_at_56 _ _ _ H) in *; rewrite (spec_at_56 _ _ _ H) in *; eauto using check_openat_complete_ok.
  - rewrite (chk_at_57 _ _ _ H) in *; rewrite (spec_at_57 _ _ _ H) in *; eauto using check_close_complete_ok.
  - rewrite (chk_at_63 _ _ _ H) in *; rewrite (spec_at_63 _ _ _ H) in *; eauto using check_read_complete_ok.
  - rewrite (chk_at_64 _ _ _ H) in *; rewrite (spec_at_64 _ _ _ H) in *; eauto using check_write_complete_ok.
  - rewrite (chk_at_66 _ _ _ H) in *; rewrite (spec_at_66 _ _ _ H) in *; eauto using check_writev_complete_ok.
  - rewrite (chk_at_93 _ _ _ H) in *; rewrite (spec_at_93 _ _ _ H) in *; eauto using check_exit_complete_ok.
  - rewrite (chk_at_94 _ _ _ H) in *; rewrite (spec_at_94 _ _ _ H) in *; eauto using check_exit_complete_ok.
  - rewrite (chk_at_96 _ _ _ H) in *; rewrite (spec_at_96 _ _ _ H) in *; eauto using check_set_tid_address_complete_ok.
  - rewrite (chk_at_214 _ _ _ H) in *; rewrite (spec_at_214 _ _ _ H) in *; eauto using check_brk_complete_ok.
  - rewrite (chk_at_215 _ _ _ H) in *; rewrite (spec_at_215 _ _ _ H) in *; eauto using check_munmap_complete_ok.
  - rewrite (chk_at_222 _ _ _ H) in *; rewrite (spec_at_222 _ _ _ H) in *; eauto using check_mmap_complete_ok.
  - rewrite (chk_at_226 _ _ _ H) in *; rewrite (spec_at_226 _ _ _ H) in *; eauto using check_mprotect_complete_ok.
Qed.

Theorem check_syscall_complete_unmodeled : forall i m eff,
  syscall_spec i m Unmodeled -> check_syscall i eff m = CheckUnmodeled.
Proof.
  intros i m eff Hs.
  destruct (lite_no (bv_unsigned (in_sysno i))) eqn:Hl; [|apply check_syscall_unlisted; exact Hl].
  destruct (lite_cases _ Hl) as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]]]].
  - rewrite (chk_at_29 _ _ _ H) in *; rewrite (spec_at_29 _ _ _ H) in *; eauto using check_ioctl_complete_unmodeled.
  - rewrite (chk_at_56 _ _ _ H) in *; rewrite (spec_at_56 _ _ _ H) in *; eauto using check_openat_complete_unmodeled.
  - rewrite (chk_at_57 _ _ _ H) in *; rewrite (spec_at_57 _ _ _ H) in *; eauto using check_close_complete_unmodeled.
  - rewrite (chk_at_63 _ _ _ H) in *; rewrite (spec_at_63 _ _ _ H) in *; eauto using check_read_complete_unmodeled.
  - rewrite (chk_at_64 _ _ _ H) in *; rewrite (spec_at_64 _ _ _ H) in *; eauto using check_write_complete_unmodeled.
  - rewrite (chk_at_66 _ _ _ H) in *; rewrite (spec_at_66 _ _ _ H) in *; eauto using check_writev_complete_unmodeled.
  - rewrite (chk_at_93 _ _ _ H) in *; rewrite (spec_at_93 _ _ _ H) in *; eauto using check_exit_complete_unmodeled.
  - rewrite (chk_at_94 _ _ _ H) in *; rewrite (spec_at_94 _ _ _ H) in *; eauto using check_exit_complete_unmodeled.
  - rewrite (chk_at_96 _ _ _ H) in *; rewrite (spec_at_96 _ _ _ H) in *; eauto using check_set_tid_address_complete_unmodeled.
  - rewrite (chk_at_214 _ _ _ H) in *; rewrite (spec_at_214 _ _ _ H) in *; eauto using check_brk_complete_unmodeled.
  - rewrite (chk_at_215 _ _ _ H) in *; rewrite (spec_at_215 _ _ _ H) in *; eauto using check_munmap_complete_unmodeled.
  - rewrite (chk_at_222 _ _ _ H) in *; rewrite (spec_at_222 _ _ _ H) in *; eauto using check_mmap_complete_unmodeled.
  - rewrite (chk_at_226 _ _ _ H) in *; rewrite (spec_at_226 _ _ _ H) in *; eauto using check_mprotect_complete_unmodeled.
Qed.

(* [comment removed for export] *)
Theorem check_syscall_ok_iff : forall i eff m m' evs,
  lite_no (bv_unsigned (in_sysno i)) = true ->
  (check_syscall i eff m = CheckOk m' evs <-> syscall_spec i m (Ok eff m' evs)).
Proof. intros i eff m m' evs Hl. split; [apply check_syscall_sound_ok | apply check_syscall_complete_ok; exact Hl]. Qed.

Theorem check_syscall_err_iff : forall i eff m,
  lite_no (bv_unsigned (in_sysno i)) = true ->
  (check_syscall i eff m = CheckUnmodeled <-> syscall_spec i m Unmodeled).
Proof. intros i eff m Hl. split; [apply check_syscall_sound_unmodeled; exact Hl | apply check_syscall_complete_unmodeled]. Qed.

(* [comment removed for export] *)
Lemma lite_no_at : forall i n, bv_unsigned (in_sysno i) = n -> lite_no n = true -> lite_no (bv_unsigned (in_sysno i)) = true.
Proof. intros i n -> H. exact H. Qed.


(* [comment removed for export] *)
Create HintDb lite_nu.
#[export] Hint Resolve check_ret_only_no_unmodeled check_ret_only_copyins_no_unmodeled : lite_nu.
Ltac lite_solve :=
  first
  [ reflexivity
  | solve [ match goal with
            | Hnu : forall eff, check_syscall ?i eff ?m <> CheckUnmodeled |- lite_no (bv_unsigned (in_sysno ?i)) = true =>
                exact (lite_of_not_unmodeled i (mkEffect (Z_to_bv 64 0) [] []) m (Hnu _))
            end ]
  | solve [ match goal with
            | Hchk : forall eff, check_syscall ?i eff ?m = _ |- lite_no (bv_unsigned (in_sysno ?i)) = true =>
                apply (lite_of_not_unmodeled i (mkEffect (Z_to_bv 64 0) [] []) m); rewrite Hchk;
                first [ discriminate | solve [eauto with lite_nu] | (let Hu := fresh "Hu" in intro Hu; discriminate Hu) ]
            end ]
  | solve [ match goal with
            | H : bv_unsigned ?x = ?n |- _ => cbn [in_sysno sys_input]; rewrite H; reflexivity
            end ] ].

(* [comment removed for export] *)
Ltac lite_iff := first [ apply check_syscall_sound_ok | (apply check_syscall_complete_ok; [lite_solve|]) ].
Ltac lite_iff_in H := first [ apply check_syscall_sound_ok in H | (apply check_syscall_complete_ok in H; [| lite_solve]) ].
