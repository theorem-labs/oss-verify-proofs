(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from Spec/Monad.v, Spec/Stdio.v and Spec/Driver.v: the driver's program tree, when argv has not two entries, has only writev, ioctl and exit nodes. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes Decode.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Prelim Monad Stdio Driver.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.BudgetWit Require Import NoAlloc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope mspec_scope.

(** * The usage path's tree makes no allocation call

    [Driver.drv_pre] is the driver's [main] up to the harness call, in the
    released plain proof ([Top.AssembleP0.prog_pre] runs set_tid_address,
    then [drv_pre]).  With argc <> 2 it is
    [io_diag io (DUsage argv0) ;;; exit_k 2]: with the [io_S] style the
    plain proof uses, [Stdio.stderr_fprintf], a writev loop on fd 2; then
    [exit_k] flushes stdout ([Stdio.stdout_exit_flush]: at most an ioctl
    and a writev loop on fd 1) and exits.  [mna m] says that, from every
    state, every node of the tree of [m] is in [NoAlloc.nna];
    [drv_pre_usage_na] is the result for [drv_pre]. *)

Definition mna {St A : Type} (m : M St A) : Prop := forall s, tna (m s).

Lemma mna_ret : forall St A (a : A), mna (@mret St A a).
Proof. intros St A a s. exact I. Qed.

Lemma mna_unr : forall St A, mna (@munr St A).
Proof. intros St A s. exact I. Qed.

Lemma mna_get : forall St, mna (@mget St).
Proof. intros St s. exact I. Qed.

Lemma mna_upd : forall St (f : St -> St), mna (@mupd St f).
Proof. intros St f s. exact I. Qed.

Lemma mna_bind : forall St A B (m : M St A) (f : A -> M St B),
  mna m -> (forall a, mna (f a)) -> mna (mbind m f).
Proof.
  intros St A B m f Hm Hf s. unfold mbind.
  apply tna_ebind; [exact (Hm s) | intros [a s']; exact (Hf a s')].
Qed.

Lemma mna_sys : forall St A n (dec : resp -> option A), nna n = true -> mna (@msys St A n dec).
Proof.
  intros St A n dec Hn s. unfold msys, enode. split; [exact Hn|].
  intros rsp. cbv beta. destruct (dec rsp); exact I.
Qed.

Lemma mna_wloop : forall St fuel fd bufs, mna (@stdio_wloop St fuel fd bufs).
Proof.
  intros St fuel. induction fuel as [|fuel IH]; intros fd bufs; cbn [stdio_wloop].
  - apply mna_unr.
  - cbv zeta. apply mna_bind; [apply mna_sys; reflexivity|]. intros k. cbv beta.
    match goal with |- mna (if ?b then _ else _) => destruct b end; [apply mna_ret | apply IH].
Qed.

Lemma mna_stdio_writev : forall St fd buf s, mna (@stdio_writev St fd buf s).
Proof. intros St fd buf s. unfold stdio_writev. cbv zeta. apply mna_wloop. Qed.

Lemma mna_stderr_pieces : forall St ps buf, mna (@stderr_pieces St buf ps).
Proof.
  intros St ps. induction ps as [|p ps IH]; intros buf; cbn [stderr_pieces].
  - apply mna_ret.
  - match goal with |- mna (if ?b then _ else _) => destruct b end.
    + apply mna_bind; [apply mna_stdio_writev | intros u; cbv beta; apply IH].
    + apply IH.
Qed.

(** The usage line on fd 2. *)
Lemma mna_usage_diag : forall St (g : St -> stdout_st) (st : stdout_st -> St -> St) a0,
  mna (io_diag (io_S g st) (DUsage a0)).
Proof.
  intros St g st a0. unfold io_S. cbn [io_diag]. unfold s_diag. cbv beta iota.
  unfold stderr_fprintf.
  apply mna_bind; [apply mna_stderr_pieces | intros buf; cbv beta; apply mna_stdio_writev].
Qed.

(** The stdout flush at exit. *)
Lemma mna_exit_flush : forall St (g : St -> stdout_st) (st : stdout_st -> St -> St),
  mna (stdout_exit_flush g st).
Proof.
  intros St g st. unfold stdout_exit_flush, stdout_writefn, stdout_stdio_write, rd_so, upd_so.
  apply mna_bind; [apply mna_bind; [apply mna_get | intros x; cbv beta; apply mna_ret] | intros so; cbv beta].
  match goal with |- mna (if ?b then _ else _) => destruct b end; [| apply mna_ret].
  apply mna_bind; [apply mna_bind; [apply mna_get | intros x; cbv beta; apply mna_ret] | intros so1; cbv beta].
  apply mna_bind.
  - match goal with |- mna (if ?b then _ else _) => destruct b end; [| apply mna_ret].
    apply mna_bind; [apply mna_upd | intros u; cbv beta].
    apply mna_bind; [apply mna_sys; reflexivity | intros r; cbv beta].
    destruct r; cbv iota; first [apply mna_upd | apply mna_unr].
  - intros u. cbv beta.
    apply mna_bind; [apply mna_bind; [apply mna_get | intros x; cbv beta; apply mna_ret] | intros so2; cbv beta].
    apply mna_bind; [apply mna_stdio_writev | intros u'; cbv beta; apply mna_upd].
Qed.

(** [exit_k]: the flush, then exit. *)
Lemma mna_exit_k : forall St (g : St -> stdout_st) (st : stdout_st -> St -> St) A code,
  mna (@exit_k St (io_S g st) A code).
Proof.
  intros St g st A code. unfold exit_k, exit_model.
  apply mna_bind; [| intros e; destruct e].
  apply mna_bind; [| intros u; cbv beta; apply mna_sys; reflexivity].
  unfold io_S. cbn [io_exit]. apply mna_exit_flush.
Qed.

(** The driver's [main] up to the harness call, when argv has not two
    entries. *)
Lemma drv_pre_usage_na : forall St ptr (g : St -> stdout_st) (st : stdout_st -> St -> St)
    (dm : Z -> M St (option ptr)) (df : ptr -> M St unit) (rs : Z) (argv : list (list Z)),
  Z.of_nat (length argv) <> 2%Z -> mna (@drv_pre St ptr (io_S g st) dm df rs argv).
Proof.
  intros St ptr g st dm df rs argv Hlen. unfold drv_pre.
  replace (Z.of_nat (length argv) =? 2)%Z with false by (symmetry; apply Z.eqb_neq; exact Hlen).
  cbn [negb].
  apply mna_bind; [apply mna_usage_diag | intros u; cbv beta; apply mna_exit_k].
Qed.
