(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from Spec/Monad.v, Spec/Stdio.v, Spec/Driver.v and Spec/Prog.v: the program tree of a run whose argv has not two entries has only writev, ioctl, set_tid_address and exit nodes. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes Decode.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import Prelim Monad Stdio Driver Prog.
From OSSVerify.Proofs.zstd.simple_decompress.lib.BudgetWit Require Import NoAlloc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

(** * The usage path's tree makes no allocation call

    [Spec.Prog.prog] is the program the released plain proof runs: [startup]
    (set_tid_address), then [Driver.main_model], then [Driver.exit_model].
    With argc <> 2, [main_model] is [io_diag io (DUsage argv0) ;;; mret 2]:
    [Stdio.stderr_fprintf], which is a loop of writev on fd 2.
    [exit_model] flushes stdout ([Stdio.stdout_exit_flush]: at most an ioctl
    and a writev loop on fd 1) and exits.  [mna m] says that, from every
    state, every node of the tree of [m] is in [NoAlloc.nna];
    [usage_tree_na] is the result for [Prog.prog], the tree that
    [Plain.PlainClosed.plain_impl_closed] speaks of. *)

Definition mna {St A : Type} (m : St -> itree node (Exc.exc (A * St))) : Prop :=
  forall s, tna (m s).

Lemma mna_ret : forall St A (a : A), mna (@mret St A a).
Proof. intros St A a s. exact I. Qed.

Lemma mna_unr : forall St A, mna (@munr St A).
Proof. intros St A s. exact I. Qed.

Lemma mna_get : forall St, mna (@mget St).
Proof. intros St s. exact I. Qed.

Lemma mna_upd : forall St (f : St -> St), mna (@mupd St f).
Proof. intros St f s. exact I. Qed.

Lemma mna_bind : forall St A B (m : St -> itree node (Exc.exc (A * St)))
    (f : A -> St -> itree node (Exc.exc (B * St))),
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

Lemma mna_stdio_write_loop : forall St fuel fd iov, mna (@stdio_write_loop St fuel fd iov).
Proof.
  intros St fuel. induction fuel as [|fuel IH]; intros fd iov; cbn [stdio_write_loop].
  - apply mna_unr.
  - apply mna_bind; [apply mna_sys; reflexivity|]. intros cnt. cbv beta.
    match goal with |- mna (if ?b then _ else _) => destruct b end; [apply mna_ret | apply IH].
Qed.

Lemma mna_stdio_write : forall St fd buf s, mna (@stdio_write St fd buf s).
Proof.
  intros St fd buf s. unfold stdio_write.
  match goal with |- mna (if ?b then _ else _) => destruct b end;
    [apply mna_unr | apply mna_stdio_write_loop].
Qed.

Lemma mna_stderr_pieces : forall St ps buf, mna (@stderr_pieces St buf ps).
Proof.
  intros St ps. induction ps as [|p ps IH]; intros buf; cbn [stderr_pieces].
  - apply mna_ret.
  - match goal with |- mna (if ?b then _ else _) => destruct b end.
    + apply mna_bind; [apply mna_stdio_write | intros u; cbv beta; apply IH].
    + apply IH.
Qed.

Lemma mna_io_diag : forall St (g : St -> stdout_st) (st : stdout_st -> St -> St) d,
  mna (io_diag (io_S g st) d).
Proof.
  intros St g st d. unfold io_S. cbn [io_diag]. unfold s_diag.
  destruct d; cbv iota.
  all: first
    [ unfold stderr_fprintf;
      apply mna_bind; [apply mna_stderr_pieces | intros buf; cbv beta; apply mna_stdio_write]
    | unfold stderr_fwrite;
      match goal with |- mna (if ?b then _ else _) => destruct b end;
      [apply mna_stdio_write | apply mna_ret] ].
Qed.

Lemma mna_io_exit : forall St (g : St -> stdout_st) (st : stdout_st -> St -> St),
  mna (io_exit (io_S g st)).
Proof.
  intros St g st. unfold io_S. cbn [io_exit].
  unfold stdout_exit_flush, stdout_writefn, stdout_stdio_write, rd_so, upd_so.
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
    apply mna_bind; [apply mna_stdio_write | intros u'; cbv beta; apply mna_upd].
Qed.

(** The whole program, when argv has not two entries. *)
Lemma prog_with_na : forall rs argv,
  Z.of_nat (length argv) <> 2%Z -> mna (prog_with rs argv).
Proof.
  intros rs argv Hlen. unfold prog_with.
  apply mna_bind; [unfold startup; apply mna_bind; [apply mna_sys; reflexivity | intros u; cbv beta; apply mna_ret] | intros u; cbv beta].
  apply mna_bind; [| intros code; cbv beta].
  - unfold main_model.
    match goal with |- mna (if ?b then _ else _) => destruct b eqn:E end.
    + apply mna_bind; [exact (mna_io_diag _ ps_so set_so_ps (DUsage (nth 0 argv []))) | intros u'; cbv beta; apply mna_ret].
    + exfalso. apply Bool.negb_false_iff, Z.eqb_eq in E. exact (Hlen E).
  - unfold exit_model.
    apply mna_bind; [exact (mna_io_exit _ ps_so set_so_ps) | intros u'; cbv beta].
    apply mna_sys. reflexivity.
Qed.

Lemma usage_tree_na : forall segs rs inp en,
  (length (in_argv inp) <> 2)%nat -> tna (Prog.prog segs rs inp en).
Proof.
  intros segs rs inp en Hlen. unfold Prog.prog, prog_itree.
  assert (Hz : Z.of_nat (length (argv_Z (in_argv inp))) <> 2%Z)
    by (unfold argv_Z; rewrite length_map; lia).
  apply tna_ebind.
  - exact (prog_with_na rs (argv_Z (in_argv inp)) Hz _).
  - intros [[] ?].
Qed.
