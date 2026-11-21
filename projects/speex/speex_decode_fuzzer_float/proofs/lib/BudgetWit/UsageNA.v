(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from Spec/X1qy.v, Spec/X1ri.v, Spec/X1o8.v and Spec/X1r6.v: the program tree of a run whose argv has not two entries has only writev, ioctl, set_tid_address and exit nodes. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1c5 X1by X1bz X1bo X1bs X1c2 X1bn.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qx X1ri X1o8 X1r3 X1r6.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.BudgetWit Require Import NoAlloc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(** * The usage path's tree makes no allocation call

    [X1r6.prog] is the program the released plain proof runs ([TopSides.impl_root],
    [PSide.HP_plain]): [X1r6.startup] (set_tid_address), then
    [X1o8.main_model], then [X1r6.io_exit].  With argc <> 2, [main_model] is
    [io_diag (DUsage argv0) ;;; mret 2], and [io_diag] is [X1ri.s_diag]:
    [X1ri.stderr_fprintf], a loop of writev on fd 2.  [io_exit] is
    [X1ri.stdio_exit_model]: it flushes stdout ([X1ri.stdout_exit_flush]: at
    most an ioctl and a writev loop on fd 1) and exits.  [mna m] says that,
    from every state, every node of the tree of [m] is in [NoAlloc.nna];
    [usage_tree_na] is the result for [X1r6.prog]. *)

Definition mna {St A : Type} (m : X1qy.M St A) : Prop := forall s, tna (m s).

Lemma mna_ret : forall St A (a : A), mna (@X1qy.mret St A a).
Proof. intros St A a s. exact I. Qed.

Lemma mna_unr : forall St A, mna (@X1qy.munr St A).
Proof. intros St A s. exact I. Qed.

Lemma mna_get : forall St, mna (@X1qy.mget St).
Proof. intros St s. exact I. Qed.

Lemma mna_upd : forall St (f : St -> St), mna (@X1qy.mupd St f).
Proof. intros St f s. exact I. Qed.

Lemma mna_bind : forall St A B (m : X1qy.M St A) (f : A -> X1qy.M St B),
  mna m -> (forall a, mna (f a)) -> mna (X1qy.mbind m f).
Proof.
  intros St A B m f Hm Hf s. unfold X1qy.mbind.
  apply tna_ebind; [exact (Hm s) | intros [a s']; exact (Hf a s')].
Qed.

Lemma mna_sys : forall St A n (dec : resp -> option A), nna n = true -> mna (@X1qy.msys St A n dec).
Proof.
  intros St A n dec Hn s. unfold X1qy.msys, X1bt.enode. split; [exact Hn|].
  intros rsp. cbv beta. destruct (dec rsp); exact I.
Qed.

Lemma mna_stdio_wloop : forall St fuel fd iovs, mna (@stdio_wloop St fuel fd iovs).
Proof.
  intros St fuel. induction fuel as [|fuel IH]; intros fd iovs; cbn [stdio_wloop].
  - apply mna_unr.
  - apply mna_bind; [apply mna_sys; reflexivity|]. intros cnt. cbv beta.
    match goal with |- mna (if ?b then _ else _) => destruct b end; [apply mna_ret | apply IH].
Qed.

Lemma mna_stdio_writev : forall St fd buf s, mna (@stdio_writev St fd buf s).
Proof.
  intros St fd buf s. unfold stdio_writev.
  match goal with |- mna (if ?b then _ else _) => destruct b end; [apply mna_unr | apply mna_stdio_wloop].
Qed.

Lemma mna_stderr_pieces : forall St ps buf, mna (@stderr_pieces St buf ps).
Proof.
  intros St ps. induction ps as [|p ps IH]; intros buf; cbn [stderr_pieces].
  - apply mna_ret.
  - match goal with |- mna (if ?b then _ else _) => destruct b end.
    + apply mna_bind; [apply mna_stdio_writev | intros u; cbv beta; apply IH].
    + apply IH.
Qed.

Lemma mna_s_diag : forall St d, mna (@s_diag St d).
Proof.
  intros St d. destruct d; unfold s_diag; cbv beta iota.
  all: first
    [ unfold stderr_fprintf;
      apply mna_bind; [apply mna_stderr_pieces | intros buf; cbv beta; apply mna_stdio_writev]
    | unfold stderr_fwrite;
      match goal with |- mna (if ?b then _ else _) => destruct b end;
      [apply mna_stdio_writev | apply mna_ret] ].
Qed.

Section StdoutExit.
Variables (St : Type) (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).

Lemma mna_rd_so : mna (rd_so get_so).
Proof. unfold rd_so. apply mna_bind; [apply mna_get | intros s; cbv beta; apply mna_ret]. Qed.

Lemma mna_upd_so : forall f, mna (upd_so get_so set_so f).
Proof. intros f. unfold upd_so. apply mna_upd. Qed.

Lemma mna_stdout_stdio_write : forall s, mna (stdout_stdio_write get_so set_so s).
Proof.
  intros s. unfold stdout_stdio_write.
  apply mna_bind; [apply mna_rd_so | intros so; cbv beta].
  apply mna_bind; [apply mna_stdio_writev | intros u; cbv beta; apply mna_upd_so].
Qed.

Lemma mna_stdout_writefn : forall s, mna (stdout_writefn get_so set_so s).
Proof.
  intros s. unfold stdout_writefn.
  apply mna_bind; [apply mna_rd_so | intros so; cbv beta].
  apply mna_bind; [| intros u; cbv beta; apply mna_stdout_stdio_write].
  match goal with |- mna (if ?b then _ else _) => destruct b end; [| apply mna_ret].
  apply mna_bind; [apply mna_upd_so | intros u; cbv beta].
  apply mna_bind; [apply mna_sys; reflexivity | intros r; cbv beta].
  destruct r; first [apply mna_upd_so | apply mna_unr].
Qed.

Lemma mna_stdout_exit_flush : mna (stdout_exit_flush get_so set_so).
Proof.
  unfold stdout_exit_flush.
  apply mna_bind; [apply mna_rd_so | intros so; cbv beta].
  match goal with |- mna (if ?b then _ else _) => destruct b end;
    [apply mna_stdout_writefn | apply mna_ret].
Qed.

Lemma mna_stdio_exit_model : forall code, mna (stdio_exit_model get_so set_so code).
Proof.
  intros code. unfold stdio_exit_model.
  apply mna_bind; [apply mna_stdout_exit_flush | intros u; cbv beta; apply mna_sys; reflexivity].
Qed.

End StdoutExit.

(** The whole program, when argv has not two entries. *)
Lemma prog_with_na : forall rstage argv,
  Z.of_nat (length argv) <> 2 -> mna (prog_with rstage argv).
Proof.
  intros rstage argv Hlen. unfold prog_with.
  apply mna_bind.
  { unfold startup. apply mna_bind; [apply mna_sys; reflexivity | intros u; cbv beta; apply mna_ret]. }
  intros u. cbv beta.
  apply mna_bind; [| intros code; cbv beta].
  - unfold main_model.
    match goal with |- mna (if ?b then _ else _) => destruct b eqn:E end.
    + apply mna_bind; [unfold io_diag; apply mna_s_diag | intros u'; cbv beta; apply mna_ret].
    + exfalso. apply Bool.negb_false_iff, Z.eqb_eq in E. exact (Hlen E).
  - unfold io_exit. apply mna_stdio_exit_model.
Qed.

Lemma usage_tree_na : forall segs rstage ceil argv,
  (length argv <> 2)%nat -> tna (X1r6.prog segs rstage ceil argv).
Proof.
  intros segs rstage ceil argv Hlen. unfold X1r6.prog.
  assert (Hz : Z.of_nat (length (argv_Z argv)) <> 2)
    by (unfold argv_Z; rewrite length_map; lia).
  apply tna_ebind.
  - exact (prog_with_na rstage (argv_Z argv) Hz _).
  - intros [[] ?].
Qed.
