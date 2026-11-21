(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from Spec/Monad.v, Spec/Stdio.v, Spec/Driver.v, Spec/HarnessP.v and Spec/ProgP.v: the program tree of a run whose argv has not two entries has only writev, ioctl, set_tid_address and exit nodes. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes Decode.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim Monad Stdio Driver PState HarnessP ProgP.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.BudgetWit Require Import NoAlloc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.

(** * The usage path's tree makes no allocation call

    [Spec.ProgP.prog] is the program the released plain proof runs: [startup]
    (set_tid_address), then [Driver.main_model], then [HarnessP.client_exit],
    then [Driver.exit_model].  With argc <> 2, [main_model] is
    [io_diag io (DUsage argv0) ;;; mret 2]: [Stdio.stderr_fprintf], which is a
    loop of writev on fd 2.  [client_exit] is [mret tt] in this harness;
    [exit_model] flushes stdout ([Stdio.stdout_exit_flush]: at most an ioctl
    and a writev loop on fd 1) and exits.

    [mnaI Inv m] says: from every state that satisfies [Inv], every node of
    the tree of [m] is in [NoAlloc.nna], and every state it returns satisfies
    [Inv] again.  It is the form simdjson/fuzz_minifyimpl needs, whose
    [client_exit] deletes the buffer [ps_fa] holds; this harness carries the
    same invariant [Inv s := ps_fa s = None] so the two files stay one shape.
    [usage_tree_na] is the result for [ProgP.prog], the tree that
    [Plain.PlainClosed.plain_impl_closed_modulo_client] speaks of. *)

(** Every node is in [nna], and every returned value satisfies [P]. *)
Fixpoint tnaQ {R : Type} (P : R -> Prop) (t : itree node (exc R)) : Prop :=
  match t with
  | Ret Unr => True
  | Ret (Ok r) => P r
  | Vis n k => nna n = true /\ forall rsp, tnaQ P (k rsp)
  end.

Lemma tnaQ_tna : forall R (P : R -> Prop) (t : itree node (exc R)), tnaQ P t -> tna t.
Proof.
  intros R P t. induction t as [[|r]|n k IH]; intros Ht; cbn [tnaQ tna] in *.
  - exact I.
  - exact I.
  - destruct Ht as [Hn Hk]. split; [exact Hn|]. intros rsp. exact (IH rsp (Hk rsp)).
Qed.

Lemma tnaQ_ebind : forall A B (P : A -> Prop) (Q : B -> Prop)
    (t : itree node (exc A)) (f : A -> itree node (exc B)),
  tnaQ P t -> (forall a, P a -> tnaQ Q (f a)) -> tnaQ Q (ebind t f).
Proof.
  intros A B P Q t f. unfold ebind.
  induction t as [[|a]|n k IH]; intros Ht Hf; cbn [bind tnaQ] in *.
  - exact I.
  - exact (Hf a Ht).
  - destruct Ht as [Hn Hk]. split; [exact Hn|]. intros rsp. exact (IH rsp (Hk rsp) Hf).
Qed.

Section Inv.
Context {St : Type} (Inv : St -> Prop).

Definition mnaI {A : Type} (m : St -> itree node (exc (A * St))) : Prop :=
  forall s, Inv s -> tnaQ (fun p => Inv (snd p)) (m s).

Lemma mnaI_ret : forall A (a : A), mnaI (@mret St A a).
Proof. intros A a s Hs. exact Hs. Qed.

Lemma mnaI_unr : forall A, mnaI (@munr St A).
Proof. intros A s _. exact I. Qed.

Lemma mnaI_get : mnaI (@mget St).
Proof. intros s Hs. exact Hs. Qed.

Lemma mnaI_upd : forall (f : St -> St), (forall s, Inv s -> Inv (f s)) -> mnaI (@mupd St f).
Proof. intros f Hf s Hs. exact (Hf s Hs). Qed.

Lemma mnaI_bind : forall A B (m : St -> itree node (exc (A * St)))
    (f : A -> St -> itree node (exc (B * St))),
  mnaI m -> (forall a, mnaI (f a)) -> mnaI (mbind m f).
Proof.
  intros A B m f Hm Hf s Hs. unfold mbind.
  apply (tnaQ_ebind _ _ (fun p => Inv (snd p))); [exact (Hm s Hs)|].
  intros [a s'] Hs'. exact (Hf a s' Hs').
Qed.

(** A read of the state, from a state that satisfies [Inv]. *)
Lemma mnaI_getk : forall C (k : St -> St -> itree node (exc (C * St))),
  (forall s0, Inv s0 -> mnaI (k s0)) -> mnaI (mbind mget k).
Proof. intros C k Hk s Hs. exact (Hk s Hs s Hs). Qed.

Lemma mnaI_sys : forall A n (dec : resp -> option A), nna n = true -> mnaI (@msys St A n dec).
Proof.
  intros A n dec Hn s Hs. unfold msys, enode. cbn [tnaQ]. split; [exact Hn|].
  intros rsp. destruct (dec rsp); [exact Hs | exact I].
Qed.

Lemma mnaI_stdio_write_loop : forall fuel fd iov, mnaI (@stdio_write_loop St fuel fd iov).
Proof.
  intros fuel. induction fuel as [|fuel IH]; intros fd iov; cbn [stdio_write_loop].
  - apply mnaI_unr.
  - apply mnaI_bind; [apply mnaI_sys; reflexivity|]. intros cnt. cbv beta.
    match goal with |- mnaI (if ?b then _ else _) => destruct b end; [apply mnaI_ret | apply IH].
Qed.

Lemma mnaI_stdio_write : forall fd buf s, mnaI (@stdio_write St fd buf s).
Proof.
  intros fd buf s. unfold stdio_write.
  match goal with |- mnaI (if ?b then _ else _) => destruct b end;
    [apply mnaI_unr | apply mnaI_stdio_write_loop].
Qed.

Lemma mnaI_stderr_pieces : forall ps buf, mnaI (@stderr_pieces St buf ps).
Proof.
  intros ps. induction ps as [|p ps IH]; intros buf; cbn [stderr_pieces].
  - apply mnaI_ret.
  - match goal with |- mnaI (if ?b then _ else _) => destruct b end.
    + apply mnaI_bind; [apply mnaI_stdio_write | intros u; cbv beta; apply IH].
    + apply IH.
Qed.

Lemma mnaI_io_diag : forall (g : St -> stdout_st) (st : stdout_st -> St -> St) d,
  mnaI (io_diag (io_S g st) d).
Proof.
  intros g st d. unfold io_S. cbn [io_diag]. unfold s_diag.
  destruct d; cbv iota.
  all: first
    [ unfold stderr_fprintf;
      apply mnaI_bind; [apply mnaI_stderr_pieces | intros buf; cbv beta; apply mnaI_stdio_write]
    | unfold stderr_fwrite;
      match goal with |- mnaI (if ?b then _ else _) => destruct b end;
      [apply mnaI_stdio_write | apply mnaI_ret] ].
Qed.

(** An update of the stdout state through [st], given that [st] keeps [Inv]. *)
Local Ltac upd_tac Hst :=
  apply mnaI_upd;
  let s := fresh "s" in let Hs := fresh "Hs" in
  intros s Hs; cbv beta; apply Hst; exact Hs.

(** The stdout flush writes the stdout state only, through [st]. *)
Lemma mnaI_io_exit : forall (g : St -> stdout_st) (st : stdout_st -> St -> St),
  (forall v s, Inv s -> Inv (st v s)) ->
  mnaI (io_exit (io_S g st)).
Proof.
  intros g st Hst. unfold io_S. cbn [io_exit].
  unfold stdout_exit_flush, stdout_writefn, stdout_stdio_write, rd_so, upd_so.
  apply mnaI_bind; [apply mnaI_bind; [apply mnaI_get | intros x; cbv beta; apply mnaI_ret] | intros so; cbv beta].
  match goal with |- mnaI (if ?b then _ else _) => destruct b end; [| apply mnaI_ret].
  apply mnaI_bind; [apply mnaI_bind; [apply mnaI_get | intros x; cbv beta; apply mnaI_ret] | intros so1; cbv beta].
  apply mnaI_bind.
  - match goal with |- mnaI (if ?b then _ else _) => destruct b end; [| apply mnaI_ret].
    apply mnaI_bind; [upd_tac Hst | intros u; cbv beta].
    apply mnaI_bind; [apply mnaI_sys; reflexivity | intros r; cbv beta].
    destruct r; cbv iota; first [upd_tac Hst | apply mnaI_unr].
  - intros u. cbv beta.
    apply mnaI_bind; [apply mnaI_bind; [apply mnaI_get | intros x; cbv beta; apply mnaI_ret] | intros so2; cbv beta].
    apply mnaI_bind; [apply mnaI_stdio_write | intros u'; cbv beta; upd_tac Hst].
Qed.
End Inv.

(** The client buffer is [ps_fa]; on the usage path it is [None]. *)
Definition fa_none (s : PState) : Prop := ps_fa s = None.

Lemma fa_none_so : forall v s, fa_none s -> fa_none (set_so_ps v s).
Proof. intros v s Hs. exact Hs. Qed.

(** [client_exit] makes no call and keeps the state. *)
Lemma mnaI_client_exit : mnaI fa_none client_exit.
Proof. unfold client_exit, HarnessP.client_exit. apply mnaI_ret. Qed.

(** The whole program, when argv has not two entries. *)
Lemma prog_with_na : forall rs argv,
  Z.of_nat (length argv) <> 2%Z -> mnaI fa_none (prog_with rs argv).
Proof.
  intros rs argv Hlen. unfold prog_with, main_exit.
  apply mnaI_bind; [unfold startup; apply mnaI_bind; [apply mnaI_sys; reflexivity | intros u; cbv beta; apply mnaI_ret] | intros u; cbv beta].
  apply mnaI_bind; [| intros code; cbv beta].
  - unfold main_model.
    match goal with |- mnaI _ (if ?b then _ else _) => destruct b eqn:E end.
    + apply mnaI_bind; [exact (mnaI_io_diag fa_none ps_so set_so_ps (DUsage (nth 0 argv []))) | intros u'; cbv beta; apply mnaI_ret].
    + exfalso. apply Bool.negb_false_iff, Z.eqb_eq in E. exact (Hlen E).
  - apply mnaI_bind; [exact mnaI_client_exit | intros u'; cbv beta].
    unfold exit_model.
    apply mnaI_bind; [exact (mnaI_io_exit fa_none ps_so set_so_ps fa_none_so) | intros u''; cbv beta].
    apply mnaI_sys. reflexivity.
Qed.

Lemma usage_tree_na : forall segs rs inp en,
  (length (in_argv inp) <> 2)%nat -> tna (ProgP.prog segs rs inp en).
Proof.
  intros segs rs inp en Hlen. unfold ProgP.prog, prog_itree.
  assert (Hz : Z.of_nat (length (argv_Z (in_argv inp))) <> 2%Z)
    by (unfold argv_Z; rewrite length_map; lia).
  apply tna_ebind.
  - refine (tnaQ_tna _ _ _ (prog_with_na rs (argv_Z (in_argv inp)) Hz _ _)). exact eq_refl.
  - intros [[] ?].
Qed.
