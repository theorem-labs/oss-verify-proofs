(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from Spec/Prog.v, Spec/Driver.v and Spec/Stdio.v: on the argc <> 2 branch of main_model the program tree has no allocation node. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import ITree Nodes Ceiling.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Spec Require Import Monad Stdio Driver Prog.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.BudgetWit Require Import Quiet.
Import ListNotations.
Open Scope Z_scope.

(** * The usage path has no allocation node

    [tall t]: every node of [t] is a [Quiet.nalloc] node, whatever the responses
    and choices.  It is a property of the tree alone, so [tall_tsafe] makes it a
    [tsafe] side condition at every model.

    [Prog.prog] is [startup], then [Driver.main_model], then [Driver.exit_model].
    With an argument count other than 2, [main_model] is [io_diag (DUsage _)]
    followed by [mret 2]: [stderr_fprintf] of the usage pieces, which is writev
    (66) on fd 2; [exit_model] flushes stdout (writev on fd 1, after an ioctl
    (29) on the first write) and exits (93 or 94); [startup] is set_tid_address
    (96).  [usage_tall] checks that tree node by node.  No allocation call is on
    the path, so the check needs no fact about the allocator or the budget. *)

Fixpoint tall {R} (t : itree node R) : Prop :=
  match t with
  | Ret _ => True
  | Vis n k => nalloc n /\ forall rsp, tall (k rsp)
  | Cho k => forall z, tall (k z)
  end.

Lemma tall_tsafe : forall {R} (t : itree node R) mo,
  tall t -> tsafe nstep (fun n (_ : Model) => nalloc n) t mo.
Proof.
  intros R t. induction t as [r|n k IH|kc IHc]; intros mo Ht; cbn [tsafe tall] in *.
  - exact I.
  - destruct Ht as [Hn Hk]. split; [exact Hn|]. intros rsp mo' evs _. apply IH. apply Hk.
  - intros z. apply IHc. apply Ht.
Qed.

Lemma tall_ebind : forall {A B} (t : itree node (Exc.exc A)) (f : A -> itree node (Exc.exc B)),
  tall t -> (forall a, tall (f a)) -> tall (ebind t f).
Proof.
  intros A B t f. unfold ebind. induction t as [r|n k IH|kc IHc]; intros Ht Hf; cbn [bind tall] in *.
  - destruct r as [|a]; [exact I | exact (Hf a)].
  - destruct Ht as [Hn Hk]. split; [exact Hn|]. intros rsp. apply IH; [apply Hk | exact Hf].
  - intros z. apply IHc; [apply Ht | exact Hf].
Qed.

(** The same on the state monad of [Spec.Monad]. *)
Definition mall {St A} (m : @M St A) : Prop := forall s, tall (m s).

Lemma mall_intro : forall {St A} (m : @M St A) s, mall m -> tall (m s).
Proof. intros St A m s H. exact (H s). Qed.

Lemma mall_ret : forall {St A} (a : A), mall (St:=St) (mret a).
Proof. intros St A a s. exact I. Qed.

Lemma mall_munr : forall {St A}, mall (St:=St) (A:=A) munr.
Proof. intros St A s. exact I. Qed.

Lemma mall_mget : forall {St}, mall (St:=St) mget.
Proof. intros St s. exact I. Qed.

Lemma mall_mupd : forall {St} (f : St -> St), mall (mupd f).
Proof. intros St f s. exact I. Qed.

Lemma mall_bind : forall {St A B} (m : @M St A) (f : A -> @M St B),
  mall m -> (forall a, mall (f a)) -> mall (mbind m f).
Proof.
  intros St A B m f Hm Hf s.
  change (tall (ebind (m s) (fun p => f (fst p) (snd p)))).
  apply tall_ebind; [apply Hm|]. intros p. exact (Hf (fst p) (snd p)).
Qed.

Lemma mall_msys : forall {St A} n (dec : resp -> option A), nalloc n -> mall (St:=St) (msys n dec).
Proof.
  intros St A n dec Hn s. unfold msys, enode. cbn [tall].
  split; [exact Hn|]. intros rsp. destruct (dec rsp); exact I.
Qed.

Lemma mall_mloop : forall {St X R} fuel (body : X -> @M St (X + R)) x,
  (forall x, mall (body x)) -> mall (mloop fuel body x).
Proof.
  intros St X R fuel. induction fuel as [|fuel IH]; intros body x Hb.
  - apply mall_munr.
  - cbn [mloop]. apply mall_bind; [apply Hb|].
    intros [x'|r]; cbv beta iota; [apply IH; exact Hb | apply mall_ret].
Qed.

(** Walk a monadic term: binds, returns, system calls, loops and case splits;
    otherwise unfold one of the driver's and stdio's definitions. *)
Ltac mall_tac :=
  repeat (cbv beta iota;
    first
    [ match goal with
      | |- mall (mbind _ _) => apply mall_bind; [|intros ?]
      | |- mall (mret _) => apply mall_ret
      | |- mall munr => apply mall_munr
      | |- mall mget => apply mall_mget
      | |- mall (mupd _) => apply mall_mupd
      | |- mall (msys _ _) => apply mall_msys; exact I
      | |- mall (mloop _ _ _) => apply mall_mloop; intros ?
      | |- mall (if ?b then _ else _) => destruct b
      | |- context [match ?x with _ => _ end] => destruct x
      end
    | progress cbn [io_diag io_exit]
    | progress unfold OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Spec.Prog.io, io_S, s_diag,
        stderr_fprintf, stderr_pieces, pieces_usage, stdio_writev, wv_body, exit_model,
        stdout_exit_flush, stdout_writefn, stdout_stdio_write, rd_so, upd_so, startup ]).

Lemma argv_Z_length : forall argv, length (argv_Z argv) = length argv.
Proof.
  intros argv. unfold argv_Z. induction argv as [|a argv IH]; cbn; [reflexivity | rewrite IH; reflexivity].
Qed.

(** On an argument count other than 2, no node of the program tree is an
    allocation call. *)
Theorem usage_tall : forall (CE : Ceiling) segs rstage argv,
  (length argv <> 2)%nat -> tall (@prog CE segs rstage argv).
Proof.
  intros CE segs rstage argv Hlen.
  assert (Hc : (Z.of_nat (length (argv_Z argv)) =? 2) = false).
  { apply Z.eqb_neq. rewrite argv_Z_length. lia. }
  unfold prog. apply tall_ebind; [| intros [[] _]].
  apply mall_intro. unfold prog_with.
  apply mall_bind; [mall_tac | intros u].
  cbv beta. apply mall_bind; [| intros code; cbv beta; mall_tac].
  unfold main_model. rewrite Hc. cbn [negb]. mall_tac.
Qed.
