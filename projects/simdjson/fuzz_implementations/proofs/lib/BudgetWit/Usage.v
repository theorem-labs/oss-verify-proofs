(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from Spec/Prog.v, Spec/Driver.v, Spec/Stdio.v and Spec/ModelInvN.v: on the argc <> 2 branch of main_model the program tree has no allocation node. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import ITree Nodes Ceiling.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Monad Stdio Driver Prog.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec Require ModelInvN.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.BudgetWit Require Import Quiet.
Import ListNotations.
Open Scope Z_scope.

(** * The usage path has no allocation node

    [tall t]: every node of [t] is a [Quiet.nalloc] node, whatever the responses
    and choices.  It is a property of the tree alone, so [tall_tsafe] makes it a
    [tsafe] side condition at every model.

    [Prog.prog] is [startup], then [Driver.main_model], then [Prog.exit_imp].
    With an argument count other than 2, [main_model] is [io_diag (DUsage _)]
    followed by [mret 2]: [stderr_fprintf] of the usage pieces, which is writev
    (66) on fd 2.  [exit_imp] is [xfree], then [Driver.exit_model]: [xfree]
    frees the pointer [ps_x] holds, if any, and is [mret tt] when [ps_x] is
    [None]; [exit_model] flushes stdout (writev on fd 1, after an ioctl (29) on
    the first write) and exits (93 or 94); [startup] is set_tid_address (96).

    [xfree]'s free is the one step whose tree depends on the state: a free may
    unmap or protect a page, so the state-free check [mall] does not cover
    [xfree].  [ps_x] is [None] in
    [Prog.ps_init], and [startup] and the usage branch of [main_model] keep it
    ([ModelInvN.keeps_x_startup], [ModelInvN.keeps_x_s_diag]), so on the usage
    path [xfree] is [mret tt] ([xfree_none]).  [usage_tall] checks the tree node
    by node with that fact.  No allocation call is on the path, so the check
    needs no fact about the allocator or the budget. *)

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
    | progress unfold OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec.Prog.io, io_S, s_diag,
        stderr_fprintf, stderr_pieces, pieces_usage, stdio_writev, wv_body, exit_model,
        stdout_exit_flush, stdout_writefn, stdout_stdio_write, rd_so, upd_so, startup ]).

Lemma argv_Z_length : forall argv, length (argv_Z argv) = length argv.
Proof.
  intros argv. unfold argv_Z. induction argv as [|a argv IH]; cbn; [reflexivity | rewrite IH; reflexivity].
Qed.

Section Xfree.
Context {CE__ : Ceiling}.

(** [ebind] of a tree whose leaves all satisfy [P] and a continuation that
    has no allocation node from every such leaf. *)
Lemma tall_ebind_on : forall {A B} (P : A -> Prop) (t : itree node (Exc.exc A))
    (f : A -> itree node (Exc.exc B)),
  tall t -> ModelInvN.tall P t -> (forall a, P a -> tall (f a)) -> tall (ebind t f).
Proof.
  intros A B P t f. unfold ebind.
  induction t as [[|a]|n k IH|kc IHc]; intros Ht HP Hf; cbn [bind tall ModelInvN.tall] in *.
  - exact I.
  - exact (Hf a HP).
  - destruct Ht as [Hn Hk]. split; [exact Hn|]. intros rsp. exact (IH rsp (Hk rsp) (HP rsp) Hf).
  - intros z. exact (IHc z (Ht z) (HP z) Hf).
Qed.

(** A bind whose first part has no allocation node and keeps [ps_x], from a
    state where [ps_x] is [None]. *)
Lemma tall_mbind_x : forall {A B} (m : @M PState A) (f : A -> @M PState B) s,
  tall (m s) -> ModelInvN.keeps ps_x m -> ps_x s = None ->
  (forall a s', ps_x s' = None -> tall (f a s')) -> tall (mbind m f s).
Proof.
  intros A B m f s Hm Hk Hs Hf. unfold mbind.
  apply (tall_ebind_on (fun p => ps_x (snd p) = None)); [exact Hm| |].
  - eapply ModelInvN.tall_mono; [exact (Hk s)|]. intros p E. rewrite E. exact Hs.
  - intros [a s'] E. exact (Hf a s' E).
Qed.

(** With [ps_x] [None], [xfree] frees nothing. *)
Lemma xfree_none : forall s, ps_x s = None -> xfree s = mret tt s.
Proof. intros s H. unfold xfree, mbind, mget, mret. cbn [ebind bind fst snd]. rewrite H. reflexivity. Qed.

(** ...so [exit_imp] is [exit_model], which has no allocation node. *)
Lemma exit_imp_none : forall code s, ps_x s = None -> tall (exit_imp code s).
Proof.
  intros code s H. unfold exit_imp, mbind. cbv beta. rewrite (xfree_none s H).
  assert (Hx : mall (exit_model OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec.Prog.io code))
    by mall_tac.
  exact (mall_intro _ s Hx).
Qed.
End Xfree.

(** On an argument count other than 2, no node of the program tree is an
    allocation call. *)
Theorem usage_tall : forall (CE : Ceiling) segs rstage argv,
  (length argv <> 2)%nat -> tall (@prog CE segs rstage argv).
Proof.
  intros CE segs rstage argv Hlen.
  assert (Hc : (Z.of_nat (length (argv_Z argv)) =? 2) = false).
  { apply Z.eqb_neq. rewrite argv_Z_length. lia. }
  unfold prog. apply tall_ebind; [| intros [[] _]].
  unfold prog_with.
  apply tall_mbind_x.
  - apply mall_intro. mall_tac.
  - exact ModelInvN.keeps_x_startup.
  - reflexivity.
  - intros u s1 H1. cbv beta.
    apply tall_mbind_x.
    + apply mall_intro. unfold main_model. rewrite Hc. cbn [negb]. mall_tac.
    + unfold main_model. rewrite Hc. cbn [negb].
      apply ModelInvN.keeps_bind; [exact (ModelInvN.keeps_x_s_diag _) | intros _; apply ModelInvN.keeps_ret].
    + exact H1.
    + intros code s2 H2. exact (exit_imp_none code s2 H2).
Qed.
