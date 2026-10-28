(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes Decode.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import Prelim Monad.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import SoftFloat FmtFp.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import Stdio.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import Printf_model Printf_mlib Printf_pieces.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF ITreeA.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg AProto MonadF F_printf_iface.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Section CANSEC1. Context {rc : runConstT}.
Section StderrBridge.
  Context {St : Type}.

  (* [comment removed for export] *)
  Definition FLUSH_stderr : M (list Z * St) unit :=
    fun bs => let '(buf, st) := bs in
      ebind (stdio_write 2 buf [] st) (fun r => ITree.Ret (Ok (tt, (@nil Z, snd r)))).

  (* [comment removed for export] *)
  Lemma stdio_write_loop_leaves : forall fuel fd iov (st : St),
    tforall (fun r => match r with Ok q => snd q = st | Unr => True end) (stdio_write_loop fuel fd iov st).
  Proof.
    induction fuel as [|fuel IH]; intros fd iov st; cbn [stdio_write_loop].
    - cbn. exact I.
    - unfold mbind, msys, enode, ebind. cbn [ITree.bind].
      intros x. destruct (dec_writev (iov_total iov) x) as [k|]; cbn [ITree.bind fst snd].
      + destruct (k =? iov_total iov); [cbn; reflexivity | apply IH].
      + exact I.
  Qed.
  Lemma stdio_writev_leaves : forall fd buf s (st : St),
    tforall (fun r => match r with Ok q => snd q = st | Unr => True end) (stdio_write fd buf s st).
  Proof.
    intros fd buf s st. unfold stdio_write.
    destruct (WRITE_MAX <? zlength buf + zlength s); [cbn; exact I | apply stdio_write_loop_leaves].
  Qed.

  Lemma OUT_stderr_leaves : forall p buf (st : St),
    tforall (fun r => match r with Ok q => snd (snd q) = st | Unr => True end) (OUT_stderr p (buf, st)).
  Proof.
    intros p buf st. unfold OUT_stderr.
    destruct (INTERNAL_BUFSIZ - zlength buf <? zlength p); [|cbn; reflexivity].
    unfold ebind. eapply tforall_bind; [apply stdio_writev_leaves|]. intros [|[a s']] H; cbn; [exact I | exact H].
  Qed.

  Lemma outsk_flush_leaves : forall ps buf (st : St),
    tforall (fun r => match r with Ok q => snd (snd q) = st | Unr => True end) (outsk OUT_stderr ps FLUSH_stderr (buf, st)).
  Proof.
    induction ps as [|p ps IH]; intros buf st; cbn [outsk].
    - unfold FLUSH_stderr, ebind. eapply tforall_bind; [apply stdio_writev_leaves|]. intros [|[a s']] H; cbn; [exact I | exact H].
    - unfold mbind at 1. unfold ebind. eapply tforall_bind; [apply OUT_stderr_leaves|].
      intros [|[[] [buf' st']]] H; cbn in H |- *; [exact I|]. subst st'. apply IH.
  Qed.

  (* [comment removed for export] *)
  Lemma stderr_bridgeF : forall RNG ps buf (st : St) (Q : St -> footprint -> machine_state -> Prop) ms,
    implS bsegs RNG (outsk OUT_stderr ps FLUSH_stderr (buf, st)) (epostF (fun p RNG' ms' => Q (snd (snd p)) RNG' ms')) ms ->
    implS bsegs RNG (mbind (stderr_pieces buf ps) (fun b => stdio_write 2 b []) st) (epostF (fun p RNG' ms' => Q (snd p) RNG' ms')) ms.
  Proof.
    intros RNG ps; revert RNG. induction ps as [|p ps IH]; intros RNG buf st Q ms H; cbn [outsk stderr_pieces] in H |- *.
    - (* [comment removed for export] *)
      rewrite mbind_mret. unfold FLUSH_stderr, ebind in H.
      eapply (implF_bind_elim bsegs _ _ RNG _ _ _ _ _ _ (stdio_writev_leaves 2 buf [] st)); [|exact H].
      intros [|[[] st']] RNG' ms' Hr Hi; cbn in Hi |- *; [apply evtF_done; exact I|].
      cbn in Hi. exact Hi.
    - destruct (INTERNAL_BUFSIZ - zlength buf <? zlength p) eqn:T.
      + (* [comment removed for export] *)
        unfold mbind at 1 in H. unfold OUT_stderr in H. rewrite T in H. unfold ebind in H.
        apply implF_bind_assoc_rev in H.
        unfold mbind at 1. change ((stdio_write 2 buf p ;;; stderr_pieces [] ps) st) with (ebind (stdio_write 2 buf p st) (fun q => stderr_pieces [] ps (snd q))).
        unfold ebind. apply implF_bind_assoc.
        eapply (implF_bind_ext2 bsegs _ _ RNG _ _ _ _ _ _ _ (stdio_writev_leaves 2 buf p st)); [|exact H].
        intros [|[[] st']] RNG' ms' Hr Hi; cbn [ITree.bind] in Hi |- *.
        * exact Hi.
        * cbn in Hr. subst st'. apply IH. exact Hi.
      + (* [comment removed for export] *)
        unfold mbind at 1 in H. unfold OUT_stderr in H. rewrite T in H. cbn [ebind ITree.bind fst snd] in H.
        apply IH. exact H.
  Qed.

  (* [comment removed for export] *)
  Lemma stderr_bridgeA : forall RNG ps buf (st : St) (Q : St -> machine_state -> Prop) ms,
    implAM RNG (outsk OUT_stderr ps FLUSH_stderr) (buf, st) (fun _ bs ms' => Q (snd bs) ms') ms ->
    implAM RNG (mbind (stderr_pieces buf ps) (fun b => stdio_write 2 b [])) st (fun _ st' ms' => Q st' ms') ms.
  Proof.
    intros RNG ps buf st Q ms H. unfold implAM, postF in *.
    pose proof (@stderr_bridgeF RNG ps buf st (fun s R m => R = RNG /\ Q s m) ms) as BR.
    eapply implF_mono.
    - apply BR. eapply implF_mono; [exact H|]. intros [|[[] [b s']]] RNG' ms' Hp; cbn in *; exact Hp.
    - intros [|[b s']] RNG' ms' Hp; cbn in *; exact Hp.
  Qed.
End StderrBridge.
End CANSEC1.
