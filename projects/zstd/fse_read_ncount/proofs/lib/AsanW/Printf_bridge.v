(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes Decode.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import Prelim Monad.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import SoftFloat FmtFp.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import Stdio.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import Printf_model Printf_mlib Printf_pieces.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import ExecF ITreeA.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AImg AProto MonadF F_printf_iface.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
Import ListNotations.
Import ITree.Exc.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_orc_old ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_k12.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.slia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.slia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.flia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.flia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange_nonneg ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_nonneg_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.solve_load ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.solve_load_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.word_eq_tac_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes_k12.
(* [comment removed for export] *)

Open Scope Z_scope.
Open Scope mspec_scope.
Section CANSEC1. Context {rc : runConstT}.
Section StderrBridge.
Context {St : Type}.
Definition FLUSH_stderr : M (list Z * St) unit :=
fun bs => let '(buf, st) := bs in
ebind (stdio_write 2 buf [] st) (fun r => ITree.Ret (Ok (tt, (@nil Z, snd r)))).
#[using="Type"] Lemma stdio_write_loop_leaves : forall fuel fd iov (st : St),
tforall (fun r => match r with Ok q => snd q = st | Unr => True end) (stdio_write_loop fuel fd iov st).
Proof.
induction fuel as [|fuel IH]; intros fd iov st; cbn [stdio_write_loop].
- cbn. exact I.
- unfold mbind, msys, enode, ebind. cbn [ITree.bind].
intros x. destruct (dec_writev (iov_total iov) x) as [k|]; cbn [ITree.bind fst snd].
+ destruct (k =? iov_total iov); [cbn; reflexivity | apply IH].
+ exact I.
Qed.
#[using="Type"] Lemma stdio_writev_leaves : forall fd buf s (st : St),
tforall (fun r => match r with Ok q => snd q = st | Unr => True end) (stdio_write fd buf s st).
Proof.
intros fd buf s st. unfold stdio_write.
destruct (WRITE_MAX <? zlength buf + zlength s); [cbn; exact I | apply stdio_write_loop_leaves].
Qed.
#[using="Type"] Lemma OUT_stderr_leaves : forall p buf (st : St),
tforall (fun r => match r with Ok q => snd (snd q) = st | Unr => True end) (OUT_stderr p (buf, st)).
Proof.
intros p buf st. unfold OUT_stderr.
destruct (INTERNAL_BUFSIZ - zlength buf <? zlength p); [|cbn; reflexivity].
unfold ebind. eapply tforall_bind; [apply stdio_writev_leaves|]. intros [|[a s']] H; cbn; [exact I | exact H].
Qed.
#[using="Type"] Lemma outsk_flush_leaves : forall ps buf (st : St),
tforall (fun r => match r with Ok q => snd (snd q) = st | Unr => True end) (outsk OUT_stderr ps FLUSH_stderr (buf, st)).
Proof.
induction ps as [|p ps IH]; intros buf st; cbn [outsk].
- unfold FLUSH_stderr, ebind. eapply tforall_bind; [apply stdio_writev_leaves|]. intros [|[a s']] H; cbn; [exact I | exact H].
- unfold mbind at 1. unfold ebind. eapply tforall_bind; [apply OUT_stderr_leaves|].
intros [|[[] [buf' st']]] H; cbn in H |- *; [exact I|]. subst st'. apply IH.
Qed.
#[using="Type"] Lemma stderr_bridgeF : forall RNG ps buf (st : St) (Q : St -> footprint -> machine_state -> Prop) ms,
implS asegs RNG (outsk OUT_stderr ps FLUSH_stderr (buf, st)) (epostF (fun p RNG' ms' => Q (snd (snd p)) RNG' ms')) ms ->
implS asegs RNG (mbind (stderr_pieces buf ps) (fun b => stdio_write 2 b []) st) (epostF (fun p RNG' ms' => Q (snd p) RNG' ms')) ms.
Proof.
intros RNG ps; revert RNG. induction ps as [|p ps IH]; intros RNG buf st Q ms H; cbn [outsk stderr_pieces] in H |- *.
-
rewrite mbind_mret. unfold FLUSH_stderr, ebind in H.
eapply (implF_bind_elim asegs _ _ RNG _ _ _ _ _ _ (stdio_writev_leaves 2 buf [] st)); [|exact H].
intros [|[[] st']] RNG' ms' Hr Hi; cbn in Hi |- *; [apply evtF_done; exact I|].
cbn in Hi. exact Hi.
- destruct (INTERNAL_BUFSIZ - zlength buf <? zlength p) eqn:T.
+
unfold mbind at 1 in H. unfold OUT_stderr in H. rewrite T in H. unfold ebind in H.
apply implF_bind_assoc_rev in H.
unfold mbind at 1. change ((stdio_write 2 buf p ;;; stderr_pieces [] ps) st) with (ebind (stdio_write 2 buf p st) (fun q => stderr_pieces [] ps (snd q))).
unfold ebind. apply implF_bind_assoc.
eapply (implF_bind_ext2 asegs _ _ RNG _ _ _ _ _ _ _ (stdio_writev_leaves 2 buf p st)); [|exact H].
intros [|[[] st']] RNG' ms' Hr Hi; cbn [ITree.bind] in Hi |- *.
* exact Hi.
* cbn in Hr. subst st'. apply IH. exact Hi.
+
unfold mbind at 1 in H. unfold OUT_stderr in H. rewrite T in H. cbn [ebind ITree.bind fst snd] in H.
apply IH. exact H.
Qed.
#[using="Type"] Lemma stderr_bridgeA : forall RNG ps buf (st : St) (Q : St -> machine_state -> Prop) ms,
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
