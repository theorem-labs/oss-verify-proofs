(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (6 recorded proofs replaced by written proofs (stdio_write_loop_leaves, stdio_writev_leaves, OUT_stderr_leaves and 3 more)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes Decode.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import Prelim Monad.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SoftFloat FmtFp.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import Stdio.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import Printf_model Printf_mlib Printf_pieces.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF ITreeA.
From OSSVerify.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg AProto MonadF F_printf_iface.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_Printf_bridge () := "C59OSSVerify5KrLib4Spec5Monad4munrC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib4Spec5Stdio@stdio_write_loopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6MonadF@implF_bind_assocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio6upd_soC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree4bindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6MonadFDimplF_bind_assoc_revC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6MonadF7tforallC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6MonadF<tforall_bindC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndC59OSSVerify5KrLib5BothW6MonadF?implF_bind_ext2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6MonadF?implF_bind_elimC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6MonadF5postFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6ITreeA5implFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6ITreeA:implF_monoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6ITreeA6epostFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree5ebindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad:mbind_mretC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes4prod00I69OSSVerify5KrLib3Lib5ITree3Exc3exc00C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C59OSSVerify5KrLib4Spec5Stdio9iov_totalC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6Decode:dec_writevC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00I59OSSVerify5KrLib3Lib5ITree5itree00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes6option01K47Corelib4Init9Datatypes6option02K69OSSVerify5KrLib3Lib5ITree3Exc3exc02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5ITree5itree01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib3Lib5ITree3Exc3exc01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad1MC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC56Stdlib6ZArith6BinInt1Z3eqbC59OSSVerify5KrLib4Spec5Monad4mretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio;iov_advanceC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C47Corelib5Lists7ListDef3mapK59OSSVerify5KrLib3Lib5Nodes4node02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5ITree5itree02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad4msysC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad5mbindC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02C47Corelib4Init9Datatypes7nat_indI59OSSVerify5KrLib3Lib5Nodes4node00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes4unit00I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01K47Corelib4Init9Datatypes3nat01C59OSSVerify5KrLib3Lib5ITree4respC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib4Spec5Stdio8to_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Prelim7zlengthC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6to_natK47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02c59OSSVerify5KrLib5BothW=Printf_bridgeGstdio_write_loop_leavesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio;stdio_writeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio9WRITE_MAXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW>F_printf_iface:OUT_stderrC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subK47Corelib7Numbers7BinNums1Z02C47Corelib4Init9Datatypes3appc59OSSVerify5KrLib5BothW=Printf_bridgeCstdio_writev_leavesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio?INTERNAL_BUFSIZC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common=Printf_pieces5outskC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW=Printf_bridge<FLUSH_stderrC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW=Printf_bridgeAOUT_stderr_leavesC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes8list_indC59OSSVerify5KrLib4Spec5Stdio=stderr_piecesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6NodesA8at_nodeAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF4evtFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF9evtF_doneC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC59OSSVerify5KrLib5BothW4BImg5bsegsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AProto6fstepSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF9footprintC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes4bool02C59OSSVerify5KrLib5BothW6MonadF6implAMC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00c59OSSVerify5KrLib5BothW=Printf_bridge>stderr_bridgeFC1?~~~~~~~~~~~~~~~".
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
