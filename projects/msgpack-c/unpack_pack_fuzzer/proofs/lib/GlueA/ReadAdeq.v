(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Exec ITree Nodes Decode.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import AcctCore ExecF ITreeA NodesA SysStepF.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Adeq.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Import ShapeAlg(TSet, realizes).
Open Scope Z_scope.
Unset Lia Cache.

Section ReadAdeq.
Variable segs : list Segment.
Variable NMAX : nat.
Notation twfAA := (twfA node nstepA nexitA (nsafeA NMAX) fstepA NMAX).

Theorem implA_twfA_realizes_silent :
  forall {R} (t : itree node (exc R)) RNG A (Q : R -> footprint -> machine_state -> Prop)
         (P : R -> footprint -> alw -> Model -> Prop) ms mo mo_ (K : TSet),
  implA segs RNG t (epostF Q) ms ->
  twfAA RNG A t mo P ->
  m_halted mo = None -> minvA mo -> mrel A mo mo_ ->
  (forall r RNG' A' ms' mo' mo_', Q r RNG' ms' -> P r RNG' A' mo' -> acct_ok NMAX RNG' A' mo' ->
       m_halted mo' = None -> minvA mo' -> mrel A' mo' mo_' -> realizes segs (mkCfg ms' mo_') K) ->
  realizes segs (mkCfg ms mo_) K.
Proof.
  intros R t RNG A Q P ms mo mo_ K. eapply implF_twfA_realizes_silent. apply nodesA_sound.
Qed.

Lemma twfA_read : forall RNG A mo fd B n p off data (P : read_ans -> footprint -> alw -> Model -> Prop),
  acct_ok NMAX RNG A mo -> fd_inv mo ->
  fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some (FdFile p off) -> fs_lookup (m_fs mo) p = Some data ->
  1 <= n < 2^62 ->
  (let bs := file_read data off (Z_to_bv 64 n) in
   let mo' := with_fds (fd_insert (m_fds mo) (Z_to_bv 64 fd) (FdFile p (off + len_word bs)%bv)) mo in
   acct_ok NMAX RNG A mo' /\ P (RdData bs) RNG A mo') ->
  twfAA RNG A (enode (NRead fd B n) (dec_read B n)) mo P.
Proof.
  intros RNG A mo fd B n p off data P ACC FDI FD FS Hn HP. cbv zeta in HP. destruct HP as [ACC' HP].
  unfold enode. cbn [twfA]. split; [exact ACC|]. split; [split; [split; [exact FDI| exact I]| exact I]|]. split; [intros code mo' []|].
  intros rsp mo' evs ST. cbn [nstepA] in ST.
  destruct (nstep_dec_read fd B n mo rsp mo' evs ltac:(lia) ST) as (-> & a & DEC & HA).
  split; [reflexivity|]. exists RNG, A. split; [reflexivity|]. split; [intros q Hq; exact Hq|].
  rewrite DEC. destruct a as [e|bs].
  - exfalso. destruct HA as (_ & [(_ & LK)|(_ & LK)]); rewrite FD in LK; discriminate.
  - destruct HA as (p' & off' & data' & LK & FS' & -> & ->). rewrite FD in LK. injection LK as <- <-.
    rewrite FS in FS'. injection FS' as <-. cbn [twfA]. split; assumption.
Qed.

Lemma twfA_read_dir : forall RNG A mo fd B n (P : read_ans -> footprint -> alw -> Model -> Prop),
  acct_ok NMAX RNG A mo -> fd_inv mo ->
  fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some FdDir ->
  1 <= n < 2^62 ->
  P (RdErr EISDIR) RNG A mo ->
  twfAA RNG A (enode (NRead fd B n) (dec_read B n)) mo P.
Proof.
  intros RNG A mo fd B n P ACC FDI FD Hn HP.
  unfold enode. cbn [twfA]. split; [exact ACC|]. split; [split; [split; [exact FDI| exact I]| exact I]|]. split; [intros code mo' []|].
  intros rsp mo' evs ST. cbn [nstepA] in ST.
  destruct (nstep_dec_read fd B n mo rsp mo' evs ltac:(lia) ST) as (-> & a & DEC & HA).
  split; [reflexivity|]. exists RNG, A. split; [reflexivity|]. split; [intros q Hq; exact Hq|].
  rewrite DEC. destruct a as [e|bs].
  - destruct HA as (-> & [(_ & LK)|(-> & _)]); [rewrite FD in LK; discriminate|]. cbn [twfA]. split; assumption.
  - exfalso. destruct HA as (p' & off' & data' & LK & _). rewrite FD in LK. discriminate.
Qed.
End ReadAdeq.

Module TwinB.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Exec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.AcctCore OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ITreeA OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.NodesA OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.SysStepF.
Import Adeq.TwinB.

Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Import ShapeAlg(TSet, realizes).
Open Scope Z_scope.
Unset Lia Cache.

Section ReadAdeq.
Variable segs : list Segment.
Variable NMAX : nat.
Notation twfAA := (twfA node nstepA nexitA (nsafeA NMAX) fstepA NMAX).

Theorem implA_twfA_realizes_silent :
  forall {R} (t : itree node (exc R)) RNG A (Q : R -> footprint -> machine_state -> Prop)
         (P : R -> footprint -> alw -> Model -> Prop) ms mo mo_ (K : TSet),
  implA segs RNG t (epostF Q) ms ->
  twfAA RNG A t mo P ->
  m_halted mo = None -> minvA mo -> mrel A mo mo_ ->
  (forall r RNG' A' ms' mo' mo_', Q r RNG' ms' -> P r RNG' A' mo' -> acct_ok NMAX RNG' A' mo' ->
       m_halted mo' = None -> minvA mo' -> mrel A' mo' mo_' -> realizes segs (mkCfg ms' mo_') K) ->
  realizes segs (mkCfg ms mo_) K.
Proof.
  intros R t RNG A Q P ms mo mo_ K. eapply implF_twfA_realizes_silent. apply nodesA_sound.
Qed.

Lemma twfA_read : forall RNG A mo fd B n p off data (P : read_ans -> footprint -> alw -> Model -> Prop),
  acct_ok NMAX RNG A mo -> fd_inv mo ->
  fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some (FdFile p off) -> fs_lookup (m_fs mo) p = Some data ->
  1 <= n < 2^62 ->
  (let bs := file_read data off (Z_to_bv 64 n) in
   let mo' := with_fds (fd_insert (m_fds mo) (Z_to_bv 64 fd) (FdFile p (off + len_word bs)%bv)) mo in
   acct_ok NMAX RNG A mo' /\ P (RdData bs) RNG A mo') ->
  twfAA RNG A (enode (NRead fd B n) (dec_read B n)) mo P.
Proof.
  intros RNG A mo fd B n p off data P ACC FDI FD FS Hn HP. cbv zeta in HP. destruct HP as [ACC' HP].
  unfold enode. cbn [twfA]. split; [exact ACC|]. split; [split; [split; [exact FDI| exact I]| exact I]|]. split; [intros code mo' []|].
  intros rsp mo' evs ST. cbn [nstepA] in ST.
  destruct (nstep_dec_read fd B n mo rsp mo' evs ltac:(lia) ST) as (-> & a & DEC & HA).
  split; [reflexivity|]. exists RNG, A. split; [reflexivity|]. split; [intros q Hq; exact Hq|].
  rewrite DEC. destruct a as [e|bs].
  - exfalso. destruct HA as (_ & [(_ & LK)|(_ & LK)]); rewrite FD in LK; discriminate.
  - destruct HA as (p' & off' & data' & LK & FS' & -> & ->). rewrite FD in LK. injection LK as <- <-.
    rewrite FS in FS'. injection FS' as <-. cbn [twfA]. split; assumption.
Qed.

Lemma twfA_read_dir : forall RNG A mo fd B n (P : read_ans -> footprint -> alw -> Model -> Prop),
  acct_ok NMAX RNG A mo -> fd_inv mo ->
  fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some FdDir ->
  1 <= n < 2^62 ->
  P (RdErr EISDIR) RNG A mo ->
  twfAA RNG A (enode (NRead fd B n) (dec_read B n)) mo P.
Proof.
  intros RNG A mo fd B n P ACC FDI FD Hn HP.
  unfold enode. cbn [twfA]. split; [exact ACC|]. split; [split; [split; [exact FDI| exact I]| exact I]|]. split; [intros code mo' []|].
  intros rsp mo' evs ST. cbn [nstepA] in ST.
  destruct (nstep_dec_read fd B n mo rsp mo' evs ltac:(lia) ST) as (-> & a & DEC & HA).
  split; [reflexivity|]. exists RNG, A. split; [reflexivity|]. split; [intros q Hq; exact Hq|].
  rewrite DEC. destruct a as [e|bs].
  - destruct HA as (-> & [(_ & LK)|(-> & _)]); [rewrite FD in LK; discriminate|]. cbn [twfA]. split; assumption.
  - exfalso. destruct HA as (p' & off' & data' & LK & _). rewrite FD in LK. discriminate.
Qed.
End ReadAdeq.
End TwinB.
