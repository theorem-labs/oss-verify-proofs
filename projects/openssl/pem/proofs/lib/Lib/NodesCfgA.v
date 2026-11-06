(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import PropExec MState Mem ITree Nodes Decode NodesCfg DecodeCfg DecodeCfg2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section WithCeiling.
Context {CE : Ceiling}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition node_live (n : node) (mo : Model) : Prop := exists rsp mo' evs, nstep_c n mo rsp mo' evs.

(* [comment removed for export] *)
Definition node_noerr (n : node) (mo : Model) : Prop :=
  match n with
  | NMmap _ _ _ flags =>
      (Z.land flags 16 = 0 -> forall rsp mo' evs, nstep_c n mo rsp mo' evs -> errno_of (eff_ret rsp) = None) /\ node_live n mo
  | NMprotect _ _ _ => (forall rsp mo' evs, nstep_c n mo rsp mo' evs -> errno_of (eff_ret rsp) = None) /\ node_live n mo
  | _ => True
  end.

Lemma node_decided_of_live : forall n mo, node_live n mo -> node_decided n mo.
Proof.
  intros n mo (rsp & mo' & evs & H). destruct (node_refusal_b n mo (eff_ret rsp)) eqn:E.
  - right. exact (proj2 H E).
  - left. exists rsp, mo', evs. split; [exact (proj1 H)| exact E].
Qed.

Lemma node_live_of_decided : forall n mo, node_decided n mo -> (exists rsp mo' evs, nstep n mo rsp mo' evs) -> node_live n mo.
Proof.
  intros n mo [(rsp & mo' & evs & H & Hr)|Hall] (rsp2 & mo2 & evs2 & H2).
  - exists rsp, mo', evs. exact (nstep_c_of_grant _ _ _ _ _ H Hr).
  - exists rsp2, mo2, evs2. split; [exact H2|]. intros _. exact Hall.
Qed.

Lemma node_live_of_grant : forall n mo,
  (exists eff mo' evs, nstep n mo eff mo' evs /\ node_refusal_b n mo (eff_ret eff) = false) -> node_live n mo.
Proof. intros n mo (eff & mo' & evs & H & Hr). exists eff, mo', evs. exact (nstep_c_of_grant _ _ _ _ _ H Hr). Qed.

Lemma node_live_nonalloc : forall n mo, node_alloc n = false -> (exists rsp mo' evs, nstep n mo rsp mo' evs) -> node_live n mo.
Proof. intros n mo Hn (rsp & mo' & evs & H). exists rsp, mo', evs. exact (nstep_c_of_nonalloc _ _ _ _ _ Hn H). Qed.

(* [comment removed for export] *)
Lemma node_live_brk : forall req mo, node_live (NBrk req) mo.
Proof.
  intros req mo. apply node_live_of_decided; [apply node_decided_brk|].
  assert (Hb : Mmap.brk_r_ok mo (Z_to_bv 64 req) (vm_brk (m_vmmaps mo)) = true).
  { unfold Mmap.brk_r_ok. rewrite bv_eqb_refl, orb_true_r.
    assert (Hg : Mmap.brk_grow_ok mo (Z_to_bv 64 req) (vm_brk (m_vmmaps mo)) = true).
    { unfold Mmap.brk_grow_ok. rewrite Z.ltb_irrefl, andb_false_r. reflexivity. }
    rewrite Hg. destruct (_ || _); [reflexivity|]. destruct (_ <? _)%Z; reflexivity. }
  eexists _, _, _. exact (nstep_brk_intro req mo _ Hb).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition nstep_a (n : node) (mo : Model) (rsp : resp) (mo' : Model) (evs : list event) : Prop :=
  nstep_c n mo rsp mo' evs /\ node_noerr n mo.

Lemma nstep_a_c : forall n mo rsp mo' evs, nstep_a n mo rsp mo' evs -> nstep_c n mo rsp mo' evs.
Proof. intros n mo rsp mo' evs H. exact (proj1 H). Qed.

Lemma nstep_a_nstep : forall n mo rsp mo' evs, nstep_a n mo rsp mo' evs -> nstep n mo rsp mo' evs.
Proof. intros n mo rsp mo' evs H. exact (nstep_c_nstep _ _ _ _ _ (proj1 H)). Qed.

Lemma nstep_a_noerr : forall n mo rsp mo' evs, nstep_a n mo rsp mo' evs -> node_noerr n mo.
Proof. intros n mo rsp mo' evs H. exact (proj2 H). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma tpath_a_c : forall {R} (t : itree node R) mo tr r mo', tpath nstep_a t mo tr r mo' -> tpath nstep_c t mo tr r mo'.
Proof.
  intros R t. induction t as [r0|n k IH|v k IH]; intros mo tr r mo' H; cbn in *; [exact H| |].
  - destruct H as (rsp & mo1 & evs & tr' & Hst & Hp & ->). exists rsp, mo1, evs, tr'.
    split; [exact (nstep_a_c _ _ _ _ _ Hst)|]. split; [exact (IH _ _ _ _ _ Hp)| reflexivity].
  - destruct H as (a & Hv & Hp). exists a. split; [exact Hv| exact (IH a _ _ _ _ Hp)].
Qed.

Lemma tpath_c_a : forall {R} (t : itree node R) mo tr r mo',
  tsafe nstep_c node_noerr t mo -> tpath nstep_c t mo tr r mo' -> tpath nstep_a t mo tr r mo'.
Proof.
  intros R t. induction t as [r0|n k IH|v k IH]; intros mo tr r mo' Hs H; cbn in *; [exact H| |].
  - destruct Hs as [Hn Hk]. destruct H as (rsp & mo1 & evs & tr' & Hst & Hp & ->). exists rsp, mo1, evs, tr'.
    split; [exact (conj Hst Hn)|]. split; [exact (IH _ _ _ _ _ (Hk _ _ _ Hst) Hp)| reflexivity].
  - destruct H as (a & Hv & Hp). exists a. split; [exact Hv| exact (IH a _ _ _ _ (Hs a Hv) Hp)].
Qed.

Lemma leaves_unreachable_a_c : forall {R} (t : itree node R) mo,
  tsafe nstep_c node_noerr t mo -> leaves_unreachable_m nstep_a t mo -> leaves_unreachable_m nstep_c t mo.
Proof. intros R t mo Hs H tr r mo' Hp. exact (H tr r mo' (tpath_c_a t mo tr r mo' Hs Hp)). Qed.

Lemma tsafe_a_c : forall {R} (S : node -> Model -> Prop) (t : itree node R) mo,
  tsafe nstep_c node_noerr t mo -> tsafe nstep_a S t mo -> tsafe nstep_c S t mo.
Proof.
  intros R S t. induction t as [r0|n k IH|v k IH]; intros mo Hs H; cbn in *; [exact I| |].
  - destruct Hs as [Hn Hk]. destruct H as [HS Hk']. split; [exact HS|].
    intros rsp mo' evs Hst. apply IH; [exact (Hk _ _ _ Hst)| exact (Hk' _ _ _ (conj Hst Hn))].
  - intros a Hv. apply IH; [exact (Hs a Hv)| exact (H a Hv)].
Qed.

Lemma tsafe_c_a : forall {R} (S : node -> Model -> Prop) (t : itree node R) mo,
  tsafe nstep_c S t mo -> tsafe nstep_a S t mo.
Proof.
  intros R S t. induction t as [r0|n k IH|v k IH]; intros mo H; cbn in *; [exact I| |].
  - destruct H as [HS Hk]. split; [exact HS|]. intros rsp mo' evs Hst. apply IH. exact (Hk _ _ _ (nstep_a_c _ _ _ _ _ Hst)).
  - intros a Hv. apply IH. exact (H a Hv).
Qed.

(* [comment removed for export] *)
Lemma node_decided_of_noerr : forall n mo, node_noerr n mo -> node_alloc n = true -> node_decided n mo.
Proof.
  intros n mo H Ha. destruct n; try discriminate Ha.
  - apply node_decided_brk.
  - apply node_decided_of_live. exact (proj2 H).
  - apply node_decided_of_live. exact (proj2 H).
Qed.

Lemma tsafe_nsafe_c : forall {R} (t : itree node R) mo,
  tsafe nstep_c node_noerr t mo -> tsafe nstep_c nsafe t mo -> tsafe nstep_c nsafe_c t mo.
Proof.
  intros R t. induction t as [r0|n k IH|v k IH]; intros mo H1 H2; cbn in *; [exact I| |].
  - destruct H1 as [Hn Hk1]. destruct H2 as [Hs Hk2]. split; [split; [exact Hs| exact (node_decided_of_noerr n mo Hn)]|].
    intros rsp mo' evs Hst. apply IH; [exact (Hk1 _ _ _ Hst)| exact (Hk2 _ _ _ Hst)].
  - intros a Hv. apply IH; [exact (H1 a Hv)| exact (H2 a Hv)].
Qed.

End WithCeiling.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Module A.
Section WithCeiling.
Context {CE : Ceiling}.

Lemma nstep_dec_read : forall fd buf count mo rsp mo' evs,
  (0 <= count < 2^64)%Z ->
  nstep_a (NRead fd buf count) mo rsp mo' evs ->
  evs = [] /\
  exists a, dec_read buf count rsp = Some a /\
  match a with
  | RdErr e => mo' = mo /\
      ((e = EBADF /\ fd_lookup (m_fds mo) (Z_to_bv 64 fd) = None)
       \/ (e = EISDIR /\ fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some FdDir))
  | RdData bs => exists p off data,
      fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some (FdFile p off) /\
      fs_lookup (m_fs mo) p = Some data /\
      bs = file_read data off (Z_to_bv 64 count) /\
      mo' = with_fds (fd_insert (m_fds mo) (Z_to_bv 64 fd) (FdFile p (off + len_word bs)%bv)) mo
  end.
Proof. intros; eapply DecodeCfg.nstep_dec_read; try eassumption; apply nstep_a_c; eassumption. Qed.

Lemma nstep_dec_writev : forall fd bufs mo rsp mo' evs,
  (Z.of_nat (length (concat bufs)) < 2^64)%Z ->
  nstep_a (NWritev fd bufs) mo rsp mo' evs ->
  mo' = mo /\
  exists k, dec_writev (Z.of_nat (length (concat bufs))) rsp = Some (Z.of_nat k)
    /\ (k <= length (concat bufs))%nat
    /\ (k = 0%nat <-> concat bufs = [])
    /\ evs = map (WriteEv (Z_to_bv 64 fd)) (firstn k (concat bufs)).
Proof. intros; eapply DecodeCfg.nstep_dec_writev; try eassumption; apply nstep_a_c; eassumption. Qed.

Lemma nstep_dec_open : forall path mo rsp mo' evs,
  minv mo ->
  nstep_a (NOpen path) mo rsp mo' evs ->
  evs = [] /\
  exists a, dec_open rsp = Some a /\
  match a with
  | SErr e => mo' = mo /\ (1 <= e <= 4095)%Z
  | SVal fd => Z_to_bv 64 fd = alloc_fd (m_fds mo) /\ (3 <= fd <= 4096)%Z
      /\ fd_lookup (m_fds mo) (Z_to_bv 64 fd) = None
      /\ exists ent, (ent = FdDir \/ ent = FdFile path (Z_to_bv 64 0))
         /\ mo' = with_fds (fd_insert (m_fds mo) (Z_to_bv 64 fd) ent) mo
  end.
Proof. intros; eapply DecodeCfg.nstep_dec_open; try eassumption; apply nstep_a_c; eassumption. Qed.

Lemma nstep_dec_close : forall fd mo rsp mo' evs,
  nstep_a (NClose fd) mo rsp mo' evs ->
  evs = [] /\
  exists a, dec_close rsp = Some a /\
  match a with
  | SErr e => e = EBADF /\ mo' = mo /\ fd_lookup (m_fds mo) (Z_to_bv 64 fd) = None
  | SVal v => v = 0%Z /\ fd_lookup (m_fds mo) (Z_to_bv 64 fd) <> None
      /\ mo' = with_fds (fd_remove (m_fds mo) (Z_to_bv 64 fd)) mo
  end.
Proof. intros; eapply DecodeCfg.nstep_dec_close; try eassumption; apply nstep_a_c; eassumption. Qed.

Lemma nstep_dec_ioctl : forall fd req mo rsp mo' evs,
  nstep_a (NIoctl fd req) mo rsp mo' evs ->
  dec_ioctl rsp = Some (SErr ENOTTY) /\ mo' = mo /\ evs = [].
Proof. intros; eapply DecodeCfg.nstep_dec_ioctl; try eassumption; apply nstep_a_c; eassumption. Qed.

Lemma nstep_dec_set_tid : forall mo rsp mo' evs,
  minv mo ->
  nstep_a NSetTid mo rsp mo' evs ->
  evs = [] /\
  exists t, dec_set_tid rsp = Some t /\ (0 < t < PID_MAX_ENVELOPE)%Z /\
  ((m_tid mo = Some (Z_to_bv 64 t) /\ mo' = mo) \/ (m_tid mo = None /\ mo' = with_tid (Z_to_bv 64 t) mo)).
Proof. intros; eapply DecodeCfg.nstep_dec_set_tid; try eassumption; apply nstep_a_c; eassumption. Qed.

Lemma nstep_exit_none : forall c mo rsp mo' evs, nstep_a (NExit c) mo rsp mo' evs -> False.
Proof. intros; eapply DecodeCfg.nstep_exit_none; try eassumption; apply nstep_a_c; eassumption. Qed.

Lemma minv_preserved_gen : forall n mo eff mo' evs,
  minv mo -> m_halted mo = None -> no_noreserve n -> nstep_a n mo eff mo' evs -> m_halted mo' = None /\ minv mo'.
Proof. intros; eapply DecodeCfg.minv_preserved_gen; try eassumption; apply nstep_a_c; eassumption. Qed.

Lemma minv_preserved : forall n mo eff mo' evs,
  minv mo -> m_halted mo = None -> nsafe n mo -> nstep_a n mo eff mo' evs -> m_halted mo' = None /\ minv mo'.
Proof. intros; eapply DecodeCfg.minv_preserved; try eassumption; apply nstep_a_c; eassumption. Qed.

End WithCeiling.
End A.
