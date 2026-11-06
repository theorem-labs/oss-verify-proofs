(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.openssl.pem.lib.Common Require Import CfgStep.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import PropExec MState Mem ITree Nodes Decode NodesCfg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Section WithCeiling.
Context {CE : Ceiling}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma nstep_dec_read : forall fd buf count mo rsp mo' evs,
  (0 <= count < 2^64)%Z ->
  nstep_c (NRead fd buf count) mo rsp mo' evs ->
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
Proof. intros; eapply Decode.nstep_dec_read; try eassumption; apply nstep_c_nstep; eassumption. Qed.

Lemma nstep_dec_writev : forall fd bufs mo rsp mo' evs,
  (Z.of_nat (length (concat bufs)) < 2^64)%Z ->
  nstep_c (NWritev fd bufs) mo rsp mo' evs ->
  mo' = mo /\
  exists k, dec_writev (Z.of_nat (length (concat bufs))) rsp = Some (Z.of_nat k)
    /\ (k <= length (concat bufs))%nat
    /\ (k = 0%nat <-> concat bufs = [])
    /\ evs = map (WriteEv (Z_to_bv 64 fd)) (firstn k (concat bufs)).
Proof. intros; eapply Decode.nstep_dec_writev; try eassumption; apply nstep_c_nstep; eassumption. Qed.

Lemma nstep_dec_open : forall path mo rsp mo' evs,
  minv mo ->
  nstep_c (NOpen path) mo rsp mo' evs ->
  evs = [] /\
  exists a, dec_open rsp = Some a /\
  match a with
  | SErr e => mo' = mo /\ (1 <= e <= 4095)%Z
  | SVal fd => Z_to_bv 64 fd = alloc_fd (m_fds mo) /\ (3 <= fd <= 4096)%Z
      /\ fd_lookup (m_fds mo) (Z_to_bv 64 fd) = None
      /\ exists ent, (ent = FdDir \/ ent = FdFile path (Z_to_bv 64 0))
         /\ mo' = with_fds (fd_insert (m_fds mo) (Z_to_bv 64 fd) ent) mo
  end.
Proof. intros; eapply Decode.nstep_dec_open; try eassumption; apply nstep_c_nstep; eassumption. Qed.

Lemma nstep_dec_close : forall fd mo rsp mo' evs,
  nstep_c (NClose fd) mo rsp mo' evs ->
  evs = [] /\
  exists a, dec_close rsp = Some a /\
  match a with
  | SErr e => e = EBADF /\ mo' = mo /\ fd_lookup (m_fds mo) (Z_to_bv 64 fd) = None
  | SVal v => v = 0%Z /\ fd_lookup (m_fds mo) (Z_to_bv 64 fd) <> None
      /\ mo' = with_fds (fd_remove (m_fds mo) (Z_to_bv 64 fd)) mo
  end.
Proof. intros; eapply Decode.nstep_dec_close; try eassumption; apply nstep_c_nstep; eassumption. Qed.

Lemma nstep_dec_ioctl : forall fd req mo rsp mo' evs,
  nstep_c (NIoctl fd req) mo rsp mo' evs ->
  dec_ioctl rsp = Some (SErr ENOTTY) /\ mo' = mo /\ evs = [].
Proof. intros; eapply Decode.nstep_dec_ioctl; try eassumption; apply nstep_c_nstep; eassumption. Qed.

Lemma nstep_dec_set_tid : forall mo rsp mo' evs,
  minv mo ->
  nstep_c NSetTid mo rsp mo' evs ->
  evs = [] /\
  exists t, dec_set_tid rsp = Some t /\ (0 < t < PID_MAX_ENVELOPE)%Z /\
  ((m_tid mo = Some (Z_to_bv 64 t) /\ mo' = mo) \/ (m_tid mo = None /\ mo' = with_tid (Z_to_bv 64 t) mo)).
Proof. intros; eapply Decode.nstep_dec_set_tid; try eassumption; apply nstep_c_nstep; eassumption. Qed.

Lemma nstep_exit_none : forall c mo rsp mo' evs, nstep_c (NExit c) mo rsp mo' evs -> False.
Proof. intros; eapply Decode.nstep_exit_none; try eassumption; apply nstep_c_nstep; eassumption. Qed.

Lemma nstep_dec_brk0 : forall mo rsp mo' evs,
  nstep_c (NBrk 0) mo rsp mo' evs ->
  evs = [] /\ dec_brk0 rsp = Some (bv_unsigned (vm_brk (m_vmmaps mo))) /\ vm_only mo mo'
  /\ vm_brk (m_vmmaps mo') = vm_brk (m_vmmaps mo).
Proof. intros; eapply Decode.nstep_dec_brk0; try eassumption; apply nstep_c_nstep; eassumption. Qed.

Lemma nstep_dec_brk : forall req mo rsp mo' evs,
  let h := m_vmmaps mo in
  (0 < bv_unsigned (vm_brk h))%Z ->
  (bv_unsigned (vm_start_brk h) <= bv_unsigned (vm_brk h))%Z ->
  (bv_unsigned (vm_brk h) <= req < 2^64)%Z ->
  alloc_top h = alloc_ceiling ->
  (bv_unsigned (vm_brk h) mod 4096 = 0)%Z -> (req mod 4096 = 0)%Z ->
  nstep_c (NBrk req) mo rsp mo' evs ->
  evs = [] /\ vm_only mo mo' /\
  exists a, dec_brk (bv_unsigned (vm_brk h)) req rsp = Some a /\
  match a with
  | BrkSame => vm_brk (m_vmmaps mo') = vm_brk h
  | BrkGrown => vm_brk (m_vmmaps mo') = Z_to_bv 64 req
  end.
Proof. intros; eapply Decode.nstep_dec_brk; try eassumption; apply nstep_c_nstep; eassumption. Qed.

Lemma nstep_dec_mmap : forall len avoid mo rsp mo' evs,
  let h := m_vmmaps mo in
  (0 < len)%Z -> (mmap_len len < 2^64)%Z ->
  alloc_top h = alloc_ceiling ->
  Forall (covered (vm_reserved h ++ vm_maps h)) avoid ->
  nstep_c (NMmap 0 len (PROT_READ + PROT_WRITE) (MAP_PRIVATE + MAP_ANONYMOUS)) mo rsp mo' evs ->
  evs = [] /\ vm_only mo mo' /\
  exists x, dec_mmap len avoid rsp = Some x /\
  match x with
  | MmErr e => e = ENOMEM /\ mo' = mo
  | MmOk a => mmap_addr_ok len avoid a = true
      /\ region_free (vm_reserved h ++ vm_maps h) (Z_to_bv 64 a) (Z_to_bv 64 (mmap_len len)) = true
      /\ (vm_backing_used mo + mmap_len len <= vm_limit h)%Z
      /\ m_vmmaps mo' = mkVmMapsFull (vm_reserved h) ((Z_to_bv 64 a, Z_to_bv 64 (mmap_len len)) :: vm_maps h)
                                    (vm_noaccess h) (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)
  end.
Proof. intros; eapply Decode.nstep_dec_mmap; try eassumption; apply nstep_c_nstep; eassumption. Qed.

Lemma nstep_dec_mmap_none : forall len avoid mo rsp mo' evs,
  let h := m_vmmaps mo in
  (0 < len)%Z -> (mmap_len len < 2^64)%Z ->
  alloc_top h = alloc_ceiling ->
  Forall (covered (vm_reserved h ++ vm_maps h)) avoid ->
  nstep_c (NMmap 0 len PROT_NONE (MAP_PRIVATE + MAP_ANONYMOUS)) mo rsp mo' evs ->
  evs = [] /\ vm_only mo mo' /\
  exists x, dec_mmap_none len avoid rsp = Some x /\
  match x with
  | MmErr e => e = ENOMEM /\ mo' = mo
  | MmOk a => mmap_addr_ok len avoid a = true
      /\ region_free (vm_reserved h ++ vm_maps h) (Z_to_bv 64 a) (Z_to_bv 64 (mmap_len len)) = true
      /\ m_vmmaps mo' = mkVmMapsFull (vm_reserved h) ((Z_to_bv 64 a, Z_to_bv 64 (mmap_len len)) :: vm_maps h)
                                    ((Z_to_bv 64 a, Z_to_bv 64 (mmap_len len)) :: vm_noaccess h)
                                    (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)
  end.
Proof. intros; eapply Decode.nstep_dec_mmap_none; try eassumption; apply nstep_c_nstep; eassumption. Qed.

Lemma nstep_dec_munmap : forall addr len mo rsp mo' evs,
  let h := m_vmmaps mo in
  let a := Z_to_bv 64 addr in let n := Z_to_bv 64 (mmap_len len) in
  (0 <= addr < 2^64)%Z -> (0 < len)%Z -> (mmap_len len < 2^64)%Z ->
  nstep_c (NMunmap addr len) mo rsp mo' evs ->
  evs = [] /\ vm_only mo mo' /\
  exists x, dec_munmap addr len rsp = Some x /\
  match x with
  | RgErr e => e = EINVAL /\ mo' = mo
  | RgDone false => mo' = mo /\ munmap_free_ok h a (mmap_len len) = true
  | RgDone true => map_has (vm_maps h) a n = true
      /\ m_vmmaps mo' = mkVmMapsFull (vm_reserved h) (map_remove (vm_maps h) a)
                                    (maps_subtract (vm_noaccess h) (bv_unsigned a) (bv_unsigned a + bv_unsigned n))
                                    (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)
  end.
Proof. intros; eapply Decode.nstep_dec_munmap; try eassumption; apply nstep_c_nstep; eassumption. Qed.

Lemma nstep_dec_mprotect : forall addr len mo rsp mo' evs,
  let h := m_vmmaps mo in
  let a := Z_to_bv 64 addr in let n := Z_to_bv 64 (mmap_len len) in
  (0 <= addr < 2^64)%Z -> (0 < len)%Z -> (mmap_len len < 2^64)%Z ->
  nstep_c (NMprotect addr len (PROT_READ + PROT_WRITE)) mo rsp mo' evs ->
  evs = [] /\ vm_only mo mo' /\
  exists x, dec_mprotect addr len rsp = Some x /\
  match x with
  | RgErr e => (e = EINVAL \/ e = ENOMEM) /\ mo' = mo
  | RgDone false => mo' = mo
  | RgDone true => map_contains (vm_noaccess h) a n = true /\ map_contains (vm_maps h) a n = true
      /\ mprotect_budget_ok mo a n = true
      /\ m_vmmaps mo' = mkVmMapsFull (vm_reserved h) (vm_maps h)
                                    (maps_subtract (vm_noaccess h) (bv_unsigned a) (bv_unsigned a + bv_unsigned n))
                                    (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)
  end.
Proof. intros; eapply Decode.nstep_dec_mprotect; try eassumption; apply nstep_c_nstep; eassumption. Qed.

Lemma nstep_mm_vm_only : forall n mo eff mo' evs,
  match n with NBrk _ | NMunmap _ _ | NMprotect _ _ _ => True
             | NMmap _ _ _ flags => mmap_noreserve_b (Z_to_bv 64 flags) = false | _ => False end ->
  nstep_c n mo eff mo' evs -> vm_only mo mo' /\ evs = [] /\ eff_copyins eff = [].
Proof. intros n mo eff mo' evs Hn H. exact (Nodes.nstep_mm_vm_only n mo eff mo' evs Hn (nstep_c_nstep _ _ _ _ _ H)). Qed.

Lemma minv_preserved_gen : forall n mo eff mo' evs,
  minv mo -> m_halted mo = None -> no_noreserve n -> nstep_c n mo eff mo' evs -> m_halted mo' = None /\ minv mo'.
Proof. intros n mo eff mo' evs H1 H2 H3 H. exact (Nodes.minv_preserved_gen n mo eff mo' evs H1 H2 H3 (nstep_c_nstep _ _ _ _ _ H)). Qed.

Lemma minv_preserved : forall n mo eff mo' evs,
  minv mo -> m_halted mo = None -> nsafe n mo -> nstep_c n mo eff mo' evs -> m_halted mo' = None /\ minv mo'.
Proof. intros n mo eff mo' evs H1 H2 H3 H. exact (Nodes.minv_preserved n mo eff mo' evs H1 H2 H3 (nstep_c_nstep _ _ _ _ _ H)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma node_refusal_mmap_enomem : forall addr len prot flags mo,
  node_refusal_b (NMmap addr len prot flags) mo (errno_ret ENOMEM) = true.
Proof.
  intros. unfold node_refusal_b. cbn [node_alloc node_input].
  apply refusal_b_mmap_errno; [cbn [pure_input in_sysno]; apply unsigned_lit; lia| left; reflexivity].
Qed.

Lemma node_refusal_mprotect_enomem : forall addr len prot mo,
  node_refusal_b (NMprotect addr len prot) mo (errno_ret ENOMEM) = true.
Proof.
  intros. unfold node_refusal_b. cbn [node_alloc node_input].
  apply refusal_b_mprotect_errno; [cbn [pure_input in_sysno]; apply unsigned_lit; lia| left; reflexivity].
Qed.

(* [comment removed for export] *)
Lemma node_refusal_mmap_below : forall addr len prot flags mo r, (bv_unsigned r <= 2^64 - 4096)%Z ->
  node_refusal_b (NMmap addr len prot flags) mo r = false.
Proof.
  intros. unfold node_refusal_b. cbn [node_alloc node_input].
  apply refusal_b_mmap_below; [cbn [pure_input in_sysno]; apply unsigned_lit; lia| assumption].
Qed.

Lemma node_refusal_mprotect_below : forall addr len prot mo r, (bv_unsigned r <= 2^64 - 4096)%Z ->
  node_refusal_b (NMprotect addr len prot) mo r = false.
Proof.
  intros. unfold node_refusal_b. cbn [node_alloc node_input].
  apply refusal_b_mprotect_below; [cbn [pure_input in_sysno]; apply unsigned_lit; lia| assumption].
Qed.

Lemma node_refusal_brk : forall req mo r,
  node_refusal_b (NBrk req) mo r = brk_refusal_b mo (Z_to_bv 64 req) r.
Proof.
  intros. unfold node_refusal_b. cbn [node_alloc node_input].
  apply refusal_b_brk. cbn [pure_input in_sysno]. apply unsigned_lit; lia.
Qed.

(* [comment removed for export] *)
Lemma nstep_brk_intro : forall req mo r, Mmap.brk_r_ok mo (Z_to_bv 64 req) r = true ->
  nstep (NBrk req) mo (mkEffectU r [] (Mmap.brk_zeros (Z_to_bv 64 req) r (vm_brk (m_vmmaps mo)))
                                  (Mmap.brk_unmaps r (vm_brk (m_vmmaps mo))) [] [])
        (Mmap.with_brk_next mo (Z_to_bv 64 req) r) [].
Proof.
  intros req mo r H. apply nstep_brk_iff. unfold check_brk. rewrite H.
  rewrite !(proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
Qed.

Lemma nstep_brk_r_ok : forall req mo eff mo' evs, nstep (NBrk req) mo eff mo' evs ->
  Mmap.brk_r_ok mo (Z_to_bv 64 req) (eff_ret eff) = true.
Proof.
  intros req mo eff mo' evs H. apply nstep_brk_iff in H. unfold check_brk in H.
  destruct eff as [r ws zs us cs ci]. destruct ws; [| discriminate H]. destruct cs; [| discriminate H]. destruct ci; [| discriminate H].
  cbn [eff_ret]. destruct (Mmap.brk_r_ok mo (Z_to_bv 64 req) r); [reflexivity| discriminate H].
Qed.

(* [comment removed for export] *)
Lemma node_decided_brk : forall req mo, node_decided (NBrk req) mo.
Proof.
  intros req mo. set (q := Z_to_bv 64 req). set (h := m_vmmaps mo). set (b := vm_brk h).
  destruct (Mmap.brk_r_ok mo q q) eqn:Hq.
  - (* [comment removed for export] *)
    left. eexists _, _, _. split; [exact (nstep_brk_intro req mo q Hq)|].
    rewrite node_refusal_brk. cbn [eff_ret]. fold q. unfold brk_refusal_b. fold h b.
    destruct (bv_eqb q b) eqn:E; [rewrite !andb_false_r; reflexivity| rewrite andb_false_r; reflexivity].
  - destruct (w_is0 q || (bv_unsigned q <? bv_unsigned (Mmap.min_brk h))%Z) eqn:Hqi.
    + (* [comment removed for export] *)
      assert (Hb : Mmap.brk_r_ok mo q b = true).
      { unfold Mmap.brk_r_ok. fold h b. rewrite Hqi. apply bv_eqb_eq. reflexivity. }
      left. eexists _, _, _. split; [exact (nstep_brk_intro req mo b Hb)|].
      rewrite node_refusal_brk. cbn [eff_ret]. fold q. unfold brk_refusal_b. fold h.
      apply orb_true_iff in Hqi as [E|E]; rewrite E; cbn [negb andb]; [reflexivity| rewrite andb_false_r; reflexivity].
    + (* [comment removed for export] *)
      right. intros eff mo' evs Hn. pose proof (nstep_brk_r_ok req mo eff mo' evs Hn) as Hr. fold q in Hr.
      rewrite node_refusal_brk. fold q. unfold brk_refusal_b. fold h b.
      apply orb_false_iff in Hqi as [E1 E2]. rewrite E1, E2. cbn [negb andb].
      unfold Mmap.brk_r_ok in Hr, Hq. fold h b in Hr, Hq. rewrite E1, E2 in Hr, Hq. cbn [orb] in Hr, Hq.
      destruct (bv_unsigned q <? bv_unsigned b)%Z eqn:Elt.
      * rewrite bv_eqb_refl in Hq. discriminate Hq.
      * rewrite bv_eqb_refl in Hq. cbn [orb andb] in Hq.
        destruct (bv_eqb (eff_ret eff) q) eqn:Eq.
        { apply bv_eqb_eq in Eq. rewrite Eq in Hr. cbn [orb andb] in Hr. congruence. }
        cbn [orb] in Hr. apply andb_prop in Hr as [Hrb _]. rewrite Hrb, andb_true_r.
        destruct (bv_eqb q b) eqn:Eqb; [| reflexivity].
        apply bv_eqb_eq in Eqb. rewrite <- Eqb in Hrb. rewrite Hrb in Eq. discriminate Eq.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma errno_ret_in_small : forall es r, Forall (fun e => (1 <= e <= 4095)%Z) es -> (bv_unsigned r <= 2^64 - 4096)%Z ->
  errno_ret_in es r = false.
Proof.
  intros es r Hes Hr. apply Bool.not_true_is_false. intros H. apply errno_ret_in_true in H as (e & HIn & ->).
  rewrite Forall_forall in Hes. specialize (Hes e HIn). rewrite errno_ret_unsigned in Hr by lia. unfold two_pow_64 in Hr. lia.
Qed.

(* [comment removed for export] *)
Lemma grant_exists_mmap_anon : forall len prot mo,
  (0 < len)%Z -> (mmap_len len < 2^64)%Z -> prot = 0%Z \/ prot = 3%Z ->
  (if (prot =? 0)%Z then mmap_reserve_refusable mo (mmap_len len)
   else mmap_grant_refusable (Z_to_bv 64 34) mo (mmap_len len)) = false ->
  exists eff mo' evs, nstep (NMmap 0 len prot 34) mo eff mo' evs
                      /\ node_refusal_b (NMmap 0 len prot 34) mo (eff_ret eff) = false.
Proof.
  intros len prot mo Hlen Hlen2 Hprot Hnr.
  assert (Hb : (len <= mmap_len len)%Z) by (pose proof (mmap_len_bound len Hlen); lia).
  assert (Hgap : vm_gap_available (m_vmmaps mo) (mmap_len len) = true).
  { destruct Hprot as [-> | ->]; cbn [Z.eqb Pos.eqb] in Hnr.
    - unfold mmap_reserve_refusable in Hnr. apply negb_false_iff in Hnr. exact Hnr.
    - unfold mmap_grant_refusable in Hnr. apply orb_false_iff in Hnr as [_ Hnr]. apply negb_false_iff in Hnr. exact Hnr. }
  apply (proj1 (vm_gap_available_iff _ _)) in Hgap. destruct Hgap as (a & Hal & Ha0 & Htop & Hfree).
  pose proof (alloc_top_room (m_vmmaps mo)) as Hroom. unfold stack_max_size, two_pow_64 in Hroom.
  assert (Hsmall : (bv_unsigned a <= 2^64 - 4096)%Z) by lia.
  assert (Herr : errno_ret_in mmap_errnos a = false).
  { apply errno_ret_in_small; [| exact Hsmall]. repeat constructor; unfold ENOMEM; lia. }
  set (n := Z_to_bv 64 (mmap_len len)) in *.
  destruct Hprot as [-> | ->]; cbn [Z.eqb Pos.eqb] in Hnr.
  - exists (mkEffectU a [] [] [(a, n)] [] []). eexists. exists []. split; [| apply node_refusal_mmap_below; exact Hsmall].
    apply nstep_mmap_iff; [reflexivity|]. unfold check_mmap.
    change (mmap_off_aligned_b (Z_to_bv 64 0)) with true. change (mmap_anon_b (Z_to_bv 64 34)) with true. cbn [negb].
    rewrite w_is0_lit by lia. replace (len =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia).
    change (mmap_modeled_b (Z_to_bv 64 0) (Z_to_bv 64 34) (Z_to_bv 64 0)) with false.
    change (mmap_noaccess_b (Z_to_bv 64 0) (Z_to_bv 64 34) (Z_to_bv 64 0)) with true. cbn iota beta.
    rewrite Herr. rewrite unsigned_lit by lia. fold (mmap_len len). fold n. cbv zeta.
    rewrite (proj2 (Z.eqb_eq _ _) Hal), (proj2 (Z.ltb_lt _ _) Ha0), (proj2 (Z.leb_le _ _) Htop), Hfree.
    rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
  - assert (Hbud : mmap_noreserve_backed_ok (Z_to_bv 64 34) mo (mmap_len len) = true).
    { unfold mmap_grant_refusable in Hnr. apply orb_false_iff in Hnr as [Hnr _]. apply negb_false_iff in Hnr. exact Hnr. }
    exists (mkEffectU a [] [(a, n)] [] [] []). eexists. exists []. split; [| apply node_refusal_mmap_below; exact Hsmall].
    apply nstep_mmap_iff; [reflexivity|]. unfold check_mmap.
    change (mmap_off_aligned_b (Z_to_bv 64 0)) with true. change (mmap_anon_b (Z_to_bv 64 34)) with true. cbn [negb].
    rewrite w_is0_lit by lia. replace (len =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia).
    change (mmap_modeled_b (Z_to_bv 64 3) (Z_to_bv 64 34) (Z_to_bv 64 0)) with true. cbn iota beta.
    rewrite Herr. rewrite unsigned_lit by lia. fold (mmap_len len). fold n. cbv zeta.
    rewrite (proj2 (Z.eqb_eq _ _) Hal), (proj2 (Z.ltb_lt _ _) Ha0), (proj2 (Z.leb_le _ _) Htop), Hfree, Hbud.
    rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
Qed.

Lemma node_refusal_mmap_eq : forall addr len prot flags mo r,
  node_refusal_b (NMmap addr len prot flags) mo r = errno_ret_in mmap_errnos r.
Proof.
  intros. unfold node_refusal_b. cbn [node_alloc node_input].
  rewrite refusal_b_mmap by (cbn [pure_input in_sysno]; apply unsigned_lit; lia). reflexivity.
Qed.

Lemma node_refusal_mprotect_eq : forall addr len prot mo r,
  node_refusal_b (NMprotect addr len prot) mo r = errno_ret_in mprotect_errnos r.
Proof.
  intros. unfold node_refusal_b. cbn [node_alloc node_input].
  rewrite refusal_b_mprotect by (cbn [pure_input in_sysno]; apply unsigned_lit; lia). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma nstep_c_mmap_anon_noerr : forall len prot mo rsp mo' evs,
  (0 < len)%Z -> (mmap_len len < 2^64)%Z -> prot = 0%Z \/ prot = 3%Z ->
  (if (prot =? 0)%Z then mmap_reserve_refusable mo (mmap_len len)
   else mmap_grant_refusable (Z_to_bv 64 34) mo (mmap_len len)) = false ->
  nstep_c (NMmap 0 len prot 34) mo rsp mo' evs -> errno_of (eff_ret rsp) = None.
Proof.
  intros len prot mo rsp mo' evs Hlen Hlen2 Hprot Hnr Hc.
  pose proof (nstep_c_grant_only _ _ _ _ _ (grant_exists_mmap_anon len prot mo Hlen Hlen2 Hprot Hnr) Hc) as Hr.
  rewrite node_refusal_mmap_eq in Hr. destruct Hc as [H _].
  assert (Hb : (len <= mmap_len len)%Z) by (pose proof (mmap_len_bound len Hlen); lia).
  apply nstep_mmap_iff in H; [| reflexivity]. destruct rsp as [r ws zs us cs ci]. unfold check_mmap in H.
  change (mmap_off_aligned_b (Z_to_bv 64 0)) with true in H.
  change (mmap_anon_b (Z_to_bv 64 34)) with true in H. cbn [negb] in H.
  rewrite w_is0_lit in H by lia. replace (len =? 0)%Z with false in H by (symmetry; apply Z.eqb_neq; lia).
  rewrite unsigned_lit in H by lia. fold (mmap_len len) in H. cbn [eff_ret] in Hr |- *.
  destruct Hprot as [-> | ->].
  - change (mmap_modeled_b (Z_to_bv 64 0) (Z_to_bv 64 34) (Z_to_bv 64 0)) with false in H.
    change (mmap_noaccess_b (Z_to_bv 64 0) (Z_to_bv 64 34) (Z_to_bv 64 0)) with true in H.
    cbn iota beta in H.
    destruct ws; [|discriminate]. destruct zs; [|destruct us; discriminate].
    destruct cs; [|destruct us; discriminate]. destruct ci; [|destruct us; discriminate].
    rewrite Hr in H. cbv beta iota zeta in H.
    match type of H with (if ?c then _ else _) = _ => destruct c eqn:E; [|discriminate] end.
    apply andb_prop in E as [E _]. apply andb_prop in E as [E _]. apply andb_prop in E as [_ E3].
    apply Z.leb_le in E3. apply errno_of_small. pose proof (alloc_top_room (m_vmmaps mo)).
    unfold stack_max_size, two_pow_64 in *. lia.
  - change (mmap_modeled_b (Z_to_bv 64 3) (Z_to_bv 64 34) (Z_to_bv 64 0)) with true in H.
    cbn iota beta in H.
    destruct ws; [|discriminate]. destruct us; [|destruct zs; discriminate].
    destruct cs; [|destruct zs; discriminate]. destruct ci; [|destruct zs; discriminate].
    rewrite Hr in H. cbv beta iota zeta in H.
    match type of H with (if ?c then _ else _) = _ => destruct c eqn:E; [|discriminate] end.
    apply andb_prop in E as [E _]. apply andb_prop in E as [E _].
    apply andb_prop in E as [E _]. apply andb_prop in E as [_ E3].
    apply Z.leb_le in E3. apply errno_of_small. pose proof (alloc_top_room (m_vmmaps mo)).
    unfold stack_max_size, two_pow_64 in *. lia.
Qed.

(* [comment removed for export] *)
Lemma grant_exists_mprotect_rw : forall addr mo,
  (0 <= addr)%Z -> (addr + 4096 < 2^64)%Z -> (addr mod 4096 = 0)%Z ->
  mprotect_budget_ok mo (Z_to_bv 64 addr) (Z_to_bv 64 4096) = true ->
  mprotect_safe_b (Z_to_bv 64 addr) (Z_to_bv 64 4096) (Z_to_bv 64 3) (m_vmmaps mo) = true ->
  exists eff mo' evs, nstep (NMprotect addr 4096 3) mo eff mo' evs
                      /\ node_refusal_b (NMprotect addr 4096 3) mo (eff_ret eff) = false.
Proof.
  intros addr mo Ha0 Ha1 Hal Hbud Hsafe.
  assert (Hz : node_refusal_b (NMprotect addr 4096 3) mo (Z_to_bv 64 0) = false).
  { apply node_refusal_mprotect_below. rewrite unsigned_lit by lia. lia. }
  assert (Herr : errno_ret_in mprotect_errnos (Z_to_bv 64 0) = false).
  { rewrite <- (node_refusal_mprotect_eq addr 4096 3 mo). exact Hz. }
  unfold mprotect_safe_b in Hsafe.
  destruct (map_contains (vm_noaccess (m_vmmaps mo)) (Z_to_bv 64 addr) (Z_to_bv 64 4096)
            && map_contains (vm_maps (m_vmmaps mo)) (Z_to_bv 64 addr) (Z_to_bv 64 4096)) eqn:Hc.
  - exists (mkEffectU (Z_to_bv 64 0) [] [(Z_to_bv 64 addr, Z_to_bv 64 4096)] [] [] []). eexists. exists [].
    split; [| exact Hz]. apply nstep_mprotect_iff. unfold check_mprotect.
    change (mprotect_grows_conflict_b (Z_to_bv 64 3)) with false. cbv iota.
    rewrite (unsigned_lit addr) by lia. change page_size with 4096%Z. rewrite Hal. cbn [negb Z.eqb].
    rewrite w_is0_lit by lia. change (4096 =? 0)%Z with false. cbv iota.
    rewrite (unsigned_lit 4096) by lia. change (page_round_up_Z 4096) with 4096%Z.
    replace (two_pow_64 <=? addr + 4096)%Z with false by (symmetry; apply Z.leb_gt; unfold two_pow_64; lia).
    change (mprotect_modeled_b (Z_to_bv 64 3)) with true. cbn [negb]. cbv iota zeta.
    rewrite Hc, Herr, Hbud. rewrite w_is0_lit by lia. cbn [Z.eqb andb].
    rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
  - exists (mkEffectU (Z_to_bv 64 0) [] [] [] [] []). eexists. exists [].
    split; [| exact Hz]. apply nstep_mprotect_iff. unfold check_mprotect.
    change (mprotect_grows_conflict_b (Z_to_bv 64 3)) with false. cbv iota.
    rewrite (unsigned_lit addr) by lia. change page_size with 4096%Z. rewrite Hal. cbn [negb Z.eqb].
    rewrite w_is0_lit by lia. change (4096 =? 0)%Z with false. cbv iota.
    rewrite (unsigned_lit 4096) by lia. change (page_round_up_Z 4096) with 4096%Z.
    replace (two_pow_64 <=? addr + 4096)%Z with false by (symmetry; apply Z.leb_gt; unfold two_pow_64; lia).
    change (mprotect_modeled_b (Z_to_bv 64 3)) with true. cbn [negb]. cbv iota zeta.
    rewrite Hc.
    unfold mprotect_safe_b in Hsafe. change (mprotect_grows_conflict_b (Z_to_bv 64 3)) with false in Hsafe. cbv iota in Hsafe.
    rewrite (unsigned_lit addr) in Hsafe by lia. change page_size with 4096%Z in Hsafe. rewrite Hal in Hsafe. cbn [negb Z.eqb] in Hsafe.
    rewrite w_is0_lit in Hsafe by lia. change (4096 =? 0)%Z with false in Hsafe. cbv iota in Hsafe.
    rewrite (unsigned_lit 4096) in Hsafe by lia. change (page_round_up_Z 4096) with 4096%Z in Hsafe.
    replace (two_pow_64 <=? addr + 4096)%Z with false in Hsafe by (symmetry; apply Z.leb_gt; unfold two_pow_64; lia).
    change (mprotect_modeled_b (Z_to_bv 64 3)) with true in Hsafe. cbv iota zeta in Hsafe.
    rewrite Hc in Hsafe. cbn [orb] in Hsafe. rewrite Hsafe. rewrite w_is0_lit by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma nstep_c_mprotect_noerr : forall addr mo rsp mo' evs,
  (0 <= addr)%Z -> (addr + 4096 < 2^64)%Z -> (addr mod 4096 = 0)%Z ->
  mprotect_budget_ok mo (Z_to_bv 64 addr) (Z_to_bv 64 4096) = true ->
  mprotect_safe_b (Z_to_bv 64 addr) (Z_to_bv 64 4096) (Z_to_bv 64 3) (m_vmmaps mo) = true ->
  nstep_c (NMprotect addr 4096 3) mo rsp mo' evs -> errno_of (eff_ret rsp) = None.
Proof.
  intros addr mo rsp mo' evs Ha0 Ha1 Hal Hbud Hsafe Hc.
  pose proof (nstep_c_grant_only _ _ _ _ _ (grant_exists_mprotect_rw addr mo Ha0 Ha1 Hal Hbud Hsafe) Hc) as Hr.
  rewrite node_refusal_mprotect_eq in Hr. destruct Hc as [H _].
  apply nstep_mprotect_iff in H. destruct rsp as [r ws zs us cs ci]. unfold check_mprotect in H. cbn [eff_ret] in Hr |- *.
  change (mprotect_grows_conflict_b (Z_to_bv 64 3)) with false in H.
  rewrite (unsigned_lit addr) in H by lia. change page_size with 4096%Z in H.
  rewrite Hal in H. cbn [negb Z.eqb] in H.
  rewrite w_is0_lit in H by lia. change (4096 =? 0)%Z with false in H.
  rewrite (unsigned_lit 4096) in H by lia. change (page_round_up_Z 4096) with 4096%Z in H.
  replace (two_pow_64 <=? addr + 4096)%Z with false in H by (symmetry; apply Z.leb_gt; unfold two_pow_64; lia).
  change (mprotect_modeled_b (Z_to_bv 64 3)) with true in H. cbn [negb] in H. cbv iota zeta in H.
  destruct (map_contains _ _ _ && map_contains _ _ _) eqn:Hcc.
  - destruct ws; [|discriminate]. destruct us; [|destruct zs; discriminate].
    destruct cs; [|destruct zs; discriminate]. destruct ci; [|destruct zs; discriminate].
    rewrite Hr in H. cbv beta iota in H.
    match type of H with context [if ?c then _ else _] => destruct c eqn:E; [|discriminate] end.
    apply andb_prop in E as [E _]. apply andb_prop in E as [_ E]. unfold w_is0 in E. apply bv_eqb_eq in E. subst r.
    apply errno_of_lit. lia.
  - match type of H with context [if ?c then _ else _] => destruct c eqn:E0; [|discriminate] end.
    destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate].
    destruct cs; [|discriminate]. destruct ci; [|discriminate].
    cbv beta iota in H.
    match type of H with context [if ?c then _ else _] => destruct c eqn:E; [|discriminate] end.
    unfold w_is0 in E. apply bv_eqb_eq in E. subst r.
    apply errno_of_lit. lia.
Qed.

(* [comment removed for export] *)
Lemma grant_exists_mmap_fixed_none : forall a mo,
  let h := m_vmmaps mo in let aw := Z_to_bv 64 a in let n := Z_to_bv 64 4096 in
  (0 < a)%Z -> (a + 4096 <= alloc_top h)%Z -> (a mod 4096 = 0)%Z ->
  region_free (vm_reserved h) aw n = true -> map_contains (vm_maps h) aw n = true ->
  exists eff mo' evs, nstep (NMmap a 4096 0 50) mo eff mo' evs
                      /\ node_refusal_b (NMmap a 4096 0 50) mo (eff_ret eff) = false.
Proof.
  intros a mo h aw n Ha Htop Hal Hrf Hmc.
  pose proof (alloc_top_room h) as Hroom. unfold stack_max_size, two_pow_64 in Hroom.
  assert (Haw : bv_unsigned aw = a) by (subst aw; apply unsigned_lit; lia).
  assert (Hsmall : (bv_unsigned aw <= 2^64 - 4096)%Z) by lia.
  assert (Herr : errno_ret_in mmap_errnos aw = false).
  { apply errno_ret_in_small; [| exact Hsmall]. repeat constructor; unfold ENOMEM; lia. }
  exists (mkEffectU aw [] [] [(aw, n)] [] []). eexists. exists []. split; [| apply node_refusal_mmap_below; exact Hsmall].
  apply Nodes.nstep_mmap_iff; [reflexivity|]. unfold check_mmap.
  change (mmap_off_aligned_b (Z_to_bv 64 0)) with true. change (mmap_anon_b (Z_to_bv 64 50)) with true. cbn [negb].
  rewrite w_is0_lit by lia. change (4096 =? 0)%Z with false.
  change (mmap_modeled_b (Z_to_bv 64 0) (Z_to_bv 64 50) (Z_to_bv 64 0)) with false.
  change (mmap_noaccess_b (Z_to_bv 64 0) (Z_to_bv 64 50) (Z_to_bv 64 0)) with false.
  change (mmap_fixed_noaccess_b (Z_to_bv 64 0) (Z_to_bv 64 50) (Z_to_bv 64 0)) with true.
  cbv iota beta. fold aw h. rewrite (unsigned_lit 4096) by lia. change (page_round_up_Z 4096) with 4096%Z. fold n.
  rewrite Haw.
  replace (two_pow_64 <=? a + 4096)%Z with false by (symmetry; apply Z.leb_gt; unfold two_pow_64; lia).
  replace (a + 4096 <=? alloc_top h)%Z with true by (symmetry; apply Z.leb_le; lia). cbn [negb].
  change page_size with 4096%Z. rewrite Hal. replace (0 <? a)%Z with true by (symmetry; apply Z.ltb_lt; lia).
  cbn [Z.eqb negb]. cbv zeta. fold n. rewrite Hrf, Hmc. cbn [andb].
  rewrite Herr, bv_eqb_refl. rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma nstep_brk_iff : forall req mo eff mo' evs,
  nstep_c (NBrk req) mo eff mo' evs -> check_brk (Z_to_bv 64 req) eff mo = CheckOk mo' evs.
Proof. intros req mo eff mo' evs H. apply Nodes.nstep_brk_iff. exact (nstep_c_nstep _ _ _ _ _ H). Qed.

Lemma nstep_mmap_iff : forall addr len prot flags mo eff mo' evs,
  mmap_noreserve_b (Z_to_bv 64 flags) = false ->
  nstep_c (NMmap addr len prot flags) mo eff mo' evs ->
  check_mmap (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) (Z_to_bv 64 flags)
             (Z_to_bv 64 (-1)) (Z_to_bv 64 0) eff mo = CheckOk mo' evs.
Proof. intros addr len prot flags mo eff mo' evs Hnr H. apply Nodes.nstep_mmap_iff; [exact Hnr|]. exact (nstep_c_nstep _ _ _ _ _ H). Qed.

Lemma nstep_munmap_iff : forall addr len mo eff mo' evs,
  nstep_c (NMunmap addr len) mo eff mo' evs ->
  check_munmap (Z_to_bv 64 addr) (Z_to_bv 64 len) eff mo = CheckOk mo' evs.
Proof. intros addr len mo eff mo' evs H. apply Nodes.nstep_munmap_iff. exact (nstep_c_nstep _ _ _ _ _ H). Qed.

Lemma nstep_mprotect_iff : forall addr len prot mo eff mo' evs,
  nstep_c (NMprotect addr len prot) mo eff mo' evs ->
  check_mprotect (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) eff mo = CheckOk mo' evs.
Proof. intros addr len prot mo eff mo' evs H. apply Nodes.nstep_mprotect_iff. exact (nstep_c_nstep _ _ _ _ _ H). Qed.

End WithCeiling.
