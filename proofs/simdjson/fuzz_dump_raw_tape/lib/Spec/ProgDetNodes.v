(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs Progress.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import DispatchCompute.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import PropExec MState Mem ITree Nodes Decode.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Spec Require Import Prelim Monad Stdio Prog Canon ProgDetIface ProgDetLogic.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Definition is_mm (n : node) : Prop :=
  match n with NBrk _ | NMmap _ _ _ _ | NMunmap _ _ | NMprotect _ _ _ => True | _ => False end.

Lemma check_brk_not_unmodeled : forall req eff mo, check_brk req eff mo <> CheckUnmodeled.
Proof.
  intros req [r ws zs us cs ci] mo. unfold check_brk. destruct ws; [|discriminate]. destruct cs; [|discriminate].
  destruct ci; [|discriminate]. destruct (_ && _); discriminate.
Qed.

Lemma nstep_mm_progress : forall n mo, is_mm n -> nsafe n mo -> no_enomem n mo -> exists rsp mo' evs, nstep n mo rsp mo' evs.
Proof.
  intros n mo Kind Safe Budget.
  pose proof (no_enomem_unforced n mo Budget) as Forced.
  assert (Answerable : forall i (chk : resp -> check_result),
            (forall e, check_syscall i e mo = chk e) -> (forall e, chk e <> CheckUnmodeled) ->
            exists e m1 v1, chk e = CheckOk m1 v1 /\ ~ spurious_refusal_cfg ACFG i mo e).
  { intros i chk Agree Modeled.
    destruct (receptive_ex i mo) as [[e0 m0 v0|] Outcome].
    - destruct (exists_nonspurious ACFG i mo e0 m0 v0 Outcome) as (e1 & m1 & v1 & Granted & Fair).
      exists e1, m1, v1. split; [|exact Fair].
      rewrite <- Agree. apply check_syscall_ok_iff. exact Granted.
    - exfalso. apply (Modeled (eff0 (Z_to_bv 64 0))). rewrite <- Agree.
      apply check_syscall_complete_unmodeled. exact Outcome. }
  destruct n as [| | | | | | |req|addr len prot flags|addr len|addr len prot]; cbn [is_mm] in Kind; try contradiction.
  4: exact Forced.
  - assert (Agree : forall e, check_syscall (pure_input 214 [Z_to_bv 64 req]) e mo = check_brk (Z_to_bv 64 req) e mo).
    { intros e. rewrite check_syscall_brk by reflexivity. reflexivity. }
    destruct (Answerable _ (fun e => check_brk (Z_to_bv 64 req) e mo) Agree (fun e => check_brk_not_unmodeled _ e mo))
      as (e1 & m1 & v1 & Checked & Fair).
    exists e1, m1, v1. apply nstep_brk_iff. exact (conj Checked Fair).
  - destruct (kernel_placed flags) eqn:Placement; [exact (Forced Placement)|].
    cbn [nsafe] in Safe.
    assert (Agree : forall e,
              check_syscall (pure_input 222 [Z_to_bv 64 addr; Z_to_bv 64 len; Z_to_bv 64 prot; Z_to_bv 64 flags;
                                            Z_to_bv 64 (-1); Z_to_bv 64 0]) e mo
              = check_mmap (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) (Z_to_bv 64 flags)
                           (Z_to_bv 64 (-1)) (Z_to_bv 64 0) e mo).
    { intros e. rewrite check_syscall_mmap by reflexivity. reflexivity. }
    destruct (Answerable _ _ Agree (fun e => mmap_safe_no_unmodeled _ _ _ _ _ _ e mo Safe))
      as (e1 & m1 & v1 & Checked & Fair).
    exists e1, m1, v1.
    apply (nstep_mmap_iff addr len prot flags mo e1 m1 v1 (mmap_safe_noreserve _ _ _ _ _ _ _ Safe)).
    split; [exact Checked|]. cbn [mm_ok]. rewrite Placement. exact Fair.
  - cbn [nsafe] in Safe.
    assert (Agree : forall e,
              check_syscall (pure_input 215 [Z_to_bv 64 addr; Z_to_bv 64 len]) e mo
              = check_munmap (Z_to_bv 64 addr) (Z_to_bv 64 len) e mo).
    { intros e. rewrite check_syscall_munmap by reflexivity. reflexivity. }
    destruct (Answerable _ _ Agree (fun e => munmap_safe_no_unmodeled _ _ e mo Safe)) as (e1 & m1 & v1 & Checked & _).
    exists e1, m1, v1. apply nstep_munmap_iff. exact Checked.
Qed.

Lemma osel_not_open : forall sel n mo rsp, match n with NOpen _ => False | _ => True end -> osel sel n mo rsp.
Proof. intros sel n mo rsp Hn. destruct sel; [destruct n; first [exact I| contradiction]| exact I]. Qed.

Lemma stepR_intro : forall sel n mo rsp mo' evs,
  match n with NOpen _ => False | _ => True end -> Pn n mo -> nstep n mo rsp mo' evs -> stepR sel n mo rsp mo' evs.
Proof. intros. split; [assumption|]. split; [assumption|]. apply osel_not_open. assumption. Qed.

Lemma nprog_of_nstep : forall sel n mo,
  match n with NOpen _ => False | _ => True end -> (exists rsp mo' evs, nstep n mo rsp mo' evs) -> nprog sel n mo.
Proof.
  intros sel n mo Hn (rsp & mo' & evs & Hst) HP. left. exists rsp, mo', evs. apply stepR_intro; assumption.
Qed.

Lemma nprog_mm : forall sel n mo, is_mm n -> nprog sel n mo.
Proof.
  intros sel n mo Hn HP. apply (nprog_of_nstep sel n mo); [destruct n; first [exact I| contradiction]| |exact HP].
  apply nstep_mm_progress; [exact Hn| exact (proj1 HP)| exact (proj1 (proj2 HP))].
Qed.

Lemma nprog_writev : forall sel fd bufs mo, nprog sel (NWritev fd bufs) mo.
Proof.
  intros sel fd bufs mo. apply nprog_of_nstep; [exact I|].
  destruct (concat bufs) as [|b bs] eqn:E.
  - exists (eff0 (Z_to_bv 64 0)), mo, []. cbn [nstep]. split; [reflexivity|]. left. rewrite E. auto.
  - exists (eff0 (Z_to_bv 64 (Z.of_nat (length (b :: bs))))), mo, (map (WriteEv (Z_to_bv 64 fd)) (b :: bs)).
    cbn [nstep]. split; [reflexivity|]. right. rewrite E. exists (length (b :: bs)).
    split; [cbn; lia|]. split; [reflexivity|]. rewrite firstn_all. reflexivity.
Qed.

Lemma nprog_set_tid : forall sel mo, nprog sel NSetTid mo.
Proof.
  intros sel mo. apply nprog_of_nstep; [exact I|].
  destruct (m_tid mo) as [t0|] eqn:E.
  - exists (eff0 t0), mo, []. cbn [nstep]. split; [reflexivity|]. exists t0. rewrite E. auto.
  - exists (eff0 (Z_to_bv 64 1)), (with_tid (Z_to_bv 64 1) mo), []. cbn [nstep]. split; [reflexivity|].
    exists (Z_to_bv 64 1). rewrite E. split; [reflexivity|]. split; [|reflexivity].
    rewrite unsigned_lit by lia. unfold PID_MAX_ENVELOPE. lia.
Qed.

Lemma nprog_ioctl : forall sel fd req mo, nprog sel (NIoctl fd req) mo.
Proof. intros. apply nprog_of_nstep; [exact I|]. exists (efferr ENOTTY), mo, []. cbn [nstep]. auto. Qed.

Lemma nprog_close : forall sel fd mo, 3 <= fd < 2^32 -> nprog sel (NClose fd) mo.
Proof.
  intros sel fd mo Hfd. apply nprog_of_nstep; [exact I|].
  destruct (fd_lookup (m_fds mo) (Z_to_bv 64 fd)) eqn:E.
  - exists (eff0 (Z_to_bv 64 0)), (with_fds (fd_remove (m_fds mo) (Z_to_bv 64 fd)) mo), []. cbn [nstep]. rewrite E. auto.
  - exists (efferr EBADF), mo, []. cbn [nstep]. rewrite E. auto.
Qed.

Lemma nprog_read : forall sel fd buf cnt mo,
  match fd_lookup (m_fds mo) (Z_to_bv 64 fd) with
  | None | Some FdDir => True
  | Some (FdFile p _) => fs_lookup (m_fs mo) p <> None
  | Some _ => False
  end -> nprog sel (NRead fd buf cnt) mo.
Proof.
  intros sel fd buf cnt mo Hfd. apply nprog_of_nstep; [exact I|].
  destruct (fd_lookup (m_fds mo) (Z_to_bv 64 fd)) as [[ch|p off|p off|p off|p off| |sk|pi pw|rd wr| ]|] eqn:E; try contradiction.
  - destruct (fs_lookup (m_fs mo) p) as [data|] eqn:Hfs; [|contradiction].
    eexists _, _, []. cbn [nstep]. rewrite E, Hfs. split; [reflexivity|]. split; reflexivity.
  - exists (efferr EISDIR), mo, []. cbn [nstep]. rewrite E. auto.
  - exists (efferr EBADF), mo, []. cbn [nstep]. rewrite E. auto.
Qed.

Lemma nprog_exit : forall sel c mo, nprog sel (NExit c) mo.
Proof. intros sel c mo _. right. exists (exit_code c), (with_halted (exit_code c) mo). split; reflexivity. Qed.

Lemma errno_of_efferr : forall e, 1 <= e <= 4095 -> errno_of (eff_ret (efferr e)) = Some e.
Proof. intros e He. unfold efferr, eff0. cbn [eff_ret]. apply errno_of_errno_ret. exact He. Qed.

Lemma nstep_open_err : forall p mo, exists e, 1 <= e <= 4095 /\ nstep (NOpen p) mo (efferr e) mo [].
Proof.
  intros p mo. cbn [nstep].
  destruct (path_max <=? length p)%nat. { exists ENAMETOOLONG. unfold ENAMETOOLONG. split; [lia|]. auto. }
  destruct p as [|c p']. { exists ENOENT. unfold ENOENT. split; [lia|]. auto. }
  assert (Hor : forall ent, open_result mo ent (efferr ENOMEM) mo).
  { intros ent. left. exists ENOMEM. split; [cbn; auto| auto]. }
  destruct (path_eqb (c :: p') dot_path).
  - exists ENOMEM. unfold ENOMEM. split; [lia|]. split; [reflexivity| apply Hor].
  - destruct (fs_lookup (m_fs mo) (c :: p')).
    + exists ENOMEM. unfold ENOMEM. split; [lia|]. split; [reflexivity| apply Hor].
    + exists ENOENT. unfold ENOENT. split; [lia|]. auto.
Qed.

Lemma nstep_open_ok : forall p mo, minv mo -> open_admits p mo = true ->
  exists rsp mo', errno_of (eff_ret rsp) = None /\ nstep (NOpen p) mo rsp mo' [].
Proof.
  intros p mo Hmi Hadm. unfold open_admits, openable_b, fd_free_b in Hadm. apply andb_prop in Hadm as [Hop Hfree].
  destruct (fd_lookup (m_fds mo) (alloc_fd (m_fds mo))) eqn:Hlk; [discriminate|].
  pose proof (alloc_fd_range mo Hmi Hlk) as Hr.
  assert (Hor : forall ent, open_result mo ent (eff0 (alloc_fd (m_fds mo))) (with_fds (fd_insert (m_fds mo) (alloc_fd (m_fds mo)) ent) mo)).
  { intros ent. right. cbv zeta. auto. }
  assert (He : errno_of (eff_ret (eff0 (alloc_fd (m_fds mo)))) = None).
  { cbn [eff_ret eff0]. apply errno_of_small. lia. }
  cbn [nstep]. destruct (path_max <=? length p)%nat; [discriminate|].
  destruct p as [|c p']; [discriminate|].
  destruct (path_eqb (c :: p') dot_path).
  - eexists _, _. split; [exact He|]. split; [reflexivity| apply Hor].
  - destruct (fs_lookup (m_fs mo) (c :: p')); [|discriminate].
    eexists _, _. split; [exact He|]. split; [reflexivity| apply Hor].
Qed.

Lemma nprog_open : forall sel p mo, nprog sel (NOpen p) mo.
Proof.
  intros sel p mo HP. left. destruct HP as (Hs & Hne & Hmi & Hh).
  assert (Herr : exists rsp mo' evs, nstep (NOpen p) mo rsp mo' evs /\ errno_of (eff_ret rsp) <> None).
  { destruct (nstep_open_err p mo) as (e & He & Hst). exists (efferr e), mo, []. split; [exact Hst|].
    rewrite errno_of_efferr by exact He. discriminate. }
  destruct sel as [b|].
  - destruct (b && open_admits p mo) eqn:E.
    + assert (E2 : open_admits p mo = true) by (apply andb_prop in E; tauto).
      destruct (nstep_open_ok p mo Hmi E2) as (rsp & mo' & He & Hst).
      exists rsp, mo', []. split; [split; [exact Hs| split; [exact Hne| split; assumption]]|]. split; [exact Hst|].
      cbn [osel]. rewrite E. exact He.
    + destruct Herr as (rsp & mo' & evs & Hst & He). exists rsp, mo', evs.
      split; [split; [exact Hs| split; [exact Hne| split; assumption]]|]. split; [exact Hst|].
      cbn [osel]. rewrite E. exact He.
  - destruct Herr as (rsp & mo' & evs & Hst & He). exists rsp, mo', evs.
    split; [split; [exact Hs| split; [exact Hne| split; assumption]]|]. split; [exact Hst| exact I].
Qed.

Lemma msysE_node {St A} sel X n (dec : resp -> option A) (P : assnE St) (Q : A -> assnE St) :
  match n with NExit _ => False | _ => True end ->
  (forall s mo tr, P s mo tr -> nprog sel n mo) ->
  (forall s mo tr rsp mo' evs a, P s mo tr -> stepR sel n mo rsp mo' evs -> dec rsp = Some a -> Q a s mo' (tr ++ evs)) ->
  mspecE sel X P (msys n dec) Q.
Proof.
  intros Hn Hp Hk. apply mspecE_sys. intros s mo tr HP. split; [exact (Hp _ _ _ HP)|]. split.
  - intros code mo' Hex. destruct n; try contradiction; destruct Hex.
  - intros rsp mo' evs a Hst Hd. exact (Hk s mo tr rsp mo' evs a HP Hst Hd).
Qed.

Lemma msysE_exit {St A} sel X c (P : assnE St) (Q : A -> assnE St) :
  (forall s mo tr, P s mo tr -> X (tr ++ [ExitEv (exit_code c) (m_fs mo)])) ->
  mspecE sel X P (msys (NExit c) (fun _ => @None A)) Q.
Proof.
  intros H. apply mspecE_sys. intros s mo tr HP. split; [apply nprog_exit|]. split.
  - intros code mo' (-> & ->). rewrite m_fs_with_halted. exact (H s mo tr HP).
  - intros rsp mo' evs a _ Hd. discriminate Hd.
Qed.

Lemma stepR_mm : forall sel n mo rsp mo' evs, is_mm n -> stepR sel n mo rsp mo' evs ->
  evs = [] /\ m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo /\ ans_ok n rsp.
Proof.
  intros sel n mo rsp mo' evs Hn Hst. pose proof (stepR_ans_ok _ _ _ _ _ _ Hst) as Hok.
  destruct Hst as ((Hs & _) & Hst & _).
  assert (Hn' : match n with NBrk _ | NMunmap _ _ | NMprotect _ _ _ => True
             | NMmap _ _ _ flags => mmap_noreserve_b (Z_to_bv 64 flags) = false | _ => False end).
  { destruct n; try exact I; try contradiction. cbn [nsafe] in Hs. eapply mmap_safe_noreserve. exact Hs. }
  destruct (nstep_mm_vm_only n mo rsp mo' evs Hn' Hst) as ((Hfd & Hfs & _) & -> & _). auto.
Qed.

Lemma concat_to_bytes : forall iovs, concat (map to_bytes iovs) = to_bytes (concat iovs).
Proof. intros. unfold to_bytes. rewrite concat_map. reflexivity. Qed.

Lemma evw_to_bytes : forall fd l, map (WriteEv (Z_to_bv 64 fd)) (to_bytes l) = evw fd l.
Proof. intros. unfold to_bytes, evw. rewrite map_map. reflexivity. Qed.

Lemma length_concat_to_bytes : forall iovs, length (concat (map to_bytes iovs)) = length (concat iovs).
Proof. intros. rewrite concat_to_bytes. unfold to_bytes. apply length_map. Qed.

Lemma stepR_writev : forall sel fd iovs mo rsp mo' evs k,
  zlength (concat iovs) < 2^64 ->
  stepR sel (NWritev fd (map to_bytes iovs)) mo rsp mo' evs -> dec_writev (iov_total iovs) rsp = Some k ->
  mo' = mo /\ ((iov_total iovs = 0 /\ k = 0) \/ (1 <= k <= iov_total iovs))
  /\ evs = evw fd (firstn (Z.to_nat k) (concat iovs)).
Proof.
  intros sel fd iovs mo rsp mo' evs k Hl (_ & Hst & _) Hd.
  assert (Hl' : Z.of_nat (length (concat (map to_bytes iovs))) < 2^64).
  { rewrite length_concat_to_bytes. exact Hl. }
  destruct (nstep_dec_writev fd _ mo rsp mo' evs Hl' Hst) as (-> & k0 & Hd0 & Hk0 & Hz & ->).
  rewrite length_concat_to_bytes in Hd0. change (Z.of_nat (length (concat iovs))) with (iov_total iovs) in Hd0.
  rewrite Hd in Hd0. injection Hd0 as ->. split; [reflexivity|].
  rewrite length_concat_to_bytes in Hk0.
  split.
  - unfold iov_total, zlength in *. destruct (Nat.eq_dec k0 0) as [->|NE].
    + left. split; [|reflexivity]. destruct Hz as [Hz _]. specialize (Hz eq_refl).
      rewrite concat_to_bytes in Hz. unfold to_bytes in Hz. apply map_eq_nil in Hz. rewrite Hz. reflexivity.
    + right. lia.
  - rewrite Nat2Z.id. rewrite concat_to_bytes. unfold to_bytes at 1. rewrite firstn_map. apply evw_to_bytes.
Qed.

Lemma stepR_ioctl : forall sel fd req mo rsp mo' evs a,
  stepR sel (NIoctl fd req) mo rsp mo' evs -> dec_ioctl rsp = Some a -> a = SErr ENOTTY /\ mo' = mo /\ evs = [].
Proof.
  intros sel fd req mo rsp mo' evs a (_ & Hst & _) Hd.
  destruct (nstep_dec_ioctl fd req mo rsp mo' evs Hst) as (Hd' & -> & ->). rewrite Hd in Hd'. injection Hd' as ->. auto.
Qed.

Lemma stepR_set_tid : forall sel mo rsp mo' evs,
  stepR sel NSetTid mo rsp mo' evs -> evs = [] /\ m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo.
Proof.
  intros sel mo rsp mo' evs (_ & (-> & t & _ & H) & _). split; [reflexivity|].
  destruct (m_tid mo); destruct H as [_ ->]; [auto|]. rewrite m_fds_with_tid, m_fs_with_tid. auto.
Qed.

Lemma stepR_close : forall sel fd mo rsp mo' evs,
  stepR sel (NClose fd) mo rsp mo' evs -> evs = [] /\ m_fs mo' = m_fs mo.
Proof.
  intros sel fd mo rsp mo' evs (_ & (-> & _ & H) & _). split; [reflexivity|].
  destruct (fd_lookup _ _); destruct H as [_ ->]; [|reflexivity]. apply m_fs_with_fds.
Qed.

Lemma stepR_read_file : forall sel fd buf cnt mo rsp mo' evs a p off data,
  0 <= cnt < 2^64 ->
  fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some (FdFile p off) -> fs_lookup (m_fs mo) p = Some data ->
  stepR sel (NRead fd buf cnt) mo rsp mo' evs -> dec_read buf cnt rsp = Some a ->
  evs = [] /\ a = RdData (file_read data off (Z_to_bv 64 cnt))
  /\ mo' = with_fds (fd_insert (m_fds mo) (Z_to_bv 64 fd) (FdFile p (off + len_word (file_read data off (Z_to_bv 64 cnt)))%bv)) mo.
Proof.
  intros sel fd buf cnt mo rsp mo' evs a p off data Hc Hlk Hfs (_ & Hst & _) Hd.
  destruct (nstep_dec_read fd buf cnt mo rsp mo' evs Hc Hst) as (-> & a' & Hd' & Ha). rewrite Hd in Hd'. injection Hd' as <-.
  split; [reflexivity|]. destruct a as [e|bs].
  - destruct Ha as (_ & [(_ & H)|(_ & H)]); congruence.
  - destruct Ha as (p' & off' & data' & Hlk' & Hfs' & -> & ->). rewrite Hlk in Hlk'. injection Hlk' as <- <-.
    rewrite Hfs in Hfs'. injection Hfs' as <-. auto.
Qed.

Lemma stepR_read_dir : forall sel fd buf cnt mo rsp mo' evs a,
  0 <= cnt < 2^64 -> fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some FdDir ->
  stepR sel (NRead fd buf cnt) mo rsp mo' evs -> dec_read buf cnt rsp = Some a ->
  evs = [] /\ mo' = mo /\ exists e, a = RdErr e.
Proof.
  intros sel fd buf cnt mo rsp mo' evs a Hc Hlk (_ & Hst & _) Hd.
  destruct (nstep_dec_read fd buf cnt mo rsp mo' evs Hc Hst) as (-> & a' & Hd' & Ha). rewrite Hd in Hd'. injection Hd' as <-.
  split; [reflexivity|]. destruct a as [e|bs].
  - destruct Ha as (-> & _). split; [reflexivity| eauto].
  - destruct Ha as (p' & off' & data' & Hlk' & _). congruence.
Qed.

Lemma nstep_open_success : forall p mo rsp mo' evs,
  nstep (NOpen p) mo rsp mo' evs -> errno_of (eff_ret rsp) = None ->
  openable_b p (m_fs mo) = true /\ rsp = eff0 (alloc_fd (m_fds mo))
  /\ mo' = with_fds (fd_insert (m_fds mo) (alloc_fd (m_fds mo)) (if path_eqb p dot_path then FdDir else FdFile p (Z_to_bv 64 0))) mo.
Proof.
  intros p mo rsp mo' evs [_ Hst] Hne.
  assert (Herr : forall e, 1 <= e <= 4095 -> rsp = efferr e -> False).
  { intros e He ->. rewrite errno_of_efferr in Hne by exact He. discriminate. }
  assert (Hres : forall ent, open_result mo ent rsp mo' ->
            rsp = eff0 (alloc_fd (m_fds mo)) /\ mo' = with_fds (fd_insert (m_fds mo) (alloc_fd (m_fds mo)) ent) mo).
  { intros ent [(e & HIn & -> & _)|(_ & -> & ->)]; [|auto]. exfalso. apply (Herr e); [apply openat_errnos_range; exact HIn| reflexivity]. }
  unfold openable_b. destruct (path_max <=? length p)%nat.
  { exfalso. destruct Hst as [He _]. apply (Herr ENAMETOOLONG); [unfold ENAMETOOLONG; lia| exact He]. }
  destruct p as [|c p'].
  { exfalso. destruct Hst as [He _]. apply (Herr ENOENT); [unfold ENOENT; lia| exact He]. }
  destruct (path_eqb (c :: p') dot_path).
  - destruct (Hres _ Hst) as [-> ->]. auto.
  - destruct (fs_lookup (m_fs mo) (c :: p')).
    + destruct (Hres _ Hst) as [-> ->]. auto.
    + exfalso. destruct Hst as [He _]. apply (Herr ENOENT); [unfold ENOENT; lia| exact He].
Qed.

Lemma stepR_open : forall sel p mo rsp mo' evs a,
  stepR sel (NOpen p) mo rsp mo' evs -> dec_open rsp = Some a ->
  evs = [] /\
  match a with
  | SErr _ => mo' = mo /\ (forall b, sel = Some b -> b && open_admits p mo = false)
  | SVal v => Z_to_bv 64 v = alloc_fd (m_fds mo) /\ 3 <= v <= 4096 /\ openable_b p (m_fs mo) = true
      /\ (forall b, sel = Some b -> b = true /\ open_admits p mo = true)
      /\ mo' = with_fds (fd_insert (m_fds mo) (Z_to_bv 64 v) (if path_eqb p dot_path then FdDir else FdFile p (Z_to_bv 64 0))) mo
  end.
Proof.
  intros sel p mo rsp mo' evs a ((_ & _ & Hmi & _) & Hst & Hsel) Hd.
  destruct (nstep_dec_open p mo rsp mo' evs Hmi Hst) as (-> & a' & Hd' & Ha). rewrite Hd in Hd'. injection Hd' as <-.
  split; [reflexivity|].
  pose proof (dec_plain_Some _ _ _ Hd) as Hrsp.
  destruct a as [e|v].
  - destruct Ha as (-> & He). split; [reflexivity|]. intros b ->. cbn [osel] in Hsel.
    destruct (b && open_admits p mo); [|reflexivity]. exfalso. destruct Hrsp as (-> & _).
    rewrite errno_of_efferr in Hsel by exact He. discriminate.
  - destruct Ha as (Hfd & Hv & _). destruct Hrsp as (-> & _ & Hv').
    assert (Hne : errno_of (eff_ret (eff0 (Z_to_bv 64 v))) = None) by (cbn [eff_ret eff0]; apply errno_of_lit; lia).
    destruct (nstep_open_success p mo _ mo' [] Hst Hne) as (Hop & _ & ->).
    rewrite <- Hfd. split; [reflexivity|]. split; [exact Hv|]. split; [exact Hop|]. split; [|reflexivity].
    intros b ->. cbn [osel] in Hsel. destruct (b && open_admits p mo) eqn:E.
    + apply andb_prop in E. exact E.
    + exfalso. apply Hsel. exact Hne.
Qed.
