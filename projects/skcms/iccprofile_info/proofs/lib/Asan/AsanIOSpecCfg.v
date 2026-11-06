(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Syscall Uaccess.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Open.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Prelude.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import
  SimInv ExitSim PropExec CatExec CatSim SeqExec StreamExec MmapSim AllocSim FileSim
  ShapeAlg SpinAlg Nodes StoreOk AgentLib AgentNodes RefNodes AsanAcct AsanAcctShape AsanNodesLibE.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import AsanAcctNoLazy.   (* [comment removed for export] *)
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import SpinAlgCfg AsanNodesLibCfg.
Unset Nia Cache.  (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache.

(* [comment removed for export] *)
Lemma materialize_above_lazy : forall m (top : Z) ranges,
  Forall (fun iv => (bv_unsigned (fst iv) + bv_unsigned (snd iv) <= top)%Z) (m_vm_lazy m) ->
  Forall (fun r => (top + 4096 <= bv_unsigned (fst r))%Z /\ (bv_unsigned (fst r) + Z.of_nat (snd r) <= 2 ^ 64)%Z) ranges ->
  materialize_model_accesses m ranges = Some m.
Proof.
  intros m top ranges Hlazy Hr.
  apply (materialize_nolazy (lazyH m) m ranges (lazy_all_hidden_lazyH m)).
  induction ranges as [|[a n] rest IH]; [apply ranges_avoid_nil|].
  apply Forall_cons_iff in Hr as [[Ha Hn] Hrest]. cbn [fst snd] in Ha, Hn.
  apply ranges_avoid_cons; [|exact (IH Hrest)].
  pose proof (u64_range a) as Hra.
  replace a with (Z_to_bv 64 (bv_unsigned a)) by (apply bv_eq; rewrite u64_lit by lia; reflexivity).
  apply range_avoids_by_addr; [lia | lia |].
  intros z Hz. unfold lazyH, mkH in Hz. apply andb_prop in Hz as [Hz _].
  unfold page_in_ranges in Hz. apply existsb_exists in Hz as [iv [Hin Hb]].
  pose proof (proj1 (Forall_forall _ _) Hlazy iv Hin) as Hiv. cbv beta in Hiv.
  apply andb_prop in Hb as [_ Hb]. apply Z.leb_le in Hb.
  pose proof (u64_range z) as Hz64.
  unfold page_base, page_base_of, page_size in Hb.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  rewrite u64_lit in Hb by lia. lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section WithSegs.
Context {FP : PropExec.FPState}.
Variable segs : list Segment.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma node_chk_ev_mat_gen : forall ms model x8 (I : Type)
    (effs : I -> SyscallEffect) (ms' ms'' : I -> Model) (evs : I -> list event),
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  (forall i, check_syscall (sys_input segs ms x8) (effs i) model = CheckOk (ms' i) (evs i)) ->
  (forall eff m' ev, check_syscall (sys_input segs ms x8) eff model = CheckOk m' ev ->
     exists i, eff = effs i /\ m' = ms' i /\ ev = evs i) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
  (forall i, m_halted (ms' i) = None) ->
  (forall i, materialize_model_accesses (ms' i) (syscall_effect_accesses (effs i)) = Some (ms'' i)) ->
  ShapeAlg.node_ok segs (mkCfg ms model) I evs
          (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms'' i)).
Proof.
  intros ms model x8 I effs ms' ms'' evs Hh Hsvc Hok Hinv Hnu Hh' Hmat. split.
  - intros i. apply (sstep_syscall segs ms model x8 (effs i) (ms' i) (ms'' i) (evs i) Hh Hsvc).
    + apply check_syscall_ok_iff. exact (Hok i).
    + exact (Hh' i).
    + exact (Hmat i).
  - intros e st Hss.
    destruct (sstep_svc_inv segs ms model x8 e st Hsvc Hss)
      as [(eff & model' & ev & Hc & [(m3 & Hh2 & -> & Hm & ->) | [(Hh2 & -> & Hm & ->) | (code & Hh2 & -> & ->)]])
         | (eff & Hc & -> & ->)].
    + destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->).
      rewrite (Hmat i) in Hm. injection Hm as <-. exists i. split; reflexivity.
    + destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->). rewrite (Hmat i) in Hm. discriminate.
    + destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->). rewrite Hh' in Hh2. discriminate.
    + exfalso. exact (Hnu eff Hc).
Qed.

(* [comment removed for export] *)
Lemma srz_cfg_ret_only_silent_noacc : forall ms model x8 r m' T,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model = check_ret_only eff r m' []) ->
  m_halted m' = None ->
  srealizes_cfg segs (mkCfg (advance_past_svc (set_gpr0 ms r)) m') T ->
  srealizes_cfg segs (mkCfg ms model) T.
Proof.
  intros ms model x8 r m' T Hh Hsvc Hchk Hh' Hc.
  rewrite <- (apply_effect_no_write ms r) in Hc.
  eapply (srz_cfg_det_noacc segs ms model x8 (mkEffect r [] []) m' T Hh Hsvc); [| | exact Hh' | reflexivity | exact Hc].
  - intros eff m'' evs. rewrite Hchk. apply check_ret_only_ok_iff.
  - intros eff. rewrite Hchk. apply check_ret_only_no_unmodeled.
Qed.

(* [comment removed for export] *)
Lemma srz_cfg_ret_only_copyins_silent_mat : forall ms model x8 reads r m' T,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model = check_ret_only_copyins reads eff r m' []) ->
  m_halted m' = None ->
  materialize_model_accesses m' reads = Some m' ->
  srealizes_cfg segs (mkCfg (advance_past_svc (set_gpr0 ms r)) m') T ->
  srealizes_cfg segs (mkCfg ms model) T.
Proof.
  intros ms model x8 reads r m' T Hh Hsvc Hchk Hh' Hmat Hc.
  eapply srz_cfg_silent1; [|exact Hc].
  rewrite <- (apply_effect_copyins_no_write ms r reads).
  apply (node_chk_ev_mat_gen ms model x8 unit (fun _ => with_copyins reads (mkEffect r [] []))
           (fun _ => m') (fun _ => m') (fun _ => []) Hh Hsvc).
  - intros []. rewrite Hchk. apply check_ret_only_copyins_ok_iff. auto.
  - intros eff m'' ev Hck. rewrite Hchk in Hck. apply check_ret_only_copyins_ok_iff in Hck as (-> & -> & ->).
    exists tt. auto.
  - intros eff. rewrite Hchk. apply check_ret_only_copyins_no_unmodeled.
  - intros []. exact Hh'.
  - intros []. unfold syscall_effect_accesses, with_copyins. cbn [eff_copyins eff_writes write_accesses].
    rewrite app_nil_r. exact Hmat.
Qed.

(* [comment removed for export] *)
Lemma node_open_mat : forall ms model x8 reads (mk : word -> Model),
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model
               = check_open_result_copyins reads eff model mk) ->
  (forall fd, m_halted (mk fd) = None) ->
  materialize_model_accesses model reads = Some model ->
  (forall fd, materialize_model_accesses (mk fd) reads = Some (mk fd)) ->
  fd_lookup (m_fds model) (alloc_fd (m_fds model)) = None ->
  ShapeAlg.node_ok segs (mkCfg ms model) (open_I model) (fun _ => []) (open_nx ms model mk).
Proof.
  intros ms model x8 reads mk Hh Hsvc Hchk Hmk Hmat0 Hmat1 Hfree.
  assert (ACC : forall r, syscall_effect_accesses (with_copyins reads (mkEffect r [] [])) = reads).
  { intros r. unfold syscall_effect_accesses, with_copyins. cbn. apply app_nil_r. }
  split.
  - intros [[e He] | []]; cbn [open_nx].
    + rewrite <- (apply_effect_copyins_no_write ms (errno_ret e) reads).
      apply (sstep_syscall segs ms model x8 _ model model [] Hh Hsvc).
      * apply check_syscall_ok_iff. rewrite Hchk. apply check_open_result_copyins_ok_iff. left. exists e. auto.
      * exact Hh.
      * rewrite ACC. exact Hmat0.
    + rewrite <- (apply_effect_copyins_no_write ms (alloc_fd (m_fds model)) reads).
      apply (sstep_syscall segs ms model x8 _ (mk (alloc_fd (m_fds model))) (mk (alloc_fd (m_fds model))) [] Hh Hsvc).
      * apply check_syscall_ok_iff. rewrite Hchk. apply check_open_result_copyins_ok_iff.
        right. exists (alloc_fd (m_fds model)). auto.
      * apply Hmk.
      * rewrite ACC. apply Hmat1.
  - intros e st Hss.
    destruct (sstep_svc_inv segs ms model x8 e st Hsvc Hss)
      as [(eff & model' & ev & Hc & [(m'' & Hh2 & -> & Hmat & ->) | [(Hh2 & -> & Hmat & ->) | (code & Hh2 & -> & ->)]])
         | (eff & Hc & -> & ->)].
    + rewrite Hchk in Hc. apply check_open_result_copyins_ok_iff in Hc.
      destruct Hc as [(er & Her & -> & -> & ->) | (fd & Hlk & Heq & -> & -> & ->)].
      * rewrite ACC, Hmat0 in Hmat. injection Hmat as <-.
        exists (inl (exist _ er Her)). cbn [open_nx].
        rewrite apply_effect_copyins_no_write. split; reflexivity.
      * subst fd. rewrite ACC, (Hmat1 _) in Hmat. injection Hmat as <-.
        exists (inr tt). cbn [open_nx]. rewrite apply_effect_copyins_no_write. split; reflexivity.
    + rewrite Hchk in Hc. apply check_open_result_copyins_ok_iff in Hc.
      destruct Hc as [(er & Her & -> & -> & ->) | (fd & Hlk & Heq & -> & -> & ->)].
      * rewrite ACC, Hmat0 in Hmat. discriminate.
      * subst fd. rewrite ACC, (Hmat1 _) in Hmat. discriminate.
    + rewrite Hchk in Hc. apply check_open_result_copyins_ok_iff in Hc.
      destruct Hc as [(er & Her & -> & -> & ->) | (fd & Hlk & Heq & -> & -> & ->)].
      * congruence.
      * rewrite Hmk in Hh2. discriminate.
    + exfalso. rewrite Hchk in Hc. exact (check_open_result_copyins_never_unmodeled _ _ _ _ Hc).
Qed.

(* [comment removed for export] *)
Lemma srz_cfg_open_mat : forall ms model x8 reads (mk : word -> Model) A B,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  alloc_no (bv_unsigned x8) = false ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model
               = check_open_result_copyins reads eff model mk) ->
  (forall fd, m_halted (mk fd) = None) ->
  materialize_model_accesses model reads = Some model ->
  (forall fd, materialize_model_accesses (mk fd) reads = Some (mk fd)) ->
  fd_lookup (m_fds model) (alloc_fd (m_fds model)) = None ->
  (forall e, In e openat_errnos ->
     srealizes_cfg segs (mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model) A) ->
  srealizes_cfg segs (mkCfg (advance_past_svc (set_gpr0 ms (alloc_fd (m_fds model))))
                       (mk (alloc_fd (m_fds model)))) B ->
  srealizes_cfg segs (mkCfg ms model) (t_alt2 A B).
Proof.
  intros ms model x8 reads mk A B Hh Hsvc Hna Hchk Hmk Hmat0 Hmat1 Hfree HA HB.
  apply (srz_cfg_alt2 segs (mkCfg ms model) {e : Z | In e openat_errnos} unit
           (open_nx ms model mk) A B (exist _ ENOMEM ENOMEM_in_openat_errnos) tt).
  - apply node_ok_cfg_of_nonalloc; [exact (nonalloc_no segs ms model x8 Hsvc Hna) | eapply node_open_mat; eassumption].
  - intros [e He]. cbn [open_nx]. apply HA. exact He.
  - intros []. cbn [open_nx]. exact HB.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma srz_cfg_close_lazy : forall regs (pc : word) mem rom model w fd e K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 57 ->
  getr regs 10 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
  fd_lookup (m_fds model) fd = Some e ->
  srealizes_cfg segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) mem rom)
                       (with_fds (fd_remove (m_fds model) fd) model)) K ->
  srealizes_cfg segs (mkCfg (mkst regs pc mem rom) model) K.
Proof.
  intros regs pc mem rom model w fd e K HF HE Hh H17 Hfd Hfd32 Hlk Hc.
  eapply srz_cfg_sys_lazy; [exact Hh | exact HF | exact HE |].
  eapply srz_cfg_ret_only_silent_noacc; [exact Hh | reflexivity | | | rewrite adv_set_epend; exact Hc].
  - intros eff. rewrite (check_syscall_57 segs) by (rewrite H17; apply u64_lit; lia).
    unfold check_close. rewrite ms_gpr_epend0, Hfd, (fd32_id fd Hfd32), Hlk. reflexivity.
  - rewrite with_fds_halted. exact Hh.
Qed.

Lemma check_syscall_29 : forall ms x8 eff m,
  bv_unsigned x8 = 29%Z ->
  check_syscall (sys_input segs ms x8) eff m = check_ioctl (fd32 (ms_gpr ms 0)) (cmd32 (ms_gpr ms 1)) eff m.
Proof. intros ms x8 eff m Hno. unfold check_syscall. rewrite in_sysno_si, Hno. reflexivity. Qed.

(* [comment removed for export] *)
Lemma srz_cfg_ioctl_winsz_lazy : forall regs (pc : word) mem rom model w fd c K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 29 ->
  getr regs 10 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
  fd_lookup (m_fds model) fd = Some (FdChannel c) ->
  getr regs 11 = Z_to_bv 64 0x5413 ->
  srealizes_cfg segs (mkCfg (mkst (regupd regs 10 (errno_ret ENOTTY)) (v_addi pc 4) mem rom) model) K ->
  srealizes_cfg segs (mkCfg (mkst regs pc mem rom) model) K.
Proof.
  intros regs pc mem rom model w fd c K HF HE Hh H17 Hfd Hfd32 Hlk H11 Hc.
  eapply srz_cfg_sys_lazy; [exact Hh | exact HF | exact HE |].
  eapply srz_cfg_ret_only_silent_noacc; [exact Hh | reflexivity | | exact Hh | rewrite adv_set_epend; exact Hc].
  intros eff. rewrite check_syscall_29 by (rewrite H17; apply u64_lit; lia).
  unfold check_ioctl. rewrite ms_gpr_epend0, ms_gpr_epend1, Hfd, (fd32_id fd Hfd32), Hlk, H11.
  reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma srz_cfg_read_dir_lazy : forall regs (pc : word) mem rom model w fd K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 63 ->
  getr regs 10 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
  fd_lookup (m_fds model) fd = Some FdDir ->
  (bv_unsigned (getr regs 11) + bv_unsigned (getr regs 12) <= TASK_SIZE)%Z ->
  srealizes_cfg segs (mkCfg (mkst (regupd regs 10 (errno_ret EISDIR)) (v_addi pc 4) mem rom) model) K ->
  srealizes_cfg segs (mkCfg (mkst regs pc mem rom) model) K.
Proof.
  intros regs pc mem rom model w fd K HF HE Hh H17 Hfd Hfd32 Hlk Hdir Hc.
  eapply srz_cfg_sys_lazy; [exact Hh | exact HF | exact HE |].
  eapply srz_cfg_ret_only_silent_noacc; [exact Hh | reflexivity | | exact Hh | rewrite adv_set_epend; exact Hc].
  intros eff. rewrite (check_syscall_63 segs _ _ eff model) by (rewrite H17; apply u64_lit; lia).
  unfold check_read. rewrite ms_gpr_epend0, ms_gpr_epend1, ms_gpr_epend2, Hfd, (fd32_id fd Hfd32), Hlk.
  rewrite (access_okb_intro _ _ Hdir). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma srz_cfg_read_file_mat : forall regs (pc : word) mem rom model w fd p off data (cnt : Z) m'' K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 63 ->
  getr regs 10 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
  fd_lookup (m_fds model) fd = Some (FdFile p off) ->
  fs_lookup (m_fs model) p = Some data ->
  getr regs 12 = Z_to_bv 64 cnt ->
  (1 <= cnt)%Z -> (cnt <= rw_bytes_max)%Z ->
  store_ok segs mem (getr regs 11) (Z.to_nat cnt) = true ->
  (bv_unsigned (getr regs 11) + cnt <= TASK_SIZE)%Z ->
  let bs := file_read data off (getr regs 12) in
  let m' := with_fds (fd_insert (m_fds model) fd (FdFile p (off + len_word bs))) model in
  materialize_model_accesses m' (write_accesses (delivered_writes (getr regs 11) bs)) = Some m'' ->
  srealizes_cfg segs (mkCfg (mkst (regupd regs 10 (len_word bs)) (v_addi pc 4)
                                  (wbytes mem (getr regs 11) bs) rom) m'') K ->
  srealizes_cfg segs (mkCfg (mkst regs pc mem rom) model) K.
Proof.
  intros regs pc mem rom model w fd p off data cnt m'' K HF HE Hh H17 Hfd Hfd32 Hlk Hfs H12 Hc1 Hmax Hok Hover bs m' Hmat Hc.
  assert (Hrw : (rw_bytes_max < 2 ^ 64)%Z) by (unfold rw_bytes_max; lia).
  assert (Hcnt : (cnt < 2 ^ 64)%Z) by lia.
  assert (Hno : bv_unsigned (getr regs 17) = 63%Z) by (rewrite H17; apply u64_lit; lia).
  eapply srz_cfg_sys_lazy; [exact Hh | exact HF | exact HE |].
  destruct (read_bytes_map_of_store_ok segs mem (getr regs 11) (Z.to_nat cnt) Hok ltac:(lia)) as [wv Hw].
  rewrite Z2Nat.id in Hw by lia.
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hu2 : bv_unsigned (ms_gpr ms 2) = cnt).
  { unfold ms. rewrite ms_gpr_epend2, H12. apply u64_lit. lia. }
  assert (H1ms : ms_gpr ms 1 = getr regs 11) by (unfold ms; apply ms_gpr_epend1).
  assert (H2ms : ms_gpr ms 2 = getr regs 12) by (unfold ms; apply ms_gpr_epend2).
  assert (H0ms : ms_gpr ms 0 = fd) by (unfold ms; rewrite ms_gpr_epend0; exact Hfd).
  assert (HL : (bv_unsigned (len_word (file_read data off (ms_gpr ms 2))) <= bv_unsigned (ms_gpr ms 2))%Z).
  { unfold len_word. rewrite Z_to_bv_unsigned, bv_wrap64_mod.
    pose proof (u64_range (ms_gpr ms 2)) as Hc2.
    rewrite length_file_read, Nat2Z.inj_min. unfold word_to_nat.
    rewrite Z.mod_small; lia. }
  assert (Hwms : read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) (ms_gpr ms 2) = Some wv).
  { unfold ms. rewrite ms_writable_byte_epend, ms_gpr_epend1, ms_gpr_epend2, H12. exact Hw. }
  subst bs m'. revert Hc Hmat.
  set (bs := file_read data off (getr regs 12)). intros Hc Hmat.
  assert (Hchk : forall eff m1 evs,
    check_syscall (sys_input segs ms (getr regs 17)) eff model = CheckOk m1 evs <->
    (eff = mkEffect (len_word bs) (delivered_writes (getr regs 11) bs) []
     /\ m1 = with_fds (fd_insert (m_fds model) fd (FdFile p (off + len_word bs))) model
     /\ evs = [])).
  { intros eff m1 evs.
    rewrite (check_syscall_63 segs ms (getr regs 17) eff model Hno). unfold check_read.
    rewrite H0ms, (fd32_id fd Hfd32), Hlk. cbv beta iota.
    rewrite (access_okb_intro (ms_gpr ms 1) (ms_gpr ms 2) ltac:(rewrite H1ms, Hu2; exact Hover)). cbn [negb]. cbv beta iota.
    rewrite (rw_count_clamp_of_rw (ms_gpr ms 2) ltac:(rewrite Hu2; exact Hmax)), Z_to_bv_bv_unsigned.
    rewrite Hfs. cbv beta iota zeta.
    rewrite in_wmem_si.
    rewrite (read_bytes_map_prefix _ _ _ _ _ HL Hwms). cbv beta iota.
    rewrite H1ms, H2ms. fold bs.
    destruct bs as [|b bsr].
    - cbv beta iota. rewrite check_ret_only_ok_iff. cbn [delivered_writes length]. tauto.
    - destruct eff as [ret ws zs us cs copyins]. split.
      + intro H.
        destruct ws as [|[a bs'] [|? ?]]; try discriminate.
        destruct zs as [|? ?]; [|discriminate].
        destruct us as [|? ?]; [|discriminate].
        destruct cs as [|? ?]; [|discriminate].
        destruct copyins as [|? ?]; [|discriminate].
        destruct (bv_eqb a (getr regs 11) && listN_eqb bs' (b :: bsr) && bv_eqb ret (len_word (b :: bsr)))
          eqn:Hb; try rewrite Hb in H; [|discriminate].
        apply andb_true_iff in Hb as [Hb Hr]. apply andb_true_iff in Hb as [Ha Hbs].
        apply bv_eqb_eq in Ha. apply bv_eqb_eq in Hr. apply listN_eqb_eq in Hbs.
        inversion H; subst. cbn [delivered_writes]. repeat split; congruence.
      + intros (Heff & -> & ->). cbn [delivered_writes] in Heff. inversion Heff; subst.
        rewrite bv_eqb_refl, (proj2 (listN_eqb_eq _ _) eq_refl), bv_eqb_refl. cbn [andb]. reflexivity. }
  assert (Hnu : forall eff, check_syscall (sys_input segs ms (getr regs 17)) eff model <> CheckUnmodeled).
  { intros eff Hu.
    rewrite (check_syscall_63 segs ms (getr regs 17) eff model Hno) in Hu. unfold check_read in Hu.
    rewrite H0ms, (fd32_id fd Hfd32), Hlk in Hu. cbv beta iota in Hu.
    rewrite (access_okb_intro (ms_gpr ms 1) (ms_gpr ms 2) ltac:(rewrite H1ms, Hu2; exact Hover)) in Hu. cbn [negb] in Hu. cbv beta iota in Hu.
    rewrite (rw_count_clamp_of_rw (ms_gpr ms 2) ltac:(rewrite Hu2; exact Hmax)), Z_to_bv_bv_unsigned in Hu.
    rewrite Hfs in Hu. cbv beta iota zeta in Hu.
    rewrite in_wmem_si in Hu.
    rewrite (read_bytes_map_prefix _ _ _ _ _ HL Hwms) in Hu. cbv beta iota in Hu.
    destruct (file_read data off (ms_gpr ms 2)) as [|b bsr].
    - exact (check_ret_only_no_unmodeled _ _ _ _ Hu).
    - destruct eff as [ret ws zs us cs copyins].
      destruct ws as [|[a bs'] [|? ?]]; try discriminate.
      destruct zs as [|? ?]; try discriminate. destruct us as [|? ?]; try discriminate.
      destruct cs as [|? ?]; try discriminate. destruct copyins as [|? ?]; try discriminate.
      destruct (bv_eqb a (ms_gpr ms 1) && listN_eqb bs' (b :: bsr) && bv_eqb ret (len_word (b :: bsr))); discriminate. }
  set (c' := mkCfg (advance_past_svc (apply_effect ms (mkEffect (len_word bs) (delivered_writes (getr regs 11) bs) []))) m'').
  assert (HN : ShapeAlg.node_ok segs (mkCfg ms model) unit (fun _ => []) (fun _ => c')).
  { apply (node_chk_ev_mat_gen ms model (getr regs 17) unit
             (fun _ => mkEffect (len_word bs) (delivered_writes (getr regs 11) bs) [])
             (fun _ => with_fds (fd_insert (m_fds model) fd (FdFile p (off + len_word bs))) model)
             (fun _ => m'') (fun _ => []) Hh eq_refl).
    + intros []. apply (proj2 (Hchk _ _ _)). auto.
    + intros eff mx ev H. apply Hchk in H as (-> & -> & ->). exists tt. auto.
    + exact Hnu.
    + intros []. rewrite with_fds_halted. exact Hh.
    + intros []. unfold syscall_effect_accesses. cbn [eff_copyins eff_writes app]. exact Hmat. }
  apply (srz_cfg_silent1 segs _ c' _ HN). unfold c'.
  destruct bs as [|b bsr]; cbn [delivered_writes].
  - unfold ms. rewrite adv_ret_epend. cbn [wbytes] in Hc. exact Hc.
  - unfold ms. rewrite adv_write1_epend. exact Hc.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma openat_dot_check : forall ms x8 model p,
  bv_unsigned x8 = 56%Z ->
  fd32 (ms_gpr ms 0) = AT_FDCWD32 ->
  read_cstr (ms_read_byte ms) (ms_gpr ms 1) = CstrOk p ->
  path_eqb p [] = false ->
  Z.ldiff (bv_unsigned (ms_gpr ms 2)) open_ignored_flags = 0%Z ->
  path_has_slash p = false -> path_is_dirref p = true ->
  forall eff,
    check_syscall (sys_input segs ms x8) eff model
    = check_open_result_copyins (open_copyins ms) eff model
        (fun fd => with_fds (fd_insert (m_fds model) fd FdDir) model).
Proof.
  intros ms x8 model p Hno Hdirfd Hpath Hpe Hfl Hunw Hdot eff.
  rewrite (check_syscall_56 segs ms x8 eff model Hno). unfold check_openat.
  rewrite (modeled_open_flags_rd _ Hfl). cbn [negb]. cbv beta iota.
  unfold Prelude.check_copyins_after, Open.check_openat_body.
  rewrite in_mem_si, Hpath. cbv beta iota zeta.
  rewrite Hpe. cbv beta iota.
  rewrite Hdirfd, bv_eqb_refl. cbn [negb]. cbv beta iota.
  unfold Open.check_openat_resolved.
  rewrite Hunw. cbv beta iota.
  rewrite Hfl, Z.eqb_refl. cbv beta iota.
  unfold Open.check_openat_read.
  rewrite Hdot.
  unfold check_open_result_copyins, open_copyins.
  destruct (check_open_result (clear_copyins eff) model
    (fun fd : word => with_fds (fd_insert (m_fds model) fd FdDir) model)) eqn:Hresult.
  - reflexivity.
  - reflexivity.
  - exfalso. now apply check_open_result_never_unmodeled in Hresult.
Qed.

(* [comment removed for export] *)
Lemma openat_file_check : forall ms x8 model p d,
  bv_unsigned x8 = 56%Z ->
  fd32 (ms_gpr ms 0) = AT_FDCWD32 ->
  read_cstr (ms_read_byte ms) (ms_gpr ms 1) = CstrOk p ->
  path_eqb p [] = false ->
  Z.ldiff (bv_unsigned (ms_gpr ms 2)) open_ignored_flags = 0%Z ->
  openat_plain_name p = true ->
  fs_lookup (m_fs model) p = Some d ->
  forall eff,
    check_syscall (sys_input segs ms x8) eff model
    = check_open_result_copyins (open_copyins ms) eff model
        (fun fd => with_fds (fd_insert (m_fds model) fd (FdFile p (Z_to_bv 64 0))) model).
Proof.
  intros ms x8 model p d Hno Hdirfd Hpath Hpe Hfl Hdot Hfs eff.
  pose proof (openat_plain_name_noslash _ Hdot) as Hunw.
  apply openat_plain_name_nodirref in Hdot.
  rewrite (check_syscall_56 segs ms x8 eff model Hno). unfold check_openat.
  rewrite (modeled_open_flags_rd _ Hfl). cbn [negb]. cbv beta iota.
  unfold Prelude.check_copyins_after, Open.check_openat_body.
  rewrite in_mem_si, Hpath. cbv beta iota zeta.
  rewrite Hpe. cbv beta iota.
  rewrite Hdirfd, bv_eqb_refl. cbn [negb]. cbv beta iota.
  unfold Open.check_openat_resolved.
  rewrite Hunw. cbv beta iota.
  rewrite Hfl, Z.eqb_refl. cbv beta iota.
  unfold Open.check_openat_read.
  rewrite ?Hdot, ?Hfs.
  unfold check_open_result_copyins, open_copyins.
  destruct (check_open_result (clear_copyins eff) model
    (fun fd : word => with_fds (fd_insert (m_fds model) fd (FdFile p (Z_to_bv 64 0))) model)) eqn:Hresult.
  - reflexivity.
  - reflexivity.
  - exfalso. now apply check_open_result_never_unmodeled in Hresult.
Qed.

(* [comment removed for export] *)
Lemma openat_enoent_check : forall ms x8 model p,
  bv_unsigned x8 = 56%Z ->
  fd32 (ms_gpr ms 0) = AT_FDCWD32 ->
  read_cstr (ms_read_byte ms) (ms_gpr ms 1) = CstrOk p ->
  Z.ldiff (bv_unsigned (ms_gpr ms 2)) open_ignored_flags = 0%Z ->
  (p = [] \/ (openat_plain_name p = true /\ fs_lookup (m_fs model) p = None)) ->
  forall eff,
    check_syscall (sys_input segs ms x8) eff model
    = check_ret_only_copyins (open_copyins ms) eff (errno_ret ENOENT) model [].
Proof.
  intros ms x8 model p Hno Hdirfd Hpath Hfl Hcase eff.
  rewrite (check_syscall_56 segs ms x8 eff model Hno).
  unfold check_openat.
  rewrite (modeled_open_flags_rd _ Hfl). cbn [negb]. cbv beta iota.
  unfold Prelude.check_copyins_after, Open.check_openat_body.
  rewrite in_mem_si, Hpath. cbv beta iota zeta.
  destruct (path_eqb p []) eqn:Hpe; cbv beta iota.
  - apply check_copyins_after_ret_only.
  - destruct Hcase as [-> | [Hdot Hfs]]; [discriminate Hpe|].
    pose proof (openat_plain_name_noslash _ Hdot) as Hunw.
    apply openat_plain_name_nodirref in Hdot.
    rewrite Hdirfd, bv_eqb_refl. cbn [negb]. cbv beta iota.
    unfold Open.check_openat_resolved.
    rewrite Hunw. cbv beta iota.
    rewrite Hfl, Z.eqb_refl. cbv beta iota.
    unfold Open.check_openat_read. rewrite Hdot, Hfs.
    apply check_copyins_after_ret_only.
Qed.

Section Openat.
  Variables (regs : bvmap 5 word) (pc : word) (mem : word -> option byte) (model : Model).
  Let rom := seg_rom segs.
  Variable w : bv 32.
  Hypothesis HF : fetch_word segs pc = Some w.
  Hypothesis HE : is_ecall w = true.
  Hypothesis Hh : m_halted model = None.
  Hypothesis H17 : getr regs 17 = Z_to_bv 64 56.
  Hypothesis H10 : fd32 (getr regs 10) = AT_FDCWD32.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis Hfl : Z.ldiff (bv_unsigned (getr regs 12)) open_ignored_flags = 0%Z.

  Let ms := epend regs pc mem rom (getr regs 17).
  Let post (r : word) := mkst (regupd regs 10 r) (v_addi pc 4) mem rom.
  Let fds := m_fds model.
  (* [comment removed for export] *)
  Definition path_reads : list (word * nat) :=
    [(getr regs 11, cstr_access_len_aux (mrb segs mem) (getr regs 11) path_max)].
  Hypothesis Hmat0 : materialize_model_accesses model path_reads = Some model.

  Lemma open_copyins_ms : open_copyins ms = path_reads.
  Proof. unfold open_copyins, path_reads, ms, rom. rewrite ms_read_byte_epend, ms_gpr_epend1. reflexivity. Qed.

  Lemma Hno56 : bv_unsigned (getr regs 17) = 56%Z.
  Proof. rewrite H17. apply u64_lit. lia. Qed.

  Lemma ms_gpr0_fdcwd : fd32 (ms_gpr ms 0) = AT_FDCWD32.
  Proof. unfold ms. rewrite ms_gpr_epend0. exact H10. Qed.

  Lemma ms_flags : Z.ldiff (bv_unsigned (ms_gpr ms 2)) open_ignored_flags = 0%Z.
  Proof. unfold ms. rewrite ms_gpr_epend2. exact Hfl. Qed.

  Lemma ms_path : forall r, read_cstr (mrb segs mem) (getr regs 11) = r -> read_cstr (ms_read_byte ms) (ms_gpr ms 1) = r.
  Proof. intros r H. unfold ms, rom. rewrite ms_read_byte_epend, ms_gpr_epend1. exact H. Qed.

  (* [comment removed for export] *)
  Definition path_at' (p : list byte) : Prop :=
    (length p <= 4095)%nat /\ ~ In (Z_to_bv 8 0) p
    /\ rdn segs mem (getr regs 11) (length p + 1) = Some (p ++ [Z_to_bv 8 0]).

  Lemma path_at_cstr' : forall p, path_at' p -> read_cstr (mrb segs mem) (getr regs 11) = CstrOk p.
  Proof. intros p (H1 & H2 & H3). apply read_cstr_of_rdn; assumption. Qed.

  (* [comment removed for export] *)
  Lemma srz_cfg_openat_toolong_lazy : forall bs K,
    rdn segs mem (getr regs 11) 4096 = Some bs -> ~ In (Z_to_bv 8 0) bs ->
    srealizes_cfg segs (mkCfg (post (errno_ret ENAMETOOLONG)) model) K ->
    srealizes_cfg segs (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
  Proof using HF HE Hh H17 H10 Hfl Hmat0.
    intros bs K Hrd Hnz Hc. cbv delta [post] in *.
    pose proof (read_cstr_toolong_of_rdn segs mem (getr regs 11) bs (rdn_length _ _ _ _ _ Hrd) Hnz Hrd) as Hp.
    eapply srz_cfg_sys_lazy; [exact Hh | exact HF | exact HE |].
    eapply srz_cfg_ret_only_copyins_silent_mat; [exact Hh | reflexivity | | exact Hh | | rewrite adv_set_epend; exact Hc].
    - intros eff. fold ms.
      exact (openat_toolong_check segs ms (getr regs 17) model Hno56
               ltac:(unfold ms; rewrite ms_gpr_epend2; exact (modeled_open_flags_rd _ Hfl)) (ms_path _ Hp) eff).
    - rewrite open_copyins_ms. exact Hmat0.
  Qed.

  (* [comment removed for export] *)
  Lemma srz_cfg_openat_empty_lazy : forall K,
    path_at' [] ->
    srealizes_cfg segs (mkCfg (post (errno_ret ENOENT)) model) K ->
    srealizes_cfg segs (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
  Proof using HF HE Hh H17 H10 Hfl Hmat0.
    intros K Hp Hc. cbv delta [post] in *.
    eapply srz_cfg_sys_lazy; [exact Hh | exact HF | exact HE |].
    eapply srz_cfg_ret_only_copyins_silent_mat; [exact Hh | reflexivity | | exact Hh | | rewrite adv_set_epend; exact Hc].
    - intros eff. fold ms.
      exact (openat_enoent_check ms (getr regs 17) model [] Hno56 ms_gpr0_fdcwd (ms_path _ (path_at_cstr' [] Hp))
               ms_flags (or_introl eq_refl) eff).
    - rewrite open_copyins_ms. exact Hmat0.
  Qed.

  (* [comment removed for export] *)
  Lemma srz_cfg_openat_absent_lazy : forall p K,
    path_at' p -> openat_plain_name p = true -> fs_lookup (m_fs model) p = None ->
    srealizes_cfg segs (mkCfg (post (errno_ret ENOENT)) model) K ->
    srealizes_cfg segs (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
  Proof using HF HE Hh H17 H10 Hfl Hmat0.
    intros p K Hp Hpl Hfs Hc. cbv delta [post] in *.
    eapply srz_cfg_sys_lazy; [exact Hh | exact HF | exact HE |].
    eapply srz_cfg_ret_only_copyins_silent_mat; [exact Hh | reflexivity | | exact Hh | | rewrite adv_set_epend; exact Hc].
    - intros eff. fold ms.
      exact (openat_enoent_check ms (getr regs 17) model p Hno56 ms_gpr0_fdcwd (ms_path _ (path_at_cstr' p Hp))
               ms_flags (or_intror (conj Hpl Hfs)) eff).
    - rewrite open_copyins_ms. exact Hmat0.
  Qed.

  Hypothesis Hfree : fd_lookup fds (alloc_fd fds) = None.
  (* [comment removed for export] *)
  Hypothesis Hmat1 : forall f, materialize_model_accesses (with_fds f model) path_reads = Some (with_fds f model).

  (* [comment removed for export] *)
  Lemma srz_cfg_openat_dot_lazy : forall KA KB,
    path_at' dot_path ->
    (forall e, In e openat_errnos -> srealizes_cfg segs (mkCfg (post (errno_ret e)) model) KA) ->
    srealizes_cfg segs (mkCfg (post (alloc_fd fds)) (with_fds (fd_insert fds (alloc_fd fds) FdDir) model)) KB ->
    srealizes_cfg segs (mkCfg (mkst regs pc mem (seg_rom segs)) model) (t_alt2 KA KB).
  Proof using HF HE Hh H17 H10 Hfl Hmat0 Hfree Hmat1.
    intros KA KB Hp HA HB. cbv delta [post] in *.
    eapply srz_cfg_sys_lazy; [exact Hh | exact HF | exact HE |].
    eapply srz_cfg_open_mat; [exact Hh | reflexivity | rewrite Hno56; reflexivity | | | | | exact Hfree | |].
    - intros eff. fold ms.
      exact (openat_dot_check ms (getr regs 17) model dot_path Hno56 ms_gpr0_fdcwd (ms_path _ (path_at_cstr' _ Hp))
               eq_refl ms_flags eq_refl eq_refl eff).
    - intros fd. cbv beta delta [fds]. rewrite with_fds_halted. exact Hh.
    - rewrite open_copyins_ms. exact Hmat0.
    - intros fd. rewrite open_copyins_ms. apply Hmat1.
    - intros e He. rewrite adv_set_epend. apply HA. exact He.
    - rewrite adv_set_epend. exact HB.
  Qed.

  (* [comment removed for export] *)
  Lemma srz_cfg_openat_file_lazy : forall p d KA KB,
    path_at' p -> p <> [] -> openat_plain_name p = true -> fs_lookup (m_fs model) p = Some d ->
    (forall e, In e openat_errnos -> srealizes_cfg segs (mkCfg (post (errno_ret e)) model) KA) ->
    srealizes_cfg segs (mkCfg (post (alloc_fd fds))
                         (with_fds (fd_insert fds (alloc_fd fds) (FdFile p (Z_to_bv 64 0))) model)) KB ->
    srealizes_cfg segs (mkCfg (mkst regs pc mem (seg_rom segs)) model) (t_alt2 KA KB).
  Proof using HF HE Hh H17 H10 Hfl Hmat0 Hfree Hmat1.
    intros p d KA KB Hp Hne Hpl Hfs HA HB. cbv delta [post] in *.
    eapply srz_cfg_sys_lazy; [exact Hh | exact HF | exact HE |].
    eapply srz_cfg_open_mat; [exact Hh | reflexivity | rewrite Hno56; reflexivity | | | | | exact Hfree | |].
    - intros eff. fold ms.
      exact (openat_file_check ms (getr regs 17) model p d Hno56 ms_gpr0_fdcwd (ms_path _ (path_at_cstr' p Hp))
               (path_eqb_neq _ _ Hne) ms_flags Hpl Hfs eff).
    - intros fd. cbv beta delta [fds]. rewrite with_fds_halted. exact Hh.
    - rewrite open_copyins_ms. exact Hmat0.
    - intros fd. rewrite open_copyins_ms. apply Hmat1.
    - intros e He. rewrite adv_set_epend. apply HA. exact He.
    - rewrite adv_set_epend. exact HB.
  Qed.
End Openat.

End WithSegs.
