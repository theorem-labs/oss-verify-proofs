(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import Bcfg BSimInv BExitSim BPropExec BCatExec BCatSim BMmapSim BAllocSim BFileSim BRelSpec BShapeAlg BNodes BAgentLib BAgentNodes Bap04 BRefNodes BefNodesDir BHoare BLibWritev BReach BazyRestrict BazyRestrictRun BazyRestrictAlg BazyLedger BazySR BazyNodes.
Import ListNotations.
Open Scope bv_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Section WithSegs.
Variable segs : list Segment.

Context {SC : StepCfg}.
Context {fx : DFP}.

Lemma rdn_restrict : forall L S mF a n bs,
  lazy_ranges_okb segs L = true ->
  rdn segs (restrict_mem L S mF) a n = Some bs ->
  rdn segs mF a n = Some bs /\ range_visible (hiddenb L S) a n.
Proof.
  intros L S mF a n bs HL H. rewrite <- ov_rdn in H |- *.
  exact (ov_read_bytes_restrict segs (hiddenb L S) (lazy_ranges_ok_avoids segs L S HL) n mF a bs H).
Qed.

Lemma store_ok_restrictL : forall L S mF a n,
  lazy_ranges_okb segs L = true ->
  store_ok segs (restrict_mem L S mF) a n = true ->
  store_ok segs mF a n = true /\ range_visible (hiddenb L S) a n.
Proof.
  intros L S mF a n HL H.
  exact (store_ok_restrict segs (hiddenb L S) (lazy_ranges_ok_avoids segs L S HL) n mF a H).
Qed.

Lemma rz_sys_lazy : forall L S Zr msF regs pc mem mo w T,
  lzok segs L S Zr (mkCfg msF mo) ->
  restrict L S msF = mkst regs pc mem (seg_rom segs) ->
  fetch_word segs pc = Some w -> is_ecall w = true ->
  (forall msF1, lzok segs L S Zr (mkCfg msF1 mo) ->
     restrict L S msF1 = epend regs pc mem (seg_rom segs) (getr regs 17) ->
     ms_svc_pending msF1 = Some (getr regs 17) ->
     hid_same L S msF msF1 ->
     realizes segs (mkCfg msF1 mo) T) ->
  realizes segs (mkCfg msF mo) T.
Proof.
  intros L S Zr msF regs pc mem mo w T Hok Hr HF HE Hk.
  destruct msF as [rg fr pcv svc rv fc mm rom].
  unfold restrict, restrict_by, with_mem in Hr. cbn in Hr. unfold mkst in Hr.
  injection Hr as Erg Efr Epc Esvc Erv Efc Emm Erom. subst rg fr pcv svc rv fc rom.
  set (msF := {| ms_regs := regs; ms_fregs := dfp_regs; ms_pc_val := pc; ms_svc_pending := None;
                 ms_resv := None; ms_fcsr := dfp_csr; ms_mem := mm; ms_rom := seg_rom segs |}) in *.
  set (msF1 := {| ms_regs := regs; ms_fregs := dfp_regs; ms_pc_val := pc; ms_svc_pending := Some (getr regs 17);
                  ms_resv := None; ms_fcsr := dfp_csr; ms_mem := mm; ms_rom := seg_rom segs |}).
  assert (Hacc : mi_account_step segs msF mo = MachineOk (msF1, mo)).
  { unfold mi_account_step. rewrite (step_accesses_ecall_gen segs msF w HF HE).
    cbn [accessed_ranges access_value]. rewrite materialize_model_accesses_nil. reflexivity. }
  eapply rz_account_step; [exact (lzok_halted Hok) | reflexivity | exact Hacc |].
  apply Hk.
  - destruct Hok as [HL Hinv Hh HZ HSZ HZL HLM]. split; cbn in *; assumption.
  - unfold msF1, epend, restrict, restrict_by, with_mem. cbn. rewrite Emm. reflexivity.
  - reflexivity.
  - intros a Ha. reflexivity.
Qed.

Lemma lzok_after_fd_op : forall L S Zr msF1 mo mo1 eff,
  lzok segs L S Zr (mkCfg msF1 mo) ->
  m_vm mo1 = m_vm mo -> m_halted mo1 = None ->
  ranges_visible (hiddenb L S) (syscall_effect_accesses eff) ->
  (forall a, hiddenb L S a = true -> ms_mem (apply_effect msF1 eff) a = ms_mem msF1 a) ->
  exists mo',
    materialize_model_accesses mo1 (syscall_effect_accesses eff) = Some mo'
    /\ same_but_materialized mo1 mo'
    /\ lzok segs L S Zr (mkCfg (advance_past_svc (apply_effect msF1 eff)) mo')
    /\ hid_same L S msF1 (advance_past_svc (apply_effect msF1 eff)).
Proof.
  intros L S Zr msF1 mo mo1 eff Hok Evm Hh1 Hvis Hmem.
  destruct Hok as [HL Hinv Hh HZ HSZ HZL HLM]. cbn in *.
  pose proof (lazy_inv_vm_frame L S mo mo1 Evm Hinv) as Hinv1.
  destruct (materialize_restrict L S mo1 _ Hinv1 Hvis) as (pages & Hmat & Hinv').
  exists (with_vm_backing (m_vm_lazy mo1) pages mo1). split; [exact Hmat|].
  split; [apply same_but_materialized_with_vm_backing|].
  assert (Hhs : hid_same L S msF1 (advance_past_svc (apply_effect msF1 eff))).
  { intros a Ha. cbn [ms_mem advance_past_svc]. apply Hmem. exact Ha. }
  split; [|exact Hhs]. split; cbn.
  - exact HL.
  - exact Hinv'.
  - rewrite (same_but_materialized_halted mo1); [exact Hh1 | apply same_but_materialized_with_vm_backing].
  - intros a Ha Hz. rewrite (Hhs a Ha). exact (HZ a Ha Hz).
  - exact HSZ.
  - exact HZL.
  - rewrite (same_but_materialized_vmmaps mo1); [|apply same_but_materialized_with_vm_backing].
    unfold m_vmmaps in *. rewrite Evm. exact HLM.
Qed.

Lemma rz_fd_det_lazy : forall L S Zr msF1 mo x8 eff mo1 T,
  lzok segs L S Zr (mkCfg msF1 mo) ->
  ms_svc_pending msF1 = Some x8 ->
  (forall o, syscall_spec (sys_input segs msF1 x8) mo o <-> o = Ok eff mo1 []) ->
  m_vm mo1 = m_vm mo -> m_halted mo1 = None ->
  ranges_visible (hiddenb L S) (syscall_effect_accesses eff) ->
  (forall a, hiddenb L S a = true -> ms_mem (apply_effect msF1 eff) a = ms_mem msF1 a) ->
  (forall mo', lzok segs L S Zr (mkCfg (advance_past_svc (apply_effect msF1 eff)) mo') ->
              same_but_materialized mo1 mo' ->
              hid_same L S msF1 (advance_past_svc (apply_effect msF1 eff)) ->
              realizes segs (mkCfg (advance_past_svc (apply_effect msF1 eff)) mo') T) ->
  realizes segs (mkCfg msF1 mo) T.
Proof.
  intros L S Zr msF1 mo x8 eff mo1 T Hok Hsvc Hspec Evm Hh1 Hvis Hmem Hk.
  destruct (lzok_after_fd_op L S Zr msF1 mo mo1 eff Hok Evm Hh1 Hvis Hmem) as (mo' & Hmat & Hsame & Hok' & Hhs).
  eapply rz_silent1; [| apply (Hk mo' Hok' Hsame Hhs)].
  apply (node_family_mat segs msF1 mo x8 unit (fun _ => eff) (fun _ => mo1) (fun _ => mo') (fun _ => []) _
           (lzok_halted Hok) Hsvc Hspec).
  - intros []. reflexivity.
  - intros []. exact (not_spurious_det segs msF1 mo x8 eff mo1 [] Hspec).
  - intros o ->. exists tt. reflexivity.
  - intros []. exact Hh1.
  - intros []. exact Hmat.
Qed.

Lemma rz_fd_det_noacc_lazy : forall L S Zr msF1 mo x8 eff mo1 T,
  lzok segs L S Zr (mkCfg msF1 mo) ->
  ms_svc_pending msF1 = Some x8 ->
  (forall o, syscall_spec (sys_input segs msF1 x8) mo o <-> o = Ok eff mo1 []) ->
  m_vm mo1 = m_vm mo -> m_halted mo1 = None ->
  syscall_effect_accesses eff = [] ->
  (forall a, hiddenb L S a = true -> ms_mem (apply_effect msF1 eff) a = ms_mem msF1 a) ->
  (lzok segs L S Zr (mkCfg (advance_past_svc (apply_effect msF1 eff)) mo1) ->
   hid_same L S msF1 (advance_past_svc (apply_effect msF1 eff)) ->
   realizes segs (mkCfg (advance_past_svc (apply_effect msF1 eff)) mo1) T) ->
  realizes segs (mkCfg msF1 mo) T.
Proof.
  intros L S Zr msF1 mo x8 eff mo1 T Hok Hsvc Hspec Evm Hh1 Hacc Hmem Hk.
  assert (Hhs : hid_same L S msF1 (advance_past_svc (apply_effect msF1 eff))).
  { intros a Ha. cbn [ms_mem advance_past_svc]. apply Hmem. exact Ha. }
  eapply rz_silent1; [| apply Hk; [| exact Hhs]].
  - apply (node_family_noacc segs msF1 mo x8 unit (fun _ => eff) (fun _ => mo1) (fun _ => []) _
             (lzok_halted Hok) Hsvc Hspec).
    + intros []. reflexivity.
    + intros []. exact (not_spurious_det segs msF1 mo x8 eff mo1 [] Hspec).
    + intros o ->. exists tt. reflexivity.
    + intros []. exact Hh1.
    + intros []. exact Hacc.
  - eapply lzok_vm_frame; [exact Hok | exact Evm | exact Hh1 | exact Hhs].
Qed.

Lemma apply_effect_ret_copyins_mem : forall ms r reads,
  ms_mem (apply_effect ms (with_copyins reads (mkEffect r [] []))) = ms_mem ms.
Proof. intros ms r reads. destruct ms; reflexivity. Qed.

Lemma apply_effect_ret_mem : forall ms r,
  ms_mem (apply_effect ms (mkEffect r [] [])) = ms_mem ms.
Proof. intros ms r. destruct ms; reflexivity. Qed.

Lemma restrict_adv_ret : forall L S msF1 regs pc mem x8 r reads,
  restrict L S msF1 = epend regs pc mem (seg_rom segs) x8 ->
  restrict L S (advance_past_svc (apply_effect msF1 (with_copyins reads (mkEffect r [] []))))
  = mkst (regupd regs 10 r) (v_addi pc 4) mem (seg_rom segs).
Proof.
  intros L S msF1 regs pc mem x8 r reads Hr.
  destruct msF1 as [rg fr pcv svc rv fc mm rom].
  unfold restrict, restrict_by, with_mem, epend in Hr. cbn in Hr.
  injection Hr as Erg Efr Epc Esvc Erv Efc Emm Erom. subst rg fr pcv svc rv fc.
  rewrite <- Emm, <- Erom. change (restrict_mem_by (hiddenb L S) mm) with (restrict_mem L S mm).
  rewrite <- (adv_eff_ret_copyins_epend regs pc (restrict_mem L S mm) rom x8 r reads).
  unfold epend. rewrite !apply_effect_copyins_no_write. reflexivity.
Qed.

Lemma ms_gpr_of_restrict_epend : forall L S msF1 regs pc mem rom x8 k,
  restrict L S msF1 = epend regs pc mem rom x8 -> ms_gpr msF1 k = ms_gpr (epend regs pc mem rom x8) k.
Proof.
  intros L S msF1 regs pc mem rom x8 k Hr. unfold ms_gpr.
  replace (ms_regs msF1) with (ms_regs (restrict L S msF1)) by reflexivity. rewrite Hr. reflexivity.
Qed.

Theorem rz_close_lazy : forall L S Zr msF regs (pc : word) mem mo w fd e K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  lzok segs L S Zr (mkCfg msF mo) ->
  restrict L S msF = mkst regs pc mem (seg_rom segs) ->
  getr regs 17 = Z_to_bv 64 57 ->
  getr regs 10 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
  fd_lookup (m_fds mo) fd = Some e ->
  (forall msF', lzok segs L S Zr (mkCfg msF' (with_fds (fd_remove (m_fds mo) fd) mo)) ->
     restrict L S msF' = mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) mem (seg_rom segs) ->
     hid_same L S msF msF' ->
     realizes segs (mkCfg msF' (with_fds (fd_remove (m_fds mo) fd) mo)) K) ->
  realizes segs (mkCfg msF mo) K.
Proof.
  intros L S Zr msF regs pc mem mo w fd e K HF HE Hok Hr H17 Hfd Hfd32 Hlk Hc.
  eapply rz_sys_lazy; [exact Hok | exact Hr | exact HF | exact HE |].
  intros msF1 Hok1 Hr1 Hsvc1 Hhs1.
  pose proof (ms_gpr_of_restrict_epend L S msF1 regs pc mem (seg_rom segs) (getr regs 17)) as Hg.
  eapply (rz_fd_det_noacc_lazy L S Zr msF1 mo (getr regs 17) (mkEffect (Z_to_bv 64 0) [] [])
            (with_fds (fd_remove (m_fds mo) fd) mo)); [exact Hok1 | exact Hsvc1 | | reflexivity | | reflexivity | |].
  - intros o. rewrite (syscall_spec_57 _ mo o) by (rewrite in_sysno_si, H17; apply u64_lit; lia).
    rewrite in_arg0_si, (Hg 0%nat Hr1), ms_gpr_epend0, Hfd, (fd32_id fd Hfd32). exact (close_outcome fd _ mo e o Hlk).
  - rewrite with_fds_halted'. exact (lzok_halted Hok).
  - intros a Ha. rewrite apply_effect_ret_mem. reflexivity.
  - intros Hok' Hhs. apply Hc; [exact Hok' | | eapply hid_same_trans; [exact Hhs1 | exact Hhs]].
    rewrite <- (restrict_adv_ret L S msF1 regs pc mem (getr regs 17) (Z_to_bv 64 0) [] Hr1). reflexivity.
Qed.

Theorem rz_ioctl_winsz_lazy : forall L S Zr msF regs (pc : word) mem mo w fd e K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  lzok segs L S Zr (mkCfg msF mo) ->
  restrict L S msF = mkst regs pc mem (seg_rom segs) ->
  getr regs 17 = Z_to_bv 64 29 ->
  getr regs 10 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
  fd_lookup (m_fds mo) fd = Some (nodevnull e) ->
  getr regs 11 = Z_to_bv 64 0x5413 ->
  (forall msF', lzok segs L S Zr (mkCfg msF' mo) ->
     restrict L S msF' = mkst (regupd regs 10 (errno_ret ENOTTY)) (v_addi pc 4) mem (seg_rom segs) ->
     hid_same L S msF msF' ->
     realizes segs (mkCfg msF' mo) K) ->
  realizes segs (mkCfg msF mo) K.
Proof.
  intros L S Zr msF regs pc mem mo w fd e K HF HE Hok Hr H17 Hfd Hfd32 Hlk H11 Hc.
  eapply rz_sys_lazy; [exact Hok | exact Hr | exact HF | exact HE |].
  intros msF1 Hok1 Hr1 Hsvc1 Hhs1.
  pose proof (ms_gpr_of_restrict_epend L S msF1 regs pc mem (seg_rom segs) (getr regs 17)) as Hg.
  eapply (rz_fd_det_noacc_lazy L S Zr msF1 mo (getr regs 17) (mkEffect (errno_ret ENOTTY) [] []) mo);
    [exact Hok1 | exact Hsvc1 | | reflexivity | exact (lzok_halted Hok) | reflexivity | |].
  - intros o. rewrite (syscall_spec_29 _ mo o) by (rewrite in_sysno_si, H17; apply u64_lit; lia).
    rewrite in_arg0_si, in_arg1_si, !(Hg _ Hr1), ms_gpr_epend0, ms_gpr_epend1, Hfd, (fd32_id fd Hfd32), H11.
    apply (ioctl_tty_outcome fd _ _ mo e o Hlk). reflexivity.
  - intros a Ha. rewrite apply_effect_ret_mem. reflexivity.
  - intros Hok' Hhs. apply Hc; [exact Hok' | | eapply hid_same_trans; [exact Hhs1 | exact Hhs]].
    rewrite <- (restrict_adv_ret L S msF1 regs pc mem (getr regs 17) (errno_ret ENOTTY) [] Hr1). reflexivity.
Qed.

Theorem rz_exit_at_lazy : forall L S Zr msF regs (pc : word) mem rom mo w code,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  lzok segs L S Zr (mkCfg msF mo) ->
  restrict L S msF = mkst regs pc mem rom -> rom = seg_rom segs ->
  (getr regs 17 = Z_to_bv 64 94 \/ getr regs 17 = Z_to_bv 64 93) ->
  getr regs 10 = code ->
  realizes segs (mkCfg msF mo) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs mo)).
Proof.
  intros L S Zr msF regs pc mem rom mo w code HF HE Hok Hr -> H17 H10.
  eapply rz_sys_lazy; [exact Hok | exact Hr | exact HF | exact HE |].
  intros msF1 Hok1 Hr1 Hsvc1 Hhs1.
  rewrite <- H10, <- (ms_gpr_epend0 regs pc mem (seg_rom segs) (getr regs 17)),
          <- (ms_gpr_of_restrict_epend L S msF1 regs pc mem (seg_rom segs) (getr regs 17) 0 Hr1).
  eapply rz_exit; [exact (lzok_halted Hok1) | exact Hsvc1 |].
  destruct H17 as [H|H]; [right|left]; rewrite H; reflexivity.
Qed.

Lemma apply_effect_write1_mem : forall ms r a bs,
  ms_mem (apply_effect ms (mkEffect r [(a, bs)] [])) = write_to_mem (ms_mem ms) a bs.
Proof. intros ms r a bs. destruct ms; reflexivity. Qed.

Lemma sysret_epend : forall regs pc mem rom x8 r M,
  sysret (epend regs pc mem rom x8) r M = mkst (regupd regs 10 r) (v_addi pc 4) M rom.
Proof.
  intros regs pc mem rom x8 r M.
  transitivity (with_mem (advance_past_svc (apply_effect (epend regs pc mem rom x8) (mkEffect r [] []))) M); [reflexivity|].
  rewrite adv_eff_ret_epend. reflexivity.
Qed.

Theorem rz_read_file_lazy : forall L S Zr msF regs (pc : word) mem mo w fd p off data (cnt : Z) K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  lzok segs L S Zr (mkCfg msF mo) ->
  restrict L S msF = mkst regs pc mem (seg_rom segs) ->
  getr regs 17 = Z_to_bv 64 63 ->
  getr regs 10 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
  fd_lookup (m_fds mo) fd = Some (FdFile p off) ->
  fs_lookup (m_fs mo) p = Some data ->
  getr regs 12 = Z_to_bv 64 cnt ->
  (1 <= cnt)%Z -> (cnt <= MAX_RW_COUNT)%Z -> (cnt < 2 ^ 64)%Z ->
  (bv_unsigned (getr regs 11) + cnt <= TASK_SIZE)%Z ->
  store_ok segs mem (getr regs 11) (Z.to_nat cnt) = true ->
  let bs := file_read data off (getr regs 12) in
  let mo1 := with_fds (fd_insert (m_fds mo) fd (FdFile p (off + len_word bs))) mo in
  (forall msF' mo', lzok segs L S Zr (mkCfg msF' mo') ->
     same_but_materialized mo1 mo' ->
     restrict L S msF' = mkst (regupd regs 10 (len_word bs)) (v_addi pc 4) (wbytes mem (getr regs 11) bs) (seg_rom segs) ->
     hid_same L S msF msF' ->
     realizes segs (mkCfg msF' mo') K) ->
  realizes segs (mkCfg msF mo) K.
Proof.
  intros L S Zr msF regs pc mem mo w fd p off data cnt K HF HE Hok Hr H17 Hfd Hfd32 Hlk Hfs H12 Hc1 Hmax H64 Hover Hst bs mo1 Hc.
  assert (Hno : bv_unsigned (getr regs 17) = 63%Z) by (rewrite H17; apply u64_lit; lia).
  eapply rz_sys_lazy; [exact Hok | exact Hr | exact HF | exact HE |].
  intros msF1 Hok1 Hr1 Hsvc1 Hhs1.
  pose proof (ms_gpr_of_restrict_epend L S msF1 regs pc mem (seg_rom segs) (getr regs 17)) as Hg.

  assert (Emem : restrict_mem L S (ms_mem msF1) = mem).
  { transitivity (ms_mem (restrict L S msF1)); [reflexivity|]. rewrite Hr1. reflexivity. }
  destruct (store_ok_restrictL L S (ms_mem msF1) (getr regs 11) (Z.to_nat cnt) (lzok_ranges Hok)
              ltac:(rewrite Emem; exact Hst)) as [HstF Hvis].
  destruct (read_bytes_map_of_store_ok segs (ms_mem msF1) (getr regs 11) (Z.to_nat cnt) HstF ltac:(lia)) as [wv Hw].
  rewrite Z2Nat.id in Hw by lia.
  assert (Hu2 : bv_unsigned (ms_gpr msF1 2) = cnt).
  { rewrite (Hg 2%nat Hr1), ms_gpr_epend2, H12. apply u64_lit. lia. }
  pose proof (read_file_outcome_si segs msF1 (getr regs 17) mo fd p off data wv Hno
              ltac:(rewrite (Hg 0%nat Hr1), ms_gpr_epend0; exact Hfd) Hfd32 Hlk Hfs
              ltac:(unfold ms_writable_byte; rewrite (Hg 1%nat Hr1), (Hg 2%nat Hr1), ms_gpr_epend1, ms_gpr_epend2, H12; exact Hw)
              ltac:(rewrite Hu2; lia) ltac:(rewrite Hu2; exact Hmax)
              ltac:(rewrite Hu2, (Hg 1%nat Hr1), ms_gpr_epend1; exact Hover)) as Hchk.
  rewrite (Hg 1%nat Hr1), (Hg 2%nat Hr1), ms_gpr_epend1, ms_gpr_epend2 in Hchk. fold bs in Hchk. fold mo1 in Hchk.
  assert (Hlen : (length bs <= Z.to_nat cnt)%nat).
  { unfold bs. rewrite length_file_read, H12. unfold word_to_nat. rewrite u64_lit by lia. lia. }
  assert (HvisW : range_visible (hiddenb L S) (getr regs 11) (length bs)).
  { intros i Hi. apply Hvis. lia. }
  eapply (rz_fd_det_lazy L S Zr msF1 mo (getr regs 17) (mkEffect (len_word bs) (delivered_writes (getr regs 11) bs) []) mo1);
    [exact Hok1 | exact Hsvc1 | exact Hchk | reflexivity | | | |].
  - unfold mo1. rewrite with_fds_halted'. exact (lzok_halted Hok).
  - unfold syscall_effect_accesses. cbn [eff_copyins eff_writes app].
    destruct bs as [|b bsr]; cbn [delivered_writes write_accesses]; intros a n Hin; [destruct Hin|].
    destruct Hin as [Hin|[]]. injection Hin as <- <-. exact HvisW.
  - intros a Ha. destruct bs as [|b bsr]; cbn [delivered_writes].
    + rewrite apply_effect_ret_mem. reflexivity.
    + rewrite apply_effect_write1_mem.
      apply (write_to_mem_hidden (hiddenb L S)); [exact HvisW | exact Ha].
  - intros mo' Hok' Hsame Hhs. apply (Hc _ mo' Hok' Hsame); [| eapply hid_same_trans; [exact Hhs1 | exact Hhs]].
    rewrite (restrict_sysret L S L S msF1), Hr1, sysret_epend. cbn [eff_ret]. f_equal.
    destruct bs as [|b bsr]; cbn [delivered_writes].
    + rewrite apply_effect_ret_mem. cbn [wbytes]. exact Emem.
    + rewrite apply_effect_write1_mem, <- (write_to_mem_wbytes (b :: bsr) mem (getr regs 11)), <- Emem.
      unfold restrict_mem. symmetry. apply (write_to_mem_restrict (hiddenb L S)). exact HvisW.
Qed.

Lemma cstr_len_of_rdn : forall str fuel mem a,
  (length str < fuel)%nat -> ~ In (Z_to_bv 8 0) str ->
  rdn segs mem a (length str + 1) = Some (str ++ [Z_to_bv 8 0]) ->
  cstr_access_len_aux (mrb segs mem) a fuel = (length str + 1)%nat.
Proof.
  induction str as [|b str IH]; intros fuel mem a Hf Hnz Hr.
  - cbn [length] in *. destruct fuel as [|fuel]; [lia|].
    cbn [cstr_access_len_aux]. rewrite (mrb_first segs mem a 0 (Z_to_bv 8 0) [] Hr), bv_eqb_refl. reflexivity.
  - cbn [length] in *. destruct fuel as [|fuel]; [lia|]. cbn [cstr_access_len_aux]. cbn [app] in Hr.
    assert (Hb : b <> Z_to_bv 8 0) by (intro; apply Hnz; left; auto).
    rewrite (mrb_first segs mem a (length str + 1) b (str ++ [Z_to_bv 8 0]) Hr), (bv_eqb_neq b (Z_to_bv 8 0) Hb).
    rewrite (IH fuel mem (a + 1) ltac:(lia) ltac:(intro; apply Hnz; right; assumption)
               (rdn_tail segs mem a (length str + 1) b (str ++ [Z_to_bv 8 0]) Hr)). lia.
Qed.

Lemma cstr_len_toolong_of_rdn : forall fuel bs mem a,
  length bs = fuel -> ~ In (Z_to_bv 8 0) bs ->
  rdn segs mem a fuel = Some bs ->
  cstr_access_len_aux (mrb segs mem) a fuel = fuel.
Proof.
  induction fuel as [|fuel IH]; intros [|b bs] mem a Hlen Hnz Hr; cbn [length] in Hlen; try lia; [reflexivity|].
  cbn [cstr_access_len_aux].
  assert (Hb : b <> Z_to_bv 8 0) by (intro; apply Hnz; left; auto).
  rewrite (mrb_first segs mem a fuel b bs Hr), (bv_eqb_neq b (Z_to_bv 8 0) Hb).
  rewrite (IH bs mem (a + 1) ltac:(lia) ltac:(intro; apply Hnz; right; assumption) (rdn_tail segs mem a fuel b bs Hr)).
  reflexivity.
Qed.

Section OpenatLazy.
  Variables (L S Zr : list (word * word)) (msF : machine_state) (regs : bvmap 5 word) (pc : word)
            (mem : word -> option byte) (mo : Model).
  Variable w : bv 32.
  Hypothesis HF : fetch_word segs pc = Some w.
  Hypothesis HE : is_ecall w = true.
  Hypothesis Hok : lzok segs L S Zr (mkCfg msF mo).
  Hypothesis Hr : restrict L S msF = mkst regs pc mem (seg_rom segs).
  Hypothesis H17 : getr regs 17 = Z_to_bv 64 56.
  Hypothesis H10 : getr regs 10 = AT_FDCWD.
  Hypothesis Hfl : Z.ldiff (bv_unsigned (getr regs 12)) open_ignored_flags = 0%Z.

  Let post (r : word) := mkst (regupd regs 10 r) (v_addi pc 4) mem (seg_rom segs).
  Let fds := m_fds mo.

  Definition path_at_lazy (p : list byte) : Prop :=
    (length p <= 4095)%nat /\ ~ In (Z_to_bv 8 0) p
    /\ rdn segs mem (getr regs 11) (length p + 1) = Some (p ++ [Z_to_bv 8 0]).

  Section Pending.
    Variable msF1 : machine_state.
    Hypothesis Hok1 : lzok segs L S Zr (mkCfg msF1 mo).
    Hypothesis Hr1 : restrict L S msF1 = epend regs pc mem (seg_rom segs) (getr regs 17).
    Hypothesis Hsvc1 : ms_svc_pending msF1 = Some (getr regs 17).

    Let iF := sys_input segs msF1 (getr regs 17).

    Lemma pend_gpr : forall k, ms_gpr msF1 k = ms_gpr (epend regs pc mem (seg_rom segs) (getr regs 17)) k.
    Proof. intros k. exact (ms_gpr_of_restrict_epend L S msF1 regs pc mem (seg_rom segs) (getr regs 17) k Hr1). Qed.

    Lemma pend_mem : restrict_mem L S (ms_mem msF1) = mem.
    Proof. transitivity (ms_mem (restrict L S msF1)); [reflexivity|]. rewrite Hr1. reflexivity. Qed.

    Lemma pend_rom : ms_rom msF1 = seg_rom segs.
    Proof. transitivity (ms_rom (restrict L S msF1)); [reflexivity|]. rewrite Hr1. reflexivity. Qed.

    Lemma pend_in_mem : in_mem iF = mrb segs (ms_mem msF1).
    Proof.
      unfold iF. rewrite in_mem_si. apply functional_extensionality. intros a.
      unfold ms_read_byte, mrb. rewrite pend_rom. reflexivity.
    Qed.

    Lemma openat_spec_head_lazy : forall o,
      syscall_spec iF mo o <-> openat_spec AT_FDCWD32 (getr regs 11) (getr regs 12) iF mo o.
    Proof.
      intros o. unfold iF.
      rewrite (syscall_spec_56 _ mo o) by (rewrite in_sysno_si, H17; apply u64_lit; lia).
      rewrite in_arg0_si, in_arg1_si, in_arg2_si, !pend_gpr, ms_gpr_epend0, ms_gpr_epend1, ms_gpr_epend2, H10.
      reflexivity.
    Qed.

    Lemma open_flags_modeled_lazy : modeled_open_flags (getr regs 12) = true.
    Proof. exact (modeled_open_flags_rd _ Hfl). Qed.

    Lemma path_full : forall p, path_at_lazy p ->
      rdn segs (ms_mem msF1) (getr regs 11) (length p + 1) = Some (p ++ [Z_to_bv 8 0])
      /\ range_visible (hiddenb L S) (getr regs 11) (length p + 1)
      /\ read_cstr (in_mem iF) (getr regs 11) = CstrOk p
      /\ open_reads iF (getr regs 11) = [(getr regs 11, (length p + 1)%nat)].
    Proof.
      intros p (Hlen & Hnz & Hrd).
      rewrite <- pend_mem in Hrd.
      destruct (rdn_restrict L S (ms_mem msF1) (getr regs 11) (length p + 1) (p ++ [Z_to_bv 8 0]) (lzok_ranges Hok) Hrd) as [HrdF Hvis].
      split; [exact HrdF|]. split; [exact Hvis|].
      assert (Hlt : (length p < path_max)%nat) by (change path_max with 4096%nat; lia).
      split.
      - rewrite pend_in_mem. apply read_cstr_of_rdn; assumption.
      - unfold open_reads. rewrite pend_in_mem.
        rewrite (cstr_len_of_rdn p path_max (ms_mem msF1) (getr regs 11) Hlt Hnz HrdF). reflexivity.
    Qed.

    Lemma rz_openat_ret_lazy : forall (n : nat) r K,
      (forall o, syscall_spec iF mo o <-> o = Ok (with_copyins [(getr regs 11, n)] (mkEffect r [] [])) mo []) ->
      range_visible (hiddenb L S) (getr regs 11) n ->
      (forall msF' mo', lzok segs L S Zr (mkCfg msF' mo') -> same_but_materialized mo mo' ->
         restrict L S msF' = post r -> hid_same L S msF1 msF' -> realizes segs (mkCfg msF' mo') K) ->
      realizes segs (mkCfg msF1 mo) K.
    Proof.
      intros n r K Hspec Hvis Hc.
      eapply (rz_fd_det_lazy L S Zr msF1 mo (getr regs 17) (with_copyins [(getr regs 11, n)] (mkEffect r [] [])) mo);
        [exact Hok1 | exact Hsvc1 | exact Hspec | reflexivity | exact (lzok_halted Hok) | | |].
      - unfold syscall_effect_accesses, with_copyins. cbn. intros a k [Hin|[]]. injection Hin as <- <-. exact Hvis.
      - intros a Ha. rewrite apply_effect_ret_copyins_mem. reflexivity.
      - intros mo' Hok' Hsame Hhs. apply (Hc _ mo' Hok' Hsame); [|exact Hhs].
        unfold post. rewrite <- (restrict_adv_ret L S msF1 regs pc mem (getr regs 17) r [(getr regs 11, n)] Hr1). reflexivity.
    Qed.

    Lemma rz_open_lazy : forall (n : nat) (mk : word -> Model) KA KB,
      injected_family_off the_scfg iF = false ->
      (forall o, syscall_spec iF mo o <-> open_out [(getr regs 11, n)] mo mk o) ->
      (forall fd, m_vm (mk fd) = m_vm mo) -> (forall fd, m_halted (mk fd) = None) ->
      fd_lookup (m_fds mo) (alloc_fd (m_fds mo)) = None ->
      range_visible (hiddenb L S) (getr regs 11) n ->
      (forall e msF' mo', In e openat_errnos ->
         lzok segs L S Zr (mkCfg msF' mo') -> same_but_materialized mo mo' ->
         restrict L S msF' = post (errno_ret e) -> hid_same L S msF1 msF' -> realizes segs (mkCfg msF' mo') KA) ->
      (forall msF' mo',
         lzok segs L S Zr (mkCfg msF' mo') -> same_but_materialized (mk (alloc_fd (m_fds mo))) mo' ->
         restrict L S msF' = post (alloc_fd (m_fds mo)) -> hid_same L S msF1 msF' -> realizes segs (mkCfg msF' mo') KB) ->
      realizes segs (mkCfg msF1 mo) (t_alt2 KA KB).
    Proof.
      intros n mk KA KB Hon Hspec Hvm Hmk Hfree Hvis HA HB.
      pose (effs := fun i : open_I mo => match i with
              | inl (exist _ e _) => with_copyins [(getr regs 11, n)] (mkEffect (errno_ret e) [] [])
              | inr _ => with_copyins [(getr regs 11, n)] (mkEffect (alloc_fd (m_fds mo)) [] []) end).
      pose (ms1 := fun i : open_I mo => match i with inl _ => mo | inr _ => mk (alloc_fd (m_fds mo)) end).
      assert (Hacc : forall i, syscall_effect_accesses (effs i) = [(getr regs 11, n)]).
      { intros [[e He]|[]]; reflexivity. }
      assert (Hmemi : forall i a, hiddenb L S a = true -> ms_mem (apply_effect msF1 (effs i)) a = ms_mem msF1 a).
      { intros [[e He]|[]] a Ha; unfold effs; rewrite apply_effect_ret_copyins_mem; reflexivity. }
      assert (Hvisl : ranges_visible (hiddenb L S) [(getr regs 11, n)]).
      { intros a k [Hin|[]]. injection Hin as <- <-. exact Hvis. }
      assert (Hstep : forall i, exists mo', materialize_model_accesses (ms1 i) (syscall_effect_accesses (effs i)) = Some mo'
                 /\ same_but_materialized (ms1 i) mo'
                 /\ lzok segs L S Zr (mkCfg (advance_past_svc (apply_effect msF1 (effs i))) mo')
                 /\ hid_same L S msF1 (advance_past_svc (apply_effect msF1 (effs i)))).
      { intros i. rewrite Hacc. rewrite <- (Hacc i).
        apply (lzok_after_fd_op L S Zr msF1 mo (ms1 i) (effs i) Hok1).
        - destruct i as [[e He]|[]]; [reflexivity | apply Hvm].
        - destruct i as [[e He]|[]]; [exact (lzok_halted Hok) | apply Hmk].
        - rewrite Hacc. exact Hvisl.
        - exact (Hmemi i). }

      assert (Hch : exists f : open_I mo -> Model, forall i,
                 materialize_model_accesses (ms1 i) (syscall_effect_accesses (effs i)) = Some (f i)
                 /\ same_but_materialized (ms1 i) (f i)
                 /\ lzok segs L S Zr (mkCfg (advance_past_svc (apply_effect msF1 (effs i))) (f i))
                 /\ hid_same L S msF1 (advance_past_svc (apply_effect msF1 (effs i)))).
      { exists (fun i => match materialize_model_accesses (ms1 i) (syscall_effect_accesses (effs i)) with Some m => m | None => mo end).
        intros i. destruct (Hstep i) as (mo' & E & H1 & H2 & H3). rewrite E. auto. }
      destruct Hch as (f & Hf).
      apply (rz_alt2 segs (mkCfg msF1 mo) {e : Z | In e openat_errnos} unit
               (fun i => mkCfg (advance_past_svc (apply_effect msF1 (effs i))) (f i)) KA KB
               (exist _ ENOMEM ENOMEM_in_openat_errnos) tt).
      - apply (node_family_mat segs msF1 mo (getr regs 17) (open_I mo) effs ms1 f (fun _ => []) _
                 (lzok_halted Hok1) Hsvc1 Hspec).
        + intros [[e He]|[]]; [left; exists e; auto | right; auto].
        + intros i. apply spurious_refusal_family_on. exact Hon.
        + intros o [(e & He & ->) | (Hlk & ->)]; [exists (inl (exist _ e He)) | exists (inr tt)]; reflexivity.
        + intros [[e He]|[]]; [exact (lzok_halted Hok) | apply Hmk].
        + intros i. exact (proj1 (Hf i)).
      - intros [e He]. unfold effs, ms1 in Hf |- *. cbv beta iota. destruct (Hf (inl (exist _ e He))) as (_ & Hs & Ho & Hh).
        cbv beta iota in Hs, Ho, Hh.
        apply (HA e _ _ He Ho Hs); [|exact Hh].
        unfold post. rewrite <- (restrict_adv_ret L S msF1 regs pc mem (getr regs 17) (errno_ret e) [(getr regs 11, n)] Hr1). reflexivity.
      - intros []. unfold effs, ms1 in Hf |- *. cbv beta iota. destruct (Hf (inr tt)) as (_ & Hs & Ho & Hh).
        cbv beta iota in Hs, Ho, Hh.
        apply (HB _ _ Ho Hs); [|exact Hh].
        unfold post. rewrite <- (restrict_adv_ret L S msF1 regs pc mem (getr regs 17) (alloc_fd (m_fds mo)) [(getr regs 11, n)] Hr1). reflexivity.
    Qed.
  End Pending.

  Theorem rz_openat_toolong_lazy : forall bs K,
    rdn segs mem (getr regs 11) 4096 = Some bs -> ~ In (Z_to_bv 8 0) bs ->
    (forall msF' mo', lzok segs L S Zr (mkCfg msF' mo') -> same_but_materialized mo mo' ->
       restrict L S msF' = post (errno_ret ENAMETOOLONG) -> hid_same L S msF msF' ->
       realizes segs (mkCfg msF' mo') K) ->
    realizes segs (mkCfg msF mo) K.
  Proof.
    intros bs K Hrd Hnz Hc.
    eapply rz_sys_lazy; [exact Hok | exact Hr | exact HF | exact HE |].
    intros msF1 Hok1 Hr1 Hsvc1 Hhs1.
    pose proof (rdn_length _ _ _ _ _ Hrd) as Hlen.
    rewrite <- (pend_mem msF1 Hr1) in Hrd.
    destruct (rdn_restrict L S (ms_mem msF1) (getr regs 11) 4096 bs (lzok_ranges Hok) Hrd) as [HrdF Hvis].
    apply (rz_openat_ret_lazy msF1 Hok1 Hr1 Hsvc1 4096%nat (errno_ret ENAMETOOLONG) K).
    - intros o. rewrite (openat_spec_head_lazy msF1 Hr1).
      rewrite (openat_toolong_outcome _ _ _ _ mo (open_flags_modeled_lazy) o).
      + unfold open_reads. change path_max with 4096%nat.
        rewrite (pend_in_mem msF1 Hr1), (cstr_len_toolong_of_rdn 4096 bs (ms_mem msF1) (getr regs 11) Hlen Hnz HrdF).
        reflexivity.
      + rewrite (pend_in_mem msF1 Hr1). exact (read_cstr_toolong_of_rdn segs (ms_mem msF1) (getr regs 11) bs Hlen Hnz HrdF).
    - exact Hvis.
    - intros msF' mo' Hok' Hsame Hr' Hhs'. apply (Hc msF' mo' Hok' Hsame Hr'). eapply hid_same_trans; eassumption.
  Qed.

  Theorem rz_openat_empty_lazy : forall K,
    path_at_lazy [] ->
    (forall msF' mo', lzok segs L S Zr (mkCfg msF' mo') -> same_but_materialized mo mo' ->
       restrict L S msF' = post (errno_ret ENOENT) -> hid_same L S msF msF' ->
       realizes segs (mkCfg msF' mo') K) ->
    realizes segs (mkCfg msF mo) K.
  Proof.
    intros K Hp Hc.
    eapply rz_sys_lazy; [exact Hok | exact Hr | exact HF | exact HE |].
    intros msF1 Hok1 Hr1 Hsvc1 Hhs1.
    destruct (path_full msF1 Hr1 [] Hp) as (HrdF & Hvis & Hcs & Hreads).
    apply (rz_openat_ret_lazy msF1 Hok1 Hr1 Hsvc1 (length (@nil byte) + 1) (errno_ret ENOENT) K).
    - intros o. rewrite (openat_spec_head_lazy msF1 Hr1).
      rewrite (openat_empty_outcome _ _ _ _ mo open_flags_modeled_lazy o Hcs), Hreads. reflexivity.
    - exact Hvis.
    - intros msF' mo' Hok' Hsame Hr' Hhs'. apply (Hc msF' mo' Hok' Hsame Hr'). eapply hid_same_trans; eassumption.
  Qed.

  Theorem rz_openat_absent_lazy : forall p K,
    path_at_lazy p -> p <> [] -> path_has_slash p = false -> path_is_dirref p = false ->
    fs_lookup (m_fs mo) p = None ->
    (forall msF' mo', lzok segs L S Zr (mkCfg msF' mo') -> same_but_materialized mo mo' ->
       restrict L S msF' = post (errno_ret ENOENT) -> hid_same L S msF msF' ->
       realizes segs (mkCfg msF' mo') K) ->
    realizes segs (mkCfg msF mo) K.
  Proof.
    intros p K Hp Hne Hsl Hnd Hfs Hc.
    eapply rz_sys_lazy; [exact Hok | exact Hr | exact HF | exact HE |].
    intros msF1 Hok1 Hr1 Hsvc1 Hhs1.
    destruct (path_full msF1 Hr1 p Hp) as (HrdF & Hvis & Hcs & Hreads).
    apply (rz_openat_ret_lazy msF1 Hok1 Hr1 Hsvc1 (length p + 1) (errno_ret ENOENT) K).
    - intros o. rewrite (openat_spec_head_lazy msF1 Hr1).
      rewrite (openat_absent_outcome _ _ _ _ mo open_flags_modeled_lazy eq_refl Hfl p o Hcs Hne Hsl Hnd Hfs), Hreads. reflexivity.
    - exact Hvis.
    - intros msF' mo' Hok' Hsame Hr' Hhs'. apply (Hc msF' mo' Hok' Hsame Hr'). eapply hid_same_trans; eassumption.
  Qed.

  Hypothesis Hfree : fd_lookup fds (alloc_fd fds) = None.

  Context {FM : FsMayFail SC}.

  Theorem rz_openat_dot_lazy : forall p KA KB,
    path_at_lazy p -> path_is_dirref p = true ->
    (forall e msF' mo', In e openat_errnos ->
       lzok segs L S Zr (mkCfg msF' mo') -> same_but_materialized mo mo' ->
       restrict L S msF' = post (errno_ret e) -> hid_same L S msF msF' -> realizes segs (mkCfg msF' mo') KA) ->
    (forall msF' mo',
       lzok segs L S Zr (mkCfg msF' mo') ->
       same_but_materialized (with_fds (fd_insert fds (alloc_fd fds) FdDir) mo) mo' ->
       restrict L S msF' = post (alloc_fd fds) -> hid_same L S msF msF' -> realizes segs (mkCfg msF' mo') KB) ->
    realizes segs (mkCfg msF mo) (t_alt2 KA KB).
  Proof.
    intros p KA KB Hp Hdr HA HB.
    eapply rz_sys_lazy; [exact Hok | exact Hr | exact HF | exact HE |].
    intros msF1 Hok1 Hr1 Hsvc1 Hhs1.
    destruct (path_full msF1 Hr1 p Hp) as (HrdF & Hvis & Hcs & Hreads).
    apply (rz_open_lazy msF1 Hok1 Hr1 Hsvc1 (length p + 1) (fun fd => with_fds (fd_insert fds fd FdDir) mo) KA KB).
    - apply family_off_openat_false. rewrite in_sysno_si, H17. apply u64_lit. lia.
    - intros o. rewrite (openat_spec_head_lazy msF1 Hr1).
      rewrite (openat_dot_outcome _ _ _ _ mo open_flags_modeled_lazy eq_refl Hfl p o Hcs Hdr), Hreads. reflexivity.
    - intros fd. reflexivity.
    - intros fd. cbv delta [fds]. rewrite with_fds_halted'. exact (lzok_halted Hok).
    - exact Hfree.
    - exact Hvis.
    - intros e msF' mo' He Hok' Hsame Hr' Hhs'. apply (HA e msF' mo' He Hok' Hsame Hr'). eapply hid_same_trans; eassumption.
    - intros msF' mo' Hok' Hsame Hr' Hhs'. apply (HB msF' mo' Hok' Hsame Hr'). eapply hid_same_trans; eassumption.
  Qed.

  Theorem rz_openat_file_lazy : forall p d KA KB,
    path_at_lazy p -> p <> [] -> path_has_slash p = false -> path_is_dirref p = false ->
    fs_lookup (m_fs mo) p = Some d ->
    (forall e msF' mo', In e openat_errnos ->
       lzok segs L S Zr (mkCfg msF' mo') -> same_but_materialized mo mo' ->
       restrict L S msF' = post (errno_ret e) -> hid_same L S msF msF' -> realizes segs (mkCfg msF' mo') KA) ->
    (forall msF' mo',
       lzok segs L S Zr (mkCfg msF' mo') ->
       same_but_materialized (with_fds (fd_insert fds (alloc_fd fds) (FdFile p (Z_to_bv 64 0))) mo) mo' ->
       restrict L S msF' = post (alloc_fd fds) -> hid_same L S msF msF' -> realizes segs (mkCfg msF' mo') KB) ->
    realizes segs (mkCfg msF mo) (t_alt2 KA KB).
  Proof.
    intros p d KA KB Hp Hne Hsl Hnd Hfs HA HB.
    eapply rz_sys_lazy; [exact Hok | exact Hr | exact HF | exact HE |].
    intros msF1 Hok1 Hr1 Hsvc1 Hhs1.
    destruct (path_full msF1 Hr1 p Hp) as (HrdF & Hvis & Hcs & Hreads).
    apply (rz_open_lazy msF1 Hok1 Hr1 Hsvc1 (length p + 1) (fun fd => with_fds (fd_insert fds fd (FdFile p (Z_to_bv 64 0))) mo) KA KB).
    - apply family_off_openat_false. rewrite in_sysno_si, H17. apply u64_lit. lia.
    - intros o. rewrite (openat_spec_head_lazy msF1 Hr1).
      rewrite (openat_file_outcome _ _ _ _ mo open_flags_modeled_lazy eq_refl Hfl p d o Hcs Hne Hsl Hnd Hfs), Hreads. reflexivity.
    - intros fd. reflexivity.
    - intros fd. cbv delta [fds]. rewrite with_fds_halted'. exact (lzok_halted Hok).
    - exact Hfree.
    - exact Hvis.
    - intros e msF' mo' He Hok' Hsame Hr' Hhs'. apply (HA e msF' mo' He Hok' Hsame Hr'). eapply hid_same_trans; eassumption.
    - intros msF' mo' Hok' Hsame Hr' Hhs'. apply (HB msF' mo' Hok' Hsame Hr'). eapply hid_same_trans; eassumption.
  Qed.
End OpenatLazy.

Lemma range_visible_8_8 : forall hid (a : word),
  range_visible hid a 8 -> range_visible hid (Z_to_bv 64 (bv_unsigned a + 8)) 8 -> range_visible hid a 16.
Proof.
  intros hid a H1 H2 i Hi. destruct (Nat.lt_ge_cases i 8) as [Hlt|Hge].
  - apply H1. exact Hlt.
  - replace (a + Z_to_bv 64 (Z.of_nat i)) with (Z_to_bv 64 (bv_unsigned a + 8) + Z_to_bv 64 (Z.of_nat (i - 8))).
    + apply H2. lia.
    + apply bv_eq. rewrite !bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64)%Z.
      rewrite (Z.mod_small (Z.of_nat (i - 8))) by lia. rewrite (Z.mod_small (Z.of_nat i)) by lia.
      rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.

Lemma iov_array_full : forall L S mF iov iovs,
  lazy_ranges_okb segs L = true ->
  iov_array segs (restrict_mem L S mF) iov iovs ->
  iov_array segs mF iov iovs
  /\ (forall rom x8 regs pc a n, In (a, n) (copy_iovecs_accesses
        (ms_read_byte {| ms_regs := regs; ms_fregs := dfp_regs; ms_pc_val := pc; ms_svc_pending := x8;
                         ms_resv := None; ms_fcsr := dfp_csr; ms_mem := mF; ms_rom := rom |}) iov (length iovs)) ->
        rom = seg_rom segs -> range_visible (hiddenb L S) a n).
Proof.
  intros L S mF iov iovs HL. revert iov. induction iovs as [|[b n] r IH]; intros iov Ha.
  - split; [exact I|]. intros rom x8 regs pc a k [].
  - destruct Ha as (Hb & Hn & Hlt & Hr).
    destruct (rdn_restrict L S mF _ _ _ HL Hb) as [HbF Vb]. destruct (rdn_restrict L S mF _ _ _ HL Hn) as [HnF Vn].
    destruct (IH _ Hr) as [HrF Hvis]. split; [repeat split; assumption|].
    intros rom x8 regs pc a k Hin ->. cbn [copy_iovecs_accesses length] in Hin.
    destruct Hin as [Hin | Hin].
    + injection Hin as <- <-. apply range_visible_8_8; assumption.
    + set (ms := {| ms_regs := regs; ms_fregs := dfp_regs; ms_pc_val := pc; ms_svc_pending := x8;
                     ms_resv := None; ms_fcsr := dfp_csr; ms_mem := mF; ms_rom := seg_rom segs |}) in *.
      unfold read_iovec_entry in Hin.
      rewrite (read_u64_rdn segs ms iov b eq_refl HbF) in Hin.
      rewrite bv_add_Zform in Hin. change (bv_unsigned (8 : word)) with 8%Z in Hin.
      rewrite (read_u64_rdn segs ms _ n eq_refl HnF) in Hin.
      rewrite (proj2 (Z.leb_gt _ _) Hlt) in Hin.
      rewrite bv_add_Zform in Hin. change (bv_unsigned (16 : word)) with 16%Z in Hin.
      eapply Hvis; [exact Hin | reflexivity].
Qed.

Lemma iov_bufs_full : forall L S mF iovs bss,
  lazy_ranges_okb segs L = true ->
  iov_bufs segs (restrict_mem L S mF) iovs bss ->
  iov_bufs segs mF iovs bss
  /\ (forall k a n, In (a, n) (iov_prefix_accesses iovs k) -> range_visible (hiddenb L S) a n).
Proof.
  intros L S mF iovs bss HL. revert bss. induction iovs as [|[b n] r IH]; intros [|bs bss] Hb; cbn in Hb; try contradiction.
  - split; [exact I|]. intros k a m Hin. destruct k; cbn in Hin; destruct Hin.
  - destruct Hb as [H1 H2]. destruct (rdn_restrict L S mF _ _ _ HL H1) as [H1F V1]. destruct (IH bss H2) as [H2F Hvis].
    split; [cbn; auto|].
    intros k a m. revert a m. induction k as [|k IHk]; intros a m Hin.
    + cbn in Hin. destruct Hin.
    + cbn [iov_prefix_accesses] in Hin. rewrite !word_to_nat_bounded_eq_min in Hin.
      destruct (Nat.eqb (Nat.min (word_to_nat n) (Datatypes.S k)) 0) eqn:E.
      * exact (Hvis _ _ _ Hin).
      * destruct Hin as [Hin|Hin].
        -- injection Hin as <- <-. intros i Hi. apply V1. lia.
        -- exact (Hvis _ _ _ Hin).
Qed.

Lemma rz_writev_pending_lazy : forall L S Zr msF1 regs pc mem mo (fd : Z) (iov : word) iovs bss (T : nat -> TSet),
  lzok segs L S Zr (mkCfg msF1 mo) ->
  restrict L S msF1 = epend regs pc mem (seg_rom segs) (getr regs 17) ->
  ms_svc_pending msF1 = Some (getr regs 17) ->
  fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  (0 < fd < 2^31)%Z ->
  getr regs 17 = Z_to_bv 64 66 ->
  getr regs 10 = Z_to_bv 64 fd ->
  getr regs 11 = iov ->
  getr regs 12 = Z_to_bv 64 (Z.of_nat (length iovs)) ->
  (1 <= length iovs <= 1024)%nat ->
  iov_array segs mem iov iovs ->
  iov_bufs segs mem iovs bss ->
  (bv_unsigned iov + 16 * Z.of_nat (length iovs) <= TASK_SIZE)%Z ->
  iov_ranges_ok iovs ->
  let bs := concat bss in
  (1 <= iovs_total iovs)%Z -> (iovs_total iovs <= 2 ^ 30)%Z ->
  (forall k msF' mo', (1 <= k)%nat -> (k <= length bs)%nat ->
     lzok segs L S Zr (mkCfg msF' mo') -> same_but_materialized mo mo' ->
     restrict L S msF' = mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat k))) (v_addi pc 4) mem (seg_rom segs) ->
     hid_same L S msF1 msF' ->
     realizes segs (mkCfg msF' mo') (T k)) ->
  realizes segs (mkCfg msF1 mo)
    (t_alt (fun i : wr_index bs => t_emit (map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) bs)) (T (proj1_sig i)))).
Proof.
  intros L S Zr msF1 regs pc mem mo fd iov iovs bss T Hok1 Hr1 Hsvc1 Hfd Hfdr H17 H10 H11 H12 Hcnt Harr Hbufs Hiov Hrng bs Ht1 Ht30 Hk.
  destruct msF1 as [rg fr pcv svc rv fc mF rom].
  unfold restrict, restrict_by, with_mem, epend in Hr1. cbn in Hr1.
  injection Hr1 as Erg Efr Epc Esvc Erv Efc Emm Erom. subst rg fr pcv svc rv fc rom.
  change (restrict_mem_by (hiddenb L S) mF) with (restrict_mem L S mF) in Emm. subst mem.
  set (ms := {| ms_regs := regs; ms_fregs := dfp_regs; ms_pc_val := pc; ms_svc_pending := Some (getr regs 17);
                 ms_resv := None; ms_fcsr := dfp_csr; ms_mem := mF; ms_rom := seg_rom segs |}) in *.
  destruct (iov_array_full L S mF iov iovs (lzok_ranges Hok1) Harr) as [HarrF HvisA].
  destruct (iov_bufs_full L S mF iovs bss (lzok_ranges Hok1) Hbufs) as [HbufsF HvisB].
  assert (Hno : bv_unsigned (getr regs 17) = 66%Z) by (rewrite H17; apply u64_lit; lia).
  destruct (writev_outcome segs ms (getr regs 17) mo fd iov iovs bss eq_refl Hfd Hfdr Hno H10 H11 H12 Hcnt HarrF HbufsF Hiov Hrng Ht1 Ht30)
    as [Hlen Hchk]. fold bs in Hlen, Hchk.
  set (CA := import_iovecs_accesses (ms_read_byte ms) iov (Z_to_bv 64 (Z.of_nat (length iovs)))) in *.
  assert (Hnb : (1 <= length bs)%nat) by lia.

  assert (HvisCA : forall a n, In (a, n) CA -> range_visible (hiddenb L S) a n).
  { intros a n Hin. unfold CA in Hin.
    destruct iovs as [|[b1 n1] [|e2 r]]; [cbn in Hcnt; lia | |].
    - change (Z_to_bv 64 (Z.of_nat (length [(b1, n1)]))) with (Z_to_bv 64 1) in Hin.
      rewrite (proj2 (import_iovecs_of_array1 segs ms b1 n1 iov eq_refl HarrF
                        ltac:(cbn [length] in Hiov; lia) (proj1 Hrng))) in Hin.
      destruct Hin as [Hin|[]]. injection Hin as <- <-.
      destruct Harr as (Hb & Hn & _ & _).
      apply range_visible_8_8;
        [exact (proj2 (rdn_restrict L S mF _ _ _ (lzok_ranges Hok1) Hb))
        | exact (proj2 (rdn_restrict L S mF _ _ _ (lzok_ranges Hok1) Hn))].
    - rewrite (proj2 (import_iovecs_of_array segs ms _ iov eq_refl HarrF
                        ltac:(cbn [length] in *; lia) Hiov Hrng)) in Hin.
      eapply (HvisA (seg_rom segs) (Some (getr regs 17)) regs pc); [exact Hin | reflexivity]. }
  pose (effs := fun i : wr_index bs =>
          mkEffectU (Z_to_bv 64 (Z.of_nat (proj1_sig i))) [] [] [] [] (CA ++ iov_prefix_accesses iovs (proj1_sig i))).
  assert (Hvis : forall i, ranges_visible (hiddenb L S) (syscall_effect_accesses (effs i))).
  { intros [k Hk'] a n Hin. unfold effs, syscall_effect_accesses in Hin. cbn [proj1_sig eff_copyins eff_writes write_accesses] in Hin.
    rewrite app_nil_r in Hin. apply in_app_iff in Hin. destruct Hin as [Hin|Hin].
    - exact (HvisCA a n Hin).
    - exact (HvisB k a n Hin). }
  assert (Hstep : forall i, exists mo', materialize_model_accesses mo (syscall_effect_accesses (effs i)) = Some mo'
             /\ same_but_materialized mo mo'
             /\ lzok segs L S Zr (mkCfg (advance_past_svc (apply_effect ms (effs i))) mo')
             /\ hid_same L S ms (advance_past_svc (apply_effect ms (effs i)))).
  { intros i. apply (lzok_after_fd_op L S Zr ms mo mo (effs i) Hok1 eq_refl (lzok_halted Hok1) (Hvis i)).
    intros a Ha. unfold effs. destruct ms; reflexivity. }
  assert (Hch : exists f : wr_index bs -> Model, forall i,
             materialize_model_accesses mo (syscall_effect_accesses (effs i)) = Some (f i)
             /\ same_but_materialized mo (f i)
             /\ lzok segs L S Zr (mkCfg (advance_past_svc (apply_effect ms (effs i))) (f i))
             /\ hid_same L S ms (advance_past_svc (apply_effect ms (effs i)))).
  { exists (fun i => match materialize_model_accesses mo (syscall_effect_accesses (effs i)) with Some m => m | None => mo end).
    intros i. destruct (Hstep i) as (mo' & E & H1 & H2 & H3). rewrite E. auto. }
  destruct Hch as (f & Hf).
  apply (rz_node segs (mkCfg ms mo) (wr_index bs)
           (fun i => map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) bs))
           (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (f i))
           (fun i => T (proj1_sig i)) (wr_full bs Hnb)).
  - apply (node_family_mat segs ms mo (getr regs 17) (wr_index bs) effs (fun _ => mo) f
             (fun i => map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) bs)) _ (lzok_halted Hok1) eq_refl Hchk).
    + intros [k Hk']. exists k. split; [exact Hk'|reflexivity].
    + intros i0. apply not_spurious_none. rewrite in_sysno_si, Hno. apply injected_arm_none_66.
    + intros o (k & Hk' & ->). exists (exist _ k Hk'). reflexivity.
    + intros _. exact (lzok_halted Hok1).
    + intros i. exact (proj1 (Hf i)).
  - intros [k [Hk1 Hk2]]. cbn [proj1_sig]. destruct (Hf (exist _ k (conj Hk1 Hk2))) as (_ & Hs & Ho & Hh).
    cbn [proj1_sig] in Hs, Ho, Hh. apply (Hk k _ _ Hk1 Hk2 Ho Hs); [|exact Hh].
    unfold effs. cbn [proj1_sig].
    transitivity (restrict L S (advance_past_svc (apply_effect ms (with_copyins (CA ++ iov_prefix_accesses iovs k)
                     (mkEffect (Z_to_bv 64 (Z.of_nat k)) [] []))))); [reflexivity|].
    rewrite <- (restrict_adv_ret L S ms regs pc (restrict_mem L S mF) (getr regs 17) (Z_to_bv 64 (Z.of_nat k))
                  (CA ++ iov_prefix_accesses iovs k)); reflexivity.
Qed.

Theorem rz_writev2_lazy : forall L S Zr msF regs (pc : word) mem mo w (fd : Z) (iov b1 n1 b2 n2 : word) bs1 bs2 (T : nat -> TSet),
  fetch_word segs pc = Some w -> is_ecall w = true ->
  lzok segs L S Zr (mkCfg msF mo) ->
  restrict L S msF = mkst regs pc mem (seg_rom segs) ->
  fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  (0 < fd < 2^31)%Z ->
  getr regs 17 = Z_to_bv 64 66 ->
  getr regs 10 = Z_to_bv 64 fd ->
  getr regs 11 = iov ->
  getr regs 12 = Z_to_bv 64 2 ->
  rdn segs mem iov 8%nat = Some (word_to_le_bytes 8 b1) ->
  rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 8)) 8%nat = Some (word_to_le_bytes 8 n1) ->
  rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 16)) 8%nat = Some (word_to_le_bytes 8 b2) ->
  rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 24)) 8%nat = Some (word_to_le_bytes 8 n2) ->
  rdn segs mem b1 (word_to_nat n1) = Some bs1 ->
  rdn segs mem b2 (word_to_nat n2) = Some bs2 ->
  (bv_unsigned iov + 32 <= TASK_SIZE)%Z ->
  (bv_unsigned b1 + bv_unsigned n1 <= TASK_SIZE)%Z ->
  (bv_unsigned b2 + bv_unsigned n2 <= TASK_SIZE)%Z ->
  (1 <= bv_unsigned n1 + bv_unsigned n2)%Z ->
  (bv_unsigned n1 + bv_unsigned n2 <= 2 ^ 30)%Z ->
  (forall k msF' mo', (1 <= k)%nat -> (k <= length (bs1 ++ bs2))%nat ->
     lzok segs L S Zr (mkCfg msF' mo') -> same_but_materialized mo mo' ->
     restrict L S msF' = mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat k))) (v_addi pc 4) mem (seg_rom segs) ->
     hid_same L S msF msF' ->
     realizes segs (mkCfg msF' mo') (T k)) ->
  realizes segs (mkCfg msF mo)
    (t_alt (fun i : wr_index (bs1 ++ bs2) =>
       t_emit (map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) (bs1 ++ bs2))) (T (proj1_sig i)))).
Proof.
  intros L S Zr msF regs pc mem mo w fd iov b1 n1 b2 n2 bs1 bs2 T HF HE Hok Hr Hfd Hfdr H17 H10 H11 H12
         Rb1 Rn1 Rb2 Rn2 Rs1 Rs2 Hiov Hrg1 Hrg2 Ht1 Ht30 Hk.
  eapply rz_sys_lazy; [exact Hok | exact Hr | exact HF | exact HE |].
  intros msF1 Hok1 Hr1 Hsvc1 Hhs1.
  pose proof (u64_range n1). pose proof (u64_range n2).
  replace (bs1 ++ bs2) with (concat [bs1; bs2]) in * by (cbn; rewrite app_nil_r; reflexivity).
  eapply (rz_writev_pending_lazy L S Zr msF1 regs pc mem mo fd iov [(b1, n1); (b2, n2)] [bs1; bs2] T);
    [exact Hok1 | exact Hr1 | exact Hsvc1 | exact Hfd | exact Hfdr | exact H17 | exact H10 | exact H11 | exact H12
    | cbn; lia | | | cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; lia | cbn [iov_ranges_ok]; repeat split; assumption
    | cbn [iovs_total]; lia | cbn [iovs_total]; lia | ].
  - cbn [iov_array].
    replace (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned iov + 16)) + 8)) with (Z_to_bv 64 (bv_unsigned iov + 24)).
    2:{ change (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned iov + 16)) + 8)) with (at_ (at_ iov 16) 8).
        rewrite at_at. reflexivity. }
    repeat split; try assumption; lia.
  - cbn [iov_bufs]. repeat split; assumption.
  - intros k msF' mo' Hk1 Hk2 Hok' Hsame Hr' Hhs'. apply (Hk k msF' mo' Hk1 Hk2 Hok' Hsame Hr').
    eapply hid_same_trans; eassumption.
Qed.

Theorem rz_writev1_lazy : forall L S Zr msF regs (pc : word) mem mo w (fd : Z) (iov b1 n1 : word) bs1 (T : nat -> TSet),
  fetch_word segs pc = Some w -> is_ecall w = true ->
  lzok segs L S Zr (mkCfg msF mo) ->
  restrict L S msF = mkst regs pc mem (seg_rom segs) ->
  fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  (0 < fd < 2^31)%Z ->
  getr regs 17 = Z_to_bv 64 66 ->
  getr regs 10 = Z_to_bv 64 fd ->
  getr regs 11 = iov ->
  getr regs 12 = Z_to_bv 64 1 ->
  rdn segs mem iov 8%nat = Some (word_to_le_bytes 8 b1) ->
  rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 8)) 8%nat = Some (word_to_le_bytes 8 n1) ->
  rdn segs mem b1 (word_to_nat n1) = Some bs1 ->
  (bv_unsigned iov + 16 <= TASK_SIZE)%Z ->
  (bv_unsigned b1 + bv_unsigned n1 <= TASK_SIZE)%Z ->
  (1 <= bv_unsigned n1)%Z -> (bv_unsigned n1 <= 2 ^ 30)%Z ->
  (forall k msF' mo', (1 <= k)%nat -> (k <= length bs1)%nat ->
     lzok segs L S Zr (mkCfg msF' mo') -> same_but_materialized mo mo' ->
     restrict L S msF' = mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat k))) (v_addi pc 4) mem (seg_rom segs) ->
     hid_same L S msF msF' ->
     realizes segs (mkCfg msF' mo') (T k)) ->
  realizes segs (mkCfg msF mo)
    (t_alt (fun i : wr_index bs1 => t_emit (map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) bs1)) (T (proj1_sig i)))).
Proof.
  intros L S Zr msF regs pc mem mo w fd iov b1 n1 bs1 T HF HE Hok Hr Hfd Hfdr H17 H10 H11 H12 Rb1 Rn1 Rs1 Hiov Hrg1 Ht1 Ht30 Hk.
  eapply rz_sys_lazy; [exact Hok | exact Hr | exact HF | exact HE |].
  intros msF1 Hok1 Hr1 Hsvc1 Hhs1.
  pose proof (u64_range n1).
  replace bs1 with (concat [bs1]) in Hk by (cbn; rewrite app_nil_r; reflexivity).
  replace bs1 with (concat [bs1]) by (cbn; rewrite app_nil_r; reflexivity).
  eapply (rz_writev_pending_lazy L S Zr msF1 regs pc mem mo fd iov [(b1, n1)] [bs1] T);
    [exact Hok1 | exact Hr1 | exact Hsvc1 | exact Hfd | exact Hfdr | exact H17 | exact H10 | exact H11 | exact H12
    | cbn; lia | | | cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; lia | cbn [iov_ranges_ok]; repeat split; assumption
    | cbn [iovs_total]; lia | cbn [iovs_total]; lia | ].
  - cbn [iov_array]. repeat split; try assumption; lia.
  - cbn [iov_bufs]. split; [assumption | exact I].
  - intros k msF' mo' Hk1 Hk2 Hok' Hsame Hr' Hhs'. apply (Hk k msF' mo' Hk1 Hk2 Hok' Hsame Hr').
    eapply hid_same_trans; eassumption.
Qed.

Theorem rz_writev2_wall_lazy : forall L S Zr msF regs (pc : word) mem mo w (fd : Z) (iov b1 n1 b2 n2 : word) bs1 bs2 (K : TSet),
  fetch_word segs pc = Some w -> is_ecall w = true ->
  lzok segs L S Zr (mkCfg msF mo) ->
  restrict L S msF = mkst regs pc mem (seg_rom segs) ->
  fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  (0 < fd < 2^31)%Z ->
  getr regs 17 = Z_to_bv 64 66 ->
  getr regs 10 = Z_to_bv 64 fd ->
  getr regs 11 = iov ->
  getr regs 12 = Z_to_bv 64 2 ->
  rdn segs mem iov 8%nat = Some (word_to_le_bytes 8 b1) ->
  rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 8)) 8%nat = Some (word_to_le_bytes 8 n1) ->
  rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 16)) 8%nat = Some (word_to_le_bytes 8 b2) ->
  rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 24)) 8%nat = Some (word_to_le_bytes 8 n2) ->
  rdn segs mem b1 (word_to_nat n1) = Some bs1 ->
  rdn segs mem b2 (word_to_nat n2) = Some bs2 ->
  (bv_unsigned iov + 32 <= TASK_SIZE)%Z ->
  (bv_unsigned b1 + bv_unsigned n1 <= TASK_SIZE)%Z ->
  (bv_unsigned b2 + bv_unsigned n2 <= TASK_SIZE)%Z ->
  (1 <= bv_unsigned n1 + bv_unsigned n2)%Z ->
  (bv_unsigned n1 + bv_unsigned n2 <= 2 ^ 30)%Z ->
  K [] ->
  (forall k msF' mo', (1 <= k)%nat -> (k <= length (bs1 ++ bs2))%nat ->
     lzok segs L S Zr (mkCfg msF' mo') -> same_but_materialized mo mo' ->
     restrict L S msF' = mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat k))) (v_addi pc 4) mem (seg_rom segs) ->
     hid_same L S msF msF' ->
     realizes segs (mkCfg msF' mo') (t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k (bs1 ++ bs2))) K)) ->
  realizes segs (mkCfg msF mo) (t_emit (map (WriteEv (Z_to_bv 64 fd)) (bs1 ++ bs2)) K).
Proof.
  intros L S Zr msF regs pc mem mo w fd iov b1 n1 b2 n2 bs1 bs2 K HF HE Hok Hr Hfd Hfdr H17 H10 H11 H12
         Rb1 Rn1 Rb2 Rn2 Rs1 Rs2 Hiov Hrg1 Hrg2 Ht1 Ht30 HK Hk.
  pose proof (rdn_length segs mem _ _ _ Rs1) as L1. pose proof (rdn_length segs mem _ _ _ Rs2) as L2.
  pose proof (u64_range n1). pose proof (u64_range n2).
  apply rz_wall; [rewrite length_app; unfold word_to_nat in L1, L2; lia | exact HK |].
  eapply (rz_writev2_lazy L S Zr msF regs pc mem mo w fd iov b1 n1 b2 n2 bs1 bs2
            (fun k => t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k (bs1 ++ bs2))) K)); eassumption.
Qed.

Theorem rz_writev1_wall_lazy : forall L S Zr msF regs (pc : word) mem mo w (fd : Z) (iov b1 n1 : word) bs1 (K : TSet),
  fetch_word segs pc = Some w -> is_ecall w = true ->
  lzok segs L S Zr (mkCfg msF mo) ->
  restrict L S msF = mkst regs pc mem (seg_rom segs) ->
  fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  (0 < fd < 2^31)%Z ->
  getr regs 17 = Z_to_bv 64 66 ->
  getr regs 10 = Z_to_bv 64 fd ->
  getr regs 11 = iov ->
  getr regs 12 = Z_to_bv 64 1 ->
  rdn segs mem iov 8%nat = Some (word_to_le_bytes 8 b1) ->
  rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 8)) 8%nat = Some (word_to_le_bytes 8 n1) ->
  rdn segs mem b1 (word_to_nat n1) = Some bs1 ->
  (bv_unsigned iov + 16 <= TASK_SIZE)%Z ->
  (bv_unsigned b1 + bv_unsigned n1 <= TASK_SIZE)%Z ->
  (1 <= bv_unsigned n1)%Z -> (bv_unsigned n1 <= 2 ^ 30)%Z ->
  K [] ->
  (forall k msF' mo', (1 <= k)%nat -> (k <= length bs1)%nat ->
     lzok segs L S Zr (mkCfg msF' mo') -> same_but_materialized mo mo' ->
     restrict L S msF' = mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat k))) (v_addi pc 4) mem (seg_rom segs) ->
     hid_same L S msF msF' ->
     realizes segs (mkCfg msF' mo') (t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k bs1)) K)) ->
  realizes segs (mkCfg msF mo) (t_emit (map (WriteEv (Z_to_bv 64 fd)) bs1) K).
Proof.
  intros L S Zr msF regs pc mem mo w fd iov b1 n1 bs1 K HF HE Hok Hr Hfd Hfdr H17 H10 H11 H12 Rb1 Rn1 Rs1 Hiov Hrg1 Ht1 Ht30 HK Hk.
  pose proof (rdn_length segs mem _ _ _ Rs1) as L1. pose proof (u64_range n1).
  apply rz_wall; [unfold word_to_nat in L1; lia | exact HK |].
  eapply (rz_writev1_lazy L S Zr msF regs pc mem mo w fd iov b1 n1 bs1
            (fun k => t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k bs1)) K)); eassumption.
Qed.

Theorem rz_writev1_zero_lazy : forall L S Zr msF regs (pc : word) mem mo w (fd : Z) (iov b1 : word) K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  lzok segs L S Zr (mkCfg msF mo) ->
  restrict L S msF = mkst regs pc mem (seg_rom segs) ->
  fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  (0 < fd < 2^31)%Z ->
  getr regs 17 = Z_to_bv 64 66 ->
  getr regs 10 = Z_to_bv 64 fd ->
  getr regs 11 = iov ->
  getr regs 12 = Z_to_bv 64 1 ->
  rdn segs mem iov 8%nat = Some (word_to_le_bytes 8 b1) ->
  rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 8)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  (bv_unsigned iov + 16 <= TASK_SIZE)%Z ->
  (bv_unsigned b1 <= TASK_SIZE)%Z ->
  (forall msF' mo', lzok segs L S Zr (mkCfg msF' mo') -> same_but_materialized mo mo' ->
     restrict L S msF' = mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) mem (seg_rom segs) ->
     hid_same L S msF msF' ->
     realizes segs (mkCfg msF' mo') K) ->
  realizes segs (mkCfg msF mo) K.
Proof.
  intros L S Zr msF regs pc mem mo w fd iov b1 K HF HE Hok Hr Hfd Hfdr H17 H10 H11 H12 Rb1 Rn1 Hiov Hb1 Hc.
  eapply rz_sys_lazy; [exact Hok | exact Hr | exact HF | exact HE |].
  intros msF1 Hok1 Hr1 Hsvc1 Hhs1.
  destruct msF1 as [rg fr pcv svc rv fc mF rom].
  unfold restrict, restrict_by, with_mem, epend in Hr1. cbn in Hr1.
  injection Hr1 as Erg Efr Epc Esvc Erv Efc Emm Erom. subst rg fr pcv svc rv fc rom.
  change (restrict_mem_by (hiddenb L S) mF) with (restrict_mem L S mF) in Emm.
  set (ms := {| ms_regs := regs; ms_fregs := dfp_regs; ms_pc_val := pc; ms_svc_pending := Some (getr regs 17);
                 ms_resv := None; ms_fcsr := dfp_csr; ms_mem := mF; ms_rom := seg_rom segs |}) in *.
  assert (Hno : bv_unsigned (getr regs 17) = 66%Z) by (rewrite H17; apply u64_lit; lia).
  assert (HarrV : iov_array segs (restrict_mem L S mF) iov [(b1, Z_to_bv 64 0)]).
  { rewrite Emm. cbn [iov_array]. refine (conj Rb1 (conj Rn1 (conj _ I))). rewrite u64_lit by lia. lia. }
  destruct (iov_array_full L S mF iov [(b1, Z_to_bv 64 0)] (lzok_ranges Hok1) HarrV) as [Harr _].
  destruct (import_iovecs_of_array1 segs ms b1 (Z_to_bv 64 0) iov eq_refl Harr Hiov
              ltac:(rewrite u64_lit by lia; lia)) as [Himp Hacc].
  eapply (rz_fd_det_lazy L S Zr ms mo (getr regs 17)
            (with_copyins (import_iovecs_accesses (ms_read_byte ms) iov (Z_to_bv 64 1)) (mkEffect (Z_to_bv 64 0) [] [])) mo);
    [exact Hok1 | reflexivity | | reflexivity | exact (lzok_halted Hok1) | | |].
  - intros o.
    rewrite (syscall_spec_66 (sys_input segs ms (getr regs 17)) mo o) by (rewrite in_sysno_si; exact Hno).
    rewrite in_arg0_si, in_arg1_si, in_arg2_si.
    change (ms_gpr ms 0) with (getr regs 10). change (ms_gpr ms 1) with (getr regs 11). change (ms_gpr ms 2) with (getr regs 12).
    rewrite H10, H11, H12. rewrite fd32_id by (rewrite u64_lit; lia).
    change (Z_to_bv 64 1) with (iovcnt32 (Z_to_bv 64 1)) at 2.
    change (ms_read_byte ms) with (in_mem (sys_input segs ms (getr regs 17))).
    apply (writev_chan_zero_outcome _ _ _ _ mo o (Z_to_bv 64 fd) [(b1, Z_to_bv 64 0)] Hfd).
    + apply w_is0_pos. rewrite u64_lit; lia.
    + rewrite in_mem_si. exact Himp.
    + cbn [iovs_total]. rewrite u64_lit by lia. reflexivity.
  - unfold syscall_effect_accesses, with_copyins. cbn [eff_copyins eff_writes write_accesses]. rewrite app_nil_r.
    rewrite Hacc. intros a n [Hin|[]]. injection Hin as <- <-.
    destruct HarrV as (Hb & Hn & _ & _).
    apply range_visible_8_8;
      [exact (proj2 (rdn_restrict L S mF _ _ _ (lzok_ranges Hok1) Hb))
      | exact (proj2 (rdn_restrict L S mF _ _ _ (lzok_ranges Hok1) Hn))].
  - intros a Ha. rewrite apply_effect_ret_copyins_mem. reflexivity.
  - intros mo' Hok' Hsame Hhs. apply (Hc _ mo' Hok' Hsame); [| eapply hid_same_trans; [exact Hhs1 | exact Hhs]].
    transitivity (restrict L S (advance_past_svc (apply_effect ms (with_copyins (import_iovecs_accesses (ms_read_byte ms) iov (Z_to_bv 64 1))
                     (mkEffect (Z_to_bv 64 0) [] []))))); [reflexivity|].
    rewrite <- Emm.
    rewrite <- (restrict_adv_ret L S ms regs pc (restrict_mem L S mF) (getr regs 17) (Z_to_bv 64 0)
                  (import_iovecs_accesses (ms_read_byte ms) iov (Z_to_bv 64 1))); reflexivity.
Qed.

Theorem rz_read_dir_mapped_lazy : forall L S Zr msF regs (pc : word) mem mo w fd (cnt : Z) K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  lzok segs L S Zr (mkCfg msF mo) ->
  restrict L S msF = mkst regs pc mem (seg_rom segs) ->
  getr regs 17 = Z_to_bv 64 63 ->
  getr regs 10 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
  fd_lookup (m_fds mo) fd = Some FdDir ->
  getr regs 12 = Z_to_bv 64 cnt ->
  (1 <= cnt)%Z -> (cnt <= 2 ^ 24)%Z ->
  (bv_unsigned (getr regs 11) + cnt <= TASK_SIZE)%Z ->
  store_ok segs mem (getr regs 11) (Z.to_nat cnt) = true ->
  (forall msF', lzok segs L S Zr (mkCfg msF' mo) ->
     restrict L S msF' = mkst (regupd regs 10 (errno_ret EISDIR)) (v_addi pc 4) mem (seg_rom segs) ->
     hid_same L S msF msF' ->
     realizes segs (mkCfg msF' mo) K) ->
  realizes segs (mkCfg msF mo) K.
Proof.
  intros L S Zr msF regs pc mem mo w fd cnt K HF HE Hok Hr H17 Hfd Hfd32 Hlk H12 Hc1 H64 Hover Hst Hc.
  eapply rz_sys_lazy; [exact Hok | exact Hr | exact HF | exact HE |].
  intros msF1 Hok1 Hr1 Hsvc1 Hhs1.
  pose proof (ms_gpr_of_restrict_epend L S msF1 regs pc mem (seg_rom segs) (getr regs 17)) as Hg.
  assert (Emem : restrict_mem L S (ms_mem msF1) = mem).
  { transitivity (ms_mem (restrict L S msF1)); [reflexivity|]. rewrite Hr1. reflexivity. }
  destruct (store_ok_restrictL L S (ms_mem msF1) (getr regs 11) (Z.to_nat cnt) (lzok_ranges Hok)
              ltac:(rewrite Emem; exact Hst)) as [HstF _].
  eapply (rz_fd_det_noacc_lazy L S Zr msF1 mo (getr regs 17) (mkEffect (errno_ret EISDIR) [] []) mo);
    [exact Hok1 | exact Hsvc1 | | reflexivity | exact (lzok_halted Hok) | reflexivity | |].
  - intros o. rewrite (syscall_spec_63 _ mo o) by (rewrite in_sysno_si, H17; apply u64_lit; lia).
    rewrite in_arg0_si, in_arg1_si, in_arg2_si, !(Hg _ Hr1), ms_gpr_epend0, ms_gpr_epend1, ms_gpr_epend2, Hfd, (fd32_id fd Hfd32).
    apply (read_dir_outcome fd _ _ _ mo o Hlk).

    apply access_okb_intro. rewrite H12, u64_lit by lia. exact Hover.
  - intros a Ha. rewrite apply_effect_ret_mem. reflexivity.
  - intros Hok' Hhs. apply Hc; [exact Hok' | | eapply hid_same_trans; [exact Hhs1 | exact Hhs]].
    rewrite <- (restrict_adv_ret L S msF1 regs pc mem (getr regs 17) (errno_ret EISDIR) [] Hr1). reflexivity.
Qed.

End WithSegs.
