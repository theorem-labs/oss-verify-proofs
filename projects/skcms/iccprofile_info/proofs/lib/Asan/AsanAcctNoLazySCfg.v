(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import DispatchCompute.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import
  SimInv ExitSim PropExec CatExec CatSim SeqExec Hoare StreamExec MmapSim AllocSim FileSim
  ShapeAlg SpinAlg DivergeSim Nodes StoreOk AgentLib AgentNodes RefNodes LibWritev
  AsanAcct AsanAcctShape AsanAcctNoLazy.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import SpinAlgCfg.
Unset Nia Cache.  (* [comment removed for export] *)
Import ListNotations.
Unset Lia Cache.
Open Scope bv_scope.

Section WithFP. Context {FP : PropExec.FPState}.

(* [comment removed for export] *)
Lemma srz_cfg_wall : forall segs c (ch : word) (bs : list byte) (K : TSet),
  (1 <= length bs)%nat -> K [] ->
  srealizes_cfg segs c (t_alt (fun i : wr_index bs =>
     t_emit (map (WriteEv ch) (firstn (proj1_sig i) bs))
            (t_emit (map (WriteEv ch) (skipn (proj1_sig i) bs)) K))) ->
  srealizes_cfg segs c (t_emit (map (WriteEv ch) bs) K).
Proof.
  intros segs c ch bs K Hnb HK H. eapply srz_cfg_conseq; [exact H | apply t_alt_wall; assumption].
Qed.


(* [comment removed for export] *)
Lemma srz_cfg_ret_only_copyins_silent_mat0 : forall segs ms model x8 reads r m' T,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model
               = check_ret_only_copyins reads eff r m' []) ->
  m_halted m' = None ->
  materialize_model_accesses m' reads = Some m' ->
  srealizes_cfg segs (mkCfg (advance_past_svc (set_gpr0 ms r)) m') T ->
  srealizes_cfg segs (mkCfg ms model) T.
Proof.
  intros segs ms model x8 reads r m' T Hh Hsvc Hchk Hh' Hmat Hc.
  eapply srz_cfg_silent1; [|exact Hc].
  rewrite <- (apply_effect_copyins_no_write ms r reads).
  pose proof (node_chk_ev_mat segs ms model x8 unit (fun _ => with_copyins reads (mkEffect r [] []))
           (fun _ => m') (fun _ => []) Hh Hsvc) as HN.
  rewrite node_ok_same in HN. apply HN.
  - intros []. rewrite Hchk. apply check_ret_only_copyins_ok_iff. auto.
  - intros eff m'' ev Hck. rewrite Hchk in Hck. apply check_ret_only_copyins_ok_iff in Hck as (-> & -> & ->).
    exists tt. auto.
  - intros eff. rewrite Hchk. apply check_ret_only_copyins_no_unmodeled.
  - intros []. exact Hh'.
  - intros []. unfold syscall_effect_accesses, with_copyins. cbn [eff_copyins eff_writes write_accesses].
    rewrite app_nil_r. exact Hmat.
Qed.

Section NoLazyS.
Variable segs : list Segment.
Variable H : word -> bool.
Hypothesis HH : H_off_segments segs H.
Hypothesis Hwx : wx_segs_nowrap segs.

Theorem srz_cfg_step_nolazy : forall ms msr' model T,
  lazy_all_hidden H model -> m_halted model = None -> ms_svc_pending ms = None ->
  RiscvSemantics.step segs (restrict H ms) = MachineOk msr' ->
  srealizes_cfg segs (mkCfg (unrestrict H (ms_mem ms) msr') model) T ->
  srealizes_cfg segs (mkCfg ms model) T.
Proof.
  intros ms msr' model T HL Hh Hsvc Hs Hk.
  destruct (node_instr_nolazy segs H HH Hwx ms msr' model HL Hh Hsvc Hs) as [_ Hnode].
  exact (srz_cfg_silent1 segs _ _ T Hnode Hk).
Qed.

Lemma srz_cfg_msteps_nolazy_ind : forall msr0 msr',
  msteps segs msr0 msr' ->
  forall ms model T,
  msr0 = restrict H ms ->
  lazy_all_hidden H model -> m_halted model = None ->
  srealizes_cfg segs (mkCfg (unrestrict H (ms_mem ms) msr') model) T ->
  srealizes_cfg segs (mkCfg ms model) T.
Proof.
  intros msr0 msr' Hms.
  induction Hms as [msr | msr msr1 msr2 Hsvc Hstep Hrest IH]; intros ms model T -> HL Hh Hk.
  - rewrite unrestrict_restrict in Hk. exact Hk.
  - rewrite restrict_svc_pending in Hsvc.
    destruct (node_instr_nolazy segs H HH Hwx ms msr1 model HL Hh Hsvc Hstep) as [Hcl1 Hnode].
    apply (srz_cfg_silent1 segs _ _ T Hnode).
    apply (IH (unrestrict H (ms_mem ms) msr1) model T).
    + symmetry. apply restrict_unrestrict_clean. exact Hcl1.
    + exact HL.
    + exact Hh.
    + rewrite unrestrict_mem, unrestrict_munrestrict. exact Hk.
Qed.

(* [comment removed for export] *)
Theorem srz_cfg_msteps_nolazy : forall ms msr' model T,
  lazy_all_hidden H model -> m_halted model = None ->
  msteps segs (restrict H ms) msr' ->
  srealizes_cfg segs (mkCfg (unrestrict H (ms_mem ms) msr') model) T ->
  srealizes_cfg segs (mkCfg ms model) T.
Proof.
  intros ms msr' model T HL Hh Hms Hk.
  exact (srz_cfg_msteps_nolazy_ind _ _ Hms ms model T eq_refl HL Hh Hk).
Qed.

(* [comment removed for export] *)
Theorem srz_cfg_msteps_R : forall F regs pc mr regs' pc' mr' rom model T,
  lazy_all_hidden H model -> m_halted model = None ->
  mclean H mr ->
  msteps segs (mkst regs pc mr rom) (mkst regs' pc' mr' rom) ->
  (mclean H mr' -> srealizes_cfg segs (mkCfg (mkst regs' pc' (munrestrict H F mr') rom) model) T) ->
  srealizes_cfg segs (mkCfg (mkst regs pc (munrestrict H F mr) rom) model) T.
Proof.
  intros F regs pc mr regs' pc' mr' rom model T HL Hh Hc Hms Hk.
  apply (srz_cfg_msteps_nolazy (mkst regs pc (munrestrict H F mr) rom) (mkst regs' pc' mr' rom) model T HL Hh).
  - rewrite (restrict_mkst_munrestrict H F regs pc mr rom Hc). exact Hms.
  - cbn [ms_mem mkst]. rewrite unrestrict_mkst, munrestrict_munrestrict_mem. apply Hk.
    apply (hclean_mkst H regs' pc' mr' rom).
    apply (msteps_hclean segs H HH Hwx _ _ Hms). apply (hclean_mkst H regs pc mr rom). exact Hc.
Qed.

(* [comment removed for export] *)
Theorem srz_cfg_sys_R : forall regs pc M rom model w T,
  lazy_all_hidden H model -> m_halted model = None ->
  fetch_word segs pc = Some w -> is_ecall w = true ->
  srealizes_cfg segs (mkCfg (epend regs pc M rom (getr regs 17)) model) T ->
  srealizes_cfg segs (mkCfg (mkst regs pc M rom) model) T.
Proof.
  intros regs pc M rom model w T HL Hh HF HE Hk.
  apply (srz_cfg_step_nolazy (mkst regs pc M rom) (epend regs pc (mrestrict H M) rom (getr regs 17)) model T HL Hh eq_refl).
  - rewrite restrict_mkst. apply (step_ecall_epend segs regs pc (mrestrict H M) rom w HF HE).
  - cbn [ms_mem mkst]. rewrite unrestrict_epend, munrestrict_mrestrict. exact Hk.
Qed.

(* [comment removed for export] *)
Theorem srz_cfg_exit_at_R : forall regs (pc : word) M rom model w code,
  lazy_all_hidden H model -> m_halted model = None ->
  fetch_word segs pc = Some w -> is_ecall w = true ->
  (getr regs 17 = Z_to_bv 64 94 \/ getr regs 17 = Z_to_bv 64 93) ->
  getr regs 10 = code ->
  srealizes_cfg segs (mkCfg (mkst regs pc M rom) model)
           (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model)).
Proof.
  intros regs pc M rom model w code HL Hh HF HE H17 H10.
  eapply srz_cfg_sys_R; [exact HL | exact Hh | exact HF | exact HE |].
  rewrite <- H10, <- (ms_gpr_epend0 regs pc M rom (getr regs 17)).
  eapply srz_cfg_exit; [exact Hh | reflexivity |].
  destruct H17 as [H7|H7]; [right|left]; rewrite H7; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma srz_cfg_writev_pending_R : forall ms x8 model (fd : Z) (iov : word) iovs bss (T : nat -> TSet),
  ms_rom ms = seg_rom segs ->
  lazy_all_hidden H model -> m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  (0 < fd < 2^31)%Z ->
  bv_unsigned x8 = 66%Z ->
  ms_gpr ms 0 = Z_to_bv 64 fd ->
  ms_gpr ms 1 = iov ->
  ms_gpr ms 2 = Z_to_bv 64 (Z.of_nat (length iovs)) ->
  (1 <= length iovs <= 1024)%nat ->
  (bv_unsigned iov + 16 * Z.of_nat (length iovs) <= TASK_SIZE)%Z ->   (* [comment removed for export] *)
  iov_array segs (ms_mem ms) iov iovs ->
  iov_bufs_ok iovs ->                                                 (* [comment removed for export] *)
  iov_bufs segs (ms_mem ms) iovs bss ->
  range_avoids H iov (16 * length iovs) ->
  (forall b n, In (b, n) iovs -> range_avoids H b (word_to_nat n)) ->
  let bs := concat bss in
  (1 <= iovs_total iovs)%Z -> (iovs_total iovs <= 2 ^ 30)%Z -> (iovs_total iovs <= 2 ^ 30)%Z ->
  (forall k, (1 <= k)%nat -> (k <= length bs)%nat ->
     srealizes_cfg segs (mkCfg (advance_past_svc (set_gpr0 ms (Z_to_bv 64 (Z.of_nat k)))) model) (T k)) ->
  srealizes_cfg segs (mkCfg ms model)
    (t_alt (fun i : wr_index bs => t_emit (map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) bs)) (T (proj1_sig i)))).
Proof.
  intros ms x8 model fd iov iovs bss T Hrom HL Hh Hsvc Hfd Hfdr Hno H0 H1 H2 Hcnt Hiok Harr Hbok Hbufs Haviov Havbuf
         bs Ht1 Htmax Ht30 Hk.
  destruct (writev_check segs ms x8 model fd iov iovs bss Hrom Hfd Hfdr Hno H0 H1 H2 Hcnt Hiok Harr Hbok Hbufs Ht1 Htmax Ht30)
    as [Hlen Hchk]. fold bs in Hlen, Hchk.
  set (tot := iovs_total iovs) in *.
  set (CA := import_iovecs_accesses (ms_read_byte ms) iov (Z_to_bv 64 (Z.of_nat (length iovs)))) in *.
  assert (HCA : ranges_avoid H CA).
  { subst CA. rewrite (import_iovecs_accesses_copy _ iov (length iovs) Hcnt Hiok).
    rewrite (copy_iovecs_accesses_of_array segs ms iovs iov Hrom Harr).
    intros a n Hin. apply in_map_iff in Hin as (i & E & Hi). injection E as <- <-.
    apply in_seq in Hi.
    replace (16 * Z.of_nat i)%Z with (Z.of_nat (16 * i)) by lia.
    apply (range_avoids_sub H iov (16 * length iovs)); [exact Haviov | lia | lia]. }
  assert (Hnb : (1 <= length bs)%nat) by lia.
  pose (effs := fun i : wr_index bs =>
          mkEffectU (Z_to_bv 64 (Z.of_nat (proj1_sig i))) [] [] [] []
                    (CA ++ iov_prefix_accesses iovs (proj1_sig i))).
  assert (Enx : forall i : wr_index bs,
    mkCfg (advance_past_svc (set_gpr0 ms (Z_to_bv 64 (Z.of_nat (proj1_sig i))))) model
    = mkCfg (advance_past_svc (apply_effect ms (effs i))) model).
  { intros [k Hk']. cbn [proj1_sig]. unfold effs. cbn [proj1_sig].
    rewrite <- (apply_effect_copyins_no_write ms (Z_to_bv 64 (Z.of_nat k)) (CA ++ iov_prefix_accesses iovs k)).
    reflexivity. }
  apply (srz_cfg_node_na segs (mkCfg ms model) (wr_index bs)
           (fun i => map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) bs))
           (fun i => mkCfg (advance_past_svc (set_gpr0 ms (Z_to_bv 64 (Z.of_nat (proj1_sig i))))) model)
           (fun i => T (proj1_sig i)) (wr_full bs Hnb)).
  1:{ exact (nonalloc_no segs ms model x8 Hsvc ltac:(rewrite Hno; reflexivity)). }   (* [comment removed for export] *)
  2:{ intros [k [Hk1 Hk2]]. cbn [proj1_sig]. apply Hk; assumption. }
  assert (Hku : forall k, (k <= length bs)%nat -> bv_unsigned (Z_to_bv 64 (Z.of_nat k)) = Z.of_nat k).
  { intros k Hk2. apply u64_lit. lia. }
  assert (Hmat : forall i : wr_index bs,
            materialize_model_accesses model (syscall_effect_accesses (effs i)) = Some model).
  { intros [k Hk']. apply (materialize_nolazy H model _ HL).
    unfold effs, syscall_effect_accesses. cbn [proj1_sig eff_copyins eff_writes write_accesses].
    rewrite app_nil_r. apply ranges_avoid_app; [exact HCA | apply (iov_prefix_accesses_avoid H); exact Havbuf]. }
  assert (Hok : forall i : wr_index bs,
            check_syscall (sys_input segs ms x8) (effs i) model
            = CheckOk model (map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) bs))).
  { intros [k [Hk1 Hk2]]. unfold effs. cbn [proj1_sig]. rewrite Hchk.
    rewrite (Hku k Hk2), Nat2Z.id.
    rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia.
    replace (addr_is_error_b (Z_to_bv 64 (Z.of_nat k))) with false
      by (symmetry; unfold addr_is_error_b, two_pow_64; apply Z.ltb_ge; rewrite (Hku k Hk2); lia).
    rewrite (proj2 (access_ranges_eqb_eq _ _) eq_refl). reflexivity. }
  split.
  - intros i. rewrite Enx. apply (sstep_of_check_mat segs ms model x8); [exact Hh | exact Hsvc | apply Hok | exact Hh | apply Hmat].
  - assert (Hinv : forall eff m' ev, check_syscall (sys_input segs ms x8) eff model = CheckOk m' ev ->
              exists i : wr_index bs, eff = effs i /\ m' = model /\ ev = map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) bs)).
    { intros [ret ws zs us cs ci] m' ev Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate].
      destruct cs; [|discriminate].
      destruct ((1 <=? bv_unsigned ret)%Z && (bv_unsigned ret <=? tot)%Z && negb (addr_is_error_b ret))%bool eqn:Eb;
        [|discriminate].
      destruct (access_ranges_eqb ci (CA ++ iov_prefix_accesses iovs (Z.to_nat (bv_unsigned ret)))) eqn:Eci;
        [|discriminate].
      injection Hc as <- <-.
      apply andb_true_iff in Eb as [Eb _]. apply andb_true_iff in Eb as [E1 E2].
      apply Z.leb_le in E1. apply Z.leb_le in E2. apply access_ranges_eqb_eq in Eci.
      assert (Hkr : (1 <= Z.to_nat (bv_unsigned ret))%nat /\ (Z.to_nat (bv_unsigned ret) <= length bs)%nat) by lia.
      exists (exist _ (Z.to_nat (bv_unsigned ret)) Hkr). cbn [proj1_sig]. unfold effs. cbn [proj1_sig].
      rewrite Z2Nat.id by lia. rewrite u64_roundtrip'. subst ci. repeat split; reflexivity. }
    intros e st Hss.
    destruct (sstep_svc_inv segs ms model x8 e st Hsvc Hss)
      as [(eff & model' & ev & Hc & [(m'' & Hh2 & -> & Hm & ->) | [(Hh2 & -> & Hm & ->) | (code & Hh2 & -> & ->)]])
         | (eff & Hc & -> & ->)].
    + destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->).
      rewrite (Hmat i) in Hm. injection Hm as <-.
      exists i. rewrite Enx. split; reflexivity.
    + destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->). rewrite (Hmat i) in Hm. discriminate.
    + destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->). congruence.
    + exfalso. rewrite Hchk in Hc. destruct eff as [ret ws zs us cs ci].
      destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate].
      destruct cs; [|discriminate]. destruct (_ && _)%bool; [destruct (access_ranges_eqb _ _)|]; discriminate.
Qed.

Lemma srz_cfg_writev2_R : forall F regs (pc : word) mr model w (fd : Z) (iov b1 n1 b2 n2 : word) bs1 bs2 (T : nat -> TSet),
  fetch_word segs pc = Some w -> is_ecall w = true ->
  lazy_all_hidden H model -> m_halted model = None -> mclean H mr ->
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  (0 < fd < 2^31)%Z ->
  getr regs 17 = Z_to_bv 64 66 ->
  getr regs 10 = Z_to_bv 64 fd ->
  getr regs 11 = iov ->
  getr regs 12 = Z_to_bv 64 2 ->
  rdn segs mr iov 8%nat = Some (word_to_le_bytes 8 b1) ->
  rdn segs mr (Z_to_bv 64 (bv_unsigned iov + 8)) 8%nat = Some (word_to_le_bytes 8 n1) ->
  rdn segs mr (Z_to_bv 64 (bv_unsigned iov + 16)) 8%nat = Some (word_to_le_bytes 8 b2) ->
  rdn segs mr (Z_to_bv 64 (bv_unsigned iov + 24)) 8%nat = Some (word_to_le_bytes 8 n2) ->
  rdn segs mr b1 (word_to_nat n1) = Some bs1 ->
  rdn segs mr b2 (word_to_nat n2) = Some bs2 ->
  (1 <= bv_unsigned n1 + bv_unsigned n2)%Z ->
  (bv_unsigned n1 + bv_unsigned n2 <= 2 ^ 30)%Z ->
  (bv_unsigned n1 + bv_unsigned n2 <= 2 ^ 30)%Z ->
  (bv_unsigned iov + 32 <= TASK_SIZE)%Z ->                     (* [comment removed for export] *)
  (bv_unsigned b1 + bv_unsigned n1 <= TASK_SIZE)%Z ->
  (bv_unsigned b2 + bv_unsigned n2 <= TASK_SIZE)%Z ->
  (forall k, (1 <= k)%nat -> (k <= length (bs1 ++ bs2))%nat ->
     srealizes_cfg segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat k))) (v_addi pc 4) (munrestrict H F mr) (seg_rom segs)) model)
              (T k)) ->
  srealizes_cfg segs (mkCfg (mkst regs pc (munrestrict H F mr) (seg_rom segs)) model)
    (t_alt (fun i : wr_index (bs1 ++ bs2) =>
       t_emit (map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) (bs1 ++ bs2))) (T (proj1_sig i)))).
Proof.
  intros F regs pc mr model w fd iov b1 n1 b2 n2 bs1 bs2 T HF HE HL Hh Hc Hfd Hfdr H17 H10 H11 H12
         Rb1 Rn1 Rb2 Rn2 Rs1 Rs2 Ht1 Htmax Ht30 HT0 HT1 HT2 Hk.
  eapply srz_cfg_sys_R; [exact HL | exact Hh | exact HF | exact HE |].
  pose proof (u64_range n1). pose proof (u64_range n2).
  replace (bs1 ++ bs2) with (concat [bs1; bs2]) in * by (cbn; rewrite app_nil_r; reflexivity).
  eapply (srz_cfg_writev_pending_R (epend regs pc (munrestrict H F mr) (seg_rom segs) (getr regs 17)) (getr regs 17) model fd iov
            [(b1, n1); (b2, n2)] [bs1; bs2] T);
    [reflexivity | exact HL | exact Hh | reflexivity | exact Hfd | exact Hfdr
    | rewrite H17; apply u64_lit; lia
    | rewrite ms_gpr_epend0; exact H10 | rewrite ms_gpr_epend1; exact H11 | rewrite ms_gpr_epend2; exact H12
    | cbn; lia | cbn [length]; lia | | cbn [iov_bufs_ok]; tauto | | | | cbn [iovs_total]; lia | cbn [iovs_total]; lia | cbn [iovs_total]; lia | ].
  - cbn [iov_array ms_mem epend].
    replace (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned iov + 16)) + 8)) with (Z_to_bv 64 (bv_unsigned iov + 24)).
    2:{ change (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned iov + 16)) + 8)) with (at_ (at_ iov 16) 8).
        rewrite at_at. reflexivity. }
    repeat split; try (apply (rdn_R segs H HH F mr); assumption); lia.
  - cbn [iov_bufs ms_mem epend]. repeat split; apply (rdn_R segs H HH F mr); assumption.
  - cbn [length]. exact (iov2_avoids segs H HH mr iov _ _ _ _ Hc Rb1 Rn1 Rb2 Rn2).
  - intros b n [E|[E|[]]]; injection E as <- <-;
      [exact (rdn_clean_avoids segs H mr _ _ _ HH Hc Rs1) | exact (rdn_clean_avoids segs H mr _ _ _ HH Hc Rs2)].
  - intros k Hk1 Hk2. rewrite adv_set_epend. apply Hk; assumption.
Qed.

Lemma srz_cfg_writev1_R : forall F regs (pc : word) mr model w (fd : Z) (iov b1 n1 : word) bs1 (T : nat -> TSet),
  fetch_word segs pc = Some w -> is_ecall w = true ->
  lazy_all_hidden H model -> m_halted model = None -> mclean H mr ->
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  (0 < fd < 2^31)%Z ->
  getr regs 17 = Z_to_bv 64 66 ->
  getr regs 10 = Z_to_bv 64 fd ->
  getr regs 11 = iov ->
  getr regs 12 = Z_to_bv 64 1 ->
  rdn segs mr iov 8%nat = Some (word_to_le_bytes 8 b1) ->
  rdn segs mr (Z_to_bv 64 (bv_unsigned iov + 8)) 8%nat = Some (word_to_le_bytes 8 n1) ->
  rdn segs mr b1 (word_to_nat n1) = Some bs1 ->
  (1 <= bv_unsigned n1)%Z ->
  (bv_unsigned n1 <= 2 ^ 30)%Z ->
  (bv_unsigned n1 <= 2 ^ 30)%Z ->
  (bv_unsigned iov + 16 <= TASK_SIZE)%Z ->                     (* [comment removed for export] *)
  (bv_unsigned b1 + bv_unsigned n1 <= TASK_SIZE)%Z ->
  (forall k, (1 <= k)%nat -> (k <= length bs1)%nat ->
     srealizes_cfg segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat k))) (v_addi pc 4) (munrestrict H F mr) (seg_rom segs)) model)
              (T k)) ->
  srealizes_cfg segs (mkCfg (mkst regs pc (munrestrict H F mr) (seg_rom segs)) model)
    (t_alt (fun i : wr_index bs1 =>
       t_emit (map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) bs1)) (T (proj1_sig i)))).
Proof.
  intros F regs pc mr model w fd iov b1 n1 bs1 T HF HE HL Hh Hc Hfd Hfdr H17 H10 H11 H12
         Rb1 Rn1 Rs1 Ht1 Htmax Ht30 HT0 HT1 Hk.
  eapply srz_cfg_sys_R; [exact HL | exact Hh | exact HF | exact HE |].
  pose proof (u64_range n1).
  replace bs1 with (concat [bs1]) in Hk by (cbn; rewrite app_nil_r; reflexivity).
  replace bs1 with (concat [bs1]) by (cbn; rewrite app_nil_r; reflexivity).
  eapply (srz_cfg_writev_pending_R (epend regs pc (munrestrict H F mr) (seg_rom segs) (getr regs 17)) (getr regs 17) model fd iov
            [(b1, n1)] [bs1] T);
    [reflexivity | exact HL | exact Hh | reflexivity | exact Hfd | exact Hfdr
    | rewrite H17; apply u64_lit; lia
    | rewrite ms_gpr_epend0; exact H10 | rewrite ms_gpr_epend1; exact H11 | rewrite ms_gpr_epend2; exact H12
    | cbn; lia | cbn [length]; lia | | cbn [iov_bufs_ok]; tauto | | | | cbn [iovs_total]; lia | cbn [iovs_total]; lia | cbn [iovs_total]; lia | ].
  - cbn [iov_array ms_mem epend]. repeat split; try (apply (rdn_R segs H HH F mr); assumption); lia.
  - cbn [iov_bufs ms_mem epend]. split; [apply (rdn_R segs H HH F mr); assumption | exact I].
  - cbn [length]. exact (iov1_avoids segs H HH mr iov _ _ Hc Rb1 Rn1).
  - intros b n [E|[]]; injection E as <- <-. exact (rdn_clean_avoids segs H mr _ _ _ HH Hc Rs1).
  - intros k Hk1 Hk2. rewrite adv_set_epend. apply Hk; assumption.
Qed.

Lemma srz_cfg_writev2_wall_R : forall F regs (pc : word) mr model w (fd : Z) (iov b1 n1 b2 n2 : word) bs1 bs2 (K : TSet),
  fetch_word segs pc = Some w -> is_ecall w = true ->
  lazy_all_hidden H model -> m_halted model = None -> mclean H mr ->
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  (0 < fd < 2^31)%Z ->
  getr regs 17 = Z_to_bv 64 66 ->
  getr regs 10 = Z_to_bv 64 fd ->
  getr regs 11 = iov ->
  getr regs 12 = Z_to_bv 64 2 ->
  rdn segs mr iov 8%nat = Some (word_to_le_bytes 8 b1) ->
  rdn segs mr (Z_to_bv 64 (bv_unsigned iov + 8)) 8%nat = Some (word_to_le_bytes 8 n1) ->
  rdn segs mr (Z_to_bv 64 (bv_unsigned iov + 16)) 8%nat = Some (word_to_le_bytes 8 b2) ->
  rdn segs mr (Z_to_bv 64 (bv_unsigned iov + 24)) 8%nat = Some (word_to_le_bytes 8 n2) ->
  rdn segs mr b1 (word_to_nat n1) = Some bs1 ->
  rdn segs mr b2 (word_to_nat n2) = Some bs2 ->
  (1 <= bv_unsigned n1 + bv_unsigned n2)%Z ->
  (bv_unsigned n1 + bv_unsigned n2 <= 2 ^ 30)%Z ->
  (bv_unsigned n1 + bv_unsigned n2 <= 2 ^ 30)%Z ->
  (bv_unsigned iov + 32 <= TASK_SIZE)%Z ->                     (* [comment removed for export] *)
  (bv_unsigned b1 + bv_unsigned n1 <= TASK_SIZE)%Z ->
  (bv_unsigned b2 + bv_unsigned n2 <= TASK_SIZE)%Z ->
  K [] ->
  (forall k, (1 <= k)%nat -> (k <= length (bs1 ++ bs2))%nat ->
     srealizes_cfg segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat k))) (v_addi pc 4) (munrestrict H F mr) (seg_rom segs)) model)
              (t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k (bs1 ++ bs2))) K)) ->
  srealizes_cfg segs (mkCfg (mkst regs pc (munrestrict H F mr) (seg_rom segs)) model)
           (t_emit (map (WriteEv (Z_to_bv 64 fd)) (bs1 ++ bs2)) K).
Proof.
  intros F regs pc mr model w fd iov b1 n1 b2 n2 bs1 bs2 K HF HE HL Hh Hc Hfd Hfdr H17 H10 H11 H12
         Rb1 Rn1 Rb2 Rn2 Rs1 Rs2 Ht1 Htmax Ht30 HT0 HT1 HT2 HK Hk.
  pose proof (rdn_length segs mr _ _ _ Rs1) as L1. pose proof (rdn_length segs mr _ _ _ Rs2) as L2.
  pose proof (u64_range n1). pose proof (u64_range n2).
  apply srz_cfg_wall; [rewrite length_app; unfold word_to_nat in L1, L2; lia | exact HK |].
  eapply (srz_cfg_writev2_R F regs pc mr model w fd iov b1 n1 b2 n2 bs1 bs2
            (fun k => t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k (bs1 ++ bs2))) K)); eassumption.
Qed.

Lemma srz_cfg_writev1_wall_R : forall F regs (pc : word) mr model w (fd : Z) (iov b1 n1 : word) bs1 (K : TSet),
  fetch_word segs pc = Some w -> is_ecall w = true ->
  lazy_all_hidden H model -> m_halted model = None -> mclean H mr ->
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  (0 < fd < 2^31)%Z ->
  getr regs 17 = Z_to_bv 64 66 ->
  getr regs 10 = Z_to_bv 64 fd ->
  getr regs 11 = iov ->
  getr regs 12 = Z_to_bv 64 1 ->
  rdn segs mr iov 8%nat = Some (word_to_le_bytes 8 b1) ->
  rdn segs mr (Z_to_bv 64 (bv_unsigned iov + 8)) 8%nat = Some (word_to_le_bytes 8 n1) ->
  rdn segs mr b1 (word_to_nat n1) = Some bs1 ->
  (1 <= bv_unsigned n1)%Z ->
  (bv_unsigned n1 <= 2 ^ 30)%Z ->
  (bv_unsigned n1 <= 2 ^ 30)%Z ->
  (bv_unsigned iov + 16 <= TASK_SIZE)%Z ->                     (* [comment removed for export] *)
  (bv_unsigned b1 + bv_unsigned n1 <= TASK_SIZE)%Z ->
  K [] ->
  (forall k, (1 <= k)%nat -> (k <= length bs1)%nat ->
     srealizes_cfg segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat k))) (v_addi pc 4) (munrestrict H F mr) (seg_rom segs)) model)
              (t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k bs1)) K)) ->
  srealizes_cfg segs (mkCfg (mkst regs pc (munrestrict H F mr) (seg_rom segs)) model)
           (t_emit (map (WriteEv (Z_to_bv 64 fd)) bs1) K).
Proof.
  intros F regs pc mr model w fd iov b1 n1 bs1 K HF HE HL Hh Hc Hfd Hfdr H17 H10 H11 H12
         Rb1 Rn1 Rs1 Ht1 Htmax Ht30 HT0 HT1 HK Hk.
  pose proof (rdn_length segs mr _ _ _ Rs1) as L1. pose proof (u64_range n1).
  apply srz_cfg_wall; [unfold word_to_nat in L1; lia | exact HK |].
  eapply (srz_cfg_writev1_R F regs pc mr model w fd iov b1 n1 bs1
            (fun k => t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k bs1)) K)); eassumption.
Qed.

(* [comment removed for export] *)
Lemma srz_cfg_writev1_zero_R : forall F regs (pc : word) mr model w (fd : Z) (iov b1 : word) K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  lazy_all_hidden H model -> m_halted model = None -> mclean H mr ->
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  (0 < fd < 2^31)%Z ->
  getr regs 17 = Z_to_bv 64 66 ->
  getr regs 10 = Z_to_bv 64 fd ->
  getr regs 11 = iov ->
  getr regs 12 = Z_to_bv 64 1 ->
  rdn segs mr iov 8%nat = Some (word_to_le_bytes 8 b1) ->
  rdn segs mr (Z_to_bv 64 (bv_unsigned iov + 8)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  (0 <= 2 ^ 30)%Z ->
  (bv_unsigned iov + 16 <= TASK_SIZE)%Z ->        (* [comment removed for export] *)
  (bv_unsigned b1 <= TASK_SIZE)%Z ->
  srealizes_cfg segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) (munrestrict H F mr) (seg_rom segs)) model) K ->
  srealizes_cfg segs (mkCfg (mkst regs pc (munrestrict H F mr) (seg_rom segs)) model) K.
Proof.
  intros F regs pc mr model w fd iov b1 K HF HE HL Hh Hc Hfd Hfdr H17 H10 H11 H12 Rb1 Rn1 Hmax HT0 HT1 Hk.
  eapply srz_cfg_sys_R; [exact HL | exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc (munrestrict H F mr) (seg_rom segs) (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 66%Z) by (rewrite H17; apply u64_lit; lia).
  assert (Harr : iov_array segs (ms_mem ms) iov [(b1, Z_to_bv 64 0)]).
  { cbn [iov_array ms_mem ms epend].
    refine (conj (rdn_R segs H HH F mr _ _ _ Hc Rb1) (conj (rdn_R segs H HH F mr _ _ _ Hc Rn1) (conj _ I))). rewrite u64_lit by lia. lia. }
  assert (Hbok : iov_bufs_ok [(b1, Z_to_bv 64 0)]).
  { cbn [iov_bufs_ok]. split; [|exact I]. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. lia. }
  pose proof (import_iovecs_of_array segs ms [(b1, Z_to_bv 64 0)] iov eq_refl ltac:(cbn; lia) ltac:(cbn [length]; lia) Harr Hbok) as Himp.
  cbn [length] in Himp. change (Z_to_bv 64 (Z.of_nat 1)) with (Z_to_bv 64 1) in Himp.
  pose proof (copy_iovecs_accesses_of_array segs ms [(b1, Z_to_bv 64 0)] iov eq_refl Harr) as Hca.
  cbn [length seq map] in Hca. rewrite Z.mul_0_r, Z.add_0_r, u64_roundtrip' in Hca.
  assert (Hia : import_iovecs_accesses (ms_read_byte ms) iov (Z_to_bv 64 1) = [(iov, 16%nat)]).
  { change (Z_to_bv 64 1) with (Z_to_bv 64 (Z.of_nat 1)).
    rewrite (import_iovecs_accesses_copy _ iov 1 ltac:(lia) ltac:(cbn; lia)). exact Hca. }
  eapply (srz_cfg_ret_only_copyins_silent_mat0 segs ms model (getr regs 17)
            (import_iovecs_accesses (ms_read_byte ms) iov (Z_to_bv 64 1)) (Z_to_bv 64 0) model);
    [exact Hh | reflexivity | | exact Hh | | unfold ms; rewrite adv_set_epend; exact Hk].
  2:{ rewrite Hia. apply (materialize_nolazy H model _ HL). apply ranges_avoid_cons; [|apply ranges_avoid_nil].
      exact (iov1_avoids segs H HH mr iov _ _ Hc Rb1 Rn1). }
  intros eff.
  rewrite (check_syscall_writev (sys_input segs ms (getr regs 17)) eff model) by (rewrite in_sysno_si; exact Hno).
  rewrite in_arg0_si, in_arg1_si, in_arg2_si.
  assert (G0 : ms_gpr ms 0 = Z_to_bv 64 fd) by (unfold ms; rewrite ms_gpr_epend0; exact H10).
  assert (G1 : ms_gpr ms 1 = iov) by (unfold ms; rewrite ms_gpr_epend1; exact H11).
  assert (G2 : ms_gpr ms 2 = Z_to_bv 64 1) by (unfold ms; rewrite ms_gpr_epend2; exact H12).
  rewrite G0, G1, G2.
  rewrite fd32_id by (rewrite u64_lit; lia).
  unfold check_writev. rewrite Hfd.
  replace (w_is0 (Z_to_bv 64 fd)) with false by (symmetry; apply w_is0_pos; rewrite u64_lit; lia).
  change (iovcnt32 (Z_to_bv 64 1)) with (Z_to_bv 64 1).
  rewrite in_mem_si. rewrite Himp.
  assert (Hcap : cap_iovecs [(b1, Z_to_bv 64 0)] = [(b1, Z_to_bv 64 0)]).
  { unfold cap_iovecs. apply cap_iovecs_id. cbn [iovs_total]. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. unfold MAX_RW_COUNT. lia. }
  rewrite Hcap. cbn [iovs_total]. change (bv_unsigned (Z_to_bv 64 0) + 0)%Z with 0%Z. cbn [Z.eqb].
  destruct (check_ret_only_copyins (import_iovecs_accesses (ms_read_byte ms) iov (Z_to_bv 64 1)) eff (Z_to_bv 64 0) model []) eqn:E;
    [reflexivity | reflexivity | exfalso; exact (check_ret_only_copyins_no_unmodeled _ _ _ _ _ E)].
Qed.

End NoLazyS.
End WithFP.
