(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.LibWritevF OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AzSLibE. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.AgentNodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRel OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.Nodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.FileSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.ShapeNodes OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.LibWritev OSSVerify.Proofs.glaze.binary_reflection.lib.LibWritevF OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.AzSLibE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section WithRel.
Variable segs : list Segment.
Variable R : shape_rel segs.

(* [comment removed for export] *)
Lemma sr_sys_lazy : forall {fx : FPState} regs pc mem rom model w T,
  m_halted model = None -> fetch_word segs pc = Some w -> is_ecall w = true ->
  R (mkCfg (epend regs pc mem rom (getr regs 17)) model) T ->
  R (mkCfg (mkst regs pc mem rom) model) T.
Proof.
  intros fx regs pc mem rom model w T Hh HF HE Hc.
  eapply (sr_silent1 segs R); [| exact Hc].
  rewrite <- (AsanAcctShape.node_ok_same segs).
  apply (AzSLibE.node_instr_noacc segs); [exact Hh | reflexivity | eapply AzSLibE.stepacc_ecall_epend; eassumption].
Qed.

(* [comment removed for export] *)
Lemma sr_writev_pending_lazy : forall (H : word -> bool) (A : list (Z * Z)) ms x8 model (fd : Z) (iov : word) iovs bss (T : nat -> TSet),
  ms_rom ms = seg_rom segs ->
  A_wf A -> MInv A model -> lazy_cover H (m_vm_lazy model) A ->
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  (0 < fd < 2^31)%Z ->
  bv_unsigned x8 = 66%Z ->
  ms_gpr ms 0 = Z_to_bv 64 fd ->
  ms_gpr ms 1 = iov ->
  ms_gpr ms 2 = Z_to_bv 64 (Z.of_nat (length iovs)) ->
  (1 <= length iovs <= 1024)%nat ->
  (bv_unsigned iov + 16 * Z.of_nat (length iovs) <= TASK_SIZE)%Z ->
  iov_array segs (ms_mem ms) iov iovs ->
  iov_bufs_ok iovs ->
  iov_bufs segs (ms_mem ms) iovs bss ->
  let bs := concat bss in
  (1 <= iovs_total iovs)%Z -> (iovs_total iovs <= 2 ^ 30)%Z ->
  (forall k, ranges_avoid H (import_iovecs_accesses (ms_read_byte ms) iov (Z_to_bv 64 (Z.of_nat (length iovs))) ++ iov_prefix_accesses iovs k)) ->
  (forall k mdl', (1 <= k)%nat -> (k <= length bs)%nat -> MInv A mdl' -> same_but_materialized model mdl' ->
     R (mkCfg (advance_past_svc (set_gpr0 ms (Z_to_bv 64 (Z.of_nat k)))) mdl') (T k)) ->
  R (mkCfg ms model)
    (t_alt (fun i : wr_index bs => t_emit (map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) bs)) (T (proj1_sig i)))).
Proof.
  intros H A ms x8 model fd iov iovs bss T Hrom Hwf Hinv Hcov Hh Hsvc Hfd Hfdr Hno H0 H1 H2 Hcnt Hiok Harr Hbok Hbufs bs
         Ht1 Ht30 Hav Hk.
  destruct (writev_checkF segs ms x8 model fd iov iovs bss Hrom Hfd Hfdr Hno H0 H1 H2 Hcnt Hiok Harr Hbok Hbufs
              Ht1 ltac:(lia) Ht30)
    as [Hlen Hchk]. fold bs in Hlen, Hchk.
  set (tot := iovs_total iovs) in *.
  set (CA := import_iovecs_accesses (ms_read_byte ms) iov (Z_to_bv 64 (Z.of_nat (length iovs)))) in *.
  assert (Hnb : (1 <= length bs)%nat) by lia.
  pose (effs := fun i : wr_index bs =>
          mkEffectU (Z_to_bv 64 (Z.of_nat (proj1_sig i))) [] [] [] []
                    (CA ++ iov_prefix_accesses iovs (proj1_sig i))).
  assert (Enx : forall (i : wr_index bs) mdl',
    mkCfg (advance_past_svc (set_gpr0 ms (Z_to_bv 64 (Z.of_nat (proj1_sig i))))) mdl'
    = mkCfg (advance_past_svc (apply_effect ms (effs i))) mdl').
  { intros [k Hk'] mdl'. cbn [proj1_sig]. unfold effs. cbn [proj1_sig].
    rewrite <- (apply_effect_copyins_no_write ms (Z_to_bv 64 (Z.of_nat k)) (CA ++ iov_prefix_accesses iovs k)).
    reflexivity. }
  assert (Hku : forall k, (k <= length bs)%nat -> bv_unsigned (Z_to_bv 64 (Z.of_nat k)) = Z.of_nat k).
  { intros k Hk2. apply u64_lit. lia. }
  assert (Hacc : forall i, syscall_effect_accesses (effs i) = CA ++ iov_prefix_accesses iovs (proj1_sig i)).
  { intros i. unfold effs, syscall_effect_accesses. cbn. rewrite ?app_nil_r. reflexivity. }
  assert (Hsound : forall i : wr_index bs,
            syscall_spec (sys_input segs ms x8) model (Ok (effs i) model (map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) bs)))).
  { intros i. apply check_syscall_ok_iff. destruct i as [k [Hk1 Hk2]]. unfold effs. cbn [proj1_sig]. rewrite Hchk.
    rewrite (Hku k Hk2), Nat2Z.id.
    rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia.
    replace (addr_is_error_b (Z_to_bv 64 (Z.of_nat k))) with false
      by (symmetry; unfold addr_is_error_b, two_pow_64; apply Z.ltb_ge; rewrite (Hku k Hk2); lia).
    rewrite (proj2 (access_ranges_eqb_eq _ _) eq_refl). reflexivity. }
  assert (Hcompl : forall r, syscall_spec (sys_input segs ms x8) model r ->
            exists i : wr_index bs, r = Ok (effs i) model (map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) bs))).
  { intros r Hr. destruct r as [eff m' ev|].
    - apply check_syscall_ok_iff in Hr. destruct eff as [ret ws zs us cs ci]. rewrite Hchk in Hr.
      destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate].
      destruct ((1 <=? bv_unsigned ret)%Z && (bv_unsigned ret <=? tot)%Z && negb (addr_is_error_b ret))%bool eqn:Eb; [|discriminate].
      destruct (access_ranges_eqb ci (CA ++ iov_prefix_accesses iovs (Z.to_nat (bv_unsigned ret)))) eqn:Eci; [|discriminate].
      injection Hr as <- <-.
      apply andb_true_iff in Eb as [Eb _]. apply andb_true_iff in Eb as [E1 E2].
      apply Z.leb_le in E1. apply Z.leb_le in E2. apply access_ranges_eqb_eq in Eci.
      assert (Hkr : (1 <= Z.to_nat (bv_unsigned ret))%nat /\ (Z.to_nat (bv_unsigned ret) <= length bs)%nat) by lia.
      exists (exist _ (Z.to_nat (bv_unsigned ret)) Hkr). cbn [proj1_sig]. unfold effs. cbn [proj1_sig].
      rewrite Z2Nat.id by lia. rewrite u64_roundtrip'. subst ci. reflexivity.
    - exfalso. apply (check_syscall_err_iff (sys_input segs ms x8) (effs (wr_full bs Hnb)) model) in Hr.
      rewrite Hchk in Hr. unfold effs in Hr. cbn [proj1_sig] in Hr.
      destruct ((1 <=? _)%Z && _ && _)%bool; [destruct (access_ranges_eqb _ _)|]; discriminate Hr. }
  destruct (node_syscall_restricted segs H A ms model x8 (wr_index bs) effs (fun _ => model)
              (fun i => map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) bs))
              Hwf Hh Hsvc ltac:(rewrite Hno; reflexivity) Hsound Hcompl (fun _ => Hh) (fun _ => Hcov) (fun _ => Hinv)
              ltac:(intros i; rewrite Hacc; apply Hav)) as [Hms Hnode].
  apply (sr_node segs R (mkCfg ms model) (wr_index bs)
           (fun i => map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) bs))
           (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (materialized_succ model (syscall_effect_accesses (effs i))))
           (fun i => T (proj1_sig i)) (wr_full bs Hnb)).
  - rewrite <- (AsanAcctShape.node_ok_same segs). exact Hnode.
  - intros i. rewrite <- Enx. destruct (Hms i) as [M1 M2]. destruct i as [k [Hk1 Hk2]]. cbn [proj1_sig]. apply Hk; assumption.
Qed.

(* [comment removed for export] *)
Lemma woff_shift : forall (a : word) (d k : nat), woff (Z_to_bv 64 (bv_unsigned a + Z.of_nat d)) k = woff a (d + k).
Proof.
  intros a d k. unfold woff. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.
Lemma range_avoids_sub : forall H (a : word) (n d m : nat),
  range_avoids H a n -> (d + m <= n)%nat -> range_avoids H (Z_to_bv 64 (bv_unsigned a + Z.of_nat d)) m.
Proof. intros H a n d m Hr Hle k Hk. rewrite woff_shift. apply Hr. lia. Qed.
Lemma range_avoids_pre : forall H (a : word) (n m : nat), range_avoids H a n -> (m <= n)%nat -> range_avoids H a m.
Proof. intros H a n m Hr Hle k Hk. apply Hr. lia. Qed.
Lemma rdn_munrestrict_avoid : forall H F (m : word -> option byte) n (a : word),
  range_avoids H a n -> rdn segs (munrestrict H F m) a n = rdn segs m a n.
Proof.
  intros H F m n. induction n as [|n IH]; intros a Hr; [reflexivity|].
  cbn [rdn]. unfold munrestrict at 1. rewrite (range_avoids_hd H a n Hr). rewrite (IH (a + 1)%bv (range_avoids_tl H a n Hr)). reflexivity.
Qed.
Lemma iov_prefix_avoid : forall H iovs left,
  Forall (fun p : word * word => range_avoids H (fst p) (word_to_nat (snd p))) iovs -> ranges_avoid H (iov_prefix_accesses iovs left).
Proof.
  intros H iovs. induction iovs as [|[b n] r IH]; intros left HF.
  - destruct left; apply ranges_avoid_nil.
  - apply Forall_cons_iff in HF as [Hb Hr]. cbn [fst snd] in Hb.
    destruct left as [|l]; [apply ranges_avoid_nil|]. cbn [iov_prefix_accesses].
    destruct (Nat.eqb (word_to_nat_bounded n (S l)) 0); [apply IH; exact Hr|].
    apply ranges_avoid_cons; [|apply IH; exact Hr].
    apply (range_avoids_pre H b (word_to_nat n)); [exact Hb|].
    unfold word_to_nat_bounded. destruct (bv_unsigned n <=? Z.of_nat (S l))%Z eqn:E; [lia|].
    apply Z.leb_gt in E. unfold word_to_nat. lia.
Qed.

(* [comment removed for export] *)
Lemma sr_ret_only_copyins_lazy : forall (H : word -> bool) (A : list (Z * Z)) ms model x8 reads r T,
  A_wf A -> MInv A model -> lazy_cover H (m_vm_lazy model) A ->
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  CfgStep.alloc_no_b (bv_unsigned x8) = false ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model = check_ret_only_copyins reads eff r model []) ->
  ranges_avoid H reads ->
  (forall mdl', MInv A mdl' -> same_but_materialized model mdl' -> R (mkCfg (advance_past_svc (set_gpr0 ms r)) mdl') T) ->
  R (mkCfg ms model) T.
Proof.
  intros H A ms model x8 reads r T Hwf Hinv Hcov Hh Hsvc Hna Hchk Hav Hk.
  set (eff0 := with_copyins reads (mkEffect r [] [])).
  assert (Hacc : syscall_effect_accesses eff0 = reads) by (unfold eff0, syscall_effect_accesses, with_copyins; cbn; rewrite ?app_nil_r; reflexivity).
  destruct (node_syscall_restricted segs H A ms model x8 unit (fun _ => eff0) (fun _ => model) (fun _ => []) Hwf Hh Hsvc Hna) as [Hms Hnode].
  - intros _. apply check_syscall_ok_iff. rewrite Hchk. apply check_ret_only_copyins_ok_iff. repeat split.
  - intros res Hres. exists tt. destruct res as [eff m' ev|].
    + apply check_syscall_ok_iff in Hres. rewrite Hchk in Hres. apply check_ret_only_copyins_ok_iff in Hres as (-> & -> & ->). reflexivity.
    + exfalso. apply (check_syscall_err_iff (sys_input segs ms x8) eff0 model) in Hres. rewrite Hchk in Hres.
      exact (check_ret_only_copyins_no_unmodeled _ _ _ _ _ Hres).
  - intros _. exact Hh.
  - intros _. exact Hcov.
  - intros _. exact Hinv.
  - intros _. rewrite Hacc. exact Hav.
  - eapply (sr_silent1 segs R); [rewrite <- (AsanAcctShape.node_ok_same segs); exact Hnode|].
    cbv beta. unfold eff0 at 1. rewrite (apply_effect_copyins_no_write ms r reads).
    destruct (Hms tt) as [M1 M2]. apply Hk; assumption.
Qed.

(* [comment removed for export] *)
Section FPG.
Context {fx : FPState}.

Lemma sr_writev1_wall_lazy : forall (H : word -> bool) (A : list (Z * Z)) (F : word -> option byte)
         regs (pc : word) (m : word -> option byte) model w (fd : Z) (iov b1 n1 : word) bs1 (K : TSet),
  A_wf A -> MInv A model -> lazy_cover H (m_vm_lazy model) A ->
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  (0 < fd < 2 ^ 31)%Z ->
  getr regs 17 = Z_to_bv 64 66 -> getr regs 10 = Z_to_bv 64 fd -> getr regs 11 = iov -> getr regs 12 = Z_to_bv 64 1 ->
  rdn segs m iov 8%nat = Some (word_to_le_bytes 8 b1) ->
  rdn segs m (Z_to_bv 64 (bv_unsigned iov + 8)) 8%nat = Some (word_to_le_bytes 8 n1) ->
  rdn segs m b1 (word_to_nat n1) = Some bs1 ->
  range_avoids H iov 16%nat -> range_avoids H b1 (word_to_nat n1) ->
  (bv_unsigned iov + 16 <= TASK_SIZE)%Z -> (bv_unsigned b1 + bv_unsigned n1 <= TASK_SIZE)%Z ->
  (1 <= bv_unsigned n1)%Z -> (bv_unsigned n1 <= 2 ^ 30)%Z ->
  K [] ->
  (forall k mdl', (1 <= k)%nat -> (k <= length bs1)%nat -> MInv A mdl' -> same_but_materialized model mdl' ->
     R (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat k))) (v_addi pc 4) (munrestrict H F m) (seg_rom segs)) mdl')
              (t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k bs1)) K)) ->
  R (mkCfg (mkst regs pc (munrestrict H F m) (seg_rom segs)) model)
           (t_emit (map (WriteEv (Z_to_bv 64 fd)) bs1) K).
Proof.
  intros H A F regs pc m model w fd iov b1 n1 bs1 K Hwf Hinv Hcov HF HE Hh Hfd Hfdr H17 H10 H11 H12
         Rb1 Rn1 Rs1 Av1 Av2 Hiok Hb1 Ht1 Ht30 HK Hk.
  pose proof (rdn_length segs m _ _ _ Rs1) as L1. pose proof (u64_range n1).
  apply (sr_wall segs R); [unfold word_to_nat in L1; lia | exact HK |].
  eapply sr_sys_lazy; [exact Hh | exact HF | exact HE |].
  set (mem := munrestrict H F m).
  replace bs1 with (concat [bs1]) in Hk by (cbn; rewrite app_nil_r; reflexivity).
  replace bs1 with (concat [bs1]) by (cbn; rewrite app_nil_r; reflexivity).
  eapply (sr_writev_pending_lazy H A (epend regs pc mem (seg_rom segs) (getr regs 17)) (getr regs 17) model fd iov
            [(b1, n1)] [bs1] (fun k => t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k (concat [bs1]))) K));
    [reflexivity | exact Hwf | exact Hinv | exact Hcov | exact Hh | reflexivity | exact Hfd | exact Hfdr
    | rewrite H17; apply u64_lit; lia
    | rewrite ms_gpr_epend0; exact H10 | rewrite ms_gpr_epend1; exact H11 | rewrite ms_gpr_epend2; exact H12
    | cbn; lia | change (Z.of_nat (length [(b1, n1)])) with 1%Z; lia
    | | cbn [iov_bufs_ok]; split; [assumption | exact I] | | cbn [iovs_total]; lia | cbn [iovs_total]; lia | | ].
  - cbn [iov_array ms_mem epend]. unfold mem.
    rewrite (rdn_munrestrict_avoid H F m 8 iov (range_avoids_pre H iov 16 8 Av1 ltac:(lia))).
    pose proof (rdn_munrestrict_avoid H F m 8 _ (range_avoids_sub H iov 16 8 8 Av1 ltac:(lia))) as X2. change (Z.of_nat 8) with 8%Z in X2. rewrite X2.
    repeat split; try assumption; lia.
  - cbn [iov_bufs ms_mem epend]. unfold mem. rewrite (rdn_munrestrict_avoid H F m _ b1 Av2). split; [assumption | exact I].
  - intros k. apply ranges_avoid_app.
    + change (Z.of_nat (length [(b1, n1)])) with 1%Z. unfold import_iovecs_accesses. rewrite (proj2 (bv_eqb_eq _ _) eq_refl).
      destruct (negb (access_okb iov 16)); [apply ranges_avoid_nil | apply ranges_avoid_cons; [exact Av1 | apply ranges_avoid_nil]].
    + apply iov_prefix_avoid. repeat constructor. exact Av2.
  - intros k mdl' Hk1 Hk2 M1 M2. rewrite adv_set_epend. apply Hk; assumption.
Qed.


Lemma sr_writev2_wall_lazy : forall (H : word -> bool) (A : list (Z * Z)) (F : word -> option byte)
         regs (pc : word) (m : word -> option byte) model w (fd : Z) (iov b1 n1 b2 n2 : word) bs1 bs2 (K : TSet),
  A_wf A -> MInv A model -> lazy_cover H (m_vm_lazy model) A ->
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  (0 < fd < 2 ^ 31)%Z ->
  getr regs 17 = Z_to_bv 64 66 -> getr regs 10 = Z_to_bv 64 fd -> getr regs 11 = iov -> getr regs 12 = Z_to_bv 64 2 ->
  rdn segs m iov 8%nat = Some (word_to_le_bytes 8 b1) ->
  rdn segs m (Z_to_bv 64 (bv_unsigned iov + 8)) 8%nat = Some (word_to_le_bytes 8 n1) ->
  rdn segs m (Z_to_bv 64 (bv_unsigned iov + 16)) 8%nat = Some (word_to_le_bytes 8 b2) ->
  rdn segs m (Z_to_bv 64 (bv_unsigned iov + 24)) 8%nat = Some (word_to_le_bytes 8 n2) ->
  rdn segs m b1 (word_to_nat n1) = Some bs1 ->
  rdn segs m b2 (word_to_nat n2) = Some bs2 ->
  range_avoids H iov 32%nat -> range_avoids H b1 (word_to_nat n1) -> range_avoids H b2 (word_to_nat n2) ->
  (bv_unsigned iov + 32 <= TASK_SIZE)%Z -> (bv_unsigned b1 + bv_unsigned n1 <= TASK_SIZE)%Z ->
  (bv_unsigned b2 + bv_unsigned n2 <= TASK_SIZE)%Z ->
  (1 <= bv_unsigned n1 + bv_unsigned n2)%Z ->
  (bv_unsigned n1 + bv_unsigned n2 <= 2 ^ 30)%Z ->
  K [] ->
  (forall k mdl', (1 <= k)%nat -> (k <= length (bs1 ++ bs2))%nat -> MInv A mdl' -> same_but_materialized model mdl' ->
     R (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat k))) (v_addi pc 4) (munrestrict H F m) (seg_rom segs)) mdl')
              (t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k (bs1 ++ bs2))) K)) ->
  R (mkCfg (mkst regs pc (munrestrict H F m) (seg_rom segs)) model)
           (t_emit (map (WriteEv (Z_to_bv 64 fd)) (bs1 ++ bs2)) K).
Proof.
  intros H A F regs pc m model w fd iov b1 n1 b2 n2 bs1 bs2 K Hwf Hinv Hcov HF HE Hh Hfd Hfdr H17 H10 H11 H12
         Rb1 Rn1 Rb2 Rn2 Rs1 Rs2 Av0 Av1 Av2 Hiok Hb1 Hb2 Ht1 Ht30 HK Hk.
  pose proof (rdn_length segs m _ _ _ Rs1) as L1. pose proof (rdn_length segs m _ _ _ Rs2) as L2.
  pose proof (u64_range n1). pose proof (u64_range n2).
  apply (sr_wall segs R); [rewrite length_app; unfold word_to_nat in L1, L2; lia | exact HK |].
  eapply sr_sys_lazy; [exact Hh | exact HF | exact HE |].
  set (mem := munrestrict H F m).
  replace (bs1 ++ bs2) with (concat [bs1; bs2]) in * by (cbn; rewrite app_nil_r; reflexivity).
  eapply (sr_writev_pending_lazy H A (epend regs pc mem (seg_rom segs) (getr regs 17)) (getr regs 17) model fd iov
            [(b1, n1); (b2, n2)] [bs1; bs2] (fun k => t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k (concat [bs1; bs2]))) K));
    [reflexivity | exact Hwf | exact Hinv | exact Hcov | exact Hh | reflexivity | exact Hfd | exact Hfdr
    | rewrite H17; apply u64_lit; lia
    | rewrite ms_gpr_epend0; exact H10 | rewrite ms_gpr_epend1; exact H11 | rewrite ms_gpr_epend2; exact H12
    | cbn; lia | change (Z.of_nat (length [(b1, n1); (b2, n2)])) with 2%Z; lia
    | | cbn [iov_bufs_ok]; repeat split; assumption | | cbn [iovs_total]; lia | cbn [iovs_total]; lia | | ].
  - cbn [iov_array ms_mem epend]. unfold mem.
    replace (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned iov + 16)) + 8)) with (Z_to_bv 64 (bv_unsigned iov + 24)).
    2:{ change (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned iov + 16)) + 8)) with (at_ (at_ iov 16) 8).
        rewrite at_at. reflexivity. }
    rewrite (rdn_munrestrict_avoid H F m 8 iov (range_avoids_pre H iov 32 8 Av0 ltac:(lia))).
    pose proof (rdn_munrestrict_avoid H F m 8 _ (range_avoids_sub H iov 32 8 8 Av0 ltac:(lia))) as X2. change (Z.of_nat 8) with 8%Z in X2. rewrite X2.
    pose proof (rdn_munrestrict_avoid H F m 8 _ (range_avoids_sub H iov 32 16 8 Av0 ltac:(lia))) as X3. change (Z.of_nat 16) with 16%Z in X3. rewrite X3.
    pose proof (rdn_munrestrict_avoid H F m 8 _ (range_avoids_sub H iov 32 24 8 Av0 ltac:(lia))) as X4. change (Z.of_nat 24) with 24%Z in X4. rewrite X4.
    repeat split; try assumption; lia.
  - cbn [iov_bufs ms_mem epend]. unfold mem.
    rewrite (rdn_munrestrict_avoid H F m _ b1 Av1), (rdn_munrestrict_avoid H F m _ b2 Av2). repeat split; assumption.
  - intros k. apply ranges_avoid_app.
    + change (Z.of_nat (length [(b1, n1); (b2, n2)])) with 2%Z. unfold import_iovecs_accesses.
      replace (bv_eqb (Z_to_bv 64 2) (Z_to_bv 64 1)) with false by reflexivity.
      replace (bv_eqb (Z_to_bv 64 2) (Z_to_bv 64 0)) with false by reflexivity.
      destruct (IOV_MAX <? bv_unsigned (Z_to_bv 64 2))%Z; [apply ranges_avoid_nil|].
      destruct (negb (access_okb iov (16 * bv_unsigned (Z_to_bv 64 2)))); [apply ranges_avoid_nil|].
      change (word_to_nat (Z_to_bv 64 2)) with 2%nat. cbn [copy_iovecs_accesses].
      apply ranges_avoid_cons; [exact (range_avoids_pre H iov 32 16 Av0 ltac:(lia))|].
      destruct (read_iovec_entry _ iov); try apply ranges_avoid_nil.
      apply ranges_avoid_cons.
      * replace (iov + 16)%bv with (Z_to_bv 64 (bv_unsigned iov + Z.of_nat 16)) by (apply bv_eq; rewrite bv_add_unsigned, Z_to_bv_unsigned; reflexivity).
        exact (range_avoids_sub H iov 32 16 16 Av0 ltac:(lia)).
      * destruct (read_iovec_entry _ _); apply ranges_avoid_nil.
    + apply iov_prefix_avoid. repeat constructor; assumption.
  - intros k mdl' Hk1 Hk2 M1 M2. rewrite adv_set_epend. apply Hk; assumption.
Qed.

Lemma sr_writev1_zero_lazy : forall (H : word -> bool) (A : list (Z * Z)) (F : word -> option byte)
         regs (pc : word) (m : word -> option byte) model w (fd : Z) (iov b1 : word) (K : TSet),
  A_wf A -> MInv A model -> lazy_cover H (m_vm_lazy model) A ->
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  (0 < fd < 2 ^ 31)%Z ->
  getr regs 17 = Z_to_bv 64 66 -> getr regs 10 = Z_to_bv 64 fd -> getr regs 11 = iov -> getr regs 12 = Z_to_bv 64 1 ->
  rdn segs m iov 8%nat = Some (word_to_le_bytes 8 b1) ->
  rdn segs m (Z_to_bv 64 (bv_unsigned iov + 8)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  range_avoids H iov 16%nat ->
  (bv_unsigned iov + 16 <= TASK_SIZE)%Z -> (bv_unsigned b1 <= TASK_SIZE)%Z ->
  (forall mdl', MInv A mdl' -> same_but_materialized model mdl' ->
     R (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) (munrestrict H F m) (seg_rom segs)) mdl') K) ->
  R (mkCfg (mkst regs pc (munrestrict H F m) (seg_rom segs)) model) K.
Proof.
  intros H A F regs pc m model w fd iov b1 K Hwf Hinv Hcov HF HE Hh Hfd Hfdr H17 H10 H11 H12 Rb1 Rn1 Av0 Hiok Hb1 Hc.
  eapply sr_sys_lazy; [exact Hh | exact HF | exact HE |].
  set (mem := munrestrict H F m).
  set (ms := epend regs pc mem (seg_rom segs) (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 66%Z) by (rewrite H17; apply u64_lit; lia).
  assert (Harr : iov_array segs (ms_mem ms) iov [(b1, Z_to_bv 64 0)]).
  { cbn [iov_array ms_mem ms epend]. unfold mem.
    rewrite (rdn_munrestrict_avoid H F m 8 iov (range_avoids_pre H iov 16 8 Av0 ltac:(lia))).
    pose proof (rdn_munrestrict_avoid H F m 8 _ (range_avoids_sub H iov 16 8 8 Av0 ltac:(lia))) as X2. change (Z.of_nat 8) with 8%Z in X2. rewrite X2.
    refine (conj Rb1 (conj Rn1 (conj _ I))). rewrite u64_lit by lia. lia. }
  assert (Himp : import_iovecs (ms_read_byte ms) iov (Z_to_bv 64 1) = ImpOk [(b1, Z_to_bv 64 0)]).
  { unfold import_iovecs. rewrite (proj2 (bv_eqb_eq _ _) eq_refl).
    rewrite (access_okb_of_le iov 16) by lia.
    rewrite (read_iovec_entry_of_array segs ms b1 (Z_to_bv 64 0) [] iov eq_refl Harr).
    rewrite u64_lit by lia. change (Z.min 0 MAX_RW_COUNT) with 0%Z.
    rewrite (access_okb_of_le b1 0) by lia. reflexivity. }
  assert (Hacc : import_iovecs_accesses (ms_read_byte ms) iov (Z_to_bv 64 1) = [(iov, 16%nat)]).
  { unfold import_iovecs_accesses. rewrite (proj2 (bv_eqb_eq _ _) eq_refl).
    rewrite (access_okb_of_le iov 16) by lia. reflexivity. }
  apply (sr_ret_only_copyins_lazy H A ms model (getr regs 17) [(iov, 16%nat)] (Z_to_bv 64 0) K Hwf Hinv Hcov Hh eq_refl ltac:(rewrite Hno; reflexivity)).
  - intros eff.
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
    rewrite in_mem_si, Himp, Hacc.
    unfold cap_iovecs. cbn [cap_iovecs_aux iovs_total].
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. rewrite Z.min_r by (unfold MAX_RW_COUNT; lia).
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. cbv beta iota zeta.
    change ((0 + 0 =? 0)%Z) with true. cbv beta iota. reflexivity.
  - apply ranges_avoid_cons; [exact Av0 | apply ranges_avoid_nil].
  - intros mdl' M1 M2. unfold ms. rewrite adv_set_epend. apply Hc; assumption.
Qed.
End FPG.
End WithRel.

(* [comment removed for export] *)
From OSSVerify.glaze.binary_reflection.images Require Import Asan.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsStdioWrite_run1. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsStdioWrite_run1.AsStdioDefs.

Theorem asan_HW1 : forall (R : shape_rel RSEGS) (fx : FPState), @HYP_writev1_wall_stmt fx R.
Proof.
  intros R fx H A F regs pc m model w fd iov b1 n1 bs1 K _ _ Hwf Hinv Hcov _ HF HE Hh Hfd Hfdr H17 H10 H11 H12 Rb1 Rn1 Rs1 Av1 Av2 Hiok Hb1 Ht1 Ht30 HK Hk.
  exact (sr_writev1_wall_lazy RSEGS R H A F regs pc m model w fd iov b1 n1 bs1 K Hwf Hinv Hcov HF HE Hh Hfd Hfdr H17 H10 H11 H12 Rb1 Rn1 Rs1 Av1 Av2 Hiok Hb1 Ht1 Ht30 HK Hk).
Qed.
Theorem asan_HW2 : forall (R : shape_rel RSEGS) (fx : FPState), @HYP_writev2_wall_stmt fx R.
Proof.
  intros R fx H A F regs pc m model w fd iov b1 n1 b2 n2 bs1 bs2 K _ _ Hwf Hinv Hcov _ HF HE Hh Hfd Hfdr H17 H10 H11 H12 Rb1 Rn1 Rb2 Rn2 Rs1 Rs2 Av0 Av1 Av2 Hiok Hb1 Hb2 Ht1 Ht30 HK Hk.
  exact (sr_writev2_wall_lazy RSEGS R H A F regs pc m model w fd iov b1 n1 b2 n2 bs1 bs2 K Hwf Hinv Hcov HF HE Hh Hfd Hfdr H17 H10 H11 H12 Rb1 Rn1 Rb2 Rn2 Rs1 Rs2 Av0 Av1 Av2 Hiok Hb1 Hb2 Ht1 Ht30 HK Hk).
Qed.
Theorem asan_HW0 : forall (R : shape_rel RSEGS) (fx : FPState), @HYP_writev1_zero_stmt fx R.
Proof.
  intros R fx H A F regs pc m model w fd iov b1 K _ _ Hwf Hinv Hcov _ HF HE Hh Hfd Hfdr H17 H10 H11 H12 Rb1 Rn1 Av0 Hiok Hb1 Hc.
  exact (sr_writev1_zero_lazy RSEGS R H A F regs pc m model w fd iov b1 K Hwf Hinv Hcov HF HE Hh Hfd Hfdr H17 H10 H11 H12 Rb1 Rn1 Av0 Hiok Hb1 Hc).
Qed.
