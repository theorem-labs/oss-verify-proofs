(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Export ShapeSet RealizesCfg SysNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim SeqExec.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition DCFG : SpuriousCfg := mkSpuriousCfg false true true true true true.

Lemma DCFG_alloc : sc_alloc DCFG = false. Proof. reflexivity. Qed.
Lemma DCFG_fs : sc_fs DCFG = true. Proof. reflexivity. Qed.

Abbreviation realizes segs c T := (realizes_cfg segs DCFG c T).

Lemma isteps_of_msteps' : forall segs ms ms', CatSim.msteps segs ms ms' -> isteps segs ms ms'.
Proof.
  intros segs ms ms' H. induction H as [ms | ms ms1 ms2 Hsvc Hst _ IH];
    [apply ist_refl | eapply ist_step; eassumption].
Qed.

(* [comment removed for export] *)
Lemma u64_roundtrip' : forall (x : word), Z_to_bv 64 (bv_unsigned x) = x.
Proof. exact u64_roundtrip. Qed.

Section Compat.
Context {fx : FPState}.
Variable segs : list Segment.

#[using="Type"] Lemma rz_msteps : forall ms ms' model T,
  m_halted model = None -> m_vm_lazy model = [] ->
  CatSim.msteps segs ms ms' ->
  realizes segs (mkCfg ms' model) T ->
  realizes segs (mkCfg ms model) T.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros ms ms' model T Hh Hl Hms H. eapply rzc_isteps; [exact Hh | exact Hl | | exact H].
  apply isteps_of_msteps'. exact Hms.
Qed.

#[using="Type"] Lemma rz_conseq : forall c T T', realizes segs c T -> t_eq T T' -> realizes segs c T'.
Proof. LiaFast.lf_pins LiaFast.u0. intros. eapply rzc_conseq; eassumption. Qed.

#[using="Type"] Lemma realizes_nonempty : forall c T, realizes segs c T -> T [].
Proof. LiaFast.lf_pins LiaFast.u0. intros c T H. exact (realizes_cfg_nonempty segs DCFG c T H). Qed.

#[using="Type"] Lemma rz_emit_nil : forall c K, realizes segs c K -> realizes segs c (t_emit [] K).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros c K H. eapply rz_conseq; [exact H|].
  apply t_eq_sym. apply t_emit_nil_eq. exact (realizes_nonempty _ _ H).
Qed.

#[using="Type"] Lemma t_emit_nil_exit : forall code fs, t_eq (t_exit code fs) (t_emit [] (t_exit code fs)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros code fs. apply t_eq_sym. apply t_emit_nil_eq.
  unfold t_exit, t_emit. left. apply is_prefix_nil.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rz_exit_at : forall regs (pc : word) mem rom model w code,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  (getr regs 17 = Z_to_bv 64 94 \/ getr regs 17 = Z_to_bv 64 93) ->
  getr regs 10 = code ->
  realizes segs (mkCfg (mkst regs pc mem rom) model)
           (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs pc mem rom model w code HF HE Hh Hl H17 H10. subst code.
  apply (rzc_exit_at segs DCFG regs pc mem rom model w HF HE Hh Hl).
  destruct H17 as [H|H]; [right|left]; exact H.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rz_writev2_wall : forall regs (pc : word) mem model w (fd : Z) (iov b1 n1 b2 n2 : word) bs1 bs2 (K : TSet),
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
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
  (1 <= bv_unsigned n1 + bv_unsigned n2)%Z ->
  (bv_unsigned n1 + bv_unsigned n2 <= 2 ^ 30)%Z ->
  (bv_unsigned n1 + bv_unsigned n2 <= 2 ^ 30)%Z ->
  (bv_unsigned iov + 32 <= TASK_SIZE)%Z ->
  (bv_unsigned b1 + bv_unsigned n1 <= TASK_SIZE)%Z ->
  (bv_unsigned b2 + bv_unsigned n2 <= TASK_SIZE)%Z ->
  K [] ->
  (forall k, (1 <= k)%nat -> (k <= length (bs1 ++ bs2))%nat ->
     realizes segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat k))) (v_addi pc 4) mem (seg_rom segs)) model)
              (t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k (bs1 ++ bs2))) K)) ->
  realizes segs (mkCfg (mkst regs pc mem (seg_rom segs)) model)
           (t_emit (map (WriteEv (Z_to_bv 64 fd)) (bs1 ++ bs2)) K).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs pc mem model w fd iov b1 n1 b2 n2 bs1 bs2 K HF HE Hh Hl Hfd Hfdr H17 H10 H11 H12
         Rb1 Rn1 Rb2 Rn2 B1 B2 Ht1 Hmax Ht30 Tiov Tb1 Tb2 HK0 HK.
  eapply rzc_ecall; [exact Hh | exact Hl | exact HF | exact HE |].
  assert (Hfd32 : fd32 (getr regs 10) = Z_to_bv 64 fd).
  { rewrite H10. apply fd32_id. rewrite u64_lit by lia. lia. }
  pose proof (bv_unsigned_in_range 64 n1) as Hn1. pose proof (bv_unsigned_in_range 64 n2) as Hn2.
  pose proof (bv_unsigned_in_range 64 iov) as Hiov. unfold bv_modulus in Hn1, Hn2, Hiov. unfold TASK_SIZE in *.
  assert (E12 : getr regs 12 = Z_to_bv 64 (Z.of_nat (length [(b1, n1); (b2, n2)]))) by (rewrite H12; reflexivity).
  assert (Hcnt : (1 <= length [(b1, n1); (b2, n2)] <= 1024)%nat) by (cbn; lia).
  assert (Hiok : (bv_unsigned (getr regs 11) + 16 * Z.of_nat (length [(b1, n1); (b2, n2)]) <= TASK_SIZE)%Z)
    by (cbn [length]; rewrite H11; unfold TASK_SIZE; lia).
  assert (Harr : iov_array segs mem (getr regs 11) [(b1, n1); (b2, n2)]).
  { rewrite H11. cbn [iov_array]. refine (conj Rb1 (conj Rn1 (conj _ (conj _ (conj _ (conj _ I)))))).
    - lia.
    - replace (Z_to_bv 64 (bv_unsigned iov + 16)) with (Z_to_bv 64 (bv_unsigned iov + 16)) by reflexivity. exact Rb2.
    - replace (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned iov + 16)) + 8))
        with (Z_to_bv 64 (bv_unsigned iov + 24)) by (f_equal; rewrite u64_lit by (unfold TASK_SIZE in *; lia); lia).
      exact Rn2.
    - lia. }
  assert (Hbok : iov_bufs_ok [(b1, n1); (b2, n2)]) by (cbn [iov_bufs_ok]; auto).
  assert (Hbufs : iov_bufs segs mem [(b1, n1); (b2, n2)] [bs1; bs2]) by (cbn [iov_bufs]; auto).
  assert (T1 : (1 <= iovs_total [(b1, n1); (b2, n2)])%Z) by (cbn [iovs_total]; lia).
  assert (T30 : (iovs_total [(b1, n1); (b2, n2)] <= 2 ^ 30)%Z) by (cbn [iovs_total]; lia).
  assert (Hw : w_is0 (Z_to_bv 64 fd) = false) by (apply w_is0_pos; rewrite u64_lit by lia; lia).
  assert (Hfd' : fd_lookup (m_fds model) (fd32 (getr regs 10)) = Some (FdChannel (Z_to_bv 64 fd)))
    by (rewrite Hfd32; exact Hfd).
  pose proof (rzc_writev_ch_wall segs DCFG regs pc mem model (Z_to_bv 64 fd) [(b1, n1); (b2, n2)] [bs1; bs2] K
           Hh Hl H17 Hfd' Hw E12 Hcnt Hiok Harr Hbok Hbufs T1 T30 HK0) as R.
  cbn [concat] in R. rewrite app_nil_r in R. apply R.
  intros k Hk1 Hk2. apply HK; assumption.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rz_writev1_wall : forall regs (pc : word) mem model w (fd : Z) (iov b1 n1 : word) bs1 (K : TSet),
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  (0 < fd < 2^31)%Z ->
  getr regs 17 = Z_to_bv 64 66 ->
  getr regs 10 = Z_to_bv 64 fd ->
  getr regs 11 = iov ->
  getr regs 12 = Z_to_bv 64 1 ->
  rdn segs mem iov 8%nat = Some (word_to_le_bytes 8 b1) ->
  rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 8)) 8%nat = Some (word_to_le_bytes 8 n1) ->
  rdn segs mem b1 (word_to_nat n1) = Some bs1 ->
  (1 <= bv_unsigned n1)%Z ->
  (bv_unsigned n1 <= 2 ^ 30)%Z ->
  (bv_unsigned n1 <= 2 ^ 30)%Z ->
  (bv_unsigned iov + 16 <= TASK_SIZE)%Z ->
  (bv_unsigned b1 + bv_unsigned n1 <= TASK_SIZE)%Z ->
  K [] ->
  (forall k, (1 <= k)%nat -> (k <= length bs1)%nat ->
     realizes segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat k))) (v_addi pc 4) mem (seg_rom segs)) model)
              (t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k bs1)) K)) ->
  realizes segs (mkCfg (mkst regs pc mem (seg_rom segs)) model)
           (t_emit (map (WriteEv (Z_to_bv 64 fd)) bs1) K).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs pc mem model w fd iov b1 n1 bs1 K HF HE Hh Hl Hfd Hfdr H17 H10 H11 H12
         Rb1 Rn1 B1 Ht1 Hmax Ht30 Tiov Tb1 HK0 HK.
  eapply rzc_ecall; [exact Hh | exact Hl | exact HF | exact HE |].
  assert (Hfd32 : fd32 (getr regs 10) = Z_to_bv 64 fd).
  { rewrite H10. apply fd32_id. rewrite u64_lit by lia. lia. }
  pose proof (bv_unsigned_in_range 64 n1) as Hn1.
  pose proof (bv_unsigned_in_range 64 iov) as Hiov. unfold bv_modulus in Hn1, Hiov. unfold TASK_SIZE in *.
  assert (E12 : getr regs 12 = Z_to_bv 64 (Z.of_nat (length [(b1, n1)]))) by (rewrite H12; reflexivity).
  assert (Hcnt : (1 <= length [(b1, n1)] <= 1024)%nat) by (cbn; lia).
  assert (Hiok : (bv_unsigned (getr regs 11) + 16 * Z.of_nat (length [(b1, n1)]) <= TASK_SIZE)%Z)
    by (cbn [length]; rewrite H11; unfold TASK_SIZE; lia).
  assert (Harr : iov_array segs mem (getr regs 11) [(b1, n1)]).
  { rewrite H11. cbn [iov_array]. refine (conj Rb1 (conj Rn1 (conj _ I))). lia. }
  assert (Hbok : iov_bufs_ok [(b1, n1)]) by (cbn [iov_bufs_ok]; auto).
  assert (Hbufs : iov_bufs segs mem [(b1, n1)] [bs1]) by (cbn [iov_bufs]; auto).
  assert (T1 : (1 <= iovs_total [(b1, n1)])%Z) by (cbn [iovs_total]; lia).
  assert (T30 : (iovs_total [(b1, n1)] <= 2 ^ 30)%Z) by (cbn [iovs_total]; lia).
  assert (Hw : w_is0 (Z_to_bv 64 fd) = false) by (apply w_is0_pos; rewrite u64_lit by lia; lia).
  assert (Hfd' : fd_lookup (m_fds model) (fd32 (getr regs 10)) = Some (FdChannel (Z_to_bv 64 fd)))
    by (rewrite Hfd32; exact Hfd).
  pose proof (rzc_writev_ch_wall segs DCFG regs pc mem model (Z_to_bv 64 fd) [(b1, n1)] [bs1] K
           Hh Hl H17 Hfd' Hw E12 Hcnt Hiok Harr Hbok Hbufs T1 T30 HK0) as R.
  cbn [concat] in R. rewrite app_nil_r in R. apply R.
  intros k Hk1 Hk2. apply HK; assumption.
Qed.

End Compat.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Zero.
Context {fx : FPState}.
Variable segs : list Segment.

#[using="Type"] Lemma rz_writev1_zero : forall regs (pc : word) mem model w (fd : Z) (iov b1 : word) K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  (0 < fd < 2^31)%Z ->
  getr regs 17 = Z_to_bv 64 66 ->
  getr regs 10 = Z_to_bv 64 fd ->
  getr regs 11 = iov ->
  getr regs 12 = Z_to_bv 64 1 ->
  rdn segs mem iov 8%nat = Some (word_to_le_bytes 8 b1) ->
  rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 8)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  (0 <= rw_bytes_max)%Z ->
  (bv_unsigned iov + 16 <= TASK_SIZE)%Z ->
  (bv_unsigned b1 <= TASK_SIZE)%Z ->
  realizes segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) mem (seg_rom segs)) model) K ->
  realizes segs (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs pc mem model w fd iov b1 K HF HE Hh Hl Hfd Hfdr H17 H10 H11 H12 Rb1 Rn1 Hmax Tiov Tb1 HK.
  eapply rzc_ecall; [exact Hh | exact Hl | exact HF | exact HE |].
  assert (Hfd32 : fd32 (getr regs 10) = Z_to_bv 64 fd).
  { rewrite H10. apply fd32_id. rewrite u64_lit by lia. lia. }
  pose proof (bv_unsigned_in_range 64 iov) as Hiov. unfold bv_modulus in Hiov. unfold TASK_SIZE in *.
  set (ms := epend regs pc mem (seg_rom segs) (getr regs 17)).
  set (i := sys_input segs ms (getr regs 17)).
  assert (A0 : in_arg i 0 = getr regs 10) by apply in_arg0_epend.
  assert (A1 : in_arg i 1 = getr regs 11) by apply in_arg1_epend.
  assert (A2 : in_arg i 2 = getr regs 12) by apply in_arg2_epend.
  assert (M0 : in_mem i = mrb segs mem) by reflexivity.
  assert (Hno : bv_unsigned (in_sysno i) = 66%Z) by (cbn [in_sysno i sys_input]; rewrite H17; reflexivity).
  assert (Harr : iov_array segs mem iov [(b1, Z_to_bv 64 0)]).
  { cbn [iov_array]. refine (conj Rb1 (conj Rn1 (conj _ I))). rewrite u64_lit by lia. lia. }
  assert (Himp : import_iovecs (mrb segs mem) iov (Z_to_bv 64 (Z.of_nat (length [(b1, Z_to_bv 64 0)])))
                 = ImpOk [(b1, Z_to_bv 64 0)]).
  { apply import_iovecs_of_array; [cbn; lia | cbn [length]; unfold TASK_SIZE; lia | exact Harr |].
    cbn [iov_bufs_ok]. rewrite u64_lit by lia. split; [unfold TASK_SIZE; lia | exact I]. }
  set (CA := import_iovecs_accesses (mrb segs mem) iov (Z_to_bv 64 1)).
  assert (Hsp : forall eff m1 evs, syscall_spec i model (Ok eff m1 evs) <->
                  eff = ret_ci (Z_to_bv 64 0) (CA ++ []) /\ m1 = model /\ evs = []).
  { intros eff m1 evs. rewrite (syscall_spec_66 i model _ Hno). rewrite A0, A1, A2, H12, Hfd32.
    unfold writev_spec. rewrite bind_input, bind_get_model. rewrite Hfd.
    replace (w_is0 (Z_to_bv 64 fd)) with false by (symmetry; apply w_is0_pos; rewrite u64_lit by lia; lia).
    rewrite M0. change (iovcnt32 (Z_to_bv 64 1)) with (Z_to_bv 64 1). rewrite H11.
    rewrite record_copyins_ok_iff. change (Z.of_nat (length [(b1, Z_to_bv 64 0)])) with 1%Z in Himp. rewrite Himp. fold CA.
    cbv beta iota zeta. cbn [iovs_total cap_iovecs cap_iovecs_aux].
    assert (E0 : (bv_unsigned (Z_to_bv 64 (Z.min MAX_RW_COUNT (bv_unsigned (Z_to_bv 64 0)))) + 0 =? 0)%Z = true)
      by (vm_compute; reflexivity).
    rewrite E0.
    unfold ret_only, pure. split.
    - intros (eff0 & H & ->). injection H; intros; subst. split; [|auto].
      unfold with_copyins, ret_ci. reflexivity.
    - intros (-> & -> & ->). exists (mkEffect (Z_to_bv 64 0) [] []). split; [reflexivity|].
      unfold with_copyins, ret_ci. reflexivity. }
  apply (rzc_sys_det segs DCFG ms model (getr regs 17) (ret_ci (Z_to_bv 64 0) (CA ++ [])) model K);
    [exact Hh | reflexivity | apply Hsp; auto | intros; apply Hsp; assumption | | | exact Hh | exact Hl | ].
  - intros Hs. fold i in Hs. rewrite (syscall_spec_66 i model _ Hno) in Hs. rewrite A0, A1, A2, H12, Hfd32 in Hs.
    unfold writev_spec in Hs. rewrite bind_input, bind_get_model in Hs. rewrite Hfd in Hs.
    replace (w_is0 (Z_to_bv 64 fd)) with false in Hs by (symmetry; apply w_is0_pos; rewrite u64_lit by lia; lia).
    rewrite M0 in Hs. change (iovcnt32 (Z_to_bv 64 1)) with (Z_to_bv 64 1) in Hs. rewrite H11 in Hs.
    apply record_copyins_unmodeled_iff in Hs. change (Z.of_nat (length [(b1, Z_to_bv 64 0)])) with 1%Z in Himp. rewrite Himp in Hs.
    cbv beta iota zeta in Hs. cbn [iovs_total cap_iovecs cap_iovecs_aux] in Hs.
    assert (E0 : (bv_unsigned (Z_to_bv 64 (Z.min MAX_RW_COUNT (bv_unsigned (Z_to_bv 64 0)))) + 0 =? 0)%Z = true)
      by (vm_compute; reflexivity).
    rewrite E0 in Hs.
    unfold ret_only, pure in Hs. discriminate.
  - intros eff. apply not_spurious_uninjected. fold i. rewrite Hno. reflexivity.
  - unfold ms, ret_ci. rewrite adv_epend_ret. exact HK.
Qed.

End Zero.
