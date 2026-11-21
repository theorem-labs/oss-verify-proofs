(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* Modified by Theorem Labs, 2026-11: made from Common/SysNodesCfg.v: the R-typed declarations restated over the budget carrier, with twin modules imported last. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the channel-reader premise of writev; RomBase.sys_rob at the system-call nodes). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi Syscall.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec SeqExec ShapeSet RealizesCfg.
Import ListNotations.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel Require Import Exit Fork.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Prelude.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import SysNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.BudgetWit Require Import Rzb.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require RomBase RomWrite.

Open Scope bv_scope.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Section Generic.
Context {fx : FPState}.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
#[using="Type"] Lemma rzb_ecall : forall regs pc mem rom model w T,
  m_halted model = None -> m_vm_lazy model = [] ->
  fetch_word segs pc = Some w -> is_ecall w = true ->
  Rzb.rzb segs cfg (mkCfg (SysNodesCfg.epend regs pc mem rom (getr regs 17)) model) T ->
  Rzb.rzb segs cfg (mkCfg (mkst regs pc mem rom) model) T.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs pc mem rom model w T Hh Hl HF HE H.
  eapply Rzb.rzb_step; [exact Hh | exact Hl | reflexivity | | exact H].
  exact (SysNodesCfg.step_ecall_epend segs regs pc mem rom w HF HE).
Qed.
#[using="Type"] Lemma rzb_sys_det : forall ms model x8 eff m' T,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  ~ In (bv_unsigned (in_sysno (sys_input segs ms x8))) alloc_mark_sysnos ->
  syscall_spec (sys_input segs ms x8) model (Ok eff m' []) ->
  (forall eff1 m1 evs1, syscall_spec (sys_input segs ms x8) model (Ok eff1 m1 evs1) ->
     eff1 = eff /\ m1 = m' /\ evs1 = []) ->
  ~ syscall_spec (sys_input segs ms x8) model Unmodeled ->
  (forall eff1, ~ spurious_refusal_cfg cfg (sys_input segs ms x8) model eff1) ->
  m_halted m' = None -> m_vm_lazy m' = [] ->
  RomBase.sys_rob segs (mkCfg ms model) ->
  Rzb.rzb segs cfg (mkCfg (advance_past_svc (apply_effect ms eff)) m') T ->
  Rzb.rzb segs cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros ms model x8 eff m' T Hh Hsvc Hna Hc Hs Hnu Hns HhM HlM Hrob HK.
  eapply Rzb.rzb_conseq.
  - apply (Rzb.rzb_sys segs cfg ms model x8 unit (fun _ => eff) (fun _ => m') (fun _ => []) (fun _ => T) tt);
      try assumption.
    + intros j. exact Hc.
    + intros eff1 m1 evs1 H. exists tt. exact (Hs _ _ _ H).
    + intros j. exact HhM.
    + intros j. exact HlM.
    + intros j. exact HK.
  - apply SysNodesCfg.t_alt_const_nil; [exact tt|]. exact (Rzb.rzb_nonempty segs cfg _ _ HK).
Qed.
End Generic.
Section Kernel.
Context {fx : FPState}.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
#[using="Type"] Lemma rzb_set_tid : forall regs (pc : word) mem rom model w T,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 96 ->
  m_tid model = None ->
  (forall tid, (0 < bv_unsigned tid < PID_MAX_ENVELOPE)%Z ->
     Rzb.rzb segs cfg (mkCfg (mkst (regupd regs 10 tid) (v_addi pc 4) mem rom) (with_tid tid model)) T) ->
  Rzb.rzb segs cfg (mkCfg (mkst regs pc mem rom) model) T.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs pc mem rom model w T HF HE Hh Hlazy H17 Htid Hk.
  eapply rzb_ecall; [exact Hh | exact Hlazy | exact HF | exact HE |].
  set (ms := SysNodesCfg.epend regs pc mem rom (getr regs 17)).
  set (x8 := getr regs 17).
  assert (Hno : bv_unsigned (in_sysno (sys_input segs ms x8)) = 96%Z) by (cbn; unfold x8; rewrite H17; reflexivity).
  assert (Hsp : forall o, syscall_spec (sys_input segs ms x8) model o
                          <-> set_tid_address_spec (sys_input segs ms x8) model o)
    by (intro o; exact (SysNodesCfg.syscall_spec_no _ _ _ 96 _ Hno eq_refl)).
  set (I := {t : word | (0 < bv_unsigned t < PID_MAX_ENVELOPE)%Z}).
  assert (i0 : I) by (exists (Z_to_bv 64 1); split; vm_compute; reflexivity).
  eapply Rzb.rzb_conseq.
  - apply (Rzb.rzb_sys segs cfg ms model x8 I (fun j => mkEffect (proj1_sig j) [] [])
             (fun j => with_tid (proj1_sig j) model) (fun _ => []) (fun _ => T) i0);
      [exact Hh | reflexivity | exact (Rzb.not_alloc_no _ 96 Hno eq_refl) | | | | | | | exact (RomWrite.rob_memfree_no segs ms model x8 96 eq_refl Hno RomBase.memfree_96) | ].
    + intros [t Ht]. apply Hsp. apply SysNodesCfg.set_tid_fresh_ok; [exact Htid|]. exists t. auto.
    + intros eff m' evs Hs. apply Hsp in Hs. apply SysNodesCfg.set_tid_fresh_ok in Hs as (t & Ht & -> & -> & ->); [|exact Htid].
      exists (exist _ t Ht). auto.
    + intros Hs. apply Hsp in Hs. exact (SysNodesCfg.set_tid_fresh_unmodeled _ _ Htid Hs).
    + intros eff. apply SysNodesCfg.not_spurious_uninjected. rewrite Hno. reflexivity.
    + intros j. rewrite SysNodesCfg.with_tid_halted. exact Hh.
    + intros j. rewrite SysNodesCfg.with_tid_lazy. exact Hlazy.
    + intros [t Ht]. cbn [proj1_sig]. unfold ms. rewrite SysNodesCfg.adv_epend_ret. apply Hk. exact Ht.
  - apply SysNodesCfg.t_alt_const_nil; [exact i0|].
    destruct i0 as [t Ht]. exact (Rzb.rzb_nonempty segs cfg _ _ (Hk t Ht)).
Qed.
#[using="Type"] Lemma rzb_exit_at : forall regs (pc : word) mem rom model w,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  (getr regs 17 = Z_to_bv 64 93 \/ getr regs 17 = Z_to_bv 64 94) ->
  Rzb.rzb segs cfg (mkCfg (mkst regs pc mem rom) model)
    (t_exit (bv_and (getr regs 10) (Z_to_bv 64 255)) (m_fs model)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs pc mem rom model w HF HE Hh Hlazy H17.
  eapply rzb_ecall; [exact Hh | exact Hlazy | exact HF | exact HE |].
  replace (getr regs 10) with (ms_gpr (SysNodesCfg.epend regs pc mem rom (getr regs 17)) 0)
    by (rewrite SysNodesCfg.ms_gpr_epend by lia; f_equal).
  apply (Rzb.rzb_exit segs cfg _ model (getr regs 17)); [exact Hh | reflexivity |].
  unfold exit_sysno. destruct H17 as [H|H]; rewrite H; [left|right]; reflexivity.
Qed.
End Kernel.
Section Writev.
Context {fx : FPState}.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Local Abbreviation PEND regs pc mem := (SysNodesCfg.epend regs pc mem (seg_rom segs) (getr regs 17)).
#[using="Type"] Lemma u64_roundtrip : forall (x : word), Z_to_bv 64 (bv_unsigned x) = x.
Proof. LiaFast.lf_pins LiaFast.u0. intros x. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.
#[using="Type"] Lemma bv_add_Zform : forall (a b : word), a + b = Z_to_bv 64 (bv_unsigned a + bv_unsigned b).
Proof. LiaFast.lf_pins LiaFast.u0. intros a b. apply bv_eq. rewrite bv_add_unsigned, Z_to_bv_unsigned. reflexivity. Qed.
#[using="Type"] Lemma word_to_nat_Z : forall z, (0 <= z < 2^64)%Z -> word_to_nat (Z_to_bv 64 z) = Z.to_nat z.
Proof. LiaFast.lf_pins LiaFast.u0. intros z Hz. unfold word_to_nat. rewrite SysNodesCfg.u64_lit by exact Hz. reflexivity. Qed.
#[using="Type"] Lemma access_okb_of_le : forall (b : word) (n : Z),
  (0 <= n)%Z -> (bv_unsigned b + n <= TASK_SIZE)%Z -> access_okb b n = true.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros b n Hn H. unfold access_okb. pose proof (bv_unsigned_in_range 64 b) as [Hb _].
  apply andb_true_iff. split; apply Z.leb_le; lia.
Qed.
#[using="Type"] Lemma mrb_read_aux : forall mem k a,
  read_bytes_aux (SysNodesCfg.mrb segs mem) a k = rdn segs mem a k.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros mem k; induction k as [|k IH]; intros a; [reflexivity|].
  cbn [read_bytes_aux rdn]. unfold SysNodesCfg.mrb. rewrite IH. reflexivity.
Qed.
#[using="Type"] Lemma mrb_read_bytes : forall mem a n,
  read_bytes_map (SysNodesCfg.mrb segs mem) a n = rdn segs mem a (word_to_nat n).
Proof. LiaFast.lf_pins LiaFast.u0. intros mem a n. rewrite read_bytes_map_eq. apply mrb_read_aux. Qed.
#[using="Type"] Lemma read_u64_rdn : forall mem a v,
  rdn segs mem a 8%nat = Some (word_to_le_bytes 8 v) ->
  read_u64 (SysNodesCfg.mrb segs mem) a = Some v.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros mem a v H. unfold read_u64. rewrite mrb_read_bytes.
  change (word_to_nat (Z_to_bv 64 8)) with 8%nat. rewrite H.
  f_equal. apply le_word_v. apply bytes_le_to_Z_8.
Qed.
#[using="Type"] Lemma read_iovec_entry_of_array : forall mem b n r iov,
  (SysNodesCfg.iov_array segs) mem iov ((b, n) :: r) ->
  read_iovec_entry (SysNodesCfg.mrb segs mem) iov = IovEntry b n.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros mem b n r iov (Hb & Hn & Hlt & _). unfold read_iovec_entry.
  rewrite (read_u64_rdn mem iov b Hb).
  rewrite bv_add_Zform. change (bv_unsigned (8 : word)) with 8%Z.
  rewrite (read_u64_rdn mem _ n Hn).
  rewrite (proj2 (Z.leb_gt _ _) Hlt). reflexivity.
Qed.
#[using="Type"] Lemma copy_iovecs_of_array : forall mem iovs iov,
  (SysNodesCfg.iov_array segs) mem iov iovs ->
  copy_iovecs_aux (SysNodesCfg.mrb segs mem) iov (length iovs) = ImpOk iovs.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros mem iovs; induction iovs as [|[b n] r IH]; intros iov Ha; [reflexivity|].
  cbn [length copy_iovecs_aux].
  rewrite (read_iovec_entry_of_array mem b n r iov Ha).
  destruct Ha as (_ & _ & _ & Hr).
  rewrite bv_add_Zform. change (bv_unsigned (16 : word)) with 16%Z.
  rewrite (IH _ Hr). reflexivity.
Qed.
#[using="Type"] Lemma gather_of_bufs : forall mem iovs bss,
  (SysNodesCfg.iov_bufs segs) mem iovs bss ->
  gather_iovecs (SysNodesCfg.mrb segs mem) iovs = Some (concat bss).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros mem iovs; induction iovs as [|[b n] r IH]; intros [|bs bss] Hb; cbn in Hb; try contradiction.
  - reflexivity.
  - destruct Hb as [H1 H2]. cbn [gather_iovecs concat].
    rewrite mrb_read_bytes, H1, (IH bss H2). reflexivity.
Qed.
#[using="Type"] Lemma cap_iovecs_id : forall iovs left,
  (iovs_total iovs <= left)%Z -> cap_iovecs_aux iovs left = iovs.
Proof. LiaFast.lf_pins LiaFast.u0.
  induction iovs as [|[b n] r IH]; intros left H; [reflexivity|].
  cbn [cap_iovecs_aux]. cbn [iovs_total] in H. pose proof (iovs_total_nonneg r).
  rewrite Z.min_r by lia. rewrite u64_roundtrip, IH by lia. reflexivity.
Qed.
#[using="Type"] Lemma iovs_access_okb_of_ok : forall iovs, SysNodesCfg.iov_bufs_ok iovs -> iovs_access_okb iovs = true.
Proof. LiaFast.lf_pins LiaFast.u0.
  induction iovs as [|[b n] r IH]; intros H; [reflexivity|].
  destruct H as [Hb Hr]. unfold iovs_access_okb. cbn [forallb fst snd].
  rewrite (access_okb_intro b n Hb). cbn [andb]. exact (IH Hr).
Qed.
#[using="Type"] Lemma import_iovecs_of_array : forall mem iovs iov,
  (1 <= length iovs <= 1024)%nat ->
  (bv_unsigned iov + 16 * Z.of_nat (length iovs) <= TASK_SIZE)%Z ->
  (SysNodesCfg.iov_array segs) mem iov iovs ->
  SysNodesCfg.iov_bufs_ok iovs ->
  import_iovecs (SysNodesCfg.mrb segs mem) iov (Z_to_bv 64 (Z.of_nat (length iovs))) = ImpOk iovs.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros mem iovs iov Hcnt Hok Harr Hbok. unfold import_iovecs.
  destruct iovs as [|[b n] r]; [cbn in Hcnt; lia|].
  destruct r as [|[b2 n2] r2].
  - cbn [length] in *. change (Z.of_nat 1) with 1%Z in *.
    rewrite (proj2 (bv_eqb_eq _ _) eq_refl).
    rewrite (access_okb_of_le iov 16) by lia.
    rewrite (read_iovec_entry_of_array mem b n [] iov Harr).
    destruct Hbok as [Hb _]. pose proof (bv_unsigned_in_range 64 n) as Hn. unfold bv_modulus in Hn.
    rewrite (access_okb_of_le b (Z.min (bv_unsigned n) MAX_RW_COUNT))
      by (unfold MAX_RW_COUNT in *; lia).
    reflexivity.
  - set (cnt := Z.of_nat (length ((b, n) :: (b2, n2) :: r2))) in *.
    assert (Hc2 : (2 <= cnt <= 1024)%Z) by (unfold cnt; cbn [length] in *; lia).
    assert (E1 : bv_eqb (Z_to_bv 64 cnt) (Z_to_bv 64 1) = false).
    { unfold bv_eqb. apply Z.eqb_neq. rewrite !SysNodesCfg.u64_lit by lia. lia. }
    assert (E0 : bv_eqb (Z_to_bv 64 cnt) (Z_to_bv 64 0) = false).
    { unfold bv_eqb. apply Z.eqb_neq. rewrite !SysNodesCfg.u64_lit by lia. lia. }
    rewrite E1, E0. rewrite SysNodesCfg.u64_lit by lia.
    replace ((IOV_MAX <? cnt)%Z) with false by (symmetry; apply Z.ltb_ge; unfold IOV_MAX; lia).
    rewrite (access_okb_of_le iov (16 * cnt)) by lia.
    rewrite word_to_nat_Z by lia. unfold cnt. rewrite Nat2Z.id.
    rewrite (copy_iovecs_of_array mem _ iov Harr).
    rewrite (iovs_access_okb_of_ok _ Hbok). reflexivity.
Qed.
#[using="Type"] Lemma writev_ch_ok_iff : forall regs pc mem model (ch : word) iovs bss eff m' evs,
  getr regs 17 = Z_to_bv 64 66 ->
  fd_lookup (m_fds model) (fd32 (getr regs 10)) = Some (FdChannel ch) ->
  w_is0 ch = false ->
  getr regs 12 = Z_to_bv 64 (Z.of_nat (length iovs)) ->
  (1 <= length iovs <= 1024)%nat ->
  (bv_unsigned (getr regs 11) + 16 * Z.of_nat (length iovs) <= TASK_SIZE)%Z ->
  (SysNodesCfg.iov_array segs) mem (getr regs 11) iovs -> SysNodesCfg.iov_bufs_ok iovs -> (SysNodesCfg.iov_bufs segs) mem iovs bss ->
  (1 <= iovs_total iovs)%Z -> (iovs_total iovs <= 2 ^ 30)%Z ->
  (* the far end has a reader: writev's channel arm raises SIGPIPE otherwise *)
  m_channel_reader model = true ->
  let bs := concat bss in
  let CA := import_iovecs_accesses (SysNodesCfg.mrb segs mem) (getr regs 11) (Z_to_bv 64 (Z.of_nat (length iovs))) in
  (syscall_spec (sys_input segs (PEND regs pc mem) (getr regs 17)) model (Ok eff m' evs) <->
   exists k, (1 <= k <= length bs)%nat
     /\ eff = SysNodesCfg.ret_ci (Z_to_bv 64 (Z.of_nat k)) (CA ++ (iov_prefix_accesses iovs k ++ []))
     /\ m' = model /\ evs = map (WriteEv ch) (firstn k bs)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs pc mem model ch iovs bss eff m' evs H17 Hfd Hch H12 Hcnt Hiok Harr Hbok Hbufs Ht1 Ht30 Hrd bs CA.
  set (i := sys_input segs (PEND regs pc mem) (getr regs 17)).
  assert (A0 : in_arg i 0 = getr regs 10) by apply SysNodesCfg.in_arg0_epend.
  assert (A1 : in_arg i 1 = getr regs 11) by apply SysNodesCfg.in_arg1_epend.
  assert (A2 : in_arg i 2 = getr regs 12) by apply SysNodesCfg.in_arg2_epend.
  assert (M0 : in_mem i = SysNodesCfg.mrb segs mem) by reflexivity.
  assert (Hno : bv_unsigned (in_sysno i) = 66%Z) by (cbn [in_sysno i sys_input]; rewrite H17; reflexivity).
  pose proof (gather_of_bufs mem iovs bss Hbufs) as Hg. fold bs in Hg.
  pose proof (gather_iovecs_length _ _ _ Hg) as Hlen.
  assert (Hcnt32 : iovcnt32 (Z_to_bv 64 (Z.of_nat (length iovs))) = Z_to_bv 64 (Z.of_nat (length iovs))).
  { unfold iovcnt32, abi_low32. rewrite SysNodesCfg.u64_lit by lia. rewrite Z.mod_small by lia. reflexivity. }
  assert (Hcap : cap_iovecs iovs = iovs).
  { unfold cap_iovecs. apply cap_iovecs_id. unfold MAX_RW_COUNT. lia. }
  assert (Hlw : bv_unsigned (len_word bs) = iovs_total iovs).
  { unfold len_word. rewrite Hlen. apply SysNodesCfg.u64_lit. lia. }
  rewrite (SysNodesCfg.syscall_spec_66 i model _ Hno). rewrite A0, A1, A2, H12.
  unfold writev_spec. rewrite SysNodesCfg.bind_input, bind_get_model. rewrite Hfd, Hch. rewrite M0, Hcnt32.
  rewrite SysNodesCfg.record_copyins_ok_iff.
  rewrite (import_iovecs_of_array mem iovs (getr regs 11) Hcnt Hiok Harr Hbok). fold CA.
  unfold writev_gathered. rewrite Hcap, (gather_prefix_full _ _ _ Hg). fold bs.
  cbv beta iota zeta.
  replace ((iovs_total iovs =? 0)%Z) with false by (symmetry; apply Z.eqb_neq; lia).
  rewrite Hrd. cbn [negb].
  replace ((length bs =? 0)%nat) with false by (symmetry; apply Nat.eqb_neq; lia).
  replace (addr_is_error_b (len_word bs)) with false
    by (symmetry; unfold addr_is_error_b, two_pow_64; apply Z.ltb_ge; rewrite Hlw; lia).
  split.
  - intros (eff0 & Hs & ->).
    unfold bind, choose, emit, pure in Hs. sys_destruct.
    match goal with H : record_copyins _ _ _ _ _ |- _ => apply SysNodesCfg.record_copyins_ok_iff in H as (eff1 & H & ->) end.
    unfold ret_only, pure in *. sys_destruct.
    match goal with H : ?ds = firstn (length ?ds) bs |- _ => rename H into Hds; rename ds into dd end.
    exists (length dd). refine (conj _ (conj _ (conj _ _))); [split; [lia | rewrite Hds; rewrite length_firstn; lia] | | reflexivity | ].
    + unfold with_copyins, SysNodesCfg.ret_ci. cbn [eff_ret eff_writes eff_zeros eff_unmaps eff_copies eff_copyins].
      rewrite !app_nil_r. unfold len_word. reflexivity.
    + rewrite app_nil_r. cbn [app]. f_equal. exact Hds.
  - intros (k & Hk & -> & -> & ->).
    exists (SysNodesCfg.ret_ci (Z_to_bv 64 (Z.of_nat k)) (iov_prefix_accesses iovs k ++ [])). split.
    2:{ unfold with_copyins, SysNodesCfg.ret_ci. cbn [eff_ret eff_writes eff_zeros eff_unmaps eff_copies eff_copyins]. reflexivity. }
    unfold bind, choose, emit, pure.
    exists (firstn k bs), model, [], (map (WriteEv ch) (firstn k bs)). split.
    { exists (firstn k bs). split; [|reflexivity]. rewrite length_firstn, Nat.min_l by lia.
      refine (conj _ (conj _ (conj _ _))).
      - lia.
      - unfold two_pow_64. lia.
      - unfold addr_is_error_b, two_pow_64. apply Z.ltb_ge. unfold len_word. rewrite length_firstn, Nat.min_l by lia.
        rewrite SysNodesCfg.u64_lit by lia. lia.
      - reflexivity. }
    split; [| reflexivity].
    exists tt, model, (map (WriteEv ch) (firstn k bs)), []. split; [reflexivity|]. split; [|rewrite app_nil_r; reflexivity].
    try rewrite Hcap. rewrite length_firstn, Nat.min_l by lia.
    apply SysNodesCfg.record_copyins_ok_iff. exists (mkEffect (len_word (firstn k bs)) [] []). split; [reflexivity|].
    unfold with_copyins, SysNodesCfg.ret_ci, len_word. cbn [eff_ret eff_writes eff_zeros eff_unmaps eff_copies eff_copyins].
    rewrite length_firstn, Nat.min_l by lia. reflexivity.
Qed.
#[using="Type"] Lemma writev_ch_no_unmodeled : forall regs pc mem model (ch : word) iovs bss,
  getr regs 17 = Z_to_bv 64 66 ->
  fd_lookup (m_fds model) (fd32 (getr regs 10)) = Some (FdChannel ch) ->
  w_is0 ch = false ->
  getr regs 12 = Z_to_bv 64 (Z.of_nat (length iovs)) ->
  (1 <= length iovs <= 1024)%nat ->
  (bv_unsigned (getr regs 11) + 16 * Z.of_nat (length iovs) <= TASK_SIZE)%Z ->
  (SysNodesCfg.iov_array segs) mem (getr regs 11) iovs -> SysNodesCfg.iov_bufs_ok iovs -> (SysNodesCfg.iov_bufs segs) mem iovs bss ->
  (1 <= iovs_total iovs)%Z -> (iovs_total iovs <= 2 ^ 30)%Z ->
  m_channel_reader model = true ->
  ~ syscall_spec (sys_input segs (PEND regs pc mem) (getr regs 17)) model Unmodeled.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs pc mem model ch iovs bss H17 Hfd Hch H12 Hcnt Hiok Harr Hbok Hbufs Ht1 Ht30 Hrd.
  set (i := sys_input segs (PEND regs pc mem) (getr regs 17)).
  assert (A0 : in_arg i 0 = getr regs 10) by apply SysNodesCfg.in_arg0_epend.
  assert (A1 : in_arg i 1 = getr regs 11) by apply SysNodesCfg.in_arg1_epend.
  assert (A2 : in_arg i 2 = getr regs 12) by apply SysNodesCfg.in_arg2_epend.
  assert (M0 : in_mem i = SysNodesCfg.mrb segs mem) by reflexivity.
  assert (Hno : bv_unsigned (in_sysno i) = 66%Z) by (cbn [in_sysno i sys_input]; rewrite H17; reflexivity).
  pose proof (gather_of_bufs mem iovs bss Hbufs) as Hg.
  pose proof (gather_iovecs_length _ _ _ Hg) as Hlen.
  assert (Hcnt32 : iovcnt32 (Z_to_bv 64 (Z.of_nat (length iovs))) = Z_to_bv 64 (Z.of_nat (length iovs))).
  { unfold iovcnt32, abi_low32. rewrite SysNodesCfg.u64_lit by lia. rewrite Z.mod_small by lia. reflexivity. }
  assert (Hcap : cap_iovecs iovs = iovs).
  { unfold cap_iovecs. apply cap_iovecs_id. unfold MAX_RW_COUNT. lia. }
  assert (Hlw : bv_unsigned (len_word (concat bss)) = iovs_total iovs).
  { unfold len_word. rewrite Hlen. apply SysNodesCfg.u64_lit. lia. }
  intros Hs. rewrite (SysNodesCfg.syscall_spec_66 i model _ Hno) in Hs. rewrite A0, A1, A2, H12 in Hs.
  unfold writev_spec in Hs. rewrite SysNodesCfg.bind_input, bind_get_model in Hs. rewrite Hfd, Hch in Hs.
  rewrite M0, Hcnt32 in Hs. apply SysNodesCfg.record_copyins_unmodeled_iff in Hs.
  rewrite (import_iovecs_of_array mem iovs (getr regs 11) Hcnt Hiok Harr Hbok) in Hs.
  unfold writev_gathered in Hs. rewrite Hcap, (gather_prefix_full _ _ _ Hg) in Hs.
  cbv beta iota zeta in Hs.
  replace ((iovs_total iovs =? 0)%Z) with false in Hs by (symmetry; apply Z.eqb_neq; lia).
  rewrite Hrd in Hs. cbn [negb] in Hs.
  replace ((length (concat bss) =? 0)%nat) with false in Hs by (symmetry; apply Nat.eqb_neq; lia).
  replace (addr_is_error_b (len_word (concat bss))) with false in Hs
    by (symmetry; unfold addr_is_error_b, two_pow_64; apply Z.ltb_ge; rewrite Hlw; lia).
  unfold bind, choose, emit, pure in Hs. sys_destruct.
  match goal with H : record_copyins _ _ _ _ _ |- _ => apply SysNodesCfg.record_copyins_unmodeled_iff in H end.
  unfold ret_only, pure in *. discriminate.
Qed.
#[using="Type"] Lemma rzb_writev_ch : forall regs pc mem model (ch : word) iovs bss (T : nat -> TSet),
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 66 ->
  fd_lookup (m_fds model) (fd32 (getr regs 10)) = Some (FdChannel ch) ->
  w_is0 ch = false ->
  getr regs 12 = Z_to_bv 64 (Z.of_nat (length iovs)) ->
  (1 <= length iovs <= 1024)%nat ->
  (bv_unsigned (getr regs 11) + 16 * Z.of_nat (length iovs) <= TASK_SIZE)%Z ->
  (SysNodesCfg.iov_array segs) mem (getr regs 11) iovs -> SysNodesCfg.iov_bufs_ok iovs -> (SysNodesCfg.iov_bufs segs) mem iovs bss ->
  (1 <= iovs_total iovs)%Z -> (iovs_total iovs <= 2 ^ 30)%Z ->
  m_channel_reader model = true ->
  (forall k, (1 <= k)%nat -> (k <= length (concat bss))%nat ->
     Rzb.rzb segs cfg (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat k))) (v_addi pc 4) mem (seg_rom segs)) model) (T k)) ->
  Rzb.rzb segs cfg (mkCfg (PEND regs pc mem) model)
    (t_alt (fun i : wr_index (concat bss) =>
       t_emit (map (WriteEv ch) (firstn (proj1_sig i) (concat bss))) (T (proj1_sig i)))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs pc mem model ch iovs bss T Hh Hlz H17 Hfd Hch H12 Hcnt Hiok Harr Hbok Hbufs Ht1 Ht30 Hrd HK.
  set (bs := concat bss) in *.
  set (CA := import_iovecs_accesses (SysNodesCfg.mrb segs mem) (getr regs 11) (Z_to_bv 64 (Z.of_nat (length iovs)))).
  pose proof (gather_of_bufs mem iovs bss Hbufs) as Hg.
  pose proof (gather_iovecs_length _ _ _ Hg) as Hlen. fold bs in Hlen.
  assert (Hnb : (1 <= length bs)%nat) by lia.
  assert (Hno : bv_unsigned (in_sysno (sys_input segs (PEND regs pc mem) (getr regs 17))) = 66%Z)
    by (cbn [in_sysno sys_input]; rewrite H17; reflexivity).
  apply (Rzb.rzb_sys segs cfg (PEND regs pc mem) model (getr regs 17) (wr_index bs)
           (fun j => SysNodesCfg.ret_ci (Z_to_bv 64 (Z.of_nat (proj1_sig j))) (CA ++ (iov_prefix_accesses iovs (proj1_sig j) ++ [])))
           (fun _ => model)
           (fun j => map (WriteEv ch) (firstn (proj1_sig j) bs))
           (fun j => T (proj1_sig j)) (wr_full bs Hnb));
    [exact Hh | reflexivity | exact (Rzb.not_alloc_no _ 66 Hno eq_refl) | | | | | |
    | exact (SysNodesCfg.rob_pend_writev segs regs pc mem model iovs bss H17 H12 Hcnt Hiok Harr Hbok Hbufs Ht30) | ].
  - intros [k Hk]. cbn [proj1_sig].
    apply (writev_ch_ok_iff regs pc mem model ch iovs bss _ _ _ H17 Hfd Hch H12 Hcnt Hiok Harr Hbok Hbufs Ht1 Ht30 Hrd).
    exists k. auto.
  - intros eff m' evs Hs.
    apply (writev_ch_ok_iff regs pc mem model ch iovs bss _ _ _ H17 Hfd Hch H12 Hcnt Hiok Harr Hbok Hbufs Ht1 Ht30 Hrd)
      in Hs as (k & Hk & -> & -> & ->).
    exists (exist _ k Hk). auto.
  - exact (writev_ch_no_unmodeled regs pc mem model ch iovs bss H17 Hfd Hch H12 Hcnt Hiok Harr Hbok Hbufs Ht1 Ht30 Hrd).
  - intros eff. apply SysNodesCfg.not_spurious_uninjected. rewrite Hno. reflexivity.
  - intros _. exact Hh.
  - intros _. exact Hlz.
  - intros [k [Hk1 Hk2]]. cbn [proj1_sig]. unfold SysNodesCfg.ret_ci. rewrite SysNodesCfg.adv_epend_ret. apply HK; assumption.
Qed.
#[using="Type"] Lemma rzb_writev_ch_wall : forall regs pc mem model (ch : word) iovs bss (K : TSet),
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 66 ->
  fd_lookup (m_fds model) (fd32 (getr regs 10)) = Some (FdChannel ch) ->
  w_is0 ch = false ->
  getr regs 12 = Z_to_bv 64 (Z.of_nat (length iovs)) ->
  (1 <= length iovs <= 1024)%nat ->
  (bv_unsigned (getr regs 11) + 16 * Z.of_nat (length iovs) <= TASK_SIZE)%Z ->
  (SysNodesCfg.iov_array segs) mem (getr regs 11) iovs -> SysNodesCfg.iov_bufs_ok iovs -> (SysNodesCfg.iov_bufs segs) mem iovs bss ->
  (1 <= iovs_total iovs)%Z -> (iovs_total iovs <= 2 ^ 30)%Z ->
  m_channel_reader model = true ->
  K [] ->
  (forall k, (1 <= k)%nat -> (k <= length (concat bss))%nat ->
     Rzb.rzb segs cfg (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat k))) (v_addi pc 4) mem (seg_rom segs)) model)
       (t_emit (map (WriteEv ch) (skipn k (concat bss))) K)) ->
  Rzb.rzb segs cfg (mkCfg (PEND regs pc mem) model) (t_emit (map (WriteEv ch) (concat bss)) K).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs pc mem model ch iovs bss K Hh Hlz H17 Hfd Hch H12 Hcnt Hiok Harr Hbok Hbufs Ht1 Ht30 Hrd HK0 HK.
  pose proof (gather_of_bufs mem iovs bss Hbufs) as Hg.
  pose proof (gather_iovecs_length _ _ _ Hg) as Hlen.
  eapply Rzb.rzb_conseq.
  - apply (rzb_writev_ch regs pc mem model ch iovs bss (fun k => t_emit (map (WriteEv ch) (skipn k (concat bss))) K));
      assumption.
  - apply t_alt_wall; [exact HK0 | lia].
Qed.
End Writev.
