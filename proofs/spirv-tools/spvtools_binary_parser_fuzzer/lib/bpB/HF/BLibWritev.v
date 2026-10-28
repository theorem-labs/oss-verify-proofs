(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import Bcfg BRelSpec BSimInv BExitSim BCatSim BCatExec BPropExec BSeqExec BHoare BShapeAlg BNodes BFileSim BAgentLib BAgentNodes.
Import ListNotations.
Open Scope bv_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Lemma bv_add_Zform : forall (a b : word), a + b = Z_to_bv 64 (bv_unsigned a + bv_unsigned b).
Proof.
  intros a b. apply bv_eq. rewrite bv_add_unsigned, Z_to_bv_unsigned. reflexivity.
Qed.

Lemma word_to_nat_Z : forall z, (0 <= z < 2^64)%Z -> word_to_nat (Z_to_bv 64 z) = Z.to_nat z.
Proof.
  intros z Hz. unfold word_to_nat. rewrite Z_to_bv_unsigned.
  rewrite (bv_wrap_small 64 z) by (change (bv_modulus 64) with (2^64)%Z; lia). reflexivity.
Qed.

Lemma u64_roundtrip' : forall (x : word), Z_to_bv 64 (bv_unsigned x) = x.
Proof. intros x. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

Lemma rz_wall {SC : StepCfg} : forall segs c (ch : word) (bs : list byte) (K : TSet),
  (1 <= length bs)%nat -> K [] ->
  realizes segs c (t_alt (fun i : wr_index bs =>
     t_emit (map (WriteEv ch) (firstn (proj1_sig i) bs))
            (t_emit (map (WriteEv ch) (skipn (proj1_sig i) bs)) K))) ->
  realizes segs c (t_emit (map (WriteEv ch) bs) K).
Proof.
  intros segs c ch bs K Hnb HK H. eapply rz_conseq; [exact H | apply t_alt_wall; assumption].
Qed.

Section WithSegs.
Context {fx : DFP}.
Variable segs : list Segment.
Context {SC : StepCfg}.

Lemma read_u64_rdn : forall ms a v,
  ms_rom ms = seg_rom segs ->
  rdn segs (ms_mem ms) a 8%nat = Some (word_to_le_bytes 8 v) ->
  read_u64 (ms_read_byte ms) a = Some v.
Proof.
  intros ms a v Hrom H. unfold read_u64.
  rewrite read_bytes_map_read_byte, (ms_read_bytes_rdn segs) by exact Hrom.
  change (word_to_nat (Z_to_bv 64 8)) with 8%nat. rewrite H.
  f_equal. apply le_word_v. apply bytes_le_to_Z_8.
Qed.

Lemma read_bytes_map_rdn : forall ms a (n : word) bs,
  ms_rom ms = seg_rom segs ->
  rdn segs (ms_mem ms) a (word_to_nat n) = Some bs ->
  read_bytes_map (ms_read_byte ms) a n = Some bs.
Proof.
  intros ms a n bs Hrom H.
  rewrite read_bytes_map_read_byte, (ms_read_bytes_rdn segs) by exact Hrom. exact H.
Qed.

Fixpoint iov_array (mem : word -> option byte) (iov : word) (iovs : list (word * word)) : Prop :=
  match iovs with
  | [] => True
  | (b, n) :: r =>
      rdn segs mem iov 8%nat = Some (word_to_le_bytes 8 b)
      /\ rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 8)) 8%nat = Some (word_to_le_bytes 8 n)
      /\ (bv_unsigned n < 2 ^ 63)%Z
      /\ iov_array mem (Z_to_bv 64 (bv_unsigned iov + 16)) r
  end.

Lemma copy_iovecs_of_array : forall ms iovs iov,
  ms_rom ms = seg_rom segs ->
  iov_array (ms_mem ms) iov iovs ->
  copy_iovecs_aux (ms_read_byte ms) iov (length iovs) = ImpOk iovs.
Proof.
  intros ms iovs; induction iovs as [|[b n] r IH]; intros iov Hrom Ha; [reflexivity|].
  destruct Ha as (Hb & Hn & Hlt & Hr).
  cbn [length copy_iovecs_aux]. unfold read_iovec_entry.
  rewrite (read_u64_rdn ms iov b Hrom Hb).
  rewrite bv_add_Zform. change (bv_unsigned (8 : word)) with 8%Z.
  rewrite (read_u64_rdn ms _ n Hrom Hn).
  rewrite (proj2 (Z.leb_gt _ _) Hlt).
  rewrite bv_add_Zform. change (bv_unsigned (16 : word)) with 16%Z.
  rewrite (IH _ Hrom Hr). reflexivity.
Qed.

Fixpoint iov_bufs (mem : word -> option byte) (iovs : list (word * word)) (bss : list (list byte)) : Prop :=
  match iovs, bss with
  | [], [] => True
  | (b, n) :: r, bs :: bss' => rdn segs mem b (word_to_nat n) = Some bs /\ iov_bufs mem r bss'
  | _, _ => False
  end.

Lemma gather_of_bufs : forall ms iovs bss,
  ms_rom ms = seg_rom segs ->
  iov_bufs (ms_mem ms) iovs bss ->
  gather_iovecs (ms_read_byte ms) iovs = Some (concat bss).
Proof.
  intros ms iovs; induction iovs as [|[b n] r IH]; intros [|bs bss] Hrom Hb; cbn in Hb; try contradiction.
  - reflexivity.
  - destruct Hb as [H1 H2]. cbn [gather_iovecs concat].
    rewrite (read_bytes_map_rdn ms b n bs Hrom H1), (IH bss Hrom H2). reflexivity.
Qed.

Fixpoint iov_ranges_ok (iovs : list (word * word)) : Prop :=
  match iovs with
  | [] => True
  | (b, n) :: r => (bv_unsigned b + bv_unsigned n <= TASK_SIZE)%Z /\ iov_ranges_ok r
  end.

Lemma iovs_access_okb_of_ranges : forall iovs,
  iov_ranges_ok iovs -> iovs_access_okb iovs = true.
Proof.
  induction iovs as [|[b n] r IH]; intros H; [reflexivity|].
  destruct H as [Hb Hr]. unfold iovs_access_okb. cbn [forallb fst snd].
  fold (iovs_access_okb r). rewrite (access_okb_intro b n Hb), (IH Hr). reflexivity.
Qed.

Lemma import_iovecs_of_array : forall ms iovs iov,
  ms_rom ms = seg_rom segs ->
  iov_array (ms_mem ms) iov iovs ->
  (2 <= length iovs <= 1024)%nat ->
  (bv_unsigned iov + 16 * Z.of_nat (length iovs) <= TASK_SIZE)%Z ->
  iov_ranges_ok iovs ->
  import_iovecs (ms_read_byte ms) iov (Z_to_bv 64 (Z.of_nat (length iovs))) = ImpOk iovs
  /\ import_iovecs_accesses (ms_read_byte ms) iov (Z_to_bv 64 (Z.of_nat (length iovs)))
     = copy_iovecs_accesses (ms_read_byte ms) iov (length iovs).
Proof.
  intros ms iovs iov Hrom Harr Hlen Hiov Hrng.
  pose proof (u64_range iov) as Hi.
  assert (Hwn : word_to_nat (Z_to_bv 64 (Z.of_nat (length iovs))) = length iovs).
  { rewrite word_to_nat_Z, Nat2Z.id by lia. reflexivity. }
  assert (E1 : bv_eqb (Z_to_bv 64 (Z.of_nat (length iovs))) (Z_to_bv 64 1) = false).
  { apply bv_eqb_neq. intros E. apply (f_equal bv_unsigned) in E. rewrite !u64_lit in E by lia. lia. }
  assert (E0 : bv_eqb (Z_to_bv 64 (Z.of_nat (length iovs))) (Z_to_bv 64 0) = false).
  { apply bv_eqb_neq. intros E. apply (f_equal bv_unsigned) in E. rewrite !u64_lit in E by lia. lia. }
  assert (Emax : (IOV_MAX <? bv_unsigned (Z_to_bv 64 (Z.of_nat (length iovs))))%Z = false).
  { apply Z.ltb_ge. unfold IOV_MAX. rewrite u64_lit; lia. }
  assert (Eacc : access_okb iov (16 * bv_unsigned (Z_to_bv 64 (Z.of_nat (length iovs)))) = true).
  { unfold access_okb. rewrite u64_lit by lia. apply andb_true_iff. unfold TASK_SIZE in *. split; apply Z.leb_le; lia. }
  unfold import_iovecs, import_iovecs_accesses. rewrite E1, E0, Emax, Eacc. cbn [negb].
  rewrite Hwn, (copy_iovecs_of_array ms iovs iov Hrom Harr), (iovs_access_okb_of_ranges iovs Hrng).
  split; reflexivity.
Qed.

Lemma import_iovecs_of_array1 : forall ms (b1 n1 : word) iov,
  ms_rom ms = seg_rom segs ->
  iov_array (ms_mem ms) iov [(b1, n1)] ->
  (bv_unsigned iov + 16 <= TASK_SIZE)%Z ->
  (bv_unsigned b1 + bv_unsigned n1 <= TASK_SIZE)%Z ->
  import_iovecs (ms_read_byte ms) iov (Z_to_bv 64 1) = ImpOk [(b1, n1)]
  /\ import_iovecs_accesses (ms_read_byte ms) iov (Z_to_bv 64 1) = [(iov, 16%nat)].
Proof.
  intros ms b1 n1 iov Hrom (Hb & Hn & Hlt & _) Hiov Hrng.
  pose proof (u64_range iov) as Hi. pose proof (u64_range b1). pose proof (u64_range n1).
  assert (Eacc : access_okb iov 16 = true).
  { unfold access_okb. apply andb_true_iff. unfold TASK_SIZE in *. split; apply Z.leb_le; lia. }
  assert (Eacc2 : access_okb b1 (Z.min (bv_unsigned n1) MAX_RW_COUNT) = true).
  { unfold access_okb. apply andb_true_iff. unfold TASK_SIZE, MAX_RW_COUNT in *. split; apply Z.leb_le; lia. }
  unfold import_iovecs, import_iovecs_accesses. rewrite bv_eqb_refl, Eacc. cbn [negb].
  unfold read_iovec_entry.
  rewrite (read_u64_rdn ms iov b1 Hrom Hb).
  rewrite bv_add_Zform. change (bv_unsigned (8 : word)) with 8%Z.
  rewrite (read_u64_rdn ms _ n1 Hrom Hn).
  rewrite (proj2 (Z.leb_gt _ _) Hlt), Eacc2. split; reflexivity.
Qed.

Lemma cap_iovecs_id_30 : forall iovs,
  (iovs_total iovs <= 2 ^ 30)%Z -> cap_iovecs iovs = iovs.
Proof.
  intros iovs H. unfold cap_iovecs. apply cap_iovecs_aux_id.
  unfold MAX_RW_COUNT. lia.
Qed.

Lemma writev_chan_outcome30 : forall fd iov iovcnt i m o ch iovs bs,
  fd_lookup (m_fds m) fd = Some (FdChannel ch) ->
  w_is0 ch = false ->
  import_iovecs (in_mem i) iov (iovcnt32 iovcnt) = ImpOk iovs ->
  (iovs_total iovs <= 2 ^ 30)%Z ->
  gather_iovecs (in_mem i) iovs = Some bs ->
  (1 <= Z.of_nat (length bs))%Z ->
  let CA := import_iovecs_accesses (in_mem i) iov (iovcnt32 iovcnt) in
  writev_spec fd iov iovcnt i m o <->
  exists k, (1 <= k <= length bs)%nat /\
    o = Ok (mkEffectU (Z_to_bv 64 (Z.of_nat k)) [] [] [] [] (CA ++ iov_prefix_accesses iovs k))
           m (map (WriteEv ch) (firstn k bs)).
Proof.
  intros fd iov iovcnt i m o ch iovs bs Hfd Hch Himp Htot Hg Hbs1.
  cbv zeta.
  pose proof (gather_iovecs_length _ _ _ Hg) as Hlen.
  pose proof (cap_iovecs_id_30 iovs Htot) as Hcap.
  assert (Herrk : forall k, (k <= length bs)%nat ->
            addr_is_error_b (len_word (firstn k bs)) = false).
  { intros k Hk. unfold addr_is_error_b, two_pow_64. apply Z.ltb_ge.
    rewrite len_word_unsigned by (rewrite firstn_length_le by lia; unfold two_pow_64; lia).
    rewrite firstn_length_le by lia. lia. }
  unfold writev_spec. rewrite bind_input_get_model. rewrite Hfd, Hch. cbv iota.
  transitivity
    (record_copyins (import_iovecs_accesses (in_mem i) iov (iovcnt32 iovcnt))
       (ds <- choose (fun ds : list byte =>
                       (1 <= Z.of_nat (length ds))%Z
                       /\ (Z.of_nat (length ds) < two_pow_64)%Z
                       /\ addr_is_error_b (len_word ds) = false
                       /\ ds = firstn (length ds) bs) ;;
        emit (map (WriteEv ch) ds) ;;
        record_copyins (iov_prefix_accesses (cap_iovecs iovs) (length ds))
          (ret_only (len_word ds)))%sys i m o).
  { rewrite Himp. cbv zeta. unfold writev_gathered.
    rewrite Hcap, (gather_prefix_full _ _ _ Hg).
    replace (iovs_total iovs =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia).
    replace (length bs =? 0)%nat with false by (symmetry; apply Nat.eqb_neq; lia).
    replace (addr_is_error_b (len_word bs)) with false
      by (symmetry; rewrite <- (firstn_all bs); rewrite (Herrk (length bs)) by lia; reflexivity).
    reflexivity. }
  rewrite Hcap. sys_unfold.
  split.
  - destruct o as [x m' evs|]; intros H; inv_sys.
    match goal with Hds : ?ds = firstn (length ?ds) bs |- _ =>
      exists (length ds); rewrite <- Hds;
      assert (Hk : (length ds <= length bs)%nat)
        by (rewrite Hds; rewrite length_firstn; apply Nat.le_min_r)
    end.
    split; [lia|]. rewrite !app_nil_r. unfold len_word. reflexivity.
  - intros (k & Hk & ->).
    assert (Hlk : length (firstn k bs) = k) by (apply firstn_length_le; lia).
    eexists _, _, _, _. split.
    + eexists _, _, _, _. split.
      * exists (firstn k bs). split; [|reflexivity].
        rewrite Hlk. split; [lia|]. split; [unfold two_pow_64 in *; lia|].
        split; [apply Herrk; lia|reflexivity].
      * split; [|reflexivity]. eexists _, _, _, _. split; [reflexivity|]. split; [|reflexivity].
        eexists _, _, _, _. split; [reflexivity|]. split; reflexivity.
    + rewrite Hlk, !app_nil_r. unfold len_word. rewrite Hlk. split; reflexivity.
Qed.

Lemma writev_outcome : forall ms x8 model (fd : Z) (iov : word) iovs bss,
  ms_rom ms = seg_rom segs ->
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  (0 < fd < 2^31)%Z ->
  bv_unsigned x8 = 66%Z ->
  ms_gpr ms 0 = Z_to_bv 64 fd ->
  ms_gpr ms 1 = iov ->
  ms_gpr ms 2 = Z_to_bv 64 (Z.of_nat (length iovs)) ->
  (1 <= length iovs <= 1024)%nat ->
  iov_array (ms_mem ms) iov iovs ->
  iov_bufs (ms_mem ms) iovs bss ->
  (bv_unsigned iov + 16 * Z.of_nat (length iovs) <= TASK_SIZE)%Z ->
  iov_ranges_ok iovs ->
  let bs := concat bss in
  let tot := iovs_total iovs in
  (1 <= tot)%Z -> (tot <= 2 ^ 30)%Z ->
  let CA := import_iovecs_accesses (ms_read_byte ms) iov (Z_to_bv 64 (Z.of_nat (length iovs))) in
  Z.of_nat (length bs) = tot /\
  forall o, syscall_spec (sys_input segs ms x8) model o <->
    exists k, (1 <= k <= length bs)%nat /\
      o = Ok (mkEffectU (Z_to_bv 64 (Z.of_nat k)) [] [] [] [] (CA ++ iov_prefix_accesses iovs k))
             model (map (WriteEv (Z_to_bv 64 fd)) (firstn k bs)).
Proof.
  intros ms x8 model fd iov iovs bss Hrom Hfd Hfdr Hno H0 H1 H2 Hcnt Harr Hbufs Hiov Hrng bs tot Ht1 Ht30 CA.
  pose proof (gather_of_bufs ms iovs bss Hrom Hbufs) as Hg. fold bs in Hg.
  pose proof (gather_iovecs_length _ _ _ Hg) as Hlen. fold tot in Hlen.
  split; [exact Hlen|].
  assert (Himp : import_iovecs (ms_read_byte ms) iov (Z_to_bv 64 (Z.of_nat (length iovs))) = ImpOk iovs).
  { destruct iovs as [|[b1 n1] [|p r]]; [cbn in Hcnt; lia | |].
    - cbn [length Z.of_nat Pos.of_succ_nat]. destruct Hrng as [Hr1 _].
      exact (proj1 (import_iovecs_of_array1 ms b1 n1 iov Hrom Harr ltac:(cbn [length] in Hiov; lia) Hr1)).
    - apply (proj1 (import_iovecs_of_array ms _ iov Hrom Harr ltac:(cbn [length] in *; lia) Hiov Hrng)). }
  intros o.
  rewrite (syscall_spec_66 (sys_input segs ms x8) model o) by (rewrite in_sysno_si; exact Hno).
  rewrite in_arg0_si, in_arg1_si, in_arg2_si, H0, H1, H2.
  rewrite fd32_id by (rewrite u64_lit; lia).
  assert (Hcnt32 : iovcnt32 (Z_to_bv 64 (Z.of_nat (length iovs))) = Z_to_bv 64 (Z.of_nat (length iovs))).
  { unfold iovcnt32, abi_low32. rewrite u64_lit by lia. rewrite Z.mod_small by lia. reflexivity. }
  subst CA. change (ms_read_byte ms) with (in_mem (sys_input segs ms x8)).
  replace (import_iovecs_accesses (in_mem (sys_input segs ms x8)) iov (Z_to_bv 64 (Z.of_nat (length iovs))))
    with (import_iovecs_accesses (in_mem (sys_input segs ms x8)) iov (iovcnt32 (Z_to_bv 64 (Z.of_nat (length iovs)))))
    by (rewrite Hcnt32; reflexivity).
  apply (writev_chan_outcome30 _ _ _ _ model o (Z_to_bv 64 fd) iovs bs Hfd).
  - apply w_is0_pos. rewrite u64_lit; lia.
  - rewrite Hcnt32, in_mem_si. exact Himp.
  - exact Ht30.
  - rewrite in_mem_si. exact Hg.
  - lia.
Qed.

End WithSegs.
