(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon Require Import
  PropExec SimInv ExitSim CatSim CatExec SeqExec StreamExec FileSim ShapeAlg ShapeAlgCfg Nodes AgentLib AgentNodes
  Hoare StoreOk LibWritev NodesCfg LibWritevCfg.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Ax Require Import AsanWLazy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Section WithSegs.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.

Fixpoint iov_nl (model : Model) (iovs : list (word * word)) : Prop :=
  match iovs with
  | [] => True
  | (b, n) :: r => no_lazy model (bv_unsigned b) (bv_unsigned b + bv_unsigned n) /\ iov_nl model r
  end.

Lemma copy_iovecs_accesses_in : forall mp k (a : word) (x : word) (m : nat),
  (bv_unsigned a + 16 * Z.of_nat k <= 2 ^ 64)%Z ->
  In (x, m) (copy_iovecs_accesses mp a k) ->
  m = 16%nat /\ (bv_unsigned a <= bv_unsigned x)%Z /\ (bv_unsigned x + 16 <= bv_unsigned a + 16 * Z.of_nat k)%Z.
Proof.
  induction k as [|k IH]; intros a x m Hnw Hin; cbn [copy_iovecs_accesses] in Hin; [destruct Hin|].
  pose proof (u64_range a).
  destruct Hin as [E|Hin].
  - injection E as <- <-. split; [reflexivity|]. lia.
  - destruct (read_iovec_entry mp a); try destruct Hin.
    destruct k as [|k']; [destruct Hin|].
    assert (Ha16 : bv_unsigned (a + 16) = (bv_unsigned a + 16)%Z).
    { rewrite bv_add_unsigned. change (bv_unsigned (16 : word)) with 16%Z.
      apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64)%Z. lia. }
    destruct (IH (a + 16) x m ltac:(lia) Hin) as (E1 & E2 & E3). lia.
Qed.

Lemma import_accesses_in : forall mp (a : word) (n : Z) (x : word) (m : nat),
  (1 <= n <= 1024)%Z -> (bv_unsigned a + 16 * n <= 2 ^ 64)%Z ->
  In (x, m) (import_iovecs_accesses mp a (Z_to_bv 64 n)) ->
  m = 16%nat /\ (bv_unsigned a <= bv_unsigned x)%Z /\ (bv_unsigned x + 16 <= bv_unsigned a + 16 * n)%Z.
Proof.
  intros mp a n x m Hn Hnw Hin. unfold import_iovecs_accesses in Hin.
  pose proof (u64_range a).
  destruct (bv_eqb (Z_to_bv 64 n) (Z_to_bv 64 1)) eqn:E1.
  - destruct (negb (access_okb a 16)); [destruct Hin|].
    destruct Hin as [E|[]]. injection E as <- <-.
    assert (n = 1)%Z.
    { apply bv_eqb_eq in E1. apply (f_equal bv_unsigned) in E1. rewrite !u64_lit in E1 by lia. exact E1. }
    subst n. split; [reflexivity|]. lia.
  - destruct (bv_eqb (Z_to_bv 64 n) (Z_to_bv 64 0)); [destruct Hin|].
    destruct (IOV_MAX <? bv_unsigned (Z_to_bv 64 n))%Z; [destruct Hin|].
    destruct (negb (access_okb a (16 * bv_unsigned (Z_to_bv 64 n)))); [destruct Hin|].
    rewrite word_to_nat_Z in Hin by lia.
    destruct (copy_iovecs_accesses_in mp (Z.to_nat n) a x m) as (E2 & E3 & E4);
      [rewrite Z2Nat.id by lia; lia | exact Hin |].
    rewrite Z2Nat.id in E4 by lia. split; [exact E2 | split; [exact E3 | exact E4]].
Qed.

Lemma iov_prefix_accesses_in : forall iovs (left : nat) (x : word) (m : nat),
  In (x, m) (iov_prefix_accesses iovs left) ->
  exists n, In (x, n) iovs /\ (Z.of_nat m <= bv_unsigned n)%Z.
Proof.
  induction iovs as [|[b n] r IH]; intros left x m Hin.
  - destruct left; destruct Hin.
  - destruct left as [|left]; [destruct Hin|].
    cbn [iov_prefix_accesses] in Hin.
    destruct (Nat.eqb (word_to_nat_bounded n (S left)) 0) eqn:E.
    + destruct (IH _ _ _ Hin) as (n' & Hn' & Hle). exists n'. split; [right; exact Hn' | exact Hle].
    + destruct Hin as [E2|Hin].
      * injection E2 as <- <-. exists n. split; [left; reflexivity|].
        rewrite word_to_nat_bounded_eq_min. unfold word_to_nat. pose proof (u64_range n). lia.
      * destruct (IH _ _ _ Hin) as (n' & Hn' & Hle). exists n'. split; [right; exact Hn' | exact Hle].
Qed.

Lemma iov_nl_in : forall model iovs (b n : word),
  iov_nl model iovs -> In (b, n) iovs -> no_lazy model (bv_unsigned b) (bv_unsigned b + bv_unsigned n).
Proof.
  induction iovs as [|[b' n'] r IH]; intros b n Hnl Hin; [destruct Hin|].
  destruct Hnl as [H1 H2]. destruct Hin as [E|Hin]; [injection E as <- <-; exact H1 | exact (IH _ _ H2 Hin)].
Qed.

Lemma iov_bufs_ok_in : forall iovs (b n : word),
  iov_bufs_ok iovs -> In (b, n) iovs -> (bv_unsigned b + bv_unsigned n <= TASK_SIZE)%Z.
Proof.
  induction iovs as [|[b' n'] r IH]; intros b n Hok Hin; [destruct Hin|].
  destruct Hok as [H1 H2]. destruct Hin as [E|Hin]; [injection E as <- <-; exact H1 | exact (IH _ _ H2 Hin)].
Qed.

Lemma acc_ok_writev : forall model mp (iov : word) iovs (k : nat),
  (1 <= length iovs <= 1024)%nat ->
  (bv_unsigned iov + 16 * Z.of_nat (length iovs) <= TASK_SIZE)%Z ->
  iov_bufs_ok iovs ->
  no_lazy model (bv_unsigned iov) (bv_unsigned iov + 16 * Z.of_nat (length iovs)) ->
  iov_nl model iovs ->
  acc_ok model (import_iovecs_accesses mp iov (Z_to_bv 64 (Z.of_nat (length iovs))) ++ iov_prefix_accesses iovs k).
Proof.
  intros model mp iov iovs k Hcnt Hiok Hbok Hnla Hnlb.
  unfold acc_ok. apply Forall_forall. intros [x m] Hin. cbn [fst snd].
  apply in_app_or in Hin as [Hin|Hin].
  - destruct (import_accesses_in mp iov (Z.of_nat (length iovs)) x m ltac:(lia) ltac:(unfold TASK_SIZE in *; lia) Hin)
      as (-> & H1 & H2).
    change (Z.of_nat 16) with 16%Z. split; [unfold TASK_SIZE in *; lia|].
    eapply no_lazy_sub; [exact Hnla | lia | lia].
  - destruct (iov_prefix_accesses_in iovs k x m Hin) as (n & Hn & Hle).
    pose proof (iov_bufs_ok_in iovs x n Hbok Hn) as Hb.
    split; [unfold TASK_SIZE in *; lia|].
    eapply no_lazy_sub; [exact (iov_nl_in model iovs x n Hnlb Hn) | lia | lia].
Qed.

Lemma rzc_writev_pending_nl : forall ms x8 model (fd : Z) (iov : word) iovs bss (T : nat -> TSet),
  ms_rom ms = seg_rom segs ->
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
  (1 <= iovs_total iovs)%Z -> (iovs_total iovs <= 2 ^ 30)%Z ->
  no_lazy model (bv_unsigned iov) (bv_unsigned iov + 16 * Z.of_nat (length iovs)) ->
  iov_nl model iovs ->
  let bs := concat bss in
  (forall k, (1 <= k)%nat -> (k <= length bs)%nat ->
     realizes_cfg segs cfg (mkCfg (advance_past_svc (set_gpr0 ms (Z_to_bv 64 (Z.of_nat k)))) model) (T k)) ->
  realizes_cfg segs cfg (mkCfg ms model)
    (t_alt (fun i : wr_index bs => t_emit (map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) bs)) (T (proj1_sig i)))).
Proof.
  intros ms x8 model fd iov iovs bss T Hrom Hh Hsvc Hfd Hfdr Hno H0 H1 H2 Hcnt Hiok Harr Hbok Hbufs
         Ht1 Ht30 Hnla Hnlb bs Hk.
  destruct (writev_check_nomax segs ms x8 model fd iov iovs bss Hrom Hfd Hfdr Hno H0 H1 H2 Hcnt Hiok Harr Hbok Hbufs
              Ht1 Ht30)
    as [Hlen Hchk]. fold bs in Hlen, Hchk.
  set (tot := iovs_total iovs) in *.
  set (CA := import_iovecs_accesses (ms_read_byte ms) iov (Z_to_bv 64 (Z.of_nat (length iovs)))) in *.
  assert (Hmat : forall k, materialize_model_accesses model (CA ++ iov_prefix_accesses iovs k) = Some model).
  { intros k. apply materialize_acc_ok. unfold CA. apply acc_ok_writev; assumption. }
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
  apply (rzc_node segs cfg (mkCfg ms model) (wr_index bs)
           (fun i => map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) bs))
           (fun i => mkCfg (advance_past_svc (set_gpr0 ms (Z_to_bv 64 (Z.of_nat (proj1_sig i))))) model)
           (fun i => T (proj1_sig i)) (wr_full bs Hnb)).
  2:{ intros [k [Hk1 Hk2]]. cbn [proj1_sig]. apply Hk; assumption. }
  assert (Hku : forall k, (k <= length bs)%nat -> bv_unsigned (Z_to_bv 64 (Z.of_nat k)) = Z.of_nat k).
  { intros k Hk2. apply u64_lit. lia. }
  apply node_ok_cfg_of_transparent;
    [| apply (transparent_uninjected segs cfg ms model x8 Hsvc); rewrite Hno; reflexivity].
  split.
  - intros i. rewrite Enx.
    apply (sstep_syscall segs ms model x8 (effs i) model model _ Hh Hsvc).
    + apply check_syscall_ok_iff.
      destruct i as [k [Hk1 Hk2]]. unfold effs. cbn [proj1_sig]. rewrite Hchk.
      rewrite (Hku k Hk2), Nat2Z.id.
      rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia.
      replace (addr_is_error_b (Z_to_bv 64 (Z.of_nat k))) with false
        by (symmetry; unfold addr_is_error_b, two_pow_64; apply Z.ltb_ge; rewrite (Hku k Hk2); lia).
      rewrite (proj2 (access_ranges_eqb_eq _ _) eq_refl). reflexivity.
    + exact Hh.
    + unfold effs, syscall_effect_accesses. cbn [eff_copyins eff_writes write_accesses]. rewrite app_nil_r.
      apply Hmat.
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
      unfold effs, syscall_effect_accesses in Hm. cbn [eff_copyins eff_writes write_accesses] in Hm.
      rewrite app_nil_r, Hmat in Hm. injection Hm as <-.
      exists i. rewrite Enx. split; reflexivity.
    + destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->).
      unfold effs, syscall_effect_accesses in Hm. cbn [eff_copyins eff_writes write_accesses] in Hm.
      rewrite app_nil_r, Hmat in Hm. discriminate.
    + destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->). congruence.
    + exfalso. rewrite Hchk in Hc. destruct eff as [ret ws zs us cs ci].
      destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate].
      destruct cs; [|discriminate]. destruct (_ && _)%bool; [destruct (access_ranges_eqb _ _)|]; discriminate.
Qed.

Lemma rzc_writev_wall_nl : forall ms x8 model (fd : Z) (iov : word) iovs bss (K : TSet),
  ms_rom ms = seg_rom segs ->
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
  (1 <= iovs_total iovs)%Z -> (iovs_total iovs <= 2 ^ 30)%Z ->
  no_lazy model (bv_unsigned iov) (bv_unsigned iov + 16 * Z.of_nat (length iovs)) ->
  iov_nl model iovs ->
  K [] ->
  (forall k, (1 <= k)%nat -> (k <= length (concat bss))%nat ->
     realizes_cfg segs cfg (mkCfg (advance_past_svc (set_gpr0 ms (Z_to_bv 64 (Z.of_nat k)))) model)
       (t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k (concat bss))) K)) ->
  realizes_cfg segs cfg (mkCfg ms model) (t_emit (map (WriteEv (Z_to_bv 64 fd)) (concat bss)) K).
Proof.
  intros ms x8 model fd iov iovs bss K Hrom Hh Hsvc Hfd Hfdr Hno H0 H1 H2 Hcnt Hiok Harr Hbok Hbufs
         Ht1 Ht30 Hnla Hnlb HK Hk.
  pose proof (gather_of_bufs segs ms iovs bss Hrom Hbufs) as Hg.
  pose proof (gather_iovecs_length _ _ _ Hg) as Hlen.
  apply rzc_wall; [lia | exact HK |].
  exact (rzc_writev_pending_nl ms x8 model fd iov iovs bss
           (fun k => t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k (concat bss))) K)
           Hrom Hh Hsvc Hfd Hfdr Hno H0 H1 H2 Hcnt Hiok Harr Hbok Hbufs Ht1 Ht30 Hnla Hnlb Hk).
Qed.

End WithSegs.
