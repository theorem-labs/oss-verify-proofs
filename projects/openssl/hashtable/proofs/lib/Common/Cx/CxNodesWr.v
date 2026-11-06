(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Prelude.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SpinAlg AgentLib AgentNodes Nodes FileSim StreamSim WallSim
  AsanAcct LazyFrame NoReserve Hoare LibWritev CxNodesBase CxNodesFs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import CxRel CxAcctShape CxNodesLibE.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma access_outside_range_sub : forall (a a' : word) (n n' : nat) (lo sz : word),
  (bv_unsigned a <= bv_unsigned a')%Z ->
  (bv_unsigned a' + Z.of_nat n' <= bv_unsigned a + Z.of_nat n)%Z ->
  access_outside_range a n lo sz -> access_outside_range a' n' lo sz.
Proof.
  intros a a' n n' lo sz H1 H2 [Hnw Hd]. split; [lia|]. destruct Hd as [Hd|Hd]; [left|right]; lia.
Qed.

(* [comment removed for export] *)
Lemma copy_iovecs_accesses_sub : forall mp k (a : word),
  (bv_unsigned a + 16 * Z.of_nat k < 2 ^ 64)%Z ->
  forall x, In x (copy_iovecs_accesses mp a k) ->
  (bv_unsigned a <= bv_unsigned (fst x))%Z /\ (bv_unsigned (fst x) + Z.of_nat (snd x) <= bv_unsigned a + 16 * Z.of_nat k)%Z.
Proof.
  intros mp k. induction k as [|k IH]; intros a Hnw x Hin; cbn [copy_iovecs_accesses] in Hin.
  - destruct Hin.
  - destruct Hin as [<- | Hin].
    + cbn [fst snd]. lia.
    + destruct (read_iovec_entry mp a) as [eb el| |]; [ | destruct Hin | destruct Hin].
      assert (Ha16 : bv_unsigned (a + Z_to_bv 64 16)%bv = (bv_unsigned a + 16)%Z).
      { rewrite bv_add_Zform. pose proof (u64_range a).
        replace (bv_unsigned (Z_to_bv 64 16)) with 16%Z by reflexivity. apply u64_lit. lia. }
      destruct (IH (a + Z_to_bv 64 16)%bv ltac:(rewrite Ha16; lia) x Hin) as [H1 H2]. rewrite Ha16 in H1, H2. lia.
Qed.

Lemma import_iovecs_accesses_sub : forall mp (a n : word),
  (bv_unsigned a + 16 * bv_unsigned n < 2 ^ 64)%Z ->
  forall x, In x (import_iovecs_accesses mp a n) ->
  (bv_unsigned a <= bv_unsigned (fst x))%Z /\ (bv_unsigned (fst x) + Z.of_nat (snd x) <= bv_unsigned a + 16 * bv_unsigned n)%Z.
Proof.
  intros mp a n Hnw x Hin. pose proof (u64_range n) as Hn. unfold import_iovecs_accesses in Hin.
  destruct (bv_eqb n (Z_to_bv 64 1)) eqn:E1.
  - apply bv_eqb_eq in E1. subst n.
    destruct (negb (access_okb a 16)); [destruct Hin|]. destruct Hin as [<-|[]]. cbn [fst snd].
    rewrite u64_lit by lia. lia.
  - destruct (bv_eqb n (Z_to_bv 64 0)); [destruct Hin|].
    destruct (IOV_MAX <? bv_unsigned n)%Z; [destruct Hin|].
    destruct (negb (access_okb a (16 * bv_unsigned n))); [destruct Hin|].
    destruct (copy_iovecs_accesses_sub mp (word_to_nat n) a ltac:(unfold word_to_nat; rewrite Z2Nat.id by lia; lia) x Hin) as [H1 H2].
    unfold word_to_nat in H2. rewrite Z2Nat.id in H2 by lia. lia.
Qed.

Lemma copy_iovecs_accesses_outside : forall mp k (a : word) lo sz,
  (bv_unsigned a + 16 * Z.of_nat k < 2 ^ 64)%Z ->
  access_outside_range a (16 * k) lo sz ->
  forall x, In x (copy_iovecs_accesses mp a k) -> access_outside_range (fst x) (snd x) lo sz.
Proof.
  intros mp k a lo sz Hnw Hout x Hin.
  destruct (copy_iovecs_accesses_sub mp k a Hnw x Hin) as [H1 H2].
  eapply access_outside_range_sub; [exact H1 | | exact Hout]. lia.
Qed.

Lemma import_iovecs_accesses_outside : forall mp (a n : word) lo sz,
  (bv_unsigned a + 16 * bv_unsigned n < 2 ^ 64)%Z ->
  access_outside_range a (16 * word_to_nat n) lo sz ->
  forall x, In x (import_iovecs_accesses mp a n) -> access_outside_range (fst x) (snd x) lo sz.
Proof.
  intros mp a n lo sz Hnw Hout x Hin. pose proof (u64_range n).
  destruct (import_iovecs_accesses_sub mp a n Hnw x Hin) as [H1 H2].
  eapply access_outside_range_sub; [exact H1 | | exact Hout]. unfold word_to_nat. rewrite Nat2Z.inj_mul, Z2Nat.id by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma iov_prefix_accesses_sub : forall iovs left x,
  In x (iov_prefix_accesses iovs left) ->
  exists b n, In (b, n) iovs /\ fst x = b /\ (snd x <= word_to_nat n)%nat.
Proof.
  induction iovs as [|[b n] rest IH]; intros left x Hin.
  - destruct left; cbn in Hin; destruct Hin.
  - destruct left as [|l]; [cbn in Hin; destruct Hin|].
    cbn [iov_prefix_accesses] in Hin.
    set (m := word_to_nat_bounded n (S l)) in Hin.
    assert (Hm : (m <= word_to_nat n)%nat) by (unfold m; rewrite word_to_nat_bounded_eq_min; lia).
    destruct (Nat.eqb m 0).
    + destruct (IH _ _ Hin) as (b' & n' & Hin' & -> & Hle). exists b', n'. split; [right; exact Hin'|]. split; [reflexivity|exact Hle].
    + destruct Hin as [<- | Hin].
      * exists b, n. cbn [fst snd]. split; [left; reflexivity|]. split; [reflexivity|exact Hm].
      * destruct (IH _ _ Hin) as (b' & n' & Hin' & -> & Hle). exists b', n'. split; [right; exact Hin'|]. split; [reflexivity|exact Hle].
Qed.

Lemma iov_prefix_accesses_outside : forall iovs left lazy,
  (forall b n, In (b, n) iovs -> accesses_outside_lazy [(b, word_to_nat n)] lazy) ->
  forall a k lo sz, In (a, k) (iov_prefix_accesses iovs left) -> In (lo, sz) lazy -> access_outside_range a k lo sz.
Proof.
  intros iovs left lazy Hb a k lo sz Hin Hl.
  destruct (iov_prefix_accesses_sub iovs left (a, k) Hin) as (b & n & Hbn & Ea & Hle). cbn [fst snd] in Ea, Hle. subst a.
  eapply access_outside_range_mono; [exact Hle|]. apply (Hb b n Hbn b (word_to_nat n) lo sz); [left; reflexivity | exact Hl].
Qed.

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
Lemma crz_wall : forall c (ch : word) (bs : list byte) (K : TSet),
  (1 <= length bs)%nat -> K [] ->
  crz segs c (t_alt (fun i : wr_index bs =>
     t_emit (map (WriteEv ch) (firstn (proj1_sig i) bs))
            (t_emit (map (WriteEv ch) (skipn (proj1_sig i) bs)) K))) ->
  crz segs c (t_emit (map (WriteEv ch) bs) K).
Proof.
  intros c ch bs K Hnb HK H. eapply crz_conseq; [exact H | apply t_alt_wall; assumption].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma srz_writev_pending_mi : forall ms x8 model (fd : Z) (iov : word) iovs bss (T : nat -> TSet),
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
  let bs := concat bss in
  (1 <= iovs_total iovs)%Z -> (iovs_total iovs <= 2 ^ 30)%Z ->
  (* [comment removed for export] *)
  (forall k, mat_id model
               (import_iovecs_accesses (ms_read_byte ms) iov (Z_to_bv 64 (Z.of_nat (length iovs))) ++ iov_prefix_accesses iovs k)) ->
  (forall k, (1 <= k)%nat -> (k <= length bs)%nat ->
     crz segs (mkCfg (advance_past_svc (set_gpr0 ms (Z_to_bv 64 (Z.of_nat k)))) model) (T k)) ->
  crz segs (mkCfg ms model)
    (t_alt (fun i : wr_index bs => t_emit (map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) bs)) (T (proj1_sig i)))).
Proof.
  intros ms x8 model fd iov iovs bss T Hrom Hh Hsvc Hfd Hfdr Hno H0 H1 H2 Hcnt Hiok Harr Hbok Hbufs bs
         Ht1 Ht30 Hmi Hk.
  destruct (writev_check segs ms x8 model fd iov iovs bss Hrom Hfd Hfdr Hno H0 H1 H2 Hcnt Hiok Harr Hbok Hbufs
              Ht1 Ht30)
    as [Hlen Hchk]. fold bs in Hlen, Hchk.
  set (tot := iovs_total iovs) in *.
  set (CA := import_iovecs_accesses (ms_read_byte ms) iov (Z_to_bv 64 (Z.of_nat (length iovs)))) in *.
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
  assert (Hmat : forall k, materialize_model_accesses model (syscall_effect_accesses
                   (mkEffectU (Z_to_bv 64 (Z.of_nat k)) [] [] [] [] (CA ++ iov_prefix_accesses iovs k))) = Some model).
  { intros k. unfold syscall_effect_accesses. cbn [eff_copyins eff_writes write_accesses].
    rewrite app_nil_r. exact (Hmi k). }
  apply (crz_node_on segs (mkCfg ms model) (wr_index bs)
           (fun i => map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) bs))
           (fun i => mkCfg (advance_past_svc (set_gpr0 ms (Z_to_bv 64 (Z.of_nat (proj1_sig i))))) model)
           (fun i => T (proj1_sig i)) (wr_full bs Hnb)).
  2:{ apply (fam_on_sysno (mkCfg ms model) x8 Hsvc); rewrite Hno; lia. }
  2:{ intros [k [Hk1 Hk2]]. cbn [proj1_sig]. apply Hk; assumption. }
  assert (Hku : forall k, (k <= length bs)%nat -> bv_unsigned (Z_to_bv 64 (Z.of_nat k)) = Z.of_nat k).
  { intros k Hk2. apply u64_lit. lia. }
  split.
  - intros i. rewrite Enx. apply (sstep_syscall segs ms model x8 (effs i) model model _ Hh Hsvc); [| exact Hh | apply Hmat].
    apply check_syscall_ok_iff.
    destruct i as [k [Hk1 Hk2]]. unfold effs. cbn [proj1_sig]. rewrite Hchk.
    rewrite (Hku k Hk2), Nat2Z.id.
    rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia.
    replace (addr_is_error_b (Z_to_bv 64 (Z.of_nat k))) with false
      by (symmetry; unfold addr_is_error_b, two_pow_64; apply Z.ltb_ge; rewrite (Hku k Hk2); lia).
    rewrite (proj2 (access_ranges_eqb_eq _ _) eq_refl). reflexivity.
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
      unfold effs in Hm. rewrite Hmat in Hm. injection Hm as <-.
      exists i. rewrite Enx. split; reflexivity.
    + destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->).
      unfold effs in Hm. rewrite Hmat in Hm. discriminate.
    + destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->). congruence.
    + exfalso. rewrite Hchk in Hc. destruct eff as [ret ws zs us cs ci].
      destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate].
      destruct cs; [|discriminate]. destruct (_ && _)%bool; [destruct (access_ranges_eqb _ _)|]; discriminate.
Qed.

Lemma srz_writev_pending_lt : forall ms x8 model (fd : Z) (iov : word) iovs bss (T : nat -> TSet),
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
  let bs := concat bss in
  (1 <= iovs_total iovs)%Z -> (iovs_total iovs <= 2 ^ 30)%Z ->
  (* [comment removed for export] *)
  (forall k, accesses_outside_lazy
               (import_iovecs_accesses (ms_read_byte ms) iov (Z_to_bv 64 (Z.of_nat (length iovs))) ++ iov_prefix_accesses iovs k)
               (m_vm_lazy model)) ->
  (forall k, (1 <= k)%nat -> (k <= length bs)%nat ->
     crz segs (mkCfg (advance_past_svc (set_gpr0 ms (Z_to_bv 64 (Z.of_nat k)))) model) (T k)) ->
  crz segs (mkCfg ms model)
    (t_alt (fun i : wr_index bs => t_emit (map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) bs)) (T (proj1_sig i)))).
Proof.
  intros ms x8 model fd iov iovs bss T Hrom Hh Hsvc Hfd Hfdr Hno H0 H1 H2 Hcnt Hiok Harr Hbok Hbufs bs
         Ht1 Ht30 Hol Hk.
  eapply srz_writev_pending_mi; try eassumption. intros k. apply mat_id_of_outside. exact (Hol k).
Qed.

(* [comment removed for export] *)
Lemma writev_accesses_outside : forall ms (iov : word) iovs lazy,
  (bv_unsigned iov + 16 * Z.of_nat (length iovs) <= TASK_SIZE)%Z ->
  (length iovs <= 1024)%nat ->
  accesses_outside_lazy [(iov, (16 * length iovs)%nat)] lazy ->
  (forall b n, In (b, n) iovs -> accesses_outside_lazy [(b, word_to_nat n)] lazy) ->
  forall k, accesses_outside_lazy
              (import_iovecs_accesses (ms_read_byte ms) iov (Z_to_bv 64 (Z.of_nat (length iovs))) ++ iov_prefix_accesses iovs k)
              lazy.
Proof.
  intros ms iov iovs lazy Htask Hlen Harr Hbufs k a n lo sz Hin Hl.
  apply in_app_iff in Hin as [Hin|Hin].
  - pose proof (u64_range iov). unfold TASK_SIZE in Htask.
    refine (import_iovecs_accesses_outside (ms_read_byte ms) iov (Z_to_bv 64 (Z.of_nat (length iovs))) lo sz _ _ (a, n) Hin).
    + rewrite u64_lit by lia. lia.
    + unfold word_to_nat. rewrite u64_lit by lia. rewrite Nat2Z.id.
      apply (Harr iov (16 * length iovs)%nat lo sz); [left; reflexivity | exact Hl].
  - exact (iov_prefix_accesses_outside iovs k lazy Hbufs a n lo sz Hin Hl).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma srz_writev2_lt : forall regs (pc : word) mem model w (fd : Z) (iov b1 n1 b2 n2 : word) bs1 bs2 (T : nat -> TSet),
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
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
  (bv_unsigned iov + 32 <= TASK_SIZE)%Z ->
  (bv_unsigned b1 + bv_unsigned n1 <= TASK_SIZE)%Z ->
  (bv_unsigned b2 + bv_unsigned n2 <= TASK_SIZE)%Z ->
  (1 <= bv_unsigned n1 + bv_unsigned n2)%Z ->
  (bv_unsigned n1 + bv_unsigned n2 <= 2 ^ 30)%Z ->
  accesses_outside_lazy [(iov, 32%nat)] (m_vm_lazy model) ->
  accesses_outside_lazy [(b1, word_to_nat n1)] (m_vm_lazy model) ->
  accesses_outside_lazy [(b2, word_to_nat n2)] (m_vm_lazy model) ->
  (forall k, (1 <= k)%nat -> (k <= length (bs1 ++ bs2))%nat ->
     crz segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat k))) (v_addi pc 4) mem (seg_rom segs)) model)
               (T k)) ->
  crz segs (mkCfg (mkst regs pc mem (seg_rom segs)) model)
    (t_alt (fun i : wr_index (bs1 ++ bs2) =>
       t_emit (map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) (bs1 ++ bs2))) (T (proj1_sig i)))).
Proof.
  intros regs pc mem model w fd iov b1 n1 b2 n2 bs1 bs2 T HF HE Hh Hfd Hfdr H17 H10 H11 H12
         Rb1 Rn1 Rb2 Rn2 Rs1 Rs2 Hiok Hb1 Hb2 Ht1 Ht30 Hoa Ho1 Ho2 Hk.
  eapply crz_sys_lazy; [exact Hh | exact HF | exact HE |].
  pose proof (u64_range n1). pose proof (u64_range n2).
  replace (bs1 ++ bs2) with (concat [bs1; bs2]) in * by (cbn; rewrite app_nil_r; reflexivity).
  eapply (srz_writev_pending_lt (epend regs pc mem (seg_rom segs) (getr regs 17)) (getr regs 17) model fd iov
            [(b1, n1); (b2, n2)] [bs1; bs2] T);
    [reflexivity | exact Hh | reflexivity | exact Hfd | exact Hfdr
    | rewrite H17; apply u64_lit; lia
    | rewrite ms_gpr_epend0; exact H10 | rewrite ms_gpr_epend1; exact H11 | rewrite ms_gpr_epend2; exact H12
    | cbn; lia | change (Z.of_nat (length [(b1, n1); (b2, n2)])) with 2%Z; lia
    | | cbn [iov_bufs_ok]; repeat split; assumption | | cbn [iovs_total]; lia | cbn [iovs_total]; lia | | ].
  - cbn [iov_array ms_mem epend].
    replace (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned iov + 16)) + 8)) with (Z_to_bv 64 (bv_unsigned iov + 24)).
    2:{ change (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned iov + 16)) + 8)) with (at_ (at_ iov 16) 8).
        rewrite at_at. reflexivity. }
    repeat split; try assumption; lia.
  - cbn [iov_bufs ms_mem epend]. repeat split; assumption.
  - apply writev_accesses_outside; [change (Z.of_nat (length [(b1, n1); (b2, n2)])) with 2%Z; lia | cbn; lia | exact Hoa |].
    intros b n [E|[E|[]]]; injection E as <- <-; assumption.
  - intros k Hk1 Hk2. rewrite adv_set_epend. apply Hk; assumption.
Qed.

Lemma srz_writev1_lt : forall regs (pc : word) mem model w (fd : Z) (iov b1 n1 : word) bs1 (T : nat -> TSet),
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
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
  (1 <= bv_unsigned n1)%Z ->
  (bv_unsigned n1 <= 2 ^ 30)%Z ->
  accesses_outside_lazy [(iov, 16%nat)] (m_vm_lazy model) ->
  accesses_outside_lazy [(b1, word_to_nat n1)] (m_vm_lazy model) ->
  (forall k, (1 <= k)%nat -> (k <= length bs1)%nat ->
     crz segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat k))) (v_addi pc 4) mem (seg_rom segs)) model)
               (T k)) ->
  crz segs (mkCfg (mkst regs pc mem (seg_rom segs)) model)
    (t_alt (fun i : wr_index bs1 =>
       t_emit (map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) bs1)) (T (proj1_sig i)))).
Proof.
  intros regs pc mem model w fd iov b1 n1 bs1 T HF HE Hh Hfd Hfdr H17 H10 H11 H12
         Rb1 Rn1 Rs1 Hiok Hb1 Ht1 Ht30 Hoa Ho1 Hk.
  eapply crz_sys_lazy; [exact Hh | exact HF | exact HE |].
  pose proof (u64_range n1).
  replace bs1 with (concat [bs1]) in Hk by (cbn; rewrite app_nil_r; reflexivity).
  replace bs1 with (concat [bs1]) by (cbn; rewrite app_nil_r; reflexivity).
  eapply (srz_writev_pending_lt (epend regs pc mem (seg_rom segs) (getr regs 17)) (getr regs 17) model fd iov
            [(b1, n1)] [bs1] T);
    [reflexivity | exact Hh | reflexivity | exact Hfd | exact Hfdr
    | rewrite H17; apply u64_lit; lia
    | rewrite ms_gpr_epend0; exact H10 | rewrite ms_gpr_epend1; exact H11 | rewrite ms_gpr_epend2; exact H12
    | cbn; lia | change (Z.of_nat (length [(b1, n1)])) with 1%Z; lia
    | | cbn [iov_bufs_ok]; split; [assumption | exact I] | | cbn [iovs_total]; lia | cbn [iovs_total]; lia | | ].
  - cbn [iov_array ms_mem epend]. repeat split; try assumption; lia.
  - cbn [iov_bufs ms_mem epend]. split; [assumption | exact I].
  - apply writev_accesses_outside; [change (Z.of_nat (length [(b1, n1)])) with 1%Z; lia | cbn; lia | exact Hoa |].
    intros b n [E|[]]; injection E as <- <-; assumption.
  - intros k Hk1 Hk2. rewrite adv_set_epend. apply Hk; assumption.
Qed.

Lemma srz_writev2_wall_lt : forall regs (pc : word) mem model w (fd : Z) (iov b1 n1 b2 n2 : word) bs1 bs2 (K : TSet),
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
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
  (bv_unsigned iov + 32 <= TASK_SIZE)%Z ->
  (bv_unsigned b1 + bv_unsigned n1 <= TASK_SIZE)%Z ->
  (bv_unsigned b2 + bv_unsigned n2 <= TASK_SIZE)%Z ->
  (1 <= bv_unsigned n1 + bv_unsigned n2)%Z ->
  (bv_unsigned n1 + bv_unsigned n2 <= 2 ^ 30)%Z ->
  accesses_outside_lazy [(iov, 32%nat)] (m_vm_lazy model) ->
  accesses_outside_lazy [(b1, word_to_nat n1)] (m_vm_lazy model) ->
  accesses_outside_lazy [(b2, word_to_nat n2)] (m_vm_lazy model) ->
  K [] ->
  (forall k, (1 <= k)%nat -> (k <= length (bs1 ++ bs2))%nat ->
     crz segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat k))) (v_addi pc 4) mem (seg_rom segs)) model)
               (t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k (bs1 ++ bs2))) K)) ->
  crz segs (mkCfg (mkst regs pc mem (seg_rom segs)) model)
            (t_emit (map (WriteEv (Z_to_bv 64 fd)) (bs1 ++ bs2)) K).
Proof.
  intros regs pc mem model w fd iov b1 n1 b2 n2 bs1 bs2 K HF HE Hh Hfd Hfdr H17 H10 H11 H12
         Rb1 Rn1 Rb2 Rn2 Rs1 Rs2 Hiok Hb1 Hb2 Ht1 Ht30 Hoa Ho1 Ho2 HK Hk.
  pose proof (rdn_length segs mem _ _ _ Rs1) as L1. pose proof (rdn_length segs mem _ _ _ Rs2) as L2.
  pose proof (u64_range n1). pose proof (u64_range n2).
  apply crz_wall; [rewrite length_app; unfold word_to_nat in L1, L2; lia | exact HK |].
  eapply (srz_writev2_lt regs pc mem model w fd iov b1 n1 b2 n2 bs1 bs2
            (fun k => t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k (bs1 ++ bs2))) K)); eassumption.
Qed.

Lemma srz_writev1_wall_lt : forall regs (pc : word) mem model w (fd : Z) (iov b1 n1 : word) bs1 (K : TSet),
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
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
  (1 <= bv_unsigned n1)%Z ->
  (bv_unsigned n1 <= 2 ^ 30)%Z ->
  accesses_outside_lazy [(iov, 16%nat)] (m_vm_lazy model) ->
  accesses_outside_lazy [(b1, word_to_nat n1)] (m_vm_lazy model) ->
  K [] ->
  (forall k, (1 <= k)%nat -> (k <= length bs1)%nat ->
     crz segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat k))) (v_addi pc 4) mem (seg_rom segs)) model)
               (t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k bs1)) K)) ->
  crz segs (mkCfg (mkst regs pc mem (seg_rom segs)) model)
            (t_emit (map (WriteEv (Z_to_bv 64 fd)) bs1) K).
Proof.
  intros regs pc mem model w fd iov b1 n1 bs1 K HF HE Hh Hfd Hfdr H17 H10 H11 H12
         Rb1 Rn1 Rs1 Hiok Hb1 Ht1 Ht30 Hoa Ho1 HK Hk.
  pose proof (rdn_length segs mem _ _ _ Rs1) as L1. pose proof (u64_range n1).
  apply crz_wall; [unfold word_to_nat in L1; lia | exact HK |].
  eapply (srz_writev1_lt regs pc mem model w fd iov b1 n1 bs1
            (fun k => t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k bs1)) K)); eassumption.
Qed.

(* [comment removed for export] *)
Lemma srz_writev1_zero_lt : forall regs (pc : word) mem model w (fd : Z) (iov b1 : word) K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  (0 < fd < 2^31)%Z ->
  getr regs 17 = Z_to_bv 64 66 ->
  getr regs 10 = Z_to_bv 64 fd ->
  getr regs 11 = iov ->
  getr regs 12 = Z_to_bv 64 1 ->
  rdn segs mem iov 8%nat = Some (word_to_le_bytes 8 b1) ->
  rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 8)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  (bv_unsigned iov + 16 <= TASK_SIZE)%Z ->
  (bv_unsigned b1 <= TASK_SIZE)%Z ->
  accesses_outside_lazy [(iov, 16%nat)] (m_vm_lazy model) ->
  crz segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) mem (seg_rom segs)) model) K ->
  crz segs (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
Proof.
  intros regs pc mem model w fd iov b1 K HF HE Hh Hfd Hfdr H17 H10 H11 H12 Rb1 Rn1 Hiok Hb1 Hoa Hc.
  eapply crz_sys_lazy; [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem (seg_rom segs) (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 66%Z) by (rewrite H17; apply u64_lit; lia).
  assert (Harr : iov_array segs (ms_mem ms) iov [(b1, Z_to_bv 64 0)]).
  { cbn [iov_array ms_mem ms epend]. refine (conj Rb1 (conj Rn1 (conj _ I))). rewrite u64_lit by lia. lia. }
  assert (Himp : import_iovecs (ms_read_byte ms) iov (Z_to_bv 64 1) = ImpOk [(b1, Z_to_bv 64 0)]).
  { unfold import_iovecs. rewrite (proj2 (bv_eqb_eq _ _) eq_refl).
    rewrite (access_okb_of_le iov 16) by lia.
    rewrite (read_iovec_entry_of_array segs ms b1 (Z_to_bv 64 0) [] iov eq_refl Harr).
    rewrite u64_lit by lia. change (Z.min 0 MAX_RW_COUNT) with 0%Z.
    rewrite (access_okb_of_le b1 0) by lia. reflexivity. }
  assert (Hacc : import_iovecs_accesses (ms_read_byte ms) iov (Z_to_bv 64 1) = [(iov, 16%nat)]).
  { unfold import_iovecs_accesses. rewrite (proj2 (bv_eqb_eq _ _) eq_refl).
    rewrite (access_okb_of_le iov 16) by lia. reflexivity. }
  eapply (srz_ret_only_copyins_silent_lt segs ms model (getr regs 17) [(iov, 16%nat)] (Z_to_bv 64 0) model);
    [exact Hh | reflexivity | | exact Hh | exact Hoa | unfold ms; rewrite adv_set_epend; exact Hc].
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
  rewrite in_mem_si, Himp, Hacc.
  unfold cap_iovecs. cbn [cap_iovecs_aux iovs_total].
  change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. rewrite Z.min_r by (unfold MAX_RW_COUNT; lia).
  change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. cbv beta iota zeta.
  change ((0 + 0 =? 0)%Z) with true. cbv beta iota. reflexivity.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma srz_writev2_mi : forall regs (pc : word) mem model w (fd : Z) (iov b1 n1 b2 n2 : word) bs1 bs2 (T : nat -> TSet),
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
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
  (bv_unsigned iov + 32 <= TASK_SIZE)%Z ->
  (bv_unsigned b1 + bv_unsigned n1 <= TASK_SIZE)%Z ->
  (bv_unsigned b2 + bv_unsigned n2 <= TASK_SIZE)%Z ->
  (1 <= bv_unsigned n1 + bv_unsigned n2)%Z ->
  (bv_unsigned n1 + bv_unsigned n2 <= 2 ^ 30)%Z ->
  (forall k, mat_id model (import_iovecs_accesses (mrb segs mem) iov (Z_to_bv 64 2) ++ iov_prefix_accesses [(b1, n1); (b2, n2)] k)) ->
  (forall k, (1 <= k)%nat -> (k <= length (bs1 ++ bs2))%nat ->
     crz segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat k))) (v_addi pc 4) mem (seg_rom segs)) model)
               (T k)) ->
  crz segs (mkCfg (mkst regs pc mem (seg_rom segs)) model)
    (t_alt (fun i : wr_index (bs1 ++ bs2) =>
       t_emit (map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) (bs1 ++ bs2))) (T (proj1_sig i)))).
Proof.
  intros regs pc mem model w fd iov b1 n1 b2 n2 bs1 bs2 T HF HE Hh Hfd Hfdr H17 H10 H11 H12
         Rb1 Rn1 Rb2 Rn2 Rs1 Rs2 Hiok Hb1 Hb2 Ht1 Ht30 Hmi Hk.
  eapply crz_sys_lazy; [exact Hh | exact HF | exact HE |].
  pose proof (u64_range n1). pose proof (u64_range n2).
  replace (bs1 ++ bs2) with (concat [bs1; bs2]) in * by (cbn; rewrite app_nil_r; reflexivity).
  eapply (srz_writev_pending_mi (epend regs pc mem (seg_rom segs) (getr regs 17)) (getr regs 17) model fd iov
            [(b1, n1); (b2, n2)] [bs1; bs2] T);
    [reflexivity | exact Hh | reflexivity | exact Hfd | exact Hfdr
    | rewrite H17; apply u64_lit; lia
    | rewrite ms_gpr_epend0; exact H10 | rewrite ms_gpr_epend1; exact H11 | rewrite ms_gpr_epend2; exact H12
    | cbn; lia | change (Z.of_nat (length [(b1, n1); (b2, n2)])) with 2%Z; lia
    | | cbn [iov_bufs_ok]; repeat split; assumption | | cbn [iovs_total]; lia | cbn [iovs_total]; lia | | ].
  - cbn [iov_array ms_mem epend].
    replace (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned iov + 16)) + 8)) with (Z_to_bv 64 (bv_unsigned iov + 24)).
    2:{ change (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned iov + 16)) + 8)) with (at_ (at_ iov 16) 8).
        rewrite at_at. reflexivity. }
    repeat split; try assumption; lia.
  - cbn [iov_bufs ms_mem epend]. repeat split; assumption.
  - intros k. change (Z.of_nat (length [(b1, n1); (b2, n2)])) with 2%Z. cbn [ms_read_byte epend]. exact (Hmi k).
  - intros k Hk1 Hk2. rewrite adv_set_epend. apply Hk; assumption.
Qed.

Lemma srz_writev1_mi : forall regs (pc : word) mem model w (fd : Z) (iov b1 n1 : word) bs1 (T : nat -> TSet),
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
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
  (1 <= bv_unsigned n1)%Z ->
  (bv_unsigned n1 <= 2 ^ 30)%Z ->
  (forall k, mat_id model (import_iovecs_accesses (mrb segs mem) iov (Z_to_bv 64 1) ++ iov_prefix_accesses [(b1, n1)] k)) ->
  (forall k, (1 <= k)%nat -> (k <= length bs1)%nat ->
     crz segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat k))) (v_addi pc 4) mem (seg_rom segs)) model)
               (T k)) ->
  crz segs (mkCfg (mkst regs pc mem (seg_rom segs)) model)
    (t_alt (fun i : wr_index bs1 =>
       t_emit (map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) bs1)) (T (proj1_sig i)))).
Proof.
  intros regs pc mem model w fd iov b1 n1 bs1 T HF HE Hh Hfd Hfdr H17 H10 H11 H12
         Rb1 Rn1 Rs1 Hiok Hb1 Ht1 Ht30 Hmi Hk.
  eapply crz_sys_lazy; [exact Hh | exact HF | exact HE |].
  pose proof (u64_range n1).
  replace bs1 with (concat [bs1]) in Hk by (cbn; rewrite app_nil_r; reflexivity).
  replace bs1 with (concat [bs1]) by (cbn; rewrite app_nil_r; reflexivity).
  eapply (srz_writev_pending_mi (epend regs pc mem (seg_rom segs) (getr regs 17)) (getr regs 17) model fd iov
            [(b1, n1)] [bs1] T);
    [reflexivity | exact Hh | reflexivity | exact Hfd | exact Hfdr
    | rewrite H17; apply u64_lit; lia
    | rewrite ms_gpr_epend0; exact H10 | rewrite ms_gpr_epend1; exact H11 | rewrite ms_gpr_epend2; exact H12
    | cbn; lia | change (Z.of_nat (length [(b1, n1)])) with 1%Z; lia
    | | cbn [iov_bufs_ok]; split; [assumption | exact I] | | cbn [iovs_total]; lia | cbn [iovs_total]; lia | | ].
  - cbn [iov_array ms_mem epend]. repeat split; try assumption; lia.
  - cbn [iov_bufs ms_mem epend]. split; [assumption | exact I].
  - intros k. change (Z.of_nat (length [(b1, n1)])) with 1%Z. cbn [ms_read_byte epend]. exact (Hmi k).
  - intros k Hk1 Hk2. rewrite adv_set_epend. apply Hk; assumption.
Qed.

Lemma srz_writev2_wall_mi : forall regs (pc : word) mem model w (fd : Z) (iov b1 n1 b2 n2 : word) bs1 bs2 (K : TSet),
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
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
  (bv_unsigned iov + 32 <= TASK_SIZE)%Z ->
  (bv_unsigned b1 + bv_unsigned n1 <= TASK_SIZE)%Z ->
  (bv_unsigned b2 + bv_unsigned n2 <= TASK_SIZE)%Z ->
  (1 <= bv_unsigned n1 + bv_unsigned n2)%Z ->
  (bv_unsigned n1 + bv_unsigned n2 <= 2 ^ 30)%Z ->
  (forall k, mat_id model (import_iovecs_accesses (mrb segs mem) iov (Z_to_bv 64 2) ++ iov_prefix_accesses [(b1, n1); (b2, n2)] k)) ->
  K [] ->
  (forall k, (1 <= k)%nat -> (k <= length (bs1 ++ bs2))%nat ->
     crz segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat k))) (v_addi pc 4) mem (seg_rom segs)) model)
               (t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k (bs1 ++ bs2))) K)) ->
  crz segs (mkCfg (mkst regs pc mem (seg_rom segs)) model)
            (t_emit (map (WriteEv (Z_to_bv 64 fd)) (bs1 ++ bs2)) K).
Proof.
  intros regs pc mem model w fd iov b1 n1 b2 n2 bs1 bs2 K HF HE Hh Hfd Hfdr H17 H10 H11 H12
         Rb1 Rn1 Rb2 Rn2 Rs1 Rs2 Hiok Hb1 Hb2 Ht1 Ht30 Hmi HK Hk.
  pose proof (rdn_length segs mem _ _ _ Rs1) as L1. pose proof (rdn_length segs mem _ _ _ Rs2) as L2.
  pose proof (u64_range n1). pose proof (u64_range n2).
  apply crz_wall; [rewrite length_app; unfold word_to_nat in L1, L2; lia | exact HK |].
  eapply (srz_writev2_mi regs pc mem model w fd iov b1 n1 b2 n2 bs1 bs2
            (fun k => t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k (bs1 ++ bs2))) K)); eassumption.
Qed.

Lemma srz_writev1_wall_mi : forall regs (pc : word) mem model w (fd : Z) (iov b1 n1 : word) bs1 (K : TSet),
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
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
  (1 <= bv_unsigned n1)%Z ->
  (bv_unsigned n1 <= 2 ^ 30)%Z ->
  (forall k, mat_id model (import_iovecs_accesses (mrb segs mem) iov (Z_to_bv 64 1) ++ iov_prefix_accesses [(b1, n1)] k)) ->
  K [] ->
  (forall k, (1 <= k)%nat -> (k <= length bs1)%nat ->
     crz segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat k))) (v_addi pc 4) mem (seg_rom segs)) model)
               (t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k bs1)) K)) ->
  crz segs (mkCfg (mkst regs pc mem (seg_rom segs)) model)
            (t_emit (map (WriteEv (Z_to_bv 64 fd)) bs1) K).
Proof.
  intros regs pc mem model w fd iov b1 n1 bs1 K HF HE Hh Hfd Hfdr H17 H10 H11 H12
         Rb1 Rn1 Rs1 Hiok Hb1 Ht1 Ht30 Hmi HK Hk.
  pose proof (rdn_length segs mem _ _ _ Rs1) as L1. pose proof (u64_range n1).
  apply crz_wall; [unfold word_to_nat in L1; lia | exact HK |].
  eapply (srz_writev1_mi regs pc mem model w fd iov b1 n1 bs1
            (fun k => t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k bs1)) K)); eassumption.
Qed.

Lemma srz_writev1_zero_mi : forall regs (pc : word) mem model w (fd : Z) (iov b1 : word) K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  (0 < fd < 2^31)%Z ->
  getr regs 17 = Z_to_bv 64 66 ->
  getr regs 10 = Z_to_bv 64 fd ->
  getr regs 11 = iov ->
  getr regs 12 = Z_to_bv 64 1 ->
  rdn segs mem iov 8%nat = Some (word_to_le_bytes 8 b1) ->
  rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 8)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  (bv_unsigned iov + 16 <= TASK_SIZE)%Z ->
  (bv_unsigned b1 <= TASK_SIZE)%Z ->
  mat_id model [(iov, 16%nat)] ->
  crz segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) mem (seg_rom segs)) model) K ->
  crz segs (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
Proof.
  intros regs pc mem model w fd iov b1 K HF HE Hh Hfd Hfdr H17 H10 H11 H12 Rb1 Rn1 Hiok Hb1 Hmi Hc.
  eapply crz_sys_lazy; [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem (seg_rom segs) (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 66%Z) by (rewrite H17; apply u64_lit; lia).
  assert (Harr : iov_array segs (ms_mem ms) iov [(b1, Z_to_bv 64 0)]).
  { cbn [iov_array ms_mem ms epend]. refine (conj Rb1 (conj Rn1 (conj _ I))). rewrite u64_lit by lia. lia. }
  assert (Himp : import_iovecs (ms_read_byte ms) iov (Z_to_bv 64 1) = ImpOk [(b1, Z_to_bv 64 0)]).
  { unfold import_iovecs. rewrite (proj2 (bv_eqb_eq _ _) eq_refl).
    rewrite (access_okb_of_le iov 16) by lia.
    rewrite (read_iovec_entry_of_array segs ms b1 (Z_to_bv 64 0) [] iov eq_refl Harr).
    rewrite u64_lit by lia. change (Z.min 0 MAX_RW_COUNT) with 0%Z.
    rewrite (access_okb_of_le b1 0) by lia. reflexivity. }
  assert (Hacc : import_iovecs_accesses (ms_read_byte ms) iov (Z_to_bv 64 1) = [(iov, 16%nat)]).
  { unfold import_iovecs_accesses. rewrite (proj2 (bv_eqb_eq _ _) eq_refl).
    rewrite (access_okb_of_le iov 16) by lia. reflexivity. }
  eapply (srz_ret_only_copyins_silent_mi segs ms model (getr regs 17) [(iov, 16%nat)] (Z_to_bv 64 0) model);
    [exact Hh | reflexivity | | exact Hh | exact Hmi | unfold ms; rewrite adv_set_epend; exact Hc].
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
  rewrite in_mem_si, Himp, Hacc.
  unfold cap_iovecs. cbn [cap_iovecs_aux iovs_total].
  change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. rewrite Z.min_r by (unfold MAX_RW_COUNT; lia).
  change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. cbv beta iota zeta.
  change ((0 + 0 =? 0)%Z) with true. cbv beta iota. reflexivity.
Qed.

End WithSegs.
