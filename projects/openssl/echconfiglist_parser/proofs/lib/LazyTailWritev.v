(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (RomBase.sys_rob robustness premises on the fd, openat, ioctl and writev nodes; the channel-reader premise on writev; C-string path reads bounded below TASK_SIZE; copy_iovecs_accesses now lists each iovec entry's own access). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/echconfiglist_parser/lib/LazyFdNodes.v; 152 of its 420 lines of code are new or changed and 873 lines of the source are left out; taken from projects/openssl/echconfiglist_parser/proofs/lib/LazyFdNodes.v, lines 7-25, 38-50, 801-837, 861-1126 and 1162-1224, as in the LPS 727298f3 update. *)
(* Theorem Labs, 2026-11 (LPS 727298f3): the writev nodes of LazyFdNodes.v (rz_writev_pending_lazy,
   rz_writev2_lazy, rz_writev1_lazy, their two wall forms and rz_writev1_zero_lazy, LazyFdNodes.v:860-1224)
   as walks over the run's segment list segs ++ tail, a tail that is neither executable nor writable.  The
   restricted state carries seg_rom (segs ++ tail) as its read-only backing; the lazy view (lzok), the code
   fetch and the memory facts stay over the binary's list segs; a step invariant I goes into the node and
   comes out on every continuation.  The system call reads the iovec array and the buffers through
   ms_read_byte (overlay, then backing), so the reads over segs are first lifted to segs ++ tail (a read the
   binary's list serves is served the same by the larger list, Common/Cfg/RomStable.v:335) and LibWritev.v's
   writev_outcome / writev_rob are then used at segs ++ tail. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import LazyTail.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import
  Scfg SimInv ExitSim PropExec CatExec CatSim MmapSim AllocSim FileSim RelSpec
  ShapeAlg Nodes AgentLib AgentNodes Gap04 RefNodes RefNodesDir Hoare LibWritev SReach
  LazyRestrict LazyRestrictRun LazyRestrictAlg LazyLedger LazySR LazyNodes LazyFdNodes.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.Cfg Require RomStable.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section LazyTailWritev.
  Variables segs tail : list Segment.
  Hypothesis Hnx : forall s, In s tail -> seg_executable s = false.
  Hypothesis Hnw : forall s, In s tail -> seg_writable s = false.
  Context {SC : StepCfg}.
  Variable I : config -> Prop.
  Hypothesis HI : forall c evs c', I c -> sstep_cfg (segs ++ tail) the_scfg c evs (SNext c') -> I c'.

  (* A read of n bytes the binary's list serves (overlay, then the list's bytes) is served the same by
     the larger list. *)
  Lemma ltW_rdn_app : forall m a n bs,
    rdn segs m a n = Some bs -> rdn (segs ++ tail) m a n = Some bs.
  Proof.
    intros m a n bs H. rewrite <- ov_rdn in H |- *.
    exact (RomStable.ov_read_bytes_app_nx segs tail n m a bs H).
  Qed.

  Lemma ltW_iov_bufs_app : forall m iovs bss,
    iov_bufs segs m iovs bss -> iov_bufs (segs ++ tail) m iovs bss.
  Proof.
    intros m iovs. induction iovs as [|[b n] r IH]; intros [|bs bss] Hb; cbn in Hb; try contradiction.
    - exact Logic.I.
    - destruct Hb as [H1 H2]. split; [exact (ltW_rdn_app _ _ _ _ H1) | exact (IH bss H2)].
  Qed.

  (* LazyFdNodes.v:800 iov_array_full with the full iovec array read over segs ++ tail and the copy-in
     ledger read through a state whose backing is seg_rom (segs ++ tail). *)
  Lemma ltW_iov_array_full : forall L S mF iov iovs,
    lazy_ranges_okb segs L = true ->
    iov_array segs (restrict_mem L S mF) iov iovs ->
    iov_array (segs ++ tail) mF iov iovs
    /\ (forall rom x8 regs pc a n, In (a, n) (copy_iovecs_accesses
          (ms_read_byte {| ms_regs := regs; ms_fregs := bvmap_empty; ms_pc_val := pc; ms_svc_pending := x8;
                           ms_resv := None; ms_fcsr := Z_to_bv 32 0; ms_mem := mF; ms_rom := rom |}) iov (length iovs)) ->
          rom = seg_rom (segs ++ tail) -> range_visible (hiddenb L S) a n).
  Proof.
    intros L S mF iov iovs HL. revert iov. induction iovs as [|[b n] r IH]; intros iov Ha.
    - split; [exact Logic.I|]. intros rom x8 regs pc a k [].
    - destruct Ha as (Hb & Hn & Hlt & Hr).
      destruct (rdn_restrict segs L S mF _ _ _ HL Hb) as [HbS Vb].
      destruct (rdn_restrict segs L S mF _ _ _ HL Hn) as [HnS Vn].
      pose proof (ltW_rdn_app _ _ _ _ HbS) as HbF. pose proof (ltW_rdn_app _ _ _ _ HnS) as HnF.
      destruct (IH _ Hr) as [HrF Hvis]. split; [repeat split; assumption|].
      intros rom x8 regs pc a k Hin ->. cbn [copy_iovecs_accesses length] in Hin.
      set (ms := {| ms_regs := regs; ms_fregs := bvmap_empty; ms_pc_val := pc; ms_svc_pending := x8;
                     ms_resv := None; ms_fcsr := Z_to_bv 32 0; ms_mem := mF; ms_rom := seg_rom (segs ++ tail) |}) in *.
      apply in_app_or in Hin. destruct Hin as [Hin | Hin].
      + unfold iovec_entry_accesses in Hin.
        rewrite (read_u64_rdn (segs ++ tail) ms iov b eq_refl HbF) in Hin.
        rewrite bv_add_Zform in Hin. change (bv_unsigned (8 : word)) with 8%Z in Hin.
        rewrite (read_u64_rdn (segs ++ tail) ms _ n eq_refl HnF) in Hin.
        destruct Hin as [Hin | []]. injection Hin as <- <-.
        apply range_visible_8_8; assumption.
      + unfold read_iovec_entry in Hin.
        rewrite (read_u64_rdn (segs ++ tail) ms iov b eq_refl HbF) in Hin.
        rewrite bv_add_Zform in Hin. change (bv_unsigned (8 : word)) with 8%Z in Hin.
        rewrite (read_u64_rdn (segs ++ tail) ms _ n eq_refl HnF) in Hin.
        rewrite (proj2 (Z.leb_gt _ _) Hlt) in Hin.
        rewrite bv_add_Zform in Hin. change (bv_unsigned (16 : word)) with 16%Z in Hin.
        eapply Hvis; [exact Hin | reflexivity].
  Qed.

  (* LazyFdNodes.v:860 *)
  Lemma rz_writev_pending_lazy_tail : forall L S Zr msF1 regs pc mem mo (fd : Z) (iov : word) iovs bss (T : nat -> TSet),
    lzok segs L S Zr (mkCfg msF1 mo) ->
    I (mkCfg msF1 mo) ->
    restrict L S msF1 = epend regs pc mem (seg_rom (segs ++ tail)) (getr regs 17) ->
    ms_svc_pending msF1 = Some (getr regs 17) ->
    fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
    m_channel_reader mo = true ->
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
       restrict L S msF' = mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat k))) (v_addi pc 4) mem (seg_rom (segs ++ tail)) ->
       hid_same L S msF1 msF' ->
       I (mkCfg msF' mo') ->
       realizes (segs ++ tail) (mkCfg msF' mo') (T k)) ->
    realizes (segs ++ tail) (mkCfg msF1 mo)
      (t_alt (fun i : wr_index bs => t_emit (map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) bs)) (T (proj1_sig i)))).
  Proof using Hnx Hnw HI.
    intros L S Zr msF1 regs pc mem mo fd iov iovs bss T Hok1 HIc Hr1 Hsvc1 Hfd Hrdr Hfdr H17 H10 H11 H12 Hcnt Harr Hbufs
           Hiov Hrng bs Ht1 Ht30 Hk.
    destruct msF1 as [rg fr pcv svc rv fc mF rom].
    unfold restrict, restrict_by, with_mem, epend in Hr1. cbn in Hr1.
    injection Hr1 as Erg Efr Epc Esvc Erv Efc Emm Erom. subst rg fr pcv svc rv fc rom.
    change (restrict_mem_by (hiddenb L S) mF) with (restrict_mem L S mF) in Emm. subst mem.
    set (ms := {| ms_regs := regs; ms_fregs := bvmap_empty; ms_pc_val := pc; ms_svc_pending := Some (getr regs 17);
                   ms_resv := None; ms_fcsr := Z_to_bv 32 0; ms_mem := mF; ms_rom := seg_rom (segs ++ tail) |}) in *.
    (* the iovec array and the buffers, read in full over segs ++ tail *)
    destruct (ltW_iov_array_full L S mF iov iovs (lzok_ranges Hok1) Harr) as [HarrF HvisA].
    destruct (iov_bufs_full segs L S mF iovs bss (lzok_ranges Hok1) Hbufs) as [HbufsS HvisB].
    pose proof (ltW_iov_bufs_app mF iovs bss HbufsS) as HbufsF.
    assert (Hno : bv_unsigned (getr regs 17) = 66%Z) by (rewrite H17; apply u64_lit; lia).
    destruct (writev_outcome (segs ++ tail) ms (getr regs 17) mo fd iov iovs bss eq_refl Hfd Hrdr Hfdr Hno H10 H11 H12
                Hcnt HarrF HbufsF Hiov Hrng Ht1 Ht30)
      as [Hlen Hchk]. fold bs in Hlen, Hchk.
    set (CA := import_iovecs_accesses (ms_read_byte ms) iov (Z_to_bv 64 (Z.of_nat (length iovs)))) in *.
    assert (Hnb : (1 <= length bs)%nat) by lia.
    (* every copy-in range of the call is visible in the restricted state *)
    assert (HvisCA : forall a n, In (a, n) CA -> range_visible (hiddenb L S) a n).
    { intros a n Hin. unfold CA in Hin.
      destruct iovs as [|[b1 n1] [|e2 r]]; [cbn in Hcnt; lia | |].
      - change (Z_to_bv 64 (Z.of_nat (length [(b1, n1)]))) with (Z_to_bv 64 1) in Hin.
        rewrite (proj2 (import_iovecs_of_array1 (segs ++ tail) ms b1 n1 iov eq_refl HarrF
                          ltac:(cbn [length] in Hiov; lia) (proj1 Hrng))) in Hin.
        destruct Hin as [Hin|[]]. injection Hin as <- <-.
        destruct Harr as (Hb & Hn & _ & _).
        apply range_visible_8_8;
          [exact (proj2 (rdn_restrict segs L S mF _ _ _ (lzok_ranges Hok1) Hb))
          | exact (proj2 (rdn_restrict segs L S mF _ _ _ (lzok_ranges Hok1) Hn))].
      - rewrite (proj2 (import_iovecs_of_array (segs ++ tail) ms _ iov eq_refl HarrF
                          ltac:(cbn [length] in *; lia) Hiov Hrng)) in Hin.
        eapply (HvisA (seg_rom (segs ++ tail)) (Some (getr regs 17)) regs pc); [exact Hin | reflexivity]. }
    pose (effs := fun i : wr_index bs =>
            mkEffectU (Z_to_bv 64 (Z.of_nat (proj1_sig i))) [] [] [] [] (CA ++ iov_prefix_accesses iovs (proj1_sig i))).
    assert (Hvis : forall i, ranges_visible (hiddenb L S) (syscall_effect_accesses (effs i))).
    { intros [k Hk'] a n Hin. unfold effs, syscall_effect_accesses in Hin.
      cbn [proj1_sig eff_copyins eff_writes write_accesses] in Hin.
      rewrite app_nil_r in Hin. apply in_app_iff in Hin. destruct Hin as [Hin|Hin].
      - exact (HvisCA a n Hin).
      - exact (HvisB k a n Hin). }
    assert (Hstep : forall i, exists mo', materialize_model_accesses mo (syscall_effect_accesses (effs i)) = Some mo'
               /\ same_but_materialized mo mo'
               /\ lzok segs L S Zr (mkCfg (advance_past_svc (apply_effect ms (effs i))) mo')
               /\ hid_same L S ms (advance_past_svc (apply_effect ms (effs i)))).
    { intros i. apply (lzok_after_fd_op segs L S Zr ms mo mo (effs i) Hok1 eq_refl (lzok_halted Hok1) (Hvis i)).
      intros a Ha. unfold effs. destruct ms; reflexivity. }
    assert (Hch : exists f : wr_index bs -> Model, forall i,
               materialize_model_accesses mo (syscall_effect_accesses (effs i)) = Some (f i)
               /\ same_but_materialized mo (f i)
               /\ lzok segs L S Zr (mkCfg (advance_past_svc (apply_effect ms (effs i))) (f i))
               /\ hid_same L S ms (advance_past_svc (apply_effect ms (effs i)))).
    { exists (fun i => match materialize_model_accesses mo (syscall_effect_accesses (effs i)) with Some m => m | None => mo end).
      intros i. destruct (Hstep i) as (mo' & E & H1 & H2 & H3). rewrite E. auto. }
    destruct Hch as (f & Hf).
    (* the node, over segs ++ tail *)
    assert (Hnode : node_ok (segs ++ tail) (mkCfg ms mo) (wr_index bs)
                      (fun i => map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) bs))
                      (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (f i))).
    { apply (node_family_mat (segs ++ tail) ms mo (getr regs 17) (wr_index bs) effs (fun _ => mo) f
               (fun i => map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) bs)) _ (lzok_halted Hok1) eq_refl Hchk).
      + intros [k Hk']. exists k. split; [exact Hk'|reflexivity].
      + intros i0. apply not_spurious_none. rewrite in_sysno_si, Hno. apply injected_arm_none_66.
      + intros o (k & Hk' & ->). exists (exist _ k Hk'). reflexivity.
      + intros _. exact (lzok_halted Hok1).
      + intros i. exact (proj1 (Hf i)). }
    pose proof Hnode as Hst. destruct Hst as [Hst _].
    apply (rz_node (segs ++ tail) (mkCfg ms mo) (wr_index bs)
             (fun i => map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) bs))
             (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (f i))
             (fun i => T (proj1_sig i)) (wr_full bs Hnb)).
    - exact Hnode.
    - exact (writev_rob (segs ++ tail) ms (getr regs 17) mo fd iov iovs bss eq_refl eq_refl Hfd Hrdr Hfdr Hno H10 H11 H12
               Hcnt HarrF HbufsF Hiov Hrng Ht1 Ht30).
    - intros [k [Hk1 Hk2]]. cbn [proj1_sig]. destruct (Hf (exist _ k (conj Hk1 Hk2))) as (_ & Hs & Ho & Hh).
      cbn [proj1_sig] in Hs, Ho, Hh. apply (Hk k _ _ Hk1 Hk2 Ho Hs).
      + unfold effs. cbn [proj1_sig].
        transitivity (restrict L S (advance_past_svc (apply_effect ms (with_copyins (CA ++ iov_prefix_accesses iovs k)
                         (mkEffect (Z_to_bv 64 (Z.of_nat k)) [] []))))); [reflexivity|].
        rewrite <- (restrict_adv_ret (segs ++ tail) L S ms regs pc (restrict_mem L S mF) (getr regs 17)
                      (Z_to_bv 64 (Z.of_nat k)) (CA ++ iov_prefix_accesses iovs k)); reflexivity.
      + exact Hh.
      + (* I after the node's step *)
        exact (HI _ _ _ HIc (Hst (exist _ k (conj Hk1 Hk2)))).
  Qed.

  (* LazyFdNodes.v:959 *)
  Theorem rz_writev2_lazy_tail : forall L S Zr msF regs (pc : word) mem mo w (fd : Z) (iov b1 n1 b2 n2 : word) bs1 bs2 (T : nat -> TSet),
    fetch_word segs pc = Some w -> is_ecall w = true ->
    lzok segs L S Zr (mkCfg msF mo) ->
    I (mkCfg msF mo) ->
    restrict L S msF = mkst regs pc mem (seg_rom (segs ++ tail)) ->
    fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
    m_channel_reader mo = true ->
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
       restrict L S msF' = mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat k))) (v_addi pc 4) mem (seg_rom (segs ++ tail)) ->
       hid_same L S msF msF' ->
       I (mkCfg msF' mo') ->
       realizes (segs ++ tail) (mkCfg msF' mo') (T k)) ->
    realizes (segs ++ tail) (mkCfg msF mo)
      (t_alt (fun i : wr_index (bs1 ++ bs2) =>
         t_emit (map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) (bs1 ++ bs2))) (T (proj1_sig i)))).
  Proof using Hnx Hnw HI.
    intros L S Zr msF regs pc mem mo w fd iov b1 n1 b2 n2 bs1 bs2 T HF HE Hok HIc Hr Hfd Hrdr Hfdr H17 H10 H11 H12
           Rb1 Rn1 Rb2 Rn2 Rs1 Rs2 Hiov Hrg1 Hrg2 Ht1 Ht30 Hk.
    eapply (rz_sys_lazy_tail segs tail Hnx Hnw I HI); [exact Hok | exact HIc | exact Hr | exact HF | exact HE |].
    intros msF1 Hok1 Hr1 Hsvc1 Hhs1 HI1.
    pose proof (u64_range n1). pose proof (u64_range n2).
    replace (bs1 ++ bs2) with (concat [bs1; bs2]) in * by (cbn; rewrite app_nil_r; reflexivity).
    eapply (rz_writev_pending_lazy_tail L S Zr msF1 regs pc mem mo fd iov [(b1, n1); (b2, n2)] [bs1; bs2] T);
      [exact Hok1 | exact HI1 | exact Hr1 | exact Hsvc1 | exact Hfd | exact Hrdr | exact Hfdr | exact H17 | exact H10
      | exact H11 | exact H12
      | cbn; lia | | | cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; lia | cbn [iov_ranges_ok]; repeat split; assumption
      | cbn [iovs_total]; lia | cbn [iovs_total]; lia | ].
    - cbn [iov_array].
      replace (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned iov + 16)) + 8)) with (Z_to_bv 64 (bv_unsigned iov + 24)).
      2:{ change (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned iov + 16)) + 8)) with (at_ (at_ iov 16) 8).
          rewrite at_at. reflexivity. }
      repeat split; try assumption; lia.
    - cbn [iov_bufs]. repeat split; assumption.
    - intros k msF' mo' Hk1 Hk2 Hok' Hsame Hr' Hhs' HI'.
      apply (Hk k msF' mo' Hk1 Hk2 Hok' Hsame Hr'); [eapply hid_same_trans; eassumption | exact HI'].
  Qed.

  (* LazyFdNodes.v:1011 *)
  Theorem rz_writev1_lazy_tail : forall L S Zr msF regs (pc : word) mem mo w (fd : Z) (iov b1 n1 : word) bs1 (T : nat -> TSet),
    fetch_word segs pc = Some w -> is_ecall w = true ->
    lzok segs L S Zr (mkCfg msF mo) ->
    I (mkCfg msF mo) ->
    restrict L S msF = mkst regs pc mem (seg_rom (segs ++ tail)) ->
    fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
    m_channel_reader mo = true ->
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
       restrict L S msF' = mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat k))) (v_addi pc 4) mem (seg_rom (segs ++ tail)) ->
       hid_same L S msF msF' ->
       I (mkCfg msF' mo') ->
       realizes (segs ++ tail) (mkCfg msF' mo') (T k)) ->
    realizes (segs ++ tail) (mkCfg msF mo)
      (t_alt (fun i : wr_index bs1 => t_emit (map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) bs1)) (T (proj1_sig i)))).
  Proof using Hnx Hnw HI.
    intros L S Zr msF regs pc mem mo w fd iov b1 n1 bs1 T HF HE Hok HIc Hr Hfd Hrdr Hfdr H17 H10 H11 H12 Rb1 Rn1 Rs1
           Hiov Hrg1 Ht1 Ht30 Hk.
    eapply (rz_sys_lazy_tail segs tail Hnx Hnw I HI); [exact Hok | exact HIc | exact Hr | exact HF | exact HE |].
    intros msF1 Hok1 Hr1 Hsvc1 Hhs1 HI1.
    pose proof (u64_range n1).
    replace bs1 with (concat [bs1]) in Hk by (cbn; rewrite app_nil_r; reflexivity).
    replace bs1 with (concat [bs1]) by (cbn; rewrite app_nil_r; reflexivity).
    eapply (rz_writev_pending_lazy_tail L S Zr msF1 regs pc mem mo fd iov [(b1, n1)] [bs1] T);
      [exact Hok1 | exact HI1 | exact Hr1 | exact Hsvc1 | exact Hfd | exact Hrdr | exact Hfdr | exact H17 | exact H10
      | exact H11 | exact H12
      | cbn; lia | | | cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; lia | cbn [iov_ranges_ok]; repeat split; assumption
      | cbn [iovs_total]; lia | cbn [iovs_total]; lia | ].
    - cbn [iov_array]. repeat split; try assumption; lia.
    - cbn [iov_bufs]. split; [assumption | exact Logic.I].
    - intros k msF' mo' Hk1 Hk2 Hok' Hsame Hr' Hhs' HI'.
      apply (Hk k msF' mo' Hk1 Hk2 Hok' Hsame Hr'); [eapply hid_same_trans; eassumption | exact HI'].
  Qed.

  (* LazyFdNodes.v:1053 *)
  Theorem rz_writev2_wall_lazy_tail : forall L S Zr msF regs (pc : word) mem mo w (fd : Z) (iov b1 n1 b2 n2 : word) bs1 bs2 (K : TSet),
    fetch_word segs pc = Some w -> is_ecall w = true ->
    lzok segs L S Zr (mkCfg msF mo) ->
    I (mkCfg msF mo) ->
    restrict L S msF = mkst regs pc mem (seg_rom (segs ++ tail)) ->
    fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
    m_channel_reader mo = true ->
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
       restrict L S msF' = mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat k))) (v_addi pc 4) mem (seg_rom (segs ++ tail)) ->
       hid_same L S msF msF' ->
       I (mkCfg msF' mo') ->
       realizes (segs ++ tail) (mkCfg msF' mo') (t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k (bs1 ++ bs2))) K)) ->
    realizes (segs ++ tail) (mkCfg msF mo) (t_emit (map (WriteEv (Z_to_bv 64 fd)) (bs1 ++ bs2)) K).
  Proof using Hnx Hnw HI.
    intros L S Zr msF regs pc mem mo w fd iov b1 n1 b2 n2 bs1 bs2 K HF HE Hok HIc Hr Hfd Hrdr Hfdr H17 H10 H11 H12
           Rb1 Rn1 Rb2 Rn2 Rs1 Rs2 Hiov Hrg1 Hrg2 Ht1 Ht30 HK Hk.
    pose proof (rdn_length segs mem _ _ _ Rs1) as L1. pose proof (rdn_length segs mem _ _ _ Rs2) as L2.
    pose proof (u64_range n1). pose proof (u64_range n2).
    apply rz_wall; [rewrite length_app; unfold word_to_nat in L1, L2; lia | exact HK |].
    eapply (rz_writev2_lazy_tail L S Zr msF regs pc mem mo w fd iov b1 n1 b2 n2 bs1 bs2
              (fun k => t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k (bs1 ++ bs2))) K)); eassumption.
  Qed.

  (* LazyFdNodes.v:1092 *)
  Theorem rz_writev1_wall_lazy_tail : forall L S Zr msF regs (pc : word) mem mo w (fd : Z) (iov b1 n1 : word) bs1 (K : TSet),
    fetch_word segs pc = Some w -> is_ecall w = true ->
    lzok segs L S Zr (mkCfg msF mo) ->
    I (mkCfg msF mo) ->
    restrict L S msF = mkst regs pc mem (seg_rom (segs ++ tail)) ->
    fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
    m_channel_reader mo = true ->
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
       restrict L S msF' = mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat k))) (v_addi pc 4) mem (seg_rom (segs ++ tail)) ->
       hid_same L S msF msF' ->
       I (mkCfg msF' mo') ->
       realizes (segs ++ tail) (mkCfg msF' mo') (t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k bs1)) K)) ->
    realizes (segs ++ tail) (mkCfg msF mo) (t_emit (map (WriteEv (Z_to_bv 64 fd)) bs1) K).
  Proof using Hnx Hnw HI.
    intros L S Zr msF regs pc mem mo w fd iov b1 n1 bs1 K HF HE Hok HIc Hr Hfd Hrdr Hfdr H17 H10 H11 H12 Rb1 Rn1 Rs1
           Hiov Hrg1 Ht1 Ht30 HK Hk.
    pose proof (rdn_length segs mem _ _ _ Rs1) as L1. pose proof (u64_range n1).
    apply rz_wall; [unfold word_to_nat in L1; lia | exact HK |].
    eapply (rz_writev1_lazy_tail L S Zr msF regs pc mem mo w fd iov b1 n1 bs1
              (fun k => t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k bs1)) K)); eassumption.
  Qed.

  (* LazyFdNodes.v:1158 *)
  Theorem rz_writev1_zero_lazy_tail : forall L S Zr msF regs (pc : word) mem mo w (fd : Z) (iov b1 : word) K,
    fetch_word segs pc = Some w -> is_ecall w = true ->
    lzok segs L S Zr (mkCfg msF mo) ->
    I (mkCfg msF mo) ->
    restrict L S msF = mkst regs pc mem (seg_rom (segs ++ tail)) ->
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
       restrict L S msF' = mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) mem (seg_rom (segs ++ tail)) ->
       hid_same L S msF msF' ->
       I (mkCfg msF' mo') ->
       realizes (segs ++ tail) (mkCfg msF' mo') K) ->
    realizes (segs ++ tail) (mkCfg msF mo) K.
  Proof using Hnx Hnw HI.
    intros L S Zr msF regs pc mem mo w fd iov b1 K HF HE Hok HIc Hr Hfd Hfdr H17 H10 H11 H12 Rb1 Rn1 Hiov Hb1 Hc.
    eapply (rz_sys_lazy_tail segs tail Hnx Hnw I HI); [exact Hok | exact HIc | exact Hr | exact HF | exact HE |].
    intros msF1 Hok1 Hr1 Hsvc1 Hhs1 HI1.
    destruct msF1 as [rg fr pcv svc rv fc mF rom].
    unfold restrict, restrict_by, with_mem, epend in Hr1. cbn in Hr1.
    injection Hr1 as Erg Efr Epc Esvc Erv Efc Emm Erom. subst rg fr pcv svc rv fc rom.
    change (restrict_mem_by (hiddenb L S) mF) with (restrict_mem L S mF) in Emm.
    set (ms := {| ms_regs := regs; ms_fregs := bvmap_empty; ms_pc_val := pc; ms_svc_pending := Some (getr regs 17);
                   ms_resv := None; ms_fcsr := Z_to_bv 32 0; ms_mem := mF; ms_rom := seg_rom (segs ++ tail) |}) in *.
    assert (Hno : bv_unsigned (getr regs 17) = 66%Z) by (rewrite H17; apply u64_lit; lia).
    assert (HarrV : iov_array segs (restrict_mem L S mF) iov [(b1, Z_to_bv 64 0)]).
    { rewrite Emm. cbn [iov_array]. refine (conj Rb1 (conj Rn1 (conj _ Logic.I))). rewrite u64_lit by lia. lia. }
    (* the one-entry iovec array, read in full over segs ++ tail *)
    destruct (ltW_iov_array_full L S mF iov [(b1, Z_to_bv 64 0)] (lzok_ranges Hok1) HarrV) as [Harr _].
    destruct (import_iovecs_of_array1 (segs ++ tail) ms b1 (Z_to_bv 64 0) iov eq_refl Harr Hiov
                ltac:(rewrite u64_lit by lia; lia)) as [Himp Hacc].
    eapply (rz_fd_det_lazy_tail segs tail Hnx Hnw I HI L S Zr ms mo (getr regs 17)
              (with_copyins (import_iovecs_accesses (ms_read_byte ms) iov (Z_to_bv 64 1)) (mkEffect (Z_to_bv 64 0) [] [])) mo);
      [exact Hok1 | exact HI1 | reflexivity
      | exact (writev_zero_rob segs ms (getr regs 17) mo fd iov [(b1, Z_to_bv 64 0)] eq_refl Hno Hfd Hfdr H10 H11
                 ltac:(change (ms_gpr ms 2) with (getr regs 12); rewrite H12; exact Himp)
                 ltac:(cbn [iovs_total]; rewrite u64_lit by lia; reflexivity))
      | | reflexivity | exact (lzok_halted Hok1) | | |].
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
        [exact (proj2 (rdn_restrict segs L S mF _ _ _ (lzok_ranges Hok1) Hb))
        | exact (proj2 (rdn_restrict segs L S mF _ _ _ (lzok_ranges Hok1) Hn))].
    - intros a Ha. rewrite apply_effect_ret_copyins_mem. reflexivity.
    - intros mo' Hok' Hsame Hhs HI'.
      apply (Hc _ mo' Hok' Hsame); [| eapply hid_same_trans; [exact Hhs1 | exact Hhs] | exact HI'].
      transitivity (restrict L S (advance_past_svc (apply_effect ms (with_copyins (import_iovecs_accesses (ms_read_byte ms) iov (Z_to_bv 64 1))
                       (mkEffect (Z_to_bv 64 0) [] []))))); [reflexivity|].
      rewrite <- Emm.
      rewrite <- (restrict_adv_ret (segs ++ tail) L S ms regs pc (restrict_mem L S mF) (getr regs 17) (Z_to_bv 64 0)
                    (import_iovecs_accesses (ms_read_byte ms) iov (Z_to_bv 64 1))); reflexivity.
  Qed.
End LazyTailWritev.
