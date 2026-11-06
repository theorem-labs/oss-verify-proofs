(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import base decidable list gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr NodesCfg ZBridge InitMem.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import AImages AImageFacts ExecA LazyModel NodesA ImplRzA NodesA_mm NodesA_mmW SysStepA StepA StepA2 Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import STree StrFun.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanConsts AsanSizeClass AsanState AsanLayout AsanOps AsanHoare AsanPS AsanRep AsanKern AsanClient AsanWf1 AsanWf2 AsanWf3 AsanWf4 AsanWf5 AsanWf6 AsanBudget AsanBudget2 AsanDepot AsanRepFrame AsanRepFrame2 AsanHit AsanRepHitB AsanRepCaB AsanRepX AsanFrame AsanRepFlipB.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import B_iface BF_place BF_fakestack_rep BF_kit BF_kit2 BF_poison BF_free_kit BF_qkit BF_free1 BF_free1e BF_free1c BF_free1d B_policy5 B_slack5 B_budget5 B_live B_bundle B_benv5 B_init5 B_instD5 B_balloc5 B_bpolicy5 B_rtok5 B_bevents5 B_bframe BF_alloc_iface BF_dput_iface BF_free_iface BF_tkit BF_ainv_kit BX_unreg BX_Exit BF_statics.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Zify.zify_internal_to_euclidean_division_equations ::= OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA.LiaFastA.zify_fast_euclid3.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
#[warnings="-notation-for-abbreviation"] Notation mem := (word -> option byte).
#[warnings="-notation-for-abbreviation"] Notation wz := (fun z : Z => Z_to_bv 64 z).

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import LiaA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac lia ::= LiaA.liaA.
Ltac pg := match goal with |- ?g => idtac "GOAL:"; idtac g end.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.

(* [comment removed for export] *)
Lemma rwc_split_d : forall segs m A cs1 cs2,
  rw_cells segs m A (cs1 ++ cs2) -> rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros segs m A cs1 cs2 [[WF B] W]. apply cells_wf_app in WF. destruct WF as [W1 W2].
  rewrite cells_bytes_app in B. apply bytes_at_app in B. destruct B as [B1 B2]. rewrite (cells_bytes_length _ W1) in B2.
  rewrite cells_size_app in W. destruct W as (Wa & Wb & Wr).
  split; split; try (split; assumption).
  - split; [lia|]. split; [lia|]. intros i Hi. apply Wr. lia.
  - split; [lia|]. split; [lia|]. intros i Hi. replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia. apply Wr. lia.
Qed.

(* [comment removed for export] *)
Lemma shadow_cells_join : forall m K lo k,
  (forall g, lo <= g < lo + Z.of_nat k -> exists v, rw_cells bsegs m (K + g) [C1 v]) -> (0 < k)%nat ->
  exists bs, rw_cells bsegs m (K + lo) [CB k bs].
Proof.
  intros m K lo k H Hk. revert lo H. induction k as [|k IH]; intros lo H; [lia|].
  destruct k as [|k'].
  - destruct (H lo ltac:(lia)) as [v X]. exists [v]. eapply rw_cells_recast; [exact X| cbn; auto| reflexivity| reflexivity].
  - destruct (H lo ltac:(lia)) as [v X]. destruct (IH ltac:(lia) (lo + 1) ltac:(intros g Hg; apply H; lia)) as [bs Y].
    pose proof (rwc_join_at bsegs m (K + lo) (K + (lo + 1)) [C1 v] _ X Y ltac:(cbn; lia)) as Z0.
    pose proof (StrFun.rw_cells_CB_length _ _ _ _ _ Y) as LY.
    exists (v :: bs). eapply rw_cells_recast; [exact Z0| cbn; rewrite LY; auto| reflexivity| cbn; lia].
Qed.

(* [comment removed for export] *)
Lemma live_block_chunk : forall E (P : list Z) (D : list batch) s blo bsz, AWf E P D s -> In (blo, bsz) (live_blocks s) ->
  exists cm aid, as_chunks s !! (blo - 16) = Some cm /\ cm_user_beg cm = blo /\ cm_n cm = bsz /\ cm_state cm = CAllocated aid.
Proof.
  intros E P D s blo bsz WF Hin. unfold live_blocks, chunk_list in Hin.
  apply in_map_iff in Hin. destruct Hin as ([k cm] & E1 & Hin). cbn in E1. injection E1 as E2 E3.
  apply filter_In in Hin. destruct Hin as [Hin AL]. cbn in AL.
  apply (proj2 (list_elem_of_In _ _)) in Hin. apply elem_of_map_to_list in Hin.
  pose proof (chunk_user_in_block E P D s k cm WF Hin) as (_ & _ & EK). unfold user_lo, kChunkHeaderSize in EK.
  destruct (cm_state cm) as [aid|i j] eqn:ST; [| discriminate].
  exists cm, aid. rewrite <- E2, <- EK. split; [exact Hin|]. split; [reflexivity|]. split; [exact E3| exact ST].
Qed.

(* [comment removed for export] *)
Lemma le4_mod32 : forall x, le4 (Z_to_bv 64 (x mod 2^32)) = le4 (Z_to_bv 64 x).
Proof.
  intros x. unfold le4. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^32 * 2^32).
  rewrite (Z.mod_small (x mod 2^32) (2^32 * 2^32)) by (pose proof (Z.mod_pos_bound x (2^32)); lia).
  rewrite Z.rem_mul_r by lia.
  set (q := x / 2^32). set (r := x mod 2^32). pose proof (Z.mod_pos_bound x (2^32) ltac:(lia)) as R. fold r in R.
  cbn [Z_to_le_bytes]. rewrite !Z.shiftr_div_pow2 by lia. change (2^8) with 256. change (2^32) with 4294967296 in *.
  repeat (apply f_equal2; [apply bv_eq; rewrite !Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 8) with 256; Z.div_mod_to_equations; lia|]). reflexivity.
Qed.
Lemma rw_cells_C4_mod32 : forall m A l1 l2 x,
  rw_cells bsegs m A (l1 ++ C4 (Z_to_bv 64 (x mod 2^32)) :: l2) <-> rw_cells bsegs m A (l1 ++ C4 (Z_to_bv 64 x) :: l2).
Proof.
  intros m A l1 l2 x.
  assert (E : cells_bytes (l1 ++ C4 (Z_to_bv 64 (x mod 2^32)) :: l2) = cells_bytes (l1 ++ C4 (Z_to_bv 64 x) :: l2)).
  { rewrite !cells_bytes_app. cbn [cells_bytes cbytes]. rewrite le4_mod32. reflexivity. }
  assert (W : forall y, cells_wf (l1 ++ C4 y :: l2) <-> cells_wf l1 /\ cells_wf l2).
  { intros y. rewrite cells_wf_app. cbn. tauto. }
  unfold rw_cells, cells_at. rewrite E, !cells_size_app. cbn [cells_size csize]. rewrite (W (Z_to_bv 64 (x mod 2^32))), (W (Z_to_bv 64 x)). tauto.
Qed.

(* [comment removed for export] *)
Lemma wr_at_C8 : forall m a, wr_at bsegs m a 8 -> exists w, rw_cells bsegs m a [C8 w].
Proof.
  intros m a WR. destruct (wr_at_bytes m a 8 WR ltac:(lia)) as (bs & L & B).
  exists (le_bytes_to_word bs). split; [split|].
  - cbn. tauto.
  - cbn [cells_bytes cbytes]. rewrite app_nil_r, le8_of_bytes by exact L. exact B.
  - cbn. exact WR.
Qed.

(* [comment removed for export] *)
Lemma freed_chunk_facts : forall E s mo m p n,
  let a := aps_alloc s in
  ARep bsegs E (DepotR bsegs E) a m -> AWf E [] [] a -> AKern E a mo ->
  fst (ae_img E) = 0x10000 -> 0x5f3000 <= snd (ae_img E) ->
  In (p, n) (live_blocks a) ->
  exists cm aid b1,
     as_chunks a !! (p - 16) = Some cm /\ cm_user_beg cm = p /\ cm_n cm = n /\ cm_state cm = CAllocated aid /\ 1 <= aid /\ 1 <= n < 2^40
  /\ 0 <= b1 < 256 /\ Z.land b1 127 = kHeaderByte1
  /\ rw_cells bsegs m (p - 16) [C1 (Z_to_bv 8 kChunkAllocated); C1 (Z_to_bv 8 b1); C2 (wz (n / 2^32)); C4 (wz n); C8 (wz aid)]
  /\ (exists uw, rw_cells bsegs m p [C8 uw])
  /\ 0x603000 <= p - 16 /\ p + rounded n <= alloc_ceiling /\ (p + rounded n <= kLowAppEnd \/ kHighMemBeg <= p - 16) /\ p mod 16 = 0
  /\ (p + rounded n <= ae_thread E \/ ae_thread E + 4096 <= p - 16)
  /\ (p + rounded n <= ae_iarena E \/ ae_iarena E + kIArenaLen <= p - 16)
  /\ ((exists c, 1 <= c <= kLargestClassID /\ region_beg (ae_space_beg E) c <= p - 16
                 /\ p + rounded n <= region_beg (ae_space_beg E) c + rg_mapped_user (get_region a c))
      \/ (exists sc, In sc (as_sec a) /\ sc_map_beg sc <= p - 16 /\ p + rounded n <= sc_map_beg sc + sc_map_size sc)).
Proof.
  intros E s mo m p n. cbv zeta. intros REP WF K EI1 EI2 Hin. pose proof ceil_range as CR.
  destruct (live_block_chunk E [] [] _ p n WF Hin) as (cm & aid & Hcm & HA & Hn & Hst).
  pose proof (chunk_user_in_block _ _ _ _ _ _ WF Hcm) as (U1 & U2 & U3).
  pose proof (chunk_user_aligned _ _ _ _ _ _ WF Hcm) as UA.
  pose proof (chunk_block_committed _ _ _ _ _ _ WF Hcm) as BC.
  pose proof WF as WF0. destruct WF as (WE & WR & WC & [WK _] & WQ & WS & WD).
  destruct (WK _ _ Hcm) as (ECB & KN & ERZ0 & KP & KS). rewrite Hst in KS.
  (* [comment removed for export] *)
  pose proof REP as (Rins & Rri & Rrm & Rthr & Rsec & Rch & Rbat & Rdep & Rglob & Rsh).
  destruct (Rch _ _ Hcm) as [_ ((b1 & HB1 & HDR) & _ & _)]. rewrite Hst in HDR. cbn [hdr_state hdr_alloc_id] in HDR. rewrite <- ECB, Hn in HDR.
  exists cm, aid, (b1 mod 256).
  split; [exact Hcm|]. split; [exact HA|]. split; [exact Hn|]. split; [exact Hst|]. split; [exact KS|]. split; [rewrite <- Hn; exact KN|].
  split; [apply Z.mod_pos_bound; lia|].
  split. { rewrite <- HB1. rewrite <- (Z.land_ones b1 8) by lia. rewrite <- Z.land_assoc. reflexivity. }
  split. { replace (Z_to_bv 8 (b1 mod 256)) with (Z_to_bv 8 b1); [exact HDR|]. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. rewrite Z.mod_mod by lia. reflexivity. }
  unfold user_lo, user_hi, blk_lo in *. rewrite HA, Hn in *.
  pose proof (ak_resv_geom _ _ _ K) as (G1 & G2 & G3).
  pose proof (wf_env_resv _ WE) as (WE2 & WE3 & WE4 & WE5 & _). pose proof (wf_env_img _ WE) as (WE29 & WE30 & WE31).
  pose proof (wf_env_thread _ WE) as (WT1 & WT2 & WT3 & WT4 & _). pose proof (wf_env_iarena _ WE) as (WI1 & WI2 & WI3 & WI4 & _).
  rewrite kHighMemBeg_val in *. rewrite kLowAppEnd_val in *. unfold blk_hi in *.
  change kSpaceSize with 137438953472 in *. change kResvLen with 137439023104 in *. change kPageSize with 4096 in *.
  (* [comment removed for export] *)
  pose proof (rounded_ge n) as (RG1 & _). pose proof (rz_size_pos n) as RZP.
  assert (UBR : p = cm_alloc_beg cm + rz_size n) by (rewrite <- HA; unfold cm_user_beg, rz_size; rewrite ERZ0; reflexivity).
  destruct (cm_prim cm) as [c|].
  - (* [comment removed for export] *)
    destruct BC as (Hc & B1 & B2). destruct KP as (FP & Ec & _).
    assert (N64 : 0 <= n <= 64512) by (pose proof (proj1 (from_primary_iff n ltac:(lia))) as X; specialize (X FP); lia).
    pose proof (malloc_class_ok n N64) as [_ NEEDc]. rewrite <- Ec in NEEDc. unfold needed1 in NEEDc.
    destruct WR as [_ WR]. destruct (WR c Hc) as (R1 & R2 & R3 & _).
    destruct (Rrm c ltac:(unfold kNumClasses; unfold kLargestClassID in Hc; lia)) as [WRc _]. cbv zeta in WRc.
    unfold region_of, region_beg in R1, R2, R3, WRc, B1, B2. fold (get_region (aps_alloc s) c) in R1, R2, R3, WRc, B1, B2.
    set (MUc := rg_mapped_user (get_region (aps_alloc s) c)) in *.
    change kRegionSize with 4294967296 in *. change kFreeArrayOffset with 3758096384 in R3. change kLargestClassID with 30 in Hc.
    assert (c * 4294967296 <= 30 * 4294967296) by (clear -Hc; lia).   (* [comment removed for export] *)
    split. { apply wr_at_C8. eapply (wr_at_sub bsegs m _ _ p 8 WRc); lia. }
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
    left. exists c. unfold region_beg. change kRegionSize with 4294967296. change kLargestClassID with 30. repeat split; lia.
  - (* [comment removed for export] *)
    destruct KP as (FP & sc & Hsc & AB0 & MS0 & ND0). clear BC.
    pose proof (map_size_facts n) as (_ & MSN & _). rewrite <- MS0 in MSN. unfold needed in MSN. rewrite FP in MSN. unfold needed1 in MSN.
    destruct WS as (_ & _ & WS3 & _). destruct (WS3 sc Hsc) as (M1 & M2 & M3 & M4 & M5 & M6 & M7).
    assert (BIG : 64512 < n).
    { destruct (Z.le_gt_cases n 64512) as [LE|GT]; [| exact GT].
      exfalso. apply (proj2 (from_primary_iff n ltac:(lia))) in LE. rewrite LE in FP. discriminate. }
    pose proof (M7 _ WE29) as IMS. rewrite EI1 in IMS. cbn [fst snd] in IMS.
    pose proof (M7 _ WT1) as TMS. pose proof (M7 _ WI1) as AMS. cbn [fst snd] in TMS, AMS.
    unfold app_mem in M2. rewrite kHighMemBeg_val, kLowAppEnd_val in M2.
    destruct Rsec as [_ RS].
    assert (WRs : wr_at bsegs m (sc_map_beg sc) (sc_map_size sc)).
    { destruct (In_nth_error _ _ Hsc) as [i Hi]. exact (proj2 (RS i sc Hi)). }
    rewrite ?Hn, <- ?MS0 in U2. unfold kPageSize in MSN.
    split. { apply wr_at_C8. eapply (wr_at_sub bsegs m _ _ p 8 WRs); clear -U1 U2 AB0 MSN RG1 RZP UBR M4; lia. }
    generalize Hsc. clear -U1 U2 AB0 MSN RG1 RZP UBR M2 M3 M4 BIG IMS TMS AMS EI2 UA CR KN. intros Hsc.
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
    right. exists sc. repeat split; [exact Hsc| lia| lia].
Qed.

Section DeallocT.
Variable E0 : aenv.
Variable FSB0 : Z.
Variable HR0 : list (Z * Z).
Variables L0 RES0 : list (word * word).
Variable EB0 : Z.
Variable PL0 : fs_plumb.
Hypothesis HR0_ok : Forall (fun iv => fst iv <= snd iv) HR0 /\ A0_pages HR0 <= 8192.
Hypothesis EB0_ok : 0 <= EB0 <= 2^32.
Hypothesis ENV_depot : zlen (ae_keys0 E0) <= 1000 /\ 0 <= ae_frames0 E0 <= 4096.
Hypothesis ENV0 : env0_ok5 E0.
Hypothesis PL0OK : pl0_ok5 E0 PL0.
Hypothesis L0OK : l0_ok5 E0 L0 RES0.
(* [comment removed for export] *)
Hypothesis DPUT : depot_put_srz_stmt E0 FSB0 HR0 L0 RES0 EB0.

#[local] Notation RTOKc := (RTOK E0 FSB0 HR0 L0 RES0 EB0).
#[local] Notation ATOKc := (ATOK E0 FSB0 HR0 L0 RES0 EB0).
#[local] Notation AINVc := (AINV E0 FSB0 PL0).
#[local] Notation aSc := (B_bundle.aS E0 FSB0 HR0).
#[local] Notation aNc := (B_bundle.aN E0 FSB0 HR0).
#[local] Notation aEBc := (B_bundle.aEB EB0).
#[local] Notation SB := (ae_space_beg E0).
#[local] Notation T := (ae_thread E0).
#[local] Notation CTX := (fp_ctx PL0).
#[local] Notation INST := 0xaaf58.

(* [comment removed for export] *)
Definition PP (s1 : aps) (mo1 : Model) : acc -> Prop := fun x => acc_ok (m_vm_lazy mo1) (aSc s1) x.
Lemma PP_KIP : forall s1 mo1 R R', ATOKc R R' s1 mo1 -> KIP (aSc s1) (aNc s1) (aEBc s1) (PP s1 mo1) mo1.
Proof. intros s1 mo1 R R' T1. split; [exact (ATOK_KIA _ _ _ _ _ _ _ _ _ _ T1)| intros x Hx; exact Hx]. Qed.

Lemma sA_self' : forall s, sA (aps_alloc s) s = s.
Proof. intros s. destruct s; reflexivity. Qed.
Lemma aps_alloc_sA' : forall a s, aps_alloc (sA a s) = a.
Proof. intros a s. destruct s; reflexivity. Qed.

(* [comment removed for export] *)
Lemma PP_zero : forall s1 mo1 w, PP s1 mo1 (w, 0%nat).
Proof.
  intros s1 mo1 w. unfold PP. right. split.
  - unfold acc_nowrap. cbn [fst snd]. pose proof (bv_unsigned_in_range _ w) as R. change (bv_modulus 64) with (2^64) in R. lia.
  - intros k Hk. cbn in Hk. lia.
Qed.
Lemma EPOL : forall s1 mo1 a k, POL E0 FSB0 HR0 s1 mo1 a k = PP s1 mo1 (Z_to_bv 64 a, k). Proof. intros; reflexivity. Qed.

(* [comment removed for export] *)
Lemma dfp_cases : forall (a : astate) mo z,
  ae_ic E0 = both_ic -> AKern E0 a mo -> AWf E0 [] [] a ->
  fst (ae_img E0) = 0x10000 -> 0x5f3000 <= snd (ae_img E0) ->
  DepotFPd E0 a z ->
     (0x180488 <= z < 0x5d04a8)
  \/ (exists b len, b <= z < b + len /\ 0x603000 <= b /\ b + len <= alloc_ceiling /\ (b + len <= kLowAppEnd \/ kHighMemBeg <= b)
        /\ (b + len <= ae_resv_beg E0 \/ ae_resv_beg E0 + kResvLen <= b)
        /\ (forall sc, In sc (as_sec a) -> b + len <= sc_map_beg sc \/ sc_map_beg sc + sc_map_size sc <= b)
        /\ (b + len <= T \/ T + 4096 <= b)
        /\ (b + len <= ae_iarena E0 \/ ae_iarena E0 + kIArenaLen <= b)).
Proof.
  intros a mo z IC0 K WF EI1 EI2 D. pose proof ceil_range as CR. rewrite kHighMemBeg_val, kLowAppEnd_val.
  pose proof ENV0 as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & _ & _ & _ & _ & _ & _ & _ & TDN & DNP).
  pose proof PL0OK as (_ & _ & TR & _). pose proof TR as (TR1 & TR2 & TR3 & TR4 & TR5 & TR6 & TR7 & TR8).
  pose proof WF as (WE & _ & _ & _ & _ & WS & _). destruct WS as (_ & _ & WS3 & _).
  pose proof (wf_env_thread _ WE) as (WT1 & _). pose proof (wf_env_iarena _ WE) as (WI1 & _). pose proof (wf_env_img _ WE) as (WE29 & _).
  pose proof (ak_store_sep _ _ _ K) as (S1 & S2 & S3 & S4 & S5).
  assert (SECR : forall sc r, In sc (as_sec a) -> In r (ae_reserved E0) -> sc_map_beg sc + sc_map_size sc <= fst r \/ fst r + snd r <= sc_map_beg sc).
  { intros sc r Hsc Hr. destruct (WS3 sc Hsc) as (_ & _ & _ & _ & _ & _ & RSV). exact (RSV _ Hr). }
  unfold placed, A_IMG_END, A_LOWAPP_END, A_HIGH_BEG in N3, N4.
  change kDepotNodeBlockBytes with 1048576 in *. change kStoreBlockBytes with 8388608 in *. change kPageSize with 4096 in *.
  destruct D as [ST|[(b & Hb & R)|(b & Hb & R)]].
  - left. destruct ST as (r & Hr & R). rewrite IC0 in Hr. cbn [aic_theDepot aic_stackStore both_ic] in Hr.
    unfold kDepotStaticBytes, kStoreStaticBytes in Hr. destruct Hr as [<-|[<-|[]]]; cbn [fst snd] in R; clear -R; lia.
  - right. unfold node_blocks in Hb. destruct Hb as [<-|Hb].
    + exists (ae_depot_nodes E0), 1048576. split; [exact R|]. split; [clear -N3; lia|]. split; [clear -N3; lia|]. split; [clear -N3; lia|]. split; [exact N7|].
      split; [intros sc Hsc; destruct (SECR sc _ Hsc N1) as [X|X]; cbn [fst snd] in X; clear -X; lia|]. split; [clear -TDN; lia| exact N10].
    + destruct (ak_blocks_sep _ _ _ K b 1048576 (or_introl (conj Hb eq_refl))) as (B1 & B2 & _ & B3 & B4 & B5).
      pose proof (B5 _ WE29) as BI. rewrite EI1 in BI. cbn [fst snd] in BI. pose proof (B5 _ WT1) as BT. pose proof (B5 _ WI1) as BA. cbn [fst snd] in BT, BA.
      unfold app_mem in B1. rewrite kHighMemBeg_val, kLowAppEnd_val in B1.
      exists b, 1048576. split; [exact R|]. split; [clear -R B1 BI EI2; lia|]. split; [exact B2|]. split; [clear -B1; lia|]. split; [exact B3|]. split; [exact B4|]. split; [exact BT| exact BA].
  - right. unfold store_blocks in Hb. destruct Hb as [<-|Hb].
    + exists (ae_store_blk E0), 8388608. split; [exact R|]. split; [clear -N4; lia|]. split; [clear -N4; lia|]. split; [clear -N4; lia|]. split; [exact S1|].
      split; [exact S2|]. split; [clear -S3; lia| exact N11].
    + destruct (ak_blocks_sep _ _ _ K b 8388608 (or_intror (conj Hb eq_refl))) as (B1 & B2 & _ & B3 & B4 & B5).
      pose proof (B5 _ WE29) as BI. rewrite EI1 in BI. cbn [fst snd] in BI. pose proof (B5 _ WT1) as BT. pose proof (B5 _ WI1) as BA. cbn [fst snd] in BT, BA.
      unfold app_mem in B1. rewrite kHighMemBeg_val, kLowAppEnd_val in B1.
      exists b, 8388608. split; [exact R|]. split; [clear -R B1 BI EI2; lia|]. split; [exact B2|]. split; [clear -B1; lia|]. split; [exact B3|]. split; [exact B4|]. split; [exact BT| exact BA].
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition denter_post (s : aps) (mo : Model) (m : mem) (usp lo cb B A len : Z) (ws : list word)
    (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (K : TSet) : Prop :=
  forall (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m1 : mem) (mo1 : Model) (cm : chunkmeta) (b1 aid : Z),
  let a := aps_alloc s in let n := cm_n cm in
  as_chunks a !! cb = Some cm -> cm_state cm = CAllocated aid -> cm_user_beg cm = cb + 16 -> Z.land b1 127 = kHeaderByte1 -> 0 <= b1 < 256 ->
  magree mo mo1 -> KIA (aSc s) (aNc s) (aEBc s) mo1 ->
  mem_inv bsegs m1 -> stk bsegs m1 lo (usp - 48) -> wmono bsegs m m1 ->
  munch [(usp - 96, usp); (cb, cb + 4); (cb + 16, cb + 24); (T + 2824, T + 2840)] m m1 ->
  rw_cells bsegs m1 (usp - 48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells bsegs m1 cb [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (wz (n / 2^32)); C4 (wz n); C8 (wz aid)] ->
  rw_cells bsegs m1 (cb + 16) [C8 (wz kInvalidTidShifted)] ->
  rw_cells bsegs m1 (T + 2824) [C8 (wz (ts_frees (as_ts a) + 1)); C8 (wz (ts_freed (as_ts a) + n))] ->
  rw_cells bsegs m1 B [C8 (wz A); C4 (wz len); C4 (wz 0)] -> u64arr bsegs m1 A ws ->
  realizes_cfg acfg bsegs
    (mkCfg (MS (mkR (wz 0x36bf8) (wz (usp - 48)) gp tp t0 t1 t2 (wz cb) (wz B) (wz A) (wz len) (wz A) (wz CTX) a4 a5 a6 a7
                    (wz INST) (wz 0) (wz T) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz A_DEPOT_PUT) fc None m1 (seg_rom bsegs)) mo1) K.

Lemma dealloc_enter :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : aps)
         (p n lo B A len C C' : Z) (ws : list word) (K : TSet),
  let a := aps_alloc s in let usp := bv_unsigned sp in
  RTOKc C C' s mo -> AINVc a m mo -> dput_mutexes m -> In (p, n) (live_blocks a) ->
  stk bsegs m lo usp -> alloc_ceiling <= lo -> lo <= usp - K_FREE -> usp mod 16 = 0 -> tp = wz 0x5e1550 ->
  usp <= B -> B + 16 <= A -> A + 8 * zlen ws < 2^47 ->
  rw_cells bsegs m B [C8 (wz A); C8 (wz len)] -> u64arr bsegs m A ws -> 1 <= len <= zlen ws -> zlen ws <= 30 ->
  denter_post s mo m usp lo (p - 16) B A len ws ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc K ->
  realizes_cfg acfg bsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz A_INST) (wz p) (wz 0) (wz 0) (wz B) (wz 1) a6 a7
                                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                            F (wz A_DEALLOCATE) fc None m (seg_rom bsegs)) mo) K.
Proof.
  intros until K. cbv zeta. intros TOK AIV DMX LIVE SK LOC LO SPA TP HB HBA HAW OBJ TR HLEN HWS DPOST.
  pose proof alloc_ceiling_range as CR. pose proof B_bundle.kHighMemBeg_val as KHB. pose proof kLowAppEnd_val as KLE.
  pose proof AIV as AIV0. destruct AIV as (Hrep & Hwf & Hkern & Hres & Hqb & Hdi & Hbinv & Hmi & Hrt & Hss).
  destruct (RTOK_elim _ _ _ _ _ _ _ _ _ _ TOK) as (R0 & R0' & ATK & HCR & HCR' & GR0 & GD0 & RLE).
  assert (ENV : ENVOK E0 FSB0 s) by exact (ATOK_ENVOK _ _ _ _ _ _ _ _ _ _ ATK).
  pose proof ENV as ENV'. destruct ENV' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & EE & EFS & [EI1 EI2]).
  pose proof L0OK as (LS_L0 & GS_L0 & HS_L0 & RES0_low & RES0_cover & RSVD & RSVD_pos).
  set (a := aps_alloc s) in *.
  rewrite EE in EI1, EI2.
  pose proof ENV0 as ENV0'. destruct ENV0' as (D0a & D0b & _ & _ & _ & _ & _ & _ & _ & _ & _ & IMGR & _ & _ & _ & _ & _ & IC0 & TDN & DNP).
  pose proof Hrep as (Rins & Rri & Rrm & Rthr & Rsec & Rch & Rbat & Rdep & Rglob & Rsh).
  pose proof Rthr as (Ttop & T40 & Tq & Tcache & Tcst & Tst & Tby & Tunw).
  pose proof Hwf as (WE & WR & WC & WK & WQ & WS & WD). pose proof WS as (WS1 & WS2 & WS3 & WS4 & WS5).
  pose proof (wf_env_thread _ WE) as (WT1 & WT2 & WT3 & WT4 & _). pose proof (wf_env_iarena _ WE) as (WI1 & WI2 & WI3 & WI4 & WI5).
  pose proof (wf_env_img _ WE) as (WE29 & WE30 & WE31). pose proof WE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & IMGT & _ & _ & IMGA).
  pose proof PL0OK as ((c0 & cl & CR0 & CC1 & CC2) & (d0 & dl & DR0 & DD1 & DD2) & TRr & CT & DT & CD & CIA).
  pose proof TRr as (TR1 & TR2 & _). pose proof TR2 as (Tlo & Thi & Timg & Tband). unfold A_IMG_END, A_LOWAPP_END, A_HIGH_BEG in Timg, Tband.
  pose proof (rt_misc5_fsenv _ _ _ _ Hrt) as FSE.
  assert (T8 : T mod 8 = 0) by (unfold FSEnv in FSE; decompose [and] FSE; assumption).
  pose proof Hrt as (_ & [tX XS] & _ & AMS & ATH). destruct ATH as [ATH1 ATH2].
  pose proof FSE as FSE'. unfold FSEnv in FSE'. pose proof FSE' as (_ & _ & _ & _ & _ & _ & FKI & FKEY & FTSD & FTSD0 & FCTXT & _). clear FSE'.
  pose proof Rglob as (Gfl & Gfu & Gth & Gdd & Gsh & Ghe & Gcp & Gai & Gmcs & Gps & Gdy & Ganc & Grm & Ghk & _).
  rewrite IC0 in Ghk. cbn [aic_malloc_hook_table both_ic] in Ghk.
  (* [comment removed for export] *)
  destruct (freed_chunk_facts E0 s mo m p n Hrep Hwf Hkern EI1 EI2 LIVE)
    as (cm & aid & b1 & Hcm & UB & Ecn & ST & AID1 & N40 & HB1 & HB1' & HDRb & [uw UW] & CB0 & CBC & CBB & P16 & CBT & CBI & CBLOC).
  set (cb := p - 16) in *. pose proof (rounded_ge n) as (RG1 & RG2 & RG3).
  set (nhi := n / 2^32). set (nlo := n mod 2^32).
  assert (HNHI : 0 <= nhi < 256) by (subst nhi; clear -N40; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  assert (HNLO : 0 <= nlo < 2^32) by (subst nlo; clear; apply Z.mod_pos_bound; lia).
  assert (En : n = nhi * 2^32 + nlo) by (subst nhi nlo; clear -N40; rewrite Z.mul_comm; apply Z_div_mod_eq_full).
  (* [comment removed for export] *)
  rewrite En in HDRb. fold nhi in HDRb.
  assert (HDR : rw_cells bsegs m cb [C4 (wz (2 + 256 * (b1 + 256 * nhi))); C4 (wz nlo); C8 (wz aid)]).
  { generalize HDRb. clear -HNHI HNLO HB1. intros HDRb.
    eapply BF_free_kit.rw_cells_reshape; [| | exact HDRb]; [cbn; tauto|].
    cbn [cells_bytes cbytes map app]. unfold le4, le2, le1. rewrite !Z_to_bv_unsigned. cbn [Z_to_le_bytes map app].
    rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. change (bv_modulus 64) with (2^64).
    unfold kChunkAllocated. rewrite !Z.shiftr_div_pow2 by lia. change (2^8) with 256. rewrite ?app_nil_r.
    rewrite !(Z.mod_small _ (2^64)) by lia.
    Time (repeat (apply f_equal2; [Z.div_mod_to_equations; lia|])). reflexivity. }
  (* [comment removed for export] *)
  assert (TC : thread_cells m tp 0x6028f8 CTX T).
  { split; [exact FKI|]. split; [exact FKEY|]. split; [| split; [exact FTSD0| exact FCTXT]].
    rewrite TP. rewrite unsigned_lit by (clear; lia). exact FTSD. }
  set (ts := as_ts a) in *.
  assert (STATS : rw_cells bsegs m (T + 2824) [C8 (wz (ts_frees ts)); C8 (wz (ts_freed ts))]).
  { pose proof (BF_tkit.u64arr_cell m _ _ 3 _ Tst eq_refl) as X3. pose proof (BF_tkit.u64arr_cell m _ _ 4 _ Tst eq_refl) as X4.
    unfold kThrStats in X3, X4. cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Pos.mul Pos.add] in X3, X4.
    pose proof (rwc_join_at bsegs m _ _ _ _ X3 X4 ltac:(cbn; clear; lia)) as X. cbn [app] in X.
    replace (T + 2824) with (T + 2800 + 24) by (clear; lia). exact X. }
  assert (HK1 : rw_cells bsegs m 0x140088 [C8 (wz 0)]).
  { pose proof (BF_tkit.u64arr_cell m _ _ 1 _ Ghk eq_refl) as X1. cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Pos.mul Pos.add Z.add] in X1. exact X1. }
  (* [comment removed for export] *)
  assert (HLEN32 : 0 <= len < 2^32) by (clear -HLEN HWS; unfold zlen in *; lia).
  assert (OBJ3 : rw_cells bsegs m B [C8 (wz A); C4 (wz len); C4 (wz 0)]).
  { generalize OBJ. clear -HLEN32. intros OBJ. destruct OBJ as [[OWF OBA] OWR]. split; [split; [cbn; tauto|]|].
    - change [C8 (Z_to_bv 64 A); C4 (Z_to_bv 64 len); C4 (Z_to_bv 64 0)] with ([C8 (Z_to_bv 64 A)] ++ [C4 (Z_to_bv 64 len); C4 (Z_to_bv 64 0)]).
      rewrite cells_bytes_app. rewrite <- (c8_c4c4 len 0) by lia. replace (len + 2^32 * 0) with len by lia. exact OBA.
    - exact OWR. }
  (* [comment removed for export] *)
  assert (HC : placed_s CTX 4096).
  { unfold placed_s, A_IMG_END, A_LOWAPP_END, A_HIGH_BEG. unfold img_sep in IMGA. rewrite EI1 in IMGA. unfold app_mem in WI2. rewrite KHB, KLE in WI2.
    clear -CIA WI2 WI3 WI5 IMGA EI2 CR. repeat split; lia. }
  pose proof (resv_range_num E0 c0 cl CR0 ltac:(clear -CC1 CC2; lia)) as (CQ1 & CQ2 & CQ3 & CQ4).
  (* [comment removed for export] *)
  set (P := PP s mo).
  set (usp := bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range _ sp) as USPR. change (bv_modulus 64) with (2^64) in USPR. fold usp in USPR.
  assert (PSTK : forall y k, lo <= y -> y + Z.of_nat k <= usp -> P (Z_to_bv 64 y, k)).
  { intros y k H1 H2. unfold P. rewrite <- EPOL. apply (pol_stack' E0 FSB0 HR0 s mo Hkern WE ENV0); clear -H1 H2 LOC HAW HB HBA CR USPR; lia. }
  assert (PSTKA : forall y k, lo <= y -> y + Z.of_nat k <= A + 8 * zlen ws -> P (Z_to_bv 64 y, k)).
  { intros y k H1 H2. unfold P. rewrite <- EPOL. apply (pol_stack' E0 FSB0 HR0 s mo Hkern WE ENV0); clear -H1 H2 LOC HAW CR; lia. }
  assert (PDAT : forall y k, 0xa5000 <= y -> y + Z.of_nat k <= 0x603000 -> P (Z_to_bv 64 y, k)).
  { intros y k H1 H2. unfold P. rewrite <- EPOL. apply (pol_img' E0 FSB0 HR0 s mo Hkern WE ENV ENV0); clear -H1 H2; lia. }
  assert (PT : forall y k, T <= y -> y + Z.of_nat k <= T + 4096 -> P (Z_to_bv 64 y, k)).
  { intros y k H1 H2. unfold P. rewrite <- EPOL. apply (pol_thread' E0 FSB0 HR0 s mo Hkern WE); clear -H1 H2; lia. }
  assert (PCTX : forall y k, CTX <= y -> y + Z.of_nat k <= CTX + 160 -> P (Z_to_bv 64 y, k)).
  { intros y k H1 H2. unfold P. rewrite <- EPOL. apply (pol_resv_range' E0 FSB0 HR0 s mo Hkern c0 cl); [exact CR0| clear -H1 CC1; lia| clear -H2 CC2; lia]. }
  assert (PCH : forall y k, cb <= y -> y + Z.of_nat k <= cb + 24 -> P (Z_to_bv 64 y, k)).
  { intros y k H1 H2. destruct k as [|k']; [apply PP_zero|]. unfold P. rewrite <- EPOL.
    destruct CBLOC as [(c & Hc & L1 & L2)|(sc & Hsc & L1 & L2)].
    - apply (pol_user E0 FSB0 HR0 s mo [] [] Hkern Hwf c); [exact Hc| clear -H1 L1; lia| clear -H2 L2 RG1; subst cb; lia| clear; lia].
    - apply (pol_sec_map E0 FSB0 HR0 s mo [] [] Hkern Hwf sc); [exact Hsc| clear -H1 L1; lia| clear -H2 L2 RG1; subst cb; lia]. }
  pose proof (PP_KIP s mo R0 R0' ATK) as KIP0.
  (* [comment removed for export] *)
  assert (HT12 : 0x5d0810 <= 0x6028f8 /\ 0x6028f8 + 8 <= 0x603000) by (clear; lia).
  assert (HTPr : 0x5d0810 + 88 <= bv_unsigned tp < 0x603000) by (rewrite TP; rewrite unsigned_lit by (clear; lia); clear; lia).
  assert (HCB24 : 0x603000 <= cb /\ cb + 24 <= alloc_ceiling /\ cb mod 16 = 0) by (subst cb; clear -CB0 CBC P16 RG1; split; [lia| split; [lia| Z.div_mod_to_equations; lia]]).
  assert (HB13 : 0 <= b1 < 256 /\ Z.land b1 3 = 1).
  { split; [exact HB1|]. clear -HB1'. replace (Z.land b1 3) with (Z.land (Z.land b1 127) 3) by (rewrite <- Z.land_assoc; reflexivity).
    rewrite HB1'. reflexivity. }
  assert (HCBT : cb + 24 <= T \/ T + 4096 <= cb) by (subst cb; clear -CBT RG1; lia).
  assert (HCBC : cb + 24 <= CTX \/ CTX + 4096 <= cb) by (subst cb; clear -CBI CIA RG1; lia).
  set (DQ := fun ms' => exists (t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
        ms' = MS (mkR (wz 0x36bf8) (wz (usp - 48)) gp tp t0' t1' t2' (wz cb) (wz B) (wz A) (wz len) (wz A) (wz CTX) a4' a5' a6' a7'
                      (wz INST) (wz 0) (wz T) s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (wz A_DEPOT_PUT) fc None m' (seg_rom bsegs)
        /\ mem_inv bsegs m' /\ stk bsegs m' lo (usp - 48) /\ wmono bsegs m m'
        /\ munch [(usp - 96, usp); (cb, cb + 4); (cb + 16, cb + 24); (T + 2824, T + 2840)] m m'
        /\ rw_cells bsegs m' (usp - 48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
        /\ rw_cells bsegs m' cb [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (wz nhi); C4 (wz nlo); C8 (wz aid)]
        /\ rw_cells bsegs m' (cb + 16) [C8 (wz kInvalidTidShifted)]
        /\ rw_cells bsegs m' (T + 2824) [C8 (wz (ts_frees ts + 1)); C8 (wz (ts_freed ts + n))]
        /\ rw_cells bsegs m' B [C8 (wz A); C4 (wz len); C4 (wz 0)] /\ u64arr bsegs m' A ws /\ thread_cells m' tp 0x6028f8 CTX T).
  unfold A_INST, A_DEALLOCATE. replace (Z_to_bv 64 p) with (Z_to_bv 64 (cb + 16)) by (subst cb; f_equal; clear; lia).
  eapply (rzA_seg_cfg bsegs (aSc s) (aNc s) (aEBc s) P DQ).
  { eapply (dealloc_walk2 P ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc DQ m lo cb B b1 nhi nlo (ts_frees ts) (ts_freed ts) (wz aid) uw 0x6028f8 CTX T);
      [ exact SK | exact LOC | clear -LO; unfold K_FREE in LO; fold usp in LO; lia | clear -HAW HB HBA HWS HLEN; fold usp; unfold zlen in *; lia | exact Hmi
      | exact HCB24 | exact HB13 | exact HNHI | exact HNLO | exact HDR | subst cb; replace (p - 16 + 16) with p by (clear; lia); exact UW | exact HK1
      | exact TC | exact (proj1 HT12) | exact (proj2 HT12) | exact HC | exact TR2 | exact HTPr | exact STATS | exact HCBT | exact HCBC | exact CT
      | exact PSTK | exact PDAT | apply PCTX; clear; lia | exact PT | exact PCH | ].
    intros m1 t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' MI1 SK1 WM1 MU1 HDR1 UW1 ST1 TC1.
    assert (AG1 : forall z, 0 <= z < 2^64 -> (z + 1 <= usp - 96 \/ usp <= z) -> (z + 1 <= cb \/ cb + 24 <= z) -> (z + 1 <= T + 2824 \/ T + 2840 <= z) -> m1 (wa z) = m (wa z)).
    { intros z Z0 Z1 Z2 Z3. apply MU1. rewrite wa_unsigned by (clear -Z0; lia). cbn [outside]. fold usp. clear -Z1 Z2 Z3. repeat split; try exact I; lia. }
    unfold K_FREE in LO.
    assert (OBJ1 : rw_cells bsegs m1 B [C8 (wz A); C4 (wz len); C4 (wz 0)]).
    { eapply BF_unwind.rw_cells_agree; [| exact OBJ3]. cbn. intros z Hz. apply AG1; clear -Hz HB HBA HAW HWS LOC LO CR HCB24 Thi USPR; unfold zlen in *; lia. }
    assert (TR1' : u64arr bsegs m1 A ws).
    { eapply u64arr_agree; [| exact TR]. intros z Hz. apply AG1; clear -Hz HB HBA HAW HWS LOC LO CR HCB24 Thi USPR; unfold zlen in *; lia. }
    assert (TCTX1 : rw_cells bsegs m1 T [C8 (wz CTX)]).
    { eapply BF_unwind.rw_cells_agree; [| exact ATH1]. cbn. intros z Hz. apply AG1; clear -Hz LOC LO CR Thi Tlo HCBT USPR; lia. }
    assert (TID1 : rw_cells bsegs m1 (CTX + 8) [C4 (wz 0)]).
    { eapply BF_unwind.rw_cells_agree; [| exact ATH2]. cbn. intros z Hz. apply AG1; clear -Hz LOC LO CR CQ1 CQ2 CC1 CC2 HCBC CT USPR; lia. }
    eapply evtA_cut.
    { eapply (qchunk_front P ra sp gp tp t0' t1' t2' s0 s1 a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6' F fc m1 lo (A + 8 * zlen ws) cb B A len b1 nhi nlo (wz aid) 0x6028f8 CTX T);
        [ exact LOC | fold usp; clear -HB; lia | clear -HBA HWS HLEN; unfold zlen in *; lia | exact HAW | clear -HLEN HWS; lia | exact HCB24 | exact HNHI | exact HNLO
        | exact (proj1 HT12) | exact (proj2 HT12) | exact HC | exact TR2 | exact HTPr | exact HCBT | exact HCBC | exact CT
        | exact PSTKA | exact PDAT | exact PCTX | exact PT | exact PCH
        | exact SK1 | clear -LO; fold usp in LO; lia | exact MI1 | exact HDR1 | exact TC1 | exact TCTX1 | exact TID1 | exact OBJ1 ]. }
    intros ms2 HQ2. unfold qchunk_front_post in HQ2.
    destruct HQ2 as (m2 & -> & MU2 & WM2 & MI2 & SK2 & FR2 & HDR2 & TC2 & TCTX2 & TID2 & OBJ2).
    assert (MU12 : munch [(usp - 96, usp); (cb, cb + 4); (cb + 16, cb + 24); (T + 2824, T + 2840)] m m2).
    { eapply munch_trans; [exact MU1|]. eapply munch_weaken; [| exact MU2]. intros z Hz. cbn in Hz |- *. fold usp in Hz. clear -Hz. lia. }
    assert (AG2 : forall z, 0 <= z < 2^64 -> (z + 1 <= usp - 64 \/ usp <= z) -> m2 (wa z) = m1 (wa z)).
    { intros z Z0 Z1. apply MU2. rewrite wa_unsigned by (clear -Z0; lia). cbn [outside]. fold usp. clear -Z1. repeat split; try exact I; lia. }
    apply evtA_done. unfold DQ. exists t0', t1', t2', a4', a5', a6', a7', t3', t4', t5', t6', m2.
    split; [fold usp; unfold A_DEPOT_PUT; reflexivity|]. split; [exact MI2|]. split; [exact SK2|]. split; [exact (wmono_trans _ _ _ _ WM1 WM2)|]. split; [exact MU12|].
    split; [exact FR2|]. split; [exact HDR2|].
    split; [eapply BF_unwind.rw_cells_agree; [| exact UW1]; cbn; intros z Hz; apply AG2; clear -Hz LOC LO CR HCB24; lia|].
    split; [unfold BF_free1e.n in ST1; rewrite <- En in ST1; eapply BF_unwind.rw_cells_agree; [| exact ST1]; cbn; intros z Hz; apply AG2; clear -Hz LOC LO CR Thi Tlo; lia|].
    split; [exact OBJ2|]. split; [| exact TC2].
    eapply u64arr_agree; [| exact TR1']. intros z Hz. apply AG2; clear -Hz HB HBA HAW HWS LOC LO CR USPR; unfold zlen in *; lia. }
  { exact KIP0. }
  (* [comment removed for export] *)
  intros ms1 mo1 HQ AG1 KIP1. unfold DQ in HQ.
  destruct HQ as (t0' & t1' & t2' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> & MI1 & SK1 & WM1 & MU1 & FR1 & HDR1 & UW1 & ST1 & OBJ1 & TRA1 & TC1).
  destruct KIP1 as [KIA1 _].
  eapply (DPOST t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' m1 mo1 cm b1 aid Hcm ST ltac:(subst cb; rewrite UB; clear; lia) HB1' HB1 AG1 KIA1 MI1);
    [ fold usp; exact SK1 | exact WM1 | fold usp; exact MU1 | fold usp; exact FR1 | | exact UW1 | | exact OBJ1 | exact TRA1 ].
  - subst nhi nlo. rewrite Ecn.
    apply (proj1 (rw_cells_C4_mod32 m1 cb [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (wz (n / 2^32))] [C8 (wz aid)] n)). exact HDR1.
  - fold ts. rewrite Ecn. exact ST1.
Qed.


(* [comment removed for export] *)

(* [comment removed for export] *)
Definition FPW1 (a2 : astate) (lo usp cb n : Z) (z : Z) : Prop :=
     (lo <= z < usp) \/ DepotFPd E0 a2 z \/ (cb <= z < cb + 4) \/ (cb + 16 <= z < cb + 24) \/ (T + 2824 <= z < T + 2840)
  \/ (kShadowBase + (cb + 16) / 8 <= z < kShadowBase + (cb + 16) / 8 + (n + 7) / 8).

(* [comment removed for export] *)
Definition W15 (usp cb n : Z) : list (Z * Z) :=
  [(usp - 144, usp); (cb, cb + 4); (cb + 16, cb + 24); (T + 2824, T + 2840);
   (kShadowBase + (cb + 16) / 8, kShadowBase + (cb + 16) / 8 + (n + 7) / 8)].

(* [comment removed for export] *)
Definition QPF_post (s : aps) (mo : Model) (m : mem) (usp lo cb B A len C C' : Z) (ws : list word)
    (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (K : TSet) : Prop :=
  forall (t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 : word) (m5 : mem) (mo5 : Model) (a2 : astate) (cm : chunkmeta) (b1 aid fid : Z),
  let a := aps_alloc s in let n := cm_n cm in let l8 := (n + 7) / 8 in let SHa := kShadowBase + (cb + 16) / 8 in
  (* [comment removed for export] *)
  as_chunks a !! cb = Some cm -> cm_state cm = CAllocated aid -> cm_user_beg cm = cb + 16 -> Z.land b1 127 = kHeaderByte1 -> 0 <= b1 < 256 ->
  (* [comment removed for export] *)
  (exists fuel orc evs orc', arun fuel (depot_put E0 (bst_key len ws) (upd_ts (ts_on_free n) a)) orc = Some (a2, ONorm fid, evs, orc')) ->
  1 <= fid < 2^31 -> AWf E0 [] [] a2 -> same_alloc (upd_ts (ts_on_free n) a) a2 ->
  AKern E0 a2 mo5 -> RTOKc (C - 1) (C' - DSLACK) (sA a2 s) mo5 -> KIA (aSc (sA a2 s)) (aNc (sA a2 s)) (aEBc (sA a2 s)) mo5 ->
  m_fs mo5 = m_fs mo -> m_fds mo5 = m_fds mo -> m_tid mo5 = m_tid mo ->
  (* [comment removed for export] *)
  mem_inv bsegs m5 -> stk bsegs m5 lo (usp - 80) -> wmono bsegs m m5 ->
  (exists Wd, munch (W15 usp cb n ++ Wd) m m5 /\ Forall (dput_w_ok E0 a2 lo (usp - 48)) Wd) ->
  (forall z, 0 <= z < 2^64 -> ~ FPW1 a2 lo usp cb n z -> m5 (wa z) = m (wa z)) ->
  DepotR bsegs E0 a2 m5 -> dput_mutexes m5 ->
  rw_cells bsegs m5 (usp - 80) [C8 (wz (T + 208)); C8 (wz B); C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells bsegs m5 cb [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (wz (n / 2^32)); C4 (wz n); C8 (wz aid)] ->
  rw_cells bsegs m5 (cb + 16) [C8 (wz fid)] ->
  rw_cells bsegs m5 (T + 2824) [C8 (wz (ts_frees (as_ts a) + 1)); C8 (wz (ts_freed (as_ts a) + n))] ->
  rw_cells bsegs m5 SHa [CB (Z.to_nat l8) (repeat (Z_to_bv 8 0xfd) (Z.to_nat l8))] ->
  realizes_cfg acfg bsegs
    (mkCfg (MS (mkR (wz 0x36ebc) (wz (usp - 80)) gp tp t0 t1 t2 (wz (INST + 728)) (wz (T + 80)) (wz (T + 80)) (wz (T + 208)) (wz B) (wz cb) (wz n) a5 a6 a7
                    (wz n) (wz B) (wz (T + 208)) (wz cb) (wz 0x100000) s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x36ec8) fc None m5 (seg_rom bsegs)) mo5) K.

Theorem qput_front_srz :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : aps)
         (p n lo B A len C C' : Z) (ws : list word) (K : TSet),
  let a := aps_alloc s in let usp := bv_unsigned sp in
  K [] ->
  RTOKc C C' s mo -> 1 <= C -> FSLACK <= C' -> AINVc a m mo -> dput_mutexes m -> fbudget_pre a ->
  In (p, n) (live_blocks a) -> n <= 2^27 ->
  stk bsegs m lo usp -> alloc_ceiling <= lo -> lo <= usp - K_FREE -> usp mod 16 = 0 -> tp = wz 0x5e1550 ->
  usp <= B -> B + 16 <= A -> A + 8 * zlen ws < 2^47 ->
  rw_cells bsegs m B [C8 (wz A); C8 (wz len)] -> u64arr bsegs m A ws -> 1 <= len <= zlen ws -> zlen ws <= 30 ->
  QPF_post s mo m usp lo (p - 16) B A len C C' ws ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc K ->
  realizes_cfg acfg bsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz A_INST) (wz p) (wz 0) (wz 0) (wz B) (wz 1) a6 a7
                                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                            F (wz A_DEALLOCATE) fc None m (seg_rom bsegs)) mo) K.
Proof.
  intros until K. cbv zeta. intros KN TOK HC1 HCS AIV DMX FB LIVE N27 SK LOC LO SPA TP HB HBA HAW OBJ TR HLEN HWS QPOST.
  pose proof alloc_ceiling_range as CR. pose proof B_bundle.kHighMemBeg_val as KHB. pose proof kLowAppEnd_val as KLE.
  pose proof AIV as AIV0. destruct AIV as (Hrep & Hwf & Hkern & Hres & Hqb & Hdi & Hbinv & Hmi & Hrt & Hss).
  destruct (RTOK_elim _ _ _ _ _ _ _ _ _ _ TOK) as (R0 & R0' & ATK & HCR & HCR' & GR0 & GD0 & RLE).
  assert (ENV : ENVOK E0 FSB0 s) by exact (ATOK_ENVOK _ _ _ _ _ _ _ _ _ _ ATK).
  pose proof ENV as ENV'. destruct ENV' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & EE & EFS & [EI1 EI2]).
  set (a := aps_alloc s) in *.
  rewrite EE in EI1, EI2.
  pose proof ENV0 as ENV0'. destruct ENV0' as (D0a & D0b & _ & _ & _ & _ & _ & _ & _ & _ & _ & IMGR & _ & _ & _ & _ & _ & IC0 & TDN & DNP).
  pose proof Hrep as (Rins & Rri & Rrm & Rthr & Rsec & Rch & Rbat & Rdep & Rglob & Rsh).
  pose proof Rthr as (Ttop & T40 & Tq & Tcache & Tcst & Tst & Tby & Tunw).
  pose proof Hwf as (WE & WR & WC & WK & WQ & WS & WD).
  pose proof (wf_env_thread _ WE) as (WT1 & WT2 & WT3 & WT4 & _). pose proof (wf_env_iarena _ WE) as (WI1 & WI2 & WI3 & WI4 & WI5).
  pose proof PL0OK as ((c0 & cl & CR0 & CC1 & CC2) & (d0 & dl & DR0 & DD1 & DD2) & TRr & CT & DT & CD & CIA).
  pose proof TRr as (TR1 & TR2 & _). pose proof TR2 as (Tlo & Thi & Timg & Tband). unfold A_IMG_END, A_LOWAPP_END, A_HIGH_BEG in Timg, Tband.
  pose proof (resv_range_num E0 c0 cl CR0 ltac:(clear -CC1 CC2; lia)) as (CQ1 & CQ2 & CQ3 & CQ4).
  set (usp := bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range _ sp) as USPR. change (bv_modulus 64) with (2^64) in USPR. fold usp in USPR.
  unfold K_FREE in LO.
  (* [comment removed for export] *)
  destruct (freed_chunk_facts E0 s mo m p n Hrep Hwf Hkern EI1 EI2 LIVE)
    as (cm & aid & b1 & Hcm & UB & Ecn & ST & AID1 & N40 & HB1 & HB1' & HDRb & [uw UW] & CB0 & CBC & CBB & P16 & CBT & CBI & CBLOC).
  set (cb := p - 16) in *.
  pose proof (rounded_ge n) as (RG1 & RG2 & RG3).
  (* [comment removed for export] *)
  eapply dealloc_enter; [exact TOK| exact AIV0| exact DMX| exact LIVE| exact SK| exact LOC| unfold K_FREE; exact LO| exact SPA| exact TP| exact HB| exact HBA| exact HAW
    | exact OBJ| exact TR| exact HLEN| exact HWS|].
  unfold denter_post. fold a cb usp.
  intros t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' m1 mo1 cm' b1' aid'. cbv zeta. intros Hcm' ST' UB' HB1x HB1y AG01 KIA1 MI1 SK1 WM1 MU1 FR1 HDR1 UW1 ST1 OBJ1 TRA1.
  (* [comment removed for export] *)
  assert (Ecm : cm' = cm) by (subst cb; rewrite Hcm in Hcm'; injection Hcm'; auto). subst cm'.
  assert (Eaid : aid' = aid) by (rewrite ST in ST'; injection ST'; auto). subst aid'.
  clear HDRb HB1 HB1' b1 UW uw. rename b1' into b1. rename HB1x into HB1'. rename HB1y into HB1.
  rewrite UB in UB'. clear UB'.
  (* [comment removed for export] *)
  pose proof (magree_frame _ _ AG01) as (Ffds1 & Fvm1 & Flz1 & Ffs1 & Fh1 & Ftid1 & _).
  pose proof (RTOK_magree _ _ _ _ _ _ _ _ _ _ _ TOK AG01 KIA1) as TOK1.
  pose proof (AKern_frame _ _ _ _ Fvm1 Flz1 Hkern) as AK1.
  set (a1 := upd_ts (ts_on_free n) a).
  assert (TOK1' : RTOKc C C' (sA a1 s) mo1).
  { rewrite <- (sA_self' s) in TOK1. fold a in TOK1. eapply (RTOK_same_fp E0 FSB0 HR0 L0 RES0 EB0); [exact TOK1| repeat split; reflexivity| reflexivity| reflexivity]. }
  assert (AK1' : AKern E0 a1 mo1) by (apply (AKern_ext E0 a a1 mo1); [reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| exact AK1]).
  assert (WF1 : AWf E0 [] [] a1) by (eapply AWf_same_core; [apply same_core_upd_ts| exact Hwf]).
  pose proof FB as (BU1 & BU2 & BU3).
  destruct (AINV_dput_nums E0 FSB0 HR0 L0 RES0 EB0 PL0 EB0_ok s m mo C C' AIV0 TOK BU1 BU3 (conj (proj1 ENV_depot) (proj2 (proj2 ENV_depot)))) as (NB1 & NB2 & NB3 & NB4).
  fold a in NB1, NB2, NB3, NB4.
  (* [comment removed for export] *)
  assert (AG1f : forall z, 0 <= z < 2^64 -> (z + 1 <= usp - 96 \/ usp <= z) -> (z + 1 <= cb \/ cb + 4 <= z) -> (z + 1 <= cb + 16 \/ cb + 24 <= z) -> (z + 1 <= T + 2824 \/ T + 2840 <= z) -> m1 (wa z) = m (wa z)).
  { intros z Z0 Z1 Z2 Z2' Z3. apply MU1. rewrite wa_unsigned by (clear -Z0; lia). cbn [outside]. clear -Z1 Z2 Z2' Z3. repeat split; try exact I; lia. }
  assert (AG1 : forall z, 0 <= z < 2^64 -> (z + 1 <= usp - 96 \/ usp <= z) -> (z + 1 <= cb \/ cb + 24 <= z) -> (z + 1 <= T + 2824 \/ T + 2840 <= z) -> m1 (wa z) = m (wa z)).
  { intros z Z0 Z1 Z2 Z3. apply AG1f; [exact Z0| exact Z1| clear -Z2; lia| clear -Z2; lia| exact Z3]. }
  assert (AGimg1 : forall z, 0x10000 <= z < 0x603000 -> m1 (wa z) = m (wa z)).
  { intros z Hz. apply AG1; clear -Hz LOC LO CR CB0 Timg Tlo USPR; lia. }
  assert (DR1 : DepotR bsegs E0 a1 m1).
  { change (DepotR bsegs E0 a m1). eapply DepotR_frame; [exact Rdep| exact WM1|]. intros z Dz.
    pose proof (wa_range z) as WZ || idtac.
    destruct (dfp_cases a mo z IC0 Hkern Hwf EI1 EI2 Dz) as [ST0|(b & bl & R & B0 & B2 & BB & B3 & B4 & BT & BA)].
    - apply AGimg1. clear -ST0. lia.
    - pose proof (ak_resv_geom _ _ _ Hkern) as (G1 & G2 & G3).
      apply AG1.
      + clear -R B0 B2 CR. lia.
      + left. clear -R B2 LOC LO CR. lia.
      + destruct CBLOC as [(c & Hc & L1 & L2)|(sc & Hsc & L1 & L2)].
        * unfold region_beg in L1, L2. destruct (proj2 WR c Hc) as (R1 & R2 & R3 & _). cbv zeta in R1, R3. unfold region_of in R1, R3.
          change kSpaceSize with 137438953472 in G3. change kResvLen with 137439023104 in G3, B3. change kRegionSize with 4294967296 in L1, L2.
          change kFreeArrayOffset with 3758096384 in R3. unfold kLargestClassID in Hc.
          fold a in L2. change kPageSize with 4096 in G3. subst cb. clear -R B3 G1 G3 L1 L2 Hc R1 R3 RG1. nia.
        * pose proof (B4 sc Hsc) as X. subst cb. clear -R X L1 L2 RG1. lia.
      + subst cb. clear -R BT CBT Tlo RG1. lia. }
  Ltac agi AG H := eapply BF_unwind.rw_cells_agree; [| exact H]; cbn -[Z.add Z.mul Z.of_nat]; intros z Hz; apply AG; clear -Hz; lia.
  assert (DS1 : dput_statics m1).
  { pose proof (AINV_dput_statics E0 FSB0 PL0 IC0 a m mo AIV0) as [STm CFm]. split.
    - unfold XB_mmap_fixed.statics, XB_mmap_fixed.GOT_PAGESIZE, XB_mmap_fixed.GOT_CFLAGS, XB_mmap_fixed.GOT_PAIR, XB_mmap_fixed.V_PAGESIZE, XB_mmap_fixed.V_CFLAGS, XB_mmap_fixed.V_MMAP_LIMIT, XB_mmap_fixed.V_DPM, XB_mmap_fixed.V_ABORTFLAG in *.
      destruct STm as (S1 & S2 & S3 & S4 & S5 & S6 & S7).
      split; [agi AGimg1 S1|]. split; [agi AGimg1 S2|]. split; [agi AGimg1 S3|]. split; [agi AGimg1 S4|]. split; [agi AGimg1 S5|]. split; [agi AGimg1 S6| agi AGimg1 S7].
    - unfold XB_mmap_fixed.V_CFLAGS in *. agi AGimg1 CFm. }
  assert (DM1 : dput_mutexes m1).
  { destruct DMX as [M1x M2x]. unfold dput_mutexes, dTD, dSS in *. split; [agi AGimg1 M1x|]. intros k Hk. pose proof (M2x k Hk) as X.
    eapply BF_unwind.rw_cells_agree; [| exact X]; cbn -[Z.add Z.mul Z.of_nat]; intros z Hz; apply AGimg1; unfold kStoreBlockCount in Hk; clear -Hz Hk; lia. }
  assert (USP48 : bv_unsigned (wz (usp - 48)) = usp - 48) by (apply unsigned_lit; clear -LO LOC CR USPR; lia).
  (* [comment removed for export] *)
  eapply (DPUT (wz 0x36bf8) (wz (usp - 48)) gp tp t0' t1' t2' (wz cb) (wz B) (wz A) (wz CTX) a4' a5' a6' a7' (wz INST) (wz 0) (wz T) s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6'
            F fc m1 mo1 (sA a1 s) [] [] lo A len C C' ws K KN);
    rewrite ?aps_alloc_sA', ?USP48;
    [ exact TOK1' | exact HC1 | unfold FSLACK, DSLACK in *; clear -HCS; lia | exact AK1' | exact WF1
    | exact NB1 | exact NB2 | exact NB3 | exact NB4
    | exact DR1 | exact DM1 | exact DS1 | exact MI1 | exact SK1 | exact LOC | unfold K_DEPOT; clear -LO; lia
    | clear -SPA; unfold usp in *; Z.div_mod_to_equations; lia | clear -HB HBA; lia | exact HAW | exact TRA1 | exact HLEN | exact HWS | ].
  intros t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' m2 mo2 a2 fid DP.
  destruct DP as (SK2 & WM12 & MI2 & (Wd & MUd & FWd) & RUN & FID & DR2 & DM2 & DS2 & AK2 & TOK2 & Ffs2 & Ffds2 & Ftid2).
  rewrite ?aps_alloc_sA' in RUN, DR2, AK2.
  replace (ret_pc (Z_to_bv 64 224248)) with (Z_to_bv 64 224248) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
  (* [comment removed for export] *)
  assert (AG12 : forall z, 0 <= z < 2^64 -> (z + 1 <= lo \/ usp - 48 <= z) -> ~ DepotFPd E0 a2 z -> m2 (wa z) = m1 (wa z)).
  { intros z Z0 Z1 Z2. apply MUd. rewrite wa_unsigned by (clear -Z0; lia). apply (proj2 (outside_forall _ _)). intros lo' hi' Hin.
    pose proof (dput_w_ok_pt E0 _ _ _ _ (proj1 (Forall_forall _ _) FWd _ Hin)) as X. cbn [fst snd] in X.
    destruct X as [X|X]; [clear -X Z1; lia|]. intros C0. apply Z2. apply X. exact C0. }
  (* [comment removed for export] *)
  pose proof Hdi as (DI1 & DI2 & DI3 & DI4 & DI5 & DI6 & DI7).
  assert (DOK : depot_ok E0 a1 (bst_key len ws)).
  { split.
    - unfold bst_key, zlen. rewrite length_map, length_firstn. clear -HLEN HWS. unfold zlen in *. lia.
    - change (depot_n_ids E0 a1) with (depot_n_ids E0 a). unfold kDepotNodesPerBlock in DI5. clear -DI5 NB1. lia. }
  pose proof RUN as (fuel & orc & evs & orc' & RUNe).
  destruct (hoare_arun _ _ _ _ _ _ _ _ _ _ (depot_put_wf E0 [] [] a1 (bst_key len ws) DOK WF1) eq_refl RUNe) as (WF2 & SAME & FID1 & NID2).
  pose proof SAME as (SRg & SCa & SCi & SCh & STq & SGq & SSe & SPt).
  (* [comment removed for export] *)
  destruct (RTOK_elim _ _ _ _ _ _ _ _ _ _ TOK2) as (Q2 & Q2' & ATK2 & _).
  assert (ENV2 : ENVOK E0 FSB0 (sA a2 s)) by exact (ATOK_ENVOK _ _ _ _ _ _ _ _ _ _ ATK2).
  pose proof (proj1 WF2) as WE2.
  (* [comment removed for export] *)
  set (P2 := PP (sA a2 s) mo2).
  assert (USPR48 : lo <= usp - 48) by (clear -LO; lia).
  assert (PSTK2 : forall y k, lo <= y -> y + Z.of_nat k <= usp -> P2 (Z_to_bv 64 y, k)).
  { intros y k H1 H2. unfold P2. rewrite <- EPOL. apply (pol_stack' E0 FSB0 HR0 (sA a2 s) mo2 AK2 WE2 ENV0); clear -H1 H2 LOC HAW HB HBA CR USPR; lia. }
  assert (PDAT2 : forall y k, 0xa5000 <= y -> y + Z.of_nat k <= 0x603000 -> P2 (Z_to_bv 64 y, k)).
  { intros y k H1 H2. unfold P2. rewrite <- EPOL. apply (pol_img' E0 FSB0 HR0 (sA a2 s) mo2 AK2 WE2 ENV2 ENV0); clear -H1 H2; lia. }
  assert (PT2 : forall y k, T <= y -> y + Z.of_nat k <= T + 4096 -> P2 (Z_to_bv 64 y, k)).
  { intros y k H1 H2. unfold P2. rewrite <- EPOL. apply (pol_thread' E0 FSB0 HR0 (sA a2 s) mo2 AK2 WE2); clear -H1 H2; lia. }
  assert (PCTX2 : forall y k, CTX <= y -> y + Z.of_nat k <= CTX + 160 -> P2 (Z_to_bv 64 y, k)).
  { intros y k H1 H2. unfold P2. rewrite <- EPOL. apply (pol_resv_range' E0 FSB0 HR0 (sA a2 s) mo2 AK2 c0 cl); [exact CR0| clear -H1 CC1; lia| clear -H2 CC2; lia]. }
  assert (GR2 : forall c, get_region a2 c = get_region a c) by (intros c; unfold get_region; rewrite SRg; reflexivity).
  assert (PCH2 : forall y k, cb <= y -> y + Z.of_nat k <= cb + 24 -> P2 (Z_to_bv 64 y, k)).
  { intros y k H1 H2. destruct k as [|k']; [apply PP_zero|]. unfold P2. rewrite <- EPOL.
    destruct CBLOC as [(c & Hc & L1 & L2)|(sc & Hsc & L1 & L2)].
    - apply (pol_user E0 FSB0 HR0 (sA a2 s) mo2 [] [] AK2 WF2 c); rewrite ?aps_alloc_sA', ?GR2; [exact Hc| clear -H1 L1; lia| fold a in L2; clear -H2 L2 RG1; subst cb; lia| clear; lia].
    - apply (pol_sec_map E0 FSB0 HR0 (sA a2 s) mo2 [] [] AK2 WF2 sc); rewrite ?aps_alloc_sA', ?SSe; [exact Hsc| clear -H1 L1; lia| clear -H2 L2 RG1; subst cb; lia]. }
  pose proof (PP_KIP (sA a2 s) mo2 Q2 Q2' ATK2) as KIP2.
  (* [comment removed for export] *)
  assert (SECA : forall sc, In sc (as_sec a) -> In sc (as_sec a2)) by (intros sc Hsc; rewrite SSe; exact Hsc).
  (* [comment removed for export] *)
  assert (NDFP : forall z, (z < 0x180488 \/ 0x5d04a8 <= z) -> (z < 0x603000 \/ alloc_ceiling <= z \/ (cb <= z < cb + 24) \/ (T <= z < T + 4096)
                              \/ (0x7fff7000 <= z < 0x10007fff8000) \/ (CTX <= z < CTX + 160)) -> ~ DepotFPd E0 a2 z).
  { intros z Z1 Z2 Dz. pose proof (ak_resv_geom _ _ _ Hkern) as (G1 & G2 & G3). change kSpaceSize with 137438953472 in G3. change kPageSize with 4096 in G3. change kResvLen with 137439023104 in G3.
    destruct (dfp_cases a2 mo2 z IC0 AK2 WF2 EI1 EI2 Dz) as [ST0|(b & bl & R & B0 & B2 & BB & B3 & B4 & BT & BA)]; [clear -Z1 ST0; lia|].
    rewrite kHighMemBeg_val, kLowAppEnd_val in BB. change kResvLen with 137439023104 in B3.
    destruct Z2 as [Z2|[Z2|[Z2|[Z2|[Z2|Z2]]]]].
    - clear -R B0 Z2. lia.
    - clear -R B2 Z2. lia.
    - destruct CBLOC as [(c & Hc & L1 & L2)|(sc & Hsc & L1 & L2)].
      + unfold region_beg in L1, L2. destruct (proj2 WR c Hc) as (R1 & R2 & R3 & _). cbv zeta in R1, R3. unfold region_of in R1, R3.
        change kRegionSize with 4294967296 in L1, L2. change kFreeArrayOffset with 3758096384 in R3. unfold kLargestClassID in Hc.
        fold a in L2. subst cb. clear -R B3 G1 G3 L1 L2 Hc R1 R3 Z2 RG1. nia.
      + pose proof (B4 sc (SECA sc Hsc)) as X. subst cb. clear -R X L1 L2 Z2 RG1. lia.
    - clear -R BT Z2. lia.
    - clear -R BB Z2. lia.
    - clear -R BA CIA Z2. unfold kIArenaLen in *. lia. }
  assert (AG2 : forall z, 0 <= z < 2^64 -> (z + 1 <= lo \/ usp <= z) -> (z + 1 <= cb \/ cb + 24 <= z) -> (z + 1 <= T + 2824 \/ T + 2840 <= z) ->
                          (z < 0x180488 \/ 0x5d04a8 <= z) -> (z < 0x603000 \/ alloc_ceiling <= z \/ (T <= z < T + 4096) \/ (0x7fff7000 <= z < 0x10007fff8000) \/ (CTX <= z < CTX + 160)) ->
                          m2 (wa z) = m (wa z)).
  { intros z Z0 Z1 Z2 Z3 Z4 Z5. rewrite (AG12 z Z0); [| clear -Z1 LO; lia| apply NDFP; [exact Z4| clear -Z5; tauto]].
    apply AG1; [exact Z0| clear -Z1 LO; lia| exact Z2| exact Z3]. }
  assert (AGimg2 : forall z, 0xa5000 <= z < 0x140810 -> m2 (wa z) = m (wa z)).
  { intros z Hz. apply AG2; clear -Hz LOC LO CR CB0 Timg Tlo USPR; lia. }
  assert (FR2 : rw_cells bsegs m2 (usp - 48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { eapply BF_unwind.rw_cells_agree; [| exact FR1]. cbn -[Z.add Z.mul Z.of_nat Z.sub]. intros z Hz. apply AG12; [clear -Hz LO LOC CR USPR; lia| clear -Hz; lia|].
    apply NDFP; clear -Hz LO LOC CR USPR; lia. }
  assert (HDR2 : rw_cells bsegs m2 cb [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (wz (cm_n cm / 2^32)); C4 (wz (cm_n cm)); C8 (wz aid)]).
  { eapply BF_unwind.rw_cells_agree; [| exact HDR1]. cbn -[Z.add Z.mul Z.of_nat Z.sub Z.div Z.pow]. intros z Hz. apply AG12; [clear -Hz LO LOC CR CB0 CBC RG1; lia| clear -Hz LO LOC CBC CR RG1; lia|].
    apply NDFP; clear -Hz CB0 CBC RG1; lia. }
  assert (UW2 : rw_cells bsegs m2 (cb + 16) [C8 (wz kInvalidTidShifted)]).
  { eapply BF_unwind.rw_cells_agree; [| exact UW1]. cbn -[Z.add Z.mul Z.of_nat Z.sub]. intros z Hz. apply AG12; [clear -Hz LO LOC CR CB0 CBC RG1; lia| clear -Hz LO LOC CBC CR RG1; lia|].
    apply NDFP; clear -Hz CB0 CBC RG1; lia. }
  (* [comment removed for export] *)
  pose proof Hrt as (_ & [tX XS] & _ & AMS & ATH). destruct ATH as [ATH1 ATH2].
  assert (US : unreg_statics m) by (unfold exit_statics in XS; decompose [and] XS; assumption). unreg_statics_open US.
  pose proof Rglob as (Gfl & Gfu & Gth & Gdd & Gsh & Ghe & Gcp & Gai & Gmcs & Gps & Gdy & Ganc & Grm & Ghk & _).
  rewrite IC0 in Ghe, Grm, Gfl. cbn [aic_kHighMemEnd aic_REAL_memcpy_var aic_musl_memcpy aic_musl_memset aic_asan_flags both_ic] in Ghe, Grm, Gfl.
  assert (PGm : poison_globals m).
  { unfold poison_globals. split.
    { pose proof (rwc_join_at bsegs m _ _ _ _ GHE GRSP ltac:(reflexivity)) as X4.
      pose proof (rwc_join_at bsegs m _ _ _ _ GME X4 ltac:(reflexivity)) as X3.
      pose proof (rwc_join_at bsegs m _ _ _ _ GMB X3 ltac:(reflexivity)) as X2.
      pose proof (rwc_join_at bsegs m _ _ _ _ GSBP X2 ltac:(reflexivity)) as X1. cbn [app] in X1. exact X1. }
    split; [exact GCF|]. split; [exact GSB|]. split; [exact Ghe|]. split; [exact Grm|]. split; [exact GCPM| exact GTHR]. }
  assert (PG2 : poison_globals m2) by (apply (poison_globals_agree m m2 PGm); intros z Hz; apply AGimg2; exact Hz).
  assert (GFL2 : rw_cells bsegs m2 0xa5598 [C8 (wz 0xabdb8)]) by (agi AGimg2 GFL).
  pose proof Rins as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & _).
  unfold ae_instance in I8. rewrite IC0 in I8. cbn [aic_instance both_ic kInsQuarantine Z.add] in I8.
  assert (QMAX2 : rw_cells bsegs m2 0xab270 [C8 (wz 0x10000000); C8 (wz kQuarantineMin); C8 (wz 0x100000)]).
  { unfold kQuarantineMax, kThreadQuarantineMax in I8. agi AGimg2 I8. }
  (* [comment removed for export] *)
  assert (FFS2 : rw_cells bsegs m2 0xabde8 [C4 (wz 0)]).
  { assert (Gfl2 : u8arr bsegs m2 0xabdb8 (map AsanRep.zb (asan_flags_bytes both_ic))).
    { eapply u8arr_agree; [| exact Gfl]. intros z Hz. apply AGimg2. rewrite length_map in Hz. cbn [length asan_flags_bytes] in Hz. clear -Hz. lia. }
    pose proof (rw_cells_of_u8arr bsegs m2 _ _ Gfl2) as X. rewrite length_map in X. cbn [length asan_flags_bytes] in X.
    apply (rw_cells_split_CB bsegs m2 0xabdb8 [] _ _ [] [48; 4; 76]%nat) in X; [| reflexivity]. cbn [mk_CB_cells app firstn skipn map asan_flags_bytes length] in X.
    apply (rwc_split bsegs m2 _ [_] [_; _]) in X. destruct X as [_ X]. apply (rwc_split bsegs m2 _ [_] [_]) in X. destruct X as [X _]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Z.add] in X.
    eapply BF_free_kit.rw_cells_reshape; [| | exact X]; [split; [reflexivity| exact I]| vm_compute; reflexivity]. }
  (* [comment removed for export] *)
  set (l8 := (n + 7) / 8). set (SHa := kShadowBase + (cb + 16) / 8).
  assert (HL8 : 1 <= l8 /\ 8 * (l8 - 1) < n /\ 8 * l8 < n + 8) by (subst l8; clear -N40; Z.div_mod_to_equations; lia).
  assert (G8 : 8 * ((cb + 16) / 8) = cb + 16) by (subst cb; clear -P16; Z.div_mod_to_equations; lia).
  assert (SHm : exists shj, rw_cells bsegs m SHa [CB (Z.to_nat l8) shj]).
  { subst SHa. apply shadow_cells_join; [| clear -HL8; lia]. intros g Hg.
    eexists. apply (Rsh g). apply (live_block_Sh E0 [] [] a cb cm aid g Hwf); [subst cb; exact Hcm| exact ST|].
    rewrite UB, Ecn. subst cb. clear -Hg HL8 G8. rewrite Z2Nat.id in Hg by lia. lia. }
  destruct SHm as [shj SHm].
  assert (SH2 : rw_cells bsegs m2 SHa [CB (Z.to_nat l8) shj]).
  { eapply BF_unwind.rw_cells_agree; [| exact SHm]. cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by (clear -HL8; lia). intros z Hz. subst SHa. unfold kShadowBase in Hz.
    rewrite kHighMemBeg_val, kLowAppEnd_val in CBB. apply AG2; subst cb; clear -Hz LOC LO CR CB0 CBC CBB Timg Tlo Tband USPR HL8 G8 RG1; lia. }
  (* [comment removed for export] *)
  assert (L8R : 8 * l8 <= rounded n) by (clear -HL8 RG1 RG2 RG3 N40; Z.div_mod_to_equations; lia).
  pose proof (hoareW_arun _ _ _ _ _ _ _ _ _ _ (depot_put_W E0 a1 (bst_key len ws)) (fsame_refl a1) RUNe) as [_ RES2e].
  assert (RES2 : res_ok a2) by (intros sc Hsc; rewrite RES2e; apply Hres; rewrite SSe in Hsc; exact Hsc).
  assert (PSH2 : forall y k, SHa <= y -> y + Z.of_nat k <= SHa + l8 -> P2 (Z_to_bv 64 y, k)).
  { intros y k H1 H2. unfold P2. rewrite <- EPOL. subst SHa. unfold kShadowBase in H1, H2.
    destruct CBLOC as [(c & Hc & L1 & L2)|(sc & Hsc & L1 & L2)].
    - apply (pol_space_shadow' E0 FSB0 HR0 (sA a2 s) mo2 WE2); rewrite A_SB_val;
        unfold region_beg in L1, L2; destruct (proj2 WR c Hc) as (R1 & R2 & R3 & _); cbv zeta in R1, R3; unfold region_of in R1, R3;
        change kRegionSize with 4294967296 in L1, L2; change kFreeArrayOffset with 3758096384 in R3; unfold kLargestClassID in Hc; fold a in L2; subst cb;
        [clear -H1 L1 G8 Hc; Z.div_mod_to_equations; nia| clear -H2 L2 L8R R1 R3 Hc G8; Z.div_mod_to_equations; nia].
    - apply (pol_sec_shadow E0 FSB0 HR0 (sA a2 s) mo2 [] [] WF2 sc); rewrite ?aps_alloc_sA', ?SSe, ?A_SB_val; [exact RES2| exact Hsc| subst cb; clear -H1 L1 G8; Z.div_mod_to_equations; lia| subst cb; clear -H2 L2 L8R G8; Z.div_mod_to_equations; lia]. }
  assert (HCBx : 0x603000 <= cb /\ cb + 16 + 8 * l8 <= alloc_ceiling /\ cb mod 16 = 0) by (subst cb; clear -CB0 CBC P16 L8R; split; [lia| split; [lia| Z.div_mod_to_equations; lia]]).
  assert (HCBP : cb + 16 + 8 * l8 <= 0x7fff7000 \/ kHighMemBeg <= cb) by (subst cb; rewrite kHighMemBeg_val, kLowAppEnd_val in CBB; rewrite kHighMemBeg_val; clear -CBB L8R; lia).
  assert (HCBTx : cb + 16 + 8 * l8 <= T \/ T + 4096 <= cb) by (subst cb; clear -CBT L8R; lia).
  assert (HCB24 : 0x603000 <= cb /\ cb + 24 <= alloc_ceiling /\ cb mod 16 = 0) by (clear -HCBx HL8; lia).
  assert (HCBT : cb + 24 <= T \/ T + 4096 <= cb) by (clear -HCBTx HL8; lia).
  assert (HCBC : cb + 24 <= CTX \/ CTX + 4096 <= cb) by (subst cb; clear -CBI CIA RG1; lia).
  assert (HC : placed_s CTX 4096).
  { pose proof (wf_env_img _ WE) as (_ & _ & _). pose proof WE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & IMGA).
    unfold placed_s, A_IMG_END, A_LOWAPP_END, A_HIGH_BEG. unfold img_sep in IMGA. rewrite EI1 in IMGA. unfold app_mem in WI2. rewrite KHB, KLE in WI2.
    clear -CIA WI2 WI3 WI5 IMGA EI2 CR. unfold kIArenaLen in *. repeat split; lia. }
  assert (HT12 : 0x5d0810 <= 0x6028f8 /\ 0x6028f8 + 8 <= 0x603000) by (clear; lia).
  assert (HTPr : 0x5d0810 + 88 <= bv_unsigned tp < 0x603000) by (rewrite TP; rewrite unsigned_lit by (clear; lia); clear; lia).
  set (nhi := n / 2^32). set (nlo := n mod 2^32).
  assert (HNHI : 0 <= nhi < 256) by (subst nhi; clear -N40; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  assert (HNLO : 0 <= nlo < 2^32) by (subst nlo; clear; apply Z.mod_pos_bound; lia).
  assert (En : n = nhi * 2^32 + nlo) by (subst nhi nlo; clear -N40; rewrite Z.mul_comm; apply Z_div_mod_eq_full).
  assert (HDR2' : rw_cells bsegs m2 cb [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (wz nhi); C4 (wz nlo); C8 (wz aid)]).
  { subst nhi nlo. apply (proj2 (rw_cells_C4_mod32 m2 cb [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (wz (n / 2^32))] [C8 (wz aid)] n)). rewrite <- Ecn. exact HDR2. }
  assert (PSTKA2 : forall y k, lo <= y -> y + Z.of_nat k <= A + 8 * zlen ws -> P2 (Z_to_bv 64 y, k)).
  { intros y k H1 H2. unfold P2. rewrite <- EPOL. apply (pol_stack' E0 FSB0 HR0 (sA a2 s) mo2 AK2 WE2 ENV0); clear -H1 H2 LOC HAW CR; lia. }
  (* [comment removed for export] *)
  set (DQ2 := fun ms5 => exists (t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 : word) (m5 : mem),
        ms5 = MS (mkR (wz 0x36ebc) (wz (usp - 80)) gp tp t0 t1 t2 (wz (INST + 728)) (wz (T + 80)) (wz (T + 80)) (wz (T + 208)) (wz B) (wz cb) (wz n) a5 a6 a7
                      (wz n) (wz B) (wz (T + 208)) (wz cb) (wz 0x100000) s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x36ec8) fc None m5 (seg_rom bsegs)
        /\ mem_inv bsegs m5 /\ stk bsegs m5 lo (usp - 80) /\ wmono bsegs m2 m5
        /\ munch [(usp - 144, usp); (cb + 16, cb + 24); (SHa, SHa + l8)] m2 m5
        /\ rw_cells bsegs m5 (usp - 80) [C8 (wz (T + 208)); C8 (wz B); C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
        /\ rw_cells bsegs m5 cb [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (wz nhi); C4 (wz nlo); C8 (wz aid)]
        /\ rw_cells bsegs m5 (cb + 16) [C8 (wz fid)]
        /\ rw_cells bsegs m5 SHa [CB (Z.to_nat l8) (repeat (Z_to_bv 8 0xfd) (Z.to_nat l8))]
        /\ poison_globals m5).
  eapply (rzA_seg_cfg bsegs (aSc (sA a2 s)) (aNc (sA a2 s)) (aEBc (sA a2 s)) P2 DQ2).
  { eapply evtA_cut.
    { eapply (qchunk_back P2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m2 lo (A + 8 * zlen ws) cb B A len b1 nhi nlo (wz aid) (wz kInvalidTidShifted) CTX T);
        [ exact LOC | fold usp; clear -HB; lia | clear -HBA HWS HLEN; unfold zlen in *; lia | clear -HLEN HWS; lia | exact HCB24 | exact HNHI | exact HNLO
        | exact HC | exact TR2 | exact HTPr | exact HCBT | exact HCBC | exact CT
        | exact PSTKA2 | exact PCH2
        | fold usp; exact SK2 | fold usp; exact USPR48 | exact MI2 | clear -FID FID1; lia | fold usp; exact FR2 | exact HDR2' | exact UW2 ]. }
    intros ms3 HQ3. unfold qchunk_back_post in HQ3. fold usp in HQ3.
    destruct HQ3 as (m3 & -> & MU3 & WM3 & MI3 & SK3 & FID3 & HDR3).
    assert (AG23 : forall z, 0 <= z < 2^64 -> (z + 1 <= cb + 16 \/ cb + 24 <= z) -> m3 (wa z) = m2 (wa z)).
    { intros z Z0 Z1. apply MU3. rewrite wa_unsigned by (clear -Z0; lia). cbn [outside]. clear -Z1. repeat split; try exact I; lia. }
    assert (AGimg3 : forall z, 0xa5000 <= z < 0x140810 -> m3 (wa z) = m2 (wa z)) by (intros z Hz; apply AG23; clear -Hz CB0; lia).
    assert (PG3 : poison_globals m3) by (apply (poison_globals_agree m2 m3 PG2); intros z Hz; apply AGimg3; exact Hz).
    assert (GFL3 : rw_cells bsegs m3 0xa5598 [C8 (wz 0xabdb8)]) by (agi AGimg3 GFL2).
    assert (QMAX3 : rw_cells bsegs m3 0xab270 [C8 (wz 0x10000000); C8 (wz kQuarantineMin); C8 (wz 0x100000)]) by (agi AGimg3 QMAX2).
    assert (FFS3 : rw_cells bsegs m3 0xabde8 [C4 (wz 0)]) by (agi AGimg3 FFS2).
    assert (SH3 : rw_cells bsegs m3 SHa [CB (Z.to_nat l8) shj]).
    { eapply BF_unwind.rw_cells_agree; [| exact SH2]. cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by (clear -HL8; lia). intros z Hz. subst SHa. unfold kShadowBase in Hz.
      rewrite kHighMemBeg_val, kLowAppEnd_val in CBB. apply AG23; subst cb; clear -Hz CR CB0 CBC CBB HL8 G8 RG1; lia. }
    rewrite <- En.
    eapply evtA_cut.
    { eapply (put_front P2 ra sp gp tp t0'' t1'' t2'' s0 s1 a6'' a7'' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3'' t4'' t5'' t6'' F fc m3 lo T B cb ((cb + 16) / 8) b1 nhi nlo n (wz aid) shj);
        [ exact En | clear -G8; lia | exact LOC | fold usp; clear -HB HBA HAW HWS HLEN; unfold zlen in *; lia | exact TR2
        | subst l8; exact HCBx | subst l8; exact HCBP | exact HNHI | exact HNLO | exact N27 | subst l8; exact HCBTx
        | exact PSTK2 | exact PDAT2 | (intros y k Y1 Y2; apply PCH2; [exact Y1| clear -Y2; lia]) | subst l8 SHa; unfold kShadowBase in PSH2; exact PSH2
        | fold usp; exact SK3 | fold usp; clear -LO; lia | exact MI3 | exact QMAX3 | exact GFL3 | exact FFS3 | exact PG3 | exact HDR3 | subst l8 SHa; unfold kShadowBase in SH3; exact SH3 ]. }
    intros ms4 HQ4. unfold put_front_post in HQ4. fold usp in HQ4.
    destruct HQ4 as (u0 & u1 & u2 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m4 & -> & MU4 & WM4 & MI4 & SK4 & PF4 & SH4 & PG4 & HDR4).
    assert (AG34 : forall z, 0 <= z < 2^64 -> (z + 1 <= usp - 144 \/ usp <= z) -> (z + 1 <= SHa \/ SHa + l8 <= z) -> m4 (wa z) = m3 (wa z)).
    { intros z Z0 Z1 Z2. apply MU4. rewrite wa_unsigned by (clear -Z0; lia). cbn [outside]. fold usp. subst SHa. unfold kShadowBase in Z2. change (BF_free1d.l8 n) with l8. clear -Z1 Z2. repeat split; try exact I; lia. }
    apply evtA_done. unfold DQ2. exists u0, u1, u2, v5, v6, v7, u3, u4, u5, u6, m4.
    split; [reflexivity|]. split; [exact MI4|]. split; [exact SK4|]. split; [exact (wmono_trans _ _ _ _ WM3 WM4)|].
    split. { eapply munch_trans; [eapply munch_weaken; [| exact MU3]| eapply munch_weaken; [| exact MU4]]; intros z Hz; cbn in Hz |- *; fold usp in Hz; subst SHa; unfold kShadowBase; change (BF_free1d.l8 n) with l8 in Hz; clear -Hz; tauto. }
    split; [unfold put_frame in PF4; fold usp in PF4; exact PF4|]. split; [exact HDR4|].
    split. { eapply BF_unwind.rw_cells_agree; [| exact FID3]. cbn -[Z.add Z.mul Z.of_nat Z.sub Z.div]. intros z Hz. apply AG34; subst SHa cb; unfold kShadowBase; rewrite kHighMemBeg_val, kLowAppEnd_val in CBB; clear -Hz LOC LO CR CB0 CBC CBB RG1 HL8 G8; lia. }
    split; [subst SHa; change (BF_free1d.l8 n) with l8 in SH4; exact SH4| exact PG4]. }
  { exact KIP2. }
  (* [comment removed for export] *)
  intros ms5 mo5 HQ5 AG25 KIP5. unfold DQ2 in HQ5.
  destruct HQ5 as (u0 & u1 & u2 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m5 & -> & MI5 & SK5 & WM25 & MU25 & PF5 & HDR5 & FID5 & SH5 & PG5).
  pose proof (magree_frame _ _ AG25) as (Ffds5 & Fvm5 & Flz5 & Ffs5 & Fh5 & Ftid5 & _).
  destruct KIP5 as [KIA5 _].
  pose proof (RTOK_magree _ _ _ _ _ _ _ _ _ _ _ TOK2 AG25 KIA5) as TOK5.
  pose proof (AKern_frame _ _ _ _ Fvm5 Flz5 AK2) as AK5.
  assert (AG45 : forall z, 0 <= z < 2^64 -> (z + 1 <= usp - 144 \/ usp <= z) -> (z + 1 <= cb + 16 \/ cb + 24 <= z) -> (z + 1 <= SHa \/ SHa + l8 <= z) -> m5 (wa z) = m2 (wa z)).
  { intros z Z0 Z1 Z2 Z3. apply MU25. rewrite wa_unsigned by (clear -Z0; lia). cbn [outside]. fold usp. clear -Z1 Z2 Z3. repeat split; try exact I; lia. }
  unfold QPF_post in QPOST. subst n.
  eapply (QPOST u0 u1 u2 v5 v6 v7 u3 u4 u5 u6 m5 mo5 a2 cm b1 aid fid);
    [ subst cb; exact Hcm | exact ST | subst cb; rewrite UB; clear; lia | exact HB1' | exact HB1 | exact RUN | clear -FID FID1; lia | exact WF2 | exact SAME | exact AK5 | exact TOK5 | exact KIA5
    | rewrite Ffs5, Ffs2, Ffs1; reflexivity | rewrite Ffds5, Ffds2, Ffds1; reflexivity | rewrite Ftid5, Ftid2, Ftid1; reflexivity
    | exact MI5 | exact SK5 | exact (wmono_trans _ _ _ _ WM1 (wmono_trans _ _ _ _ WM12 WM25)) | | | | | exact PF5 | | exact FID5 | | exact SH5 ].
  - (* [comment removed for export] *)
    exists Wd. split; [| exact FWd].
    eapply munch_trans; [eapply munch_weaken; [| exact MU1] | eapply munch_trans; [eapply munch_weaken; [| exact MUd] | eapply munch_weaken; [| exact MU25]]];
      intros z Hz; unfold W15 in Hz; cbn [outside app] in Hz |- *; fold usp in Hz; destruct Hz as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6).
    + clear -Z1 Z2 Z3 Z4. repeat split; try exact I; lia.
    + exact Z6.
    + subst SHa l8. clear -Z1 Z3 Z5. repeat split; try exact I; lia.
  - (* [comment removed for export] *)
    intros z Z0 NF. unfold FPW1 in NF.
    assert (X1 : ~ (lo <= z < usp) /\ ~ DepotFPd E0 a2 z /\ ~ (cb <= z < cb + 4) /\ ~ (cb + 16 <= z < cb + 24) /\ ~ (T + 2824 <= z < T + 2840) /\ ~ (SHa <= z < SHa + l8))
      by (subst SHa l8; clear -NF; tauto).
    clear NF. destruct X1 as (N1 & N2 & N3 & N4 & N5 & N6).
    rewrite AG45; [| exact Z0| clear -N1 LO; lia| clear -N4; lia| clear -N6; lia].
    rewrite AG12; [| exact Z0| clear -N1 LO; lia| exact N2].
    apply AG1f; [exact Z0| clear -N1 LO; lia| clear -N3; lia| clear -N4; lia| clear -N5; lia].
  - (* [comment removed for export] *)
    eapply DepotR_frame; [exact DR2| exact WM25|]. intros z Dz. pose proof (wa_range z) as WZ || assert (WZ : True) by exact I.
    rewrite kHighMemBeg_val, kLowAppEnd_val in CBB.
    destruct (dfp_cases a2 mo2 z IC0 AK2 WF2 EI1 EI2 Dz) as [ST0|(b & bl & R & B0 & B2 & BB & B3 & B4 & BT & BA)].
    + apply AG45; subst SHa cb; unfold kShadowBase; clear -ST0 LO LOC CR CB0; lia.
    + pose proof (ak_resv_geom _ _ _ Hkern) as (G1 & G2 & G3). change kSpaceSize with 137438953472 in G3. change kPageSize with 4096 in G3. change kResvLen with 137439023104 in G3, B3.
      rewrite kHighMemBeg_val, kLowAppEnd_val in BB.
      apply AG45.
      * clear -R B0 B2 CR. lia.
      * clear -R B2 LO LOC CR. lia.
      * destruct CBLOC as [(c & Hc & L1 & L2)|(sc & Hsc & L1 & L2)].
        -- unfold region_beg in L1, L2. destruct (proj2 WR c Hc) as (R1 & R2 & R3 & _). cbv zeta in R1, R3. unfold region_of in R1, R3.
           change kRegionSize with 4294967296 in L1, L2. change kFreeArrayOffset with 3758096384 in R3. unfold kLargestClassID in Hc.
           fold a in L2. subst cb. clear -R B3 G1 G3 L1 L2 Hc R1 R3 RG1. nia.
        -- pose proof (B4 sc (SECA sc Hsc)) as X. subst cb. clear -R X L1 L2 RG1. lia.
      * subst SHa cb. unfold kShadowBase. clear -R BB CR CB0 CBC L8R G8 HL8. lia.
  - (* [comment removed for export] *)
    destruct DM2 as [M1x M2x]. unfold dput_mutexes, dTD, dSS in *. rewrite kHighMemBeg_val, kLowAppEnd_val in CBB. split.
    + eapply BF_unwind.rw_cells_agree; [| exact M1x]. cbn -[Z.add Z.mul Z.of_nat]. intros z Hz. apply AG45; subst SHa cb; unfold kShadowBase; clear -Hz LO LOC CR CB0; lia.
    + intros k Hk. pose proof (M2x k Hk) as X. eapply BF_unwind.rw_cells_agree; [| exact X]. cbn -[Z.add Z.mul Z.of_nat]. intros z Hz. unfold kStoreBlockCount in Hk.
      apply AG45; subst SHa cb; unfold kShadowBase; clear -Hz Hk LO LOC CR CB0; lia.
  - (* [comment removed for export] *)
    apply (proj1 (rw_cells_C4_mod32 m5 cb [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (wz (cm_n cm / 2^32))] [C8 (wz aid)] (cm_n cm))). exact HDR5.
  - (* [comment removed for export] *)
    rewrite kHighMemBeg_val, kLowAppEnd_val in CBB.
    eapply BF_unwind.rw_cells_agree; [| exact ST1]. cbn -[Z.add Z.mul Z.of_nat Z.sub Z.div]. intros z Hz.
    rewrite AG45; [| clear -Hz Tlo Thi CR; lia| clear -Hz LO LOC Thi; lia| subst cb; clear -Hz CBT RG1; lia| subst SHa cb; unfold kShadowBase; clear -Hz Tband Tlo CB0 CBC L8R G8 HL8 CR; lia].
    apply AG12; [clear -Hz Tlo Thi CR; lia| clear -Hz LO LOC Thi; lia|]. apply NDFP; clear -Hz Timg Tlo Thi; lia.
Qed.

End DeallocT.
End RC__1.
