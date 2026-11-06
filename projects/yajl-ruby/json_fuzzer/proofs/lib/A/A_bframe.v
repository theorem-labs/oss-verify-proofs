(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import base decidable list gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling PropExec MState Mem Cells Frame Arr.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import LiaA AImages AImageFacts LazyModel NodesA Shadow BackingAlgebraA.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import StdioBase STree.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import
  AsanConsts AsanSizeClass AsanState AsanLayout AsanOps AsanHoare AsanRep AsanFakeStack AsanPS AsanKern AsanClient AsanDepot
  AsanBudget AsanBudget2 AsanGap AsanSlack.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import
  A_base A_alloc_iface A_iface A_live A_policy5 A_budget5 A_slack5 AI_shadow AI_lowshadow AYajlRep AYajl_iface AF_place AF_fakestack_rep A_bundle A_benv5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
#[warnings="-notation-for-abbreviation"] Notation mem := (word -> option byte).

Ltac lia ::= LiaA.liaA.

Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section Bundle.
(* [comment removed for export] *)
Variable StdioRep : stdout_st -> mem -> Prop.
Variable RTMisc : aenv -> mem -> Prop.
Variable E0 : aenv.
Variable FSB0 : Z.
Variable HR0 : list (Z * Z).
Variables L0 RES0 : list (word * word).
Variable EB0 : Z.
#[local] Notation AHKc := (AHK StdioRep RTMisc E0 FSB0 HR0 L0 RES0 EB0).
#[local] Notation aSc := (aS E0 FSB0 HR0).
#[local] Notation aNc := (aN E0 FSB0 HR0).
#[local] Notation aEBc := (aEB EB0).
(* [comment removed for export] *)
Variable PL0 : fs_plumb.
Hypothesis ENV0 : env0_ok5 E0.
Hypothesis PL0OK : pl0_ok5 E0 PL0.
(* [comment removed for export] *)
Variable rt_fp : Z -> Prop.
Hypothesis RTMisc_agree : forall m m', RTMisc E0 m -> (forall a, rt_fp a -> m' (wa a) = m (wa a)) -> RTMisc E0 m'.
Hypothesis rt_fp_where : forall a, rt_fp a -> (0x10000 <= a < 0x603000 /\ ~ cl_cells a /\ ~ stdio_w a /\ ~ in_cells img_mut a) \/ rt_high2 E0 PL0 a.
Hypothesis RT_fsenv : forall m, RTMisc E0 m -> FSEnv asegs E0 FSB0 PL0 m.
Variable so_fp : Z -> Prop.
Hypothesis StdioRep_agree : forall so m m', StdioRep so m -> (forall a, so_fp a -> m' (wa a) = m (wa a)) -> StdioRep so m'.
Hypothesis so_fp_where : forall a, so_fp a -> 0x10000 <= a < 0x603000 /\ ~ cl_cells a /\ ~ in_cells img_mut a.
Hypothesis StdioRep_buf : forall so m, StdioRep so m -> Z.of_nat (length (so_buf so)) <= 1024.
(* [comment removed for export] *)
Ltac clear_frame_kit := clear StdioRep_buf so_fp_where StdioRep_agree so_fp RT_fsenv rt_fp_where RTMisc_agree rt_fp.
Ltac clear_all_hyps := clear_frame_kit; clear PL0OK ENV0.

(* [comment removed for export] *)
Lemma ceil_range : 0x7fff80000000 - 8388608 <= alloc_ceiling <= 0x800000000000 - 8388608.
Proof. pose proof alloc_ceiling_range. lia. Qed.

(* [comment removed for export] *)
Ltac wfe_open WE :=
  destruct WE as (WE1 & WE2 & WE3 & WE4 & WE5 & WE6 & WE7 & WE8 & WE9 & WE10 & WE11 & WE12 & WE13 & WE14 & WE15 & WE16 & WE17 & WE18 &
                  WE19 & WE20 & WE21 & WE22 & WE23 & WE24 & WE25 & WE26 & WE27 & WE28 & WE29 & WE30 & WE31 & WE32 & WE33 & WE34 & WE35rest).
Lemma wf_env_resv : forall E, wf_env E ->
  kHighMemBeg <= ae_resv_beg E /\ ae_resv_beg E <= ae_space_beg E
  /\ ae_space_beg E + kSpaceSize + 0x1000 <= ae_resv_beg E + 0x2000011000 /\ ae_resv_beg E + 0x2000011000 <= alloc_ceiling
  /\ In (ae_resv_beg E, 0x2000011000) (ae_reserved E).
Proof. intros E WE. wfe_open WE. repeat split; assumption. Qed.
Lemma wf_env_img : forall E, wf_env E ->
  In (ae_img E) (ae_reserved E) /\ 0x10000 <= fst (ae_img E) /\ fst (ae_img E) + snd (ae_img E) <= kLowAppEnd.
Proof. intros E WE. wfe_open WE. repeat split; assumption. Qed.
Lemma wf_env_fs : forall E, wf_env E ->
  In (ae_fs_beg E, ae_fs_len E) (ae_reserved E) /\ app_mem (ae_fs_beg E) (ae_fs_len E) /\ 0 <= ae_fs_len E
  /\ ae_fs_beg E + ae_fs_len E <= alloc_ceiling
  /\ (ae_fs_beg E + ae_fs_len E <= ae_resv_beg E \/ ae_resv_beg E + 0x2000011000 <= ae_fs_beg E)
  /\ img_sep E (ae_fs_beg E) (ae_fs_len E).
Proof. intros E WE. wfe_open WE. repeat split; assumption. Qed.
Lemma wf_env_thread : forall E, wf_env E ->
  In (ae_thread E, 4096) (ae_reserved E) /\ app_mem (ae_thread E) 4096 /\ ae_thread E + 4096 <= alloc_ceiling
  /\ (ae_thread E + 4096 <= ae_resv_beg E \/ ae_resv_beg E + 0x2000011000 <= ae_thread E)
  /\ (ae_thread E + 4096 <= ae_fs_beg E \/ ae_fs_beg E + ae_fs_len E <= ae_thread E)
  /\ (ae_thread E + 4096 <= ae_ptr_array E \/ ae_ptr_array E + 0x800000 <= ae_thread E)
  /\ img_sep E (ae_thread E) 4096.
Proof. intros E WE. wfe_open WE. repeat split; assumption. Qed.
Lemma wf_env_ptr : forall E, wf_env E ->
  In (ae_ptr_array E, 0x800000) (ae_reserved E) /\ app_mem (ae_ptr_array E) 0x800000 /\ ae_ptr_array E + 0x800000 <= alloc_ceiling
  /\ (ae_ptr_array E + 0x800000 <= ae_resv_beg E \/ ae_resv_beg E + 0x2000011000 <= ae_ptr_array E)
  /\ (ae_ptr_array E + 0x800000 <= ae_fs_beg E \/ ae_fs_beg E + ae_fs_len E <= ae_ptr_array E)
  /\ img_sep E (ae_ptr_array E) 0x800000.
Proof. intros E WE. wfe_open WE. repeat split; assumption. Qed.
Lemma wf_env_iarena : forall E, wf_env E ->
  In (ae_iarena E, kIArenaLen) (ae_reserved E) /\ app_mem (ae_iarena E) kIArenaLen /\ ae_iarena E + kIArenaLen <= alloc_ceiling
  /\ (ae_iarena E + kIArenaLen <= ae_resv_beg E \/ ae_resv_beg E + 0x2000011000 <= ae_iarena E)
  /\ ae_iarena E mod 4096 = 0.
Proof. intros E WE. wfe_open WE. repeat split; assumption. Qed.
Lemma wf_env_stack : forall E, wf_env E -> ae_stack_bottom E < ae_stack_top E /\ ae_space_beg E mod 2^16 = 0.
Proof. intros E WE. wfe_open WE. split; assumption. Qed.
Ltac app_mem_num H := unfold app_mem, kLowAppEnd, kLowShadowMapBeg, kShadowBase, kPageSize in H; rewrite ?kHighMemBeg_val in H.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma live_block_geom : forall {P D} s mo b,
  AWf (aps_env s) P D (aps_alloc s) -> AKern (aps_env s) (aps_alloc s) mo -> ENVOK E0 FSB0 s ->
  In (ab_addr b, ab_size b) (live_blocks (aps_alloc s)) ->
  placed (ab_addr b) (ab_size b) /\ ab_addr b mod 16 = 0
  /\ (ab_addr b + ab_size b <= ae_store_blk (aps_env s) \/ ae_store_blk (aps_env s) + 2^23 <= ab_addr b)
  /\ (forall sb, In sb (as_store_blocks (aps_alloc s)) -> ab_addr b + ab_size b <= sb \/ sb + kStoreBlockBytes <= ab_addr b).
Proof.
  intros P D s mo b WF K EV Hin. pose proof ceil_range as CR.
  destruct EV as (V1 & V2 & V3 & V4 & V5 & V6 & EIN & EF1 & EF2 & EE & EFS & EIMG).
  destruct (live_blocks_chunk _ _ _ Hin) as (cb & cm & i & Hcm & HA & Hn & Hst).
  pose proof (chunk_user_in_block _ _ _ _ _ _ WF Hcm) as (U1 & U2 & U3).
  pose proof (chunk_user_aligned _ _ _ _ _ _ WF Hcm) as UA.
  pose proof (chunk_block_committed _ _ _ _ _ _ WF Hcm) as BC.
  pose proof WF as WF0. destruct WF as (WE & WR & WC & [WK _] & WQ & WS & WD).
  destruct (WK _ _ Hcm) as (_ & KN & _ & KP & _).
  unfold user_lo, user_hi, blk_lo in *. rewrite HA, Hn in *.
  pose proof (ak_resv_geom _ _ _ K) as (G1 & G2 & G3). pose proof (ak_store_sep _ _ _ K) as (S1 & S2 & _).
  pose proof (ak_blocks_sep _ _ _ K) as KB.
  pose proof (wf_env_resv _ WE) as (WE2 & WE3 & WE4 & WE5 & _). pose proof (wf_env_img _ WE) as (WE29 & WE30 & WE31).
  rewrite kHighMemBeg_val in *. unfold blk_hi in *. unfold placed, A_IMG_END, A_LOWAPP_END, A_HIGH_BEG.
  change kSpaceSize with 137438953472 in *. change kResvLen with 137439023104 in *. change kPageSize with 4096 in *.
  change kStoreBlockBytes with 8388608 in *.
  destruct (cm_prim cm) as [c|].
  - (* [comment removed for export] *)
    destruct BC as (Hc & B1 & B2).
    destruct WR as [_ WR]. destruct (WR c Hc) as (R1 & R2 & R3 & _).
    unfold region_of, region_beg in *.
    change kRegionSize with 4294967296 in *. change kFreeArrayOffset with 3758096384 in R3. change kLargestClassID with 30 in Hc.
    assert (c * 4294967296 <= 30 * 4294967296) by (clear -Hc; lia).   (* [comment removed for export] *)
    repeat split; try lia.
    intros sb Hsb. destruct (KB sb 8388608 (or_intror (conj Hsb eq_refl))) as (K1 & K2 & K3 & K4 & K5 & K6). lia.
  - (* [comment removed for export] *)
    destruct KP as (FP & sc0 & Hsc0 & AB0 & MS0 & ND0).
    destruct BC as (sc & Hsc & B1 & B2).
    destruct WS as (_ & _ & WS3 & _). destruct (WS3 sc Hsc) as (M1 & M2 & M3 & M4 & M5 & M6 & M7).
    assert (BIG : 64512 < ab_size b).
    { destruct (Z.le_gt_cases (ab_size b) 64512) as [LE|GT]; [| exact GT].
      exfalso. apply (proj2 (from_primary_iff (ab_size b) ltac:(lia))) in LE. rewrite LE in FP. discriminate. }
    (* [comment removed for export] *)
    pose proof (M7 _ WE29) as IMS. destruct EIMG as [EI1 EI2]. rewrite EI1 in IMS. app_mem_num M2.
    (* [comment removed for export] *)
    destruct (S2 sc Hsc) as [SS|SS]; repeat split;
      try (lazymatch goal with |- forall _ : Z, _ => fail | |- _ => clear -U1 U2 B1 B2 UA M2 M3 M4 IMS EI2 SS BIG CR KN; lia end).
    all: try (intros sb Hsb; destruct (KB sb 8388608 (or_intror (conj Hsb eq_refl))) as (K1 & K2 & K3 & K4 & K5 & K6); destruct (K5 sc Hsc); lia).
Qed.

(* [comment removed for export] *)
Lemma AHK_blocks : forall s LB LF m mo, AHKc s LB LF m mo ->
    (forall b, In b LB -> ablock_range ACONSTS (ab_addr b) (ab_size b))
    /\ (forall b1 b2, In b1 LB -> In b2 LB -> ab_addr b1 <> ab_addr b2 ->
          ab_addr b1 + ab_size b1 <= ab_addr b2 \/ ab_addr b2 + ab_size b2 <= ab_addr b1)
    /\ List.NoDup (map ab_addr LB).
Proof.
  intros s LB LF m mo H. pose proof H as H0. ahk_open H. split; [| split].
  - intros b Hb. pose proof (live_block_geom s mo b Hwf Hkern Henv (blocks_match_In _ _ _ Hbm Hb)) as ((G1 & G2 & G3) & GA & _).
    destruct (live_blocks_chunk _ _ _ (blocks_match_In _ _ _ Hbm Hb)) as (cb & cm & i & Hcm & HA & Hn & _).
    destruct Hwf as (WE & WR & WC & [WK _] & _). destruct (WK _ _ Hcm) as (_ & Kn & _).
    unfold ablock_range. cbn [c_img_hi ACONSTS]. unfold A_IMG_END in G1. rewrite <- Hn. rewrite <- Hn in G2.
    repeat split; try lia.
  - intros b1 b2 H1 H2 Hne.
    destruct (live_blocks_chunk _ _ _ (blocks_match_In _ _ _ Hbm H1)) as (cb1 & cm1 & i1 & Hc1 & HA1 & Hn1 & _).
    destruct (live_blocks_chunk _ _ _ (blocks_match_In _ _ _ Hbm H2)) as (cb2 & cm2 & i2 & Hc2 & HA2 & Hn2 & _).
    pose proof (chunk_user_in_block _ _ _ _ _ _ Hwf Hc1) as (_ & _ & E1).
    pose proof (chunk_user_in_block _ _ _ _ _ _ Hwf Hc2) as (_ & _ & E2).
    assert (Hcb : cb1 <> cb2) by (unfold user_lo in *; rewrite HA1 in E1; rewrite HA2 in E2; lia).
    pose proof (live_blocks_disjoint _ _ _ _ _ _ _ _ Hwf Hc1 Hc2 Hcb) as DJ.
    unfold user_lo, user_hi in DJ. rewrite HA1, HA2, Hn1, Hn2 in DJ. exact DJ.
  - (* [comment removed for export] *)
    assert (HN : List.NoDup (map fst (live_blocks (aps_alloc s)))).
    { unfold live_blocks, chunk_list. rewrite map_map. cbn [fst].
      set (L := map_to_list (as_chunks (aps_alloc s))).
      assert (HK : List.NoDup (map fst L)) by (apply NoDup_ListNoDup; apply NoDup_fst_map_to_list).
      assert (HF : forall p, In p L -> cm_user_beg (snd p) = fst p + kChunkHeaderSize).
      { intros [cb cm] Hp. cbn. assert (Hl : as_chunks (aps_alloc s) !! cb = Some cm).
        { apply (elem_of_map_to_list (as_chunks (aps_alloc s)) cb cm). apply base.list_elem_of_In. exact Hp. }
        pose proof (chunk_user_in_block _ _ _ _ _ _ Hwf Hl) as (_ & _ & E). unfold user_lo in E. lia. }
      clearbody L. induction L as [|p L IH]; cbn; [constructor|].
      inversion HK as [|x l Hx Hl]; subst.
      destruct (match cm_state (snd p) with CAllocated _ => true | CQuarantined _ _ => false end); cbn.
      + constructor.
        * intros Hin. apply in_map_iff in Hin. destruct Hin as (q & Eq & Hq). apply filter_In in Hq as [Hq _].
          apply Hx. rewrite (HF p (or_introl eq_refl)) in Eq. rewrite (HF q (or_intror Hq)) in Eq.
          apply in_map_iff. exists q. split; [lia| exact Hq].
        * apply IH; [exact Hl | intros q Hq; apply HF; right; exact Hq].
      + apply IH; [exact Hl | intros q Hq; apply HF; right; exact Hq]. }
    unfold blocks_match in Hbm.
    assert (E : map ab_addr LB = map fst (map (fun b => (ab_addr b, ab_size b)) LB)) by (rewrite map_map; reflexivity).
    rewrite E. eapply Permutation_NoDup; [| exact HN]. apply Permutation_map. apply Permutation_sym. exact Hbm.
Qed.

(* [comment removed for export] *)
Lemma AHK_y_small_high : forall s LB LF m mo b, AHKc s LB LF m mo -> In b LB -> 0 < ab_size b <= 64512 ->
  kHighMemBeg <= ab_addr b /\ ab_addr b + ab_size b <= alloc_ceiling.
Proof.
  intros s LB LF m mo b H Hb Hsz. ahk_open H.
  destruct (live_blocks_chunk _ _ _ (blocks_match_In _ _ _ Hbm Hb)) as (cb & cm & i & Hcm & HA & Hn & _).
  destruct (live_small_is_primary _ _ _ _ _ _ Hwf Hcm ltac:(rewrite Hn; lia)) as (c & Hc).
  pose proof (chunk_user_in_block _ _ _ _ _ _ Hwf Hcm) as (U1 & U2 & U3).
  pose proof (chunk_block_committed _ _ _ _ _ _ Hwf Hcm) as BC. rewrite Hc in BC. destruct BC as (Hcc & B1 & B2).
  pose proof Hwf as (WE & [_ WR] & _). pose proof (wf_env_resv _ WE) as (WE2 & WE3 & WE4 & WE5 & _).
  destruct (WR c Hcc) as (R1 & R2 & R3 & _).
  unfold user_lo, user_hi, blk_lo, blk_hi, region_of, region_beg in *. rewrite HA, Hn in *.
  change kRegionSize with 4294967296 in *. change kFreeArrayOffset with 3758096384 in R3. change kLargestClassID with 30 in Hcc.
  change kSpaceSize with 137438953472 in *.
  assert (c * 4294967296 <= 30 * 4294967296) by nia.
  clear Hrep Hkern Hkvm Hres Hqb Hdi Hbinv Hbm Hfs Hicp Hyst Hlow Hrt Hso Hkm Hli Hbud Hmi Henv Hycl Hss Hcs WR WE.
  split; lia.
Qed.

(* [comment removed for export] *)
Lemma lazy_disjoint_low : forall {P D} s mo lo hi,
  AKern (aps_env s) (aps_alloc s) mo -> AWf (aps_env s) P D (aps_alloc s) -> ENVOK E0 FSB0 s ->
  hi <= 0x7fff7000 ->
  (hi <= ae_store_blk (aps_env s) \/ ae_store_blk (aps_env s) + 2^23 <= lo) ->
  (forall b, In b (as_store_blocks (aps_alloc s)) -> hi <= b \/ b + kStoreBlockBytes <= lo) ->
  (hi <= ae_ptr_array (aps_env s) \/ ae_ptr_array (aps_env s) + kPtrArrayLen <= lo) ->
  lazy_disjoint mo lo hi.
Proof.
  intros P D s mo lo hi K WF EV Hhi HS0 HSB HP l sz Hin.
  pose proof (ak_lazy _ _ _ K (l, sz) Hin) as HL. unfold elo, ehi in HL. cbn [fst snd] in HL.
  pose proof (bvu64 l). pose proof (bvu64 sz).
  pose proof WF as (WE & _). pose proof (wf_env_resv _ WE) as (WE2 & _).
  rewrite kHighMemBeg_val in *.
  destruct HL as [HL | [HL | [(b & Hb & HL1 & HL2) | [HL | (HL & _)]]]].
  - lia.
  - lia.
  - destruct (HSB b Hb); lia.
  - destruct (as_ptr_committed (aps_alloc s) =? 0); change kPtrArrayCommit with 131072 in HL; lia.
  - lia.
Qed.

(* [comment removed for export] *)
Lemma lazy_disjoint_img : forall {P D} s mo lo hi,
  AKern (aps_env s) (aps_alloc s) mo -> AWf (aps_env s) P D (aps_alloc s) -> ENVOK E0 FSB0 s ->
  hi <= 0x603000 -> lazy_disjoint mo lo hi.
Proof.
  intros P D s mo lo hi K WF EV Hhi. pose proof EV as (V1 & V2 & _ & _ & _ & _ & _ & _ & _ & EE & _ & EI1 & EI2).
  pose proof WF as (WE & _). pose proof (wf_env_ptr _ WE) as (_ & P2 & _ & _ & _ & P6). pose proof (wf_env_img _ WE) as (I1 & I2 & _).
  pose proof ENV0 as (_ & _ & _ & S0P & _ & S0I & _). rewrite <- EE in S0P, S0I.
  unfold img_sep in P6, S0I. rewrite EI1 in P6, S0I. app_mem_num P2. pose proof (placed_num _ _ S0P ltac:(unfold kStoreBlockBytes; clear; lia)) as (S01 & S02 & S03).
  apply (lazy_disjoint_low s mo lo hi K WF EV); [clear -Hhi; lia| | | ].
  - change kStoreBlockBytes with 8388608 in *. clear -Hhi S01 S0I EI2. lia.
  - intros b Hb. destruct (ak_blocks_sep _ _ _ K b kStoreBlockBytes (or_intror (conj Hb eq_refl))) as (B1 & _ & _ & _ & _ & B6).
    destruct (B6 _ I1) as [X|X]; [| rewrite EI1 in X; clear -X Hhi EI2; lia].
    exfalso. app_mem_num B1. rewrite EI1 in X. change kStoreBlockBytes with 8388608 in *. clear -B1 X. lia.
  - change kPtrArrayLen with 0x800000. clear -Hhi P2 P6 EI2. lia.
Qed.

Lemma lazy_disjoint_stack : forall {P D} s mo lo hi,
  AKern (aps_env s) (aps_alloc s) mo -> AWf (aps_env s) P D (aps_alloc s) -> ENVOK E0 FSB0 s ->
  alloc_ceiling <= lo -> lazy_disjoint mo lo hi.
Proof.
  intros P D s mo lo hi K WF EV Hlo l sz Hin. pose proof ceil_range as CR.
  pose proof (ak_lazy _ _ _ K (l, sz) Hin) as HL. unfold elo, ehi in HL. cbn [fst snd] in HL.
  pose proof (bvu64 l). pose proof (bvu64 sz). pose proof EV as (V1 & V2 & _).
  pose proof WF as (WE & _). pose proof (wf_env_resv _ WE) as (WE2 & WE3 & WE4 & WE5 & _). pose proof (wf_env_ptr _ WE) as (_ & _ & P3 & _).
  rewrite kHighMemBeg_val in *. change kResvLen with 0x2000011000 in HL. change kPtrArrayLen with 8388608 in HL.
  destruct HL as [HL | [HL | [(b & Hb & HL1 & HL2) | [HL | (HL0 & HL1 & _)]]]].
  - lia.
  - lia.
  - destruct (ak_blocks_sep _ _ _ K b kStoreBlockBytes (or_intror (conj Hb eq_refl))) as (_ & B2 & _). lia.
  - destruct (as_ptr_committed (aps_alloc s) =? 0); change kPtrArrayCommit with 131072 in HL; lia.
  - lia.
Qed.

(* [comment removed for export] *)
Lemma lazy_disjoint_gen : forall {P D} s mo lo hi,
  AKern (aps_env s) (aps_alloc s) mo -> AWf (aps_env s) P D (aps_alloc s) -> ENVOK E0 FSB0 s ->
  (hi <= 0x7fff7000 \/ kHighMemBeg <= lo) ->
  (hi <= ae_store_blk (aps_env s) \/ ae_store_blk (aps_env s) + 2^23 <= lo) ->
  (forall b, In b (as_store_blocks (aps_alloc s)) -> hi <= b \/ b + kStoreBlockBytes <= lo) ->
  (hi <= ae_ptr_array (aps_env s) \/ ae_ptr_array (aps_env s) + kPtrArrayLen <= lo) ->
  (hi <= ae_resv_beg (aps_env s) \/ ae_resv_beg (aps_env s) + kResvLen <= lo) ->
  lazy_disjoint mo lo hi.
Proof.
  intros P D s mo lo hi K WF Henv Hband HS0 HSB HP HR l sz Hin.
  pose proof (ak_lazy _ _ _ K (l, sz) Hin) as HL. unfold elo, ehi in HL. cbn [fst snd] in HL.
  pose proof (bvu64 l). pose proof (bvu64 sz).
  rewrite kHighMemBeg_val in *.
  destruct HL as [HL | [HL | [(b & Hb & HL1 & HL2) | [HL | (HL0 & HL1 & _)]]]].
  - lia.
  - lia.
  - destruct (HSB b Hb); lia.
  - destruct (as_ptr_committed (aps_alloc s) =? 0); change kPtrArrayCommit with 131072 in HL; lia.
  - lia.
Qed.
(* [comment removed for export] *)
Lemma lazy_disjoint_high : forall {P D} s mo lo hi,
  AKern (aps_env s) (aps_alloc s) mo -> AWf (aps_env s) P D (aps_alloc s) -> ENVOK E0 FSB0 s ->
  kHighMemBeg <= lo ->
  (hi <= ae_store_blk (aps_env s) \/ ae_store_blk (aps_env s) + 2^23 <= lo) ->
  (forall b, In b (as_store_blocks (aps_alloc s)) -> hi <= b \/ b + kStoreBlockBytes <= lo) ->
  (hi <= ae_ptr_array (aps_env s) \/ ae_ptr_array (aps_env s) + kPtrArrayLen <= lo) ->
  (hi <= ae_resv_beg (aps_env s) \/ ae_resv_beg (aps_env s) + kResvLen <= lo) ->
  lazy_disjoint mo lo hi.
Proof. intros P D s mo lo hi K WF Henv Hlo. apply (lazy_disjoint_gen s mo lo hi K WF Henv). right; exact Hlo. Qed.

(* [comment removed for export] *)
Lemma lazy_disjoint_fs : forall {P D} s mo,
  AKern (aps_env s) (aps_alloc s) mo -> AWf (aps_env s) P D (aps_alloc s) -> ENVOK E0 FSB0 s ->
  lazy_disjoint mo (aps_fsbase s) (aps_fsbase s + kFsBytes).
Proof.
  intros P D s mo K WF Henv. pose proof Henv as (V1 & V2 & V3 & V4 & V5 & V6 & EIN & EF1 & EF2 & EE & EFS & _).
  pose proof WF as (WE & _). pose proof (wf_env_fs _ WE) as (F1 & F2 & F3 & F4 & F5 & F6). pose proof (wf_env_ptr _ WE) as (_ & _ & _ & _ & P5 & _).
  rewrite EF1, EF2 in F5, P5. app_mem_num V3.
  apply (lazy_disjoint_gen s mo _ _ K WF Henv); [rewrite kHighMemBeg_val; unfold kFsBytes in *; clear -V3; lia| exact V6| | |].
  - intros b Hb. destruct (ak_blocks_sep _ _ _ K b kStoreBlockBytes (or_intror (conj Hb eq_refl))) as (_ & _ & _ & _ & _ & B6).
    destruct (B6 _ EIN) as [X|X]; cbn [fst snd] in X; lia.
  - change kPtrArrayLen with (0x800000). lia.
  - change kResvLen with 0x2000011000. lia.
Qed.

(* [comment removed for export] *)
Lemma lazy_disjoint_block : forall {P D} s mo A n,
  AKern (aps_env s) (aps_alloc s) mo -> AWf (aps_env s) P D (aps_alloc s) -> ENVOK E0 FSB0 s ->
  In (A, n) (live_blocks (aps_alloc s)) ->
  lazy_disjoint mo (A - 16) (A + n).
Proof.
  intros P D s mo A n K WF Henv Hin l sz Hl.
  pose proof (ak_lazy _ _ _ K (l, sz) Hl) as HL. unfold elo, ehi in HL. cbn [fst snd] in HL.
  pose proof (bvu64 l) as Bl. pose proof (bvu64 sz) as Bsz.
  destruct (live_blocks_chunk _ _ _ Hin) as (cb & cm & i & Hcm & HA & Hn & Hst).
  pose proof (chunk_user_in_block _ _ _ _ _ _ WF Hcm) as (U1 & U2 & U3).
  pose proof (chunk_block_committed _ _ _ _ _ _ WF Hcm) as BC.
  unfold user_lo, user_hi, blk_lo, blk_hi in *. rewrite HA, Hn in *.
  pose proof Henv as (V1 & V2 & V3 & V4 & V5 & V6 & EIN & EF1 & EF2 & EE & EFS & _).
  pose proof WF as (WE & WR & _ & _ & _ & WS & _).
  pose proof (wf_env_resv _ WE) as (WE2 & WE3 & WE4 & WE5 & WE7). pose proof (wf_env_ptr _ WE) as (WE8 & _ & _ & WP4 & _).
  pose proof (ak_store_sep _ _ _ K) as (S1 & S2 & _).
  rewrite kHighMemBeg_val in *.
  change kResvLen with 0x2000011000 in *. change kPtrArrayLen with 8388608 in *. change kPtrArrayCommit with 131072 in HL.
  change kSpaceSize with 137438953472 in *. change kPageSize with 4096 in *. change kStoreBlockBytes with 8388608 in *.
  destruct (cm_prim cm) as [c|].
  - destruct BC as (Hc & B1 & B2). change kLargestClassID with 30 in Hc.
    destruct WR as [_ WR]. destruct (WR c Hc) as (R1 & R2 & R3 & _).
    unfold region_of, region_beg in *. change kRegionSize with 4294967296 in *. change kFreeArrayOffset with 3758096384 in R3.
    assert (CC : 0 <= c * 4294967296 <= 30 * 4294967296) by nia.
    destruct HL as [HL | [HL | [(b & Hb & HL1 & HL2) | [HL | (HL0 & HL1 & HL2 & HL3)]]]].
    + lia.
    + lia.
    + destruct (ak_blocks_sep _ _ _ K b 8388608 (or_intror (conj Hb eq_refl))) as (_ & _ & _ & B3 & _).
      change kResvLen with 0x2000011000 in B3. clear -B3 HL1 HL2 B1 B2 U1 U2 U3 WE3 WE4 CC Bl Bsz R3. lia.
    + destruct (as_ptr_committed (aps_alloc s) =? 0); clear -HL WP4 WE3 WE4 B1 B2 U1 U2 U3 CC R3 Bl Bsz; lia.
    + pose proof (class_size_mod c ltac:(clear -Hc; lia)) as [_ CS].
      assert (MU : 0 < rg_mapped_user (get_region (aps_alloc s) c)) by (clear -B1 B2 CS; lia).
      destruct (HL2 c ltac:(clear -Hc; change kLargestClassID with 30; lia) MU) as [X|X]; clear -X B1 B2 U1 U2 U3 Bl Bsz; lia.
  - destruct BC as (sc & Hsc & B1 & B2). destruct WS as (_ & _ & WS3 & _).
    destruct (WS3 sc Hsc) as (M1 & M2 & M3 & M4 & M5 & M6 & M7). app_mem_num M2.
    destruct HL as [HL | [HL | [(b & Hb & HL1 & HL2) | [HL | (HL0 & HL1 & HL2 & HL3)]]]].
    + lia.
    + destruct (S2 sc Hsc); lia.
    + destruct (ak_blocks_sep _ _ _ K b 8388608 (or_intror (conj Hb eq_refl))) as (_ & _ & _ & _ & B4 & _). destruct (B4 sc Hsc); lia.
    + destruct (M7 _ WE8) as [X|X]; cbn [fst snd] in X; destruct (as_ptr_committed (aps_alloc s) =? 0); lia.
    + destruct (M7 _ WE7) as [X|X]; cbn [fst snd] in X; lia.
Qed.

(* [comment removed for export] *)
Lemma acc_ok_of_lazy_disjoint : forall mo S lo hi (a : Z) (k : nat),
  lazy_disjoint mo lo hi -> 0 <= lo -> hi <= 2^64 -> lo <= a -> a + Z.of_nat k <= hi -> acc_ok (m_vm_lazy mo) S (Z_to_bv 64 a, k).
Proof.
  intros mo S lo hi a k HD Hlo Hhi Ha Hk.
  destruct k as [|k'].
  - right. split; [unfold acc_nowrap; cbn [fst snd]; pose proof (bvu64 (Z_to_bv 64 a)); lia| intros kk Hkk; cbn in Hkk; lia].
  - left. eapply lazy_disjoint_acc_out; [exact HD| lia| lia| lia| exact Hk| lia].
Qed.

(* [comment removed for export] *)
Lemma AHK_adrv_policy : forall s LB LF m mo x,
  AHKc s LB LF m mo -> adrv_acc ACONSTS LB x -> acc_ok (m_vm_lazy mo) (aSc s) x.
Proof.
  intros s LB LF m mo [w k] H Hacc. pose proof H as H0. ahk_open H. pose proof ceil_range as CR.
  rewrite <- (Z_to_bv_bv_unsigned 64 w) || rewrite <- (Z_to_bv_bv_unsigned w). pose proof (bvu64 w) as Hw.
  unfold adrv_acc in Hacc. cbn [fst snd c_img_lo c_img_hi ACONSTS] in Hacc.
  set (a := bv_unsigned w) in *. clearbody a.
  destruct Hacc as [[S1 S2] | [[I1 I2] | (b & Hb & B1 & B2)]].
  - eapply (acc_ok_of_lazy_disjoint mo (aSc s) a (2^64)); [| lia| lia| lia| lia].
    apply (lazy_disjoint_stack s mo _ _ Hkern Hwf Henv). lia.
  - eapply (acc_ok_of_lazy_disjoint mo (aSc s) 0 0x603000); [| lia| lia| lia| lia].
    apply (lazy_disjoint_img s mo _ _ Hkern Hwf Henv). lia.
  - pose proof (live_block_geom s mo b Hwf Hkern Henv (blocks_match_In _ _ _ Hbm Hb)) as ((G1 & G2 & G3) & _).
    unfold A_IMG_END in G1.
    eapply (acc_ok_of_lazy_disjoint mo (aSc s) (ab_addr b - 16) (ab_addr b + ab_size b)); [| lia| lia| lia| lia].
    exact (lazy_disjoint_block s mo _ _ Hkern Hwf Henv (blocks_match_In _ _ _ Hbm Hb)).
Qed.

Lemma AHK_kip : forall s LB LF m mo, AHKc s LB LF m mo ->
    m_halted mo = None /\ minvA mo /\ LI (aSc s) (aNc s) (aEBc s) mo
    /\ (forall x, adrv_acc ACONSTS LB x -> acc_ok (m_vm_lazy mo) (aSc s) x)
    /\ (forall mo', magree mo mo' -> LI (aSc s) (aNc s) (aEBc s) mo' -> AHKc s LB LF m mo').
Proof.
  intros s LB LF m mo H. split; [exact (AHK_halted _ _ _ _ _ _ _ _ _ _ _ _ _ H)|]. split; [exact (AHK_minvA _ _ _ _ _ _ _ _ _ _ _ _ _ H)|].
  split; [exact (AHK_LI _ _ _ _ _ _ _ _ _ _ _ _ _ H)|]. split.
  - intros x Hx. exact (AHK_adrv_policy _ _ _ _ _ _ H Hx).
  - intros mo' Hag HLI. exact (AHK_magree _ _ _ _ _ _ _ _ _ _ _ _ _ _ H Hag HLI).
Qed.

(* [comment removed for export] *)
Lemma u8arr_of_C1s : forall m (base : Z) (bs : list byte),
  0 <= base -> base + Z.of_nat (length bs) <= 2^64 ->
  (forall i, (i < length bs)%nat -> rw_cells asegs m (base + Z.of_nat i) [C1 (nth i bs (Z_to_bv 8 0))]) ->
  u8arr asegs m base bs.
Proof.
  intros m base bs Hb Hl H. split.
  - split; [lia|]. split; [lia|]. intros i Hi.
    destruct (H i Hi) as [[_ Hba] _]. cbn [cells_bytes cbytes app] in Hba.
    destruct Hba as (_ & _ & Hr). specialize (Hr 0%nat ltac:(cbn; lia)). cbn [nth_error] in Hr.
    rewrite Z.add_0_r in Hr. rewrite Hr. symmetry. apply nth_error_nth'. exact Hi.
  - split; [lia|]. split; [lia|]. intros i Hi.
    destruct (H (Z.to_nat i) ltac:(lia)) as [_ (_ & _ & Hw)]. cbn [cells_size csize] in Hw.
    specialize (Hw 0 ltac:(lia)). rewrite Z2Nat.id in Hw by lia. rewrite Z.add_0_r in Hw. exact Hw.
Qed.

(* [comment removed for export] *)
Lemma blk_shadow_nth : forall n i, 0 < n -> (i < length (blk_shadow n))%nat ->
  nth i (blk_shadow n) (Z_to_bv 8 0) = Z_to_bv 8 (if 8 * Z.of_nat i + 8 <=? n then 0 else n mod 8).
Proof.
  intros n i Hn Hi. pose proof (blk_shadow_length n ltac:(lia)) as HL.
  unfold blk_shadow in *. rewrite length_app, repeat_length in Hi.
  destruct (Nat.lt_ge_cases i (Z.to_nat (n / 8))) as [Hlt|Hge].
  - rewrite app_nth1 by (rewrite repeat_length; exact Hlt). rewrite nth_repeat_lt by exact Hlt.
    replace (8 * Z.of_nat i + 8 <=? n) with true; [reflexivity|]. symmetry. apply Z.leb_le. Z.div_mod_to_equations; lia.
  - rewrite app_nth2 by (rewrite repeat_length; lia). rewrite repeat_length.
    destruct (Z.eqb_spec (n mod 8) 0) as [E|E]; [cbn in Hi; lia|].
    cbn [length] in Hi. replace (i - Z.to_nat (n / 8))%nat with 0%nat by lia. cbn [nth].
    replace (8 * Z.of_nat i + 8 <=? n) with false; [reflexivity|]. symmetry. apply Z.leb_gt. Z.div_mod_to_equations; lia.
Qed.

(* [comment removed for export] *)
Lemma AHK_block_oshadow : forall s LB LF m mo b,
  AHKc s LB LF m mo -> In b LB -> 0 < ab_size b -> oshadow m (ab_addr b) (ab_size b) /\ amem (ab_addr b) (ab_size b).
Proof.
  intros s LB LF m mo b H Hb Hn. pose proof H as H0. ahk_open H. pose proof ceil_range as CR.
  pose proof (live_block_geom s mo b Hwf Hkern Henv (blocks_match_In _ _ _ Hbm Hb)) as ((G1 & G2 & G3) & GA & _).
  unfold A_IMG_END in G1. unfold A_LOWAPP_END, A_HIGH_BEG in G3.
  destruct (live_blocks_chunk _ _ _ (blocks_match_In _ _ _ Hbm Hb)) as (cb & cm & i & Hcm & HA & Hsz & Hst).
  split.
  2:{ unfold amem. split; [exact G1| exact G3]. }
  unfold oshadow, block_shadow. split; [lia|]. split; [lia|].
  pose proof (blk_shadow_length (ab_size b) ltac:(lia)) as HL.
  apply u8arr_of_C1s.
  - rewrite ?A_SB_val. clear -G1. Z.div_mod_to_equations. lia.
  - rewrite ?A_SB_val. clear -G1 G2 CR HL Hn. Z.div_mod_to_equations. lia.
  - intros k Hk. rewrite blk_shadow_nth by lia.
    set (g := ab_addr b / 8 + Z.of_nat k).
    assert (HG : ab_addr b <= 8 * g < ab_addr b + ab_size b).
    { subst g. assert (Z.of_nat k < (ab_size b + 7) / 8) by lia. clear -H GA Hn. Z.div_mod_to_equations. lia. }
    pose proof (live_block_Sh _ _ _ _ _ _ i g Hwf Hcm Hst ltac:(rewrite HA, Hsz; exact HG)) as HSH.
    pose proof (ARep_shadow_cells _ _ _ _ _ g _ Hrep HSH) as HC.
    unfold A_SB. change kShadowBase with 2147450880 in HC.
    replace (2147450880 + ab_addr b / 8 + Z.of_nat k) with (2147450880 + g) by lia.
    rewrite HA, Hsz in HC.
    replace (8 * Z.of_nat k + 8 <=? ab_size b) with (8 * g + 8 <=? ab_addr b + ab_size b); [exact HC|].
    subst g. assert (E8 : ab_addr b mod 8 = 0) by (clear -GA; Z.div_mod_to_equations; lia).
    destruct (Z.leb_spec (8 * Z.of_nat k + 8) (ab_size b)), (Z.leb_spec (8 * (ab_addr b / 8 + Z.of_nat k) + 8) (ab_addr b + ab_size b));
      try reflexivity; exfalso; clear Hrep Hwf Hkern Hkvm Hres Hqb Hdi Hbinv Hbm Hfs Hicp Hyst Hlow Hrt Hso Hkm Hli Hbud Hmi Henv Hycl Hss Hcs H0 HC HSH;
      Z.div_mod_to_equations; lia.
Qed.

(* [comment removed for export] *)
Lemma page_size_val : page_size = 4096.
Proof. reflexivity. Qed.

Lemma aS_intro_A0 : forall s lo hi z,
  In (lo, hi) (A0 E0 FSB0 HR0) -> lo mod 4096 = 0 -> 0 <= lo -> hi <= 2^64 -> lo <= z < hi ->
  aSc s (page_base_of z).
Proof.
  intros s lo hi z Hin Hal Hlo Hhi Hz. unfold aS, A_policy5.aS, A_policy5.aSa, page_base_of. rewrite page_size_val.
  rewrite unsigned_lit by (Z.div_mod_to_equations; lia). split; [Z.div_mod_to_equations; lia|].
  left. exists (lo, hi). split; [exact Hin|]. cbn [fst snd]. Z.div_mod_to_equations; lia.
Qed.

Lemma pages_budgeted_A0 : forall s lo hi a b,
  In (lo, hi) (A0 E0 FSB0 HR0) -> lo mod 4096 = 0 -> 0 <= lo -> hi <= 2^64 -> lo <= a -> b <= hi ->
  pages_budgeted (aSc s) a b.
Proof. intros s lo hi a b Hin Hal Hlo Hhi Ha Hb z Hz. eapply aS_intro_A0; eauto. lia. Qed.

(* [comment removed for export] *)
Lemma In_A0_S0 : forall iv, In iv (S0_ivs5 E0 FSB0) -> In iv (A0 E0 FSB0 HR0).
Proof. intros iv H. unfold A0. apply in_app_iff. left. exact H. Qed.

Lemma pgdn_sh_shadow_page : forall x, pgdn (sh x) = shadow_page x.
Proof.
  intros x. unfold pgdn, sh, shadow_page, round_down, mem_to_shadow. rewrite A_SB_val.
  change kShadowBase with 2147450880. change kPageSize with 4096. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma page_base_of_shadow : forall a', 0 <= a' < 2^47 ->
  page_base_of (A_SB + a' / 8) = Z_to_bv 64 (shadow_page a') /\ 0 <= shadow_page a' < 2^45 /\ shadow_page a' mod 4096 = 0.
Proof.
  intros a' Ha. unfold page_base_of, shadow_page, round_down, mem_to_shadow. rewrite page_size_val, A_SB_val.
  change kShadowBase with 2147450880. change kPageSize with 4096.
  split; [reflexivity|]. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma pages_budgeted_block : forall {P D} s mo b,
  AWf (aps_env s) P D (aps_alloc s) -> AKern (aps_env s) (aps_alloc s) mo -> ENVOK E0 FSB0 s -> res_ok (aps_alloc s) ->
  In (ab_addr b, ab_size b) (live_blocks (aps_alloc s)) -> 0 < ab_size b ->
  pages_budgeted (aSc s) (oshw_lo (ab_addr b)) (oshw_hi (ab_addr b) (ab_size b)).
Proof.
  intros P D s mo b WF K ENV RES Hin Hn z Hz. pose proof ceil_range as CR.
  pose proof (live_block_geom s mo b WF K ENV Hin) as ((G1 & G2 & G3) & GA & _). unfold A_IMG_END in G1.
  pose proof ENV as (_ & _ & _ & _ & _ & _ & _ & _ & _ & EE & EFS & _).
  destruct (live_blocks_chunk _ _ _ Hin) as (cb & cm & i & Hcm & HA & Hsz & Hst).
  pose proof (chunk_user_in_block _ _ _ _ _ _ WF Hcm) as (U1 & U2 & U3).
  pose proof (chunk_block_committed _ _ _ _ _ _ WF Hcm) as BC.
  unfold oshw_lo, oshw_hi in Hz.
  (* [comment removed for export] *)
  set (a' := ab_addr b + 8 * (z - (A_SB + ab_addr b / 8))).
  assert (Ha' : ab_addr b <= a' < ab_addr b + ab_size b) by (subst a'; clear -Hz GA Hn; rewrite A_SB_val in *; Z.div_mod_to_equations; lia).
  assert (Ez : z = A_SB + a' / 8).
  { subst a'. rewrite A_SB_val in *. clear -Hz GA Hn. Z.div_mod_to_equations. lia. }
  rewrite Ez. destruct (page_base_of_shadow a' ltac:(clear -Ha' G1 G2 CR; lia)) as (-> & R1 & R2).
  unfold aS, A_policy5.aS, A_policy5.aSa. rewrite unsigned_lit by lia. split; [exact R2|].
  unfold user_lo, user_hi, blk_lo, blk_hi in *. rewrite HA, Hsz in *.
  destruct (cm_prim cm) as [c|] eqn:PC.
  - (* [comment removed for export] *)
    left. pose proof (prim_block_in_space _ _ _ _ _ _ c WF Hcm PC) as [P1 P2].
    destruct BC as (Hc & B1 & B2).
    exists (pgdn (sh (ae_space_beg E0)), pgup (sh (ae_space_beg E0 + 2^37))). split.
    + apply In_A0_S0. cbn. tauto.
    + cbn [fst snd]. rewrite <- EE.
      change kRegionSize with 4294967296 in P1. change kSpaceSize with 137438953472 in P2.
      assert (L1 : shadow_page (ae_space_beg (aps_env s)) <= shadow_page a') by (apply shadow_page_mono; lia).
      assert (L2 : shadow_page a' <= shadow_page (ae_space_beg (aps_env s) + 137438953472 - 1)) by (apply shadow_page_mono; lia).
      rewrite pgdn_sh_shadow_page. pose proof (pgup_ge (sh (ae_space_beg (aps_env s) + 2^37))) as L3.
      assert (L4 : shadow_page (ae_space_beg (aps_env s) + 137438953472 - 1) < sh (ae_space_beg (aps_env s) + 2^37)).
      { unfold shadow_page, round_down, mem_to_shadow, sh. change kShadowBase with 2147450880. change kPageSize with 4096.
        rewrite A_SB_val. pose proof (ak_resv_geom _ _ _ K) as (_ & AL & _).
        clear -AL. Z.div_mod_to_equations. lia. }
      lia.
  - (* [comment removed for export] *)
    destruct BC as (sc & Hsc & B1 & B2).
    destruct WF as (WE & WR & WC & WK & WQ & WS & WD). destruct WS as (_ & _ & WS3 & _).
    destruct (WS3 sc Hsc) as (M1 & M2 & M3 & M4 & M5 & M6 & M7). change kPageSize with 4096 in *.
    assert (Hin' : sc_map_beg sc <= a' < sc_map_beg sc + sc_map_size sc) by lia.
    destruct (Z.ltb_spec (sc_map_size sc) kBigMapSize) as [SM|BG].
    + (* [comment removed for export] *)
      right. right. left. apply (RES sc Hsc). unfold residue_pages.
      replace (sc_map_size sc <? kBigMapSize) with true by (symmetry; apply Z.ltb_lt; exact SM).
      apply shadow_page_in_hull. exact Hin'.
    + pose proof (shadow_page_big (sc_map_beg sc) (sc_map_size sc) a' M1 M4 Hin') as BIG.
      destruct (remap_range (sc_map_beg sc) (sc_map_size sc)) as [pb plen] eqn:RR.
      destruct BIG as [[I1 I2] | BD].
      * right. left. exists sc. split; [exact Hsc|]. split; [lia|]. rewrite RR. cbn [fst snd]. change kPageSize with 4096 in I2.
        lia.
      * right. right. left. apply (RES sc Hsc). unfold residue_pages.
        replace (sc_map_size sc <? kBigMapSize) with false by (symmetry; apply Z.ltb_ge; lia).
        cbn. destruct BD as [-> | ->]; tauto.
Qed.

(* [comment removed for export] *)
Lemma fframe_geom : forall E fsbase fs LF m N ff,
  FSRep asegs E fsbase fs LF m -> In (N, ff) LF ->
  0 <= N <= 1 /\ fsbase + 4096 <= ff /\ ff + ff_bytes N <= fsbase + 11571200
  /\ fsbase + 4096 <= aflagB E fsbase N ff /\ aflagB E fsbase N ff + 1 <= fsbase + 11571200.
Proof.
  intros E fsbase fs LF m N ff R Hin.
  destruct R as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RL).
  destruct (RL N ff Hin) as (pos & [PC PP] & ->). clear RL Hin.
  rewrite aflagB_frame by lia.
  unfold fs_frame_addr, fs_frames_base, fs_flag_addr, fs_flags_base, fs_flags_off, fs_frame_bytes, fs_nframes,
         kFsFlagsOffset, kFsLog, kFsMinFrameLog, ff_bytes in *.
  assert (HN : N = 0 \/ N = 1) by lia.
  destruct HN as [-> | ->];
    repeat match goal with
    | |- context [?a ^ ?e] => let v := eval vm_compute in (a ^ e) in change (a ^ e) with v
    | |- context [Z.shiftl ?a ?b] => let v := eval vm_compute in (Z.shiftl a b) in change (Z.shiftl a b) with v
    | H : context [?a ^ ?e] |- _ => let v := eval vm_compute in (a ^ e) in change (a ^ e) with v in H
    end; cbn in *; lia.
Qed.

Ltac zground :=
  repeat match goal with
    | |- context [?a ^ ?e] => let v := eval vm_compute in (a ^ e) in change (a ^ e) with v
    | |- context [Z.shiftl ?a ?b] => let v := eval vm_compute in (Z.shiftl a b) in change (Z.shiftl a b) with v
    | H : context [?a ^ ?e] |- _ => let v := eval vm_compute in (a ^ e) in change (a ^ e) with v in H
    | H : context [Z.shiftl ?a ?b] |- _ => let v := eval vm_compute in (Z.shiftl a b) in change (Z.shiftl a b) with v in H
    end.

(* [comment removed for export] *)
Lemma fframe_pos : forall E fsbase fs LF m N ff,
  FSRep asegs E fsbase fs LF m -> In (N, ff) LF ->
  exists pos, 0 <= pos /\ fsbase mod 4096 = 0 /\ 0x603000 <= fsbase /\ fsbase + 11571200 <= alloc_ceiling /\
    (fsbase + 11571200 <= FS_SB - 4096 \/ FS_SB + 2^44 <= fsbase) /\
    ((N = 0 /\ pos < 16384 /\ ff = fsbase + 36864 + 64 * pos /\ forall E', aflagB E' fsbase N ff = fsbase + 4096 + pos)
     \/ (N = 1 /\ pos < 8192 /\ ff = fsbase + 1085440 + 128 * pos /\ forall E', aflagB E' fsbase N ff = fsbase + 20480 + pos)).
Proof.
  intros E fsbase fs LF m N ff R Hin.
  destruct R as (P1 & P2 & P3 & P4 & _ & _ & _ & _ & _ & _ & RL).
  destruct (RL N ff Hin) as (pos & [PC PP] & ->). clear RL Hin.
  exists pos. split; [lia|]. split; [exact P1|]. split; [exact P2|]. split; [unfold kFsBytes in P3; exact P3|].
  split; [unfold kFsBytes in P4; exact P4|].
  assert (FLQ : forall E', aflagB E' fsbase N (fs_frame_addr fsbase N pos) = fs_flag_addr fsbase N pos)
    by (intros E'; apply aflagB_frame; lia).
  revert FLQ.
  unfold fs_frame_addr, fs_frames_base, fs_flag_addr, fs_flags_base, fs_flags_off, fs_frame_bytes, fs_nframes,
         kFsFlagsOffset, kFsLog, kFsMinFrameLog in *.
  assert (HN : N = 0 \/ N = 1) by lia.
  destruct HN as [-> | ->]; zground; cbn in *; intros FLQ; [left|right]; (split; [lia|]); (split; [lia|]); (split; [lia|]);
    intros E'; rewrite FLQ; lia.
Qed.

(* [comment removed for export] *)
Lemma live_block_fs_sep : forall {P D} s mo A n,
  AWf (aps_env s) P D (aps_alloc s) -> AKern (aps_env s) (aps_alloc s) mo -> ENVOK E0 FSB0 s ->
  In (A, n) (live_blocks (aps_alloc s)) ->
  A + n <= aps_fsbase s \/ aps_fsbase s + 11571200 <= A.
Proof.
  intros P D s mo A n WF K Henv Hin.
  destruct Henv as (_ & _ & _ & _ & _ & _ & EIN & EF1 & EF2 & _).
  destruct (live_blocks_chunk _ _ _ Hin) as (cb & cm & i & Hcm & HA & Hn & Hst).
  pose proof (chunk_user_in_block _ _ _ _ _ _ WF Hcm) as (U1 & U2 & U3).
  pose proof (chunk_block_committed _ _ _ _ _ _ WF Hcm) as BC.
  unfold user_lo, user_hi, blk_lo in *. rewrite HA, Hn in *.
  destruct WF as (WE & WR & WC & WK & WQ & WS & WD).
  unfold blk_hi in *.
  destruct (cm_prim cm) as [c|].
  - destruct BC as (Hc & B1 & B2).
    destruct WR as [_ WR]. destruct (WR c Hc) as (R1 & R2 & R3 & _).
    pose proof (wf_env_resv _ WE) as (WE2 & WE3 & WE4 & WE5 & _). pose proof (wf_env_fs _ WE) as (_ & _ & _ & _ & WEfs & _).
    rewrite EF1, EF2 in WEfs. unfold kFsBytes in WEfs.
    unfold region_of, region_beg in *.
    change kRegionSize with 4294967296 in *. change kFreeArrayOffset with 3758096384 in R3.
    change kSpaceSize with 137438953472 in *. change kLargestClassID with 30 in Hc.
    assert (c * 4294967296 <= 30 * 4294967296) by nia.
    assert (0 <= c * 4294967296) by nia.
    lia.
  - destruct BC as (sc & Hsc & B1 & B2).
    destruct WS as (_ & _ & WS3 & _). destruct (WS3 sc Hsc) as (M1 & M2 & M3 & M4 & M5 & M6 & M7).
    destruct (M7 _ EIN) as [X|X]; cbn [fst snd] in X; unfold kFsBytes in X; change kPageSize with 4096 in *; lia.
Qed.

Lemma oshw_hi_0_47 : oshw_hi 0 (2^47) = FS_SB + 2^44.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma AHK_y_layout : forall s LB LF m mo, AHKc s LB LF m mo ->
    (forall f, In f LF -> amem (snd f) (ff_bytes (fst f)) /\ snd f + ff_bytes (fst f) <= alloc_ceiling /\ snd f mod ff_bytes (fst f) = 0 /\ 0 <= fst f <= 1
                          /\ amem (aflagB E0 FSB0 (fst f) (snd f)) 1 /\ aflagB E0 FSB0 (fst f) (snd f) + 1 <= alloc_ceiling)
    /\ (forall f b, In f LF -> In b LB ->
          (ab_addr b + ab_size b <= snd f \/ snd f + ff_bytes (fst f) <= ab_addr b)
          /\ (ab_addr b + ab_size b <= aflagB E0 FSB0 (fst f) (snd f) \/ aflagB E0 FSB0 (fst f) (snd f) + 1 <= ab_addr b))
    /\ (forall f1 f2, In f1 LF -> In f2 LF -> snd f1 <> snd f2 ->
          snd f1 + ff_bytes (fst f1) <= snd f2 \/ snd f2 + ff_bytes (fst f2) <= snd f1).
Proof.
  intros s LB LF m mo H. ahk_open H. pose proof ceil_range as CR.
  pose proof Henv as Henv0.
  destruct Henv as (_ & _ & _ & _ & _ & _ & EIN & EF1 & EF2 & EE & EFS & _).
  rewrite EFS in Hfs. unfold ff_bytes, amem, FS_SB.
  split; [| split].
  - intros [N ff] Hin. cbn [fst snd].
    destruct (fframe_pos _ _ _ _ _ _ _ Hfs Hin) as (pos & P0 & P1 & P2 & P3 & P4 & CASES). unfold FS_SB in P4.
    destruct CASES as [(-> & PP & -> & FL) | (-> & PP & -> & FL)]; rewrite FL; zground; cbn;
      (repeat split; try lia); clear -P0 P1 P2 P3 P4 PP CR; Z.div_mod_to_equations; lia.
  - intros [N ff] b Hin Hb. cbn [fst snd].
    pose proof (live_block_fs_sep s mo (ab_addr b) (ab_size b) Hwf Hkern Henv0 (blocks_match_In _ _ _ Hbm Hb)) as SEP.
    rewrite EFS in SEP.
    destruct (fframe_pos _ _ _ _ _ _ _ Hfs Hin) as (pos & P0 & P1 & P2 & P3 & P4 & CASES).
    destruct CASES as [(-> & PP & -> & FL) | (-> & PP & -> & FL)]; rewrite FL; zground; cbn; split; clear -SEP P0 PP; lia.
  - intros [N1 ff1] [N2 ff2] H1 H2 Hne. cbn [fst snd] in *.
    destruct (fframe_pos _ _ _ _ _ _ _ Hfs H1) as (pos1 & Q0 & _ & _ & _ & _ & C1).
    destruct (fframe_pos _ _ _ _ _ _ _ Hfs H2) as (pos2 & R0 & _ & _ & _ & _ & C2).
    destruct C1 as [(-> & PP1 & -> & _) | (-> & PP1 & -> & _)];
    destruct C2 as [(-> & PP2 & -> & _) | (-> & PP2 & -> & _)]; zground; cbn; clear -Q0 R0 PP1 PP2 Hne; lia.
Qed.

End Bundle.
End RC__1.
