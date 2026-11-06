(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import base decidable list gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling PropExec MState Mem Cells Frame Arr.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import LiaA AImages AImageFacts LazyModel NodesA Shadow BackingAlgebraA.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import StdioBase STree.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanConsts AsanSizeClass AsanState AsanLayout AsanOps AsanHoare AsanRep AsanFakeStack AsanPS AsanKern AsanClient AsanDepot AsanBudget AsanBudget2 AsanGap AsanSlack.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import B_base B_alloc_iface B_iface B_live B_policy5 B_budget5 B_slack5 BI_shadow BI_lowshadow BYajlRep BYajl_iface BF_place BF_fakestack_rep B_bundle B_benv5 B_bframe.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanRepFrame.
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
Hypothesis RT_fsenv : forall m, RTMisc E0 m -> FSEnv bsegs E0 FSB0 PL0 m.
Variable so_fp : Z -> Prop.
Hypothesis StdioRep_agree : forall so m m', StdioRep so m -> (forall a, so_fp a -> m' (wa a) = m (wa a)) -> StdioRep so m'.
Hypothesis so_fp_where : forall a, so_fp a -> 0x10000 <= a < 0x603000 /\ ~ cl_cells a /\ ~ in_cells img_mut a.
Hypothesis StdioRep_buf : forall so m, StdioRep so m -> Z.of_nat (length (so_buf so)) <= 1024.
(* [comment removed for export] *)
Ltac clear_frame_kit := clear StdioRep_buf so_fp_where StdioRep_agree so_fp RT_fsenv rt_fp_where RTMisc_agree rt_fp.
Ltac clear_all_hyps := clear_frame_kit; clear PL0OK ENV0.

Ltac zground :=
  repeat match goal with
    | |- context [?a ^ ?e] => let v := eval vm_compute in (a ^ e) in change (a ^ e) with v
    | |- context [Z.shiftl ?a ?b] => let v := eval vm_compute in (Z.shiftl a b) in change (Z.shiftl a b) with v
    | H : context [?a ^ ?e] |- _ => let v := eval vm_compute in (a ^ e) in change (a ^ e) with v in H
    | H : context [Z.shiftl ?a ?b] |- _ => let v := eval vm_compute in (Z.shiftl a b) in change (Z.shiftl a b) with v in H
    end.
(* [comment removed for export] *)
#[local] Notation live_block_geom := (B_bframe.live_block_geom E0 FSB0).
#[local] Notation live_block_fs_sep := (B_bframe.live_block_fs_sep E0 FSB0).
#[local] Notation lazy_disjoint_img := (B_bframe.lazy_disjoint_img E0 FSB0 ENV0).
#[local] Notation lazy_disjoint_stack := (B_bframe.lazy_disjoint_stack E0 FSB0).
#[local] Notation lazy_disjoint_fs := (B_bframe.lazy_disjoint_fs E0 FSB0).
#[local] Notation lazy_disjoint_block := (B_bframe.lazy_disjoint_block E0 FSB0).
#[local] Notation lazy_disjoint_gen := (B_bframe.lazy_disjoint_gen E0 FSB0).
#[local] Notation pages_budgeted_block := (B_bframe.pages_budgeted_block E0 FSB0 HR0).
#[local] Notation pages_budgeted_A0 := (B_bframe.pages_budgeted_A0 E0 FSB0 HR0).
#[local] Notation AHK_blocks := (B_bframe.AHK_blocks StdioRep RTMisc E0 FSB0 HR0 L0 RES0 EB0).
#[local] Notation AHK_block_oshadow := (B_bframe.AHK_block_oshadow StdioRep RTMisc E0 FSB0 HR0 L0 RES0 EB0).
#[local] Notation AHK_adrv_policy := (B_bframe.AHK_adrv_policy StdioRep RTMisc E0 FSB0 HR0 L0 RES0 EB0 ENV0).
#[local] Notation AHK_y_layout := (B_bframe.AHK_y_layout StdioRep RTMisc E0 FSB0 HR0 L0 RES0 EB0).
#[local] Notation In_A0_S0 := (B_bframe.In_A0_S0 E0 FSB0 HR0).

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma outside_of_Forall : forall (Pw : Z * Z -> Prop) W x,
  Forall Pw W -> (forall iv, Pw iv -> ~ (fst iv <= x < snd iv)) -> outside W x.
Proof.
  intros Pw W x FW H. induction W as [|[a b] W IH]; cbn; [exact I|].
  inversion FW as [|y l F1 F2]; subst. split; [exact (H _ F1)| apply IH; exact F2].
Qed.

(* [comment removed for export] *)
Definition cl_write_ok (LB : list ablock) (LF : list fblock) (iv : Z * Z) : Prop :=
  alloc_ceiling <= fst iv
  \/ (exists b, In b LB /\ ab_addr b <= fst iv /\ snd iv <= ab_addr b + ab_size b)
  \/ (exists f, In f LF /\ snd f <= fst iv /\ snd iv <= snd f + ff_bytes (fst f))
  \/ (exists f, In f LF /\ oshw_lo (snd f) <= fst iv /\ snd iv <= oshw_lo (snd f) + Z.shiftl 8 (fst f))
  \/ (c_initialized ACONSTS <= fst iv /\ snd iv <= c_initialized ACONSTS + 32)
  \/ (c_errno ACONSTS <= fst iv /\ snd iv <= c_errno ACONSTS + 4)
  \/ (0x5d0c10 <= fst iv /\ snd iv <= 0x5d0c10 + 65536)         (* [comment removed for export] *)
  \/ (c_initialized ACONSTS + 0x20990 <= fst iv /\ snd iv <= c_initialized ACONSTS + 0x20990 + 544).   (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma not_outside_In : forall W x, ~ outside W x -> exists iv, In iv W /\ fst iv <= x < snd iv.
Proof.
  induction W as [|[lo hi] W IH]; cbn; intros x H.
  - exfalso. exact (H I).
  - destruct (Z_le_dec lo x); [destruct (Z_lt_dec x hi)|].
    + exists (lo, hi). cbn. auto.
    + destruct (IH x) as (iv & Hiv & R); [intros O; apply H; split; [lia| exact O]|]. exists iv. auto.
    + destruct (IH x) as (iv & Hiv & R); [intros O; apply H; split; [lia| exact O]|]. exists iv. auto.
Qed.

Lemma munch_changed : forall W m m' x, munch W m m' -> 0 <= x < 2^64 -> m' (wa x) <> m (wa x) ->
  exists iv, In iv W /\ fst iv <= x < snd iv.
Proof.
  intros W m m' x MU Hx NE. apply not_outside_In. intros O. apply NE. apply MU. rewrite wa_unsigned by lia. exact O.
Qed.

(* [comment removed for export] *)
Definition cl_byte (s : aps) (LB : list ablock) (LF : list fblock) (x : Z) : Prop :=
  alloc_ceiling <= x
  \/ (exists b, In b LB /\ ab_addr b <= x < ab_addr b + ab_size b)
  \/ (aps_fsbase s + 36864 <= x < aps_fsbase s + 11571200
      /\ exists f, In f LF /\ snd f <= x < snd f + ff_bytes (fst f))
  \/ (exists g, x = kShadowBase + g /\ aps_fsbase s + 36864 <= 8 * g /\ 8 * g < aps_fsbase s + 11571200)
  \/ cl_cells x.

Lemma cl_write_byte : forall s LB LF m iv x,
  FSRep bsegs (aps_env s) (aps_fsbase s) (aps_fs s) LF m ->
  cl_write_ok LB LF iv -> fst iv <= x < snd iv -> cl_byte s LB LF x.
Proof.
  clear_all_hyps.
  intros s LB LF m iv x FS W Hx. unfold cl_byte, cl_cells. unfold cl_write_ok in W. cbn [c_initialized c_errno ACONSTS] in *.
  destruct W as [W|[(b & Hb & W1 & W2)|[(f & Hf & W1 & W2)|[(f & Hf & W1 & W2)|[[W1 W2]|[[W1 W2]|[[W1 W2]|[W1 W2]]]]]]]];
    [| | | | right; right; right; right; lia| right; right; right; right; lia| right; right; right; right; lia| right; right; right; right; lia].
  - left. lia.
  - right; left. exists b. split; [exact Hb| lia].
  - right; right; left. destruct f as [N ff]. cbn [fst snd] in *.
    destruct (fframe_pos _ _ _ _ _ _ _ FS Hf) as (pos & P0 & P1 & P2 & P3 & P4 & CASES).
    split.
    + unfold ff_bytes in *. destruct CASES as [(-> & PP & -> & _)|(-> & PP & -> & _)]; zground; cbn in *; lia.
    + exists (N, ff). cbn. split; [exact Hf| lia].
  - right; right; right; left. destruct f as [N ff]. cbn [fst snd] in *. unfold oshw_lo in *.
    destruct (fframe_pos _ _ _ _ _ _ _ FS Hf) as (pos & P0 & P1 & P2 & P3 & P4 & CASES).
    exists (x - kShadowBase). split; [lia|]. unfold kShadowBase. rewrite A_SB_val in *.
    destruct CASES as [(-> & PP & -> & _)|(-> & PP & -> & _)]; zground; cbn in *; Z.div_mod_to_equations; lia.
Qed.

(* [comment removed for export] *)
Lemma AK_blocks_sep : forall {P D} s mo,
  AWf (aps_env s) P D (aps_alloc s) -> AKern (aps_env s) (aps_alloc s) mo -> ENVOK E0 FSB0 s ->
  blocks_sep (aps_env s) (aps_alloc s).
Proof.
  clear_frame_kit. clear PL0OK.
  intros P D s mo WF K Henv.
  destruct Henv as (V1 & V2 & V3 & V4 & V5 & V6 & EIN & EF1 & EF2 & EE & EFS & _).
  destruct ENV0 as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & _). rewrite <- EE in *.
  destruct WF as (WE & _ & _ & _ & _ & WS & _). destruct WS as (_ & _ & WS3 & _).
  assert (SECR : forall sc r, In sc (as_sec (aps_alloc s)) -> In r (ae_reserved (aps_env s)) ->
                 sc_map_beg sc + sc_map_size sc <= fst r \/ fst r + snd r <= sc_map_beg sc).
  { intros sc r Hsc Hr. destruct (WS3 sc Hsc) as (_ & _ & _ & _ & _ & _ & RSV). exact (RSV _ Hr). }
  pose proof (wf_env_fs _ WE) as (WEfs & _). pose proof (wf_env_img _ WE) as (WEimg & _).
  pose proof (ak_store_sep _ _ _ K) as (S1 & S2 & S3 & S4 & S5).
  pose proof N3 as (D1 & D2 & D3). unfold A_IMG_END in D1. unfold A_LOWAPP_END, A_HIGH_BEG in D3.
  intros b len [[Hb ->]|[Hb ->]].
  - destruct Hb as [<-|Hb].
    + split; [| split; [exact (proj1 (proj2 N3))| split; [exact N7| split; [| split; [exact N8| exact N5]]]]].
      * unfold app_mem, kLowAppEnd, kLowShadowMapBeg, kShadowBase, kPageSize. rewrite kHighMemBeg_val.
        unfold kDepotNodeBlockBytes in *. clear -D1 D2 D3. lia.
      * intros sc Hsc. destruct (SECR sc _ Hsc N1); cbn [fst snd] in *; lia.
    + destruct (ak_blocks_sep _ _ _ K b kDepotNodeBlockBytes (or_introl (conj Hb eq_refl))) as (B1 & B2 & _ & B3 & B4 & B5).
      split; [exact B1|]. split; [exact B2|]. split; [change 0x2000011000 with kResvLen; exact B3|]. split; [exact B4|].
      split; [destruct (B5 _ WEfs); cbn [fst snd] in *; lia|].
      unfold img_sep. exact (B5 _ WEimg).
  - destruct Hb as [<-|Hb].
    + change (2^23) with kStoreBlockBytes in *.
      split; [exact V1|]. split; [exact V2|]. split; [change 0x2000011000 with kResvLen; exact S1|]. split; [exact S2|].
      split; [rewrite EF1, EF2; clear -V6; lia| exact N6].
    + destruct (ak_blocks_sep _ _ _ K b kStoreBlockBytes (or_intror (conj Hb eq_refl))) as (B1 & B2 & _ & B3 & B4 & B5).
      split; [exact B1|]. split; [exact B2|]. split; [change 0x2000011000 with kResvLen; exact B3|]. split; [exact B4|].
      split; [destruct (B5 _ WEfs); cbn [fst snd] in *; lia|].
      unfold img_sep. exact (B5 _ WEimg).
Qed.

(* [comment removed for export] *)
Lemma IMG_IN_of : forall s, ENVOK E0 FSB0 s -> forall r, In r (arep_img_ranges (aps_env s) ++ depot_static (aps_env s)) ->
  fst (ae_img (aps_env s)) <= fst r /\ fst r + snd r <= fst (ae_img (aps_env s)) + snd (ae_img (aps_env s)).
Proof.
  clear_frame_kit. clear PL0OK.
  intros s Henv r Hr. destruct Henv as (_ & _ & _ & _ & _ & _ & _ & _ & _ & EE & _ & EI1 & EI2).
  destruct ENV0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & IMG_LOW & _). rewrite EE in Hr. pose proof (IMG_LOW r Hr). rewrite EI1. lia.
Qed.

(* [comment removed for export] *)
Lemma cl_byte_not_fp : forall s LB LF m mo x,
  AHKc s LB LF m mo -> cl_byte s LB LF x -> ~ arep_fp (aps_env s) (DepotFP (aps_env s)) (aps_alloc s) x.
Proof.
  intros s LB LF m mo x H CB. pose proof H as H0. ahk_open H. pose proof ceil_range as CR.
  pose proof (AK_blocks_sep s mo Hwf Hkern Henv) as BS. pose proof (IMG_IN_of s Henv) as IMG_IN.
  pose proof (DepotFP_where (aps_env s)) as DW.
  destruct Henv as (V1 & V2 & V3 & V4 & V5 & V6 & EIN & EF1 & EF2 & EE & EFS & EI1 & EI2).
  destruct ENV0 as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & IMG_LOW & IMG_CL & _).
  destruct CB as [X|[(b & Hb & X)|[[X _]|[(g & -> & X1 & X2)|X]]]].
  - apply (fp_stack_free _ _ [] [] IMG_IN DW); [exact Hwf| exact BS| exact X].
  - destruct (live_blocks_chunk _ _ _ (blocks_match_In _ _ _ Hbm Hb)) as (cb & cm & i & Hcm & HA & Hn & Hst).
    apply (fp_live_free _ _ [] [] IMG_IN DW _ x cb cm i Hwf BS Hcm Hst). lia.
  - apply (fp_fs_free _ _ [] [] IMG_IN DW _ _ Hwf BS).
    unfold in_fakestack. rewrite EF1, EF2. apply andb_true_iff. split; [apply Z.leb_le| apply Z.ltb_lt]; unfold kFsBytes; lia.
  - apply (fp_fs_shadow_free _ _ [] [] IMG_IN DW _ _ Hwf BS).
    unfold in_fakestack. rewrite EF1, EF2. apply andb_true_iff. split; [apply Z.leb_le| apply Z.ltb_lt]; unfold kFsBytes; lia.
  - apply (fp_img_free _ _ [] [] IMG_IN DW _ _ Hwf BS).
    + unfold in_img. rewrite EI1. apply andb_true_iff. unfold cl_cells in X. cbn [c_initialized c_errno ACONSTS] in X.
      split; [apply Z.leb_le| apply Z.ltb_lt]; lia.
    + intros (r & Hr & R). rewrite <- EE in IMG_CL. exact (proj1 (IMG_CL r x Hr R) X).
Qed.

(* [comment removed for export] *)
Lemma live_block_reserved_sep : forall {P D} s mo A n r0 rl,
  AWf (aps_env s) P D (aps_alloc s) -> AKern (aps_env s) (aps_alloc s) mo ->
  In (r0, rl) (ae_reserved (aps_env s)) ->
  (r0 + rl <= ae_resv_beg (aps_env s) \/ ae_resv_beg (aps_env s) + kResvLen <= r0) ->
  In (A, n) (live_blocks (aps_alloc s)) ->
  A + n <= r0 \/ r0 + rl <= A.
Proof.
  clear_all_hyps.
  intros P D s mo A n r0 rl WF K HR HD Hin.
  destruct (live_blocks_chunk _ _ _ Hin) as (cb & cm & i & Hcm & HA & Hn & Hst).
  pose proof (chunk_user_in_block _ _ _ _ _ _ WF Hcm) as (U1 & U2 & U3).
  pose proof (chunk_block_committed _ _ _ _ _ _ WF Hcm) as BC.
  unfold user_lo, user_hi, blk_lo in *. rewrite HA, Hn in *.
  destruct WF as (WE & WR & WC & WK & WQ & WS & WD).
  unfold blk_hi in *.
  pose proof (wf_env_resv _ WE) as (_ & WE3 & WE4 & _). clear WE WC WK WQ WD K.
  change kResvLen with 0x2000011000 in HD.
  destruct (cm_prim cm) as [c|].
  - destruct BC as (Hc & B1 & B2).
    destruct WR as [_ WR]. destruct (WR c Hc) as (R1 & R2 & R3 & _). clear WR WS.
    unfold region_of, region_beg in *.
    change kRegionSize with 4294967296 in *. change kFreeArrayOffset with 3758096384 in R3.
    change kSpaceSize with 137438953472 in *. change kLargestClassID with 30 in Hc.
    assert (c * 4294967296 <= 30 * 4294967296) by nia.
    assert (0 <= c * 4294967296) by nia.
    lia.
  - destruct BC as (sc & Hsc & B1 & B2).
    destruct WS as (_ & _ & WS3 & _). destruct (WS3 sc Hsc) as (M1 & M2 & M3 & M4 & M5 & M6 & M7).
    destruct (M7 _ HR) as [X|X]; cbn [fst snd] in X; change kPageSize with 4096 in *; lia.
Qed.

Lemma live_block_iarena_sep : forall {P D} s mo A n,
  AWf (aps_env s) P D (aps_alloc s) -> AKern (aps_env s) (aps_alloc s) mo ->
  In (A, n) (live_blocks (aps_alloc s)) ->
  A + n <= ae_iarena (aps_env s) \/ ae_iarena (aps_env s) + kIArenaLen <= A.
Proof.
  clear_all_hyps.
  intros P D s mo A n WF K Hin. pose proof (wf_env_iarena _ (proj1 WF)) as (I1 & I2 & I3 & I4 & I5).
  eapply live_block_reserved_sep; [exact WF| exact K| exact I1| change kResvLen with 0x2000011000; exact I4| exact Hin].
Qed.

(* [comment removed for export] *)
Lemma live_block_reginfo_sep : forall {P D} s mo A n,
  AWf (aps_env s) P D (aps_alloc s) -> AKern (aps_env s) (aps_alloc s) mo ->
  In (A, n) (live_blocks (aps_alloc s)) ->
  (A + n <= ae_space_beg (aps_env s) + kSpaceSize \/ ae_space_beg (aps_env s) + kSpaceSize + kPageSize <= A)
  /\ ae_space_beg (aps_env s) mod 2^16 = 0 /\ ae_space_beg (aps_env s) + kSpaceSize + kPageSize <= alloc_ceiling.
Proof.
  clear_all_hyps.
  intros P D s mo A n WF K Hin.
  destruct (live_blocks_chunk _ _ _ Hin) as (cb & cm & i & Hcm & HA & Hn & Hst).
  pose proof (chunk_user_in_block _ _ _ _ _ _ WF Hcm) as (U1 & U2 & U3).
  pose proof (chunk_block_committed _ _ _ _ _ _ WF Hcm) as BC.
  unfold user_lo, user_hi, blk_lo in *. rewrite HA, Hn in *.
  destruct WF as (WE & WR & WC & WK & WQ & WS & WD).
  unfold blk_hi in *.
  pose proof (wf_env_resv _ WE) as (_ & WE3 & WE4 & WE5 & WE7). pose proof (wf_env_stack _ WE) as [_ WE1]. clear WE WC WK WQ WD K.
  change kSpaceSize with 137438953472 in *. change kPageSize with 4096 in *.
  split; [| split; [exact WE1| lia]].
  destruct (cm_prim cm) as [c|].
  - destruct BC as (Hc & B1 & B2).
    destruct WR as [_ WR]. destruct (WR c Hc) as (R1 & R2 & R3 & _). clear WR WS.
    unfold region_of, region_beg in *.
    change kRegionSize with 4294967296 in *. change kFreeArrayOffset with 3758096384 in R3. change kLargestClassID with 30 in Hc.
    assert (c * 4294967296 <= 30 * 4294967296) by nia.
    lia.
  - destruct BC as (sc & Hsc & B1 & B2).
    destruct WS as (_ & _ & WS3 & _). destruct (WS3 sc Hsc) as (M1 & M2 & M3 & M4 & M5 & M6 & M7).
    destruct (M7 _ WE7) as [X|X]; cbn [fst snd] in X; lia.
Qed.

(* [comment removed for export] *)
Lemma cl_byte_where : forall s LB LF m mo x,
  AHKc s LB LF m mo -> cl_byte s LB LF x ->
  (x < 0x603000 -> cl_cells x) /\ 0x10000 <= x
  /\ ~ (aps_fsbase s <= x < aps_fsbase s + 36864)
  /\ ~ rt_high E0 PL0 x.
Proof.
  clear_frame_kit. clear ENV0.
  unfold rt_high.
  intros s LB LF m mo x H CB. ahk_open H. pose proof ceil_range as CR.
  pose proof Henv as Henv0.
  destruct Henv as (V1 & V2 & V3 & V4 & V5 & V6 & EIN & EF1 & EF2 & EE & EFS & _).
  destruct PL0OK as ((c0 & cl & (CR1 & CR2 & CR3 & CR4 & CR5 & _) & CC1 & CC2) & (d0 & dl & (DR1 & DR2 & DR3 & DR4 & DR5 & _) & DD1 & DD2)
                     & (TR1 & TR2 & TR3 & TR4 & TR5 & _) & _).
  rewrite <- EE in CR1, CR4, CR5, DR1, DR4, DR5, TR1, TR4, TR5.
  pose proof (placed_s_num _ _ CR2 ltac:(clear -CC1 CC2; lia)) as (CN1 & CN2 & CN3 & CN4).
  pose proof (placed_s_num _ _ DR2 ltac:(clear -DD1 DD2; lia)) as (DN1 & DN2 & DN3 & DN4).
  pose proof (placed_s_num _ _ TR2 ltac:(clear; lia)) as (TN1 & TN2 & TN3 & TN4).
  destruct CR2 as (_ & CC & _). destruct DR2 as (_ & DC & _). destruct TR2 as (_ & TC & _).
  rewrite EF1, EF2 in *. unfold kFsBytes in *.
  destruct Hfs as (P1 & P2 & P3 & P4 & _). unfold FS_SB, kFsBytes in *.
  unfold cl_cells in *. cbn [c_initialized c_errno ACONSTS] in *.
  clear Hrep Hkvm Hres Hqb Hdi Hbinv Hicp Hyst Hlow Hrt Hso Hkm Hli Hbud Hmi Hycl Hss Hcs EIN.
  destruct CB as [X|[(b & Hb & X)|[[X _]|[(g & -> & X1 & X2)|X]]]].
  - clear Hwf Hbm Hkern Henv0 CR1 DR1 TR1. split; [clear -X CR; lia|]. split; [clear -X CR; lia|]. split; [clear -X P3; lia|]. clear -X TC CC DC CC1 CC2 DD1 DD2. lia.
  - pose proof (live_block_geom s mo b Hwf Hkern Henv0 (blocks_match_In _ _ _ Hbm Hb)) as ((G1 & G2 & G3) & _). unfold A_IMG_END in G1.
    pose proof (live_block_fs_sep s mo _ _ Hwf Hkern Henv0 (blocks_match_In _ _ _ Hbm Hb)) as FSS.
    pose proof (live_block_reserved_sep s mo _ _ _ _ Hwf Hkern TR1 TR4 (blocks_match_In _ _ _ Hbm Hb)) as TS.
    pose proof (live_block_reserved_sep s mo _ _ _ _ Hwf Hkern CR1 CR4 (blocks_match_In _ _ _ Hbm Hb)) as CS.
    pose proof (live_block_reserved_sep s mo _ _ _ _ Hwf Hkern DR1 DR4 (blocks_match_In _ _ _ Hbm Hb)) as DS.
    rewrite <- ?EE in *. rewrite <- ?EFS in FSS.
    split; [clear -G1 X; lia|]. split; [clear -G1 X; lia|]. split; [clear -FSS X; lia|]. clear -TS CS DS X CC1 CC2 DD1 DD2. lia.
  - rewrite <- ?EE in *.
    split; [clear -P2 X; lia|]. split; [clear -P2 X; lia|]. split; [clear -X; lia|]. clear -X TR5 CR5 DR5 CC1 CC2 DD1 DD2 EFS. subst. lia.
  - unfold kShadowBase in *. rewrite <- ?EE in *.
    split; [clear -X1 P2; lia|]. split; [clear -X1 P2; lia|]. split; [clear -X1 X2 P2 P3 P4 CR; lia|].
    clear -X1 X2 P2 P3 P4 CR TN4 CN4 DN4 CC1 CC2 DD1 DD2 TC CC DC. lia.
  - unfold cl_cells in X. cbn [c_initialized c_errno ACONSTS] in X.
    split; [clear -X; lia|]. split; [clear -X; lia|]. split; [clear -X P2 EFS; subst; lia|]. clear -X TN3 CN3 DN3 CC1 CC2 DD1 DD2. lia.
Qed.

(* [comment removed for export] *)
Lemma rt_high_range : forall a, rt_high E0 PL0 a -> 0x1000 <= a < alloc_ceiling /\ (a < 0x10000 \/ 0x603000 <= a).
Proof.
  clear_frame_kit. clear ENV0.
  intros a R. unfold rt_high in R.
  destruct PL0OK as ((c0 & cl & (CR1 & CR2 & _) & CC1 & CC2) & (d0 & dl & (DR1 & DR2 & _) & DD1 & DD2) & (TR1 & TR2 & _) & _).
  pose proof (placed_s_num _ _ CR2 ltac:(clear -CC1 CC2; lia)) as (CN1 & CN2 & CN3 & CN4).
  pose proof (placed_s_num _ _ DR2 ltac:(clear -DD1 DD2; lia)) as (DN1 & DN2 & DN3 & DN4).
  pose proof (placed_s_num _ _ TR2 ltac:(clear; lia)) as (TN1 & TN2 & TN3 & TN4).
  destruct CR2 as (_ & CC & _). destruct DR2 as (_ & DC & _). destruct TR2 as (_ & TC & _).
  lia.
Qed.

Lemma RTMisc_frame : forall m m' W,
  RTMisc E0 m -> munch W m m' -> wmono bsegs m m' -> (forall a, rt_fp a -> outside W a) -> RTMisc E0 m'.
Proof.
  intros m m' W H MU _ OUT. eapply RTMisc_agree; [exact H|]. intros a Ha. pose proof ceil_range as CR.
  assert (Ra : 0 <= a < 2^64).
  { destruct (rt_fp_where a Ha) as [(R & _)|R]; [lia|]. pose proof (rt_high_range a (rt_high2_high _ _ _ R)) as RR. lia. }
  apply MU. rewrite wa_unsigned by lia. apply OUT. exact Ha.
Qed.
Lemma StdioRep_frame : forall so m m' W,
  StdioRep so m -> munch W m m' -> wmono bsegs m m' -> (forall a, so_fp a -> outside W a) -> StdioRep so m'.
Proof.
  intros so m m' W H MU _ OUT. eapply StdioRep_agree; [exact H|]. intros a Ha.
  destruct (so_fp_where a Ha) as [Ra _]. apply MU. rewrite wa_unsigned by lia. apply OUT. exact Ha.
Qed.

(* [comment removed for export] *)
Lemma Forall_disjoint_from' : forall W lo0 hi0 A n,
  Forall (fun iv : Z * Z => snd iv <= lo0 \/ hi0 <= fst iv) W -> lo0 <= A -> A + n <= hi0 -> disjoint_from W A n.
Proof.
  intros W lo0 hi0 A n FW H1 H2. induction W as [|[lo hi] W IH]; cbn; [exact I|].
  inversion FW as [|x l F1 F2]; subst. cbn in F1. split; [lia| apply IH; exact F2].
Qed.

(* [comment removed for export] *)
Lemma cl_write_ok_high : forall s LB LF m mo iv,
  AHKc s LB LF m mo -> cl_write_ok LB LF iv -> 0x5d0c10 <= fst iv.
Proof.
  intros s LB LF m mo iv H W. pose proof H as H0. ahk_open H. pose proof ceil_range as CR.
  destruct W as [W|[(b & Hb & W1 & W2)|[(f & Hf & W1 & W2)|[(f & Hf & W1 & W2)|[[W1 W2]|[[W1 W2]|[[W1 W2]|[W1 W2]]]]]]]].
  - lia.
  - pose proof (live_block_geom s mo b Hwf Hkern Henv (blocks_match_In _ _ _ Hbm Hb)) as ((G1 & _) & _). unfold A_IMG_END in G1. lia.
  - destruct f as [N ff]. cbn [fst snd] in *.
    destruct (fframe_pos _ _ _ _ _ _ _ Hfs Hf) as (pos & P0 & P1 & P2 & P3 & P4 & CASES).
    unfold ff_bytes in *. destruct CASES as [(-> & PP & -> & _)|(-> & PP & -> & _)]; zground; lia.
  - destruct f as [N ff]. cbn [fst snd] in *. unfold oshw_lo in *. rewrite A_SB_val in *.
    destruct (fframe_pos _ _ _ _ _ _ _ Hfs Hf) as (pos & P0 & P1 & P2 & P3 & P4 & CASES).
    destruct CASES as [(-> & PP & -> & _)|(-> & PP & -> & _)]; zground; Z.div_mod_to_equations; lia.
  - cbn [c_initialized ACONSTS] in W1. lia.
  - cbn [c_errno ACONSTS] in W1. lia.
  - lia.
  - cbn [c_initialized ACONSTS] in W1. lia.
Qed.

Lemma Forall_cl_high : forall s LB LF m mo W,
  AHKc s LB LF m mo -> Forall (cl_write_ok LB LF) W ->
  Forall (fun iv : Z * Z => snd iv <= 0x140c80 \/ 0x5d0c10 <= fst iv) W.
Proof.
  intros s LB LF m mo W H FW. apply Forall_forall. intros iv Hiv. right.
  exact (cl_write_ok_high _ _ _ _ _ iv H (proj1 (Forall_forall _ _) FW iv Hiv)).
Qed.

(* [comment removed for export] *)
Lemma cl_write_ok_split : forall s LB LF m mo iv,
  AHKc s LB LF m mo -> cl_write_ok LB LF iv -> snd iv <= LSLO \/ LSHI <= fst iv.
Proof.
  intros s LB LF m mo iv H W. pose proof H as H0. ahk_open H. pose proof ceil_range as CR. unfold LSLO, LSHI.
  destruct W as [W|[(b & Hb & W1 & W2)|[(f & Hf & W1 & W2)|[(f & Hf & W1 & W2)|[[W1 W2]|[[W1 W2]|[[W1 W2]|[W1 W2]]]]]]]];
    [right| | | right| left; cbn [c_initialized ACONSTS] in W2; lia| left; cbn [c_errno ACONSTS] in W2; lia| left; lia
    | left; cbn [c_initialized ACONSTS] in W2; lia].
  - lia.
  - pose proof (live_block_geom s mo b Hwf Hkern Henv (blocks_match_In _ _ _ Hbm Hb)) as ((G1 & G2 & G3) & _).
    unfold A_LOWAPP_END, A_HIGH_BEG in G3. destruct G3; [left| right]; lia.
  - destruct f as [N ff]. cbn [fst snd] in *. unfold FS_SB in *.
    destruct (fframe_pos _ _ _ _ _ _ _ Hfs Hf) as (pos & P0 & P1 & P2 & P3 & P4 & CASES). unfold FS_SB in P4.
    unfold ff_bytes in *. destruct CASES as [(-> & PP & -> & _)|(-> & PP & -> & _)]; zground; cbn in *; (destruct P4; [left| right]; lia).
  - destruct f as [N ff]. cbn [fst snd] in *. unfold oshw_lo in *. rewrite A_SB_val in *.
    destruct (fframe_pos _ _ _ _ _ _ _ Hfs Hf) as (pos & P0 & P1 & P2 & P3 & P4 & CASES).
    destruct CASES as [(-> & PP & -> & _)|(-> & PP & -> & _)]; zground; Z.div_mod_to_equations; lia.
Qed.
Lemma Forall_cl_split : forall s LB LF m mo W,
  AHKc s LB LF m mo -> Forall (cl_write_ok LB LF) W ->
  Forall (fun iv : Z * Z => snd iv <= LSLO \/ LSHI <= fst iv) W.
Proof.
  intros s LB LF m mo W H FW. apply Forall_forall. intros iv Hiv.
  exact (cl_write_ok_split _ _ _ _ _ iv H (proj1 (Forall_forall _ _) FW iv Hiv)).
Qed.

(* [comment removed for export] *)
Lemma stk_wmono_high : forall m m' lo hi,
  stk bsegs m lo hi -> wmono bsegs m m' -> 0x603000 <= lo -> stk bsegs m' lo hi.
Proof.
  clear_all_hyps.
  intros m m' lo hi (H0 & H1 & H) WM Hlo. split; [exact H0|]. split; [exact H1|].
  intros a Ha. destruct (H a Ha) as [W _]. pose proof (WM _ W) as W'. split; [exact W'|].
  rewrite both_wview_overlay in W' by (rewrite wa_unsigned by lia; lia).
  destruct (m' (wa a)) as [b|] eqn:Eb; [| exfalso; exact (W' eq_refl)].
  exists b. unfold mrd. rewrite Eb. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma FSRep_frame_w : forall E fsbase fs LF m m',
  (forall a, fsbase <= a < fsbase + 36864 -> m' (wa a) = m (wa a)) ->
  wmono bsegs m m' ->
  FSRep bsegs E fsbase fs LF m -> FSRep bsegs E fsbase fs LF m'.
Proof.
  clear_all_hyps.
  intros E fsbase fs LF m m' HA WM FS.
  pose proof FS as (G1 & G2 & G3 & G4 & HH & HL & HG & HF & HW & ND & HLF).
  assert (AGR : forall A cs, fsbase <= A -> A + Z.of_nat (cells_size cs) <= fsbase + 36864 ->
                rw_cells bsegs m A cs -> rw_cells bsegs m' A cs).
  { intros A cs H1 H2 R. apply (rw_cells_agree_eq bsegs m m'); [| exact R]. intros a Ha. split; [apply HA; lia| apply WM]. }
  split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. split; [exact G4|].
  split. { intros cid Hc. destruct (HH cid Hc) as [h Hh]. exists h. apply AGR; [cbn; unfold kFsClasses in Hc; lia| cbn; unfold kFsClasses in Hc; lia| exact Hh]. }
  split. { apply AGR; [lia| cbn; lia| exact HL]. }
  split. { apply AGR; [lia| cbn; lia| exact HG]. }
  split. { intros cid pos Hp. pose proof (HF cid pos Hp) as R. destruct Hp as [Hc Hq].
           unfold fs_flag_addr, fs_flags_base, fs_flags_off, fs_nframes, kFsFlagsOffset, kFsLog, kFsMinFrameLog in *.
           assert (HN : cid = 0 \/ cid = 1) by lia.
           destruct HN as [-> | ->]; zground; cbn -[rw_cells flag_byte] in *; (apply AGR; [lia| cbn; lia| exact R]). }
  split. { intros cid pos Hp. destruct (HW cid pos Hp) as [W1 W2]. destruct Hp as [Hc Hq].
           unfold fs_frame_addr, fs_frames_base, fs_frame_bytes, fs_nframes, kFsFlagsOffset, kFsLog, kFsMinFrameLog, fs_shadow, FS_SB in *.
           assert (HN : cid = 0 \/ cid = 1) by lia.
           destruct HN as [-> | ->]; zground; cbn -[stk Z.add Z.mul Z.div] in *; split;
             (eapply stk_wmono_high; [eassumption| exact WM| clear -G2 Hq; Z.div_mod_to_equations; lia]). }
  split; [exact ND| exact HLF].
Qed.

(* [comment removed for export] *)
Lemma asan_ro_addr_false_data : forall x : word, 0xa5000 <= bv_unsigned x -> ro_addr bsegs x = false.
Proof.
  clear_all_hyps.
  intros x Hx. pose proof (bvu64 x).
  destruct (Z_lt_dec (bv_unsigned x) 0x603000); [| apply both_ro_addr_false; lia].
  unfold ro_addr, bsegs, AsanUbsan.M.loaded_segments, AsanUbsan.AsanUbsan_loaded_segments. cbn [find_segment].
  replace (Z.of_N (seg_base AsanUbsan.AsanUbsan_segment_000)) with 0x10000%Z by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size AsanUbsan.AsanUbsan_segment_000)) with 0x21000%Z by (vm_compute; reflexivity).
  replace (Z.of_N (seg_base AsanUbsan.AsanUbsan_segment_001)) with 0x31000%Z by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size AsanUbsan.AsanUbsan_segment_001)) with 0x74000%Z by (vm_compute; reflexivity).
  replace (Z.of_N (seg_base AsanUbsan.AsanUbsan_segment_002)) with 0xa5000%Z by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size AsanUbsan.AsanUbsan_segment_002)) with 0x2000%Z by (vm_compute; reflexivity).
  replace (Z.of_N (seg_base AsanUbsan.AsanUbsan_segment_003)) with 0xa7000%Z by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size AsanUbsan.AsanUbsan_segment_003)) with 0x55c000%Z by (vm_compute; reflexivity).
  destruct (Z.leb_spec0 0x10000 (bv_unsigned x)); destruct (Z.leb_spec0 (bv_unsigned x + 1) (0x10000 + 0x21000)); cbn [andb]; try lia.
  all: destruct (Z.leb_spec0 0x31000 (bv_unsigned x)); destruct (Z.leb_spec0 (bv_unsigned x + 1) (0x31000 + 0x74000)); cbn [andb]; try lia.
  all: destruct (Z.leb_spec0 0xa5000 (bv_unsigned x)); destruct (Z.leb_spec0 (bv_unsigned x + 1) (0xa5000 + 0x2000)); cbn [andb]; try lia.
  all: destruct (Z.leb_spec0 0xa7000 (bv_unsigned x)); destruct (Z.leb_spec0 (bv_unsigned x + 1) (0xa7000 + 0x55c000)); cbn [andb]; try lia.
  all: vm_compute; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma cl_agree : forall s LB LF m m' mo W x,
  AHKc s LB LF m mo -> munch W m m' -> Forall (cl_write_ok LB LF) W ->
  ~ cl_byte s LB LF x -> 0 <= x < 2^64 -> m' (wa x) = m (wa x).
Proof.
  intros s LB LF m m' mo W x H MU FW NCB Hx. pose proof H as H0. ahk_open H.
  destruct (decide (m' (wa x) = m (wa x))) as [E|NE]; [exact E|]. exfalso. apply NCB.
  destruct (munch_changed W m m' x MU Hx NE) as (iv & Hiv & R).
  eapply cl_write_byte; [exact Hfs| exact (proj1 (Forall_forall _ _) FW iv Hiv)| exact R].
Qed.

Lemma mem_inv_cl : forall s LB LF m m' mo W,
  AHKc s LB LF m mo -> munch W m m' -> Forall (cl_write_ok LB LF) W -> mem_inv bsegs m'.
Proof.
  intros s LB LF m m' mo W H MU FW w b Hb. pose proof H as H0. ahk_open H.
  pose proof (bvu64 w) as Hw.
  destruct (decide (m' w = m w)) as [E|NE].
  - apply (Hmi w b). rewrite <- E. exact Hb.
  - assert (NO : ~ outside W (bv_unsigned w)) by (intros O; apply NE; apply MU; exact O).
    destruct (not_outside_In W _ NO) as (iv & Hiv & R).
    pose proof (cl_write_ok_high _ _ _ _ _ iv H0 (proj1 (Forall_forall _ _) FW iv Hiv)).
    apply asan_ro_addr_false_data. lia.
Qed.

(* [comment removed for export] *)
Lemma img_cells_not_cl : forall x,
  in_cells icp_globals_cellsL x \/ in_cells ay_statics_cellsL x \/ in_cells ay_cells_cellsL x -> x < 0x140c80.
Proof.
  clear_all_hyps.
  intros x H.
  assert (R : forall l y, in_cells l y -> Exists (fun c => fst c <= y < fst c + snd c) l).
  { intros l y (c & Hc & Hr). apply Exists_exists. exists c. auto. }
  unfold icp_globals_cellsL, ay_statics_cellsL, ay_cells_cellsL in *.
  unfold A_GOT_SBPTR, A_SBVAR, A_GOT_RIC, A_RIC, A_REAL_MEMCPY, A_REAL_MEMSET, A_GOT_MIDBEG, A_MIDBEG, A_GOT_MIDEND, A_MIDEND,
         A_GOT_HIGHEND, A_HIGHEND, A_INITED, AY_GOT_SHADOW, AY_SHADOW_VAR, AY_GOT_UAR, AY_UAR_VAR, AY_CALLBACKS, AY_BUF_ALLOC_ERROR, AY_NOOP_ALLOCS in *.
  destruct H as [H|[H|H]]; apply R in H; repeat (apply Exists_cons in H; destruct H as [H|H]; [cbn in H; lia|]); apply Exists_nil in H; destruct H.
Qed.

(* [comment removed for export] *)
Lemma AHK_frame_cl : forall s LB LF m m' mo W,
  AHKc s LB LF m mo -> munch W m m' -> wmono bsegs m m' -> Forall (cl_write_ok LB LF) W -> AHKc s LB LF m' mo.
Proof.
  intros s LB LF m m' mo W H MU WM FW. pose proof H as H0. ahk_open H. pose proof ceil_range as CR.
  pose proof (fun x => cl_agree s LB LF m m' mo W x H0 MU FW) as AG.
  pose proof (fun x CB => cl_byte_where _ _ _ _ _ x H0 CB) as WH.
  pose proof (fun x CB => cl_byte_not_fp _ _ _ _ _ x H0 CB) as NFP.
  pose proof (Forall_cl_high _ _ _ _ _ _ H0 FW) as FH.
  pose proof (Forall_cl_split _ _ _ _ _ _ H0 FW) as FS2.
  pose proof Henv as Henv0. destruct Henv as (V1 & V2 & V3 & V4 & V5 & V6 & EIN & EF1 & EF2 & EE & EFS & _).
  (* [comment removed for export] *)
  assert (AGI : forall a, a < 0x140c80 -> 0x10000 <= a -> m' (wa a) = m (wa a)).
  { intros a H1 H2. apply AG; [| lia]. intros CB. destruct (WH a CB) as (W1 & _). unfold cl_cells in W1. cbn [c_initialized c_errno ACONSTS] in W1. lia. }
  assert (AGL : forall a, LSLO <= a < LSHI -> m' (wa a) = m (wa a)).
  { intros a Ha. unfold LSLO, LSHI in Ha. apply MU. rewrite wa_unsigned by lia. eapply outside_of_Forall; [exact FS2|]. intros iv Piv. unfold LSLO, LSHI in Piv. cbn beta in Piv. lia. }
  unfold AHK. cbv zeta.
  split. { (* [comment removed for export] *) eapply (ARep_frame_client bsegs _ _ (DepotFP (aps_env s))); [| exact Hrep| exact WM|].
           - intros a0 mm mm' D W' A'. eapply DepotR_frame; [exact D| exact W'| exact A'].
           - intros x FPx. pose proof Hwf as WF'.
             pose proof (AK_blocks_sep s mo Hwf Hkern Henv0) as BS. pose proof (IMG_IN_of s Henv0) as IMG_IN.
             assert (Hx : 0 <= x < 2^64).
             { pose proof (fp_below_ceiling _ _ [] [] IMG_IN (DepotFP_where (aps_env s)) _ _ WF' BS FPx) as UB.
               destruct (fp_locate _ _ [] [] IMG_IN (DepotFP_where (aps_env s)) _ _ WF' BS FPx) as [(r & Hr & R)|[[R _]|[R _]]].
               - pose proof (IMG_IN r Hr). pose proof (wf_env_img _ (proj1 WF')) as (_ & I2 & _). lia.
               - unfold sh_band, kLowShadowBeg, kShadowBase in R. rewrite kHighShadowBeg_val in R. clear -UB CR R. lia.
               - unfold app_addr in R. rewrite kHighMemBeg_val in R. clear -UB CR R. lia. }
             apply AG; [| exact Hx]. intros CB. exact (NFP x CB FPx). }
  split; [exact Hwf|]. split; [exact Hkern|]. split; [exact Hkvm|]. split; [exact Hres|]. split; [exact Hqb|]. split; [exact Hdi|]. split; [exact Hbinv|].
  split; [exact Hbm|].
  split. { (* [comment removed for export] *) eapply FSRep_frame_w; [| exact WM| exact Hfs].
           intros a Ha. pose proof Hfs as (_ & P2 & P3 & _). apply AG.
           - intros CB. destruct (WH a CB) as (_ & _ & NF & _). exact (NF Ha).
           - unfold kFsBytes in P3. lia. }
  split. { (* [comment removed for export] *) eapply icp_globals_agree; [exact Hicp|]. intros a Ha.
           pose proof (img_cells_not_cl a (or_introl Ha)). pose proof (img_cells_not_mut a (or_introl Ha)) as [? _]. apply AGI; lia. }
  split. { (* [comment removed for export] *) eapply ay_statics_agree; [exact Hyst|]. intros a Ha.
           pose proof (img_cells_not_cl a (or_intror (or_introl Ha))). pose proof (img_cells_not_mut a (or_intror (or_introl Ha))) as [? _]. apply AGI; lia. }
  split. { (* [comment removed for export] *) eapply low_shadow_agree; [exact Hlow| exact AGL]. }
  assert (OUT : forall x, ~ cl_byte s LB LF x -> outside W x).
  { intros x NCB. eapply outside_of_Forall; [exact FW|]. intros iv Piv R. apply NCB. eapply cl_write_byte; [exact Hfs| exact Piv| exact R]. }
  rewrite EE in Hrt.
  split. { (* [comment removed for export] *) rewrite EE. eapply RTMisc_frame; [exact Hrt| exact MU| exact WM|]. intros a Ra.
           destruct (rt_fp_where a Ra) as [(R1 & R2 & R3 & R4)|R].
           - apply OUT. intros CB. destruct (WH a CB) as (W1 & _). exact (R2 (W1 ltac:(lia))).
           - apply OUT. intros CB. destruct (WH a CB) as (_ & _ & _ & W4). exact (W4 (rt_high2_high _ _ _ R)). }
  split. { (* [comment removed for export] *) eapply StdioRep_frame; [exact Hso| exact MU| exact WM|]. intros a Sa.
           destruct (so_fp_where a Sa) as (R1 & R2 & R3). apply OUT. intros CB. destruct (WH a CB) as (W1 & _). exact (R2 (W1 ltac:(lia))). }
  split; [exact Hkm|]. split; [exact Hli|]. split; [exact Hbud|].
  split; [exact (mem_inv_cl _ _ _ _ _ _ _ H0 MU FW)|]. split; [exact Henv0|].
  (* [comment removed for export] *)
  split; [| split; [exact Hss| exact Hcs]].                    (* [comment removed for export] *)
  eapply ay_cells_agree; [exact Hycl|]. intros a Ha.
  pose proof (img_cells_not_cl a (or_intror (or_intror Ha))). pose proof (img_cells_not_mut a (or_intror (or_intror Ha))) as [? _]. apply AGI; lia.
Qed.

(* [comment removed for export] *)
Lemma AHK_frame_drv : forall s LB LF m m' mo W,
  AHKc s LB LF m mo -> munch W m m' -> wmono bsegs m m' -> Forall (aclient_write_ok ACONSTS LB) W -> AHKc s LB LF m' mo.
Proof.
  intros s LB LF m m' mo W H MU WM FW. eapply AHK_frame_cl; [exact H| exact MU| exact WM|].
  apply Forall_forall. intros iv Hiv. pose proof (proj1 (Forall_forall _ _) FW iv Hiv) as X.
  unfold aclient_write_ok, cl_write_ok in *.
  destruct X as [X|[X|[X|X]]]; [left; exact X| right; left; exact X| right; right; right; right; left; lia
                               | right; right; right; right; right; right; right; exact X].
Qed.

Lemma AHK_frame_drv_errno : forall s LB LF m m' mo W,
  AHKc s LB LF m mo -> munch W m m' -> wmono bsegs m m' ->
  Forall (fun iv => aclient_write_ok ACONSTS LB iv \/ iv = (c_errno ACONSTS, c_errno ACONSTS + 4)) W -> AHKc s LB LF m' mo.
Proof.
  intros s LB LF m m' mo W H MU WM FW. eapply AHK_frame_cl; [exact H| exact MU| exact WM|].
  apply Forall_forall. intros iv Hiv. pose proof (proj1 (Forall_forall _ _) FW iv Hiv) as [X| ->].
  - unfold aclient_write_ok, cl_write_ok in *.
    destruct X as [X|[X|[X|X]]]; [left; exact X| right; left; exact X| right; right; right; right; left; lia
                                 | right; right; right; right; right; right; right; exact X].
  - unfold cl_write_ok. cbn [fst snd]. right; right; right; right; right; left. lia.
Qed.

(* [comment removed for export] *)
Lemma AHK_frame_rstage : forall s LB LF m m' mo W,
  AHKc s LB LF m mo -> munch W m m' -> wmono bsegs m m' ->
  Forall (fun iv => aclient_write_ok ACONSTS LB iv \/ (0x5d0c10 <= fst iv /\ snd iv <= 0x5d0c10 + 65536) \/ iv = (c_errno ACONSTS, c_errno ACONSTS + 4)) W ->
  AHKc s LB LF m' mo.
Proof.
  intros s LB LF m m' mo W H MU WM FW. eapply AHK_frame_cl; [exact H| exact MU| exact WM|].
  apply Forall_forall. intros iv Hiv. pose proof (proj1 (Forall_forall _ _) FW iv Hiv) as [X|[X| ->]].
  - unfold aclient_write_ok, cl_write_ok in *.
    destruct X as [X|[X|[X|X]]]; [left; exact X| right; left; exact X| right; right; right; right; left; lia
                                 | right; right; right; right; right; right; right; exact X].
  - unfold cl_write_ok. right; right; right; right; right; right; left. exact X.
  - unfold cl_write_ok. cbn [fst snd]. right; right; right; right; right; left. lia.
Qed.

(* [comment removed for export] *)
Lemma AHK_frame_y : forall s LB LF m m' mo W,
  AHKc s LB LF m mo -> munch W m m' -> wmono bsegs m m' ->
  Forall (fun iv => alloc_ceiling <= fst iv
    \/ (exists b, In b LB /\ ab_addr b <= fst iv /\ snd iv <= ab_addr b + ab_size b)
    \/ (exists f, In f LF /\ snd f <= fst iv /\ snd iv <= snd f + ff_bytes (fst f))
    \/ (exists f, In f LF /\ oshw_lo (snd f) <= fst iv /\ snd iv <= oshw_lo (snd f) + Z.shiftl 8 (fst f))
    \/ (0x5e0c10 <= fst iv /\ snd iv <= 0x5e0c14)) W ->
  AHKc s LB LF m' mo.
Proof.
  intros s LB LF m m' mo W H MU WM FW. eapply AHK_frame_cl; [exact H| exact MU| exact WM|].
  apply Forall_forall. intros iv Hiv. pose proof (proj1 (Forall_forall _ _) FW iv Hiv) as X.
  unfold cl_write_ok in *. cbn [c_initialized c_errno ACONSTS].
  destruct X as [X|[X|[X|[X|X]]]]; [left; exact X| right; left; exact X| right; right; left; exact X| right; right; right; left; exact X| right; right; right; right; left; lia].
Qed.

(* [comment removed for export] *)
Lemma lf_remove_ff_remove : forall N ff LF, lf_remove N ff LF = ff_remove N ff LF.
Proof. induction LF as [|f r IH]; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma AHK_fake_release : forall s LB LF m m' mo N ff,
  AHKc s LB LF m mo -> In (N, ff) LF ->
  munch [(aflagB E0 FSB0 N ff, aflagB E0 FSB0 N ff + 1)] m m' -> wmono bsegs m m' ->
  rw_cells bsegs m' (aflagB E0 FSB0 N ff) [C1 (Z_to_bv 8 0)] -> AHKc s LB (ff_remove N ff LF) m' mo.
Proof.
  intros s LB LF m m' mo N ff H Hin MU WM FL. pose proof H as H0. ahk_open H. pose proof ceil_range as CR.
  pose proof Henv as Henv0. destruct Henv as (V1 & V2 & V3 & V4 & V5 & V6 & EIN & EF1 & EF2 & EE & EFS & _).
  destruct (fframe_pos _ _ _ _ _ _ _ Hfs Hin) as (pos & P0 & P1 & P2 & P3 & P4 & CASES).
  assert (FS' : FSRep bsegs (aps_env s) (aps_fsbase s) (aps_fs s) (ff_remove N ff LF) m').
  { rewrite <- lf_remove_ff_remove. rewrite EE, EFS. rewrite EE, EFS in Hfs. eapply FSRep_release; [exact Hfs| exact Hin| exact MU| exact WM| exact FL]. }
  set (fl := aflagB E0 FSB0 N ff) in *.
  assert (FLR : aps_fsbase s + 4096 <= fl < aps_fsbase s + 36864).
  { subst fl. rewrite <- EFS. destruct CASES as [(-> & PP & _ & FQ)|(-> & PP & _ & FQ)]; rewrite (FQ E0); lia. }
  clearbody fl. clear CASES.
  (* [comment removed for export] *)
  assert (AG : forall x, x <> fl -> 0 <= x < 2^64 -> m' (wa x) = m (wa x)).
  { intros x Hx Rx. apply MU. rewrite wa_unsigned by lia. cbn. split; [lia| exact I]. }
  assert (AGI : forall a, a < 0x140c80 -> 0x10000 <= a -> m' (wa a) = m (wa a)) by (intros a H1 H2; apply AG; lia).
  unfold AHK. cbv zeta.
  split. { (* [comment removed for export] *)
           eapply (ARep_frame_client bsegs _ _ (DepotFP (aps_env s))); [| exact Hrep| exact WM|].
           - intros a0 mm mm' D W' A'. eapply DepotR_frame; [exact D| exact W'| exact A'].
           - intros x FPx. pose proof (AK_blocks_sep s mo Hwf Hkern Henv0) as BS. pose proof (IMG_IN_of s Henv0) as IMG_IN.
             pose proof Hwf as WF'.
             destruct (Z.eq_dec x fl) as [->|NE].
             + exfalso. apply (fp_fs_free _ _ [] [] IMG_IN (DepotFP_where (aps_env s)) _ fl WF' BS); [| exact FPx].
               unfold in_fakestack. rewrite EF1, EF2. apply andb_true_iff. split; [apply Z.leb_le| apply Z.ltb_lt]; unfold kFsBytes; lia.
             + apply AG; [exact NE|].
               pose proof (fp_below_ceiling _ _ [] [] IMG_IN (DepotFP_where (aps_env s)) _ _ WF' BS FPx) as UB.
               destruct (fp_locate _ _ [] [] IMG_IN (DepotFP_where (aps_env s)) _ _ WF' BS FPx) as [(r & Hr & R)|[[R _]|[R _]]].
               * pose proof (IMG_IN r Hr). pose proof (wf_env_img _ (proj1 WF')) as (_ & I2 & _). lia.
               * unfold sh_band, kLowShadowBeg, kShadowBase in R. rewrite kHighShadowBeg_val in R. clear -UB CR R. lia.
               * unfold app_addr in R. rewrite kHighMemBeg_val in R. clear -UB CR R. lia. }
  split; [exact Hwf|]. split; [exact Hkern|]. split; [exact Hkvm|]. split; [exact Hres|]. split; [exact Hqb|]. split; [exact Hdi|]. split; [exact Hbinv|].
  split; [exact Hbm|].
  split. { exact FS'. }
  split. { eapply icp_globals_agree; [exact Hicp|]. intros a Ha.
           pose proof (img_cells_not_cl a (or_introl Ha)). pose proof (img_cells_not_mut a (or_introl Ha)) as [? _]. apply AGI; lia. }
  split. { eapply ay_statics_agree; [exact Hyst|]. intros a Ha.
           pose proof (img_cells_not_cl a (or_intror (or_introl Ha))). pose proof (img_cells_not_mut a (or_intror (or_introl Ha))) as [? _]. apply AGI; lia. }
  split. { eapply low_shadow_agree; [exact Hlow|]. intros a Ha. unfold LSLO, LSHI in Ha. pose proof Hfs as (_ & Q2 & Q3 & Q4 & _). unfold FS_SB, kFsBytes in *.
           apply AG; lia. }
  assert (OUT : forall x, x <> fl -> outside [(fl, fl + 1)] x) by (intros x Hx; cbn; split; [lia| exact I]).
  rewrite EE in Hrt.
  split. { rewrite EE. eapply RTMisc_frame; [exact Hrt| exact MU| exact WM|]. intros a Ra.
           destruct (rt_fp_where a Ra) as [(R1 & R2 & R3 & R4)|R].
           - pose proof Hfs as (_ & Q2 & _). apply OUT. lia.
           - (* [comment removed for export] *)
             destruct PL0OK as ((c0 & cl & (CR1 & CR2 & CR3 & CR4 & CR5 & _) & CC1 & CC2) & (d0 & dl & (DR1 & DR2 & DR3 & DR4 & DR5 & _) & DD1 & DD2)
                                & (TR1 & TR2 & TR3 & TR4 & TR5 & _) & _).
             rewrite <- EE, EF1, EF2 in CR5, DR5, TR5. unfold rt_high2 in R. rewrite <- EE in R.
             apply OUT. unfold kFsBytes in *. lia. }
  split. { eapply StdioRep_frame; [exact Hso| exact MU| exact WM|]. intros a Sa. destruct (so_fp_where a Sa) as (R1 & R2 & R3).
           pose proof Hfs as (_ & Q2 & _). apply OUT; lia. }
  split; [exact Hkm|]. split; [exact Hli|]. split; [exact Hbud|].
  split.
  { (* [comment removed for export] *)
    intros w b Hb. pose proof (bvu64 w) as Hw.
    destruct (decide (m' w = m w)) as [E|NE].
    - apply (Hmi w b). rewrite <- E. exact Hb.
    - apply asan_ro_addr_false_data. pose proof Hfs as (_ & Q2 & _).
      destruct (Z.eq_dec (bv_unsigned w) fl) as [E|NE']; [lia|].
      exfalso. apply NE. rewrite <- (Z_to_bv_bv_unsigned 64 w) at 1 2 || rewrite <- (Z_to_bv_bv_unsigned w) at 1 2. apply AG; [exact NE'| lia]. }
  split; [exact Henv0|].
  split; [| split; [exact Hss| exact Hcs]].                    (* [comment removed for export] *)
  eapply ay_cells_agree; [exact Hycl|]. intros a Ha.
  pose proof (img_cells_not_cl a (or_intror (or_intror Ha))). pose proof (img_cells_not_mut a (or_intror (or_intror Ha))) as [? _]. apply AGI; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma acc_ok_fs : forall {P D} s mo S (a : Z) (k : nat),
  AWf (aps_env s) P D (aps_alloc s) -> AKern (aps_env s) (aps_alloc s) mo -> ENVOK E0 FSB0 s ->
  aps_fsbase s <= a -> a + Z.of_nat k <= aps_fsbase s + 11571200 ->
  acc_ok (m_vm_lazy mo) S (Z_to_bv 64 a, k).
Proof.
  clear_all_hyps.
  intros P D s mo S a k WF K Henv H1 H2. pose proof Henv as Henv0. pose proof ceil_range as CR.
  destruct Henv as (V1 & V2 & V3 & V4 & V5 & V6 & EIN & EF1 & EF2 & EE & EFS & _).
  unfold app_mem, kLowAppEnd, kLowShadowMapBeg, kShadowBase, kPageSize in V3. rewrite kHighMemBeg_val in V3. unfold kFsBytes in *.
  eapply (acc_ok_of_lazy_disjoint mo S (aps_fsbase s) (aps_fsbase s + 11571200)); [| lia| lia| lia| lia].
  exact (lazy_disjoint_fs s mo K WF Henv0).
Qed.

Lemma oshw_lo_val : forall A, oshw_lo A = A_SB + A / 8. Proof. reflexivity. Qed.
Lemma oshw_hi_val : forall A n, oshw_hi A n = A_SB + A / 8 + (n + 7) / 8. Proof. reflexivity. Qed.

Lemma AHK_y_policy : forall s LB LF m mo (w : word) (k : nat),
  AHKc s LB LF m mo ->
  (let a := bv_unsigned w in let kz := Z.of_nat k in
   (alloc_ceiling <= a /\ a + kz <= 2^47)
   \/ (AY_IMG_LO <= a /\ a + kz <= AY_IMG_HI)
   \/ (exists b, In b LB /\ ab_addr b <= a /\ a + kz <= ab_addr b + ab_size b)
   \/ (exists b, In b LB /\ oshw_lo (ab_addr b) <= a /\ a + kz <= oshw_hi (ab_addr b) (ab_size b))
   \/ (exists f, In f LF /\ snd f <= a /\ a + kz <= snd f + ff_bytes (fst f))
   \/ (exists f, In f LF /\ oshw_lo (snd f) <= a /\ a + kz <= oshw_lo (snd f) + Z.shiftl 8 (fst f))
   \/ (exists f, In f LF /\ a = aflagB E0 FSB0 (fst f) (snd f) /\ kz = 1)
   \/ (oshw_lo AY_IMG_LO <= a /\ a + kz <= oshw_hi AY_IMG_LO (AY_IMG_HI - AY_IMG_LO))) ->
  acc_ok (m_vm_lazy mo) (aSc s) (w, k).
Proof.
  intros s LB LF m mo w k H Hacc. pose proof H as H0. ahk_open H. pose proof ceil_range as CR.
  rewrite <- (Z_to_bv_bv_unsigned 64 w) || rewrite <- (Z_to_bv_bv_unsigned w). pose proof (bvu64 w) as Hw.
  cbv zeta in Hacc. set (a := bv_unsigned w) in *. clearbody a.
  pose proof Henv as Henv0. destruct Henv as (V1 & V2 & V3 & V4 & V5 & V6 & EIN & EF1 & EF2 & EE & EFS & _).
  unfold app_mem, kLowAppEnd, kLowShadowMapBeg, kShadowBase, kPageSize in V3. rewrite kHighMemBeg_val in V3. unfold kFsBytes in *.
  unfold AY_IMG_LO, AY_IMG_HI in Hacc.
  destruct Hacc as [[S1 S2] | [[I1 I2] | [(b & Hb & B1 & B2) | [(b & Hb & B1 & B2) | [(f & Hf & F1 & F2) | [(f & Hf & F1 & F2) | [(f & Hf & F1 & F2) | [I1 I2]]]]]]]];
    unfold oshw_lo, oshw_hi in *; rewrite ?A_SB_val in *.
  - eapply (acc_ok_of_lazy_disjoint mo (aSc s) a (2^64)); [| lia| lia| lia| lia].
    apply (lazy_disjoint_stack s mo _ _ Hkern Hwf Henv0). lia.
  - eapply (acc_ok_of_lazy_disjoint mo (aSc s) 0 0x603000); [| lia| lia| lia| lia].
    apply (lazy_disjoint_img s mo _ _ Hkern Hwf Henv0). lia.
  - pose proof (live_block_geom s mo b Hwf Hkern Henv0 (blocks_match_In _ _ _ Hbm Hb)) as ((G1 & G2 & G3) & _). unfold A_IMG_END in G1.
    eapply (acc_ok_of_lazy_disjoint mo (aSc s) (ab_addr b - 16) (ab_addr b + ab_size b)); [| lia| lia| lia| lia].
    exact (lazy_disjoint_block s mo _ _ Hkern Hwf Henv0 (blocks_match_In _ _ _ Hbm Hb)).
  - (* [comment removed for export] *)
    pose proof (live_block_geom s mo b Hwf Hkern Henv0 (blocks_match_In _ _ _ Hbm Hb)) as ((G1 & G2 & _) & _). unfold A_IMG_END in G1.
    destruct (Z_lt_dec 0 (ab_size b)) as [POS|NP].
    2:{ (* [comment removed for export] *)
        assert (k = 0%nat). { clear -B1 B2 NP. Z.div_mod_to_equations; lia. } subst k. right. split.
        - unfold acc_nowrap. cbn [fst snd]. rewrite unsigned_lit by lia. lia.
        - intros kk Hkk. cbn in Hkk. lia. }
    right. eapply pages_budgeted_acc_inS.
    + pose proof (pages_budgeted_block s mo b Hwf Hkern Henv0 Hres (blocks_match_In _ _ _ Hbm Hb) POS) as PB.
      unfold oshw_lo, oshw_hi in PB. rewrite ?A_SB_val in PB. exact PB.
    + lia. + lia. + lia.
    + clear -G1 G2 POS CR. Z.div_mod_to_equations. lia.
  - (* [comment removed for export] *)
    destruct f as [N ff]. cbn [fst snd] in *.
    destruct (fframe_pos _ _ _ _ _ _ _ Hfs Hf) as (pos & P0 & P1 & P2 & P3 & P4 & CASES). unfold ff_bytes in F2.
    apply (acc_ok_fs s mo (aSc s) a k Hwf Hkern Henv0);
      destruct CASES as [(-> & PP & -> & _)|(-> & PP & -> & _)]; zground; cbn in *; lia.
  - (* [comment removed for export] *)
    destruct f as [N ff]. cbn [fst snd] in *.
    destruct (fframe_pos _ _ _ _ _ _ _ Hfs Hf) as (pos & P0 & P1 & P2 & P3 & P4 & CASES). unfold FS_SB in P4.
    right. eapply (pages_budgeted_acc_inS (aSc s) (pgdn (sh FSB0)) (pgup (sh (FSB0 + kFsBytes)))).
    + eapply (pages_budgeted_A0 s (pgdn (sh FSB0)) (pgup (sh (FSB0 + kFsBytes)))); [| apply pgdn_mod| | | lia| lia].
      * apply In_A0_S0. unfold S0_ivs5. cbn -[pgdn pgup sh Z.add kFsBytes alloc_ceiling]. do 3 right. left. reflexivity.
      * unfold pgdn, sh. rewrite A_SB_val. rewrite <- EFS. clear -P2. Z.div_mod_to_equations. lia.
      * unfold pgup, pgdn, sh, kFsBytes. rewrite A_SB_val. rewrite <- EFS. clear -P3 P2 CR. Z.div_mod_to_equations. lia.
    + lia.
    + unfold pgdn, sh. rewrite A_SB_val. rewrite <- EFS.
      destruct CASES as [(-> & PP & -> & _)|(-> & PP & -> & _)]; zground; cbn in *; clear -F1 P0 PP P2; Z.div_mod_to_equations; lia.
    + unfold pgup, pgdn, sh, kFsBytes. rewrite A_SB_val. rewrite <- EFS.
      destruct CASES as [(-> & PP & -> & _)|(-> & PP & -> & _)]; zground; cbn in *; clear -F2 P0 PP P2; Z.div_mod_to_equations; lia.
    + unfold pgup, pgdn, sh, kFsBytes. rewrite A_SB_val. rewrite <- EFS. clear -P3 P2 CR. Z.div_mod_to_equations. lia.
  - (* [comment removed for export] *)
    destruct f as [N ff]. cbn [fst snd] in *.
    destruct (fframe_pos _ _ _ _ _ _ _ Hfs Hf) as (pos & P0 & P1 & P2 & P3 & P4 & CASES).
    apply (acc_ok_fs s mo (aSc s) a k Hwf Hkern Henv0);
      destruct CASES as [(-> & PP & _ & FQ)|(-> & PP & _ & FQ)]; rewrite <- EFS, (FQ E0) in F1; zground; lia.
  - (* [comment removed for export] *)
    right. eapply (pages_budgeted_acc_inS (aSc s) 0x7fff7000 0x8fff7000).
    + eapply (pages_budgeted_A0 s 0x7fff7000 0x8fff7000); [| reflexivity| lia| lia| lia| lia]. apply In_A0_S0. unfold S0_ivs5. left. reflexivity.
    + lia.
    + cbn in I1. lia.
    + cbn in I2. lia.
    + lia.
Qed.

Lemma AHK_y_kip : forall s LB LF m mo, AHKc s LB LF m mo ->
    m_halted mo = None /\ minvA mo /\ LI (aSc s) (aNc s) (aEBc s) mo
    /\ (forall (w : word) (k : nat),
         (let a := bv_unsigned w in let kz := Z.of_nat k in
          (alloc_ceiling <= a /\ a + kz <= 2^47)
          \/ (AY_IMG_LO <= a /\ a + kz <= AY_IMG_HI)
          \/ (exists b, In b LB /\ ab_addr b <= a /\ a + kz <= ab_addr b + ab_size b)
          \/ (exists b, In b LB /\ oshw_lo (ab_addr b) <= a /\ a + kz <= oshw_hi (ab_addr b) (ab_size b))
          \/ (exists f, In f LF /\ snd f <= a /\ a + kz <= snd f + ff_bytes (fst f))
          \/ (exists f, In f LF /\ oshw_lo (snd f) <= a /\ a + kz <= oshw_lo (snd f) + Z.shiftl 8 (fst f))
          \/ (exists f, In f LF /\ a = aflagB E0 FSB0 (fst f) (snd f) /\ kz = 1)
          \/ (oshw_lo AY_IMG_LO <= a /\ a + kz <= oshw_hi AY_IMG_LO (AY_IMG_HI - AY_IMG_LO))) ->
         acc_ok (m_vm_lazy mo) (aSc s) (w, k))
    /\ (forall mo', magree mo mo' -> LI (aSc s) (aNc s) (aEBc s) mo' -> AHKc s LB LF m mo' /\ ayR s mo s mo').
Proof.
  intros s LB LF m mo H. split; [exact (AHK_halted _ _ _ _ _ _ _ _ _ _ _ _ _ H)|]. split; [exact (AHK_minvA _ _ _ _ _ _ _ _ _ _ _ _ _ H)|].
  split; [exact (AHK_LI _ _ _ _ _ _ _ _ _ _ _ _ _ H)|]. split.
  - intros w k Hx. exact (AHK_y_policy _ _ _ _ _ w k H Hx).
  - intros mo' Hag HLI. pose proof (AHK_magree _ _ _ _ _ _ _ _ _ _ _ _ _ _ H Hag HLI) as H'. split; [exact H'|].
    eapply AHK_ayR; [exact H| exact H'].
Qed.
End Bundle.
End RC__1.
