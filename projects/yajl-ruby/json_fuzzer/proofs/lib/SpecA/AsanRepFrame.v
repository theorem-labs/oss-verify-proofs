(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Mem Cells Step Frame Arr.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import STree.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanConsts AsanSizeClass AsanState AsanLayout AsanOps AsanHoare AsanRep AsanWf1 AsanWf3 AsanWf4 AsanWf5 AsanClient.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section AGREE.
Variable segs : list Segment.
#[warnings="-notation-for-abbreviation"] Notation mem := (word -> option byte).
Definition agree_on (m m' : mem) (A n : Z) : Prop := forall x, A <= x < A + n -> m' (wa x) = m (wa x).

Lemma bytes_at_agree : forall m m' A bs, agree_on m m' A (Z.of_nat (length bs)) -> bytes_at segs m A bs -> bytes_at segs m' A bs.
Proof.
  intros m m' A bs AG (B0 & B1 & BR). split; [exact B0|]. split; [exact B1|].
  intros i Hi. rewrite <- (BR i Hi). unfold mrd. rewrite AG by lia. reflexivity.
Qed.
Lemma wr_at_agree : forall m m' A n, agree_on m m' A n -> wr_at segs m A n -> wr_at segs m' A n.
Proof.
  intros m m' A n AG (W0 & W1 & WR). split; [exact W0|]. split; [exact W1|].
  intros i Hi. specialize (WR i Hi). unfold wview in *. rewrite AG by lia. exact WR.
Qed.
Lemma rw_cells_agree' : forall m m' A cs, agree_on m m' A (Z.of_nat (cells_size cs)) -> rw_cells segs m A cs -> rw_cells segs m' A cs.
Proof.
  intros m m' A cs AG [[WF B] W]. pose proof (cells_bytes_length _ WF) as L.
  split; [split; [exact WF| eapply bytes_at_agree; [| exact B]; rewrite L; exact AG]|].
  eapply wr_at_agree; [exact AG| exact W].
Qed.
Lemma u8arr_agree : forall m m' A bs, agree_on m m' A (Z.of_nat (length bs)) -> u8arr segs m A bs -> u8arr segs m' A bs.
Proof. intros m m' A bs AG [B W]. split; [eapply bytes_at_agree; eauto| eapply wr_at_agree; eauto]. Qed.
Lemma u32arr_agree : forall m m' A ws, agree_on m m' A (4 * Z.of_nat (length ws)) -> u32arr segs m A ws -> u32arr segs m' A ws.
Proof.
  intros m m' A ws AG [B W]. split; [| eapply wr_at_agree; eauto].
  eapply bytes_at_agree; [| exact B]. rewrite u32s_length. intros x Hx. apply AG. lia.
Qed.
Lemma u64arr_agree : forall m m' A ws, agree_on m m' A (8 * Z.of_nat (length ws)) -> u64arr segs m A ws -> u64arr segs m' A ws.
Proof.
  intros m m' A ws AG [B W]. split; [| eapply wr_at_agree; eauto].
  eapply bytes_at_agree; [| exact B]. rewrite u64s_length. intros x Hx. apply AG. lia.
Qed.
End AGREE.

(* [comment removed for export] *)
Section RF.
Variable segs : list Segment.
Variable E : aenv.
Let IC := ae_ic E.
Let INST : Z := ae_instance E.
Let SB : Z := ae_space_beg E.
Let RI : Z := ae_region_info E.
Let T : Z := ae_thread E.
#[warnings="-notation-for-abbreviation"] Notation mem := (word -> option byte).

(* [comment removed for export] *)
Variable DepotR : astate -> mem -> Prop.
Variable DepotFP : astate -> Z -> Prop.
Hypothesis DepotR_frame : forall s m m',
  DepotR s m -> wmono segs m m' -> (forall a, DepotFP s a -> m' (wa a) = m (wa a)) -> DepotR s m'.

Definition in_ranges (l : list (Z * Z)) (a : Z) : Prop := exists r, In r l /\ fst r <= a < fst r + snd r.

(* [comment removed for export] *)
Definition arep_img_ranges : list (Z * Z) :=
  [(INST, 3632); (aic_asan_flags IC, Z.of_nat (length (asan_flags_bytes IC)));
   (aic_common_flags IC + 34, 1); (aic_common_flags IC + 120, 8); (aic_common_flags IC + 219, 1);
   (aic_shadow_dyn_addr IC, 8); (aic_kHighMemEnd IC, 24); (aic_can_poison_memory IC, 1); (aic_asan_inited IC, 1);
   (aic_malloc_context_size IC, 4); (aic_page_size_cached IC, 8); (aic_dying_flag IC, 4); (aic_stack_anchor IC, 8);
   (aic_REAL_memcpy_var IC, 16); (aic_malloc_hook_table IC, 80); (aic_internal_alloc_initialized IC, 2);
   (aic_internal_allocator_instance IC, 0x81030)].
(* [comment removed for export] *)
Definition arep_thr_ranges : list (Z * Z) :=
  [(T + kThrStackTop, 16); (T + 40, 1); (T + kThrQCache, 32); (T + kThrCache, kPerClassSize * kNumClasses);
   (T + kThrCacheStats + 16, 16); (T + kThrStats, 112 + 8 * 32); (T + kThrUnwinding, 1)].

(* [comment removed for export] *)
Definition chunk_meta_fp (cm : chunkmeta) (a : Z) : Prop :=
  cm_chunk_beg cm <= a < cm_chunk_beg cm + 16
  \/ (16 < 16 * 2 ^ cm_rz_log cm /\ cm_alloc_beg cm <= a < cm_alloc_beg cm + 16)
  \/ (match cm_state cm with CQuarantined _ _ => cm_user_beg cm <= a < cm_user_beg cm + 8 | CAllocated _ => False end).

Definition arep_fp (s : astate) (a : Z) : Prop :=
     in_ranges arep_img_ranges a
  \/ RI <= a < RI + kRegSize * kNumClasses
  \/ in_ranges arep_thr_ranges a
  \/ (exists c, 0 <= c < kNumClasses /\ free_array SB c <= a < free_array SB c + rg_mapped_fa (region_of s c))
  \/ ae_ptr_array E <= a < ae_ptr_array E + 8 * kChunksBlockCount
  \/ (exists sc, In sc (as_sec s) /\ sc_map_beg sc <= a < sc_map_beg sc + 32)
  \/ (exists cb cm, as_chunks s !! cb = Some cm /\ chunk_meta_fp cm a)
  \/ (exists b, In b (as_tq s ++ as_gq s) /\ b_addr b <= a < b_addr b + 24 + 8 * kBatchCap)
  \/ DepotFP s a
  \/ (exists g v, a = kShadowBase + g /\ Sh E s (8 * g) = Some v).

Lemma in_ranges_here : forall r l a, fst r <= a < fst r + snd r -> in_ranges (r :: l) a.
Proof. intros r l a H. exists r. split; [left; reflexivity| exact H]. Qed.
Lemma in_ranges_later : forall r l a, in_ranges l a -> in_ranges (r :: l) a.
Proof. intros r l a (r' & Hin & H). exists r'. split; [right; exact Hin| exact H]. Qed.

#[warnings="-notation-for-abbreviation"] Notation AREP := (ARep segs E DepotR).
#[warnings="-notation-for-abbreviation"] Notation FP := arep_fp.

Lemma fp_img_nth : forall s k A n x, nth_error arep_img_ranges k = Some (A, n) -> A <= x < A + n -> FP s x.
Proof. intros s k A n x Hk Hx. left. exists (A, n). split; [eapply nth_error_In; exact Hk| exact Hx]. Qed.
Lemma fp_thr_nth : forall s k A n x, nth_error arep_thr_ranges k = Some (A, n) -> A <= x < A + n -> FP s x.
Proof. intros s k A n x Hk Hx. right; right; left. exists (A, n). split; [eapply nth_error_In; exact Hk| exact Hx]. Qed.

(* [comment removed for export] *)
Ltac zconsts Hx := unfold kInsSpaceBeg, kInsSecondary, kInsNReserved, kInsSecStats, kInsSecMutex, kInsGlobalStats, kInsQuarantine, kInsQMutex,
  kInsQGlobal, kInsFallbackMutex, kInsMaxUserDefined, kThrStackTop, kThrQCache, kThrCache, kPerClassSize, kNumClasses, kThrCacheStats,
  kThrStats, kThrUnwinding, kRegSize, kBatchCap, kChunksBlockCount, kIaPageSizeOff in Hx |- *; unfold SB, RI, T, INST, IC in Hx |- *.
(* [comment removed for export] *)
Ltac ag AG ARM := let Hx := fresh "Hx" in intros x Hx; cbn -[Z.add Z.mul Z.sub Z.of_nat Z.to_nat free_array region_beg region_of get_region Z.pow] in Hx; apply AG; ARM Hx.
Ltac agI AG k := ag AG ltac:(fun Hx => eapply (fp_img_nth _ k); [reflexivity| cbn [length asan_flags_bytes]; zconsts Hx; lia]).
Ltac agT AG k := ag AG ltac:(fun Hx => eapply (fp_thr_nth _ k); [reflexivity| zconsts Hx; lia]).

(* [comment removed for export] *)
Lemma zeros_ia_len : Z.of_nat (length (zeros (Z.to_nat 0x40000))) = 0x40000.
Proof. unfold zeros. rewrite repeat_length. rewrite Z2Nat.id by (cbv; discriminate). reflexivity. Qed.

Section CLIENT.
Variables (s : astate) (m m' : mem).
Hypothesis WM : wmono segs m m'.
Hypothesis AG : forall a, FP s a -> m' (wa a) = m (wa a).

Lemma frameA : arep_instance segs E s m -> arep_instance segs E s m'.
Proof.
  intros RA. destruct RA as (A1 & A2 & A3 & A4 & (bsl & A5 & L5) & A6 & A7 & A8 & A9 & A10 & A11 & A12).
  unfold arep_instance. repeat match goal with |- _ /\ _ => split end.
  all: try (exists bsl; split; [| exact L5]).
  all: first [ eapply rw_cells_agree'; [| eassumption]; agI AG 0%nat
             | eapply u64arr_agree; [| eassumption]; rewrite ?L5; agI AG 0%nat ].
Qed.
Lemma frameB : arep_regioninfo segs E s m -> arep_regioninfo segs E s m'.
Proof.
  intros RB. unfold arep_regioninfo in *. intros c Hc. eapply rw_cells_agree'; [| exact (RB c Hc)]. unfold kNumClasses in Hc.
  ag AG ltac:(fun Hx => right; left; zconsts Hx; lia).
Qed.
Lemma frameC : arep_region_mem segs E s m -> arep_region_mem segs E s m'.
Proof.
  intros RC. unfold arep_region_mem in *. intros c Hc. destruct (RC c Hc) as (W & junk & U & L). unfold kNumClasses in Hc. split.
  - eapply wr_at_transport; [exact W| exact WM].
  - exists junk. split; [| exact L]. eapply u32arr_agree; [| exact U].
    intros x Hx. rewrite length_app, length_map in Hx. apply AG. right; right; right; left. exists c. zconsts Hx. lia.
Qed.
Lemma frameD : arep_thread segs E s m -> arep_thread segs E s m'.
Proof.
  intros RD. destruct RD as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8). unfold arep_thread.
  split; [eapply rw_cells_agree'; [| exact D1]; agT AG 0%nat|].
  split; [eapply rw_cells_agree'; [| exact D2]; agT AG 1%nat|].
  split; [eapply rw_cells_agree'; [| exact D3]; agT AG 2%nat|].
  split.
  { intros c Hc. destruct (D4 c Hc) as (X1 & junk & X2 & L). unfold kNumClasses in Hc. split.
    - eapply rw_cells_agree'; [| exact X1]. agT AG 3%nat.
    - exists junk. split; [| exact L]. eapply u32arr_agree; [| exact X2].
      ag AG ltac:(fun Hx => eapply (fp_thr_nth _ 3); [reflexivity| rewrite length_app, length_map in Hx; zconsts Hx; lia]). }
  split; [eapply rw_cells_agree'; [| exact D5]; agT AG 4%nat|].
  split; [eapply u64arr_agree; [| exact D6]; ag AG ltac:(fun Hx => eapply (fp_thr_nth _ 5); [reflexivity| zconsts Hx; lia])|].
  split; [eapply u64arr_agree; [| exact D7]; ag AG ltac:(fun Hx => eapply (fp_thr_nth _ 5); [reflexivity| zconsts Hx; lia])|].
  eapply rw_cells_agree'; [| exact D8]; agT AG 6%nat.
Qed.
Lemma frameE : arep_secondary segs E s m -> arep_secondary segs E s m'.
Proof.
  intros RE. destruct RE as [E1 E2]. unfold arep_secondary. split.
  - destruct E1 as [E1|(E11 & junk & U & L)]; [left; exact E1| right]. split; [exact E11|]. exists junk. split; [| exact L].
    eapply u64arr_agree; [| exact U].
    pose proof (f_equal Z.of_nat L) as L'. rewrite Z2Nat.id in L' by (cbv; discriminate). clear L.
    intros x Hx. rewrite length_app, length_map in Hx. apply AG. do 4 right; left. unfold kChunksBlockCount in L'. zconsts Hx. lia.
  - intros i c Hi. destruct (E2 i c Hi) as [X1 X2]. split; [| eapply wr_at_transport; [exact X2| exact WM]].
    eapply rw_cells_agree'; [| exact X1]. ag AG ltac:(fun Hx => do 5 right; left; exists c; split; [eapply nth_error_In; exact Hi| lia]).
Qed.
Lemma frameF : arep_chunks segs s m -> arep_chunks segs s m'.
Proof.
  intros RF. unfold arep_chunks in *. intros cb cm Hcm. destruct (RF cb cm Hcm) as (X0 & (b1 & Hb1 & X1) & X2 & X3). split; [exact X0|].
  split; [| split].
  - exists b1. split; [exact Hb1|]. eapply rw_cells_agree'; [| exact X1]. ag AG ltac:(fun Hx => do 6 right; left; exists cb, cm; split; [exact Hcm| left; lia]).
  - intros Hrz. eapply rw_cells_agree'; [| exact (X2 Hrz)]. ag AG ltac:(fun Hx => do 6 right; left; exists cb, cm; split; [exact Hcm| right; left; split; [exact Hrz| lia]]).
  - destruct (cm_state cm) as [i|i j] eqn:ST; [exact I|].
    eapply rw_cells_agree'; [| exact X3]. ag AG ltac:(fun Hx => do 6 right; left; exists cb, cm; split; [exact Hcm| right; right; rewrite ST; lia]).
Qed.
Lemma frameG : arep_batches segs s m -> arep_batches segs s m'.
Proof.
  intros RG.
  assert (BL : forall l, (forall b, In b l -> In b (as_tq s ++ as_gq s)) -> arep_batch_list segs s l m -> arep_batch_list segs s l m').
  { induction l as [|b l IH]; intros SUB H; [exact I|]. destruct H as [[X1 (junk & X2 & L)] H2]. split; [| apply IH; [intros b' Hb'; apply SUB; right; exact Hb'| exact H2]].
    split.
    - eapply rw_cells_agree'; [| exact X1]. ag AG ltac:(fun Hx => do 7 right; left; exists b; split; [apply SUB; left; reflexivity| zconsts Hx; lia]).
    - exists junk. split; [| exact L]. eapply u64arr_agree; [| exact X2].
      pose proof (f_equal Z.of_nat L) as L'. rewrite Z2Nat.id in L' by (cbv; discriminate). clear L.
      intros x Hx. rewrite length_app, length_map in Hx. apply AG. do 7 right; left. exists b. split; [apply SUB; left; reflexivity| unfold kBatchCap in L'; zconsts Hx; lia]. }
  destruct RG as [G1 G2]. split; (apply BL; [| assumption]); intros b Hb; apply in_app_iff; [left| right]; exact Hb.
Qed.
Lemma frameH : arep_depot DepotR s m -> arep_depot DepotR s m'.
Proof. intros RH. unfold arep_depot in *. eapply DepotR_frame; [exact RH| exact WM|]. intros a Ha. apply AG. do 8 right; left. exact Ha. Qed.
Lemma frameI : arep_globals segs E s m -> arep_globals segs E s m'.
Proof.
  intros RI'. destruct RI' as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9 & I10 & I11 & I12 & I13 & I14 & I15 & I16 & I17 & I18). unfold arep_globals.
  split; [eapply u8arr_agree; [| exact I1]; ag AG ltac:(fun Hx => eapply (fp_img_nth _ 1); [reflexivity| cbn; zconsts Hx; lia])|].
  split; [eapply rw_cells_agree'; [| exact I2]; agI AG 2%nat|].
  split; [eapply rw_cells_agree'; [| exact I3]; agI AG 3%nat|].
  split; [eapply rw_cells_agree'; [| exact I4]; agI AG 4%nat|].
  split; [eapply rw_cells_agree'; [| exact I5]; agI AG 5%nat|].
  split; [eapply rw_cells_agree'; [| exact I6]; agI AG 6%nat|].
  split; [eapply rw_cells_agree'; [| exact I7]; agI AG 7%nat|].
  split; [eapply rw_cells_agree'; [| exact I8]; agI AG 8%nat|].
  split; [eapply rw_cells_agree'; [| exact I9]; agI AG 9%nat|].
  split; [eapply rw_cells_agree'; [| exact I10]; agI AG 10%nat|].
  split; [eapply rw_cells_agree'; [| exact I11]; agI AG 11%nat|].
  split; [eapply rw_cells_agree'; [| exact I12]; agI AG 12%nat|].
  split; [eapply rw_cells_agree'; [| exact I13]; agI AG 13%nat|].
  split; [eapply u64arr_agree; [| exact I14]; ag AG ltac:(fun Hx => eapply (fp_img_nth _ 14); [reflexivity| zconsts Hx; lia])|].
  split; [eapply rw_cells_agree'; [| exact I15]; agI AG 15%nat|].
  split; [intros Hia; eapply rw_cells_agree'; [| exact (I16 Hia)]; agI AG 16%nat|].
  split.
  { eapply u8arr_agree; [| exact I17]. intros x Hx. rewrite zeros_ia_len in Hx.
    apply AG; eapply (fp_img_nth _ 16); [reflexivity| zconsts Hx; clear -Hx; lia]. }
  eapply wr_at_transport; [exact I18| exact WM].
Qed.
Lemma frameJ : arep_shadow segs E s m -> arep_shadow segs E s m'.
Proof.
  intros RJ. unfold arep_shadow in *. intros g v Hg. eapply rw_cells_agree'; [| exact (RJ g v Hg)].
  ag AG ltac:(fun Hx => do 9 right; exists g, v; split; [lia| exact Hg]).
Qed.
End CLIENT.

Theorem ARep_frame_client : forall s (m m' : mem),
  AREP s m -> wmono segs m m' -> (forall a, FP s a -> m' (wa a) = m (wa a)) -> AREP s m'.
Proof.
  intros s m m' (RA & RB & RC & RD & RE & RF & RG & RH & RI' & RJ) WM AG.
  split; [exact (frameA s m m' AG RA)|]. split; [exact (frameB s m m' AG RB)|]. split; [exact (frameC s m m' WM AG RC)|].
  split; [exact (frameD s m m' AG RD)|]. split; [exact (frameE s m m' WM AG RE)|]. split; [exact (frameF s m m' AG RF)|].
  split; [exact (frameG s m m' AG RG)|]. split; [exact (frameH s m m' WM AG RH)|]. split; [exact (frameI s m m' WM AG RI')|].
  exact (frameJ s m m' AG RJ).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section KIT.
Variables (P : list Z) (D : list batch).
#[warnings="-notation-for-abbreviation"] Notation AWF := (AWf E P D).

(* [comment removed for export] *)
Definition depot_static : list (Z * Z) := [(aic_theDepot IC, 0x440010); (aic_stackStore IC, 0x10010)].

(* [comment removed for export] *)
Hypothesis IMG_IN : forall r, In r (arep_img_ranges ++ depot_static) ->
  fst (ae_img E) <= fst r /\ fst r + snd r <= fst (ae_img E) + snd (ae_img E).
(* [comment removed for export] *)
Hypothesis DEPOT_WHERE : forall s a, DepotFP s a ->
  in_ranges depot_static a
  \/ (exists b, In b (ae_depot_nodes E :: as_node_blocks s) /\ b <= a < b + kDepotNodeBlockBytes)
  \/ (exists b, In b (ae_store_blk E :: as_store_blocks s) /\ b <= a < b + kStoreBlockBytes).
(* [comment removed for export] *)
Definition blocks_sep (s : astate) : Prop :=
  forall b len, (In b (ae_depot_nodes E :: as_node_blocks s) /\ len = kDepotNodeBlockBytes)
                \/ (In b (ae_store_blk E :: as_store_blocks s) /\ len = kStoreBlockBytes) ->
    app_mem b len /\ b + len <= alloc_ceiling
    /\ (b + len <= ae_resv_beg E \/ ae_resv_beg E + 0x2000011000 <= b)
    /\ (forall sc, In sc (as_sec s) -> b + len <= sc_map_beg sc \/ sc_map_beg sc + sc_map_size sc <= b)
    /\ (b + len <= ae_fs_beg E \/ ae_fs_beg E + ae_fs_len E <= b)
    /\ img_sep E b len.

(* [comment removed for export] *)
Lemma app_obj_addr : forall X L a, app_mem X L -> img_sep E X L -> X <= a < X + L -> app_addr a /\ in_img E a = false.
Proof.
  intros X L a AM IS Ha. split; [exact (app_mem_addr X L a AM Ha)|].
  unfold img_sep in IS. unfold in_img. apply Bool.andb_false_iff. destruct IS; [left; apply Z.leb_gt; lia| right; apply Z.ltb_ge; lia].
Qed.
(* [comment removed for export] *)
Lemma high_obj_addr : forall a, wf_env E -> kHighMemBeg <= a < alloc_ceiling -> app_addr a /\ in_img E a = false.
Proof.
  intros a WE Ha. split; [unfold app_addr; lia|].
  unfold wf_env in WE. destruct WE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & IMG1 & IMG2 & IMG3 & _).
  unfold in_img. apply Bool.andb_false_iff. right. apply Z.ltb_ge. rewrite kLowAppEnd_val, kHighMemBeg_val in *. lia.
Qed.

Lemma depot_fp_where : forall s a, blocks_sep s -> DepotFP s a ->
  in_ranges depot_static a
  \/ (app_addr a /\ in_img E a = false
      /\ ~ (ae_resv_beg E <= a < ae_resv_beg E + 0x2000011000)
      /\ (forall sc, In sc (as_sec s) -> ~ (sc_map_beg sc <= a < sc_map_beg sc + sc_map_size sc))
      /\ in_fakestack E a = false).
Proof.
  intros s a BS H. destruct (DEPOT_WHERE s a H) as [X|[(b & Hb & R)|(b & Hb & R)]]; [left; exact X| right| right].
  - destruct (BS b kDepotNodeBlockBytes ltac:(left; auto)) as (B1 & B2 & B3 & B4 & B5 & B6).
    destruct (app_obj_addr _ _ a B1 B6 R) as [A1 A2]. split; [exact A1|]. split; [exact A2|].
    split; [lia|]. split; [intros sc Hsc; destruct (B4 sc Hsc); lia|].
    unfold in_fakestack. apply Bool.andb_false_iff. destruct B5; [left; apply Z.leb_gt; lia| right; apply Z.ltb_ge; lia].
  - destruct (BS b kStoreBlockBytes ltac:(right; auto)) as (B1 & B2 & B3 & B4 & B5 & B6).
    destruct (app_obj_addr _ _ a B1 B6 R) as [A1 A2]. split; [exact A1|]. split; [exact A2|].
    split; [lia|]. split; [intros sc Hsc; destruct (B4 sc Hsc); lia|].
    unfold in_fakestack. apply Bool.andb_false_iff. destruct B5; [left; apply Z.leb_gt; lia| right; apply Z.ltb_ge; lia].
Qed.

(* [comment removed for export] *)
Lemma blk_hi_mod16 : forall s cb cm, AWF s -> as_chunks s !! cb = Some cm -> blk_hi s cm mod 16 = 0.
Proof.
  intros s cb cm WF Hcm. pose proof WF as ((SBM & _) & WR & WC & [K1 _] & WQ & (_ & _ & S3 & _) & _).
  destruct (K1 _ _ Hcm) as (_ & Bn & C & D0 & _). unfold blk_hi.
  destruct (cm_prim cm) as [c|].
  - destruct D0 as (D1 & D2 & (k & Hk & Hab & _) & _).
    assert (Hc : 1 <= c <= kLargestClassID).
    { subst c. apply malloc_class_ok. pose proof (proj1 (from_primary_iff (cm_n cm) ltac:(lia)) D1). lia. }
    pose proof (class_size_mod c Hc) as [CM _]. rewrite Hab. unfold region_beg, kRegionSize.
    apply Z.mod_divide in CM; [|lia]. destruct CM as [q Hq]. apply Z.mod_divide in SBM; [|lia]. destruct SBM as [u Hu].
    rewrite Hq, Hu. apply Z.mod_divide; [lia|]. exists (u * 2^12 + c * 2^28 + k * q * 2 + q * 2). lia.
  - pose proof (map_size_facts (cm_n cm)) as (MM & _). destruct D0 as (_ & sc & Hsc & Hab & Hms & _).
    destruct (S3 sc Hsc) as (AL & _). rewrite Hab. unfold kPageSize in *.
    apply Z.mod_divide in AL; [|lia]. destruct AL as [q Hq]. apply Z.mod_divide in MM; [|lia]. destruct MM as [q' Hq'].
    apply Z.mod_divide; [lia|]. exists (256 * q + 256 * q'). lia.
Qed.

(* [comment removed for export] *)
Lemma chunk_meta_in_block : forall s cb cm a, AWF s -> as_chunks s !! cb = Some cm -> chunk_meta_fp cm a ->
  blk_lo cm <= a < blk_hi s cm
  /\ (match cm_state cm with CAllocated _ => a < cm_user_beg cm | CQuarantined _ _ => True end).
Proof.
  intros s cb cm a WF Hcm H.
  pose proof (chunk_user_in_block E P D s cb cm WF Hcm) as (A & B & C). unfold user_lo, user_hi, kChunkHeaderSize in *.
  pose proof WF as (_ & _ & _ & [K1 _] & _). destruct (K1 _ _ Hcm) as (CB & Bn & _).
  pose proof (chunk_user_aligned E P D s cb cm WF Hcm) as UA. unfold user_lo in UA.
  pose proof (blk_hi_mod16 s cb cm WF Hcm) as HA.
  assert (U16 : cm_user_beg cm + 16 <= blk_hi s cm).
  { apply Z.mod_divide in UA; [|lia]. destruct UA as [u Hu]. apply Z.mod_divide in HA; [|lia]. destruct HA as [h Hh]. nia. }
  destruct H as [H|[[Hrz H]|H]].
  - rewrite <- CB, C in H. split; [lia|]. destruct (cm_state cm); [lia| exact I].
  - unfold blk_lo in *. split; [lia|]. destruct (cm_state cm); [lia| exact I].
  - destruct (cm_state cm); [destruct H|]. unfold blk_lo in *. split; [lia| exact I].
Qed.

(* [comment removed for export] *)
Lemma block_where : forall s cb cm, AWF s -> as_chunks s !! cb = Some cm ->
  (SB <= blk_lo cm /\ blk_hi s cm <= SB + kSpaceSize
   /\ exists c, 1 <= c <= kLargestClassID /\ cm_prim cm = Some c /\ carved E s c (blk_lo cm)
      /\ region_beg SB c <= blk_lo cm /\ blk_hi s cm <= region_beg SB c + kFreeArrayOffset /\ blk_hi s cm = blk_lo cm + class_size c)
  \/ (exists sc, In sc (as_sec s) /\ cm_prim cm = None /\ blk_lo cm = sc_map_beg sc + kPageSize /\ blk_hi s cm = sc_map_beg sc + sc_map_size sc).
Proof.
  intros s cb cm WF Hcm. pose proof (chunk_block_committed E P D s cb cm WF Hcm) as CB.
  pose proof WF as (WE & WR & _ & [K1 _] & _). destruct (K1 _ _ Hcm) as (_ & Bn & _ & D0 & _).
  unfold blk_hi in *. destruct (cm_prim cm) as [c|].
  - left. destruct CB as (Hc & L1 & L2). destruct D0 as (_ & _ & CV & _).
    pose proof (carved_range E s c _ Hc WR CV) as [R1 R2]. pose proof (carved_in_space E s c _ Hc WR CV) as [I1 I2].
    unfold blk_lo in *. unfold kRegionSize in *. split; [lia|]. split; [lia|].
    exists c. repeat split; try assumption; try lia.
  - right. destruct CB as (sc & Hsc & L1 & L2). exists sc. auto.
Qed.

Lemma pos_mod_ge : forall x k, 0 < x -> x mod k = 0 -> 0 < k -> k <= x.
Proof.
  intros x k Hx Hm Hk. apply Z.mod_divide in Hm; [|lia]. destruct Hm as [q ->].
  assert (1 <= q) by (destruct (Z_lt_le_dec q 1); [exfalso; assert (k * q <= k * 0) by (apply Z.mul_le_mono_nonneg_l; lia); lia| lia]).
  nia.
Qed.

(* [comment removed for export] *)
Definition live_free (s : astate) (a : Z) : Prop :=
  forall cb cm i, as_chunks s !! cb = Some cm -> cm_state cm = CAllocated i -> ~ (cm_user_beg cm <= a < cm_user_beg cm + cm_n cm).

Lemma live_free_outside : forall s a, AWF s ->
  (a < SB \/ SB + kSpaceSize <= a) ->
  (forall sc, In sc (as_sec s) -> ~ (sc_map_beg sc + kPageSize <= a < sc_map_beg sc + sc_map_size sc)) ->
  live_free s a.
Proof.
  intros s a WF OUT SEC cb cm i Hcm ST R.
  pose proof (chunk_user_in_block E P D s cb cm WF Hcm) as (A & B & _). unfold user_lo, user_hi in *.
  destruct (block_where s cb cm WF Hcm) as [(I1 & I2 & _)|(sc & Hsc & _ & L1 & L2)]; [lia|].
  apply (SEC sc Hsc). lia.
Qed.

Lemma fs_false_of_disj : forall a lo n, lo <= a < lo + n ->
  (lo + n <= ae_fs_beg E \/ ae_fs_beg E + ae_fs_len E <= lo) -> in_fakestack E a = false.
Proof.
  intros a lo n Ha DJ. unfold in_fakestack. apply Bool.andb_false_iff.
  destruct DJ; [left; apply Z.leb_gt; lia| right; apply Z.ltb_ge; lia].
Qed.

Lemma secchunk_eq_dec : forall a b : secchunk, {a = b} + {a <> b}.
Proof. intros [a1 a2 a3] [b1 b2 b3]. destruct (Z.eq_dec a1 b1), (Z.eq_dec a2 b2), (Z.eq_dec a3 b3); subst; try (left; reflexivity); right; intros H; injection H; intros; subst; contradiction. Qed.

Lemma fp_locate : forall s a, AWF s -> blocks_sep s -> FP s a ->
     in_ranges (arep_img_ranges ++ depot_static) a
  \/ (sh_band a /\ exists g v, a = kShadowBase + g /\ Sh E s (8 * g) = Some v)
  \/ (app_addr a /\ in_img E a = false /\ in_fakestack E a = false /\ live_free s a).
Proof.
  intros s a WF BS H. pose proof WF as (WE & WR & WC & [K1 K2] & WQ & WS & WD). pose proof WS as (_ & _ & S3 & S4 & S5).
  pose proof WE as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27 & E28
                    & IMG1 & IMG2 & IMG3 & IST & ISP & ISF & ISI).
  (* [comment removed for export] *)
  assert (SECR : forall sc b k, In sc (as_sec s) -> In (b, k) (ae_reserved E) ->
                 sc_map_beg sc + sc_map_size sc <= b \/ b + k <= sc_map_beg sc).
  { intros sc b k Hsc Hr. destruct (S3 sc Hsc) as (_ & _ & _ & _ & _ & _ & RSV). exact (RSV _ Hr). }
  (* [comment removed for export] *)
  assert (SECI : forall sc, In sc (as_sec s) -> img_sep E (sc_map_beg sc) (sc_map_size sc)).
  { intros sc Hsc. unfold img_sep. destruct (ae_img E) as [ib il] eqn:EI. cbn [fst snd]. apply (SECR sc ib il Hsc). first [exact IMG1| rewrite <- EI; exact IMG1]. }
  (* [comment removed for export] *)
  assert (HIGH : forall x, ae_resv_beg E <= x < ae_resv_beg E + 0x2000011000 -> app_addr x /\ in_img E x = false).
  { intros x Hx. apply high_obj_addr; [exact WE| lia]. }
  destruct H as [H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]].
  - (* [comment removed for export] *) left. destruct H as (r & Hr & X). exists r. split; [apply in_app_iff; left; exact Hr| exact X].
  - (* [comment removed for export] *)
    right; right. unfold RI, ae_region_info in H. unfold kRegSize, kNumClasses in H.
    destruct (HIGH a ltac:(unfold kSpaceSize in *; unfold SB in *; lia)) as [A1 A2]. split; [exact A1|]. split; [exact A2|]. split.
    + eapply (fs_false_of_disj a (ae_resv_beg E) 0x2000011000); [unfold kSpaceSize in *; unfold SB in *; lia| ]. unfold kSpaceSize in *; lia.
    + apply live_free_outside; [exact WF| unfold SB in *; lia|]. intros sc Hsc R.
      destruct (SECR sc _ _ Hsc E7). all: unfold kSpaceSize, kPageSize in *; unfold SB in *; lia.
  - (* [comment removed for export] *)
    right; right. destruct H as (r & Hr & X).
    assert (TP : T <= a < T + 4096).
    { unfold arep_thr_ranges in Hr. unfold kThrStackTop, kThrQCache, kThrCache, kPerClassSize, kNumClasses, kThrCacheStats, kThrStats, kThrUnwinding in Hr.
      cbn in Hr. destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; cbn [fst snd] in X; lia. }
    unfold T in *. destruct (app_obj_addr _ _ a E14 IST TP) as [A1 A2]. split; [exact A1|]. split; [exact A2|].
    split; [eapply (fs_false_of_disj a (ae_thread E) 4096); [lia| exact E21]|].
    apply live_free_outside; [exact WF| unfold kSpaceSize in *; unfold SB in *; lia|]. intros sc Hsc R.
    destruct (SECR sc _ _ Hsc E13); unfold kPageSize in *; lia.
  - (* [comment removed for export] *)
    right; right. destruct H as (c & Hc & X).
    assert (RG : 0 <= rg_mapped_fa (region_of s c) <= kFreeArraySize).
    { destruct WR as [WR0 WR1]. destruct (Z_le_dec 1 c); [destruct (Z_le_dec c kLargestClassID)|].
      - destruct (WR1 c ltac:(lia)) as (_ & _ & _ & _ & A3 & _ & A4 & _). cbn in A3, A4. lia.
      - unfold region_of, get_region. destruct (as_regions s !! c) as [r|] eqn:Hr; [pose proof (WR0 c r Hr); lia|]. cbn. unfold kFreeArraySize; lia.
      - unfold region_of, get_region. destruct (as_regions s !! c) as [r|] eqn:Hr; [pose proof (WR0 c r Hr); unfold kNumClasses in Hc; lia|]. cbn. unfold kFreeArraySize; lia. }
    assert (SP : SB <= a < SB + kSpaceSize /\ region_beg SB c + kFreeArrayOffset <= a < region_beg SB c + kRegionSize).
    { unfold free_array, region_beg, kRegionSize, kFreeArrayOffset, kFreeArraySize, kNumClasses, kSpaceSize in *. nia. }
    destruct SP as [SP1 SP2].
    destruct (HIGH a ltac:(unfold kSpaceSize in *; unfold SB in *; lia)) as [A1 A2]. split; [exact A1|]. split; [exact A2|]. split.
    + eapply (fs_false_of_disj a (ae_resv_beg E) 0x2000011000); unfold kSpaceSize in *; unfold SB in *; lia.
    + intros cb cm i Hcm ST R. pose proof (chunk_user_in_block E P D s cb cm WF Hcm) as (A & B & _). unfold user_lo, user_hi in *.
      destruct (block_where s cb cm WF Hcm) as [(I1 & I2 & c' & Hc' & _ & _ & G1 & G2 & G3)|(sc & Hsc & _ & L1 & L2)].
      * (* [comment removed for export] *)
        destruct (Z.eq_dec c c') as [->|NE]; [lia|].
        unfold region_beg, kRegionSize, kFreeArrayOffset in *.
        destruct (Z_lt_le_dec c c'); nia.
      * destruct (S3 sc Hsc) as (_ & _ & _ & _ & _ & OUT & _). unfold kPageSize in *. unfold SB in *. lia.
  - (* [comment removed for export] *)
    right; right. unfold kChunksBlockCount in H.
    destruct (app_obj_addr _ _ a E16 ISP ltac:(lia)) as [A1 A2]. split; [exact A1|]. split; [exact A2|].
    split; [eapply (fs_false_of_disj a (ae_ptr_array E) 0x800000); [lia| exact E22]|].
    apply live_free_outside; [exact WF| unfold kSpaceSize in *; unfold SB in *; lia|]. intros sc Hsc R.
    destruct (SECR sc _ _ Hsc E8); unfold kPageSize in *; lia.
  - (* [comment removed for export] *)
    right; right. destruct H as (sc & Hsc & X). destruct (S3 sc Hsc) as (AL & HB & CE & POS & MODS & OUT & RSV).
    pose proof (pos_mod_ge _ _ POS MODS ltac:(unfold kPageSize; lia)) as GE.
    destruct (app_obj_addr _ _ a HB (SECI sc Hsc) ltac:(unfold kPageSize in *; lia)) as [A1 A2]. split; [exact A1|]. split; [exact A2|]. split.
    + eapply (fs_false_of_disj a (sc_map_beg sc) (sc_map_size sc)); [unfold kPageSize in *; lia| exact (RSV _ E9)].
    + intros cb cm i Hcm ST R. pose proof (chunk_user_in_block E P D s cb cm WF Hcm) as (A & B & _). unfold user_lo, user_hi in *.
      destruct (block_where s cb cm WF Hcm) as [(I1 & I2 & _)|(sc' & Hsc' & _ & L1 & L2)]; [unfold kPageSize in *; unfold SB in *; lia|].
      destruct (secchunk_eq_dec sc sc') as [<-|NE]; [unfold kPageSize in *; lia|].
      destruct (S5 sc sc' Hsc Hsc' NE); unfold kPageSize in *; lia.
  - (* [comment removed for export] *)
    right; right. destruct H as (cb & cm & Hcm & X). pose proof (chunk_meta_in_block s cb cm a WF Hcm X) as [BL BU].
    pose proof (chunk_user_in_block E P D s cb cm WF Hcm) as (A & B & _). unfold user_lo, user_hi in *.
    destruct (block_where s cb cm WF Hcm) as [(I1 & I2 & c & Hc & _ & CV & G1 & G2 & G3)|(sc & Hsc & _ & L1 & L2)].
    + destruct (HIGH a ltac:(unfold kSpaceSize in *; unfold SB in *; lia)) as [A1 A2]. split; [exact A1|]. split; [exact A2|]. split.
      * eapply (fs_false_of_disj a (ae_resv_beg E) 0x2000011000); unfold kSpaceSize in *; unfold SB in *; lia.
      * intros cb' cm' i Hcm' ST R. destruct (Z.eq_dec cb cb') as [<-|NE].
        { rewrite Hcm in Hcm'. injection Hcm' as <-. rewrite ST in BU. lia. }
        pose proof (chunk_user_in_block E P D s cb' cm' WF Hcm') as (A' & B' & _). unfold user_lo, user_hi in *.
        destruct (chunks_disjoint E P D s cb cm cb' cm' WF Hcm Hcm' NE); lia.
    + destruct (S3 sc Hsc) as (AL & HB & CE & POS & MODS & OUT & RSV).
      destruct (app_obj_addr _ _ a HB (SECI sc Hsc) ltac:(unfold kPageSize in *; lia)) as [A1 A2]. split; [exact A1|]. split; [exact A2|]. split.
      * eapply (fs_false_of_disj a (sc_map_beg sc) (sc_map_size sc)); [unfold kPageSize in *; lia| exact (RSV _ E9)].
      * intros cb' cm' i Hcm' ST R. destruct (Z.eq_dec cb cb') as [<-|NE].
        { rewrite Hcm in Hcm'. injection Hcm' as <-. rewrite ST in BU. lia. }
        pose proof (chunk_user_in_block E P D s cb' cm' WF Hcm') as (A' & B' & _). unfold user_lo, user_hi in *.
        destruct (chunks_disjoint E P D s cb cm cb' cm' WF Hcm Hcm' NE); lia.
  - (* [comment removed for export] *)
    right; right. destruct H as (b & Hb & X).
    destruct (batch_block E D s b WQ ltac:(unfold all_batches; rewrite app_assoc; apply in_app_iff; left; exact Hb)) as (CV & _ & _ & NCB).
    assert (HB24 : 1 <= kBatchClass <= kLargestClassID) by (unfold kBatchClass, kLargestClassID; lia).
    pose proof (carved_in_space E s kBatchClass _ HB24 WR CV) as [I1 I2].
    assert (CS : class_size kBatchClass = 8192) by reflexivity.
    destruct (HIGH a ltac:(unfold kBatchCap, kSpaceSize, kRegionSize in *; unfold SB in *; lia)) as [A1 A2]. split; [exact A1|]. split; [exact A2|]. split.
    + eapply (fs_false_of_disj a (ae_resv_beg E) 0x2000011000); unfold kBatchCap, kSpaceSize, kRegionSize in *; unfold SB in *; lia.
    + intros cb cm i Hcm ST R. pose proof (chunk_user_in_block E P D s cb cm WF Hcm) as (A & B & _). unfold user_lo, user_hi in *.
      destruct (block_where s cb cm WF Hcm) as [(J1 & J2 & c & Hc & PR & CVc & G1 & G2 & G3)|(sc & Hsc & _ & L1 & L2)].
      * destruct (carved_blocks_disjoint E s c (blk_lo cm) kBatchClass (b_addr b) Hc HB24 WR CVc CV) as [[_ EQ]|DJ].
        { exfalso. apply NCB. exists cb, cm. split; [exact Hcm| unfold blk_lo in EQ; exact EQ]. }
        unfold kBatchCap in *. lia.
      * destruct (S3 sc Hsc) as (_ & _ & _ & _ & _ & OUT & _). unfold kBatchCap, kPageSize, kSpaceSize, kRegionSize in *. unfold SB in *. lia.
  - (* [comment removed for export] *)
    destruct (depot_fp_where s a BS H) as [(r & Hr & X)|(X1 & X1' & X2 & X3 & X4)].
    + left. exists r. split; [apply in_app_iff; right; exact Hr| exact X].
    + right; right. split; [exact X1|]. split; [exact X1'|]. split; [exact X4|].
      apply live_free_outside; [exact WF| unfold kSpaceSize in *; unfold SB in *; lia|]. intros sc Hsc R. apply (X3 sc Hsc). unfold kPageSize in *; lia.
  - (* [comment removed for export] *)
    right; left. destruct H as (g & v & -> & SH). split; [| exists g, v; auto].
    replace (kShadowBase + g) with (mem_to_shadow (8 * g)) by (unfold mem_to_shadow; rewrite Z.mul_comm, Z.div_mul by lia; reflexivity).
    apply sh_band_of_granule.
    unfold Sh in SH. destruct (in_some_region_map E s (8 * g)) eqn:RM.
    + right. pose proof (region_map_in_space E P D s (8 * g) WF RM). pose proof alloc_ceiling_le_high_end. unfold kSpaceSize in *. unfold SB in *. lia.
    + destruct (in_some_sec_map s (8 * g)) eqn:SM.
      * unfold in_some_sec_map in SM. apply existsb_exists in SM as (sc & Hsc & Hb). apply andb_true_iff in Hb as [B1 B2].
        apply Z.leb_le in B1. apply Z.ltb_lt in B2. destruct (S3 sc Hsc) as (_ & HB & S & _).
        pose proof alloc_ceiling_le_high_end. unfold app_mem in HB. lia.
      * cbn [orb] in SH. destruct (sh_default_dom E (8 * g) && negb (sh_excluded E (8 * g))) eqn:C; [|discriminate].
        apply andb_true_iff in C as [C _]. unfold sh_default_dom in C. apply Bool.orb_true_iff in C as [C|C].
        -- apply andb_true_iff in C as [C _]. apply andb_true_iff in C as [C1 C2]. apply Z.leb_le in C1. apply Z.ltb_lt in C2. left; lia.
        -- apply andb_true_iff in C as [C1 C2]. apply Z.leb_le in C1. apply Z.leb_le in C2. right; lia.
Qed.

(* [comment removed for export] *)
Corollary fp_below_ceiling : forall s a, AWF s -> blocks_sep s -> FP s a -> a < alloc_ceiling.
Proof.
  intros s a WF BS H. pose proof WF as (WE & _).
  pose proof WE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & IMG1 & IMG2 & IMG3 & _).
  pose proof kHighMemBeg_lt_ceiling as KC.
  destruct (fp_locate s a WF BS H) as [(r & Hr & X)|[[X _]|(X & _)]].
  - pose proof (IMG_IN r Hr). rewrite kLowAppEnd_val, kHighMemBeg_val in *. lia.
  - pose proof (sh_band_below_ceiling a X). rewrite kHighMemBeg_val in *. lia.
  - exact (proj2 (app_addr_below_ceiling a X)).
Qed.
Corollary fp_stack_free : forall s a, AWF s -> blocks_sep s -> alloc_ceiling <= a -> ~ FP s a.
Proof. intros s a WF BS Ha H. pose proof (fp_below_ceiling s a WF BS H). lia. Qed.

(* [comment removed for export] *)
Corollary fp_img_free : forall s a, AWF s -> blocks_sep s -> in_img E a = true ->
  ~ in_ranges (arep_img_ranges ++ depot_static) a -> ~ FP s a.
Proof.
  intros s a WF BS Ha NI H. pose proof WF as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & IMG1 & IMG2 & IMG3 & _) & _).
  unfold in_img in Ha. apply andb_true_iff in Ha as [Ha1 Ha2]. apply Z.leb_le in Ha1. apply Z.ltb_lt in Ha2.
  destruct (fp_locate s a WF BS H) as [X|[[X _]|(_ & X & _)]]; [exact (NI X)| |].
  - pose proof (sh_band_below_ceiling a X). lia.
  - unfold in_img in X. apply Bool.andb_false_iff in X. destruct X as [X|X]; [apply Z.leb_gt in X| apply Z.ltb_ge in X]; lia.
Qed.

(* [comment removed for export] *)
Corollary fp_fs_free : forall s a, AWF s -> blocks_sep s -> in_fakestack E a = true -> ~ FP s a.
Proof.
  intros s a WF BS FS H. pose proof WF as ((E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27 & E28
                    & IMG1 & IMG2 & IMG3 & IST & ISP & ISF & ISI) & _).
  pose proof FS as FS'. unfold in_fakestack in FS'. apply andb_true_iff in FS' as [F1 F2]. apply Z.leb_le in F1. apply Z.ltb_lt in F2.
  destruct (fp_locate s a WF BS H) as [(r & Hr & X)|[[X _]|(_ & _ & X & _)]].
  - pose proof (IMG_IN r Hr). unfold img_sep in ISF. lia.
  - pose proof (sh_band_not_app a X) as NA. apply NA. eapply app_mem_addr; [exact E10| lia].
  - rewrite FS in X. discriminate.
Qed.

(* [comment removed for export] *)
Corollary fp_fs_shadow_free : forall s g, AWF s -> blocks_sep s -> in_fakestack E (8 * g) = true -> ~ FP s (kShadowBase + g).
Proof.
  intros s g WF BS FS H. pose proof WF as ((E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27 & E28
                    & IMG1 & IMG2 & IMG3 & IST & ISP & ISF & ISI) & _).
  pose proof FS as FS'. unfold in_fakestack in FS'. apply andb_true_iff in FS' as [F1 F2]. apply Z.leb_le in F1. apply Z.ltb_lt in F2.
  assert (BAND : sh_band (kShadowBase + g)).
  { replace (kShadowBase + g) with (mem_to_shadow (8 * g)) by (unfold mem_to_shadow; rewrite Z.mul_comm, Z.div_mul by lia; reflexivity).
    apply sh_band_of_granule. pose proof (app_mem_addr _ _ (8 * g) E10 ltac:(lia)) as AA. unfold app_addr in AA. pose proof alloc_ceiling_le_high_end. lia. }
  destruct (fp_locate s _ WF BS H) as [(r & Hr & X)|[[_ (g' & v & EQ & SH)]|(X & _)]].
  - pose proof (IMG_IN r Hr). pose proof (sh_band_below_ceiling _ BAND). lia.
  - assert (g' = g) by lia. subst g'. rewrite (Sh_fs_none E P D s (8 * g) WF FS) in SH. discriminate.
  - exact (sh_band_not_app _ BAND X).
Qed.

(* [comment removed for export] *)
Corollary fp_live_free : forall s a cb cm i, AWF s -> blocks_sep s ->
  as_chunks s !! cb = Some cm -> cm_state cm = CAllocated i -> cm_user_beg cm <= a < cm_user_beg cm + cm_n cm -> ~ FP s a.
Proof.
  intros s a cb cm i WF BS Hcm ST R H. pose proof WF as (WE & _ & _ & _ & _ & (_ & _ & S3 & _) & _).
  pose proof WE as (_ & E2 & E3 & E4 & E5 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & IMG1 & IMG2 & IMG3 & _).
  pose proof (chunk_user_in_block E P D s cb cm WF Hcm) as (A & B & _). unfold user_lo, user_hi in *.
  (* [comment removed for export] *)
  assert (HI : app_addr a /\ in_img E a = false).
  { destruct (block_where s cb cm WF Hcm) as [(I1 & I2 & _)|(sc & Hsc & _ & L1 & L2)].
    - apply high_obj_addr; [exact WE| unfold kSpaceSize in *; unfold SB in *; lia].
    - destruct (S3 sc Hsc) as (_ & HB & _ & _ & _ & _ & RSV). eapply (app_obj_addr _ _ a HB); [| unfold kPageSize in *; lia].
      unfold img_sep. destruct (ae_img E) as [ib il] eqn:EI. cbn [fst snd]. apply (RSV (ib, il)). first [exact IMG1| rewrite <- EI; exact IMG1]. }
  destruct HI as [HA HIm].
  destruct (fp_locate s a WF BS H) as [(r & Hr & X)|[[X _]|(_ & _ & _ & LF)]].
  - pose proof (IMG_IN r Hr). unfold in_img in HIm. apply Bool.andb_false_iff in HIm. destruct HIm as [Y|Y]; [apply Z.leb_gt in Y| apply Z.ltb_ge in Y]; lia.
  - exact (sh_band_not_app _ X HA).
  - exact (LF cb cm i Hcm ST R).
Qed.

End KIT.
End RF.
End RC__1.
