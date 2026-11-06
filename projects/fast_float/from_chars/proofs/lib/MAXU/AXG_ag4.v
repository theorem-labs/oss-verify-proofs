(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk SeqExec AxSymExec3 AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfFrame OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGroup.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng MngRepr MngHeap MngWb MngWk MngGeoX MngLt MngSurgery MngExc MngGM MngNtfPre MngCtx MngCtx2 MngShape.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import MngNtfM MngNtfS MngMWP MngMW0 MngMW1 MngMW2 AXG_as1 AXG_as5 AXG_am1 AXG_amr0 AXG_ag0 AXG_ag2 AXG_ag3.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ctx_same3 (s s' : astate) : Prop :=
  st_init_done s' = st_init_done s /\ st_mmap_counter s' = st_mmap_counter s /\ st_free_meta_head s' = st_free_meta_head s /\
  st_areas s' = st_areas s /\ st_avail_meta s' = st_avail_meta s /\ st_avail_meta_count s' = st_avail_meta_count s /\
  st_avail_meta_area_count s' = st_avail_meta_area_count s /\ st_meta_alloc_shift s' = st_meta_alloc_shift s /\
  st_area_head s' = st_area_head s /\ st_area_tail s' = st_area_tail s /\ st_avail_meta_areas s' = st_avail_meta_areas s /\
  st_brk s' = st_brk s /\ st_active s' = st_active s /\ st_usage s' = st_usage s /\ st_metas s' = st_metas s /\
  st_regions s' = st_regions s.

Lemma s3_same : forall s sc, ctx_same3 s (ag_s3 s sc).
Proof.
  intros s sc. unfold ag_s3, sq_st, ab_st. destruct (bounce_idx sc) as [k|].
  - destruct (negb (znth k (st_unmap_seq s) =? 0) && (st_seq s - znth k (st_unmap_seq s) <? 10));
      (destruct (st_seq _ =? 255)); cbn; repeat split; reflexivity.
  - destruct (st_seq s =? 255); cbn; repeat split; reflexivity.
Qed.

Lemma s3_seq : forall s sc, st_seq (ag_s3 s sc) = if st_seq s =? 255 then 1 else st_seq s + 1.
Proof.
  intros s sc. unfold ag_s3, sq_st, ab_st. destruct (bounce_idx sc) as [k|].
  - destruct (negb (znth k (st_unmap_seq s) =? 0) && (st_seq s - znth k (st_unmap_seq s) <? 10)); cbn [st_seq set_bounces];
      destruct (st_seq s =? 255); reflexivity.
  - destruct (st_seq s =? 255); reflexivity.
Qed.

Lemma s3_unmap : forall s sc, st_unmap_seq (ag_s3 s sc) = if st_seq s =? 255 then repeat 0 32 else st_unmap_seq s.
Proof.
  intros s sc. unfold ag_s3, sq_st, ab_st. destruct (bounce_idx sc) as [k|].
  - destruct (negb (znth k (st_unmap_seq s) =? 0) && (st_seq s - znth k (st_unmap_seq s) <? 10)); cbn [st_seq set_bounces];
      destruct (st_seq s =? 255); reflexivity.
  - destruct (st_seq s =? 255); reflexivity.
Qed.

Lemma s3_bounces : forall s sc, st_bounces (ag_s3 s sc) = st_bounces (ab_st s sc).
Proof. intros s sc. unfold ag_s3, sq_st. destruct (st_seq (ab_st s sc) =? 255); reflexivity. Qed.

Lemma Inv_s3 : forall X R U s sc, Inv X R U s -> Inv X R U (ag_s3 s sc).
Proof.
  intros X R U s sc HI.
  pose proof (account_bounce_spec X R U s sc (fun r => Inv X R U (snd r)) HI (fun s' H _ => H)) as H1.
  rewrite account_bounce_eq in H1. cbn [itok fst snd] in H1.
  pose proof (step_seq_spec X R U (ab_st s sc) (fun r => Inv X R U (snd r)) H1 (fun s' H _ => H)) as H2.
  rewrite step_seq_eq in H2. cbn [itok fst snd] in H2. exact H2.
Qed.

Lemma XNM_same : forall X s s', st_metas s' = st_metas s -> XNM X s -> XNM X s'.
Proof. intros X s s' E H x Hx. unfold MT. rewrite E. exact (H x Hx). Qed.

Lemma footprint_same : forall s s', st_areas s' = st_areas s -> st_regions s' = st_regions s -> footprint s' = footprint s.
Proof.
  intros s s' Ea Er. unfold footprint. rewrite Ea. f_equal. f_equal. rewrite Er. apply flat_map_ext. intros k.
  unfold region_of. rewrite Er. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma cov_ctx3 : forall s s' c, ctx_same3 s s' -> In c (ctx_cells s') ->
  In c (ctx_cells s) \/ c = seq_cell (st_seq s') \/ (exists k, (k < 32)%nat /\ c = unm_cell k (nth k (st_unmap_seq s') 0)) \/
  (exists k, (k < 32)%nat /\ c = bnc_cell k (nth k (st_bounces s') 0)).
Proof.
  intros s s' c (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & _) Hc.
  unfold ctx_cells in Hc. rewrite E1, E2, E3, E4, E5, E6, E7, E8, E9, E10, E11, E12, E13, E14 in Hc.
  apply in_app_iff in Hc as [Hc|Hc].
  - cbn [In] in Hc.
    repeat (destruct Hc as [<-|Hc]; [first [ (right; left; reflexivity)
                                           | (left; unfold ctx_cells; apply in_app_iff; left; cbn [In]; repeat first [ (left; reflexivity) | right ]) ] |]).
    destruct Hc.
  - apply in_app_iff in Hc as [Hc|Hc]; [left; unfold ctx_cells; apply in_app_iff; right; apply in_app_iff; left; exact Hc|].
    apply in_app_iff in Hc as [Hc|Hc]; [left; unfold ctx_cells; apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; left; exact Hc|].
    apply in_app_iff in Hc as [Hc|Hc].
    + right. right. left. apply in_map_iff in Hc as (k & <- & Hk). apply in_seq in Hk. exists k. split; [lia | reflexivity].
    + right. right. right. apply in_map_iff in Hc as (k & <- & Hk). apply in_seq in Hk. exists k. split; [lia | reflexivity].
Qed.

Lemma rev_ctx3 : forall s s' c, ctx_same3 s s' -> In c (ctx_cells s) ->
  In c (ctx_cells s') \/ c = seq_cell (st_seq s) \/ (exists k, (k < 32)%nat /\ c = unm_cell k (nth k (st_unmap_seq s) 0)) \/
  (exists k, (k < 32)%nat /\ c = bnc_cell k (nth k (st_bounces s) 0)).
Proof.
  intros s s' c (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & _) Hc.
  unfold ctx_cells in Hc.
  apply in_app_iff in Hc as [Hc|Hc].
  - cbn [In] in Hc.
    repeat (destruct Hc as [<-|Hc]; [first [ (right; left; reflexivity)
                                           | (left; unfold ctx_cells; rewrite E1, E2, E3, E4, E5, E6, E7, E8, E9, E10, E11, E12;
                                              apply in_app_iff; left; cbn [In]; repeat first [ (left; reflexivity) | right ]) ] |]).
    destruct Hc.
  - apply in_app_iff in Hc as [Hc|Hc]; [left; unfold ctx_cells; rewrite E13; apply in_app_iff; right; apply in_app_iff; left; exact Hc|].
    apply in_app_iff in Hc as [Hc|Hc]; [left; unfold ctx_cells; rewrite E14; apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; left; exact Hc|].
    apply in_app_iff in Hc as [Hc|Hc].
    + right. right. left. apply in_map_iff in Hc as (k & <- & Hk). apply in_seq in Hk. exists k. split; [lia | reflexivity].
    + right. right. right. apply in_map_iff in Hc as (k & <- & Hk). apply in_seq in Hk. exists k. split; [lia | reflexivity].
Qed.

(* [comment removed for export] *)
Definition C3 (s : astate) : list mcell :=
  seq_cell (st_seq s) :: map (fun k => unm_cell k (nth k (st_unmap_seq s) 0)) (seq 0 32) ++ map (fun k => bnc_cell k (nth k (st_bounces s) 0)) (seq 0 32).

Lemma C3_in : forall s c, In c (C3 s) -> In c (image s).
Proof.
  intros s c Hc. unfold C3 in Hc. destruct Hc as [<-|Hc]; [exact (seq_cell_in s)|].
  apply in_app_iff in Hc as [Hc|Hc]; apply in_map_iff in Hc as (k & <- & Hk); apply in_seq in Hk.
  - apply unm_cell_in. lia.
  - apply bnc_cell_in. lia.
Qed.

Lemma cov_s3 : forall s s' c, ctx_same3 s s' -> In c (image s') -> In c (image s) \/ In c (C3 s').
Proof.
  intros s s' c E Hc. pose proof E as (_ & _ & _ & Ea & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Em & _).
  destruct (cov_ctx_only s s' c Em Ea Hc) as [H|H]; [left; exact H|].
  destruct (cov_ctx3 s s' c E H) as [A|[A|[(k & Hk & A)|(k & Hk & A)]]].
  - left. apply ctx_in_image. exact A.
  - right. unfold C3. left. symmetry. exact A.
  - right. unfold C3. right. apply in_app_iff. left. subst c. apply (in_map (fun k => unm_cell k (nth k (st_unmap_seq s') 0))). apply in_seq. lia.
  - right. unfold C3. right. apply in_app_iff. right. subst c. apply (in_map (fun k => bnc_cell k (nth k (st_bounces s') 0))). apply in_seq. lia.
Qed.

Lemma rev_s3 : forall L s s' c, ctx_same3 s s' -> In c (image s) ->
  In c (image s') \/ exists c', In c' (C3 s') /\ cell_range L c' = cell_range L c.
Proof.
  intros L s s' c E Hc. pose proof E as (_ & _ & _ & Ea & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Em & _).
  unfold image in Hc. apply in_app_iff in Hc as [Hc|Hc].
  - destruct (rev_ctx3 s s' c E Hc) as [A|[A|[(k & Hk & A)|(k & Hk & A)]]].
    + left. apply ctx_in_image. exact A.
    + right. exists (seq_cell (st_seq s')). split; [unfold C3; left; reflexivity|]. subst c. reflexivity.
    + right. exists (unm_cell k (nth k (st_unmap_seq s') 0)). split; [|subst c; reflexivity].
      unfold C3. right. apply in_app_iff. left. apply (in_map (fun k => unm_cell k (nth k (st_unmap_seq s') 0))). apply in_seq. lia.
    + right. exists (bnc_cell k (nth k (st_bounces s') 0)). split; [|subst c; reflexivity].
      unfold C3. right. apply in_app_iff. right. apply (in_map (fun k => bnc_cell k (nth k (st_bounces s') 0))). apply in_seq. lia.
  - left. unfold image. apply in_app_iff. right. rewrite Ea. rewrite (areas_cells_metas s s' _ Em), (used_metas_metas s s' Em). exact Hc.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac side := cbn [length word_to_le_bytes Z_to_le_bytes]; (rewrite ?u_wa_small by lia); lia.

Lemma mmw_frame_out : forall m spm sc mt len s4 s5 x, 0 <= x < 2^64 -> 2^20 <= spm <= 2^47 -> ~ (spm - 56 <= x < spm) ->
  mmw_frame m spm sc mt len s4 s5 (wa x) = m (wa x).
Proof. intros m spm sc mt len s4 s5 x Hx Hs Hn. unfold mmw_frame. rewrite !MngWb.wbytes_out by side. reflexivity. Qed.

Lemma sq_mem_out : forall m seq x, 0 <= x < 2^64 -> ~ (622568 <= x < 622600) -> x <> 622632 -> sq_mem m seq (wa x) = m (wa x).
Proof. intros m seq x Hx H1 H2. unfold sq_mem. destruct (seq =? 255); rewrite !MngWb.wbytes_out by side; reflexivity. Qed.

Lemma ab_mem_out : forall m sc b useq seq x, 0 <= x < 2^64 -> 0 <= sc <= 47 -> x <> sc + 622593 -> ab_mem m sc b useq seq (wa x) = m (wa x).
Proof. intros m sc b useq seq x Hx Hsc H. unfold ab_mem. destruct (ab_hit sc useq seq); [rewrite MngWb.wbytes_out by side|]; reflexivity. Qed.

Lemma sq_mem_seq : forall m seq, sq_mem m seq (wa 622632) = Some (nth 0 (word_to_le_bytes 1 (wa (if seq =? 255 then 1 else seq + 1))) (Z_to_bv 8 0)).
Proof.
  intros m seq. unfold sq_mem. destruct (seq =? 255).
  - apply MngWb.wbytes_at_wa0; [lia | side | cbn; lia].
  - apply MngWb.wbytes_at_wa0; [lia | side | cbn; lia].
Qed.

Lemma sq_mem_unm : forall m k, 0 <= k < 32 -> sq_mem m 255 (wa (622568 + k)) = Some (nth 0 (word_to_le_bytes 1 (wa 0)) (Z_to_bv 8 0)).
Proof.
  intros m k Hk. unfold sq_mem. cbn [Z.eqb Pos.eqb]. rewrite MngWb.wbytes_out by side.
  assert (E : forall bs (M : word -> option byte) a j, bs = word_to_le_bytes 8 (wa 0) -> 0 <= a -> a + 8 <= 2^64 -> 0 <= j < 8 ->
             wbytes M (wa a) bs (wa (a + j)) = Some (nth 0 (word_to_le_bytes 1 (wa 0)) (Z_to_bv 8 0))).
  { intros bs M a j -> H1 H2 Hj. replace j with (Z.of_nat (Z.to_nat j)) by lia.
    rewrite (MngWb.wbytes_at_wa (word_to_le_bytes 8 (wa 0)) M a (Z.to_nat j)) by (first [exact H1 | side | rewrite length_N_to_le_bytes; lia]).
    f_equal. assert (Ej : (Z.to_nat j < 8)%nat) by lia. clear - Ej.
    destruct (Z.to_nat j) as [|[|[|[|[|[|[|[|]]]]]]]]; try lia; reflexivity. }
  destruct (Z_lt_ge_dec k 24) as [K1|K1].
  - rewrite MngWb.wbytes_out by side. destruct (Z_lt_ge_dec k 16) as [K2|K2].
    + rewrite MngWb.wbytes_out by side. destruct (Z_lt_ge_dec k 8) as [K3|K3].
      * rewrite MngWb.wbytes_out by side. replace (622568 + k) with (0 + 622568 + k) by ring. apply E; [reflexivity | lia | lia | lia].
      * replace (622568 + k) with (0 + 622576 + (k - 8)) by ring. apply E; [reflexivity | lia | lia | lia].
    + replace (622568 + k) with (0 + 622584 + (k - 16)) by ring. apply E; [reflexivity | lia | lia | lia].
  - replace (622568 + k) with (0 + 622592 + (k - 24)) by ring. apply E; [reflexivity | lia | lia | lia].
Qed.

Lemma ab_mem_hit : forall m sc b useq seq, 0 <= sc <= 47 -> ab_hit sc useq seq = true ->
  ab_mem m sc b useq seq (wa (sc + 622593)) = Some (nth 0 (word_to_le_bytes 1 (wa (ab_nb b))) (Z_to_bv 8 0)).
Proof. intros m sc b useq seq Hsc H. unfold ab_mem. rewrite H. apply MngWb.wbytes_at_wa0; [lia | side | cbn; lia]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma ab_hit_st : forall s sc, 0 <= sc <= 47 ->
  ab_hit sc (znth (sc - 7) (st_unmap_seq s)) (st_seq s) = true ->
  st_bounces (ab_st s sc) = zset (sc - 7) (ab_nb (znth (sc - 7) (st_bounces s))) (st_bounces s).
Proof.
  intros s sc Hsc H. unfold ab_hit, ab_tr in H. unfold ab_st, bounce_idx.
  destruct ((7 <=? sc) && (sc <? 39)); [|discriminate H]. cbn [andb] in H. rewrite H. reflexivity.
Qed.

Lemma ab_nohit_st : forall s sc, 0 <= sc <= 47 ->
  ab_hit sc (znth (sc - 7) (st_unmap_seq s)) (st_seq s) = false -> st_bounces (ab_st s sc) = st_bounces s.
Proof.
  intros s sc Hsc H. unfold ab_hit, ab_tr in H. unfold ab_st, bounce_idx.
  destruct ((7 <=? sc) && (sc <? 39)); [|reflexivity]. cbn [andb] in H. rewrite H. reflexivity.
Qed.

Section CUT3.
Variables (HTOP : Z) (X : list sptr) (R : option (sptr * Z)) (U : Z -> Z) (L : layout) (s : astate) (m : word -> option byte) (sp0 K sc : Z).
Variables (mt len s4 s5 : Z).
Hypothesis C : CUT HTOP X R U L s m sp0 K.
Hypothesis Hsc : 0 <= sc <= 47.
Hypothesis HK : 208 <= K.

Local Notation b := (znth (sc - 7) (st_bounces s)).
Local Notation useq := (znth (sc - 7) (st_unmap_seq s)).
Local Notation seq := (st_seq s).
Local Notation m3 := (mmw_frame (sq_mem (ab_mem m sc b useq seq) seq) (sp0 + -144) sc mt len s4 s5).
Local Notation s3 := (ag_s3 s sc).

#[using="Type"] Lemma m3_grows : mem_grows m m3.
Proof. LiaFast.lf_pins LiaFast.u0.
  apply (mem_grows_trans _ (sq_mem (ab_mem m sc b useq seq) seq)); [|unfold mmw_frame; repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl].
  apply (mem_grows_trans _ (ab_mem m sc b useq seq)).
  - unfold ab_mem. destruct (ab_hit sc useq seq); [apply wbytes_grows | apply mem_grows_refl].
  - unfold sq_mem. destruct (seq =? 255); repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl.
Qed.

#[using="C Hsc HK"] Theorem cut_s3 : CUT HTOP X R U L s3 m3 sp0 K /\ GROW sp0 K L s m L s3 m3.
Proof. LiaFast.lf_pins (fun (C Hsc HK : LiaFast.U) => LiaFast.u0).
  pose proof C as [HI HX N HG HD HT HTB].
  pose proof (nc_ctx _ _ _ _ _ _ _ N) as Hctx. pose proof (nc_sp1 _ _ _ _ _ _ _ N) as Hsp1. pose proof (nc_sp2 _ _ _ _ _ _ _ N) as Hsp2.
  pose proof (s3_same s sc) as SAME. pose proof SAME as (_ & _ & _ & Ea & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Em & Er).
  assert (OUT : forall x, 0 <= x < 2^64 -> ~ (sp0 - 200 <= x < sp0 - 144) -> x <> 622632 -> (seq = 255 -> ~ (622568 <= x < 622600)) ->
                  (ab_hit sc useq seq = true -> x <> sc + 622593) -> m3 (wa x) = m (wa x)).
  { intros x Hx N1 N2 N3 N4. rewrite mmw_frame_out by (clear - Hx N1 Hsp1 Hsp2 HK; lia).
    unfold sq_mem. destruct (seq =? 255) eqn:E9; [apply Z.eqb_eq in E9; specialize (N3 E9)|];
      rewrite !MngWb.wbytes_out by (clear - Hx N2 N3; side);
      unfold ab_mem; destruct (ab_hit sc useq seq) eqn:Eh; [specialize (N4 eq_refl); rewrite MngWb.wbytes_out by (clear - Hx N4 Hsc; side) | | specialize (N4 eq_refl); rewrite MngWb.wbytes_out by (clear - Hx N4 Hsc; side) |];
      reflexivity. }
  assert (Lc : forall o, loc_addr L (LCtx o) = 621720 + o) by (intros o; cbn [loc_addr]; rewrite Hctx; reflexivity).
  (* [comment removed for export] *)
  assert (OLD : forall c, In c (ctx_cells s) -> (forall x, in_rng (cell_range L c) x -> m3 (wa x) = m (wa x)) -> cell_holds L (bview SEGS m3) c).
  { intros c Hc Hx. apply (cell_holds_frame L (bview SEGS m)); [exact (image_cell_width s c (ctx_in_image s c Hc)) | exact (nc_ctx_holds L s m sp0 K c N Hc)|].
    intros x Hin. apply MngWb.bview_ext. exact (Hx x Hin). }
  apply (silent_step HTOP X R U X R U L s s3 m m3 sp0 K (C3 s3) C).
  - exact (Inv_s3 X R U s sc HI).
  - exact (XNM_same X s s3 Em HX).
  - exact Er.
  - intros rg Hrg. left. rewrite (footprint_same s s3 Ea Er) in Hrg. exact Hrg.
  - intros c Hc. exact (cov_s3 s s3 c SAME Hc).
  - exact (C3_in s3).
  - intros c Hc. exact (rev_s3 L s s3 c SAME Hc).
  - unfold C3. apply Forall_cons; [|apply Forall_app; split; apply Forall_forall; intros c Hc; apply in_map_iff in Hc as (k & <- & Hk); apply in_seq in Hk].
    + (* [comment removed for export] *)
      unfold seq_cell. apply holds_of_mem; cbn [mc_loc mc_w mc_val]; [intros z E; discriminate E | lia | rewrite Lc; unfold CTX_seq; lia | rewrite Lc; unfold CTX_seq; cbn; lia |].
      intros k Hk. assert (k = 0%nat) as -> by (cbn in Hk; lia). rewrite Lc. unfold CTX_seq. cbn [sval_num Z.of_nat].
      change (621720 + 912 + 0) with 622632. rewrite mmw_frame_out by (clear - Hsp1 Hsp2 HK; lia). rewrite sq_mem_seq. rewrite s3_seq. reflexivity.
    + (* [comment removed for export] *)
      rewrite s3_unmap. destruct (seq =? 255) eqn:E9.
      * apply Z.eqb_eq in E9. replace (nth k (repeat 0 32) 0) with 0 by (rewrite nth_repeat'; destruct (Nat.ltb k 32); reflexivity).
        unfold unm_cell. apply holds_of_mem; cbn [mc_loc mc_w mc_val]; [intros z E; discriminate E | lia | rewrite Lc; unfold CTX_unmap_seq; lia | rewrite Lc; unfold CTX_unmap_seq; cbn; lia |].
        intros j Hj. assert (j = 0%nat) as -> by (cbn in Hj; lia). rewrite Lc. unfold CTX_unmap_seq. cbn [sval_num].
        replace (621720 + (848 + Z.of_nat k) + Z.of_nat 0) with (622568 + Z.of_nat k) by lia.
        rewrite mmw_frame_out by (clear - Hk Hsp1 Hsp2 HK; lia). rewrite E9. apply sq_mem_unm. lia.
      * apply OLD; [apply unmap_in_ctx; lia|].
        intros x Hin. unfold in_rng, cell_range, unm_cell in Hin. cbn [mc_loc mc_w fst snd] in Hin. rewrite Lc in Hin. unfold CTX_unmap_seq in Hin.
        cbn [Z.of_nat Pos.of_succ_nat] in Hin. apply OUT; [clear - Hin Hk; lia | clear - Hin Hk Hsp1 HK; lia | clear - Hin Hk; lia | intros E; rewrite E in E9; discriminate E9 |].
        intros Eh. unfold ab_hit, ab_tr in Eh. destruct (7 <=? sc) eqn:E1; [|discriminate Eh]. apply Z.leb_le in E1. clear - Hin Hk E1. lia.
    + (* [comment removed for export] *)
      rewrite s3_bounces. destruct (ab_hit sc useq seq) eqn:Eh.
      * rewrite (ab_hit_st s sc Hsc Eh).
        assert (Hs7 : 7 <= sc < 39) by (unfold ab_hit, ab_tr in Eh; destruct (7 <=? sc) eqn:E1; destruct (sc <? 39) eqn:E2; cbn [andb] in Eh; try discriminate Eh;
                                        apply Z.leb_le in E1; apply Z.ltb_lt in E2; lia).
        pose proof (inv_ctx HI) as (_ & _ & _ & C4 & _).
        destruct (Nat.eq_dec k (Z.to_nat (sc - 7))) as [->|Hne].
        -- unfold zset. rewrite nth_zupd_same by (rewrite C4; lia).
           unfold bnc_cell. apply holds_of_mem; cbn [mc_loc mc_w mc_val]; [intros z E; discriminate E | lia | rewrite Lc; unfold CTX_bounces; lia | rewrite Lc; unfold CTX_bounces; cbn; lia |].
           intros j Hj. assert (j = 0%nat) as -> by (cbn in Hj; lia). rewrite Lc. unfold CTX_bounces. cbn [sval_num].
           replace (621720 + (880 + Z.of_nat (Z.to_nat (sc - 7))) + Z.of_nat 0) with (sc + 622593) by lia.
           rewrite mmw_frame_out by (clear - Hs7 Hsp1 Hsp2 HK; lia). rewrite sq_mem_out by (clear - Hs7; lia). apply ab_mem_hit; [exact Hsc | exact Eh].
        -- unfold zset. rewrite nth_zupd_other by exact Hne. apply OLD; [apply bounce_in_ctx; lia|].
           intros x Hin. unfold in_rng, cell_range, bnc_cell in Hin. cbn [mc_loc mc_w fst snd] in Hin. rewrite Lc in Hin. unfold CTX_bounces in Hin.
           cbn [Z.of_nat Pos.of_succ_nat] in Hin. apply OUT; [clear - Hin Hk; lia | clear - Hin Hk Hsp1 HK; lia | clear - Hin Hk; lia | clear - Hin Hk; lia |].
           intros _ E. apply Hne. clear - Hin E Hs7. lia.
      * rewrite (ab_nohit_st s sc Hsc Eh). apply OLD; [apply bounce_in_ctx; lia|].
        intros x Hin. unfold in_rng, cell_range, bnc_cell in Hin. cbn [mc_loc mc_w fst snd] in Hin. rewrite Lc in Hin. unfold CTX_bounces in Hin.
        cbn [Z.of_nat Pos.of_succ_nat] in Hin. apply OUT; [clear - Hin Hk; lia | clear - Hin Hk Hsp1 HK; lia | clear - Hin Hk; lia | clear - Hin Hk; lia |].
        intros E. exfalso. clear - E Eh. congruence.
  - exact m3_grows.
  - intros x Hx Hne. destruct (range_dec x (sp0 - 200) 56) as [A|A]; [left; clear - A HK; lia|].
    destruct (Z.eq_dec x 622632) as [B|B].
    { right. exists (seq_cell (st_seq s3)). split; [unfold C3; left; reflexivity|]. unfold in_rng, cell_range, seq_cell. cbn [mc_loc mc_w fst snd].
      rewrite Lc. unfold CTX_seq. cbn. clear - B. lia. }
    destruct (range_dec x 622568 32) as [D|D].
    { right. exists (unm_cell (Z.to_nat (x - 622568)) (nth (Z.to_nat (x - 622568)) (st_unmap_seq s3) 0)).
      split; [unfold C3; right; apply in_app_iff; left; apply (in_map (fun k => unm_cell k (nth k (st_unmap_seq s3) 0))); apply in_seq; clear - D; lia|].
      unfold in_rng, cell_range, unm_cell. cbn [mc_loc mc_w fst snd]. rewrite Lc. unfold CTX_unmap_seq. cbn. clear - D. lia. }
    destruct (ab_hit sc useq seq) eqn:Eh.
    + destruct (Z.eq_dec x (sc + 622593)) as [E|E].
      * assert (Hs7 : 7 <= sc < 39) by (unfold ab_hit, ab_tr in Eh; destruct (7 <=? sc) eqn:E1; destruct (sc <? 39) eqn:E2; cbn [andb] in Eh; try discriminate Eh;
                                          apply Z.leb_le in E1; apply Z.ltb_lt in E2; lia).
        right. exists (bnc_cell (Z.to_nat (sc - 7)) (nth (Z.to_nat (sc - 7)) (st_bounces s3) 0)).
        split; [unfold C3; right; apply in_app_iff; right; apply (in_map (fun k => bnc_cell k (nth k (st_bounces s3) 0))); apply in_seq; clear - Hs7; lia|].
        unfold in_rng, cell_range, bnc_cell. cbn [mc_loc mc_w fst snd]. rewrite Lc. unfold CTX_bounces. cbn. clear - E Hs7. lia.
      * exfalso. apply Hne. apply OUT; [exact Hx | clear - A; lia | exact B | intros _; exact D | intros _; exact E].
    + exfalso. apply Hne. apply OUT; [exact Hx | clear - A; lia | exact B | intros _; exact D | intros E; clear - E Eh; congruence].
Qed.
End CUT3.
