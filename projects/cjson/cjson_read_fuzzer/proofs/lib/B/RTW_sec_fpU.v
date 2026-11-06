(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes PropExec MState Mem Cells Step Frame Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import BImg RT_defs RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_geom.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RT_wf RT_rep RT_kit CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_kit.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit.RT_shlem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RT_art.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_cost.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_cost.RT_artG.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_fp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp.RT_artB.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RT_fp AShadow.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.ABand.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Lemma rw_cells_transport_munch : forall W m m' A cs,
  rw_cells bsegs m A cs -> munch W m m' -> disjoint_from W A (Z.of_nat (cells_size cs)) -> rw_cells bsegs m' A cs.
Proof.
  intros W m m' A cs [[Hwf HB] HW] MU HD. split; [split; [exact Hwf|]|].
  - eapply bytes_at_transport; [exact HB| exact MU| rewrite cells_bytes_length by exact Hwf; exact HD].
  - destruct HW as (H0 & H1 & HW). split; [exact H0|]. split; [exact H1|]. intros i Hi.
    unfold wview in *. rewrite (MU (wa (A + i))); [apply HW; exact Hi|].
    rewrite wa_unsigned by lia. eapply disjoint_outside; [exact HD| lia].
Qed.
Lemma stk_transport_munch : forall W m m' lo hi,
  stk bsegs m lo hi -> munch W m m' -> disjoint_from W lo (hi - lo) -> stk bsegs m' lo hi.
Proof.
  intros W m m' lo hi (H0 & H1 & H) MU HD. split; [exact H0|]. split; [exact H1|]. intros a Ha.
  assert (E : m' (wa a) = m (wa a)). { apply MU. rewrite wa_unsigned by lia. eapply disjoint_outside; [exact HD| lia]. }
  destruct (H a Ha) as [Hw [b Hb]]. unfold wview, mrd in *. rewrite E. split; [exact Hw| exists b; exact Hb].
Qed.
Lemma SH_add_le : forall a k, 0 <= a -> 0 <= k -> SH a + k / 8 <= SH (a + k).
Proof. intros a k Ha Hk. rewrite !SH_def. Z.div_mod_to_equations. lia. Qed.

Section FPU.
Variable st : rtstate.
Hypothesis WF : RTWF st.
Variables (W : list (Z * Z)) (m m' : word -> option byte).
Hypothesis MU : munch W m m'.
(* [comment removed for export] *)
(* [comment removed for export] *)
Hypothesis VD : forall lo hi, ((hi <= AIMG_HI \/ (KLOWSHADOW_BEG <= lo /\ hi <= KHIGHMEM_BEG)) \/ exists r, In r (rt_ranges st) /\ fst r <= lo /\ hi <= snd r) -> disjoint_from W lo (hi - lo).

(* [comment removed for export] *)
Local Ltac inprim := right; exists (st_pbase st, st_pbase st + PRIM_RES_SIZE); split; [unfold rt_ranges; left; reflexivity| cbn [fst snd]; unfold KREGIONSIZE, KFREEARRAY_OFF, KFREEARRAY_SIZE, QBATCH_SIZE in *; lia].
Local Ltac inloose obj H := right; exists (fst obj, fst obj + snd obj); split; [unfold rt_ranges; do 2 right; rewrite !in_app_iff; left; apply in_map_iff; exists obj; split; [reflexivity| exact H]| cbn [fst snd]; unfold T_STATS, T_UNWINDING, FS_FRAMES_OFF in *; lia].
Local Ltac insec e H := right; exists (fst e, fst e + smapsize (snd e)); split; [unfold rt_ranges; do 2 right; rewrite !in_app_iff; right; left; apply in_map_iff; exists e; split; [reflexivity| exact H]| cbn [fst snd]; lia].


Lemma rwU : forall a cs, rw_cells bsegs m a cs -> disjoint_from W a (Z.of_nat (cells_size cs)) -> rw_cells bsegs m' a cs.
Proof. intros a cs H D. eapply rw_cells_transport_munch; [exact H| exact MU| exact D]. Qed.
Lemma roU : forall a cs, cells_at bsegs m a cs -> disjoint_from W a (Z.of_nat (cells_size cs)) -> cells_at bsegs m' a cs.
Proof. intros a cs H D. eapply (ro_cells_transport bsegs W m m'); [exact H| exact MU| exact D]. Qed.
Lemma rwUn : forall a cs n, rw_cells bsegs m a cs -> Z.of_nat (cells_size cs) <= n -> disjoint_from W a n -> rw_cells bsegs m' a cs.
Proof. intros a cs n H Hn D. eapply rwU; [exact H|]. eapply disjoint_from_mono; eauto. Qed.
Lemma roUn : forall a cs n, cells_at bsegs m a cs -> Z.of_nat (cells_size cs) <= n -> disjoint_from W a n -> cells_at bsegs m' a cs.
Proof. intros a cs n H Hn D. eapply roU; [exact H|]. eapply disjoint_from_mono; eauto. Qed.
Lemma visU' : forall lo hi, vis m lo hi ->
  ((hi <= AIMG_HI \/ (KLOWSHADOW_BEG <= lo /\ hi <= KHIGHMEM_BEG)) \/ exists r, In r (rt_ranges st) /\ fst r <= lo /\ hi <= snd r) -> vis m' lo hi.
Proof. intros lo hi H HD. eapply stk_transport_munch; [exact H| exact MU| apply VD; exact HD]. Qed.
(* [comment removed for export] *)
Lemma visU : forall lo hi, vis m lo hi -> AIMG_HI <= lo ->
  ((hi <= AIMG_HI \/ (KLOWSHADOW_BEG <= lo /\ hi <= KHIGHMEM_BEG)) \/ exists r, In r (rt_ranges st) /\ fst r <= lo /\ hi <= snd r) -> vis m' lo hi.
Proof. intros lo hi H _ HD. exact (visU' lo hi H HD). Qed.

Local Ltac tru H K := first [ eapply (roU _ _ H); exact K | eapply (rwU _ _ H); exact K
                           | eapply (roUn _ _ _ H); [| exact K]; cbn; lia | eapply (rwUn _ _ _ H); [| exact K]; cbn; lia ].

(* [comment removed for export] *)
Lemma U_link : R_link m -> WOK_link W -> R_link m'.
Proof.
  intros [H HP] [K KP]. split; [intros a v Hin; tru (H a v Hin) (K a v Hin)|].
  intros a Ha. rewrite <- (HP a Ha). apply MU. eapply disjoint_outside; [exact KP|]. rewrite wa_unsigned by (unfold A_GLOBREC_LO, A_GLOBREC_HI in Ha; lia). lia.
Qed.

(* [comment removed for export] *)
Lemma U_consts : R_consts st m -> WOK_consts W -> R_consts st m'.
Proof.
  intros H K. unfold R_consts, WOK_consts in *.
  destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & [oom H15] & H16 & H17 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27 & [(j0 & j1 & H28) H29]).
  destruct K as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15 & K16 & K17 & K18 & K19 & K20 & K21 & K22 & K23 & K24 & K25 & K26 & K27 & K28).
  split; [tru H1 K1|]. split; [tru H2 K2|]. split; [tru H3 K3|]. split; [tru H4 K4|]. split; [tru H5 K5|]. split; [tru H6 K6|].
  split; [tru H7 K7|]. split; [tru H8 K8|]. split; [tru H9 K9|]. split; [tru H10 K10|]. split; [tru H11 K11|]. split; [tru H12 K12|].
  split; [tru H13 K13|]. split; [tru H14 K14|]. split; [exists oom; tru H15 K15|]. split; [tru H16 K16|]. split; [tru H17 K17|].
  split; [tru H18 K18|]. split; [tru H19 K19|]. split; [tru H20 K20|]. split; [tru H21 K21|]. split; [tru H22 K22|]. split; [tru H23 K23|]. split; [tru H24 K24|].
  split; [tru H25 K25|]. split; [tru H26 K26|]. split; [tru H27 K27|].
  (* [comment removed for export] *)
  split; [exists j0, j1; tru H28 K28|].
  intros Hd. pose proof (emb_block_range st WF Hd) as (E1 & E2 & E3). apply visU; [exact (H29 Hd)| unfold AIMG_HI, KHIGHMEM_BEG in *; blia|].
  right. exists (emb_d st, emb_d st + EMB_CAP). split; [| cbn [fst snd]; lia].
  unfold rt_ranges. do 2 right. rewrite !in_app_iff. left. apply in_map_iff. exists (emb_d st, EMB_CAP). split; [reflexivity| exact (wb_emb_loose st (wf_base_ok st WF) Hd)].
Qed.

(* [comment removed for export] *)
Lemma U_alloc : R_alloc st m -> WOK_alloc W -> R_alloc st m'.
Proof.
  intros H K. unfold R_alloc, WOK_alloc in *.
  destruct H as ((j1 & j2 & j3 & H1) & (k1 & k2 & k3 & H2) & [j H3] & (l1 & l2 & l3 & l4 & H4) & H5).
  destruct K as (K1 & K2 & K3 & K4 & K5).
  split; [exists j1, j2, j3; tru H1 K1|]. split; [exists k1, k2, k3; tru H2 K2|]. split; [exists j; tru H3 K3|].
  split; [exists l1, l2, l3, l4; tru H4 K4|]. tru H5 K5.
Qed.

(* [comment removed for export] *)
Lemma U_rinfo : R_rinfo st m -> WOK_rinfo st W -> R_rinfo st m'.
Proof.
  intros [V H] K. pose proof (ris_range st WF) as (X1 & X2 & X3 & X4). split; [apply visU'; [exact V| inprim]|].
  intros c Hc. destruct (H c Hc) as (jr & je & js & RC). exists jr, je, js. tru RC (K c Hc).
Qed.

(* [comment removed for export] *)


Lemma U_regions : R_regions st m -> WOK_regions st W -> R_regions st m'.
Proof.
  intros H K c Hc. destruct (H c Hc) as (V1 & V2 & V3 & V4 & FA & TL). destruct (K c Hc) as [KF KT].
  pose proof (region_facts st WF c Hc) as RF. cbn zeta in RF.
  destruct RF as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10).
  pose proof (rt_SH_bounds (rbeg st c) ltac:(unfold KHIGHMEM_BEG, AIMG_HI, KREGIONSIZE in *; lia)) as B1.
  assert (FB : fabeg st c = rbeg st c + KFREEARRAY_OFF) by reflexivity.
  unfold KHIGHMEM_BEG, AIMG_HI, KREGIONSIZE, KFREEARRAY_OFF, KFREEARRAY_SIZE in *.
  pose proof (rt_SH_bounds (fabeg st c) ltac:(lia)) as B2.
  pose proof (SH_add_le (rbeg st c) (r_mapped (rg st c)) ltac:(lia) ltac:(lia)). pose proof (rt_SH_bounds (rbeg st c + r_mapped (rg st c)) ltac:(lia)).
  pose proof (SH_add_le (fabeg st c) (r_mapped_fa (rg st c)) ltac:(lia) ltac:(lia)). pose proof (rt_SH_bounds (fabeg st c + r_mapped_fa (rg st c)) ltac:(lia)).
  split; [apply visU'; [exact V1| inprim]|]. split; [apply visU'; [exact V2| left; unfold KHIGHMEM_BEG, KLOWSHADOW_BEG, AIMG_HI in *; lia]|].
  split; [apply visU'; [exact V3| inprim]|]. split; [apply visU'; [exact V4| left; unfold KHIGHMEM_BEG, KLOWSHADOW_BEG, AIMG_HI in *; lia]|].
  split.
  - intros i Hi. tru (FA i Hi) (KF i Hi).
  - eapply rwU; [exact TL|]. rewrite zcells_zrep_size by (Z.div_mod_to_equations; lia). exact KT.
Qed.

(* [comment removed for export] *)
Lemma U_avail : R_avail st m -> WOK_avail st W -> R_avail st m'.
Proof.
  intros H K c k Hc Hk. eapply rwU; [exact (H c k Hc Hk)|].
  destruct (Z.eq_dec c 0) as [->|NZ].
  { exfalso. unfold avail_cptrs in Hk. pose proof (wb_class0 st (wf_base_ok st WF)) as [E1 E2]. rewrite E1, E2 in Hk. cbn in Hk.
    unfold apend_cptrs in Hk. apply in_map_iff in Hk as ([c' k'] & _ & Hf). apply filter_In in Hf as [Hin Hb]. cbn [fst] in Hb.
    apply Z.eqb_eq in Hb. subst c'. pose proof (wq_apend st (wf_quar_ok st WF) _ Hin). cbn [fst] in *. lia. }
  pose proof (csize_pos c ltac:(unfold KNUMCLASSES in Hc; lia)) as SP.
  unfold sh_avail. rewrite zcells_zrep_size by (Z.div_mod_to_equations; lia). exact (K c k Hc Hk).
Qed.

(* [comment removed for export] *)
Lemma U_cache : R_cache st m -> WOK_cache st W -> R_cache st m'.
Proof.
  intros H K c Hc. destruct (H c Hc) as [H1 H2]. destruct (K c Hc) as [K1 K2]. split.
  - tru H1 K1.
  - intros i Hi. tru (H2 i Hi) (K2 i Hi).
Qed.

(* [comment removed for export] *)
Lemma U_thread : R_thread st m -> WOK_thread st W -> R_thread st m'.
Proof.
  intros H K. destruct H as (V & (j1 & j2 & j3 & j4 & j5 & HT) & HQ & HU & HC1 & HC2 & I1 & I2 & I3 & I4 & I5 & I6 & HD).
  destruct K as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12).
  pose proof (t_range st WF) as [T1 T2].
  split; [apply visU'; [exact V| inloose (st_t st, 4096) (wb_t_loose st (wf_base_ok st WF))]|].
  split; [exists j1, j2, j3, j4, j5; tru HT K1|].
  split; [tru HQ K2|]. split; [tru HU K3|]. split; [tru HC1 K4|]. split; [tru HC2 K5|].
  split; [tru I1 K6|]. split; [tru I2 K7|]. split; [tru I3 K8|]. split; [tru I4 K9|]. split; [tru I5 K10|]. split; [tru I6 K11|].
  tru HD K12.
Qed.

(* [comment removed for export] *)
Lemma U_block : forall live A n, In (A, n) (all_blocks st) ->
  R_block st m live A n -> WOK_block W A n -> R_block st m' live A n.
Proof.
  intros live A n HB (HD & BG & SC & V & SHD) (K1 & K2 & K3 & K4).
  pose proof (block_geom st WF A n HB) as (Gn & GA & K & X & Y & CE & L16 & H16 & EA & Gp & Gs). unfold usz in Y. unfold KHIGHMEM_BEG, AIMG_HI in K.
  split; [|split; [|split; [|split]]].
  - destruct HD as (b1 & cid & HC & HB1). exists b1, cid. split; [| exact HB1]. tru HC K1.
  - intros HRZ. tru (BG HRZ) (K2 HRZ).
  - intros EP. destruct (SC EP) as (V1 & V2 & HC). destruct (Gs EP) as (S1 & T1 & T2 & M4).
    assert (E : b_map_beg A = b_lo A n) by (unfold b_lo; rewrite EP; reflexivity).
    pose proof (rt_SH_bounds (b_lo A n) ltac:(blia)).
    pose proof (SH_add_le (b_lo A n) (smapsize n) ltac:(blia) ltac:(unfold b_hi in *; lia)). pose proof (rt_SH_bounds (b_lo A n + smapsize n) ltac:(blia)).
    split; [apply visU'; [exact V1| rewrite E; insec (b_lo A n, n) S1]|].
    split; [apply visU'; [exact V2| rewrite E; left; unfold KHIGHMEM_BEG, KLOWSHADOW_BEG, AIMG_HI in *; lia]|].
    tru HC (K3 EP).
  - destruct (bprim n) eqn:EP.
    + destruct (Gp eq_refl) as (_ & _ & _ & Q1 & Q2 & _). apply visU'; [exact V| inprim].
    + destruct (Gs eq_refl) as (S1 & T1 & _). apply visU'; [exact V| insec (b_lo A n, n) S1].
  - unfold R_bshadow in *. pose proof (rt_SH_bounds (b_lo A n) ltac:(blia)) as SB. destruct (bprim n) eqn:EP.
    + destruct live.
      * eapply rwU; [exact SHD|]. rewrite zcells_size. rewrite sh_live_len by lia. exact K4.
      * eapply rwU; [exact SHD|]. rewrite zcells_size. rewrite sh_quar_len by lia. exact K4.
      * pose proof (SH_add_le (b_lo A n) (asz n) ltac:(blia) ltac:(unfold b_hi in *; lia)). pose proof (rt_SH_bounds (b_lo A n + asz n) ltac:(unfold b_hi in *; blia)).
        apply visU'; [exact SHD| left; unfold sh_tot, b_hi, KHIGHMEM_BEG, KLOWSHADOW_BEG, AIMG_HI in *; lia].
    + destruct live; [| exact I| exact I]. eapply rwU; [exact SHD|]. rewrite zcells_size.
      (* [comment removed for export] *)
      assert (L8 : b_lo A n mod 8 = 0) by (apply (mod0_trans _ 8 16); [lia|lia|reflexivity|exact L16]).
      destruct (sh_fits n ltac:(lia)) as [SL SF].
      assert (ES : SH (b_lo A n) + sh_left n = SH A).
      { transitivity (SH (b_lo A n + 8 * sh_left n)); [| f_equal; lia]. rewrite rt_SH_aligned_add by exact L8. clear - SL. Z.div_mod_to_equations. lia. }
      eapply disjoint_from_sub; [exact K4| lia| lia].
Qed.

Lemma U_live : R_live st m -> WOK_live st W -> R_live st m'.
Proof.
  intros H K A n Hin. assert (HB : In (A, n) (all_blocks st)) by (unfold all_blocks; apply in_or_app; left; exact Hin).
  apply U_block; [exact HB| exact (H A n Hin)| exact (K A n Hin)].
Qed.
Lemma U_quar : R_quar st m -> WOK_quar st W -> R_quar st m'.
Proof.
  intros [H HP] K. split.
  - intros A n Hin. assert (HB : In (A, n) (all_blocks st)) by (unfold all_blocks; rewrite !in_app_iff; right; left; exact Hin).
    apply U_block; [exact HB| exact (H A n Hin)| apply K; rewrite in_app_iff; left; exact Hin].
  - intros A n Hin. assert (HB : In (A, n) (all_blocks st)) by (unfold all_blocks; rewrite !in_app_iff; right; right; exact Hin).
    apply U_block; [exact HB| exact (HP A n Hin)| apply K; rewrite in_app_iff; right; exact Hin].
Qed.

(* [comment removed for export] *)
Lemma U_qlist : forall q, (forall b, In b q -> In b (qall st)) -> R_qlist m q -> WOK_batches st W -> R_qlist m' q.
Proof.
  induction q as [|b q IH]; intros Hsub H K; [exact I|]. cbn [R_qlist] in H |- *. destruct H as (HL & (V & SL & SHD) & HQ).
  assert (Hb : In b (qall st)) by (apply Hsub; left; reflexivity).
  destruct (K b Hb) as (K1 & K2 & K3).
  destruct (wq_batch st (wf_quar_ok st WF) b Hb) as (_ & k & CV & EQ).
  assert (Hc : 0 <= 24 < KNUMCLASSES) by (unfold KNUMCLASSES; lia).
  destruct (carved_chunk st WF 24 k Hc ltac:(lia) CV) as (C1 & C2 & C3). rewrite <- EQ in C1. change (csize 24) with 8192 in C2.
  pose proof (region_facts st WF 24 Hc) as RF. cbn zeta in RF. destruct RF as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10).
  unfold KHIGHMEM_BEG, AIMG_HI, KREGIONSIZE, KFREEARRAY_OFF, QBATCH_SIZE, QBATCH_CAP in *.
  split; [| split; [split; [| split]|]].
  - tru HL K1.
  - apply visU'; [exact V| inprim].
  - intros i Hi. tru (SL i Hi) (K2 i Hi).
  - eapply rwU; [exact SHD|]. unfold sh_avail. change (csize 24) with 8192. rewrite zcells_zrep_size by lia. exact K3.
  - apply IH; [| exact HQ| exact K]. intros b' Hb'. apply Hsub. right. exact Hb'.
Qed.
Lemma U_batches : R_batches st m -> WOK_batches st W -> R_batches st m'.
Proof.
  intros (H1 & H2 & H3 & H4) K.
  split; [| split; [| split]].
  - apply U_qlist; [| exact H1| exact K]. intros b Hb; unfold qall; rewrite !in_app_iff; tauto.
  - apply U_qlist; [| exact H2| exact K]. intros b Hb; unfold qall; rewrite !in_app_iff; tauto.
  - apply U_qlist; [| exact H3| exact K]. intros b Hb; unfold qall; rewrite !in_app_iff; tauto.
  - intros bd Hbd. destruct (H4 bd Hbd) as ([nx HL] & V & SL & SHD).   (* [comment removed for export] *)
    assert (Hb : In (fst bd) (qall st)) by (unfold qall; rewrite !in_app_iff; right; right; right; apply in_map; exact Hbd).
    destruct (K (fst bd) Hb) as (K1 & K2 & K3).
    destruct (wq_batch st (wf_quar_ok st WF) (fst bd) Hb) as (_ & k & CV & EQ).
    assert (Hc : 0 <= 24 < KNUMCLASSES) by (unfold KNUMCLASSES; lia).
    destruct (carved_chunk st WF 24 k Hc ltac:(lia) CV) as (C1 & C2 & C3). rewrite <- EQ in C1. change (csize 24) with 8192 in C2.
    pose proof (region_facts st WF 24 Hc) as RF. cbn zeta in RF. destruct RF as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10).
    unfold KHIGHMEM_BEG, AIMG_HI, KREGIONSIZE, KFREEARRAY_OFF, QBATCH_SIZE, QBATCH_CAP in *.
    split; [exists nx; tru HL K1|]. split; [apply visU'; [exact V| inprim]|]. split; [intros i Hi; tru (SL i Hi) (K2 i Hi)|].
    eapply rwU; [exact SHD|]. unfold sh_avail. change (csize 24) with 8192. rewrite zcells_zrep_size by lia. exact K3.
Qed.

(* [comment removed for export] *)
Lemma U_ptrarr : R_ptrarr st m -> WOK_ptrarr st W -> R_ptrarr st m'.
Proof.
  intros (V & H & HS) [K KS]. pose proof (pa_range st WF) as (P1 & P2 & P3 & P4 & P5). unfold KHIGHMEM_BEG, AIMG_HI, PTRARR_RES_SIZE in *.
  split; [apply visU'; [exact V| right; exists (st_pa st, st_pa st + PTRARR_RES_SIZE); split; [unfold rt_ranges; right; left; reflexivity| cbn [fst snd]; unfold PTRARR_RES_SIZE; lia]]|].
  split; [intros i Hi; tru (H i Hi) (K i Hi)|].
  intros e He. destruct (HS e He) as (V1 & V2 & HC). destruct (ws_spend st (wf_sec_ok st WF) e He) as [HE _].
  destruct (ws_entry st (wf_sec_ok st WF) e HE) as (E1 & E2 & E3 & _).
  pose proof (wb_ranges st (wf_base_ok st WF) (fst e, fst e + smapsize (snd e))) as R. cbn [fst snd] in R.
  specialize (R ltac:(unfold rt_ranges; do 2 right; rewrite !in_app_iff; right; left; apply in_map_iff; exists e; auto)).
  pose proof (rt_SH_bounds (fst e) ltac:(unfold KHIGHMEM_BEG, AIMG_HI in *; blia)).
  pose proof (SH_add_le (fst e) (smapsize (snd e)) ltac:(unfold KHIGHMEM_BEG, AIMG_HI in *; blia) ltac:(lia)). pose proof (rt_SH_bounds (fst e + smapsize (snd e)) ltac:(unfold KHIGHMEM_BEG, AIMG_HI in *; blia)).
  split; [apply visU'; [exact V1| insec e HE]|].
  split; [apply visU'; [exact V2| left; unfold KHIGHMEM_BEG, KLOWSHADOW_BEG, AIMG_HI in *; lia]|].
  tru HC (KS e He).
Qed.

(* [comment removed for export] *)
Lemma U_depot : R_depot st m -> WOK_depot st W -> R_depot st m'.
Proof.
  intros H K. destruct H as (TAB & [j NIDS] & MAP1 & NBV & NODES & SS & BLKS & SBV).
  destruct K as (K1 & K2 & K3 & K4 & K5 & K6). unfold R_depot.
  split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]].
  - intros i Hi. tru (TAB i Hi) (K1 i Hi).
  - exists j. tru NIDS K2.
  - intros k Hk. tru (MAP1 k Hk) (K3 k Hk).
  - intros b Hb. destruct (nb_range st WF b Hb) as (R1 & R2 & R3). apply visU'; [exact (NBV b Hb)| right; exists (b, b + NODEBLOCK_SIZE); split; [unfold rt_ranges; do 2 right; rewrite !in_app_iff; right; right; left; apply in_map_iff; exists b; auto| cbn [fst snd]; lia]].
  - intros id Hid. tru (NODES id Hid) (K4 id Hid).
  - tru SS K5.
  - intros b Hb. destruct (BLKS b Hb) as (j1 & HC). exists j1. tru HC (K6 b Hb).
  - intros b Hb. destruct (sb_range st WF b Hb) as (R1 & R2 & R3). apply visU'; [exact (SBV b Hb)| right; exists (b, b + STOREBLOCK_SIZE); split; [unfold rt_ranges; do 2 right; rewrite !in_app_iff; right; right; right; apply in_map_iff; exists b; auto| cbn [fst snd]; lia]].
Qed.

(* [comment removed for export] *)
Lemma U_fs : R_fs st m -> WOK_fs st W -> R_fs st m'.
Proof.
  intros H K. destruct H as (V1 & V2 & HINTS & LOG & GC & FLG & SAV). destruct K as (K1 & K2 & K3 & K4 & K5).
  pose proof (fs_range st WF) as (F1 & F2 & F3). unfold KHIGHMEM_BEG, AIMG_HI in F1.
  pose proof (rt_SH_bounds (st_fs st + FS_FRAMES_OFF) ltac:(unfold FS_FRAMES_OFF, FS_TOTAL in *; blia)) as B1.
  pose proof (rt_SH_bounds (st_fs st + FS_TOTAL) ltac:(unfold FS_FRAMES_OFF, FS_TOTAL in *; blia)) as B2.
  split; [apply visU'; [exact V1| inloose (st_fs st, FS_TOTAL) (wb_fs_loose st (wf_base_ok st WF))]|].
  split; [apply visU'; [exact V2| left; unfold KHIGHMEM_BEG, KLOWSHADOW_BEG, AIMG_HI; lia]|].
  split; [intros k Hk; tru (HINTS k Hk) (K1 k Hk)|].
  split; [tru LOG K2|]. split; [tru GC K3|]. split.
  - intros k pos Hk Hpos. tru (FLG k pos Hk Hpos) (K4 k pos Hk Hpos).
  - intros F k Hin. tru (SAV F k Hin) (K5 F k Hin).
Qed.

(* [comment removed for export] *)
Lemma U_ia : R_ia m -> WOK_ia W -> R_ia m'.
Proof. intros H K i Hi. tru (H i Hi) (K i Hi). Qed.
Lemma U_lowshadow : R_lowshadow m -> WOK_lowshadow W -> R_lowshadow m'.
Proof. intros H K g Hg. tru (H g Hg) (K g Hg). Qed.

Theorem RTREP_transportU : RTREP st m -> WOK_all st W -> RTREP st m'.
Proof.
  intros HR (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15 & K16). constructor.
  - apply U_link; [exact (rr_link st m HR)| exact K1].
  - apply U_consts; [exact (rr_consts st m HR)| exact K2].
  - apply U_alloc; [exact (rr_alloc st m HR)| exact K3].
  - apply U_rinfo; [exact (rr_rinfo st m HR)| exact K4].
  - apply U_regions; [exact (rr_regions st m HR)| exact K5].
  - apply U_avail; [exact (rr_avail st m HR)| exact K6].
  - apply U_cache; [exact (rr_cache st m HR)| exact K7].
  - apply U_thread; [exact (rr_thread st m HR)| exact K8].
  - apply U_live; [exact (rr_live st m HR)| exact K9].
  - apply U_quar; [exact (rr_quar st m HR)| exact K10].
  - apply U_batches; [exact (rr_batches st m HR)| exact K11].
  - apply U_ptrarr; [exact (rr_ptrarr st m HR)| exact K12].
  - apply U_depot; [exact (rr_depot st m HR)| exact K13].
  - apply U_fs; [exact (rr_fs st m HR)| exact K14].
  - apply U_ia; [exact (rr_ia st m HR)| exact K15].
  - apply U_lowshadow; [exact (rr_lowshadow st m HR)| exact K16].
Qed.
End FPU.


End CeilWrap.
