(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes PropExec MState Mem Cells Step Frame Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AImg RT_defs RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_wf RT_rep RT_kit CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_kit.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit.RT_shlem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_art.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_cost.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_cost.RT_artG.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_fp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp.RT_artB.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_fp RT_artF.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_m_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RTW_m_tpz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.ABand.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_bandtac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_bandtac2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_bandtac4.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section G.
Variable st : rtstate.
Hypothesis WF : RTWF st.

(* [comment removed for export] *)
Lemma grid_disj : forall c k1 k2, 0 <= c < KNUMCLASSES -> 1 <= c -> carved_cptr st c k1 -> carved_cptr st c k2 -> k1 <> k2 ->
  cptr_addr st c k1 + csize c <= cptr_addr st c k2 \/ cptr_addr st c k2 + csize c <= cptr_addr st c k1.
Proof.
  intros c k1 k2 Hc Hc1 (j1 & Hj1 & E1) (j2 & Hj2 & E2) NE.
  pose proof (chunk_cptr_eq c j1 ltac:(unfold KNUMCLASSES in Hc; lia)) as F1. pose proof (chunk_cptr_eq c j2 ltac:(unfold KNUMCLASSES in Hc; lia)) as F2.
  rewrite <- E1 in F1. rewrite <- E2 in F2. pose proof (csize_pos c ltac:(unfold KNUMCLASSES in Hc; lia)).
  unfold cptr_addr. assert (j1 <> j2) by (intros ->; apply NE; lia).
  destruct (Z_lt_le_dec j1 j2); [left| right]; nia.
Qed.

(* [comment removed for export] *)
Lemma region_disj : forall c1 c2 a1 a2 e1 e2, 0 <= c1 < KNUMCLASSES -> 0 <= c2 < KNUMCLASSES -> c1 <> c2 ->
  rbeg st c1 <= a1 -> e1 <= rbeg st c1 + KFREEARRAY_OFF -> rbeg st c2 <= a2 -> e2 <= rbeg st c2 + KFREEARRAY_OFF ->
  e1 <= a2 \/ e2 <= a1.
Proof.
  intros c1 c2 a1 a2 e1 e2 H1 H2 NE A1 E1 A2 E2. rewrite (rbeg_val st c1) in *. rewrite (rbeg_val st c2) in *.
  unfold KREGIONSIZE, KFREEARRAY_OFF in *. destruct (Z_lt_le_dec c1 c2); [left| right]; nia.
Qed.

Variables (c k : Z).
Hypothesis HIN : In (c, k) (st_apend st).
Local Abbreviation CH := (cptr_addr st c k).
Local Abbreviation CS := (csize c).

Lemma apend_class : 1 <= c <= 31 /\ 0 <= c < KNUMCLASSES.
Proof. pose proof (wq_apend st (wf_quar_ok st WF) _ HIN) as H. cbn [fst] in H. unfold KNUMCLASSES in *. lia. Qed.

Lemma apend_in_cptrs : In k (apend_cptrs st c).
Proof. unfold apend_cptrs. apply in_map_iff. exists (c, k). split; [reflexivity|]. apply filter_In. split; [exact HIN| cbn; apply Z.eqb_refl]. Qed.

Lemma apend_carved : carved_cptr st c k.
Proof.
  destruct apend_class as [Hc HcK]. apply (wc_used_carved st c (wf_class_ok st WF c HcK)).
  unfold used_cptrs. rewrite !in_app_iff. do 5 right. exact apend_in_cptrs.
Qed.

(* [comment removed for export] *)
Lemma apend_geom :
  rbeg st c <= CH /\ CH + CS <= rbeg st c + r_allocated (rg st c) /\ r_allocated (rg st c) <= r_mapped (rg st c)
  /\ r_mapped (rg st c) <= KFREEARRAY_OFF /\ KHIGHMEM_BEG <= rbeg st c /\ st_pbase st <= rbeg st c
  /\ rbeg st c + KREGIONSIZE <= st_pbase st + PRIM_RES_SIZE /\ st_pbase st + PRIM_RES_SIZE <= CEIL
  /\ CH mod 32 = 0 /\ 32 <= CS /\ CS mod 32 = 0.
Proof.
  destruct apend_class as [Hc HcK].
  (nelim (carved_chunk st WF c k HcK ltac:(lia) apend_carved) 3%nat; intros C1 C2 C3).
  pose proof (region_facts st WF c HcK) as RF. cbn zeta in RF. (nelim RF 10%nat; intros X1 X2 X3 X4 X5 X6 X7 X8 X9 X10).
  (nelim (region_range st WF c HcK) 6%nat; intros R1 R2 R3 R4 R5 R6).
  pose proof (csize_pos c ltac:(lia)) as SP. pose proof (csize_mod32 c ltac:(lia)) as SM.
  assert (AL : CH mod 32 = 0).
  { apply (mod0_of_sub CH (rbeg st c) 32 ltac:(lia)); [apply (mod0_trans _ 32 CS); [lia|lia|exact SM|exact C3]| apply (mod0_trans _ 32 4096); [lia|lia|reflexivity|exact R4]]. }
  unfold CEIL. repeat split; try lia.
Qed.

(* [comment removed for export] *)
Lemma apend_vs_block : forall A n, In (A, n) (all_blocks st) -> b_hi A n <= CH \/ CH + CS <= b_lo A n.
Proof.
  intros A n HB. destruct apend_class as [Hc HcK].
  (nelimp apend_geom 11%nat; intros G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11).
  (nelimp (block_geom st WF A n HB) 11%nat; intros _ _ _ _ _ _ _ _ _ Gp Gs).
  destruct (bprim n) eqn:EP.
  - (nelim (Gp eq_refl) 6%nat; intros Hcl RB RE _ _ BH). cbn zeta in *.
    destruct (Z.eq_dec (pclass n) c) as [EC|NC].
    + (nelim (prim_block_cptr st WF A n HB EP) 4%nat; intros IN1 IK1 CVb Lb). rewrite EC in IK1, CVb, Lb.
      pose proof (wc_used_nodup st c (wf_class_ok st WF c HcK)) as ND. rewrite used_cptrs_split in ND.
      assert (NK : b_cptr st A n <> k).
      { intros EK. apply NoDup_app_remove_l in ND. eapply (nodup_app_disj _ _ _ ND IK1). rewrite EK. apply in_or_app. right. exact apend_in_cptrs. }
      rewrite BH, Lb, EC. destruct (grid_disj c (b_cptr st A n) k HcK ltac:(lia) CVb apend_carved NK); [left| right]; lia.
    + assert (MM : r_mapped (rg st (pclass n)) <= KFREEARRAY_OFF) by (apply (wc_mapped_max st (pclass n) (wf_class_ok st WF (pclass n) ltac:(unfold KNUMCLASSES; lia)))).
      rewrite BH. destruct (region_disj (pclass n) c (b_lo A n) CH (b_lo A n + csize (pclass n)) (CH + CS)
                  ltac:(unfold KNUMCLASSES; lia) HcK NC ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); [left| right]; lia.
  - (nelim (Gs eq_refl) 3%nat; intros S1' T1 _).
    destruct (prim_vs_tail st WF (b_lo A n, b_lo A n + smapsize n)) as [D|D].
    { apply in_or_app; right; apply in_or_app; left; apply in_map_iff; exists (b_lo A n, n); split; [reflexivity| exact S1']. }
    + cbn [fst snd] in D. rewrite T1. unfold KREGIONSIZE, KFREEARRAY_OFF, PRIM_RES_SIZE in *. lia.
    + cbn [fst snd] in D. rewrite T1. unfold KREGIONSIZE, KFREEARRAY_OFF, PRIM_RES_SIZE in *. lia.
Qed.

(* [comment removed for export] *)
Lemma apend_vs_batch : forall b, In b (qall st) -> qb_addr b + QBATCH_SIZE <= CH \/ CH + CS <= qb_addr b.
Proof.
  intros b Hb. destruct apend_class as [Hc HcK].
  (nelimp apend_geom 11%nat; intros G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11).
  (nelim (wq_batch st (wf_quar_ok st WF) b Hb) 4%nat; intros _ kb CV EQ).
  assert (H24 : 0 <= 24 < KNUMCLASSES) by (unfold KNUMCLASSES; lia).
  (nelim (carved_chunk st WF 24 kb H24 ltac:(lia) CV) 3%nat; intros C1 C2 C3).
  assert (MM : r_mapped (rg st 24) <= KFREEARRAY_OFF) by (apply (wc_mapped_max st 24 (wf_class_ok st WF 24 H24))).
  pose proof (wc_alloc_mapped st 24 (wf_class_ok st WF 24 H24)) as AM.
  unfold QBATCH_SIZE. change 8192 with (csize 24). rewrite EQ.
  destruct (Z.eq_dec c 24) as [E24|NC].
  - assert (CV' : carved_cptr st c kb) by (rewrite E24; exact CV).
    assert (NK : kb <> k).
    { intros EK. pose proof (wc_used_nodup st c (wf_class_ok st WF c HcK)) as ND. rewrite used_cptrs_split in ND.
      apply NoDup_app_remove_l in ND. apply NoDup_app_remove_l in ND.
      eapply (nodup_app_disj _ _ k ND); [| exact apend_in_cptrs].
      unfold batch_cptrs. rewrite E24, Z.eqb_refl. apply in_map_iff. exists (qb_addr b). split; [rewrite EQ, <- EK; unfold cptr_addr; Z.div_mod_to_equations; nia|].
      unfold qbatch_addrs. apply in_map. exact Hb. }
    rewrite <- E24. destruct (grid_disj c kb k HcK ltac:(lia) CV' apend_carved NK); [left| right]; lia.
  - destruct (region_disj 24 c (cptr_addr st 24 kb) CH (cptr_addr st 24 kb + csize 24) (CH + CS) H24 HcK ltac:(lia)
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); [left| right]; lia.
Qed.

(* [comment removed for export] *)
Lemma apend_vs_avail : forall c' k', 0 <= c' < KNUMCLASSES -> In k' (avail_cptrs st c' ++ apend_cptrs st c') -> (c', k') <> (c, k) ->
  cptr_addr st c' k' + csize c' <= CH \/ CH + CS <= cptr_addr st c' k'.
Proof.
  intros c' k' Hc' Hin NE. destruct apend_class as [Hc HcK].
  (nelimp apend_geom 11%nat; intros G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11).
  destruct (Z.eq_dec c' 0) as [->|NZ].
  { exfalso. unfold avail_cptrs in Hin. pose proof (wb_class0 st (wf_base_ok st WF)) as [E1 E2]. rewrite E1, E2 in Hin. cbn in Hin.
    unfold apend_cptrs in Hin. apply in_map_iff in Hin as ([c'' k''] & _ & Hf). apply filter_In in Hf as [Hin Hb]. cbn [fst] in Hb.
    apply Z.eqb_eq in Hb. subst c''. pose proof (wq_apend st (wf_quar_ok st WF) _ Hin). cbn [fst] in *. lia. }
  pose proof (wf_class_ok st WF c' Hc') as WC'.
  assert (CV' : carved_cptr st c' k').
  { apply (wc_used_carved st c' WC'). unfold used_cptrs. rewrite !in_app_iff. apply in_app_iff in Hin. tauto. }
  (nelim (carved_chunk st WF c' k' Hc' ltac:(lia) CV') 3%nat; intros C1 C2 C3).
  pose proof (wc_mapped_max st c' WC') as MM. pose proof (wc_alloc_mapped st c' WC') as AM.
  destruct (Z.eq_dec c' c) as [->|NC].
  - assert (NK : k' <> k) by (intros ->; apply NE; reflexivity).
    destruct (grid_disj c k' k HcK ltac:(lia) CV' apend_carved NK); [left| right]; lia.
  - destruct (region_disj c' c (cptr_addr st c' k') CH (cptr_addr st c' k' + csize c') (CH + CS) Hc' HcK NC
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); [left| right]; lia.
Qed.
End G.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition apz_ok (st : rtstate) (c k : Z) (iv : Z * Z) : Prop :=
     (cptr_addr st c k <= fst iv /\ snd iv <= cptr_addr st c k + csize c)
  \/ (SH (cptr_addr st c k) <= fst iv /\ snd iv <= SH (cptr_addr st c k + csize c))
  \/ (st_t st + T_STATS <= fst iv /\ snd iv <= st_t st + T_UNWINDING)
  \/ CEIL <= fst iv.

Local Ltac ulia := unfold KHIGHMEM_BEG, AIMG_HI, CEIL, KREGIONSIZE, KFREEARRAY_OFF, PRIM_RES_SIZE, PTRARR_RES_SIZE, QBATCH_SIZE in *; first [lia | blia].

Section APZ.
Variable st : rtstate.
Hypothesis WF : RTWF st.
Hypothesis HX : tpx_ok st.
Variables (c k : Z).
Hypothesis HIN : In (c, k) (st_apend st).
Variable W : list (Z * Z).
Hypothesis HW : Forall (apz_ok st c k) W.
Local Abbreviation CH := (cptr_addr st c k).
Local Abbreviation CS := (csize c).
Local Abbreviation t := (st_t st).

Lemma apz_disj : forall a sz,
  (a + sz <= CH \/ CH + CS <= a) -> (a + sz <= SH CH \/ SH (CH + CS) <= a) ->
  (a + sz <= t + T_STATS \/ (t + T_UNWINDING <= a /\ a + sz <= CEIL)) ->
  disjoint_from W a sz.
Proof.
  intros a sz H1 H2 H3. pose proof (t_range st WF) as TR. induction W as [|[lo hi] W' IH]; [exact I|].
  pose proof (Forall_inv HW) as A1. unfold apz_ok in A1. cbn [fst snd] in A1. cbn.
  split; [unfold T_STATS, T_UNWINDING, CEIL, KHIGHMEM_BEG, AIMG_HI in *; lia| apply IH; exact (Forall_inv_tail HW)].
Qed.

Lemma geomA : rbeg st c <= CH /\ CH + CS <= rbeg st c + r_allocated (rg st c) /\ r_allocated (rg st c) <= r_mapped (rg st c)
  /\ r_mapped (rg st c) <= KFREEARRAY_OFF /\ KHIGHMEM_BEG <= rbeg st c /\ st_pbase st <= rbeg st c
  /\ rbeg st c + KREGIONSIZE <= st_pbase st + PRIM_RES_SIZE /\ st_pbase st + PRIM_RES_SIZE <= CEIL
  /\ CH mod 32 = 0 /\ 32 <= CS /\ CS mod 32 = 0.
Proof. exact (apend_geom st WF c k HIN). Qed.

(* [comment removed for export] *)
Lemma shA : SH KHIGHMEM_BEG <= SH CH /\ SH (CH + CS) <= SH CEIL /\ SH CH + CS / 8 = SH (CH + CS) /\ SH CEIL < KHIGHMEM_BEG.
Proof.
  (nelimp geomA 11%nat; intros G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11). unfold KREGIONSIZE, KFREEARRAY_OFF in *.
  split; [apply rt_SH_mono; lia|]. split; [apply rt_SH_mono; lia|].
  split; [rewrite rt_SH_aligned_add by (apply (mod0_trans _ 8 32); [lia|lia|reflexivity|exact G9]); reflexivity|].
  rewrite SH_CEIL. unfold KHIGHMEM_BEG, AIMG_HI. lia.
Qed.

(* [comment removed for export] *)
Lemma apz_low : forall a sz, AIMG_LO <= a -> a + sz <= KHIGHMEM_BEG -> (a + sz <= AIMG_HI \/ KLOWSHADOW_BEG <= a) ->
  (a + sz <= SH CH \/ SH (CH + CS) <= a) -> disjoint_from W a sz.
Proof.
  (* [comment removed for export] *)
  intros a sz H0 H1 HZ H2. (nelimp geomA 6%nat; intros G1 G2 G3 G4 G5 _). pose proof (t_range st WF) as [TR _].
  apply apz_disj; [lia| exact H2|]. unfold T_STATS, T_UNWINDING, CEIL in *. clear - H0 H1 HZ TR. blia.
Qed.
(* [comment removed for export] *)
Lemma apz_img : forall a sz, AIMG_LO <= a -> a + sz <= AIMG_HI -> disjoint_from W a sz.
Proof.
  intros a sz H0 H. pose proof shA as (S1 & _). change (SH KHIGHMEM_BEG) with 0x2008fff7000 in S1.
  apply apz_low; unfold AIMG_LO, AIMG_HI, KHIGHMEM_BEG in *; lia.
Qed.
Local Ltac img := apply apz_img; unfold AIMG_LO, AIMG_HI; cbn -[Z.add Z.mul Z.le Z.lt Z.sub]; lia.

(* [comment removed for export] *)
Lemma apz_obj : forall lo hi a sz, (hi <= CH \/ CH + CS <= lo) -> (hi <= t \/ t + 4096 <= lo) ->
  (hi <= KLOWSHADOW_BEG \/ KHIGHMEM_BEG <= lo) -> hi <= CEIL -> lo <= a -> a + sz <= hi -> disjoint_from W a sz.   (* [comment removed for export] *)
Proof.
  intros lo hi a sz D1 D2 K1 K2 Ha Hs. (nelimp shA 4%nat; intros S1 S2 S3 S4). change (SH KHIGHMEM_BEG) with 0x2008fff7000 in S1.
  apply apz_disj; [lia| unfold KLOWSHADOW_BEG, KHIGHMEM_BEG in *; lia| unfold T_STATS, T_UNWINDING; lia].
Qed.

(* [comment removed for export] *)
Lemma apz_sh : forall lo hi a sz, (hi <= CH \/ CH + CS <= lo) -> 0 <= lo -> lo mod 8 = 0 -> hi <= CEIL ->
  SH lo <= a -> a + sz <= SH hi -> disjoint_from W a sz.
Proof.
  intros lo hi a sz D L0 L8 HC Ha Hs. (nelimp shA 4%nat; intros S1 S2 S3 S4). (nelimp geomA 10%nat; intros G1 G2 G3 G4 G5 G6 G7 G8 G9 _).
  pose proof (rt_SH_mono hi CEIL HC). pose proof (t_range st WF) as [TR _].
  pose proof (rt_SH_mono 0 lo L0) as M0. change (SH 0) with 0x7fff8000 in M0.
  apply apz_disj; [lia| | unfold T_STATS, T_UNWINDING, CEIL in *; blia].
  destruct D as [D|D].
  - left. pose proof (rt_SH_mono hi CH D). lia.
  - right. assert (E : SH (CH + CS) <= SH lo) by (apply rt_SH_mono; exact D). lia.
Qed.

(* [comment removed for export] *)
Lemma t_vs_chunk : t + 4096 <= CH \/ CH + CS <= t.
Proof. (nelimp geomA 9%nat; intros G1 G2 G3 G4 G5 G6 G7 G8 _). pose proof (t_vs_prim st WF). unfold KREGIONSIZE, KFREEARRAY_OFF in *. lia. Qed.

Lemma loose_vs_chunk : forall b sz, In (b, sz) (st_loose0 st) -> b + sz <= CH \/ CH + CS <= b.
Proof.
  intros b sz Hb. (nelimp geomA 9%nat; intros G1 G2 G3 G4 G5 G6 G7 G8 _).
  destruct (prim_vs_tail st WF (b, b + sz) ltac:(apply in_or_app; left; apply in_map_iff; exists (b, sz); auto)) as [D|D]; cbn [fst snd] in D;
    unfold KREGIONSIZE, KFREEARRAY_OFF in *; lia.
Qed.
Lemma tail_vs_chunk : forall r, In r (map (fun e => (fst e, fst e + smapsize (snd e))) (st_sec st)
                                  ++ map (fun b => (b, b + NODEBLOCK_SIZE)) (d_nblocks (st_depot st))
                                  ++ map (fun b => (b, b + STOREBLOCK_SIZE)) (d_sblocks (st_depot st))) ->
  snd r <= CH \/ CH + CS <= fst r.
Proof.
  intros r Hr. (nelimp geomA 9%nat; intros G1 G2 G3 G4 G5 G6 G7 G8 _).
  destruct (prim_vs_tail st WF r ltac:(apply in_or_app; right; exact Hr)) as [D|D]; unfold KREGIONSIZE, KFREEARRAY_OFF in *; lia.
Qed.

(* [comment removed for export] *)
Lemma AZ_link : WOK_link W.
Proof. split; [intros a v Hin; destruct (alink_range a v Hin); img| unfold A_GLOBREC_LO, A_GLOBREC_HI; img]. Qed.
Lemma AZ_consts : WOK_consts W.
Proof.
  unfold WOK_consts.
  unfold A_SHADOW_OFF_CELL, A_UAR_OPTION, A_AFLAGS, A_CFLAGS, A_PAGESIZE_CACHED, A_KHIGHMEMEND, A_KMIDMEMBEG, A_KMIDMEMEND,
    A_ASAN_INITED, A_MCS, A_CAN_POISON, A_TSD_KEY_INITED, A_TSD_KEY, A_MAY_RETURN_NULL, A_ALLOC_OOM, A_DYING, A_VERBOSITY,
    A_MFHOOKS, A_LSAN_DISABLE, A_IA_INITED, AHOOKS, A_LIBC_PAGESIZE, A_MU_GLOBALS, A_GLOBALS_REGD, A_TPCG_INITED, A_TOOLNAME, A_PRINTF_CB, A_EMB, ATP.
  repeat lazymatch goal with |- _ /\ _ => split | _ => idtac end; img.
Qed.
Lemma AZ_alloc : WOK_alloc W.
Proof.
  unfold WOK_alloc, A_ALLOC, A_SECONDARY, A_GSTATS, A_QUAR, A_MAXUSERSZ, A_ALLOC.
  repeat lazymatch goal with |- _ /\ _ => split | _ => idtac end; img.
Qed.
Lemma AZ_ia : WOK_ia W.
Proof. intros i Hi. unfold A_IA_MAP1. img. Qed.
Lemma AZ_lowshadow : WOK_lowshadow W.
Proof.
  intros g Hg. change (SH AIMG_LO) with 0x7fffa000 in Hg. change (SH AIMG_HI) with 0x800b7e00 in Hg.
  pose proof shA as (S1 & _). change (SH KHIGHMEM_BEG) with 0x2008fff7000 in S1.
  apply apz_low; unfold KHIGHMEM_BEG, AIMG_LO, AIMG_HI, KLOWSHADOW_BEG; lia.
Qed.

(* [comment removed for export] *)
Lemma AZ_rinfo : WOK_rinfo st W.
Proof.
  intros c' Hc'. (nelimp (ris_range st WF) 4%nat; intros X1 X2 X3 X4). unfold KNUMCLASSES in Hc'.
  (nelimp geomA 9%nat; intros G1 G2 G3 G4 G5 G6 G7 G8 _). (nelimp (S_range st WF) 3%nat; intros SR1 SR2 SR3).
  pose proof (t_vs_prim st WF) as TP.
  rewrite (rbeg_val st c) in *. destruct (apend_class st WF c k HIN) as [Hc _].
  eapply (apz_obj (ris st) (ris st + 4096)); unfold rinfo, ris, KSPACESIZE, KREGIONSIZE, KFREEARRAY_OFF, PRIM_RES_SIZE, CEIL in *; first [lia| nia].
Qed.

(* [comment removed for export] *)
Lemma AZ_regions : WOK_regions st W.
Proof.
  intros c' Hc'. pose proof (region_facts st WF c' Hc') as RF. cbn zeta in RF.
  (nelim RF 10%nat; intros X1 X2 X3 X4 X5 X6 X7 X8 X9 X10).
  assert (FB : fabeg st c' = rbeg st c' + KFREEARRAY_OFF) by reflexivity.
  (nelimp geomA 10%nat; intros G1 G2 G3 G4 G5 G6 G7 G8 G9 _). destruct (apend_class st WF c k HIN) as [Hc HcK].
  pose proof (t_vs_prim st WF) as TP.
  assert (DFA : fabeg st c' + r_mapped_fa (rg st c') <= CH \/ CH + CS <= fabeg st c').
  { destruct (Z.eq_dec c' c) as [->|NC]; [right; rewrite FB; lia|].
    rewrite FB. rewrite (rbeg_val st c') in *. rewrite (rbeg_val st c) in *. unfold KREGIONSIZE, KFREEARRAY_OFF, KFREEARRAY_SIZE, KNUMCLASSES in *.
    destruct (Z_lt_le_dec c' c); [left| right]; nia. }
  unfold KHIGHMEM_BEG, AIMG_HI, KREGIONSIZE, KFREEARRAY_OFF, KFREEARRAY_SIZE, PRIM_RES_SIZE in *.
  split.
  - intros i Hi. pose proof (wc_num_freed st c' (wf_class_ok st WF c' Hc')) as NF.
    eapply (apz_obj (fabeg st c') (fabeg st c' + r_mapped_fa (rg st c'))); [exact DFA| ulia| ulia| ulia| ulia| ulia].
  - (* [comment removed for export] *)
    assert (DT : rbeg st c' + r_mapped (rg st c') <= CH \/ CH + CS <= rbeg st c' + r_allocated (rg st c')).
    { destruct (Z.eq_dec c' c) as [->|NC]; [right; lia|].
      destruct (region_disj st c' c (rbeg st c') CH (rbeg st c' + r_mapped (rg st c')) (CH + CS) Hc' HcK NC); unfold KFREEARRAY_OFF; try lia. }
    eapply (apz_sh (rbeg st c' + r_allocated (rg st c')) (rbeg st c' + r_mapped (rg st c')));
      [lia| lia| apply mod0_add; [lia| exact X8| exact X9]| unfold CEIL; lia| lia|].
    rewrite !rt_SH_aligned_add by exact X8. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma AZ_avail_other : forall c' k', 0 <= c' < KNUMCLASSES -> In k' (avail_cptrs st c' ++ apend_cptrs st c') -> (c', k') <> (c, k) ->
  disjoint_from W (SH (cptr_addr st c' k')) (csize c' / 8).
Proof.
  intros c' k' Hc' Hin NE.
  pose proof (apend_vs_avail st WF c k HIN c' k' Hc' Hin NE) as D.
  pose proof (region_facts st WF c' Hc') as RF. cbn zeta in RF. (nelim RF 10%nat; intros X1 X2 X3 X4 X5 X6 X7 X8 X9 X10).
  destruct (Z.eq_dec c' 0) as [->|NZ].
  { exfalso. unfold avail_cptrs in Hin. pose proof (wb_class0 st (wf_base_ok st WF)) as [E1 E2]. rewrite E1, E2 in Hin. cbn in Hin.
    unfold apend_cptrs in Hin. apply in_map_iff in Hin as ([c'' k''] & _ & Hf). apply filter_In in Hf as [Hin Hb]. cbn [fst] in Hb.
    apply Z.eqb_eq in Hb. subst c''. pose proof (wq_apend st (wf_quar_ok st WF) _ Hin). cbn [fst] in *. lia. }
  assert (CV : carved_cptr st c' k').
  { apply (wc_used_carved st c' (wf_class_ok st WF c' Hc')). unfold used_cptrs. rewrite !in_app_iff. apply in_app_iff in Hin. tauto. }
  (nelim (carved_chunk st WF c' k' Hc' ltac:(lia) CV) 3%nat; intros C1 C2 C3).
  pose proof (csize_pos c' ltac:(unfold KNUMCLASSES in Hc'; lia)) as SP. pose proof (csize_mod32 c' ltac:(unfold KNUMCLASSES in Hc'; lia)) as SM.
  assert (AL : cptr_addr st c' k' mod 8 = 0).
  { apply (mod0_of_sub _ (rbeg st c') 8 ltac:(lia)); [| exact X8]. apply (mod0_trans _ 8 (csize c')); [lia|lia| apply (mod0_trans _ 8 32); [lia|lia|reflexivity|exact SM]| exact C3]. }
  unfold KHIGHMEM_BEG, AIMG_HI, KREGIONSIZE, KFREEARRAY_OFF in *.
  eapply (apz_sh (cptr_addr st c' k') (cptr_addr st c' k' + csize c')); [ulia| ulia| exact AL| ulia| ulia| ].
  rewrite rt_SH_aligned_add by exact AL. lia.
Qed.

(* [comment removed for export] *)
Lemma AZ_cache : WOK_cache st W.
Proof.
  intros c' Hc'. pose proof (wc_cache_max st c' (wf_class_ok st WF c' Hc')) as CM. pose proof (cmaxcount_le16 c'). unfold KNUMCLASSES in Hc'.
  pose proof (t_range st WF) as [T1 T2]. pose proof t_vs_chunk as TC. (nelimp shA 4%nat; intros S1 S2 S3 S4).
  assert (D : forall a sz, t + T_ACACHE <= a -> a + sz <= t + T_ACACHE + 2560 -> disjoint_from W a sz).
  { intros a sz H1 H2. change (SH KHIGHMEM_BEG) with 0x2008fff7000 in S1. apply apz_disj; unfold T_ACACHE, T_STATS, CEIL in *; blia. }
  split; [apply D; unfold pcaddr, acache; lia|]. intros i Hi. apply D; unfold pcaddr, acache; lia.
Qed.

(* [comment removed for export] *)
Lemma AZ_thread : WOK_thread st W.
Proof.
  pose proof (t_range st WF) as [T1 T2]. pose proof t_vs_chunk as TC. (nelimp shA 4%nat; intros S1 S2 S3 S4). unfold WOK_thread.
  change (SH KHIGHMEM_BEG) with 0x2008fff7000 in S1.
  split; [apply apz_disj; unfold T_STATS, CEIL in *; blia|].
  split; [apply apz_disj; unfold qcache_t, T_QCACHE, T_STATS, CEIL in *; blia|].
  split; [apply apz_disj; unfold T_UNWINDING, T_STATS, CEIL in *; blia|].
  destruct HX as [CX DX].
  (nelim (wb_ctx_loose st (wf_base_ok st WF)) 5%nat; intros cb ck CL1 CL2 CL3). (nelim (loose0_range st WF _ _ CL1) 4%nat; intros R1 R2 R3 R4). olin R1.
  pose proof (loose_vs_chunk cb ck CL1) as LC.
  split; [eapply (apz_obj (st_ctx st) (st_ctx st + 160)); unfold CTX_TID, CEIL in *; blia|].
  split; [eapply (apz_obj (st_ctx st) (st_ctx st + 160)); unfold CTX_THREAD, CEIL in *; blia|].
  unfold A_TSD_PTR, A_TSD_MAIN, A_DTV_PTR, A_DTV, A_TLSMOD, A_FSTLS_CELL, A_DTLS_OFF, ATP in *.
  split; [img|]. split; [img|]. split; [img|]. split; [img|]. split; [img|]. split; [img|].
  (nelim (wb_dtls_loose st (wf_base_ok st WF)) 5%nat; intros db dk DL1 DL2 DL3). (nelim (loose0_range st WF _ _ DL1) 4%nat; intros Q1 Q2 Q3 Q4). (nelimp (oclr_lin _ _ Q1 ltac:(lia)) 3%nat; intros _ QLB _). unfold KLOWSHADOW_BEG, KHIGHMEM_BEG in QLB.
  pose proof (loose_vs_chunk db dk DL1) as LD.
  eapply (apz_obj (tl_dtls_block (st_tls st) + 24) (tl_dtls_block (st_tls st) + 32));
    [ clear - LD DL2 DL3; lia | exact DX | clear - QLB DL2 DL3 Q2; unfold KLOWSHADOW_BEG, KHIGHMEM_BEG; lia
    | unfold CEIL; clear - Q3 DL3; lia | lia | lia ].
Qed.

(* [comment removed for export] *)
Lemma AZ_block : forall A n, In (A, n) (all_blocks st) -> WOK_block W A n.
Proof.
  intros A n HB.
  (nelimp (block_geom st WF A n HB) 11%nat; intros Gn GA K X Y CE L16 H16 EA Gp Gs). unfold usz in Y.
  assert (L8 : b_lo A n mod 8 = 0) by (apply (mod0_trans _ 8 16); [lia|lia|reflexivity|exact L16]).
  pose proof (t_vs_block st WF A n HB) as TB. pose proof (apend_vs_block st WF c k HIN A n HB) as CB.
  pose proof K as K'. unfold KHIGHMEM_BEG, AIMG_HI in K'. olin_all. pose proof (rz_size_range n) as (Z1 & Z2).
  assert (OBJ : forall a sz, b_lo A n <= a -> a + sz <= b_hi A n -> disjoint_from W a sz).
  { intros a sz Ha Hs. eapply (apz_obj (b_lo A n) (b_hi A n)); [ulia| ulia| exact (ablk_disj_band _ _ K)| ulia| exact Ha| exact Hs]. }
  assert (RZA : b_lo A n + rz_size n <= A).
  { rewrite EA at 2. unfold sh_left, SEC_HDR, SEC_RZ. destruct (bprim n) eqn:EP.
    + Z.div_mod_to_equations. lia.
    + (nelim (sec_facts n EP) 3%nat; intros _ F2 _). rewrite F2. cbn. lia. }
  split; [|split; [|split]].
  - apply OBJ; unfold b_chunk_beg; lia.
  - intros HRZ. apply OBJ; unfold b_alloc_beg; lia.
  - intros EP. apply OBJ; unfold b_lo in *; rewrite EP in *; unfold b_map_beg, SEC_HDR, SEC_RZ in *; lia.
  - assert (EH : b_hi A n = b_lo A n + asz n) by reflexivity.
    assert (ST8 : sh_tot n = asz n / 8) by reflexivity.
    eapply (apz_sh (b_lo A n) (b_hi A n)); [exact CB| ulia| exact L8| ulia| ulia| ].
    rewrite EH, rt_SH_aligned_add by exact L8. rewrite ST8. lia.
Qed.
Lemma AZ_live : WOK_live st W.
Proof. intros A n Hin. apply AZ_block. unfold all_blocks; apply in_or_app; left; exact Hin. Qed.
Lemma AZ_quar : WOK_quar st W.
Proof. intros A n Hin. apply AZ_block. unfold all_blocks; apply in_or_app; right; exact Hin. Qed.

(* [comment removed for export] *)
Lemma AZ_batches : WOK_batches st W.
Proof.
  intros b Hb.
  (nelim (batch_geom st WF b Hb) 5%nat; intros BB BF R1 R2 AL).
  destruct (wq_batch st (wf_quar_ok st WF) b Hb) as [CNT (kb & CV & EQ)].
  pose proof (region_facts st WF 24 ltac:(unfold KNUMCLASSES; lia)) as RF. cbn zeta in RF. (nelim RF 10%nat; intros X1 X2 X3 X4 X5 X6 X7 X8 X9 X10).
  pose proof (apend_vs_batch st WF c k HIN b Hb) as CB.
  assert (TB : qb_addr b + QBATCH_SIZE <= t \/ t + 4096 <= qb_addr b).
  { pose proof (t_vs_prim st WF). unfold KREGIONSIZE, KFREEARRAY_OFF, QBATCH_SIZE in *. lia. }
  unfold KHIGHMEM_BEG, AIMG_HI, KREGIONSIZE, KFREEARRAY_OFF, QBATCH_SIZE, QBATCH_CAP, PRIM_RES_SIZE in *.
  assert (OBJ : forall a sz, qb_addr b <= a -> a + sz <= qb_addr b + 8192 -> disjoint_from W a sz).
  { intros a sz Ha Hs. eapply (apz_obj (qb_addr b) (qb_addr b + 8192)); [ulia| ulia| ulia| ulia| ulia| ulia]. }
  split; [| split].
  - apply OBJ; lia.
  - intros i Hi. apply OBJ; lia.
  - assert (AL8 : qb_addr b mod 8 = 0) by (apply (mod0_trans _ 8 32); [lia|lia|reflexivity|exact AL]).
    eapply (apz_sh (qb_addr b) (qb_addr b + 8192)); [ulia| ulia| exact AL8| ulia| ulia| ].
    rewrite rt_SH_aligned_add by exact AL8. change (8192 / 8) with 1024. lia.
Qed.

(* [comment removed for export] *)
Lemma AZ_ptrarr : WOK_ptrarr st W.
Proof.
  (nelimp geomA 9%nat; intros G1 G2 G3 G4 G5 G6 G7 G8 _).
  split.
  - intros i Hi. (nelimp (pa_range st WF) 5%nat; intros P1 P2 P3 P4 P5). pose proof (t_vs_pa st WF).
    pose proof (wb_pwdj st (wf_base_ok st WF)) as PW. rewrite rt_ranges_tail in PW. cbn [app] in PW. destruct PW as [PF _].
    rewrite Forall_forall in PF. specialize (PF _ ltac:(left; reflexivity)). cbn [fst snd] in PF.
    unfold KHIGHMEM_BEG, AIMG_HI, PTRARR_RES_SIZE, KREGIONSIZE, KFREEARRAY_OFF, PRIM_RES_SIZE in *.
    eapply (apz_obj (st_pa st) (st_pa st + 0x800000)); [ulia| ulia| ulia| ulia| ulia| ulia].
  - intros e He. destruct (ws_spend st (wf_sec_ok st WF) e He) as [HE _].
    (nelim (ws_entry st (wf_sec_ok st WF) e HE) 4%nat; intros E1 E2 E3 _).
    pose proof (wb_ranges st (wf_base_ok st WF) (fst e, fst e + smapsize (snd e))) as R. cbn [fst snd] in R.
    specialize (R ltac:(unfold rt_ranges; do 2 right; rewrite !in_app_iff; right; left; apply in_map_iff; exists e; auto)).
    destruct e as [mb n]. cbn [fst snd] in *. (nelim (sec_facts n E1) 5%nat; intros _ _ _ F4 _). pose proof (usz_le_rounded8 n) as (U1 & _).
    pose proof (t_vs_sec st WF mb n HE).
    pose proof (tail_vs_chunk (mb, mb + smapsize n) ltac:(apply in_or_app; left; apply in_map_iff; exists (mb, n); auto)) as D. cbn [fst snd] in D.
    eapply (apz_obj mb (mb + smapsize n)); [ulia| ulia| ulia| ulia| ulia| unfold usz in *; lia].
Qed.

(* [comment removed for export] *)
Lemma AZ_depot : WOK_depot st W.
Proof.
  pose proof (wf_depot_ok st WF) as WD. unfold WOK_depot.
  unfold A_DEPOT, A_DEPOT_NIDS, A_DEPOT_MAP1, A_STACKSTORE, DEPOT_TAB_LOG, SSTORE_NBLOCKS in *.
  split; [| split; [| split; [| split; [| split]]]].
  - intros i Hi. img.
  - img.
  - intros k' Hk. img.
  - intros id Hid.
    set (q := id / DEPOT_L2_NODES). set (b := nthz (d_nblocks (st_depot st)) q 0).
    assert (Hq : 0 <= q < d_nnb (st_depot st)).
    { pose proof (wd_nnb st WD) as E. unfold d_nnb in *. rewrite E. subst q. unfold DEPOT_L2_NODES. Z.div_mod_to_equations. nia. }
    assert (Hb : In b (d_nblocks (st_depot st))) by (subst b; apply nthz_In; unfold d_nnb in Hq; exact Hq).
    (nelim (nb_range st WF b Hb) 3%nat; intros R1 R2 R3). pose proof (t_vs_nb st WF b Hb) as TB.
    pose proof (tail_vs_chunk (b, b + NODEBLOCK_SIZE) ltac:(apply in_or_app; right; apply in_or_app; left; apply in_map_iff; exists b; auto)) as D. cbn [fst snd] in D.
    assert (ADDR : dnode_addr (st_depot st) id = b + DEPOT_NODE_SZ * (id mod DEPOT_L2_NODES)) by reflexivity.
    rewrite ADDR. unfold DEPOT_NODE_SZ, DEPOT_L2_NODES, NODEBLOCK_SIZE in *.
    eapply (apz_obj b (b + 1048576)); [ulia| ulia| ulia| ulia| Z.div_mod_to_equations; lia| Z.div_mod_to_equations; lia].
  - img.
  - intros b Hb. img.
Qed.

(* [comment removed for export] *)
Lemma AZ_fs : WOK_fs st W.
Proof.
  (nelimp (fs_range st WF) 3%nat; intros F1 F2 F3). unfold KHIGHMEM_BEG, AIMG_HI in F1. olin_all. pose proof (t_vs_fs st WF) as TF.
  pose proof (loose_vs_chunk _ _ (wb_fs_loose st (wf_base_ok st WF))) as CF.
  assert (OBJ : forall a sz, st_fs st <= a -> a + sz <= st_fs st + FS_TOTAL -> disjoint_from W a sz).
  { intros a sz Ha Hs. eapply (apz_obj (st_fs st) (st_fs st + FS_TOTAL)); [ulia| ulia| ulia| exact F2| ulia| ulia]. }
  unfold WOK_fs. split; [| split; [| split; [| split]]].
  - intros k' Hk. apply OBJ; unfold FS_TOTAL in *; lia.
  - apply OBJ; unfold FS_TOTAL in *; lia.
  - apply OBJ; unfold FS_TOTAL in *; lia.
  - intros k' pos Hk Hp. pose proof (flags_ok k' Hk) as [O1 O2]. apply OBJ; unfold fflag_addr, FS_TOTAL in *; lia.
  - intros F k' Hin. (nelimp (frame_range st WF F k' Hin) 4%nat; intros Hk X Y _). unfold FS_FRAMES_OFF, FS_TOTAL in *.
    assert (64 <= fsz k') by (destruct Hk as [-> | ->]; [change (fsz 1) with 128| change (fsz 2) with 256]; lia).
    apply OBJ; unfold FS_TOTAL; lia.
Qed.

(* [comment removed for export] *)
Theorem apz_others : forall m m', munch W m m' -> wmono asegs m m' -> RTREP st m ->
  R_link m' /\ R_consts st m' /\ R_alloc st m' /\ R_rinfo st m' /\ R_regions st m' /\ R_cache st m' /\ R_thread st m'
  /\ R_live st m' /\ R_quar st m' /\ R_batches st m' /\ R_ptrarr st m' /\ R_depot st m' /\ R_fs st m' /\ R_ia m' /\ R_lowshadow m'
  /\ (forall c' k', 0 <= c' < KNUMCLASSES -> In k' (avail_cptrs st c' ++ apend_cptrs st c') -> (c', k') <> (c, k) ->
        rw_cells asegs m' (SH (cptr_addr st c' k')) (zcells (sh_avail c'))).
Proof.
  intros m m' MU WM HR.
  Local Ltac tapp T st WF W m m' MU WM :=
    first [ eapply (T st WF W m m' MU WM) | eapply (T st W m m' MU WM) | eapply (T W m m' MU WM) | eapply (T W m m' MU) ].
  split; [tapp T_link st WF W m m' MU WM; [exact (rr_link st m HR)| exact AZ_link]|].
  split; [tapp T_consts st WF W m m' MU WM; [exact (rr_consts st m HR)| exact AZ_consts]|].
  split; [tapp T_alloc st WF W m m' MU WM; [exact (rr_alloc st m HR)| exact AZ_alloc]|].
  split; [tapp T_rinfo st WF W m m' MU WM; [exact (rr_rinfo st m HR)| exact AZ_rinfo]|].
  split; [tapp T_regions st WF W m m' MU WM; [exact (rr_regions st m HR)| exact AZ_regions]|].
  split; [tapp T_cache st WF W m m' MU WM; [exact (rr_cache st m HR)| exact AZ_cache]|].
  split; [tapp T_thread st WF W m m' MU WM; [exact (rr_thread st m HR)| exact AZ_thread]|].
  split; [tapp T_live st WF W m m' MU WM; [exact (rr_live st m HR)| exact AZ_live]|].
  split; [tapp T_quar st WF W m m' MU WM; [exact (rr_quar st m HR)| exact AZ_quar]|].
  split; [tapp T_batches st WF W m m' MU WM; [exact (rr_batches st m HR)| exact AZ_batches]|].
  split; [tapp T_ptrarr st WF W m m' MU WM; [exact (rr_ptrarr st m HR)| exact AZ_ptrarr]|].
  split; [tapp T_depot st WF W m m' MU WM; [exact (rr_depot st m HR)| exact AZ_depot]|].
  split; [tapp T_fs st WF W m m' MU WM; [exact (rr_fs st m HR)| exact AZ_fs]|].
  split; [tapp T_ia st WF W m m' MU WM; [exact (rr_ia st m HR)| exact AZ_ia]|].
  split; [tapp T_lowshadow st WF W m m' MU WM; [exact (rr_lowshadow st m HR)| exact AZ_lowshadow]|].
  intros c' k' Hc' Hin NE. eapply (rwT W m m' MU WM); [exact (rr_avail st m HR c' k' Hc' Hin)|].
  destruct (Z.eq_dec c' 0) as [->|NZ].
  { exfalso. unfold avail_cptrs in Hin. pose proof (wb_class0 st (wf_base_ok st WF)) as [E1 E2]. rewrite E1, E2 in Hin. cbn in Hin.
    unfold apend_cptrs in Hin. apply in_map_iff in Hin as ([c'' k''] & _ & Hf). apply filter_In in Hf as [Hin Hb]. cbn [fst] in Hb.
    apply Z.eqb_eq in Hb. subst c''. pose proof (wq_apend st (wf_quar_ok st WF) _ Hin). cbn [fst] in *. lia. }
  pose proof (csize_pos c' ltac:(unfold KNUMCLASSES in Hc'; lia)) as SP.
  unfold sh_avail. rewrite zcells_zrep_size by (Z.div_mod_to_equations; lia). apply AZ_avail_other; assumption.
Qed.

(* [comment removed for export] *)
Theorem apz_all : forall m m', munch W m m' -> wmono asegs m m' -> RTREP st m ->
  Forall (fun iv : Z * Z => (cptr_addr st c k <= fst iv /\ snd iv <= cptr_addr st c k + csize c) \/ CEIL <= fst iv) W ->
  RTREP st m'.
Proof.
  intros m m' MU WM HR HS.
  (nelim (apz_others m m' MU WM HR) 16%nat; intros X1 X2 X3 X4 X5 X7 X8 X9 X10 X11 X12 X13 X14 X15 X16 _).
  assert (KA : WOK_avail st W).
  { intros c' k' Hc' Hin. (nelimp shA 4%nat; intros S1 S2 S3 S4). (nelimp geomA 6%nat; intros G1 G2 G3 G4 G5 _).
    pose proof (region_facts st WF c' Hc') as RF. cbn zeta in RF. (nelim RF 10%nat; intros Y1 Y2 Y3 Y4 Y5 Y6 Y7 Y8 Y9 Y10).
    destruct (Z.eq_dec c' 0) as [->|NZ].
    { exfalso. unfold avail_cptrs in Hin. pose proof (wb_class0 st (wf_base_ok st WF)) as [E1 E2]. rewrite E1, E2 in Hin. cbn in Hin.
      unfold apend_cptrs in Hin. apply in_map_iff in Hin as ([c'' k''] & _ & Hf). apply filter_In in Hf as [Hin Hb]. cbn [fst] in Hb.
      apply Z.eqb_eq in Hb. subst c''. pose proof (wq_apend st (wf_quar_ok st WF) _ Hin). cbn [fst] in *. lia. }
    assert (CV : carved_cptr st c' k').
    { apply (wc_used_carved st c' (wf_class_ok st WF c' Hc')). unfold used_cptrs. rewrite !in_app_iff. apply in_app_iff in Hin. tauto. }
    (nelim (carved_chunk st WF c' k' Hc' ltac:(lia) CV) 3%nat; intros C1 C2 C3).
    pose proof (csize_pos c' ltac:(unfold KNUMCLASSES in Hc'; lia)) as SP'.
    pose proof (rt_SH_mono (cptr_addr st c' k' + csize c') (@CEIL ACEIL) ltac:(unfold CEIL, KREGIONSIZE, KFREEARRAY_OFF in *; lia)) as B2. rewrite SH_CEIL in B2.
    pose proof (rt_SH_mono (cptr_addr st c' k') (cptr_addr st c' k' + csize c') ltac:(lia)) as B3.
    clear - HS B2 B3 G1 G5 SP' Y1. induction W as [|[lo hi] W' IH]; [exact I|].
    pose proof (Forall_inv HS) as A1. cbn [fst snd] in A1. cbn.
    split; [unfold SH, CEIL, KHIGHMEM_BEG, AIMG_HI in *; Z.div_mod_to_equations; lia| apply IH; exact (Forall_inv_tail HS)]. }
  constructor; try assumption. eapply (T_avail st WF W m m' MU WM); [exact (rr_avail st m HR)| exact KA].
Qed.
End APZ.


End CeilWrap.
