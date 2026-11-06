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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RT_fp RT_artF.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_common_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_m_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RTW_m_tpz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.ABand.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_bandtac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_bandtac2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RT_bandtac4.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Ceil.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import LiaOn.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition pz_ok (st : rtstate) (cls : Z) (iv : Z * Z) : Prop :=
  (st_t st + T_ACACHE <= fst iv /\ snd iv <= st_t st + T_UNWINDING)
  \/ CEIL <= fst iv
  \/ (rinfo st cls <= fst iv /\ snd iv <= rinfo st cls + 128)
  \/ (rbeg st cls + r_mapped (rg st cls) <= fst iv /\ snd iv <= rbeg st cls + KFREEARRAY_OFF)
  \/ (fabeg st cls + 4 * num_freed st cls <= fst iv /\ snd iv <= fabeg st cls + KFREEARRAY_SIZE)
  \/ (SH (rbeg st cls + r_mapped (rg st cls)) <= fst iv /\ snd iv <= SH (rbeg st cls + KREGIONSIZE)).

Section PZ.
Variable st : rtstate.
Hypothesis WF : RTWF st.
Variable cls : Z.
Hypothesis Hcls : 1 <= cls <= 30.
Variable W : list (Z * Z).
Hypothesis HW : Forall (pz_ok st cls) W.

Local Abbreviation t := (st_t st).
Local Abbreviation P := (st_pbase st).
Let rb := rbeg st cls.
Let mapped := r_mapped (rg st cls).
Let nf := num_freed st cls.

Lemma tpx : tpx_ok st.
Proof. split; [exact (wb_ctx_t st (wf_base_ok st WF))| exact (wb_dtls_t st (wf_base_ok st WF))]. Qed.

(* [comment removed for export] *)
Lemma cls_facts : KHIGHMEM_BEG <= rb /\ P <= rb /\ rb + KREGIONSIZE <= ris st /\ ris st + 4096 <= P + PRIM_RES_SIZE /\ P + PRIM_RES_SIZE <= CEIL
  /\ 0 <= r_allocated (rg st cls) <= mapped /\ mapped <= KFREEARRAY_OFF /\ 0 <= nf /\ 4 * nf <= r_mapped_fa (rg st cls) /\ r_mapped_fa (rg st cls) <= KFREEARRAY_SIZE
  /\ rb mod 8 = 0 /\ mapped mod 8 = 0 /\ fabeg st cls = rb + KFREEARRAY_OFF /\ rinfo st cls = ris st + 128 * cls.
Proof.
  assert (Hc : 0 <= cls < KNUMCLASSES) by (unfold KNUMCLASSES; lia).
  pose proof (region_facts st WF cls Hc) as RF. cbn zeta in RF. (nelim RF 10%nat; intros X1 X2 X3 X4 X5 X6 X7 X8 X9 X10).
  (nelimp (region_range st WF cls Hc) 6%nat; intros Y1 Y2 Y3 Y4 Y5 Y6).
  (nelimp (ris_range st WF) 4%nat; intros Z1 Z2 Z3 Z4). (nelimp (P_range st WF) 3%nat; intros P1 P2 P3).
  pose proof (wc_num_freed st cls (wf_class_ok st WF cls Hc)) as NF. pose proof (zlen_nonneg (r_fa (rg st cls))) as NF0.
  subst rb mapped nf. unfold num_freed, ris, CEIL in *. unfold KSPACESIZE in *. repeat split; try lia; try reflexivity.
Qed.

(* [comment removed for export] *)
Lemma pz_disj : forall a sz,
  (a + sz <= t + T_ACACHE \/ t + T_UNWINDING <= a) -> a + sz <= CEIL ->
  (a + sz <= rinfo st cls \/ rinfo st cls + 128 <= a) ->
  (a + sz <= rb + mapped \/ rb + KFREEARRAY_OFF <= a) ->
  (a + sz <= fabeg st cls + 4 * nf \/ fabeg st cls + KFREEARRAY_SIZE <= a) ->
  (a + sz <= SH (rb + mapped) \/ SH (rb + KREGIONSIZE) <= a) ->
  disjoint_from W a sz.
Proof.
  intros a sz H1 H2 H3 H4 H5 H6. clear Hcls. induction W as [|[lo hi] W' IH]; [exact I|].
  pose proof (Forall_inv HW) as A. pose proof (Forall_inv_tail HW) as B. unfold pz_ok in A. cbn [fst snd] in A. subst rb mapped nf.
  cbn. split; [unfold T_ACACHE, T_UNWINDING, CEIL in *; lia| apply IH; exact B].
Qed.

(* [comment removed for export] *)
Lemma pz_low : forall a sz, AIMG_LO <= a -> a + sz <= SH KHIGHMEM_BEG -> (a + sz <= AIMG_HI \/ KLOWSHADOW_BEG <= a) -> disjoint_from W a sz.   (* [comment removed for export] *)
Proof.
  intros a sz H0 H HZ. (nelimp cls_facts 14%nat; intros X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 X13 X14). pose proof (t_rng st WF) as [T1 T2].
  pose proof (rt_SH_mono KHIGHMEM_BEG (rb + mapped) ltac:(lia)) as M1.
  change (SH KHIGHMEM_BEG) with 0x2008fff7000 in *. unfold KHIGHMEM_BEG, AIMG_HI, CEIL in *.
  apply pz_disj; unfold T_ACACHE, T_UNWINDING, CEIL.
  - clear - H0 H HZ T1. blia.
  - lia.
  - left. rewrite X14. unfold ris, KSPACESIZE, KREGIONSIZE in *. lia.
  - left. lia.
  - left. rewrite X13. unfold KFREEARRAY_OFF. lia.
  - left. lia.
Qed.
Local Ltac low := apply pz_low; change (SH KHIGHMEM_BEG) with 0x2008fff7000; unfold KHIGHMEM_BEG, AIMG_LO, AIMG_HI, KLOWSHADOW_BEG; cbn -[Z.add Z.mul Z.le Z.lt Z.sub]; lia.

(* [comment removed for export] *)
Lemma pz_obj : forall lo hi a sz, (hi <= t \/ t + 4096 <= lo) -> (hi <= P \/ P + PRIM_RES_SIZE <= lo) ->
  (hi <= KLOWSHADOW_BEG \/ KHIGHMEM_BEG <= lo) -> lo <= a -> a + sz <= hi -> hi <= CEIL -> disjoint_from W a sz.   (* [comment removed for export] *)
Proof.
  intros lo hi a sz Dt Dp K H1 H2 H3. (nelimp cls_facts 14%nat; intros X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 X13 X14).
  pose proof (rt_SH_bounds (rb + KREGIONSIZE) ltac:(unfold KREGIONSIZE, CEIL, KHIGHMEM_BEG, AIMG_HI in *; lia)) as B.
  pose proof (rt_SH_mono KHIGHMEM_BEG (rb + mapped) ltac:(lia)) as M1. change (SH KHIGHMEM_BEG) with 0x2008fff7000 in M1.
  unfold KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG, KREGIONSIZE, KFREEARRAY_OFF, KFREEARRAY_SIZE, CEIL in *.
  apply pz_disj; unfold T_ACACHE, T_UNWINDING, CEIL, KFREEARRAY_OFF, KFREEARRAY_SIZE, KREGIONSIZE; rewrite ?X13, ?X14; unfold ris, KSPACESIZE in *; (cut_on [Dt H1 H2 X1 H3 Hcls Dp X2 X3 X4 X6 X12 X8 K B M1] blia).
Qed.

(* [comment removed for export] *)
Lemma pz_prim : forall a sz, P <= a -> a + sz <= P + PRIM_RES_SIZE ->
  (a + sz <= rinfo st cls \/ rinfo st cls + 128 <= a) ->
  (a + sz <= rb + mapped \/ rb + KFREEARRAY_OFF <= a) ->
  (a + sz <= fabeg st cls + 4 * nf \/ fabeg st cls + KFREEARRAY_SIZE <= a) ->
  disjoint_from W a sz.
Proof.
  intros a sz H1 H2 H3 H4 H5. (nelimp cls_facts 14%nat; intros X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 X13 X14).
  pose proof (t_vs_prim st WF) as TP. (nelimp (P_range st WF) 3%nat; intros P1 P2 P3).
  pose proof (rt_SH_bounds (rb + KREGIONSIZE) ltac:(unfold KREGIONSIZE, CEIL, KHIGHMEM_BEG, AIMG_HI in *; lia)) as B.
  unfold KHIGHMEM_BEG, AIMG_HI, CEIL, KREGIONSIZE in *.
  apply pz_disj; try assumption; unfold T_ACACHE, T_UNWINDING, CEIL, KREGIONSIZE; lia.
Qed.

(* [comment removed for export] *)
Lemma pz_sh : forall lo hi, 0 <= lo -> lo <= hi -> hi <= CEIL -> lo mod 8 = 0 ->   (* [comment removed for export] *)
  (hi <= rb + mapped \/ rb + KREGIONSIZE <= lo) ->
  disjoint_from W (SH lo) (SH hi - SH lo).
Proof.
  intros lo hi K1 K2 K3 AL D. (nelimp cls_facts 14%nat; intros X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 X13 X14).
  pose proof (t_rng st WF) as [T1 T2].
  pose proof (rt_SH_bounds hi ltac:(unfold CEIL, KHIGHMEM_BEG, AIMG_HI in *; lia)) as B1. pose proof (rt_SH_mono lo hi K2) as B2.
  pose proof (rt_SH_mono 0 lo K1) as M0. change (SH 0) with 0x7fff8000 in M0.
  assert (D6 : SH lo + (SH hi - SH lo) <= SH (rb + mapped) \/ SH (rb + KREGIONSIZE) <= SH lo).
  { destruct D as [D|D]; [left; pose proof (rt_SH_mono hi (rb + mapped) D); lia| right; exact (rt_SH_mono _ _ D)]. }
  unfold KHIGHMEM_BEG, AIMG_HI, CEIL in *.
  apply pz_disj; try exact D6; unfold T_ACACHE, T_UNWINDING, CEIL, KFREEARRAY_OFF, KFREEARRAY_SIZE, KREGIONSIZE; rewrite ?X13, ?X14; unfold ris, KSPACESIZE, KREGIONSIZE in *; blia.
Qed.

(* [comment removed for export] *)
Lemma PZ_link : WOK_link W.
Proof. split; [intros a v Hin; destruct (alink_range a v Hin); low| unfold A_GLOBREC_LO, A_GLOBREC_HI; low]. Qed.
Lemma PZ_consts : WOK_consts W.
Proof.
  unfold WOK_consts.
  unfold A_SHADOW_OFF_CELL, A_UAR_OPTION, A_AFLAGS, A_CFLAGS, A_PAGESIZE_CACHED, A_KHIGHMEMEND, A_KMIDMEMBEG, A_KMIDMEMEND,
    A_ASAN_INITED, A_MCS, A_CAN_POISON, A_TSD_KEY_INITED, A_TSD_KEY, A_MAY_RETURN_NULL, A_ALLOC_OOM, A_DYING, A_VERBOSITY,
    A_MFHOOKS, A_LSAN_DISABLE, A_IA_INITED, AHOOKS, A_LIBC_PAGESIZE, A_MU_GLOBALS, A_GLOBALS_REGD, A_TPCG_INITED, A_TOOLNAME, A_PRINTF_CB, A_EMB, ATP.
  repeat lazymatch goal with |- _ /\ _ => split | _ => idtac end; low.
Qed.
Lemma PZ_alloc : WOK_alloc W.
Proof.
  unfold WOK_alloc, A_ALLOC, A_SECONDARY, A_GSTATS, A_QUAR, A_MAXUSERSZ, A_ALLOC.
  repeat lazymatch goal with |- _ /\ _ => split | _ => idtac end; low.
Qed.
Lemma PZ_ia : WOK_ia W.
Proof. intros i Hi. unfold A_IA_MAP1. low. Qed.
Lemma PZ_lowshadow : WOK_lowshadow W.
Proof. intros g Hg. change (SH AIMG_LO) with 0x7fffa000 in Hg. change (SH AIMG_HI) with 0x800b7e00 in Hg. low. Qed.

(* [comment removed for export] *)
Lemma pa_vs_prim : P + PRIM_RES_SIZE <= st_pa st \/ st_pa st + PTRARR_RES_SIZE <= P.
Proof.
  pose proof (wb_pwdj st (wf_base_ok st WF)) as PW. unfold rt_ranges in PW. cbn [pwdj] in PW.
  destruct PW as [PW _]. pose proof (Forall_inv PW) as D. cbn [fst snd] in D. lia.
Qed.
Lemma loose_vs_prim : forall b k, In (b, k) (st_loose0 st) -> P + PRIM_RES_SIZE <= b \/ b + k <= P.
Proof.
  intros b k Hin. exact (prim_vs_tail st WF (b, b + k) ltac:(apply in_or_app; left; apply in_map_iff; exists (b, k); auto)).
Qed.
Lemma sec_vs_prim : forall mb n, In (mb, n) (st_sec st) -> P + PRIM_RES_SIZE <= mb \/ mb + smapsize n <= P.
Proof.
  intros mb n Hin. exact (prim_vs_tail st WF (mb, mb + smapsize n) ltac:(apply in_or_app; right; apply in_or_app; left; apply in_map_iff; exists (mb, n); auto)).
Qed.
Lemma nb_vs_prim : forall b, In b (d_nblocks (st_depot st)) -> P + PRIM_RES_SIZE <= b \/ b + NODEBLOCK_SIZE <= P.
Proof.
  intros b Hin. exact (prim_vs_tail st WF (b, b + NODEBLOCK_SIZE) ltac:(apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; apply in_map_iff; exists b; auto)).
Qed.

(* [comment removed for export] *)
Lemma rbeg_other : forall c, 0 <= c < KNUMCLASSES -> c <> cls -> rbeg st c + KREGIONSIZE <= rb \/ rb + KREGIONSIZE <= rbeg st c.
Proof.
  intros c Hc NE. subst rb. unfold rbeg, region_beg, KREGIONSIZE. destruct (Z_lt_le_dec c cls); [left| right]; nia.
Qed.
Lemma rinfo_other : forall c, 0 <= c < KNUMCLASSES -> c <> cls -> rinfo st c + 128 <= rinfo st cls \/ rinfo st cls + 128 <= rinfo st c.
Proof. intros c Hc NE. unfold rinfo. destruct (Z_lt_le_dec c cls); [left| right]; nia. Qed.

(* [comment removed for export] *)
Lemma PZ_rinfo_other : forall c, 0 <= c < KNUMCLASSES -> c <> cls -> disjoint_from W (rinfo st c) 128.
Proof.
  intros c Hc NE. (nelimp cls_facts 14%nat; intros X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 X13 X14).
  (nelimp (ris_range st WF) 4%nat; intros Z1 Z2 Z3 Z4). pose proof (rinfo_other c Hc NE). unfold KNUMCLASSES in Hc.
  apply pz_prim; unfold rinfo in *; rewrite ?X13; unfold KFREEARRAY_OFF, KFREEARRAY_SIZE, KREGIONSIZE in *; lia.
Qed.

(* [comment removed for export] *)
Lemma PZ_regions : WOK_regions st W.
Proof.
  intros c Hc. (nelimp cls_facts 14%nat; intros X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 X13 X14).
  pose proof (region_facts st WF c Hc) as RF. cbn zeta in RF. (nelim RF 10%nat; intros R1 R2 R3 R4 R5 R6 R7 R8 R9 R10).
  assert (FB : fabeg st c = rbeg st c + KFREEARRAY_OFF) by reflexivity.
  pose proof (wc_num_freed st c (wf_class_ok st WF c Hc)) as NFc.
  (nelimp (ris_range st WF) 4%nat; intros Z1 Z2 Z3 Z4).
  assert (RR : rbeg st c + KREGIONSIZE <= ris st) by ((nelimp (region_range st WF c Hc) 4%nat; intros _ _ Y3 _); unfold ris; exact Y3).
  assert (AL8 : (rbeg st c + r_allocated (rg st c)) mod 8 = 0) by (rewrite Z.add_mod, R8, R9 by lia; reflexivity).
  assert (ESH : (r_mapped (rg st c) - r_allocated (rg st c)) / 8 = SH (rbeg st c + r_mapped (rg st c)) - SH (rbeg st c + r_allocated (rg st c)))
    by (rewrite !rt_SH_aligned_add by exact R8; Z.div_mod_to_equations; lia).
  rewrite ESH.
  destruct (Z.eq_dec c cls) as [->|NE].
  - split.
    + intros i Hi. apply pz_prim; rewrite ?FB, ?X13, ?X14 in *; unfold num_freed, KFREEARRAY_OFF, KFREEARRAY_SIZE, KREGIONSIZE in *; subst rb mapped nf; lia.
    + apply pz_sh; unfold CEIL, KREGIONSIZE, KFREEARRAY_OFF, KHIGHMEM_BEG, AIMG_HI in *; subst rb mapped; lia.
  - pose proof (rbeg_other c Hc NE) as RO. split.
    + intros i Hi. apply pz_prim; rewrite ?FB, ?X13, ?X14 in *; unfold num_freed, KFREEARRAY_OFF, KFREEARRAY_SIZE, KREGIONSIZE in *; subst rb mapped nf; (lia_on R2 R5 Hi R7 NFc Z4 RR Hcls X6 X11 X12 R8 R10 RO X8).
    + apply pz_sh; unfold CEIL, KREGIONSIZE, KFREEARRAY_OFF, KHIGHMEM_BEG, AIMG_HI in *; subst rb mapped; (lia_on X1 R1 R5 R4 R6 Z4 RR AL8 X6 X11 X12 R8 R9 R10 RO).
Qed.

(* [comment removed for export] *)
Lemma PZ_avail : WOK_avail st W.
Proof.
  intros c k Hc Hk. (nelimp cls_facts 14%nat; intros X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 X13 X14).
  pose proof (region_facts st WF c Hc) as RF. cbn zeta in RF. (nelim RF 10%nat; intros R1 R2 R3 R4 R5 R6 R7 R8 R9 R10).
  destruct (Z.eq_dec c 0) as [->|NZ].
  { exfalso. unfold avail_cptrs in Hk. pose proof (wb_class0 st (wf_base_ok st WF)) as [E1 E2]. rewrite E1, E2 in Hk. cbn in Hk.
    unfold apend_cptrs in Hk. apply in_map_iff in Hk as ([c' k'] & _ & Hf). apply filter_In in Hf as [Hin Hb]. cbn [fst] in Hb.
    apply Z.eqb_eq in Hb. subst c'. pose proof (wq_apend st (wf_quar_ok st WF) _ Hin). cbn [fst] in *. lia. }
  assert (CV : carved_cptr st c k).
  { apply (wc_used_carved st c (wf_class_ok st WF c Hc)). unfold used_cptrs. rewrite !in_app_iff. apply in_app_iff in Hk. tauto. }
  (nelim (carved_chunk st WF c k Hc ltac:(lia) CV) 3%nat; intros C1 C2 C3).
  pose proof (csize_pos c ltac:(unfold KNUMCLASSES in Hc; lia)) as SP.
  assert (AL8 : cptr_addr st c k mod 8 = 0).
  { unfold cptr_addr. replace (rbeg st c + 16 * k) with (2 * k * 8 + rbeg st c) by lia. rewrite Z.add_mod, Z_mod_mult, R8 by lia. reflexivity. }
  replace (csize c / 8) with (SH (cptr_addr st c k + csize c) - SH (cptr_addr st c k)) by (rewrite rt_SH_aligned_add by exact AL8; lia).
  assert (RR : rbeg st c + KREGIONSIZE <= ris st) by ((nelimp (region_range st WF c Hc) 4%nat; intros _ _ Y3 _); unfold ris; exact Y3).
  (nelimp (ris_range st WF) 4%nat; intros Z1 Z2 Z3 Z4).
  destruct (Z.eq_dec c cls) as [->|NE].
  - apply pz_sh; unfold CEIL, KREGIONSIZE, KFREEARRAY_OFF, KHIGHMEM_BEG, AIMG_HI in *; subst rb mapped; lia.
  - pose proof (rbeg_other c Hc NE). apply pz_sh; unfold CEIL, KREGIONSIZE, KFREEARRAY_OFF, KHIGHMEM_BEG, AIMG_HI in *; subst rb mapped; (lia_on X1 R1 R5 C1 SP R4 R6 C2 RR Z4 AL8 Hc X6 X11 X12 R8 R9 R10 NZ C3 H).
Qed.

(* [comment removed for export] *)
Lemma PZ_thread : WOK_thread st W.
Proof.
  pose proof (t_rng st WF) as [T1 T2]. pose proof (t_vs_prim st WF) as TP. (nelimp cls_facts 14%nat; intros X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 X13 X14).
  pose proof (rt_SH_bounds (rb + KREGIONSIZE) ltac:(unfold KREGIONSIZE, CEIL, KHIGHMEM_BEG, AIMG_HI in *; lia)) as B.
  pose proof (rt_SH_mono KHIGHMEM_BEG (rb + mapped) ltac:(lia)) as M1. change (SH KHIGHMEM_BEG) with 0x2008fff7000 in M1.
  unfold WOK_thread.
  assert (TC : forall a sz, t <= a -> (a + sz <= t + T_ACACHE \/ (t + T_UNWINDING <= a /\ a + sz <= t + 4096)) -> disjoint_from W a sz).
  { intros a sz Ha H. unfold KHIGHMEM_BEG, AIMG_HI, CEIL, KREGIONSIZE in *.
    apply pz_disj; unfold T_ACACHE, T_UNWINDING, CEIL, KFREEARRAY_OFF, KFREEARRAY_SIZE, KREGIONSIZE in *; rewrite ?X13, ?X14; unfold ris, KSPACESIZE in *; (cut_on [H T2 X1 Hcls TP X2 X3 X4 Ha X6 X12 X8 T1 B M1] blia). }
  split; [apply TC; [lia| left; unfold T_ACACHE; lia]|].
  split; [apply TC; [unfold qcache_t, T_QCACHE; lia| left; unfold qcache_t, T_QCACHE, T_ACACHE; lia]|].
  split; [apply TC; [unfold T_UNWINDING; lia| right; unfold T_UNWINDING; lia]|].
  destruct tpx as [CX DX].
  (nelim (wb_ctx_loose st (wf_base_ok st WF)) 5%nat; intros cb ck CL1 CL2 CL3). (nelim (loose0_range st WF _ _ CL1) 4%nat; intros Q1 Q2 Q3 Q4).
  (nelimp (oclr_lin _ _ Q1 ltac:(lia)) 3%nat; intros _ QL2 _).
  pose proof (loose_vs_prim cb ck CL1) as CP.
  split; [eapply (pz_obj (st_ctx st) (st_ctx st + 160)); [exact CX| clear - CP CL2 CL3; lia| clear - QL2 CL2 CL3; lia| unfold CTX_TID; lia| unfold CTX_TID; lia| unfold CEIL; clear - Q3 CL3; lia]|].
  split; [eapply (pz_obj (st_ctx st) (st_ctx st + 160)); [exact CX| clear - CP CL2 CL3; lia| clear - QL2 CL2 CL3; lia| unfold CTX_THREAD; lia| unfold CTX_THREAD; lia| unfold CEIL; clear - Q3 CL3; lia]|].
  unfold A_TSD_PTR, A_TSD_MAIN, A_DTV_PTR, A_DTV, A_TLSMOD, A_FSTLS_CELL, A_DTLS_OFF, ATP in *.
  split; [low|]. split; [low|]. split; [low|]. split; [low|]. split; [low|]. split; [low|].
  (nelim (wb_dtls_loose st (wf_base_ok st WF)) 5%nat; intros db dk DL1 DL2 DL3). (nelim (loose0_range st WF _ _ DL1) 4%nat; intros D1 D2 D3 D4).
  (nelimp (oclr_lin _ _ D1 ltac:(lia)) 3%nat; intros _ DLB _).
  pose proof (loose_vs_prim db dk DL1) as DP.
  eapply (pz_obj (tl_dtls_block (st_tls st) + 24) (tl_dtls_block (st_tls st) + 32)); [exact DX| clear - DP DL2 DL3; lia| clear - DLB DL2 DL3; lia| lia| lia| unfold CEIL; clear - D3 DL3; lia].
Qed.

(* [comment removed for export] *)
Lemma PZ_block : forall A n, In (A, n) (all_blocks st) -> WOK_block W A n.
Proof.
  intros A n HB. (nelimp cls_facts 14%nat; intros X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 X13 X14).
  (nelimp (block_geom st WF A n HB) 11%nat; intros Gn GA K X Y CE L16 H16 EA Gp Gs). unfold usz in Y.
  assert (L8 : b_lo A n mod 8 = 0) by (clear -L16; Z.div_mod_to_equations; lia).
  pose proof (rz_size_range n) as (Z1 & Z2).
  (nelimp (ris_range st WF) 4%nat; intros W1 W2 W3 W4).
  assert (RZA : b_lo A n + rz_size n <= A).
  { rewrite EA at 2. unfold sh_left, SEC_HDR, SEC_RZ. destruct (bprim n) eqn:EP.
    + Z.div_mod_to_equations. lia.
    + (nelim (sec_facts n EP) 3%nat; intros _ F2 _). rewrite F2. cbn. (lia_on Z1). }
  unfold KHIGHMEM_BEG, AIMG_HI, KREGIONSIZE, KFREEARRAY_OFF, KFREEARRAY_SIZE, PRIM_RES_SIZE, CEIL in *.
  (* [comment removed for export] *)
  assert (LOC : (P <= b_lo A n /\ b_hi A n + 4096 <= P + 0x2000011000 /\ b_hi A n <= rb + mapped)
              \/ (P <= b_lo A n /\ b_hi A n + 4096 <= P + 0x2000011000 /\ (b_hi A n <= rb \/ rb + 4294967296 <= b_lo A n) /\ b_hi A n <= ris st)
              \/ ((b_hi A n <= t \/ t + 4096 <= b_lo A n) /\ (b_hi A n <= P \/ P + 0x2000011000 <= b_lo A n))).
  { destruct (bprim n) eqn:EP.
    - (nelim (Gp eq_refl) 6%nat; intros C1 C2 C3 C4 C5 C6).
      assert (Hc' : 0 <= pclass n < KNUMCLASSES) by (unfold KNUMCLASSES; lia).
      destruct (Z.eq_dec (pclass n) cls) as [E|NE].
      + left. rewrite E in C2, C3. subst rb mapped. lia.
      + right. left. pose proof (rbeg_other (pclass n) Hc' NE) as RO. unfold KREGIONSIZE in RO.
        (nelimp (region_range st WF (pclass n) Hc') 4%nat; intros _ Y2 Y3 _). unfold KFREEARRAY_OFF, KREGIONSIZE, ris in *. subst rb. clear -C2 C3 C4 C5 RO Y2 Y3. lia.
    - (nelim (Gs eq_refl) 4%nat; intros S1 S2 S3 S4). right. right. split; [exact (t_vs_block st WF A n HB)|].
      pose proof (sec_vs_prim _ _ S1) as SP. unfold PRIM_RES_SIZE in SP. clear -SP S2. lia. }
  clear Gp Gs.
  assert (OBJ : forall a sz, b_lo A n <= a -> a + sz <= b_hi A n -> disjoint_from W a sz).
  { intros a sz Ha Hs. destruct LOC as [(C4 & C5 & C3)|[(C4 & C5 & RO & RI)|[TB SP]]].
    - apply pz_prim; unfold KFREEARRAY_OFF, KFREEARRAY_SIZE, PRIM_RES_SIZE; rewrite ?X13, ?X14; clear -Ha Hs C4 C5 C3 X3 X6 X7 X8 W3 Hcls; lia.
    - apply pz_prim; unfold KFREEARRAY_OFF, KFREEARRAY_SIZE, PRIM_RES_SIZE; rewrite ?X13, ?X14; clear -Ha Hs C4 C5 RO RI X3 X6 X7 X8 W3 Hcls; lia.
    - eapply (pz_obj (b_lo A n) (b_hi A n)); unfold KHIGHMEM_BEG, AIMG_HI, PRIM_RES_SIZE, CEIL; [exact TB| exact SP| exact (ablk_disj_band _ _ K)| exact Ha| exact Hs| exact CE]. }
  split; [|split; [|split]].
  - apply OBJ; unfold b_chunk_beg; lia.
  - intros HRZ. apply OBJ; unfold b_alloc_beg; lia.
  - intros EP. apply OBJ; unfold b_lo in *; rewrite ?EP in *; unfold b_map_beg, SEC_HDR, SEC_RZ in *; lia.
  - (* [comment removed for export] *)
    assert (EH : b_hi A n = b_lo A n + asz n) by reflexivity.
    replace (sh_tot n) with (SH (b_hi A n) - SH (b_lo A n)) by (change (sh_tot n) with (asz n / 8); rewrite EH, rt_SH_aligned_add by exact L8; lia).
    (nelimp (ablk_lin _ _ K) 3%nat; intros KL1 KL2 _). 
    apply pz_sh; unfold KHIGHMEM_BEG, AIMG_HI, CEIL, KREGIONSIZE; [exact KL2| lia| exact CE| exact L8|].
    destruct LOC as [(C4 & C5 & C3)|[(C4 & C5 & RO & RI)|[TB SP]]]; [clear -C3 X6 KL2 X| clear -RO X6 KL2 X| clear -SP X2 X3 X6 W4 KL2 X]; subst rb mapped; lia.
Qed.
Lemma PZ_live : WOK_live st W.
Proof. intros A n Hin. apply PZ_block. unfold all_blocks; apply in_or_app; left; exact Hin. Qed.
Lemma PZ_quar : WOK_quar st W.
Proof. intros A n Hin. apply PZ_block. unfold all_blocks; apply in_or_app; right; exact Hin. Qed.

(* [comment removed for export] *)
Lemma PZ_batches : WOK_batches st W.
Proof.
  intros b Hb. (nelimp cls_facts 14%nat; intros X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 X13 X14).
  (nelim (batch_geom st WF b Hb) 5%nat; intros BB BF R1 R2 AL). destruct (wq_batch st (wf_quar_ok st WF) b Hb) as [CNT _]. unfold QBATCH_CAP in CNT.
  assert (H24 : 0 <= 24 < KNUMCLASSES) by (unfold KNUMCLASSES; lia).
  pose proof (region_facts st WF 24 H24) as RF. cbn zeta in RF. (nelim RF 10%nat; intros Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 Q9 Q10).
  (nelimp (region_range st WF 24 H24) 4%nat; intros _ Y2 Y3 _). (nelimp (ris_range st WF) 4%nat; intros W1 W2 W3 W4).
  unfold ris in *. unfold KHIGHMEM_BEG, AIMG_HI, KREGIONSIZE, KFREEARRAY_OFF, KFREEARRAY_SIZE, QBATCH_SIZE, PRIM_RES_SIZE, KSPACESIZE in *.
  assert (LOC : qb_addr b + 8192 <= rb + mapped \/ (qb_addr b + 8192 <= rb \/ rb + 4294967296 <= qb_addr b)).
  { destruct (Z.eq_dec 24 cls) as [E|NE]; [left; subst rb mapped; rewrite <- E; lia| right].
    pose proof (rbeg_other 24 H24 NE) as RO. unfold KREGIONSIZE in RO. clear -RO R1 R2 Y2. lia. }
  assert (OBJ : forall a sz, qb_addr b <= a -> a + sz <= qb_addr b + 8192 -> disjoint_from W a sz).
  { intros a sz Ha Hs. apply pz_prim; unfold KFREEARRAY_OFF, KFREEARRAY_SIZE, PRIM_RES_SIZE; rewrite ?X13, ?X14; unfold ris; unfold KSPACESIZE; clear -Ha Hs LOC R1 R2 Y2 Y3 Q2 W4 X2 X3 X6 X7 X8 Hcls; subst rb mapped nf; lia. }
  split; [| split].
  - apply OBJ; lia.
  - intros i Hi. apply OBJ; lia.
  - assert (AL8 : qb_addr b mod 8 = 0) by (clear -AL; Z.div_mod_to_equations; lia).
    replace 1024 with (SH (qb_addr b + 8192) - SH (qb_addr b)) by (rewrite rt_SH_aligned_add by exact AL8; change (8192 / 8) with 1024; lia).
    apply pz_sh; unfold KHIGHMEM_BEG, AIMG_HI, CEIL, KREGIONSIZE; [lia| lia| lia| exact AL8| clear -LOC X6; subst rb mapped; lia].
Qed.

(* [comment removed for export] *)
Lemma PZ_ptrarr : WOK_ptrarr st W.
Proof.
  split.
  - intros i Hi. (nelimp (pa_range st WF) 5%nat; intros P1 P2 P3 P4 P5). pose proof (t_vs_pa st WF) as TP. pose proof pa_vs_prim as PP.
    unfold KHIGHMEM_BEG, AIMG_HI, PTRARR_RES_SIZE in *.
    eapply (pz_obj (st_pa st) (st_pa st + 0x800000)); unfold KHIGHMEM_BEG, AIMG_HI, CEIL; [lia| lia| blia| lia| lia| lia].
  - intros e He. destruct (ws_spend st (wf_sec_ok st WF) e He) as [HE _].
    (nelim (ws_entry st (wf_sec_ok st WF) e HE) 4%nat; intros E1 E2 E3 _).
    pose proof (wb_ranges st (wf_base_ok st WF) (fst e, fst e + smapsize (snd e))) as R. cbn [fst snd] in R.
    specialize (R ltac:(unfold rt_ranges; do 2 right; rewrite !in_app_iff; right; left; apply in_map_iff; exists e; auto)).
    destruct e as [mb n]. cbn [fst snd] in *. (nelim (sec_facts n E1) 5%nat; intros _ _ _ F4 _). pose proof (usz_le_rounded8 n) as (U1 & _).
    pose proof (t_vs_sec st WF mb n HE) as TS. pose proof (sec_vs_prim mb n HE) as SP.
    (nelim R 4%nat; intros R1 R2 R3 R4). (nelimp (oclr_lin _ _ R1 ltac:(lia)) 3%nat; intros _ RLB _).
    eapply (pz_obj mb (mb + smapsize n)); unfold CEIL; [exact TS| clear -SP; lia| exact RLB| lia| unfold usz in *; lia| lia].
Qed.

(* [comment removed for export] *)
Lemma PZ_depot : WOK_depot st W.
Proof.
  pose proof (wf_depot_ok st WF) as WD. unfold WOK_depot.
  unfold A_DEPOT, A_DEPOT_NIDS, A_DEPOT_MAP1, A_STACKSTORE, DEPOT_TAB_LOG, SSTORE_NBLOCKS in *.
  split; [| split; [| split; [| split; [| split]]]].
  - intros i Hi. low.
  - low.
  - intros k Hk. low.
  - intros id Hid.
    set (q := id / DEPOT_L2_NODES). set (b := nthz (d_nblocks (st_depot st)) q 0).
    assert (Hq : 0 <= q < d_nnb (st_depot st)).
    { pose proof (wd_nnb st WD) as E. unfold d_nnb in *. rewrite E. subst q. unfold DEPOT_L2_NODES. Z.div_mod_to_equations. (cut_on [Hid H H0 H4 H5 H9 H10 H11 H12 H13] nia). }
    assert (Hb : In b (d_nblocks (st_depot st))) by (subst b; apply nthz_In; unfold d_nnb in Hq; exact Hq).
    (nelim (nb_range st WF b Hb) 3%nat; intros R1 R2 R3). pose proof (t_vs_nb st WF b Hb) as TB. pose proof (nb_vs_prim b Hb) as NP.
    assert (ADDR : dnode_addr (st_depot st) id = b + DEPOT_NODE_SZ * (id mod DEPOT_L2_NODES)) by reflexivity.
    rewrite ADDR. unfold DEPOT_NODE_SZ, DEPOT_L2_NODES, NODEBLOCK_SIZE in *.
    eapply (pz_obj b (b + 1048576)); unfold CEIL; [exact TB| clear -NP; lia| exact (ablk_disj_band _ _ R1)| Z.div_mod_to_equations; lia| Z.div_mod_to_equations; lia| lia].
  - low.
  - intros b Hb. low.
Qed.

(* [comment removed for export] *)
Lemma PZ_fs : WOK_fs st W.
Proof.
  (nelimp (fs_range st WF) 3%nat; intros F1 F2 F3). pose proof (t_vs_fs st WF) as TF.
  pose proof (loose_vs_prim _ _ (wb_fs_loose st (wf_base_ok st WF))) as FP.
  assert (OBJ : forall a sz, st_fs st <= a -> a + sz <= st_fs st + FS_TOTAL -> disjoint_from W a sz).
  { intros a sz Ha Hs. eapply (pz_obj (st_fs st) (st_fs st + FS_TOTAL)); [lia| clear -FP; lia| exact (ablk_disj_band _ _ F1)| lia| lia| exact F2]. }
  unfold WOK_fs. split; [| split; [| split; [| split]]].
  - intros k Hk. apply OBJ; unfold FS_TOTAL in *; lia.
  - apply OBJ; unfold FS_TOTAL in *; lia.
  - apply OBJ; unfold FS_TOTAL in *; lia.
  - intros k pos Hk Hp. pose proof (flags_ok k Hk) as [O1 O2]. apply OBJ; unfold fflag_addr, FS_TOTAL in *; lia.
  - intros F k Hin. (nelimp (frame_range st WF F k Hin) 4%nat; intros Hk X Y _). unfold FS_FRAMES_OFF, FS_TOTAL in *.
    assert (64 <= fsz k) by (destruct Hk as [-> | ->]; [change (fsz 1) with 128| change (fsz 2) with 256]; lia).
    apply OBJ; unfold FS_TOTAL; lia.
Qed.

(* [comment removed for export] *)
Theorem pz_others : forall m m', munch W m m' -> wmono bsegs m m' -> RTREP st m ->
  R_link m' /\ R_consts st m' /\ R_alloc st m' /\ R_regions st m' /\ R_avail st m' /\ R_thread st m'
  /\ R_live st m' /\ R_quar st m' /\ R_batches st m' /\ R_ptrarr st m' /\ R_depot st m' /\ R_fs st m' /\ R_ia m' /\ R_lowshadow m'.
Proof.
  intros m m' MU WM HR.
  split; [eapply (T_link W m m' MU); [exact (rr_link st m HR)| exact PZ_link]|].
  split; [eapply (T_consts st WF W m m' MU WM); [exact (rr_consts st m HR)| exact PZ_consts]|].
  split; [eapply (T_alloc st W m m' MU WM); [exact (rr_alloc st m HR)| exact PZ_alloc]|].
  split; [eapply (T_regions st WF W m m' MU WM); [exact (rr_regions st m HR)| exact PZ_regions]|].
  split; [eapply (T_avail st WF W m m' MU WM); [exact (rr_avail st m HR)| exact PZ_avail]|].
  split; [eapply (T_thread st WF W m m' MU WM); [exact (rr_thread st m HR)| exact PZ_thread]|].
  split; [eapply (T_live st WF W m m' MU WM); [exact (rr_live st m HR)| exact PZ_live]|].
  split; [eapply (T_quar st WF W m m' MU WM); [exact (rr_quar st m HR)| exact PZ_quar]|].
  split; [eapply (T_batches st WF W m m' MU WM); [exact (rr_batches st m HR)| exact PZ_batches]|].
  split; [eapply (T_ptrarr st WF W m m' MU WM); [exact (rr_ptrarr st m HR)| exact PZ_ptrarr]|].
  split; [eapply (T_depot st WF W m m' MU WM); [exact (rr_depot st m HR)| exact PZ_depot]|].
  split; [eapply (T_fs st WF W m m' MU WM); [exact (rr_fs st m HR)| exact PZ_fs]|].
  split; [eapply (T_ia W m m' MU WM); [exact (rr_ia st m HR)| exact PZ_ia]|].
  eapply (T_lowshadow W m m' MU WM); [exact (rr_lowshadow st m HR)| exact PZ_lowshadow].
Qed.

(* [comment removed for export] *)
Lemma pz_rinfo_other : forall m m' c jr je js, munch W m m' -> wmono bsegs m m' -> 0 <= c < KNUMCLASSES -> c <> cls ->
  rw_cells bsegs m (rinfo st c) (rinfo_cells st c jr je js) -> rw_cells bsegs m' (rinfo st c) (rinfo_cells st c jr je js).
Proof.
  intros m m' c jr je js MU WM Hc NE H. pose proof H as [[Wf _] _].
  eapply rw_cells_transport; [exact H| exact MU| exact WM|].
  rewrite (cells_bytes_length _ Wf) || idtac. replace (Z.of_nat (cells_size (rinfo_cells st c jr je js))) with 128.
  - exact (PZ_rinfo_other c Hc NE).
  - pose proof (cells_bytes_length _ Wf) as L. cbn in Wf. unfold rinfo_cells in *. cbn [cells_size Cells.csize] in *.
    (nelim Wf 13%nat; intros _ _ _ _ _ _ _ _ L1 _ L2 L3 _). lia.
Qed.
End PZ.


End CeilWrap.
