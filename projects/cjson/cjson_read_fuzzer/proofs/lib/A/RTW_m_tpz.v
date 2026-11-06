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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.ABand.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_bandtac4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition tpz_ok (st : rtstate) (iv : Z * Z) : Prop :=
  (st_t st + T_ACACHE <= fst iv /\ snd iv <= st_t st + T_UNWINDING) \/ CEIL <= fst iv.
(* [comment removed for export] *)
Definition tpx_ok (st : rtstate) : Prop :=
  (st_ctx st + 160 <= st_t st \/ st_t st + 4096 <= st_ctx st)
  /\ (tl_dtls_block (st_tls st) + 32 <= st_t st \/ st_t st + 4096 <= tl_dtls_block (st_tls st) + 24).

Section TPZ.
Variable st : rtstate.
Hypothesis WF : RTWF st.
Hypothesis HX : tpx_ok st.
Variable W : list (Z * Z).
Hypothesis HW : Forall (tpz_ok st) W.

Local Abbreviation t := (st_t st).

Lemma tpz_disj : forall a sz, (a + sz <= t + T_ACACHE \/ (t + T_UNWINDING <= a /\ a + sz <= CEIL)) -> disjoint_from W a sz.
Proof.
  intros a sz H. pose proof (t_range st WF) as TR. induction W as [|[lo hi] W' IH]; [exact I|].
  inversion HW; subst. cbn. unfold tpz_ok in H2. cbn [fst snd] in H2. unfold T_ACACHE, T_UNWINDING, CEIL, KHIGHMEM_BEG in *.
  split; [lia| apply IH; assumption].
Qed.

(* [comment removed for export] *)
Lemma t_rng : oclr t (t + 4096) /\ t + 4096 <= CEIL.
Proof. pose proof (t_range st WF). unfold CEIL. auto. Qed.

(* [comment removed for export] *)
Lemma tpz_obj : forall lo hi a sz, (hi <= t \/ t + 4096 <= lo) -> lo <= a -> a + sz <= hi -> hi <= CEIL -> disjoint_from W a sz.
Proof.
  intros lo hi a sz D H1 H2 H3. apply tpz_disj. unfold T_ACACHE, T_UNWINDING. lia.
Qed.
(* [comment removed for export] *)
Lemma tpz_low : forall a sz, AIMG_LO <= a -> a + sz <= KHIGHMEM_BEG -> (a + sz <= AIMG_HI \/ KLOWSHADOW_BEG <= a) -> disjoint_from W a sz.
Proof. intros a sz H0 H HZ. pose proof t_rng as [T1 T2]. apply tpz_disj. unfold T_ACACHE, T_UNWINDING, CEIL in *. clear - H0 H HZ T1 T2. blia. Qed.

(* [comment removed for export] *)
Lemma tpz_shadow : forall a sz, 0x7fff8000 <= a -> a + sz <= KHIGHMEM_BEG -> disjoint_from W a sz.
Proof. intros a sz H0 H. apply tpz_low; unfold AIMG_LO, KLOWSHADOW_BEG in *; lia. Qed.
Local Ltac shlo := unfold SH, SHADOW_OFFSET in *; Z.div_mod_to_equations; lia.

Local Ltac low := apply tpz_low; unfold KHIGHMEM_BEG, AIMG_LO, AIMG_HI, KLOWSHADOW_BEG; cbn -[Z.add Z.mul Z.le Z.lt Z.sub]; lia.

(* [comment removed for export] *)
Lemma t_in_loose : In (t, t + 4096) (map (fun e => (fst e, fst e + snd e)) (st_loose0 st)).
Proof. apply in_map_iff. exists (st_t st, 4096). split; [reflexivity| exact (wb_t_loose st (wf_base_ok st WF))]. Qed.

Lemma t_vs_prim : st_pbase st + PRIM_RES_SIZE <= t \/ t + 4096 <= st_pbase st.
Proof.
  destruct (prim_vs_tail st WF (t, t + 4096) ltac:(apply in_or_app; left; exact t_in_loose)) as [D|D]; cbn [fst snd] in D; lia.
Qed.

Lemma t_vs_pa : st_pa st + PTRARR_RES_SIZE <= t \/ t + 4096 <= st_pa st.
Proof.
  pose proof (wb_pwdj st (wf_base_ok st WF)) as PW. rewrite rt_ranges_tail in PW.
  pose proof (pwdj_app_disj _ _ (st_pa st, st_pa st + PTRARR_RES_SIZE) (t, t + 4096) PW ltac:(right; left; reflexivity)
                ltac:(apply in_or_app; left; exact t_in_loose)) as D. cbn [fst snd] in D. lia.
Qed.

Lemma t_vs_tail : forall r, In r (map (fun e => (fst e, fst e + smapsize (snd e))) (st_sec st)
                                  ++ map (fun b => (b, b + NODEBLOCK_SIZE)) (d_nblocks (st_depot st))
                                  ++ map (fun b => (b, b + STOREBLOCK_SIZE)) (d_sblocks (st_depot st))) ->
  8192 <= snd r - fst r -> snd r <= t \/ t + 4096 <= fst r.
Proof.
  intros r Hr Hsz. pose proof (wb_pwdj st (wf_base_ok st WF)) as PW. rewrite rt_ranges_tail in PW.
  cbn [app] in PW. destruct PW as [_ [_ PW]].
  destruct (pwdj_In _ _ _ PW ltac:(apply in_or_app; left; exact t_in_loose) ltac:(apply in_or_app; right; exact Hr)) as [E|D].
  - exfalso. destruct r as [a b]. injection E. intros. cbn [fst snd] in Hsz. lia.
  - cbn [fst snd] in D. lia.
Qed.

Lemma t_vs_sec : forall mb n, In (mb, n) (st_sec st) -> mb + smapsize n <= t \/ t + 4096 <= mb.
Proof.
  intros mb n Hin. destruct (ws_entry st (wf_sec_ok st WF) _ Hin) as (E1 & E2 & _). cbn [fst snd] in *.
  destruct (sec_facts n E1) as (_ & _ & _ & F4 & _). pose proof (usz_le_rounded8 n) as (U1 & _). unfold usz in *.
  destruct (t_vs_tail (mb, mb + smapsize n)) as [D|D]; [apply in_or_app; left; apply in_map_iff; exists (mb, n); auto| cbn [fst snd]; lia| left| right]; cbn [fst snd] in D; lia.
Qed.

Lemma t_vs_nb : forall b, In b (d_nblocks (st_depot st)) -> b + NODEBLOCK_SIZE <= t \/ t + 4096 <= b.
Proof.
  intros b Hb. destruct (t_vs_tail (b, b + NODEBLOCK_SIZE)) as [D|D];
    [apply in_or_app; right; apply in_or_app; left; apply in_map_iff; exists b; auto| cbn [fst snd]; unfold NODEBLOCK_SIZE; lia| left| right]; cbn [fst snd] in D; lia.
Qed.

Lemma t_vs_fs : t + 4096 <= st_fs st \/ st_fs st + FS_TOTAL <= t.
Proof. pose proof (t_page st WF) as (_ & _ & _ & FF). exact FF. Qed.

Lemma t_vs_block : forall A n, In (A, n) (all_blocks st) -> b_hi A n <= t \/ t + 4096 <= b_lo A n.
Proof. intros A n HB. exact (loose0_vs_block st WF t 4096 A n (wb_t_loose st (wf_base_ok st WF)) HB). Qed.

(* [comment removed for export] *)
Lemma TZ_link : WOK_link W.
Proof. split; [intros a v Hin; destruct (alink_range a v Hin); low| unfold A_GLOBREC_LO, A_GLOBREC_HI; low]. Qed.
Lemma TZ_consts : WOK_consts W.
Proof.
  unfold WOK_consts.
  unfold A_SHADOW_OFF_CELL, A_UAR_OPTION, A_AFLAGS, A_CFLAGS, A_PAGESIZE_CACHED, A_KHIGHMEMEND, A_KMIDMEMBEG, A_KMIDMEMEND,
    A_ASAN_INITED, A_MCS, A_CAN_POISON, A_TSD_KEY_INITED, A_TSD_KEY, A_MAY_RETURN_NULL, A_ALLOC_OOM, A_DYING, A_VERBOSITY,
    A_MFHOOKS, A_LSAN_DISABLE, A_IA_INITED, AHOOKS, A_LIBC_PAGESIZE, A_MU_GLOBALS, A_GLOBALS_REGD, A_TPCG_INITED, A_TOOLNAME, A_PRINTF_CB, A_EMB, ATP.
  repeat lazymatch goal with |- _ /\ _ => split | _ => idtac end; low.
Qed.
Lemma TZ_alloc : WOK_alloc W.
Proof.
  unfold WOK_alloc, A_ALLOC, A_SECONDARY, A_GSTATS, A_QUAR, A_MAXUSERSZ, A_ALLOC.
  repeat lazymatch goal with |- _ /\ _ => split | _ => idtac end; low.
Qed.
Lemma TZ_ia : WOK_ia W.
Proof. intros i Hi. unfold A_IA_MAP1. low. Qed.
Lemma TZ_lowshadow : WOK_lowshadow W.
Proof.
  intros g Hg. change (SH AIMG_LO) with 0x7fffa000 in Hg. change (SH AIMG_HI) with 0x800b7e00 in Hg. low.
Qed.

(* [comment removed for export] *)
Lemma TZ_rinfo : WOK_rinfo st W.
Proof.
  intros c Hc. pose proof (ris_range st WF) as (X1 & X2 & X3 & X4). unfold KNUMCLASSES in Hc.
  pose proof (P_range st WF) as (P1 & P2 & P3). pose proof t_vs_prim.
  eapply (tpz_obj (st_pbase st) (st_pbase st + PRIM_RES_SIZE)); [lia| unfold rinfo; lia| unfold rinfo; lia| unfold CEIL; lia].
Qed.

Lemma TZ_regions : WOK_regions st W.
Proof.
  intros c Hc. pose proof (region_facts st WF c Hc) as RF. cbn zeta in RF.
  destruct RF as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10).
  assert (FB : fabeg st c = rbeg st c + KFREEARRAY_OFF) by reflexivity.
  pose proof t_vs_prim as TP.
  unfold KHIGHMEM_BEG, KREGIONSIZE, KFREEARRAY_OFF, KFREEARRAY_SIZE, PRIM_RES_SIZE in *.
  split.
  - intros i Hi. pose proof (wc_num_freed st c (wf_class_ok st WF c Hc)) as NF.
    eapply (tpz_obj (st_pbase st) (st_pbase st + 0x2000011000)); [lia| lia| lia| unfold CEIL; lia].
  - pose proof (rt_SH_bounds (rbeg st c + r_allocated (rg st c)) ltac:(lia)) as B1.
    pose proof (rt_SH_mono (rbeg st c + r_mapped (rg st c)) (@CEIL ACEIL) ltac:(unfold CEIL; lia)) as B2. rewrite SH_CEIL in B2.
    rewrite !rt_SH_aligned_add in * by exact X8.
    apply tpz_shadow; [clear - B1 X8; shlo|]. unfold KHIGHMEM_BEG. Z.div_mod_to_equations. lia.
Qed.

Lemma TZ_avail : WOK_avail st W.
Proof.
  intros c k Hc Hk.
  pose proof (region_facts st WF c Hc) as RF. cbn zeta in RF. destruct RF as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10).
  destruct (Z.eq_dec c 0) as [->|NZ].
  { exfalso. unfold avail_cptrs in Hk. pose proof (wb_class0 st (wf_base_ok st WF)) as [E1 E2]. rewrite E1, E2 in Hk. cbn in Hk.
    unfold apend_cptrs in Hk. apply in_map_iff in Hk as ([c' k'] & _ & Hf). apply filter_In in Hf as [Hin Hb]. cbn [fst] in Hb.
    apply Z.eqb_eq in Hb. subst c'. pose proof (wq_apend st (wf_quar_ok st WF) _ Hin). cbn [fst] in *. lia. }
  assert (CV : carved_cptr st c k).
  { apply (wc_used_carved st c (wf_class_ok st WF c Hc)). unfold used_cptrs. rewrite !in_app_iff. apply in_app_iff in Hk. tauto. }
  destruct (carved_chunk st WF c k Hc ltac:(lia) CV) as (C1 & C2 & C3).
  pose proof (csize_pos c ltac:(unfold KNUMCLASSES in Hc; lia)) as SP.
  unfold KHIGHMEM_BEG, KREGIONSIZE, KFREEARRAY_OFF in *.
  pose proof (rt_SH_mono (cptr_addr st c k + csize c) (@CEIL ACEIL) ltac:(unfold CEIL; lia)) as B2. rewrite SH_CEIL in B2.
  pose proof (rt_SH_mono (cptr_addr st c k) (cptr_addr st c k + csize c) ltac:(lia)) as B3.
  apply tpz_shadow; [clear - C1 X1; shlo|]. unfold KHIGHMEM_BEG. unfold SH in *. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma TZ_thread : WOK_thread st W.
Proof.
  pose proof t_rng as [T1 T2]. unfold WOK_thread.
  split; [apply tpz_disj; left; unfold T_ACACHE; lia|].
  split; [apply tpz_disj; left; unfold qcache_t, T_QCACHE, T_ACACHE; lia|].
  split; [apply tpz_disj; right; unfold T_UNWINDING, CEIL in *; lia|].
  destruct HX as [CX DX].
  destruct (wb_ctx_loose st (wf_base_ok st WF)) as (cb & ck & CL1 & CL2 & CL3). destruct (loose0_range st WF _ _ CL1) as (R1 & R2 & R3 & R4).
  split; [eapply (tpz_obj (st_ctx st) (st_ctx st + 160)); [lia| unfold CTX_TID; lia| unfold CTX_TID; lia| unfold CEIL; lia]|].
  split; [eapply (tpz_obj (st_ctx st) (st_ctx st + 160)); [lia| unfold CTX_THREAD; lia| unfold CTX_THREAD; lia| unfold CEIL; lia]|].
  unfold A_TSD_PTR, A_TSD_MAIN, A_DTV_PTR, A_DTV, A_TLSMOD, A_FSTLS_CELL, A_DTLS_OFF, ATP in *.
  split; [low|]. split; [low|]. split; [low|]. split; [low|]. split; [low|]. split; [low|].
  destruct (wb_dtls_loose st (wf_base_ok st WF)) as (db & dk & DL1 & DL2 & DL3). destruct (loose0_range st WF _ _ DL1) as (Q1 & Q2 & Q3 & Q4).
  eapply (tpz_obj (tl_dtls_block (st_tls st) + 24) (tl_dtls_block (st_tls st) + 32)); [lia| lia| lia| unfold CEIL; lia].
Qed.

(* [comment removed for export] *)
Lemma TZ_block : forall A n, In (A, n) (all_blocks st) -> WOK_block W A n.
Proof.
  intros A n HB.
  pose proof (block_geom st WF A n HB) as (Gn & GA & K & X & Y & CE & L16 & H16 & EA & Gp & Gs). unfold usz in Y. unfold KHIGHMEM_BEG in K.
  assert (L8 : b_lo A n mod 8 = 0) by (apply (mod0_trans _ 8 16); [lia|lia|reflexivity|exact L16]).
  pose proof (t_vs_block A n HB) as TB. pose proof (rz_size_range n) as (Z1 & Z2).
  assert (OBJ : forall a sz, b_lo A n <= a -> a + sz <= b_hi A n -> disjoint_from W a sz).
  { intros a sz Ha Hs. eapply (tpz_obj (b_lo A n) (b_hi A n)); [lia| exact Ha| exact Hs| unfold CEIL; lia]. }
  assert (RZA : b_lo A n + rz_size n <= A).
  { rewrite EA at 2. unfold sh_left, SEC_HDR, SEC_RZ. destruct (bprim n) eqn:EP.
    + Z.div_mod_to_equations. lia.
    + destruct (sec_facts n EP) as (_ & F2 & _). rewrite F2. cbn. lia. }
  split; [|split; [|split]].
  - apply OBJ; unfold b_chunk_beg; lia.
  - intros HRZ. apply OBJ; unfold b_alloc_beg; lia.
  - intros EP. apply OBJ; unfold b_lo; rewrite ?EP; [| ]; unfold b_map_beg, SEC_HDR, SEC_RZ in *.
    + unfold b_lo in *. rewrite EP in *. unfold b_map_beg, SEC_HDR, SEC_RZ in *. lia.
    + unfold b_lo in *. rewrite EP in *. unfold b_map_beg, SEC_HDR, SEC_RZ in *. lia.
  - pose proof (rt_SH_mono (b_hi A n) (@CEIL ACEIL) ltac:(unfold CEIL; lia)) as B2. rewrite SH_CEIL in B2.
    assert (EH : b_hi A n = b_lo A n + asz n) by reflexivity.
    assert (ST8 : sh_tot n = asz n / 8) by reflexivity.
    rewrite EH, rt_SH_aligned_add in B2 by exact L8.
    apply tpz_shadow; [pose proof (ablk_lin _ _ K) as (K1 & K2 & _); clear - K1 K2; shlo|]. unfold KHIGHMEM_BEG. rewrite ST8. lia.
Qed.
Lemma TZ_live : WOK_live st W.
Proof. intros A n Hin. apply TZ_block. unfold all_blocks; apply in_or_app; left; exact Hin. Qed.
Lemma TZ_quar : WOK_quar st W.
Proof. intros A n Hin. apply TZ_block. unfold all_blocks; apply in_or_app; right; exact Hin. Qed.

(* [comment removed for export] *)
Lemma TZ_batches : WOK_batches st W.
Proof.
  intros b Hb.
  destruct (batch_geom st WF b Hb) as (BB & BF & R1 & R2 & AL).
  destruct (wq_batch st (wf_quar_ok st WF) b Hb) as [CNT (k & CV & EQ)].
  pose proof (region_facts st WF 24 ltac:(unfold KNUMCLASSES; lia)) as RF. cbn zeta in RF. destruct RF as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10).
  destruct (carved_chunk st WF 24 k ltac:(unfold KNUMCLASSES; lia) ltac:(lia) CV) as (C1 & C2 & C3). rewrite <- EQ in *.
  pose proof t_vs_prim as TP.
  unfold KHIGHMEM_BEG, KREGIONSIZE, KFREEARRAY_OFF, QBATCH_SIZE, QBATCH_CAP, PRIM_RES_SIZE in *.
  change (csize 24) with 8192 in *.
  assert (OBJ : forall a sz, qb_addr b <= a -> a + sz <= qb_addr b + 8192 -> disjoint_from W a sz).
  { intros a sz Ha Hs. eapply (tpz_obj (st_pbase st) (st_pbase st + 0x2000011000)); [lia| lia| lia| unfold CEIL; lia]. }
  split; [| split].
  - apply OBJ; lia.
  - intros i Hi. apply OBJ; lia.
  - pose proof (rt_SH_mono (qb_addr b + 8192) (@CEIL ACEIL) ltac:(unfold CEIL; lia)) as B2. rewrite SH_CEIL in B2.
    assert (AL8 : qb_addr b mod 8 = 0) by (apply (mod0_trans _ 8 32); [lia|lia|reflexivity|exact AL]).
    rewrite rt_SH_aligned_add in B2 by exact AL8. apply tpz_shadow; [clear - C1 X1; shlo|]. unfold KHIGHMEM_BEG. change (8192 / 8) with 1024 in B2. lia.
Qed.

(* [comment removed for export] *)
Lemma TZ_ptrarr : WOK_ptrarr st W.
Proof.
  split.
  - intros i Hi. pose proof (pa_range st WF) as (P1 & P2 & P3 & P4 & P5). pose proof t_vs_pa. unfold KHIGHMEM_BEG, PTRARR_RES_SIZE in *.
    eapply (tpz_obj (st_pa st) (st_pa st + 0x800000)); [lia| lia| lia| unfold CEIL; lia].
  - intros e He. destruct (ws_spend st (wf_sec_ok st WF) e He) as [HE _].
    destruct (ws_entry st (wf_sec_ok st WF) e HE) as (E1 & E2 & E3 & _).
    pose proof (wb_ranges st (wf_base_ok st WF) (fst e, fst e + smapsize (snd e))) as R. cbn [fst snd] in R.
    specialize (R ltac:(unfold rt_ranges; do 2 right; rewrite !in_app_iff; right; left; apply in_map_iff; exists e; auto)).
    destruct e as [mb n]. cbn [fst snd] in *. destruct (sec_facts n E1) as (_ & _ & _ & F4 & _). pose proof (usz_le_rounded8 n) as (U1 & _).
    pose proof (t_vs_sec mb n HE).
    eapply (tpz_obj mb (mb + smapsize n)); [lia| lia| unfold usz in *; lia| unfold CEIL; lia].
Qed.

(* [comment removed for export] *)
Lemma TZ_depot : WOK_depot st W.
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
    { pose proof (wd_nnb st WD) as E. unfold d_nnb in *. rewrite E. subst q. unfold DEPOT_L2_NODES. Z.div_mod_to_equations. nia. }
    assert (Hb : In b (d_nblocks (st_depot st))) by (subst b; apply nthz_In; unfold d_nnb in Hq; exact Hq).
    destruct (nb_range st WF b Hb) as (R1 & R2 & R3). pose proof (t_vs_nb b Hb) as TB.
    assert (ADDR : dnode_addr (st_depot st) id = b + DEPOT_NODE_SZ * (id mod DEPOT_L2_NODES)) by reflexivity.
    rewrite ADDR. unfold DEPOT_NODE_SZ, DEPOT_L2_NODES, NODEBLOCK_SIZE in *.
    eapply (tpz_obj b (b + 1048576)); [lia| Z.div_mod_to_equations; lia| Z.div_mod_to_equations; lia| unfold CEIL; lia].
  - low.
  - intros b Hb. low.
Qed.

(* [comment removed for export] *)
Lemma TZ_fs : WOK_fs st W.
Proof.
  pose proof (fs_range st WF) as (F1 & F2 & F3). unfold KHIGHMEM_BEG in F1. pose proof t_vs_fs as TF.
  assert (OBJ : forall a sz, st_fs st <= a -> a + sz <= st_fs st + FS_TOTAL -> disjoint_from W a sz).
  { intros a sz Ha Hs. eapply (tpz_obj (st_fs st) (st_fs st + FS_TOTAL)); [lia| lia| lia| exact F2]. }
  unfold WOK_fs. split; [| split; [| split; [| split]]].
  - intros k Hk. apply OBJ; unfold FS_TOTAL in *; lia.
  - apply OBJ; unfold FS_TOTAL in *; lia.
  - apply OBJ; unfold FS_TOTAL in *; lia.
  - intros k pos Hk Hp. pose proof (flags_ok k Hk) as [O1 O2]. apply OBJ; unfold fflag_addr, FS_TOTAL in *; lia.
  - intros F k Hin. pose proof (frame_range st WF F k Hin) as (Hk & X & Y & _). unfold FS_FRAMES_OFF, FS_TOTAL in *.
    assert (64 <= fsz k) by (destruct Hk as [-> | ->]; [change (fsz 1) with 128| change (fsz 2) with 256]; lia).
    apply OBJ; unfold FS_TOTAL; lia.
Qed.

(* [comment removed for export] *)
Theorem tpz_others : forall m m', munch W m m' -> wmono asegs m m' -> RTREP st m ->
  R_link m' /\ R_consts st m' /\ R_alloc st m' /\ R_rinfo st m' /\ R_regions st m' /\ R_avail st m' /\ R_thread st m'
  /\ R_live st m' /\ R_quar st m' /\ R_batches st m' /\ R_ptrarr st m' /\ R_depot st m' /\ R_fs st m' /\ R_ia m' /\ R_lowshadow m'.
Proof.
  intros m m' MU WM HR.
  Local Ltac tapp T st WF W m m' MU WM :=
    first [ eapply (T st WF W m m' MU WM) | eapply (T st W m m' MU WM) | eapply (T W m m' MU WM) | eapply (T W m m' MU) ].
  split; [tapp T_link st WF W m m' MU WM; [exact (rr_link st m HR)| exact TZ_link]|].
  split; [tapp T_consts st WF W m m' MU WM; [exact (rr_consts st m HR)| exact TZ_consts]|].
  split; [tapp T_alloc st WF W m m' MU WM; [exact (rr_alloc st m HR)| exact TZ_alloc]|].
  split; [tapp T_rinfo st WF W m m' MU WM; [exact (rr_rinfo st m HR)| exact TZ_rinfo]|].
  split; [tapp T_regions st WF W m m' MU WM; [exact (rr_regions st m HR)| exact TZ_regions]|].
  split; [tapp T_avail st WF W m m' MU WM; [exact (rr_avail st m HR)| exact TZ_avail]|].
  split; [tapp T_thread st WF W m m' MU WM; [exact (rr_thread st m HR)| exact TZ_thread]|].
  split; [tapp T_live st WF W m m' MU WM; [exact (rr_live st m HR)| exact TZ_live]|].
  split; [tapp T_quar st WF W m m' MU WM; [exact (rr_quar st m HR)| exact TZ_quar]|].
  split; [tapp T_batches st WF W m m' MU WM; [exact (rr_batches st m HR)| exact TZ_batches]|].
  split; [tapp T_ptrarr st WF W m m' MU WM; [exact (rr_ptrarr st m HR)| exact TZ_ptrarr]|].
  split; [tapp T_depot st WF W m m' MU WM; [exact (rr_depot st m HR)| exact TZ_depot]|].
  split; [tapp T_fs st WF W m m' MU WM; [exact (rr_fs st m HR)| exact TZ_fs]|].
  split; [tapp T_ia st WF W m m' MU WM; [exact (rr_ia st m HR)| exact TZ_ia]|].
  tapp T_lowshadow st WF W m m' MU WM; [exact (rr_lowshadow st m HR)| exact TZ_lowshadow].
Qed.

(* [comment removed for export] *)
Theorem tpz_transport_cache : forall m m', munch W m m' -> wmono asegs m m' -> RTREP st m ->
  Forall (fun iv : Z * Z => st_t st + T_ACACHE + 2560 <= fst iv \/ CEIL <= fst iv) W ->
  RTREP st m'.
Proof.
  intros m m' MU WM HR HS.
  destruct (tpz_others m m' MU WM HR) as (X1 & X2 & X3 & X4 & X5 & X6 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15 & X16).
  assert (D : forall a sz, a + sz <= st_t st + T_ACACHE + 2560 -> disjoint_from W a sz).
  { intros a sz Ha. pose proof (t_range st WF) as TR. clear - HW HS Ha TR.
    induction W as [|[lo hi] W' IH]; [exact I|].
    pose proof (Forall_inv HW) as A1. pose proof (Forall_inv HS) as A2. cbn [fst snd] in A1, A2. unfold tpz_ok in A1. cbn [fst snd] in A1.
    cbn. split; [unfold T_ACACHE, T_UNWINDING, CEIL, KHIGHMEM_BEG in *; lia|].
    apply IH; [exact (Forall_inv_tail HW)| exact (Forall_inv_tail HS)]. }
  assert (KC : WOK_cache st W).
  { intros c Hc. pose proof (wc_cache_max st c (wf_class_ok st WF c Hc)) as CM. pose proof (cmaxcount_le16 c) as CM16. unfold KNUMCLASSES in Hc.
    split; [apply D; unfold pcaddr, acache; lia|]. intros i Hi. apply D; unfold pcaddr, acache; lia. }
  constructor; try assumption. tapp T_cache st WF W m m' MU WM; [exact (rr_cache st m HR)| exact KC].
Qed.
End TPZ.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CLI.
Variable st : rtstate.
Hypothesis WF : RTWF st.
Variable SP : Z.
Hypothesis HSP : CEIL <= SP.

Lemma tpage_not_client : forall a, st_t st + T_ACACHE <= a < st_t st + 4096 ->
  ~ cj_client_addr (st_sp0 st) (st_lb st) (st_lf st) SP a.
Proof.
  intros a Ha HC. pose proof (t_range st WF) as [T1 T2]. unfold T_ACACHE, KHIGHMEM_BEG, CEIL in *.
  destruct HC as [H|[H|[(A & n & Hb & Hr)|[(F & k & Hb & Hr)|H]]]].
  - lia.
  - unfold aclient_image, AERRNO, AGERROR0, AGERROR1, ADATA_LO, AIMG_HI, ATP in H. blia.
  - assert (HB : In (A, n) (all_blocks st)) by (unfold all_blocks; apply in_or_app; left; exact Hb).
    pose proof (t_vs_block st WF A n HB) as TB.
    pose proof (block_geom st WF A n HB) as (_ & _ & _ & X & Y & _). unfold usz in Y. lia.
  - pose proof (t_vs_fs st WF) as TF. pose proof (frame_range st WF F k Hb) as (Hk & X & Y & _). pose proof (fs_range st WF) as (F1 & F2 & _).
    unfold FS_FRAMES_OFF, KHIGHMEM_BEG in *.
    destruct Hr as [Hr|Hr]; [lia|].
    pose proof (rt_SH_bounds (F + fsz k) ltac:(unfold CEIL in *; blia)) as B.
    pose proof (rt_SH_bounds F ltac:(unfold CEIL in *; blia)) as B0.   (* [comment removed for export] *)
    pose proof (frame_range st WF F k Hb) as (_ & _ & _ & AL). rewrite (rt_SH_aligned_add F (fsz k) AL) in B. clear - Ha Hr B B0 T1. blia.
  - unfold astack_shadow in H. rewrite CEIL_eq, SH_CEIL in H. change (SH (2^47)) with 0x10007fff8000 in H. blia.
Qed.

Lemma below_sp_not_client : forall a, CEIL <= a < SP -> ~ cj_client_addr (st_sp0 st) (st_lb st) (st_lf st) SP a.
Proof.
  intros a Ha HC. unfold CEIL in *.
  destruct HC as [H|[H|[(A & n & Hb & Hr)|[(F & k & Hb & Hr)|H]]]].
  - lia.
  - unfold aclient_image, AERRNO, AGERROR0, AGERROR1, ADATA_LO, AIMG_HI, ATP in H. lia.
  - assert (HB : In (A, n) (all_blocks st)) by (unfold all_blocks; apply in_or_app; left; exact Hb).
    pose proof (block_geom st WF A n HB) as (_ & _ & _ & X & Y & Z6 & _). unfold usz in Y. lia.
  - pose proof (frame_range st WF F k Hb) as (Hk & X & Y & AL). pose proof (fs_range st WF) as (F1 & F2 & _).
    unfold FS_FRAMES_OFF, KHIGHMEM_BEG, CEIL in *.
    destruct Hr as [Hr|Hr]; [lia|].
    pose proof (rt_SH_bounds (F + fsz k) ltac:(blia)) as B. rewrite (rt_SH_aligned_add F (fsz k) AL) in B. lia.
  - unfold astack_shadow in H. rewrite CEIL_eq, SH_CEIL in H. change (SH (2^47)) with 0x10007fff8000 in H. lia.
Qed.

(* [comment removed for export] *)
Lemma cli_pres_tpz : forall W m m',
  munch W m m' -> wmono asegs m m' ->
  Forall (fun iv : Z * Z => (st_t st + T_ACACHE <= fst iv /\ snd iv <= st_t st + 4096) \/ (CEIL <= fst iv /\ snd iv <= SP)) W ->
  cli_pres st SP m m'.
Proof.
  intros W m m' MU WM HW. unfold cli_pres. eapply cj_pres_of_munch; [exact MU| exact WM|].
  intros a Ha HC. clear MU WM. induction W as [|[lo hi] W' IH]; [exact I|].
  pose proof (Forall_inv HW) as A1. cbn [fst snd] in A1. cbn. split; [| apply IH; exact (Forall_inv_tail HW)].
  intros Hin. destruct A1 as [A1|A1].
  - apply (tpage_not_client a); [lia| exact HC].
  - apply (below_sp_not_client a); [lia| exact HC].
Qed.
End CLI.


End CeilWrap.
