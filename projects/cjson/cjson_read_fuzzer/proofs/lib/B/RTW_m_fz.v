(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require PropExec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require MState.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Mem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Cells.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Step.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Frame.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require BImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_wf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_rep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_kit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_art.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_cost.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_fp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_artF.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_primary_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_m_tpz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_bandtac4.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Ceil.
Module RTW_m_lbz.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Mem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Cells OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Frame OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.BImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit.RT_shlem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_cost.RT_artG OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp.RT_artB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_m_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_m_tpz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.ABand OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_bandtac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_bandtac2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_bandtac4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition lbz_ok (st : rtstate) (A n : Z) (iv : Z * Z) : Prop :=
     (b_lo A n <= fst iv /\ snd iv <= b_hi A n)
  \/ (st_t st + T_STATS <= fst iv /\ snd iv <= st_t st + T_UNWINDING)
  \/ CEIL <= fst iv.

Local Ltac ulia := unfold KHIGHMEM_BEG, AIMG_HI, CEIL, KREGIONSIZE, KFREEARRAY_OFF, PRIM_RES_SIZE, PTRARR_RES_SIZE, QBATCH_SIZE in *; first [lia | blia].

(* [comment removed for export] *)
Lemma all_blocks_neq : forall st A n A' n', RTWF st -> In (A, n) (all_blocks st) -> In (A', n') (all_blocks st) ->
  (A', n') <> (A, n) -> A' <> A.
Proof.
  intros st A n A' n' WF H1 H2 NE E. subst A'. apply NE. f_equal.
  pose proof (nodup_map_inj fst _ (A, n') (A, n) (wk_nodup st (wf_blocks_ok st WF)) H2 H1 eq_refl) as EQ. injection EQ. auto.
Qed.

Section LBZ.
Variable st : rtstate.
Hypothesis WF : RTWF st.
Hypothesis HX : tpx_ok st.
Variables (A n : Z).
Hypothesis HB : In (A, n) (all_blocks st).
Variable W : list (Z * Z).
Hypothesis HW : Forall (lbz_ok st A n) W.
Local Abbreviation LO := (b_lo A n).
Local Abbreviation HI := (b_hi A n).
Local Abbreviation t := (st_t st).

Lemma geomB : ablk LO HI /\ LO + 16 <= A /\ A + usz n <= HI /\ HI <= CEIL /\ LO mod 16 = 0.
Proof. pose proof (block_geom st WF A n HB) as (_ & _ & G1 & G2 & G3 & G4 & G5 & _). unfold CEIL. repeat split; try lia; assumption. Qed.

Lemma lbz_disj : forall a sz,
  (a + sz <= LO \/ HI <= a) -> (a + sz <= t + T_STATS \/ (t + T_UNWINDING <= a /\ a + sz <= CEIL)) ->
  disjoint_from W a sz.
Proof.
  intros a sz H1 H3. pose proof (t_range st WF) as TR. induction W as [|[lo hi] W' IH]; [exact I|].
  pose proof (Forall_inv HW) as A1. unfold lbz_ok in A1. cbn [fst snd] in A1. cbn.
  split; [unfold T_STATS, T_UNWINDING, CEIL, KHIGHMEM_BEG, AIMG_HI in *; lia| apply IH; exact (Forall_inv_tail HW)].
Qed.

(* [comment removed for export] *)
Lemma lbz_low : forall a sz, AIMG_LO <= a -> a + sz <= KHIGHMEM_BEG -> (a + sz <= AIMG_HI \/ KLOWSHADOW_BEG <= a) -> disjoint_from W a sz.
Proof.
  intros a sz H0 H1 HZ. pose proof geomB as (G1 & _). pose proof (t_range st WF) as [TR _].
  apply lbz_disj; [clear - H0 H1 HZ G1; blia| unfold T_STATS, T_UNWINDING, CEIL in *; clear - H0 H1 HZ TR; blia].
Qed.
Lemma lbz_img : forall a sz, AIMG_LO <= a -> a + sz <= AIMG_HI -> disjoint_from W a sz.
Proof. intros a sz H0 H. apply lbz_low; unfold AIMG_LO, AIMG_HI, KHIGHMEM_BEG in *; lia. Qed.
Local Ltac img := apply lbz_img; unfold AIMG_LO, AIMG_HI; cbn -[Z.add Z.mul Z.le Z.lt Z.sub]; lia.
Lemma lbz_shad : forall a sz, KLOWSHADOW_BEG <= a -> a + sz <= SH CEIL -> disjoint_from W a sz.
Proof. intros a sz H0 H. rewrite SH_CEIL in H. apply lbz_low; unfold KHIGHMEM_BEG, AIMG_LO, AIMG_HI, KLOWSHADOW_BEG in *; lia. Qed.
(* [comment removed for export] *)
Local Ltac shlow := lazymatch goal with |- KLOWSHADOW_BEG <= SH ?x => let M := fresh "M0" in pose proof (rt_SH_mono 0 x ltac:(ulia)) as M; change (SH 0) with 0x7fff8000 in M; unfold KLOWSHADOW_BEG; lia end.

(* [comment removed for export] *)
Lemma lbz_obj : forall lo hi a sz, (hi <= LO \/ HI <= lo) -> (hi <= t \/ t + 4096 <= lo) ->
  hi <= CEIL -> lo <= a -> a + sz <= hi -> disjoint_from W a sz.
Proof.
  intros lo hi a sz D1 D2 K2 Ha Hs. apply lbz_disj; [lia| unfold T_STATS, T_UNWINDING; lia].
Qed.
(* [comment removed for export] *)
Lemma lbz_bf : forall lo hi a sz, blockfree st lo hi -> (hi <= t \/ t + 4096 <= lo) ->
  hi <= CEIL -> lo <= a -> a + sz <= hi -> disjoint_from W a sz.
Proof.
  intros lo hi a sz BF D2 K2 Ha Hs. eapply (lbz_obj lo hi); [destruct (BF A n HB); lia| exact D2| exact K2| exact Ha| exact Hs].
Qed.

(* [comment removed for export] *)
Lemma LZ_link : WOK_link W.
Proof. split; [intros a v Hin; destruct (alink_range a v Hin); img| unfold A_GLOBREC_LO, A_GLOBREC_HI; img]. Qed.
Lemma LZ_consts : WOK_consts W.
Proof.
  unfold WOK_consts.
  unfold A_SHADOW_OFF_CELL, A_UAR_OPTION, A_AFLAGS, A_CFLAGS, A_PAGESIZE_CACHED, A_KHIGHMEMEND, A_KMIDMEMBEG, A_KMIDMEMEND,
    A_ASAN_INITED, A_MCS, A_CAN_POISON, A_TSD_KEY_INITED, A_TSD_KEY, A_MAY_RETURN_NULL, A_ALLOC_OOM, A_DYING, A_VERBOSITY,
    A_MFHOOKS, A_LSAN_DISABLE, A_IA_INITED, AHOOKS, A_LIBC_PAGESIZE, A_MU_GLOBALS, A_GLOBALS_REGD, A_TPCG_INITED, A_TOOLNAME, A_PRINTF_CB, A_EMB, ATP.
  repeat lazymatch goal with |- _ /\ _ => split | _ => idtac end; img.
Qed.
Lemma LZ_alloc : WOK_alloc W.
Proof.
  unfold WOK_alloc, A_ALLOC, A_SECONDARY, A_GSTATS, A_QUAR, A_MAXUSERSZ, A_ALLOC.
  repeat lazymatch goal with |- _ /\ _ => split | _ => idtac end; img.
Qed.
Lemma LZ_ia : WOK_ia W.
Proof. intros i Hi. unfold A_IA_MAP1. img. Qed.
Lemma LZ_lowshadow : WOK_lowshadow W.
Proof.
  intros g Hg. change (SH AIMG_LO) with 0x7fffa000 in Hg. change (SH AIMG_HI) with 0x800b7e00 in Hg. apply lbz_low; unfold KHIGHMEM_BEG, AIMG_LO, AIMG_HI, KLOWSHADOW_BEG; lia.
Qed.
Lemma LZ_avail : WOK_avail st W.
Proof.
  intros c' k' Hc' Hin. pose proof (region_facts st WF c' Hc') as RF. cbn zeta in RF. destruct RF as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10).
  assert (CV : carved_cptr st c' k').
  { apply (wc_used_carved st c' (wf_class_ok st WF c' Hc')). unfold used_cptrs. rewrite !in_app_iff. apply in_app_iff in Hin. tauto. }
  destruct (Z.eq_dec c' 0) as [->|NZ].
  { exfalso. unfold avail_cptrs in Hin. pose proof (wb_class0 st (wf_base_ok st WF)) as [E1 E2]. rewrite E1, E2 in Hin. cbn in Hin.
    unfold apend_cptrs in Hin. apply in_map_iff in Hin as ([c'' k''] & _ & Hf). apply filter_In in Hf as [Hin Hb]. cbn [fst] in Hb.
    apply Z.eqb_eq in Hb. subst c''. pose proof (wq_apend st (wf_quar_ok st WF) _ Hin). cbn [fst] in *. lia. }
  destruct (carved_chunk st WF c' k' Hc' ltac:(lia) CV) as (C1 & C2 & C3). pose proof (csize_pos c' ltac:(unfold KNUMCLASSES in Hc'; lia)).
  pose proof (csize_mod32 c' ltac:(unfold KNUMCLASSES in Hc'; lia)) as SM.
  assert (AL : cptr_addr st c' k' mod 8 = 0).
  { apply (mod0_of_sub _ (rbeg st c') 8 ltac:(lia)); [| exact X8]. apply (mod0_trans _ 8 (csize c')); [lia|lia| apply (mod0_trans _ 8 32); [lia|lia|reflexivity|exact SM]| exact C3]. }
  apply lbz_shad; [shlow|]. pose proof (rt_SH_mono (cptr_addr st c' k' + csize c') (@CEIL ACEIL) ltac:(ulia)) as M.
  rewrite rt_SH_aligned_add in M by exact AL. lia.
Qed.

(* [comment removed for export] *)
Lemma LZ_rinfo : WOK_rinfo st W.
Proof.
  intros c' Hc'. pose proof (ris_range st WF) as (X1 & X2 & X3 & X4). pose proof (t_vs_prim st WF) as TP. unfold KNUMCLASSES in Hc'.
  eapply (lbz_bf (ris st) (ris st + 4096)); [apply ris_blockfree; exact WF| ulia| ulia| unfold rinfo; lia| unfold rinfo; lia].
Qed.
Lemma LZ_regions : WOK_regions st W.
Proof.
  intros c' Hc'. pose proof (region_facts st WF c' Hc') as RF. cbn zeta in RF. destruct RF as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10).
  assert (FB : fabeg st c' = rbeg st c' + KFREEARRAY_OFF) by reflexivity. pose proof (t_vs_prim st WF) as TP.
  split.
  - intros i Hi. pose proof (wc_num_freed st c' (wf_class_ok st WF c' Hc')) as NF.
    eapply (lbz_bf (fabeg st c') (fabeg st c' + r_mapped_fa (rg st c'))); [apply fa_blockfree; [exact WF| exact Hc']| | | |];
      unfold KFREEARRAY_SIZE in *; ulia.
  - apply lbz_shad; [shlow|]. pose proof (rt_SH_mono (rbeg st c' + r_mapped (rg st c')) (@CEIL ACEIL) ltac:(ulia)) as M.
    rewrite !rt_SH_aligned_add in * by exact X8. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma LZ_cache : WOK_cache st W.
Proof.
  intros c' Hc'. pose proof (wc_cache_max st c' (wf_class_ok st WF c' Hc')) as CM. pose proof (cmaxcount_le16 c'). unfold KNUMCLASSES in Hc'.
  pose proof (t_range st WF) as [T1 T2]. pose proof (t_vs_block st WF A n HB) as TC.
  assert (D : forall a sz, t + T_ACACHE <= a -> a + sz <= t + T_ACACHE + 2560 -> disjoint_from W a sz).
  { intros a sz H1 H2. apply lbz_disj; unfold T_ACACHE, T_STATS, CEIL in *; lia. }
  split; [apply D; unfold pcaddr, acache; lia|]. intros i Hi. apply D; unfold pcaddr, acache; lia.
Qed.
Lemma LZ_thread : WOK_thread st W.
Proof.
  pose proof (t_range st WF) as [T1 T2]. pose proof (t_vs_block st WF A n HB) as TC. unfold WOK_thread.
  split; [apply lbz_disj; unfold T_STATS, CEIL in *; lia|].
  split; [apply lbz_disj; unfold qcache_t, T_QCACHE, T_STATS, CEIL in *; lia|].
  split; [apply lbz_disj; unfold T_UNWINDING, T_STATS, CEIL in *; lia|].
  destruct HX as [CX DX].
  destruct (wb_ctx_loose st (wf_base_ok st WF)) as (cb & ck & CL1 & CL2 & CL3). destruct (loose0_range st WF _ _ CL1) as (R1 & R2 & R3 & R4).
  pose proof (loose_blockfree st WF cb ck CL1 A n HB) as LB.
  split; [eapply (lbz_obj (st_ctx st) (st_ctx st + 160)); [lia| exact CX| unfold CEIL in *; lia| unfold CTX_TID; lia| unfold CTX_TID; lia]|].
  split; [eapply (lbz_obj (st_ctx st) (st_ctx st + 160)); [lia| exact CX| unfold CEIL in *; lia| unfold CTX_THREAD; lia| unfold CTX_THREAD; lia]|].
  unfold A_TSD_PTR, A_TSD_MAIN, A_DTV_PTR, A_DTV, A_TLSMOD, A_FSTLS_CELL, A_DTLS_OFF, ATP in *.
  split; [img|]. split; [img|]. split; [img|]. split; [img|]. split; [img|]. split; [img|].
  destruct (wb_dtls_loose st (wf_base_ok st WF)) as (db & dk & DL1 & DL2 & DL3). destruct (loose0_range st WF _ _ DL1) as (Q1 & Q2 & Q3 & Q4).
  pose proof (loose_blockfree st WF db dk DL1 A n HB) as LD.
  eapply (lbz_obj (tl_dtls_block (st_tls st) + 24) (tl_dtls_block (st_tls st) + 32)); [lia| exact DX| unfold CEIL in *; lia| lia| lia].
Qed.

(* [comment removed for export] *)
Lemma LZ_block_other : forall A' n', In (A', n') (all_blocks st) -> A' <> A -> WOK_block W A' n'.
Proof.
  intros A' n' HB' NE.
  pose proof (block_geom st WF A' n' HB') as (Gn & GA & K & X & Y & CE & L16 & H16 & EA & Gp & Gs). unfold usz in Y.
  pose proof (t_vs_block st WF A' n' HB') as TB. pose proof (blocks_disj st WF A' n' A n HB' HB NE) as CB.
  pose proof (rz_size_range n') as (Z1 & Z2).
  assert (OBJ : forall a sz, b_lo A' n' <= a -> a + sz <= b_hi A' n' -> disjoint_from W a sz).
  { intros a sz Ha Hs. eapply (lbz_obj (b_lo A' n') (b_hi A' n')); [lia| lia| ulia| exact Ha| exact Hs]. }
  assert (RZA : b_lo A' n' + rz_size n' <= A').
  { rewrite EA at 2. unfold sh_left, SEC_HDR, SEC_RZ. destruct (bprim n') eqn:EP.
    + Z.div_mod_to_equations. lia.
    + destruct (sec_facts n' EP) as (_ & F2 & _). rewrite F2. cbn. lia. }
  split; [|split; [|split]].
  - apply OBJ; unfold b_chunk_beg; lia.
  - intros HRZ. apply OBJ; unfold b_alloc_beg; lia.
  - intros EP. apply OBJ; unfold b_lo in *; rewrite EP in *; unfold b_map_beg, SEC_HDR, SEC_RZ in *; lia.
  - apply lbz_shad; [shlow|]. pose proof (rt_SH_mono (b_hi A' n') (@CEIL ACEIL) ltac:(ulia)) as M.
    assert (L8 : b_lo A' n' mod 8 = 0) by (apply (mod0_trans _ 8 16); [lia|lia|reflexivity|exact L16]).
    assert (EH : b_hi A' n' = b_lo A' n' + asz n') by reflexivity. rewrite EH, rt_SH_aligned_add in M by exact L8.
    unfold sh_tot. lia.
Qed.
(* [comment removed for export] *)
Lemma LZ_block_self_shadow : disjoint_from W (SH LO) (sh_tot n).
Proof.
  pose proof (block_geom st WF A n HB) as (Gn & GA & K & X & Y & CE & L16 & H16 & _).
  apply lbz_shad; [shlow|]. pose proof (rt_SH_mono HI (@CEIL ACEIL) ltac:(ulia)) as M.
  assert (L8 : LO mod 8 = 0) by (apply (mod0_trans _ 8 16); [lia|lia|reflexivity|exact L16]).
  assert (EH : HI = LO + asz n) by reflexivity. rewrite EH, rt_SH_aligned_add in M by exact L8. unfold sh_tot. lia.
Qed.

(* [comment removed for export] *)
Lemma LZ_batches : WOK_batches st W.
Proof.
  intros b Hb. destruct (batch_geom st WF b Hb) as (BB & BF & R1 & R2 & AL).
  destruct (wq_batch st (wf_quar_ok st WF) b Hb) as [CNT _].
  pose proof (region_facts st WF 24 ltac:(unfold KNUMCLASSES; lia)) as RF. cbn zeta in RF. destruct RF as (X1 & X2 & X3 & X4 & X5 & X6 & _).
  assert (TB : qb_addr b + QBATCH_SIZE <= t \/ t + 4096 <= qb_addr b) by (pose proof (t_vs_prim st WF); ulia).
  assert (OBJ : forall a sz, qb_addr b <= a -> a + sz <= qb_addr b + QBATCH_SIZE -> disjoint_from W a sz).
  { intros a sz Ha Hs. eapply (lbz_bf (qb_addr b) (qb_addr b + QBATCH_SIZE)); [exact BB| exact TB| ulia| exact Ha| exact Hs]. }
  unfold QBATCH_SIZE, QBATCH_CAP in *.
  split; [| split].
  - apply OBJ; lia.
  - intros i Hi. apply OBJ; lia.
  - apply lbz_shad; [shlow|]. assert (AL8 : qb_addr b mod 8 = 0) by (apply (mod0_trans _ 8 32); [lia|lia|reflexivity|exact AL]).
    pose proof (rt_SH_mono (qb_addr b + 8192) (@CEIL ACEIL) ltac:(ulia)) as M. rewrite rt_SH_aligned_add in M by exact AL8. change (8192 / 8) with 1024 in M. lia.
Qed.
Lemma LZ_ptrarr : WOK_ptrarr st W.
Proof.
  split.
  - intros i Hi. pose proof (pa_range st WF) as (P1 & P2 & P3 & P4 & P5). pose proof (t_vs_pa st WF).
    eapply (lbz_bf (st_pa st) (st_pa st + PTRARR_RES_SIZE)); [apply pa_blockfree; exact WF| | | |]; ulia.
  - intros e He. pose proof (spend_blockfree st WF e He) as BF. destruct (ws_spend st (wf_sec_ok st WF) e He) as [HE _].
    destruct (ws_entry st (wf_sec_ok st WF) e HE) as (E1 & E2 & E3 & _).
    pose proof (wb_ranges st (wf_base_ok st WF) (fst e, fst e + smapsize (snd e))) as R. cbn [fst snd] in R.
    specialize (R ltac:(unfold rt_ranges; do 2 right; rewrite !in_app_iff; right; left; apply in_map_iff; exists e; auto)).
    destruct e as [mb k]. cbn [fst snd] in *. destruct (sec_facts k E1) as (_ & _ & _ & F4 & _). pose proof (t_vs_sec st WF mb k HE).
    eapply (lbz_bf mb (mb + smapsize k)); [exact BF| | | |]; unfold usz in *; ulia.
Qed.
Lemma LZ_depot : WOK_depot st W.
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
    destruct (nb_range st WF b Hb) as (R1 & R2 & R3). pose proof (t_vs_nb st WF b Hb) as TB. destruct (nb_blockfree st WF b Hb) as [NB _].
    assert (ADDR : dnode_addr (st_depot st) id = b + DEPOT_NODE_SZ * (id mod DEPOT_L2_NODES)) by reflexivity.
    rewrite ADDR. unfold DEPOT_NODE_SZ, DEPOT_L2_NODES, NODEBLOCK_SIZE in *.
    eapply (lbz_bf b (b + 1048576)); [exact NB| ulia| ulia| Z.div_mod_to_equations; lia| Z.div_mod_to_equations; lia].
  - img.
  - intros b Hb. img.
Qed.
Lemma LZ_fs : WOK_fs st W.
Proof.
  pose proof (fs_range st WF) as (F1 & F2 & F3). pose proof (t_vs_fs st WF) as TF.
  pose proof (loose_blockfree st WF _ _ (wb_fs_loose st (wf_base_ok st WF))) as CF.
  assert (OBJ : forall a sz, st_fs st <= a -> a + sz <= st_fs st + FS_TOTAL -> disjoint_from W a sz).
  { intros a sz Ha Hs. eapply (lbz_bf (st_fs st) (st_fs st + FS_TOTAL)); [exact CF| ulia| exact F2| exact Ha| exact Hs]. }
  unfold WOK_fs. split; [| split; [| split; [| split]]].
  - intros k' Hk. apply OBJ; unfold FS_TOTAL in *; lia.
  - apply OBJ; unfold FS_TOTAL in *; lia.
  - apply OBJ; unfold FS_TOTAL in *; lia.
  - intros k' pos Hk Hp. pose proof (flags_ok k' Hk) as [O1 O2]. apply OBJ; unfold fflag_addr, FS_TOTAL in *; lia.
  - intros F k' Hin. pose proof (frame_range st WF F k' Hin) as (Hk & X & Y & _). change FS_FRAMES_OFF with 36864 in X. unfold FS_TOTAL in *.
    assert (64 <= fsz k') by (destruct Hk as [-> | ->]; [change (fsz 1) with 128| change (fsz 2) with 256]; lia).
    apply OBJ; unfold FS_TOTAL; lia.
Qed.

(* [comment removed for export] *)
Theorem lbz_others : forall m m', munch W m m' -> wmono bsegs m m' -> RTREP st m ->
  R_link m' /\ R_consts st m' /\ R_alloc st m' /\ R_rinfo st m' /\ R_regions st m' /\ R_avail st m' /\ R_cache st m' /\ R_thread st m'
  /\ R_batches st m' /\ R_ptrarr st m' /\ R_depot st m' /\ R_fs st m' /\ R_ia m' /\ R_lowshadow m'
  /\ (forall md A' n', In (A', n') (all_blocks st) -> R_block st m md A' n' -> (A' <> A \/ WOK_block W A' n') -> R_block st m' md A' n').
Proof.
  intros m m' MU WM HR.
  Local Ltac tapp T st WF W m m' MU WM :=
    first [ eapply (T st WF W m m' MU WM) | eapply (T st W m m' MU WM) | eapply (T W m m' MU WM) | eapply (T W m m' MU) ].
  split; [tapp T_link st WF W m m' MU WM; [exact (rr_link st m HR)| exact LZ_link]|].
  split; [tapp T_consts st WF W m m' MU WM; [exact (rr_consts st m HR)| exact LZ_consts]|].
  split; [tapp T_alloc st WF W m m' MU WM; [exact (rr_alloc st m HR)| exact LZ_alloc]|].
  split; [tapp T_rinfo st WF W m m' MU WM; [exact (rr_rinfo st m HR)| exact LZ_rinfo]|].
  split; [tapp T_regions st WF W m m' MU WM; [exact (rr_regions st m HR)| exact LZ_regions]|].
  split; [tapp T_avail st WF W m m' MU WM; [exact (rr_avail st m HR)| exact LZ_avail]|].
  split; [tapp T_cache st WF W m m' MU WM; [exact (rr_cache st m HR)| exact LZ_cache]|].
  split; [tapp T_thread st WF W m m' MU WM; [exact (rr_thread st m HR)| exact LZ_thread]|].
  split; [tapp T_batches st WF W m m' MU WM; [exact (rr_batches st m HR)| exact LZ_batches]|].
  split; [tapp T_ptrarr st WF W m m' MU WM; [exact (rr_ptrarr st m HR)| exact LZ_ptrarr]|].
  split; [tapp T_depot st WF W m m' MU WM; [exact (rr_depot st m HR)| exact LZ_depot]|].
  split; [tapp T_fs st WF W m m' MU WM; [exact (rr_fs st m HR)| exact LZ_fs]|].
  split; [tapp T_ia st WF W m m' MU WM; [exact (rr_ia st m HR)| exact LZ_ia]|].
  split; [tapp T_lowshadow st WF W m m' MU WM; [exact (rr_lowshadow st m HR)| exact LZ_lowshadow]|].
  intros md A' n' HB' RB HD. eapply (T_block st WF W m m' MU WM); [exact HB'| exact RB|].
  destruct HD as [NE|K]; [apply LZ_block_other; [exact HB'| exact NE]| exact K].
Qed.

(* [comment removed for export] *)
Theorem lbz_all : forall m m', munch W m m' -> wmono bsegs m m' -> RTREP st m -> WOK_block W A n -> RTREP st m'.
Proof.
  intros m m' MU WM HR K.
  destruct (lbz_others m m' MU WM HR) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & XB).
  assert (BL : forall md A' n', In (A', n') (all_blocks st) -> R_block st m md A' n' -> R_block st m' md A' n').
  { intros md A' n' HB' RB. destruct (Z.eq_dec A' A) as [->|NE].
    - pose proof (nodup_map_inj fst _ (A, n') (A, n) (wk_nodup st (wf_blocks_ok st WF)) HB' HB eq_refl) as EQ. injection EQ as ->.
      apply XB; [exact HB'| exact RB| right; exact K].
    - apply XB; [exact HB'| exact RB| left; exact NE]. }
  constructor; try assumption.
  - intros A' n' Hin. apply BL; [unfold all_blocks; apply in_or_app; left; exact Hin| exact (rr_live st m HR A' n' Hin)].
  - split.
    + intros A' n' Hin. apply BL; [unfold all_blocks; rewrite !in_app_iff; right; left; exact Hin| exact (proj1 (rr_quar st m HR) A' n' Hin)].
    + intros A' n' Hin. apply BL; [unfold all_blocks; rewrite !in_app_iff; right; right; exact Hin| exact (proj2 (rr_quar st m HR) A' n' Hin)].
Qed.
End LBZ.


End CeilWrap.
End RTW_m_lbz.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
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
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_depot_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_malloc_leaves_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_m_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RTW_m_tpz.
Import RTW_m_lbz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_sec_dstateP.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_sec_dstateP.RT_trans.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.ABand.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RT_bandtac4.
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
Lemma set_ia_same : forall st,
  st_sp0 (set_ia_inited st) = st_sp0 st /\ st_lb (set_ia_inited st) = st_lb st /\ st_lf (set_ia_inited st) = st_lf st
  /\ st_trs (set_ia_inited st) = st_trs st /\ st_t (set_ia_inited st) = st_t st /\ st_ctx (set_ia_inited st) = st_ctx st
  /\ st_qpend (set_ia_inited st) = st_qpend st /\ st_qtmp (set_ia_inited st) = st_qtmp st /\ st_qcur (set_ia_inited st) = st_qcur st
  /\ st_apend (set_ia_inited st) = st_apend st /\ st_spend (set_ia_inited st) = st_spend st /\ st_sec (set_ia_inited st) = st_sec st
  /\ st_qthread (set_ia_inited st) = st_qthread st /\ st_depot (set_ia_inited st) = st_depot st /\ st_fs (set_ia_inited st) = st_fs st
  /\ st_pa (set_ia_inited st) = st_pa st /\ st_spacebeg (set_ia_inited st) = st_spacebeg st /\ st_pbase (set_ia_inited st) = st_pbase st.
Proof. intros st. destruct st. cbn. repeat (split; [reflexivity|]). reflexivity. Qed.

Lemma RTWF_ia' : forall st, RTWF st -> RTWF (set_ia_inited st).
Proof.
  intros st WF. destruct st. cbn. constructor.
  - destruct (wf_base_ok _ WF); constructor; assumption.
  - intros c' Hc'. destruct (wf_class_ok _ WF c' Hc'); constructor; assumption.
  - destruct (wf_blocks_ok _ WF); constructor; assumption.
  - destruct (wf_sec_ok _ WF); constructor; assumption.
  - destruct (wf_quar_ok _ WF); constructor; assumption.
  - destruct (wf_depot_ok _ WF); constructor; assumption.
  - destruct (wf_fs_ok _ WF); constructor; assumption.
Qed.
Lemma rt_prov_ia' : forall st, rt_prov (set_ia_inited st) = rt_prov st.
Proof.
  intros st. destruct st. cbn [set_ia_inited].
  match goal with |- rt_prov ?X = rt_prov ?Y => set (stI := X); set (st := Y) end.
  assert (E1 : prov_classes stI = prov_classes st) by reflexivity.
  assert (E2 : prov_nb stI = prov_nb st) by reflexivity.
  assert (E3 : prov_q stI = prov_q st) by reflexivity.
  assert (E4 : prov_ptr stI = prov_ptr st) by reflexivity.
  assert (E5 : prov_live stI = prov_live st) by reflexivity.
  assert (E6 : prov_quar stI = prov_quar st) by reflexivity.
  assert (E7 : prov_depot stI = prov_depot st) by reflexivity.
  assert (E8 : prov_slots stI = prov_slots st) by reflexivity.
  unfold rt_prov. rewrite E1, E2, E3, E4, E5, E6, E7, E8. reflexivity.
Qed.
Lemma RTMODEL_ia' : forall st mo, RTMODEL st mo -> RTMODEL (set_ia_inited st) mo.
Proof. intros st mo H. destruct st. exact H. Qed.
Lemma SWIN_ia' : forall st g, SWIN st g -> SWIN (set_ia_inited st) g.
Proof. intros st g H. destruct st. exact H. Qed.
Lemma GWIN_ia' : forall st m mo g, GWIN st m mo g -> GWIN (set_ia_inited st) m mo g.
Proof. intros st m mo g H. destruct st. exact H. Qed.
Lemma tpx_ia' : forall st, tpx_ok st -> tpx_ok (set_ia_inited st).
Proof. intros st H. destruct st. exact H. Qed.
Lemma all_blocks_ia' : forall st, all_blocks (set_ia_inited st) = all_blocks st.
Proof. intros st. destruct st. reflexivity. Qed.
Lemma qcache_t_ia' : forall st, qcache_t (set_ia_inited st) = qcache_t st /\ acache (set_ia_inited st) = acache st.
Proof. intros st. destruct st. split; reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition st_freeP (st : rtstate) (A n : Z) : rtstate :=
  match st with
  | mkRT a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 LB AP SP QP b4 b5 =>
    mkRT a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 (remove_first ck_eqb (A, n) LB) AP SP ((A, n) :: QP) b4 b5
  end.

Lemma st_freeP_same : forall st A n,
  st_sp0 (st_freeP st A n) = st_sp0 st /\ st_lb (st_freeP st A n) = remove_first ck_eqb (A, n) (st_lb st) /\ st_lf (st_freeP st A n) = st_lf st
  /\ st_trs (st_freeP st A n) = st_trs st /\ st_apend (st_freeP st A n) = st_apend st
  /\ st_spend (st_freeP st A n) = st_spend st /\ st_sec (st_freeP st A n) = st_sec st
  /\ st_qpend (st_freeP st A n) = (A, n) :: st_qpend st /\ st_qtmp (st_freeP st A n) = st_qtmp st /\ st_qcur (st_freeP st A n) = st_qcur st
  /\ st_qthread (st_freeP st A n) = st_qthread st /\ st_qglobal (st_freeP st A n) = st_qglobal st /\ st_depot (st_freeP st A n) = st_depot st
  /\ st_fs (st_freeP st A n) = st_fs st /\ st_t (st_freeP st A n) = st_t st /\ st_spacebeg (st_freeP st A n) = st_spacebeg st
  /\ st_pbase (st_freeP st A n) = st_pbase st /\ st_pa (st_freeP st A n) = st_pa st
  /\ st_ctx (st_freeP st A n) = st_ctx st /\ st_tls (st_freeP st A n) = st_tls st /\ st_cache_inited (st_freeP st A n) = st_cache_inited st
  /\ st_regions (st_freeP st A n) = st_regions st /\ st_nreserved (st_freeP st A n) = st_nreserved st
  /\ st_trs0 (st_freeP st A n) = st_trs0 st /\ st_hints (st_freeP st A n) = st_hints st /\ st_loose0 (st_freeP st A n) = st_loose0 st
  /\ st_ia_inited (st_freeP st A n) = st_ia_inited st /\ st_cache (st_freeP st A n) = st_cache st.
Proof. intros st A n. destruct st. cbn. repeat (split; [reflexivity|]). reflexivity. Qed.

Lemma qcache_t_freeP' : forall st A n, qcache_t (st_freeP st A n) = qcache_t st /\ acache (st_freeP st A n) = acache st.
Proof. intros st A n. destruct st. split; reflexivity. Qed.

Lemma RTWF_freeP' : forall st A n, RTWF st -> In (A, n) (st_lb st) -> st_qpend st = [] -> RTWF (st_freeP st A n).
Proof. intros st A n WF HIN HQP. destruct st. eapply RTWF_free; eauto. Qed.
Lemma rt_prov_freeP' : forall st A n, In (A, n) (st_lb st) -> rt_prov (st_freeP st A n) = rt_prov st - fp n - (if is_cl24 n then CL24_TAX else 0).
Proof. intros st A n HIN. destruct st. eapply rt_prov_free; eauto. Qed.
Lemma RTMODEL_freeP' : forall st A n mo, RTMODEL st mo -> RTMODEL (st_freeP st A n) mo.
Proof. intros st A n mo H. destruct st. exact H. Qed.
Lemma SWIN_freeP' : forall st A n g, SWIN st g -> SWIN (st_freeP st A n) g.
Proof. intros st A n g H. destruct st. exact H. Qed.
Lemma GWIN_freeP' : forall st A n m mo g, GWIN st m mo g -> GWIN (st_freeP st A n) m mo g.
Proof. intros st A n m mo g H. destruct st. exact H. Qed.
Lemma tpx_freeP' : forall st A n, tpx_ok st -> tpx_ok (st_freeP st A n).
Proof. intros st A n H. destruct st. exact H. Qed.
Lemma all_blocks_freeP' : forall st A n, In (A, n) (st_lb st) -> Permutation (all_blocks st) (all_blocks (st_freeP st A n)).
Proof. intros st A n HIN. destruct st. eapply free_all_blocks. exact HIN. Qed.

(* [comment removed for export] *)
Lemma nodup_fst_app3 : forall (l1 l2 l3 : list (Z * Z)) x y,
  List.NoDup (map fst (l1 ++ l2 ++ l3)) ->
  ((In x l1 /\ (In y l2 \/ In y l3)) \/ (In x l2 /\ In y l3)) -> fst x <> fst y.
Proof.
  intros l1 l2 l3 x y ND H E.
  rewrite !map_app in ND.
  assert (D12 : forall u v, In u (map fst l1) -> In v (map fst l2 ++ map fst l3) -> u <> v).
  { intros u v Hu Hv ->. exact (nodup_app_disj _ _ v ND Hu Hv). }
  apply NoDup_app_remove_l in ND.
  assert (D23 : forall u v, In u (map fst l2) -> In v (map fst l3) -> u <> v).
  { intros u v Hu Hv ->. exact (nodup_app_disj _ _ v ND Hu Hv). }
  destruct H as [[Hx Hy]|[Hx Hy]].
  - apply (D12 (fst x) (fst y)); [apply in_map; exact Hx| apply in_or_app; destruct Hy; [left|right]; apply in_map; assumption| exact E].
  - apply (D23 (fst x) (fst y)); [apply in_map; exact Hx| apply in_map; exact Hy| exact E].
Qed.

(* [comment removed for export] *)
Lemma lb_vs_rest : forall st A n A' n', RTWF st -> In (A, n) (st_lb st) ->
  (In (A', n') (qelems st) \/ In (A', n') (st_qpend st)) -> A' <> A.
Proof.
  intros st A n A' n' WF HIN H E.
  apply (nodup_fst_app3 (st_lb st) (qelems st) (st_qpend st) (A, n) (A', n')); [exact (wk_nodup st (wf_blocks_ok st WF))| left; split; [exact HIN| exact H]| cbn; congruence].
Qed.
Lemma lb_remove_other : forall st A n A' n', RTWF st -> In (A, n) (st_lb st) ->
  In (A', n') (remove_first ck_eqb (A, n) (st_lb st)) -> A' <> A /\ In (A', n') (st_lb st).
Proof.
  intros st A n A' n' WF HIN H. pose proof (remove_first_In _ _ _ _ H) as H0. split; [| exact H0].
  intros ->. pose proof (wk_nodup st (wf_blocks_ok st WF)) as ND. unfold all_blocks in ND. rewrite map_app in ND. apply NoDup_app_remove_r in ND.
  pose proof (nodup_map_inj fst _ (A, n') (A, n) ND H0 HIN eq_refl) as EQ. injection EQ as ->.
  apply (remove_first_nodup_notin (A, n) (st_lb st)); [| exact H].
  eapply NoDup_map_inv. exact ND.
Qed.

(* [comment removed for export] *)
Lemma cb_remove_first : forall st A n, RTWF st -> In (A, n) (st_lb st) -> cb_remove A (st_lb st) = remove_first ck_eqb (A, n) (st_lb st).
Proof.
  intros st A n WF HIN. pose proof (wk_nodup st (wf_blocks_ok st WF)) as ND. unfold all_blocks in ND. rewrite map_app in ND. apply NoDup_app_remove_r in ND.
  revert ND HIN. generalize (st_lb st) as l. induction l as [|[B k] l IH]; intros ND HIN; [destruct HIN|].
  cbn. unfold ck_eqb at 1. cbn [fst snd]. cbn [map fst] in ND. inversion ND as [|B' l' Hni ND']; subst.
  destruct HIN as [E|HIN].
  - injection E as -> ->. rewrite !Z.eqb_refl. reflexivity.
  - destruct (Z.eqb_spec B A) as [->|NE].
    + exfalso. apply Hni. apply in_map_iff. exists (A, n). auto.
    + rewrite (proj2 (Z.eqb_neq A B) ltac:(congruence)). cbn [andb]. f_equal. apply IH; [exact ND'| exact HIN].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section FREEM.
Variable st : rtstate.
Hypothesis WF : RTWF st.
Hypothesis HX : tpx_ok st.
Variables (A n : Z).
Hypothesis HIN : In (A, n) (st_lb st).
Let stF := st_freeP st A n.

Lemma freeM_HB : In (A, n) (all_blocks st).
Proof. unfold all_blocks. apply in_or_app. left. exact HIN. Qed.

(* [comment removed for export] *)
Lemma R_block_freeP : forall m md A' n', R_block st m md A' n' -> R_block stF m md A' n'.
Proof. intros m md A' n' H. unfold stF, st_freeP. destruct st. exact H. Qed.

Theorem RTREP_freeP' : forall W m m',
  Forall (lbz_ok st A n) W -> munch W m m' -> wmono bsegs m m' -> RTREP st m ->
  R_block st m' BPend A n ->
  RTREP stF m'.
Proof.
  intros W m m' HW MU WM HR HB.
  destruct (lbz_others st WF HX A n freeM_HB W HW m m' MU WM HR)
    as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & XB).
  assert (RL : R_live stF m').
  { unfold stF. intros A' n' Hin. destruct (st_freeP_same st A n) as (_ & E & _). rewrite E in Hin.
    destruct (lb_remove_other st A n A' n' WF HIN Hin) as [NE Hin0].
    apply R_block_freeP. apply XB; [unfold all_blocks; apply in_or_app; left; exact Hin0| exact (rr_live st m HR A' n' Hin0)| left; exact NE]. }
  assert (RQ : R_quar stF m').
  { unfold stF. split.
    - intros A' n' Hin. assert (Hin0 : In (A', n') (qelems st)) by (destruct st; exact Hin).
      apply R_block_freeP. apply XB; [unfold all_blocks; rewrite !in_app_iff; right; left; exact Hin0| exact (proj1 (rr_quar st m HR) A' n' Hin0)|].
      left. eapply lb_vs_rest; [exact WF| exact HIN| left; exact Hin0].
    - intros A' n' Hin. destruct (st_freeP_same st A n) as (_ & _ & _ & _ & _ & _ & _ & E & _). rewrite E in Hin. destruct Hin as [E'|Hin0].
      + injection E' as <- <-. apply R_block_freeP. exact HB.
      + apply R_block_freeP. apply XB; [unfold all_blocks; rewrite !in_app_iff; right; right; exact Hin0| exact (proj2 (rr_quar st m HR) A' n' Hin0)|].
        left. eapply lb_vs_rest; [exact WF| exact HIN| right; exact Hin0]. }
  unfold stF, st_freeP in *. destruct st. constructor; assumption.
Qed.
End FREEM.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition lbzc_ok (st : rtstate) (A n SP : Z) (iv : Z * Z) : Prop :=
     (b_lo A n <= fst iv /\ snd iv <= b_hi A n)
  \/ (st_t st + T_STATS <= fst iv /\ snd iv <= st_t st + T_UNWINDING)
  \/ (CEIL <= fst iv /\ snd iv <= SP).

Lemma lbzc_lbz : forall st A n SP W, Forall (lbzc_ok st A n SP) W -> Forall (lbz_ok st A n) W.
Proof.
  intros st A n SP W H. eapply Forall_impl; [| exact H]. intros [lo hi] A1. unfold lbzc_ok, lbz_ok in *. cbn [fst snd] in *. tauto.
Qed.

Section CLIQ.
Variable st : rtstate.
Hypothesis WF : RTWF st.
Variables (A n : Z).
Hypothesis HQ : In (A, n) (qelems st) \/ In (A, n) (st_qpend st).
Variable SP : Z.
Hypothesis HSP : CEIL <= SP.

Lemma cliq_HB : In (A, n) (all_blocks st).
Proof. unfold all_blocks. rewrite !in_app_iff. destruct HQ; tauto. Qed.

Lemma qchunk_not_client : forall a, b_lo A n <= a < b_hi A n -> ~ cj_client_addr (st_sp0 st) (st_lb st) (st_lf st) SP a.
Proof.
  intros a Ha HC. pose proof (block_geom st WF A n cliq_HB) as (_ & _ & G1 & G2 & G3 & G4 & _).
  destruct HC as [H|[H|[(A' & n' & Hb & Hr)|[(F & j & Hb & Hr)|H]]]].
  - unfold CEIL in *. lia.
  - unfold aclient_image, AERRNO, AGERROR0, AGERROR1, ADATA_LO, AIMG_HI, KHIGHMEM_BEG in *. blia.
  - assert (HB' : In (A', n') (all_blocks st)) by (unfold all_blocks; apply in_or_app; left; exact Hb).
    assert (NE : A' <> A).
    { intros ->. apply (lb_vs_rest st A n' A n WF Hb HQ). reflexivity. }
    pose proof (blocks_disj st WF A' n' A n HB' cliq_HB NE) as D.
    pose proof (block_geom st WF A' n' HB') as (_ & _ & _ & X & Y & _). unfold usz in Y. lia.
  - pose proof (frame_range st WF F j Hb) as (Hk & X & Y & AL). pose proof (fs_range st WF) as (F1 & F2 & _).
    pose proof (loose_blockfree st WF _ _ (wb_fs_loose st (wf_base_ok st WF)) A n cliq_HB) as D.
    change FS_FRAMES_OFF with 36864 in X. unfold FS_TOTAL in *.
    destruct Hr as [Hr|Hr]; [lia|].
    pose proof (rt_SH_bounds F ltac:(unfold CEIL, KHIGHMEM_BEG, AIMG_HI in *; blia)) as B0.
    pose proof (rt_SH_bounds (F + fsz j) ltac:(unfold CEIL, KHIGHMEM_BEG, AIMG_HI in *; blia)) as B. rewrite (rt_SH_aligned_add F (fsz j) AL) in B. unfold KHIGHMEM_BEG, AIMG_HI in *. blia.
  - unfold astack_shadow in H. rewrite CEIL_eq, SH_CEIL in H. change (SH (2^47)) with 0x10007fff8000 in H. unfold KHIGHMEM_BEG, AIMG_HI in *. blia.
Qed.

Lemma cli_pres_qz : forall W m m',
  munch W m m' -> wmono bsegs m m' -> Forall (lbzc_ok st A n SP) W -> cli_pres st SP m m'.
Proof.
  intros W m m' MU WM HW. unfold cli_pres. eapply cj_pres_of_munch; [exact MU| exact WM|].
  intros a Ha HC. clear MU WM. induction W as [|[lo hi] W' IH]; [exact I|].
  pose proof (Forall_inv HW) as A1. unfold lbzc_ok in A1. cbn [fst snd] in A1. cbn. split; [| apply IH; exact (Forall_inv_tail HW)].
  intros Hin. destruct A1 as [A1|[A1|A1]].
  - apply (qchunk_not_client a); [lia| exact HC].
  - apply (tpage_not_client st WF SP HSP a); [unfold T_STATS, T_UNWINDING, T_ACACHE in *; lia| exact HC].
  - apply (below_sp_not_client st WF SP a); [lia| exact HC].
Qed.
End CLIQ.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma disjoint_from_forall : forall (P : Z * Z -> Prop) W a sz,
  Forall P W -> (forall lo hi, P (lo, hi) -> a + sz <= lo \/ hi <= a) -> disjoint_from W a sz.
Proof.
  intros P W a sz HW HP. induction W as [|[lo hi] W IH]; [exact I|]. cbn. split; [apply HP; exact (Forall_inv HW)| apply IH; exact (Forall_inv_tail HW)].
Qed.

Section BGEO.
Variable st : rtstate.
Hypothesis WF : RTWF st.
Variables (A n : Z).
Hypothesis HB : In (A, n) (all_blocks st).

(* [comment removed for export] *)
Lemma block_extra :
  A + 8 <= b_hi A n /\ b_lo A n <= b_alloc_beg A n /\ b_alloc_beg A n + rz_size n = A
  /\ (bprim n = false -> b_map_beg A = b_lo A n) /\ (16 < rz_size n -> 32 <= rz_size n).
Proof.
  pose proof (block_geom st WF A n HB) as (Gn & GA & K & X & Y & CE & L16 & H16 & EA & Gp & Gs).
  pose proof (rz_size_range n) as [RZ RZ16]. pose proof (usz_le_rounded8 n) as (U1 & U2 & U3).
  assert (R32 : 16 < rz_size n -> 32 <= rz_size n) by (intros; Z.div_mod_to_equations; lia).
  unfold b_alloc_beg. destruct (bprim n) eqn:EP.
  - destruct (Gp eq_refl) as (C1 & C2 & C3 & C4 & C5 & C6). clear Gs.
    assert (SL : sh_left n = rz_size n / 8) by (unfold sh_left; rewrite EP; reflexivity).
    assert (EA' : A = b_lo A n + rz_size n) by (rewrite SL in EA; Z.div_mod_to_equations; lia).
    assert (NP : needed0 n <= 65536) by (unfold bprim, is_primary, KMAXSIZE in EP; apply Z.leb_le in EP; exact EP).
    pose proof (needed0_ge n) as NG. destruct (class_ok (needed0 n) ltac:(lia)) as [CC _]. unfold pclass in C6.
    assert (NE : needed0 n = rounded8 n + rz_size n) by reflexivity.
    repeat split; lia.
  - destruct (Gs eq_refl) as (S1 & S2 & S3 & S4). clear Gp. destruct (sec_facts n EP) as (F1 & F2 & _).
    assert (SL : sh_left n = (SEC_HDR + SEC_RZ) / 8) by (unfold sh_left; rewrite EP; reflexivity).
    unfold SEC_HDR, SEC_RZ in SL. rewrite SL in EA. change ((4096 + 2048) / 8) with 768 in EA.
    unfold b_map_beg, SEC_HDR, SEC_RZ. unfold usz in *. repeat split; lia.
Qed.

(* [comment removed for export] *)
Lemma block_vs_depot_fp : forall a, b_lo A n <= a < b_hi A n -> ~ in_ivs (depot_fp st) a.
Proof.
  intros a Ha (lo & hi & Hin & Hr).
  pose proof (block_geom st WF A n HB) as (Gn & GA & K & X & Y & CE & _).
  unfold depot_fp, fp_depot_blocks in Hin. destruct Hin as [E|Hin].
  - injection E as E1 E2. subst lo hi. unfold A_STACKSTORE, A_DEPOT_MAP1, KHIGHMEM_BEG, AIMG_HI in *. blia.
  - apply in_app_iff in Hin as [Hin|Hin]; apply in_map_iff in Hin as (b & E & Hb); injection E as E1 E2; subst lo hi.
    + destruct (nb_blockfree st WF b Hb) as [BF _]. destruct (BF A n HB); lia.
    + destruct (sb_blockfree st WF b Hb) as [BF _]. destruct (BF A n HB); lia.
Qed.

(* [comment removed for export] *)
Variable W : list (Z * Z).
Hypothesis HW : Forall (fun iv : Z * Z => (A - 16 <= fst iv /\ snd iv <= b_hi A n) \/ snd iv <= b_lo A n \/ b_hi A n <= fst iv) W.

Theorem R_block_to_pend : forall m m' (b1 : byte) (cid : word), munch W m m' -> wmono bsegs m m' -> R_block st m BLive A n ->
  rw_cells bsegs m' (b_chunk_beg A) (hdr_cells hdr_state_quar n b1 cid) -> hdr_b1_ok (bv_unsigned b1) ->
  R_block st m' BPend A n.
Proof.
  intros m m' b1 cid MU WM (HD & BG & SC & V & SHD) HC HB1.
  pose proof (block_geom st WF A n HB) as (Gn & GA & K & X & Y & CE & L16 & H16 & EA & Gp & Gs).
  pose proof block_extra as (E1 & E2 & E3 & E4 & E5). pose proof (rz_size_range n) as [RZ _].
  pose proof (rt_SH_bounds (b_lo A n) ltac:(unfold KHIGHMEM_BEG, AIMG_HI in K; blia)) as SB.
  split; [exists b1, cid; split; [exact HC| exact HB1]|].
  split; [| split; [| split]].
  - intros HRZ. eapply rw_cells_transport; [exact (BG HRZ)| exact MU| exact WM|].
    eapply disjoint_from_forall; [exact HW|]. intros lo hi P. cbn [fst snd] in P. cbn. specialize (E5 HRZ). lia.
  - intros EP. destruct (SC EP) as (V1 & V2 & HCS). specialize (E4 EP).
    pose proof E4 as E4'. unfold b_map_beg, SEC_RZ, SEC_HDR in E4'.
    unfold R_secmap. rewrite E4 in V1, V2, HCS |- *.
    split; [eapply stk_wmono_noseg; [exact V1| exact WM| unfold AIMG_HI, KHIGHMEM_BEG in *; blia]|].
    split; [eapply stk_wmono_noseg; [exact V2| exact WM| unfold AIMG_HI, KHIGHMEM_BEG in *; lia]|].
    eapply rw_cells_transport; [exact HCS| exact MU| exact WM|].
    eapply disjoint_from_forall; [exact HW|]. intros lo hi P. cbn [fst snd] in P. cbn. lia.
  - eapply stk_wmono_noseg; [exact V| exact WM| unfold AIMG_HI, KHIGHMEM_BEG in *; blia].
  - unfold R_bshadow in *. destruct (bprim n) eqn:EP; [| exact I].
    eapply stk_wmono_noseg; [| exact WM| unfold AIMG_HI; lia].
    eapply stk_of_rw_cellsZ; [exact SHD|]. rewrite zcells_size. rewrite sh_live_len by lia. reflexivity.
Qed.
End BGEO.


End CeilWrap.
