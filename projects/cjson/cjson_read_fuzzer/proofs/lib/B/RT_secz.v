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
From Stdlib Require Permutation.
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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_bandtac4.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Ceil.
Module RT_artZ.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Mem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Cells OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Frame OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.BImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit.RT_shlem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_cost.RT_artG OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp.RT_artB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.ABand OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_bandtac4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition A_DEPOT_END : Z := A_DEPOT_MAP1 + 8 * 2^15.
Lemma A_DEPOT_END_val : A_DEPOT_END = 0x5cb8a8. Proof. reflexivity. Qed.
Lemma A_STACKSTORE_val : A_STACKSTORE = 0x17b888. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition rt_nd (st : rtstate) : list (Z * Z) :=
  (st_pbase st, st_pbase st + PRIM_RES_SIZE)
  :: (st_pa st, st_pa st + PTRARR_RES_SIZE)
  :: map (fun e => (fst e, fst e + snd e)) (st_loose0 st)
  ++ map (fun e => (fst e, fst e + smapsize (snd e))) (st_sec st).
Definition NBR (st : rtstate) : list (Z * Z) := map (fun b => (b, b + NODEBLOCK_SIZE)) (d_nblocks (st_depot st)).
Definition SBR (st : rtstate) : list (Z * Z) := map (fun b => (b, b + STOREBLOCK_SIZE)) (d_sblocks (st_depot st)).
Lemma rt_ranges_nd : forall st, rt_ranges st = rt_nd st ++ NBR st ++ SBR st.
Proof. intros st. unfold rt_ranges, rt_nd, NBR, SBR. cbn [app]. rewrite <- !app_assoc. reflexivity. Qed.
Lemma rt_nd_In : forall st r, In r (rt_nd st) -> In r (rt_ranges st).
Proof. intros st r H. rewrite rt_ranges_nd. apply in_or_app. left. exact H. Qed.

(* [comment removed for export] *)
Definition RTREP_nd (st : rtstate) (m : word -> option byte) : Prop :=
  R_link m /\ R_consts st m /\ R_alloc st m /\ R_rinfo st m /\ R_regions st m /\ R_avail st m /\ R_cache st m
  /\ R_thread st m /\ R_live st m /\ R_quar st m /\ R_batches st m /\ R_ptrarr st m /\ R_fs st m /\ R_ia m
  /\ R_lowshadow m.
Lemma RTREP_to_nd : forall st m, RTREP st m -> RTREP_nd st m.
Proof.
  intros st m H. unfold RTREP_nd.
  repeat lazymatch goal with |- _ /\ _ => split | _ => idtac end;
  [exact (rr_link st m H)| exact (rr_consts st m H)| exact (rr_alloc st m H)| exact (rr_rinfo st m H)| exact (rr_regions st m H)
  | exact (rr_avail st m H)| exact (rr_cache st m H)| exact (rr_thread st m H)| exact (rr_live st m H)| exact (rr_quar st m H)
  | exact (rr_batches st m H)| exact (rr_ptrarr st m H)| exact (rr_fs st m H)| exact (rr_ia st m H)| exact (rr_lowshadow st m H)].
Qed.
Lemma RTREP_of_nd : forall st m, RTREP_nd st m -> R_depot st m -> RTREP st m.
Proof.
  intros st m (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15) HD. constructor; assumption.
Qed.
(* [comment removed for export] *)
Definition set_depot (st : rtstate) (D : depot_st) (T : list (list Z)) : rtstate :=
  match st with
  | mkRT a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 _ _ a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5 =>
    mkRT a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 D T a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5
  end.
Lemma set_depot_depot : forall st D T, st_depot (set_depot st D T) = D. Proof. intros [] D T; reflexivity. Qed.
Lemma set_depot_trs : forall st D T, st_trs (set_depot st D T) = T. Proof. intros [] D T; reflexivity. Qed.
Lemma RTREP_nd_set_depot : forall st D T m, RTREP_nd st m -> RTREP_nd (set_depot st D T) m.
Proof. intros [] D T m H. exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section RZ.
Variable st : rtstate.
Hypothesis WF : RTWF st.
Variable W : list (Z * Z).
Hypothesis Hlow : forall a sz, a + sz <= A_STACKSTORE -> disjoint_from W a sz.
(* [comment removed for export] *)
Hypothesis Hmid : forall a sz, A_DEPOT_END <= a -> a + sz <= KHIGHMEM_BEG -> (a + sz <= AIMG_HI \/ KLOWSHADOW_BEG <= a) -> disjoint_from W a sz.
Hypothesis Hheap : forall r a sz, In r (rt_nd st) -> fst r <= a -> a + sz <= snd r -> disjoint_from W a sz.

Local Abbreviation P := (st_pbase st).

Lemma RZprim : forall a sz, P <= a -> a + sz <= P + PRIM_RES_SIZE -> disjoint_from W a sz.
Proof. intros a sz H1 H2. apply (Hheap (P, P + PRIM_RES_SIZE)); [left; reflexivity| exact H1| exact H2]. Qed.
Lemma RZpa : forall a sz, st_pa st <= a -> a + sz <= st_pa st + PTRARR_RES_SIZE -> disjoint_from W a sz.
Proof. intros a sz H1 H2. apply (Hheap (st_pa st, st_pa st + PTRARR_RES_SIZE)); [right; left; reflexivity| exact H1| exact H2]. Qed.
Lemma RZloose : forall b k a sz, In (b, k) (st_loose0 st) -> b <= a -> a + sz <= b + k -> disjoint_from W a sz.
Proof.
  intros b k a sz Hin H1 H2. apply (Hheap (b, b + k)); [| exact H1| exact H2].
  right; right. apply in_or_app. left. apply in_map_iff. exists (b, k). auto.
Qed.
Lemma RZsec : forall e a sz, In e (st_sec st) -> fst e <= a -> a + sz <= fst e + smapsize (snd e) -> disjoint_from W a sz.
Proof.
  intros e a sz Hin H1 H2. apply (Hheap (fst e, fst e + smapsize (snd e))); [| exact H1| exact H2].
  right; right. apply in_or_app. right. apply in_map_iff. exists e. auto.
Qed.
(* [comment removed for export] *)
Lemma RZsh : forall x k, 0 <= x -> 0 <= k -> x + 8 * k <= CEIL -> disjoint_from W (SH x) k.
Proof.
  intros x k H0 Hk Hx. apply Hmid; rewrite ?A_DEPOT_END_val; unfold SH, SHADOW_OFFSET, CEIL, KHIGHMEM_BEG, KLOWSHADOW_BEG, AIMG_HI in *; Z.div_mod_to_equations; lia.
Qed.
Lemma RZsh2 : forall lo hi, 0 <= lo -> lo <= hi -> hi <= CEIL -> disjoint_from W (SH lo) (SH hi - SH lo).
Proof.
  intros lo hi H0 H1 H2. apply Hmid; rewrite ?A_DEPOT_END_val; unfold SH, SHADOW_OFFSET, CEIL, KHIGHMEM_BEG, KLOWSHADOW_BEG, AIMG_HI in *; Z.div_mod_to_equations; lia.
Qed.

Local Ltac lowmid := first [ apply Hlow; rewrite ?A_STACKSTORE_val; lia | apply Hmid; rewrite ?A_DEPOT_END_val; unfold KHIGHMEM_BEG, KLOWSHADOW_BEG, AIMG_HI; lia ].

(* [comment removed for export] *)
Lemma RZ_link : WOK_link W.
Proof.
  split; [intros a v Hin; destruct (alink_range a v Hin); lowmid| unfold A_GLOBREC_LO, A_GLOBREC_HI; lowmid].
Qed.
Lemma RZ_consts : WOK_consts W.
Proof.
  unfold WOK_consts.
  unfold A_SHADOW_OFF_CELL, A_UAR_OPTION, A_AFLAGS, A_CFLAGS, A_PAGESIZE_CACHED, A_KHIGHMEMEND, A_KMIDMEMBEG, A_KMIDMEMEND,
    A_ASAN_INITED, A_MCS, A_CAN_POISON, A_TSD_KEY_INITED, A_TSD_KEY, A_MAY_RETURN_NULL, A_ALLOC_OOM, A_DYING, A_VERBOSITY,
    A_MFHOOKS, A_LSAN_DISABLE, A_IA_INITED, AHOOKS, A_LIBC_PAGESIZE, A_MU_GLOBALS, A_GLOBALS_REGD, A_TPCG_INITED, A_TOOLNAME, A_PRINTF_CB, A_EMB, ATP.
  repeat lazymatch goal with |- _ /\ _ => split | _ => idtac end; lowmid.
Qed.
Lemma RZ_alloc : WOK_alloc W.
Proof.
  unfold WOK_alloc, A_ALLOC, A_SECONDARY, A_GSTATS, A_QUAR, A_MAXUSERSZ, A_ALLOC.
  repeat lazymatch goal with |- _ /\ _ => split | _ => idtac end; lowmid.
Qed.
Lemma RZ_ia : WOK_ia W.
Proof. intros i Hi. unfold A_IA_MAP1. lowmid. Qed.
Lemma RZ_lowshadow : WOK_lowshadow W.
Proof.
  intros g Hg. change (SH AIMG_LO) with 0x7fffa000 in Hg. change (SH AIMG_HI) with 0x800b7e00 in Hg. lowmid.
Qed.

(* [comment removed for export] *)
Lemma RZ_rinfo : WOK_rinfo st W.
Proof.
  intros c Hc. pose proof (ris_range st WF) as (X1 & X2 & X3 & X4). unfold KNUMCLASSES in Hc.
  apply RZprim; unfold rinfo; lia.
Qed.
Lemma RZ_regions : WOK_regions st W.
Proof.
  intros c Hc. pose proof (region_facts st WF c Hc) as RF. cbn zeta in RF.
  destruct RF as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10).
  assert (FB : fabeg st c = rbeg st c + KFREEARRAY_OFF) by reflexivity.
  unfold KHIGHMEM_BEG, KREGIONSIZE, KFREEARRAY_OFF, KFREEARRAY_SIZE in *.
  split.
  - intros i Hi. pose proof (wc_num_freed st c (wf_class_ok st WF c Hc)) as NF. apply RZprim; lia.
  - apply RZsh; [lia| Z.div_mod_to_equations; lia| unfold CEIL; Z.div_mod_to_equations; lia].
Qed.
Lemma RZ_avail : WOK_avail st W.
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
  apply RZsh; [lia| Z.div_mod_to_equations; lia| unfold CEIL; Z.div_mod_to_equations; lia].
Qed.

(* [comment removed for export] *)
Lemma RZt : forall a sz, st_t st <= a -> a + sz <= st_t st + 4096 -> disjoint_from W a sz.
Proof. intros a sz H1 H2. eapply RZloose; [exact (wb_t_loose st (wf_base_ok st WF))| exact H1| exact H2]. Qed.
Lemma RZ_cache : WOK_cache st W.
Proof.
  intros c Hc. pose proof (wc_cache_max st c (wf_class_ok st WF c Hc)) as CM. pose proof (cmaxcount_le16 c). unfold KNUMCLASSES in Hc.
  split.
  - apply RZt; unfold pcaddr, acache, T_ACACHE; lia.
  - intros i Hi. apply RZt; unfold pcaddr, acache, T_ACACHE; lia.
Qed.
Lemma RZ_thread : WOK_thread st W.
Proof.
  unfold WOK_thread.
  split; [apply RZt; lia|].
  split; [apply RZt; unfold qcache_t, T_QCACHE; lia|].
  split; [apply RZt; unfold T_UNWINDING; lia|].
  destruct (wb_ctx_loose st (wf_base_ok st WF)) as (cb & ck & CL1 & CL2 & CL3).
  split; [eapply RZloose; [exact CL1| unfold CTX_TID; lia| unfold CTX_TID; lia]|].
  split; [eapply RZloose; [exact CL1| unfold CTX_THREAD; lia| unfold CTX_THREAD; lia]|].
  unfold A_TSD_PTR, A_TSD_MAIN, A_DTV_PTR, A_DTV, A_TLSMOD, A_FSTLS_CELL, A_DTLS_OFF, ATP in *.
  split; [lowmid|]. split; [lowmid|]. split; [lowmid|]. split; [lowmid|]. split; [lowmid|]. split; [lowmid|].
  destruct (wb_dtls_loose st (wf_base_ok st WF)) as (db & dk & DL1 & DL2 & DL3).
  eapply RZloose; [exact DL1| lia| lia].
Qed.

(* [comment removed for export] *)
Lemma RZ_block : forall A n, In (A, n) (all_blocks st) -> WOK_block W A n.
Proof.
  intros A n HB.
  pose proof (block_geom st WF A n HB) as (Gn & GA & K & X & Y & CE & L16 & H16 & EA & Gp & Gs). unfold usz in Y. unfold KHIGHMEM_BEG in K.
  pose proof (rz_size_range n) as (Z1 & Z2).
  assert (OBJ : forall a sz, b_lo A n <= a -> a + sz <= b_hi A n -> disjoint_from W a sz).
  { intros a sz Ha Hs. destruct (bprim n) eqn:EP.
    - destruct (Gp eq_refl) as (_ & _ & _ & Q1 & Q2 & _). apply RZprim; lia.
    - destruct (Gs eq_refl) as (S1 & T1 & _). eapply (RZsec (b_lo A n, n)); [exact S1| cbn [fst]; lia| cbn [fst snd]; lia]. }
  apply WOK_block_intro.
  - intros a sz Ha Hs. apply OBJ; lia.
  - unfold sh_tot. assert (EH : b_hi A n = b_lo A n + asz n) by reflexivity.
    assert (ASZ : 0 <= asz n).
    { destruct (bprim n) eqn:EP; [destruct (prim_facts n EP) as (_ & _ & F3 & F4 & F5); rewrite F5 | destruct (sec_facts n EP) as (_ & _ & F3 & _ & F5 & _); rewrite F5]; Z.div_mod_to_equations; lia. }
    apply RZsh; [blia| Z.div_mod_to_equations; lia| unfold CEIL; Z.div_mod_to_equations; lia].
  - rewrite EA at 2. unfold sh_left, SEC_HDR, SEC_RZ. destruct (bprim n) eqn:EP.
    + Z.div_mod_to_equations. lia.
    + destruct (sec_facts n EP) as (_ & F2 & _). rewrite F2. cbn. lia.
Qed.
Lemma RZ_live : WOK_live st W.
Proof. intros A n Hin. apply RZ_block. unfold all_blocks; apply in_or_app; left; exact Hin. Qed.
Lemma RZ_quar : WOK_quar st W.
Proof. intros A n Hin. apply RZ_block. unfold all_blocks; apply in_or_app; right; exact Hin. Qed.

(* [comment removed for export] *)
Lemma RZ_batches : WOK_batches st W.
Proof.
  intros b Hb.
  destruct (batch_geom st WF b Hb) as (BB & BF & R1 & R2 & AL).
  destruct (wq_batch st (wf_quar_ok st WF) b Hb) as [CNT _].
  pose proof (region_facts st WF 24 ltac:(unfold KNUMCLASSES; lia)) as RF. cbn zeta in RF. destruct RF as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10).
  unfold KHIGHMEM_BEG, KREGIONSIZE, KFREEARRAY_OFF, QBATCH_SIZE, QBATCH_CAP in *.
  split; [| split].
  - apply RZprim; lia.
  - intros i Hi. apply RZprim; lia.
  - apply RZsh; [lia| lia| unfold CEIL; lia].
Qed.

(* [comment removed for export] *)
Lemma RZ_ptrarr : WOK_ptrarr st W.
Proof.
  split.
  - intros i Hi. pose proof (pa_range st WF) as (P1 & P2 & P3 & P4 & P5). apply RZpa; lia.
  - intros e He. destruct (ws_spend st (wf_sec_ok st WF) e He) as [HE _].
    destruct e as [mb n]. destruct (ws_entry st (wf_sec_ok st WF) _ HE) as (E1 & _). destruct (sec_facts n E1) as (_ & _ & _ & F4 & _).
    pose proof (usz_le_rounded8 n) as (U1 & _).
    eapply (RZsec (mb, n)); [exact HE| cbn [fst]; lia| cbn [fst snd]; unfold usz in *; lia].
Qed.

(* [comment removed for export] *)
Lemma RZ_fs : WOK_fs st W.
Proof.
  pose proof (wb_fs_loose st (wf_base_ok st WF)) as FL.
  assert (OBJ : forall a sz, st_fs st <= a -> a + sz <= st_fs st + FS_TOTAL -> disjoint_from W a sz).
  { intros a sz H1 H2. eapply RZloose; [exact FL| exact H1| exact H2]. }
  unfold WOK_fs. split; [| split; [| split; [| split]]].
  - intros k Hk. apply OBJ; unfold FS_TOTAL; lia.
  - apply OBJ; unfold FS_TOTAL; lia.
  - apply OBJ; unfold FS_TOTAL; lia.
  - intros k pos Hk Hp. pose proof (flags_ok k Hk) as [O1 O2]. apply OBJ; unfold fflag_addr, FS_TOTAL in *; lia.
  - intros F k Hin. pose proof (frame_range st WF F k Hin) as (Hk & X1 & X2 & _). pose proof (fsz_12 k Hk) as (FZ & _).
    assert (8 <= fsz k) by (rewrite FZ; destruct Hk as [-> | ->]; cbn; lia).
    apply OBJ; unfold FS_FRAMES_OFF in *; lia.
Qed.

(* [comment removed for export] *)
Theorem rz_others : forall m m', munch W m m' -> wmono bsegs m m' -> RTREP st m -> RTREP_nd st m'.
Proof.
  intros m m' MU WM HR. unfold RTREP_nd.
  Local Ltac tapp T st WF W m m' MU WM :=
    first [ eapply (T st WF W m m' MU WM) | eapply (T st W m m' MU WM) | eapply (T st W m m' MU) | eapply (T W m m' MU WM) | eapply (T W m m' MU) ].
  split; [tapp T_link st WF W m m' MU WM; [exact (rr_link st m HR)| apply RZ_link]|].
  split; [tapp T_consts st WF W m m' MU WM; [exact (rr_consts st m HR)| apply RZ_consts]|].
  split; [tapp T_alloc st WF W m m' MU WM; [exact (rr_alloc st m HR)| apply RZ_alloc]|].
  split; [tapp T_rinfo st WF W m m' MU WM; [exact (rr_rinfo st m HR)| apply RZ_rinfo]|].
  split; [tapp T_regions st WF W m m' MU WM; [exact (rr_regions st m HR)| apply RZ_regions]|].
  split; [tapp T_avail st WF W m m' MU WM; [exact (rr_avail st m HR)| apply RZ_avail]|].
  split; [tapp T_cache st WF W m m' MU WM; [exact (rr_cache st m HR)| apply RZ_cache]|].
  split; [tapp T_thread st WF W m m' MU WM; [exact (rr_thread st m HR)| apply RZ_thread]|].
  split; [tapp T_live st WF W m m' MU WM; [exact (rr_live st m HR)| apply RZ_live]|].
  split; [tapp T_quar st WF W m m' MU WM; [exact (rr_quar st m HR)| apply RZ_quar]|].
  split; [tapp T_batches st WF W m m' MU WM; [exact (rr_batches st m HR)| apply RZ_batches]|].
  split; [tapp T_ptrarr st WF W m m' MU WM; [exact (rr_ptrarr st m HR)| apply RZ_ptrarr]|].
  split; [tapp T_fs st WF W m m' MU WM; [exact (rr_fs st m HR)| apply RZ_fs]|].
  split; [tapp T_ia st WF W m m' MU WM; [exact (rr_ia st m HR)| apply RZ_ia]|].
  tapp T_lowshadow st WF W m m' MU WM; [exact (rr_lowshadow st m HR)| apply RZ_lowshadow].
Qed.
End RZ.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition dz_ok (st : rtstate) (FR : list (Z * Z)) (iv : Z * Z) : Prop :=
  CEIL <= fst iv
  \/ (A_STACKSTORE <= fst iv /\ snd iv <= A_DEPOT_END)
  \/ (exists b, In b (d_nblocks (st_depot st)) /\ b <= fst iv /\ snd iv <= b + NODEBLOCK_SIZE)
  \/ (exists b, In b (d_sblocks (st_depot st)) /\ b <= fst iv /\ snd iv <= b + STOREBLOCK_SIZE)
  \/ (exists f, In f FR /\ fst f <= fst iv /\ snd iv <= snd f).
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fresh_ok (st : rtstate) (FR : list (Z * Z)) : Prop :=
  forall f, In f FR -> ablk (fst f) (snd f) /\ forall r, In r (rt_ranges st) -> snd f <= fst r \/ snd r <= fst f.

Section DZ.
Variable st : rtstate.
Hypothesis WF : RTWF st.
Variables (W FR : list (Z * Z)).
Hypothesis HW : Forall (dz_ok st FR) W.
Hypothesis HFR : fresh_ok st FR.

Lemma dz_low : forall a sz, a + sz <= A_STACKSTORE -> disjoint_from W a sz.
Proof.
  intros a sz H. induction W as [|[lo hi] W' IH]; [exact I|]. inversion HW as [|x l H2 H3]; subst. cbn. split; [| apply IH; exact H3].
  unfold dz_ok in H2. cbn [fst snd] in H2. rewrite A_STACKSTORE_val in *. unfold CEIL in *.
  destruct H2 as [H2|[H2|[(b & Hb & H2)|[(b & Hb & H2)|(f & Hf & H2)]]]]; try lia.
  - destruct (nb_range st WF b Hb) as (B1 & _). pose proof (ablk_img _ _ B1) as B2. unfold AIMG_HI in B2. lia.
  - destruct (sb_range st WF b Hb) as (B1 & _). pose proof (ablk_img _ _ B1) as B2. unfold AIMG_HI in B2. lia.
  - destruct (HFR f Hf) as [F1 _]. pose proof (ablk_img _ _ F1) as B2. unfold AIMG_HI in B2. lia.
Qed.
Lemma dz_mid : forall a sz, A_DEPOT_END <= a -> a + sz <= KHIGHMEM_BEG -> (a + sz <= AIMG_HI \/ KLOWSHADOW_BEG <= a) -> disjoint_from W a sz.
Proof.
  intros a sz H1 H2 HZ. induction W as [|[lo hi] W' IH]; [exact I|]. inversion HW as [|x l H3 H4]; subst. cbn. split; [| apply IH; exact H4].
  unfold dz_ok in H3. cbn [fst snd] in H3. unfold CEIL in *.
  destruct H3 as [H3|[H3|[(b & Hb & H3)|[(b & Hb & H3)|(f & Hf & H3)]]]].
  - unfold KHIGHMEM_BEG in *. lia.
  - lia.
  - destruct (nb_range st WF b Hb) as (B1 & _). clear - B1 H3 HZ H1 H2. blia.
  - destruct (sb_range st WF b Hb) as (B1 & _). clear - B1 H3 HZ H1 H2. blia.
  - destruct (HFR f Hf) as [F1 _]. clear - F1 H3 HZ H1 H2. blia.
Qed.
Lemma dz_heap : forall r a sz, In r (rt_nd st) -> fst r <= a -> a + sz <= snd r -> disjoint_from W a sz.
Proof.
  intros r a sz Hr H1 H2. pose proof (wb_ranges st (wf_base_ok st WF) r (rt_nd_In st r Hr)) as (R1 & R2 & R3 & R4).
  pose proof (wb_pwdj st (wf_base_ok st WF)) as PW. rewrite rt_ranges_nd in PW.
  induction W as [|[lo hi] W' IH]; [exact I|]. inversion HW as [|x l H3 H4]; subst. cbn. split; [| apply IH; exact H4].
  unfold dz_ok in H3. cbn [fst snd] in H3. rewrite A_DEPOT_END_val in *. rewrite ?A_STACKSTORE_val in *. unfold CEIL, KHIGHMEM_BEG in *.
  destruct H3 as [H3|[H3|[(b & Hb & H3)|[(b & Hb & H3)|(f & Hf & H3)]]]]; try (clear - R1 R2 R3 H1 H2 H3; blia).
  - pose proof (pwdj_app_disj _ _ r (b, b + NODEBLOCK_SIZE) PW Hr ltac:(apply in_or_app; left; unfold NBR; apply in_map_iff; exists b; auto)) as D.
    cbn [fst snd] in D. lia.
  - pose proof (pwdj_app_disj _ _ r (b, b + STOREBLOCK_SIZE) PW Hr ltac:(apply in_or_app; right; unfold SBR; apply in_map_iff; exists b; auto)) as D.
    cbn [fst snd] in D. lia.
  - destruct (HFR f Hf) as [_ F2]. destruct (F2 r (rt_nd_In st r Hr)); lia.
Qed.

Theorem dz_others : forall m m', munch W m m' -> wmono bsegs m m' -> RTREP st m -> RTREP_nd st m'.
Proof. intros m m' MU WM HR. exact (rz_others st WF W dz_low dz_mid dz_heap m m' MU WM HR). Qed.

(* [comment removed for export] *)
Lemma dz_wok : WOK_link W /\ WOK_consts W /\ WOK_alloc W /\ WOK_rinfo st W /\ WOK_regions st W /\ WOK_avail st W
  /\ WOK_cache st W /\ WOK_thread st W /\ WOK_live st W /\ WOK_quar st W /\ WOK_batches st W /\ WOK_ptrarr st W
  /\ WOK_fs st W /\ WOK_ia W /\ WOK_lowshadow W.
Proof.
  pose proof dz_low as L. pose proof dz_mid as M. pose proof dz_heap as H.
  repeat lazymatch goal with |- _ /\ _ => split | _ => idtac end;
  [apply RZ_link| apply RZ_consts| apply RZ_alloc| apply RZ_rinfo| apply RZ_regions| apply RZ_avail| apply RZ_cache| apply RZ_thread
  | apply RZ_live| apply RZ_quar| apply RZ_batches| apply RZ_ptrarr| apply RZ_fs| apply RZ_ia| apply RZ_lowshadow]; auto.
Qed.
End DZ.

(* [comment removed for export] *)
Lemma dz_ok_stack : forall st FR lo hi, CEIL <= lo -> dz_ok st FR (lo, hi).
Proof. intros. left. cbn. assumption. Qed.
Lemma dz_ok_static : forall st FR lo hi, A_STACKSTORE <= lo -> hi <= A_DEPOT_END -> dz_ok st FR (lo, hi).
Proof. intros. right; left. cbn. auto. Qed.
Lemma dz_ok_nb : forall st FR b lo hi, In b (d_nblocks (st_depot st)) -> b <= lo -> hi <= b + NODEBLOCK_SIZE -> dz_ok st FR (lo, hi).
Proof. intros. right; right; left. exists b. cbn. auto. Qed.
Lemma dz_ok_sb : forall st FR b lo hi, In b (d_sblocks (st_depot st)) -> b <= lo -> hi <= b + STOREBLOCK_SIZE -> dz_ok st FR (lo, hi).
Proof. intros. right; right; right; left. exists b. cbn. auto. Qed.
Lemma dz_ok_fresh : forall st FR f lo hi, In f FR -> fst f <= lo -> hi <= snd f -> dz_ok st FR (lo, hi).
Proof. intros. do 4 right. exists f. cbn. auto. Qed.
Lemma fresh_ok_nil : forall st, fresh_ok st [].
Proof. intros st f []. Qed.
(* [comment removed for export] *)
Lemma fresh_ok_cons : forall st FR lo hi, ablk lo hi ->
  (forall r, In r (rt_ranges st) -> hi <= fst r \/ snd r <= lo) -> fresh_ok st FR -> fresh_ok st ((lo, hi) :: FR).
Proof.
  intros st FR lo hi H1 H2 H3 f [<-|Hf]; [| exact (H3 f Hf)]. cbn [fst snd]. split; [exact H1| exact H2].
Qed.


End CeilWrap.
End RT_artZ.

(* [comment removed for export] *)
From LinuxProcessSemantics.LinuxProcessSem Require Monad.
From LinuxProcessSemantics.LinuxProcessSem Require Specs.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SysStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LMeasure.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_sec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_bandtac3.
Module RT_emb0.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Mem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Cells OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Frame OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LMeasure OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMM.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.BImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit.RT_shlem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_cost.RT_artG OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp.RT_artB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_artF RT_artZ OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_sec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.ABand OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_bandtac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_bandtac2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_bandtac3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_bandtac4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

(* [comment removed for export] *)
Definition RTREP_nc (st : rtstate) (m : word -> option byte) : Prop :=
  R_link m /\ R_alloc st m /\ R_rinfo st m /\ R_regions st m /\ R_avail st m /\ R_cache st m
  /\ R_thread st m /\ R_live st m /\ R_quar st m /\ R_batches st m /\ R_ptrarr st m /\ R_depot st m /\ R_fs st m /\ R_ia m
  /\ R_lowshadow m.
Lemma RTREP_to_nc : forall st m, RTREP st m -> RTREP_nc st m.
Proof.
  intros st m H. unfold RTREP_nc.
  repeat lazymatch goal with |- _ /\ _ => split | _ => idtac end;
  [exact (rr_link st m H)| exact (rr_alloc st m H)| exact (rr_rinfo st m H)| exact (rr_regions st m H)
  | exact (rr_avail st m H)| exact (rr_cache st m H)| exact (rr_thread st m H)| exact (rr_live st m H)| exact (rr_quar st m H)
  | exact (rr_batches st m H)| exact (rr_ptrarr st m H)| exact (rr_depot st m H)| exact (rr_fs st m H)| exact (rr_ia st m H)| exact (rr_lowshadow st m H)].
Qed.
Lemma RTREP_of_nc : forall st m, RTREP_nc st m -> R_consts st m -> RTREP st m.
Proof.
  intros st m (X1 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15 & X16) HC. constructor; assumption.
Qed.

(* [comment removed for export] *)
Definition R_consts_rest (st : rtstate) (m : word -> option byte) : Prop :=
  cells_at bsegs m A_SHADOW_OFF_CELL [W8 SHADOW_OFFSET]
  /\ cells_at bsegs m A_UAR_OPTION [W4 1]
  /\ cells_at bsegs m A_AFLAGS [CB 120 (map zb aflags_bytes)]
  /\ cells_at bsegs m A_CFLAGS [CB 288 (map zb cflags_bytes)]
  /\ cells_at bsegs m A_PAGESIZE_CACHED [W8 4096]
  /\ cells_at bsegs m A_KHIGHMEMEND [W8 KHIGHMEM_END]
  /\ cells_at bsegs m A_KMIDMEMBEG [W8 0]
  /\ cells_at bsegs m A_KMIDMEMEND [W8 0]
  /\ cells_at bsegs m A_ASAN_INITED [W1 1; W1 1; W1 0]
  /\ cells_at bsegs m A_MCS [W4 30]
  /\ cells_at bsegs m A_CAN_POISON [W1 1]
  /\ cells_at bsegs m A_TSD_KEY_INITED [W1 1]
  /\ cells_at bsegs m A_TSD_KEY [W4 0]
  /\ cells_at bsegs m A_MAY_RETURN_NULL [W1 1; W1 0]
  /\ (exists oom : byte, rw_cells bsegs m A_ALLOC_OOM [C1 oom])
  /\ cells_at bsegs m A_DYING [W4 0]
  /\ cells_at bsegs m A_VERBOSITY [W4 0]
  /\ cells_at bsegs m A_MFHOOKS (repeat (W8 0) 10)
  /\ cells_at bsegs m A_LSAN_DISABLE [W4 0]
  /\ rw_cells bsegs m A_IA_INITED [W1 (if st_ia_inited st then 1 else 0); W1 0; W1 0; W1 0]
  /\ cells_at bsegs m AHOOKS [W8 AMALLOC; W8 AFREE; W8 AREALLOC]
  /\ cells_at bsegs m A_LIBC_PAGESIZE [W8 4096]
  /\ rw_cells bsegs m A_MU_GLOBALS [W8 0]
  /\ rw_cells bsegs m A_GLOBALS_REGD [W8 1]
  /\ cells_at bsegs m A_TPCG_INITED [W1 0]
  /\ cells_at bsegs m A_TOOLNAME [W8 A_ASAN_STR]
  /\ cells_at bsegs m A_PRINTF_CB [W8 A_EMB_CB].
Lemma R_consts_split : forall st m, R_consts st m -> R_consts_rest st m /\ R_emb st m.
Proof.
  intros st m H. unfold R_consts in H. unfold R_consts_rest.
  destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27 & H28).
  repeat lazymatch goal with |- _ /\ _ => split | _ => idtac end; assumption.
Qed.
Lemma R_consts_join : forall st m, R_consts_rest st m -> R_emb st m -> R_consts st m.
Proof.
  intros st m H HE. unfold R_consts_rest in H. unfold R_consts.
  destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27).
  repeat lazymatch goal with |- _ /\ _ => split | _ => idtac end; assumption.
Qed.
(* [comment removed for export] *)
Lemma R_consts_rest_indep : forall st st' m, st_ia_inited st' = st_ia_inited st -> R_consts_rest st m -> R_consts_rest st' m.
Proof. intros st st' m E H. unfold R_consts_rest in *. rewrite E. exact H. Qed.


End CeilWrap.
End RT_emb0.

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
Import RT_artZ.
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

Lemma A_SECONDARY_val : A_SECONDARY = 0xa6398. Proof. reflexivity. Qed.
Lemma A_QUAR_val : A_QUAR = 0xa6630. Proof. reflexivity. Qed.
Lemma KHIGHSHADOW_BEG_val : KHIGHSHADOW_BEG = 0x2008fff7000. Proof. reflexivity. Qed.
Lemma KHIGHSHADOW_BEG_SH : KHIGHSHADOW_BEG = SH KHIGHMEM_BEG. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition rt_nd2 (st : rtstate) : list (Z * Z) :=
  (st_pbase st, st_pbase st + PRIM_RES_SIZE)
  :: map (fun e => (fst e, fst e + snd e)) (st_loose0 st)
  ++ map (fun e => (fst e, fst e + smapsize (snd e))) (st_sec st).
Lemma rt_nd2_nd : forall st r, In r (rt_nd2 st) -> In r (rt_nd st).
Proof. intros st r [H|H]; [left; exact H| right; right; exact H]. Qed.
Lemma rt_nd2_In : forall st r, In r (rt_nd2 st) -> In r (rt_ranges st).
Proof. intros st r H. apply rt_nd_In. apply rt_nd2_nd. exact H. Qed.

(* [comment removed for export] *)
Definition RTREP_nsec (st : rtstate) (m : word -> option byte) : Prop :=
  R_link m /\ R_consts st m /\ R_rinfo st m /\ R_regions st m /\ R_avail st m /\ R_cache st m
  /\ R_thread st m /\ R_live st m /\ R_quar st m /\ R_batches st m /\ R_depot st m /\ R_fs st m /\ R_ia m
  /\ R_lowshadow m.
Lemma RTREP_to_nsec : forall st m, RTREP st m -> RTREP_nsec st m.
Proof.
  intros st m H. unfold RTREP_nsec.
  repeat lazymatch goal with |- _ /\ _ => split | _ => idtac end;
  [exact (rr_link st m H)| exact (rr_consts st m H)| exact (rr_rinfo st m H)| exact (rr_regions st m H)
  | exact (rr_avail st m H)| exact (rr_cache st m H)| exact (rr_thread st m H)| exact (rr_live st m H)| exact (rr_quar st m H)
  | exact (rr_batches st m H)| exact (rr_depot st m H)| exact (rr_fs st m H)| exact (rr_ia st m H)| exact (rr_lowshadow st m H)].
Qed.
Lemma RTREP_of_nsec : forall st m, RTREP_nsec st m -> R_alloc st m -> R_ptrarr st m -> RTREP st m.
Proof.
  intros st m (X1 & X2 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X13 & X14 & X15 & X16) HA HP. constructor; assumption.
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Section SZ.
Variable st : rtstate.
Hypothesis WF : RTWF st.
Variable W : list (Z * Z).
Local Abbreviation P := (st_pbase st).
Local Abbreviation T := (st_t st).

(* [comment removed for export] *)
Hypothesis S1 : forall a sz, AIMG_LO <= a -> a + sz <= A_SECONDARY -> disjoint_from W a sz.
Hypothesis S2 : forall a sz, A_QUAR <= a -> a + sz <= KHIGHSHADOW_BEG ->
  (a + sz <= AIMG_HI \/ (KLOWSHADOW_BEG <= a /\ a + sz <= SH AIMG_HI)) -> disjoint_from W a sz.
Hypothesis S3 : forall r a b, In r (rt_nd2 st) -> fst r <= a -> a <= b -> b <= snd r -> disjoint_from W (SH a) (SH b - SH a).
Hypothesis S4 : forall r a sz, In r (rt_nd2 st) -> fst r <= a -> a + sz <= snd r ->
  (snd r <= T \/ T + 4096 <= fst r \/ a + sz <= T + T_STATS \/ T + T_UNWINDING <= a) -> disjoint_from W a sz.

(* [comment removed for export] *)
Lemma prim_vs_t : P + PRIM_RES_SIZE <= T \/ T + 4096 <= P.
Proof.
  pose proof (prim_vs_tail st WF (T, T + 4096)) as D. cbn [fst snd] in D.
  specialize (D ltac:(apply in_or_app; left; apply in_map_iff; exists (st_t st, 4096); split; [reflexivity| exact (wb_t_loose st (wf_base_ok st WF))])). lia.
Qed.
Lemma SZprim : forall a sz, P <= a -> a + sz <= P + PRIM_RES_SIZE -> disjoint_from W a sz.
Proof.
  intros a sz H1 H2. apply (S4 (P, P + PRIM_RES_SIZE)); [left; reflexivity| exact H1| exact H2|]. cbn [fst snd]. pose proof prim_vs_t. lia.
Qed.
Lemma SZprim_sh : forall a b, P <= a -> a <= b -> b <= P + PRIM_RES_SIZE -> disjoint_from W (SH a) (SH b - SH a).
Proof. intros a b H1 H2 H3. apply (S3 (P, P + PRIM_RES_SIZE)); [left; reflexivity| exact H1| exact H2| exact H3]. Qed.
(* [comment removed for export] *)
Lemma sec_vs_t : forall e, In e (st_sec st) -> fst e + smapsize (snd e) <= T \/ T + 4096 <= fst e.
Proof.
  intros e He. pose proof (wb_pwdj st (wf_base_ok st WF)) as PW. rewrite rt_ranges_tail in PW. cbn [app] in PW.
  destruct PW as [_ [_ PW]].
  pose proof (pwdj_app_disj _ _ (T, T + 4096) (fst e, fst e + smapsize (snd e)) PW
                ltac:(apply in_map_iff; exists (st_t st, 4096); split; [reflexivity| exact (wb_t_loose st (wf_base_ok st WF))])
                ltac:(apply in_or_app; left; apply in_map_iff; exists e; auto)) as D.
  cbn [fst snd] in D. lia.
Qed.
Lemma SZsec : forall e a sz, In e (st_sec st) -> fst e <= a -> a + sz <= fst e + smapsize (snd e) -> disjoint_from W a sz.
Proof.
  intros e a sz He H1 H2. apply (S4 (fst e, fst e + smapsize (snd e))); [| exact H1| exact H2| cbn [fst snd]; pose proof (sec_vs_t e He); lia].
  right. apply in_or_app. right. apply in_map_iff. exists e. auto.
Qed.
Lemma SZsec_sh : forall e a b, In e (st_sec st) -> fst e <= a -> a <= b -> b <= fst e + smapsize (snd e) -> disjoint_from W (SH a) (SH b - SH a).
Proof.
  intros e a b He H1 H2 H3. apply (S3 (fst e, fst e + smapsize (snd e))); [| exact H1| exact H2| exact H3].
  right. apply in_or_app. right. apply in_map_iff. exists e. auto.
Qed.
Lemma SZloose : forall b k a sz, In (b, k) (st_loose0 st) -> b <= a -> a + sz <= b + k ->
  (b + k <= T \/ T + 4096 <= b \/ a + sz <= T + T_STATS \/ T + T_UNWINDING <= a) -> disjoint_from W a sz.
Proof.
  intros b k a sz Hin H1 H2 H3. apply (S4 (b, b + k)); [| exact H1| exact H2| exact H3].
  right. apply in_or_app. left. apply in_map_iff. exists (b, k). auto.
Qed.

Local Ltac s12 := first [ apply S1; rewrite ?A_SECONDARY_val; unfold AIMG_LO; lia
                         | apply S2; rewrite ?A_QUAR_val, ?KHIGHSHADOW_BEG_val; change (SH AIMG_HI) with 0x800b7e00; unfold AIMG_HI, KLOWSHADOW_BEG; lia ].

(* [comment removed for export] *)
Lemma SZ_link : WOK_link W.
Proof. split; [intros a v Hin; destruct (alink_range a v Hin); s12| unfold A_GLOBREC_LO, A_GLOBREC_HI; s12]. Qed.
Lemma SZ_consts : WOK_consts W.
Proof.
  unfold WOK_consts.
  unfold A_SHADOW_OFF_CELL, A_UAR_OPTION, A_AFLAGS, A_CFLAGS, A_PAGESIZE_CACHED, A_KHIGHMEMEND, A_KMIDMEMBEG, A_KMIDMEMEND,
    A_ASAN_INITED, A_MCS, A_CAN_POISON, A_TSD_KEY_INITED, A_TSD_KEY, A_MAY_RETURN_NULL, A_ALLOC_OOM, A_DYING, A_VERBOSITY,
    A_MFHOOKS, A_LSAN_DISABLE, A_IA_INITED, AHOOKS, A_LIBC_PAGESIZE, A_MU_GLOBALS, A_GLOBALS_REGD, A_TPCG_INITED, A_TOOLNAME, A_PRINTF_CB, A_EMB, ATP.
  repeat lazymatch goal with |- _ /\ _ => split | _ => idtac end; s12.
Qed.
Lemma SZ_ia : WOK_ia W.
Proof. intros i Hi. unfold A_IA_MAP1. s12. Qed.
Lemma SZ_lowshadow : WOK_lowshadow W.
Proof. intros g Hg. change (SH AIMG_LO) with 0x7fffa000 in Hg. change (SH AIMG_HI) with 0x800b7e00 in Hg. s12. Qed.
(* [comment removed for export] *)
Hypothesis S5 : forall b a sz, In b (d_nblocks (st_depot st)) -> b <= a -> a + sz <= b + NODEBLOCK_SIZE -> disjoint_from W a sz.
Lemma SZ_depot : WOK_depot st W.
Proof.
  pose proof (wf_depot_ok st WF) as WD. unfold WOK_depot.
  unfold A_DEPOT, A_DEPOT_NIDS, A_DEPOT_MAP1, A_STACKSTORE, DEPOT_TAB_LOG, SSTORE_NBLOCKS in *.
  split; [| split; [| split; [| split; [| split]]]].
  - intros i Hi. s12.
  - s12.
  - intros k Hk. s12.
  - intros id Hid.
    set (q := id / DEPOT_L2_NODES). set (b := nthz (d_nblocks (st_depot st)) q 0).
    assert (Hq : 0 <= q < d_nnb (st_depot st)).
    { pose proof (wd_nnb st WD) as E. unfold d_nnb in *. rewrite E. subst q. unfold DEPOT_L2_NODES. Z.div_mod_to_equations. nia. }
    assert (Hb : In b (d_nblocks (st_depot st))) by (subst b; apply nthz_In; unfold d_nnb in Hq; exact Hq).
    assert (ADDR : dnode_addr (st_depot st) id = b + DEPOT_NODE_SZ * (id mod DEPOT_L2_NODES)) by reflexivity.
    rewrite ADDR. unfold DEPOT_NODE_SZ, DEPOT_L2_NODES, NODEBLOCK_SIZE in *.
    apply (S5 b); [exact Hb| Z.div_mod_to_equations; lia| Z.div_mod_to_equations; lia].
  - s12.
  - intros b Hb. s12.
Qed.

(* [comment removed for export] *)
Lemma SZ_rinfo : WOK_rinfo st W.
Proof. intros c Hc. pose proof (ris_range st WF) as (X1 & X2 & X3 & X4). unfold KNUMCLASSES in Hc. apply SZprim; unfold rinfo; lia. Qed.
Lemma SZ_regions : WOK_regions st W.
Proof.
  intros c Hc. pose proof (region_facts st WF c Hc) as RF. cbn zeta in RF.
  destruct RF as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10).
  assert (FB : fabeg st c = rbeg st c + KFREEARRAY_OFF) by reflexivity.
  unfold KHIGHMEM_BEG, KREGIONSIZE, KFREEARRAY_OFF, KFREEARRAY_SIZE in *.
  split.
  - intros i Hi. pose proof (wc_num_freed st c (wf_class_ok st WF c Hc)) as NF. apply SZprim; lia.
  - replace ((r_mapped (rg st c) - r_allocated (rg st c)) / 8) with (SH (rbeg st c + r_mapped (rg st c)) - SH (rbeg st c + r_allocated (rg st c)))
      by (rewrite !rt_SH_aligned_add by exact X8; Z.div_mod_to_equations; lia).
    apply SZprim_sh; lia.
Qed.
Lemma SZ_avail : WOK_avail st W.
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
  pose proof (csize_pos c ltac:(unfold KNUMCLASSES in Hc; lia)) as SP. pose proof (csize_mod32 c ltac:(unfold KNUMCLASSES in Hc; lia)) as SM.
  assert (AL : cptr_addr st c k mod 8 = 0).
  { apply (mod0_of_sub _ (rbeg st c) 8 ltac:(lia)); [| exact X8]. apply (mod0_trans _ 8 (csize c)); [lia|lia| apply (mod0_trans _ 8 32); [lia|lia|reflexivity|exact SM]| exact C3]. }
  replace (csize c / 8) with (SH (cptr_addr st c k + csize c) - SH (cptr_addr st c k)) by (rewrite rt_SH_aligned_add by exact AL; lia).
  unfold KHIGHMEM_BEG, KREGIONSIZE, KFREEARRAY_OFF in *. apply SZprim_sh; lia.
Qed.

(* [comment removed for export] *)
Lemma SZt : forall a sz, T <= a -> a + sz <= T + T_STATS -> disjoint_from W a sz.
Proof.
  intros a sz H1 H2. eapply SZloose; [exact (wb_t_loose st (wf_base_ok st WF))| lia| unfold T_STATS in *; lia| lia].
Qed.
Lemma SZ_cache : WOK_cache st W.
Proof.
  intros c Hc. pose proof (wc_cache_max st c (wf_class_ok st WF c Hc)) as CM. pose proof (cmaxcount_le16 c). unfold KNUMCLASSES in Hc.
  split.
  - apply SZt; unfold pcaddr, acache, T_ACACHE, T_STATS; lia.
  - intros i Hi. apply SZt; unfold pcaddr, acache, T_ACACHE, T_STATS; lia.
Qed.
Lemma SZ_thread : WOK_thread st W.
Proof.
  unfold WOK_thread.
  split; [apply SZt; unfold T_STATS; lia|].
  split; [apply SZt; unfold qcache_t, T_QCACHE, T_STATS; lia|].
  split; [eapply SZloose; [exact (wb_t_loose st (wf_base_ok st WF))| unfold T_UNWINDING; lia| unfold T_UNWINDING; lia| lia]|].
  destruct (wb_ctx_loose st (wf_base_ok st WF)) as (cb & ck & CL1 & CL2 & CL3). pose proof (wb_ctx_t st (wf_base_ok st WF)) as CT.
  destruct (loose0_range st WF _ _ CL1) as (Q1 & Q2 & Q3 & Q4).
  assert (CTX : forall a sz, st_ctx st <= a -> a + sz <= st_ctx st + 160 -> disjoint_from W a sz).
  { intros a sz H1 H2.
    (* [comment removed for export] *)
    eapply SZloose; [exact CL1| lia| lia|]. unfold T_STATS, T_UNWINDING. lia. }
  split; [apply CTX; unfold CTX_TID; lia|].
  split; [apply CTX; unfold CTX_THREAD; lia|].
  unfold A_TSD_PTR, A_TSD_MAIN, A_DTV_PTR, A_DTV, A_TLSMOD, A_FSTLS_CELL, A_DTLS_OFF, ATP in *.
  split; [s12|]. split; [s12|]. split; [s12|]. split; [s12|]. split; [s12|]. split; [s12|].
  destruct (wb_dtls_loose st (wf_base_ok st WF)) as (db & dk & DL1 & DL2 & DL3). pose proof (wb_dtls_t st (wf_base_ok st WF)) as DT.
  eapply SZloose; [exact DL1| lia| lia| unfold T_STATS, T_UNWINDING; lia].
Qed.

(* [comment removed for export] *)
Lemma SZ_block : forall A n, In (A, n) (all_blocks st) -> WOK_block W A n.
Proof.
  intros A n HB.
  pose proof (block_geom st WF A n HB) as (Gn & GA & K & X & Y & CE & L16 & H16 & EA & Gp & Gs). unfold usz in Y. unfold KHIGHMEM_BEG in K.
  pose proof (rz_size_range n) as (Z1 & Z2).
  assert (ASZ : b_hi A n = b_lo A n + asz n) by reflexivity.
  apply WOK_block_intro.
  - intros a sz Ha Hs. destruct (bprim n) eqn:EP.
    + destruct (Gp eq_refl) as (_ & _ & _ & Q1 & Q2 & _). apply SZprim; lia.
    + destruct (Gs eq_refl) as (S1' & T1 & _). eapply (SZsec (b_lo A n, n)); [exact S1'| cbn [fst]; lia| cbn [fst snd]; lia].
  - unfold sh_tot. replace (asz n / 8) with (SH (b_hi A n) - SH (b_lo A n)).
    2:{ rewrite ASZ, rt_SH_aligned_add by (apply (mod0_trans _ 8 16); [lia|lia|reflexivity|exact L16]).
        destruct (bprim n) eqn:EP; [destruct (prim_facts n EP) as (_ & _ & F3 & F4 & F5); rewrite F5 | destruct (sec_facts n EP) as (_ & _ & F3 & _ & F5 & _); rewrite F5]; Z.div_mod_to_equations; lia. }
    destruct (bprim n) eqn:EP.
    + destruct (Gp eq_refl) as (_ & _ & _ & Q1 & Q2 & _). apply SZprim_sh; lia.
    + destruct (Gs eq_refl) as (S1' & T1 & _). eapply (SZsec_sh (b_lo A n, n)); [exact S1'| cbn [fst]; lia| lia| cbn [fst snd]; lia].
  - rewrite EA at 2. unfold sh_left, SEC_HDR, SEC_RZ. destruct (bprim n) eqn:EP.
    + Z.div_mod_to_equations. lia.
    + destruct (sec_facts n EP) as (_ & F2 & _). rewrite F2. cbn. lia.
Qed.
Lemma SZ_live : WOK_live st W.
Proof. intros A n Hin. apply SZ_block. unfold all_blocks; apply in_or_app; left; exact Hin. Qed.
Lemma SZ_quar : WOK_quar st W.
Proof. intros A n Hin. apply SZ_block. unfold all_blocks; apply in_or_app; right; exact Hin. Qed.

(* [comment removed for export] *)
Lemma SZ_batches : WOK_batches st W.
Proof.
  intros b Hb.
  destruct (batch_geom st WF b Hb) as (BB & BF & R1 & R2 & AL).
  destruct (wq_batch st (wf_quar_ok st WF) b Hb) as [CNT _].
  pose proof (region_facts st WF 24 ltac:(unfold KNUMCLASSES; lia)) as RF. cbn zeta in RF. destruct RF as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10).
  unfold KHIGHMEM_BEG, KREGIONSIZE, KFREEARRAY_OFF, QBATCH_SIZE, QBATCH_CAP in *.
  split; [| split].
  - apply SZprim; lia.
  - intros i Hi. apply SZprim; lia.
  - assert (AL8 : qb_addr b mod 8 = 0) by (apply (mod0_trans _ 8 32); [lia|lia|reflexivity|exact AL]).
    replace 1024 with (SH (qb_addr b + 8192) - SH (qb_addr b)) by (rewrite rt_SH_aligned_add by exact AL8; change (8192 / 8) with 1024; lia).
    apply SZprim_sh; lia.
Qed.

(* [comment removed for export] *)
Lemma SZ_fs : WOK_fs st W.
Proof.
  pose proof (wb_fs_loose st (wf_base_ok st WF)) as FL. pose proof (t_page st WF) as (_ & _ & _ & TF). unfold framefree in TF.
  assert (OBJ : forall a sz, st_fs st <= a -> a + sz <= st_fs st + FS_TOTAL -> disjoint_from W a sz).
  { intros a sz H1 H2. eapply SZloose; [exact FL| exact H1| exact H2| lia]. }
  unfold WOK_fs. split; [| split; [| split; [| split]]].
  - intros k Hk. apply OBJ; unfold FS_TOTAL; lia.
  - apply OBJ; unfold FS_TOTAL; lia.
  - apply OBJ; unfold FS_TOTAL; lia.
  - intros k pos Hk Hp. pose proof (flags_ok k Hk) as [O1 O2]. apply OBJ; unfold fflag_addr, FS_TOTAL in *; lia.
  - intros F k Hin. pose proof (frame_range st WF F k Hin) as (Hk & X1 & X2 & _). pose proof (fsz_12 k Hk) as (FZ & _).
    assert (8 <= fsz k) by (rewrite FZ; destruct Hk as [-> | ->]; cbn; lia).
    apply OBJ; unfold FS_FRAMES_OFF in *; lia.
Qed.

Theorem sz_others : forall m m', munch W m m' -> wmono bsegs m m' -> RTREP st m -> RTREP_nsec st m'.
Proof.
  intros m m' MU WM HR. unfold RTREP_nsec.
  Local Ltac tapp T st WF W m m' MU WM :=
    first [ eapply (T st WF W m m' MU WM) | eapply (T st W m m' MU WM) | eapply (T st W m m' MU) | eapply (T W m m' MU WM) | eapply (T W m m' MU) ].
  split; [tapp T_link st WF W m m' MU WM; [exact (rr_link st m HR)| apply SZ_link]|].
  split; [tapp T_consts st WF W m m' MU WM; [exact (rr_consts st m HR)| apply SZ_consts]|].
  split; [tapp T_rinfo st WF W m m' MU WM; [exact (rr_rinfo st m HR)| apply SZ_rinfo]|].
  split; [tapp T_regions st WF W m m' MU WM; [exact (rr_regions st m HR)| apply SZ_regions]|].
  split; [tapp T_avail st WF W m m' MU WM; [exact (rr_avail st m HR)| apply SZ_avail]|].
  split; [tapp T_cache st WF W m m' MU WM; [exact (rr_cache st m HR)| apply SZ_cache]|].
  split; [tapp T_thread st WF W m m' MU WM; [exact (rr_thread st m HR)| apply SZ_thread]|].
  split; [tapp T_live st WF W m m' MU WM; [exact (rr_live st m HR)| apply SZ_live]|].
  split; [tapp T_quar st WF W m m' MU WM; [exact (rr_quar st m HR)| apply SZ_quar]|].
  split; [tapp T_batches st WF W m m' MU WM; [exact (rr_batches st m HR)| apply SZ_batches]|].
  split; [tapp T_depot st WF W m m' MU WM; [exact (rr_depot st m HR)| apply SZ_depot]|].
  split; [tapp T_fs st WF W m m' MU WM; [exact (rr_fs st m HR)| apply SZ_fs]|].
  split; [tapp T_ia st WF W m m' MU WM; [exact (rr_ia st m HR)| apply SZ_ia]|].
  tapp T_lowshadow st WF W m m' MU WM; [exact (rr_lowshadow st m HR)| apply SZ_lowshadow].
Qed.
End SZ.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sz_ok (st : rtstate) (FR : list (Z * Z)) (iv : Z * Z) : Prop :=
  CEIL <= fst iv
  \/ (A_SECONDARY <= fst iv /\ snd iv <= A_QUAR)
  \/ (st_t st + T_STATS <= fst iv /\ snd iv <= st_t st + T_UNWINDING)
  \/ (st_pa st <= fst iv /\ snd iv <= st_pa st + PTRARR_RES_SIZE)
  \/ (exists f, In f FR /\ fst f <= fst iv /\ snd iv <= snd f)
  \/ (exists f, In f FR /\ SH (fst f) <= fst iv /\ snd iv <= SH (snd f)).

Section SZI.
Variable st : rtstate.
Hypothesis WF : RTWF st.
Variables (W FR : list (Z * Z)).
Hypothesis HW : Forall (sz_ok st FR) W.
Hypothesis HFR : fresh_ok st FR.
Hypothesis HFRceil : forall f, In f FR -> snd f <= CEIL.
Local Abbreviation T := (st_t st).

Lemma pa_facts : ablk (st_pa st) (st_pa st + PTRARR_RES_SIZE) /\ st_pa st + PTRARR_RES_SIZE <= CEIL.
Proof. pose proof (pa_range st WF) as (P1 & P2 & _). unfold CEIL. auto. Qed.
Lemma t_facts : oclr T (T + 4096) /\ T + 4096 <= CEIL.
Proof. pose proof (t_range st WF). unfold CEIL. auto. Qed.

Local Ltac kinds H3 :=
  unfold sz_ok in H3; cbn [fst snd] in H3;
  destruct H3 as [H3|[H3|[H3|[H3|[(f & Hf & H3)|(f & Hf & H3)]]]]];
  rewrite ?A_SECONDARY_val, ?A_QUAR_val, ?KHIGHSHADOW_BEG_val in *;
  unfold CEIL, KHIGHMEM_BEG, KHIGHSHADOW_BEG, T_STATS, T_UNWINDING, NODEBLOCK_SIZE, PTRARR_RES_SIZE in *.

(* [comment removed for export] *)
Lemma fr_facts : forall f, In f FR ->
  ablk (fst f) (snd f) /\ snd f <= CEIL /\ 0x800b7e00 <= SH (fst f) /\ SH (snd f) <= 0x10007fef8000
  /\ forall r, In r (rt_ranges st) -> snd f <= fst r \/ snd r <= fst f.
Proof.
  intros f Hf. destruct (HFR f Hf) as [F1 F2]. pose proof (HFRceil f Hf) as F3.
  pose proof (rt_SH_mono _ _ (ablk_img _ _ F1)) as M1. change (SH AIMG_HI) with 0x800b7e00 in M1.
  pose proof (rt_SH_mono _ _ F3) as M2. pose proof SH_CEIL_range as SC.
  split; [exact F1|]. split; [exact F3|]. split; [exact M1|]. split; [lia| exact F2].
Qed.

Lemma szi_S1 : forall a sz, AIMG_LO <= a -> a + sz <= A_SECONDARY -> disjoint_from W a sz.
Proof.
  intros a sz H0 H. pose proof pa_facts as [PA1 PA2]. pose proof t_facts as [T1 T2].
  induction W as [|[lo hi] W' IH]; [exact I|]. inversion HW as [|x l H3 H4]; subst. cbn. split; [| apply IH; exact H4].
  kinds H3; try (clear - H0 H H3 PA1 PA2 T1 T2; blia).
  - destruct (fr_facts f Hf) as (F1 & F2 & F3 & F4 & _). clear - H0 H H3 F1. blia.
  - destruct (fr_facts f Hf) as (F1 & F2 & F3 & F4 & _). clear - H0 H H3 F3. lia.
Qed.
Lemma szi_S2 : forall a sz, A_QUAR <= a -> a + sz <= KHIGHSHADOW_BEG ->
  (a + sz <= AIMG_HI \/ (KLOWSHADOW_BEG <= a /\ a + sz <= SH AIMG_HI)) -> disjoint_from W a sz.
Proof.
  intros a sz H1 H2 HZ. change (SH AIMG_HI) with 0x800b7e00 in HZ. pose proof pa_facts as [PA1 PA2]. pose proof t_facts as [T1 T2].
  induction W as [|[lo hi] W' IH]; [exact I|]. inversion HW as [|x l H3 H4]; subst. cbn. split; [| apply IH; exact H4].
  kinds H3; try (clear - H1 H2 HZ H3 PA1 PA2 T1 T2; blia).
  - destruct (fr_facts f Hf) as (F1 & F2 & F3 & F4 & _). clear - H1 H2 HZ H3 F1. blia.
  - destruct (fr_facts f Hf) as (F1 & F2 & F3 & F4 & _). clear - H1 H2 HZ H3 F3 F4. blia.
Qed.
Lemma szi_S3 : forall r a b, In r (rt_nd2 st) -> fst r <= a -> a <= b -> b <= snd r -> disjoint_from W (SH a) (SH b - SH a).
Proof.
  intros r a b Hr H1 H2 H3. pose proof pa_facts as [PA1 PA2]. pose proof t_facts as [T1 T2].
  pose proof (wb_ranges st (wf_base_ok st WF) r (rt_nd2_In st r Hr)) as (R1 & R2 & R3 & R4).
  pose proof (rt_SH_mono a b H2) as M1.
  pose proof (rt_SH_mono b (@CEIL ACEIL) ltac:(unfold CEIL; lia)) as M2. pose proof SH_CEIL_range as SC.
  (* [comment removed for export] *)
  assert (M0 : 0x7fff8000 <= SH a) by (unfold SH, SHADOW_OFFSET; destruct (oclr_lin _ _ R1 ltac:(lia)) as (L1 & _); Z.div_mod_to_equations; lia).
  induction W as [|[lo hi] W' IH]; [exact I|]. inversion HW as [|x l K3 K4]; subst. cbn. split; [| apply IH; exact K4].
  kinds K3; try (clear - M0 M1 M2 SC K3 PA1 PA2 T1 T2; blia).
  - destruct (fr_facts f Hf) as (F1 & F2 & F3 & F4 & _). clear - M0 M1 M2 SC K3 F1. blia.
  - (* [comment removed for export] *)
    destruct (fr_facts f Hf) as (F1 & F2 & F3 & F4 & F5). destruct (F5 r (rt_nd2_In st r Hr)) as [D|D].
    + right. pose proof (rt_SH_mono (snd f) a ltac:(lia)). lia.
    + left. pose proof (rt_SH_mono b (fst f) ltac:(lia)). lia.
Qed.
Lemma szi_S4 : forall r a sz, In r (rt_nd2 st) -> fst r <= a -> a + sz <= snd r ->
  (snd r <= T \/ T + 4096 <= fst r \/ a + sz <= T + T_STATS \/ T + T_UNWINDING <= a) -> disjoint_from W a sz.
Proof.
  intros r a sz Hr H1 H2 HT. pose proof pa_facts as [PA1 PA2]. pose proof t_facts as [T1 T2].
  pose proof (wb_ranges st (wf_base_ok st WF) r (rt_nd2_In st r Hr)) as (R1 & R2 & R3 & R4).
  (* [comment removed for export] *)
  assert (RPA : snd r <= st_pa st \/ st_pa st + PTRARR_RES_SIZE <= fst r).
  { pose proof (wb_pwdj st (wf_base_ok st WF)) as PW. rewrite rt_ranges_tail in PW. cbn [app] in PW. destruct PW as [F0 [F1 _]].
    destruct Hr as [<-|Hr].
    - inversion F0 as [|y l Y _]; subst. cbn [fst snd] in Y |- *. lia.
    - rewrite Forall_forall in F1.
      specialize (F1 r ltac:(rewrite app_assoc; apply in_or_app; left; exact Hr)). cbv beta in F1. cbn [fst snd] in F1. lia. }
  induction W as [|[lo hi] W' IH]; [exact I|]. inversion HW as [|x l K3 K4]; subst. cbn. split; [| apply IH; exact K4].
  kinds K3; try (clear - H1 H2 HT RPA R1 R2 R3 K3; blia).
  - destruct (fr_facts f Hf) as (F1 & F2 & F3 & F4 & F5). destruct (F5 r (rt_nd2_In st r Hr)); lia.
  - destruct (fr_facts f Hf) as (F1 & F2 & F3 & F4 & _). clear - H1 H2 R1 R2 K3 F3 F4. blia.
Qed.
Lemma szi_S5 : forall b a sz, In b (d_nblocks (st_depot st)) -> b <= a -> a + sz <= b + NODEBLOCK_SIZE -> disjoint_from W a sz.
Proof.
  intros b a sz Hb H1 H2. pose proof pa_facts as [PA1 PA2]. pose proof t_facts as [T1 T2].
  destruct (nb_range st WF b Hb) as (N1 & N2 & N3).
  pose proof (wb_pwdj st (wf_base_ok st WF)) as PW. rewrite rt_ranges_nd in PW.
  assert (INB : In (b, b + NODEBLOCK_SIZE) (NBR st ++ SBR st)) by (apply in_or_app; left; unfold NBR; apply in_map_iff; exists b; auto).
  pose proof (pwdj_app_disj _ _ (st_pa st, st_pa st + PTRARR_RES_SIZE) _ PW ltac:(right; left; reflexivity) INB) as DPA.
  pose proof (pwdj_app_disj _ _ (st_t st, st_t st + 4096) _ PW
                ltac:(right; right; apply in_or_app; left; apply in_map_iff; exists (st_t st, 4096); split; [reflexivity| exact (wb_t_loose st (wf_base_ok st WF))]) INB) as DT.
  cbn [fst snd] in DPA, DT.
  assert (INR : In (b, b + NODEBLOCK_SIZE) (rt_ranges st)) by (rewrite rt_ranges_nd; apply in_or_app; right; exact INB).
  induction W as [|[lo hi] W' IH]; [exact I|]. inversion HW as [|x l K3 K4]; subst. cbn. split; [| apply IH; exact K4].
  kinds K3; try (clear - H1 H2 N1 N2 DPA DT K3; blia).
  - destruct (fr_facts f Hf) as (F1 & F2 & F3 & F4 & F5). destruct (F5 _ INR); cbn [fst snd] in *; lia.
  - destruct (fr_facts f Hf) as (F1 & F2 & F3 & F4 & _). clear - H1 H2 N1 N2 K3 F3 F4. blia.
Qed.

Theorem szi_others : forall m m', munch W m m' -> wmono bsegs m m' -> RTREP st m -> RTREP_nsec st m'.
Proof. intros m m' MU WM HR. exact (sz_others st WF W szi_S1 szi_S2 szi_S3 szi_S4 szi_S5 m m' MU WM HR). Qed.
End SZI.

(* [comment removed for export] *)
Lemma sz_ok_stack : forall st FR lo hi, CEIL <= lo -> sz_ok st FR (lo, hi).
Proof. intros. left. cbn. assumption. Qed.
Lemma sz_ok_static : forall st FR lo hi, A_SECONDARY <= lo -> hi <= A_QUAR -> sz_ok st FR (lo, hi).
Proof. intros. right; left. cbn. auto. Qed.
Lemma sz_ok_stats : forall st FR lo hi, st_t st + T_STATS <= lo -> hi <= st_t st + T_UNWINDING -> sz_ok st FR (lo, hi).
Proof. intros. right; right; left. cbn. auto. Qed.
Lemma sz_ok_pa : forall st FR lo hi, st_pa st <= lo -> hi <= st_pa st + PTRARR_RES_SIZE -> sz_ok st FR (lo, hi).
Proof. intros. right; right; right; left. cbn. auto. Qed.
Lemma sz_ok_fresh : forall st FR f lo hi, In f FR -> fst f <= lo -> hi <= snd f -> sz_ok st FR (lo, hi).
Proof. intros. do 4 right; left. exists f. cbn. auto. Qed.
Lemma sz_ok_fresh_sh : forall st FR f lo hi, In f FR -> SH (fst f) <= lo -> hi <= SH (snd f) -> sz_ok st FR (lo, hi).
Proof. intros. do 5 right. exists f. cbn. auto. Qed.


End CeilWrap.
