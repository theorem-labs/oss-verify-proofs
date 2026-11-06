(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_secz.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_secz.RT_artZ.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RT_sec RT_secz.
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

Section HZ.
Variable st : rtstate.
Hypothesis WF : RTWF st.
Variable W : list (Z * Z).
(* [comment removed for export] *)
Variables (M nM : Z).
Hypothesis HM : In (M, nM) (st_sec st).
Hypothesis HW : Forall (fun iv : Z * Z => M <= fst iv /\ snd iv <= M + 4096) W.

(* [comment removed for export] *)
Lemma M_range : ablk M (M + smapsize nM) /\ M + smapsize nM <= CEIL /\ 8192 <= smapsize nM.
Proof.
  pose proof (wb_ranges st (wf_base_ok st WF) (M, M + smapsize nM)) as R. cbn [fst snd] in R.
  specialize (R ltac:(unfold rt_ranges; do 2 right; rewrite !in_app_iff; right; left; apply in_map_iff; exists (M, nM); auto)).
  destruct (ws_entry st (wf_sec_ok st WF) _ HM) as (_ & K & _). cbn [snd] in K. pose proof (smapsize_pos nM ltac:(lia)).
  pose proof (sec_range st WF (M, nM) HM) as (S1 & S2 & _). cbn [fst snd] in S1, S2. unfold CEIL. split; [exact S1| lia].
Qed.
(* [comment removed for export] *)
Lemma HZdisj : forall a sz, (a + sz <= M \/ M + 4096 <= a) -> disjoint_from W a sz.
Proof.
  intros a sz H. induction W as [|[lo hi] W' IH]; [exact I|]. inversion HW as [|x l H1 H2]; subst. cbn [fst snd] in H1. cbn. split; [lia| apply IH; exact H2].
Qed.
Lemma Hlow : forall a sz, a + sz <= A_STACKSTORE -> disjoint_from W a sz.
Proof. intros a sz H. apply HZdisj. left. pose proof M_range as (R1 & _). pose proof (ablk_img _ _ R1). rewrite A_STACKSTORE_val in H. unfold AIMG_HI in *. lia. Qed.
Lemma Hmid : forall a sz, A_DEPOT_END <= a -> a + sz <= KHIGHMEM_BEG -> (a + sz <= AIMG_HI \/ KLOWSHADOW_BEG <= a) -> disjoint_from W a sz.
Proof.
  intros a sz H1 H2 H3. apply HZdisj. pose proof M_range as (R1 & _ & R3). pose proof (ablk_img _ _ R1). pose proof (ablk_disj_band _ _ R1).
  destruct H3 as [H3|H3]; [left; lia|]. destruct H0 as [H0|H0]; [right; lia| left; lia].
Qed.
(* [comment removed for export] *)
Lemma Hheap : forall r a sz, In r (rt_ranges st) -> r <> (M, M + smapsize nM) -> fst r <= a -> a + sz <= snd r -> disjoint_from W a sz.
Proof.
  intros r a sz Hr NE H1 H2. apply HZdisj. pose proof M_range as (R1 & R2 & R3).
  assert (HMr : In (M, M + smapsize nM) (rt_ranges st)).
  { unfold rt_ranges. do 2 right. rewrite !in_app_iff. right. left. apply in_map_iff. exists (M, nM). auto. }
  destruct (pwdj_In _ _ _ (wb_pwdj st (wf_base_ok st WF)) Hr HMr) as [E|D]; [exfalso; exact (NE E)|]. cbn [fst snd] in D. lia.
Qed.

Local Abbreviation P := (st_pbase st).

(* [comment removed for export] *)
Lemma head_neq : forall r, In r ((st_pbase st, st_pbase st + PRIM_RES_SIZE) :: (st_pa st, st_pa st + PTRARR_RES_SIZE) :: map (fun e => (fst e, fst e + snd e)) (st_loose0 st)) ->
  r <> (M, M + smapsize nM).
Proof.
  intros r Hr E. subst r. pose proof (PW_tail st WF) as (PW & F1 & F2). pose proof M_range as (R1 & R2 & R3).
  assert (INs : In (M, M + smapsize nM) (map (fun e : Z * Z => (fst e, fst e + smapsize (snd e))) (st_sec st))) by (apply in_map_iff; exists (M, nM); auto).
  destruct Hr as [Hr|[Hr|Hr]].
  - rewrite Forall_forall in F1. specialize (F1 (M, M + smapsize nM) ltac:(right; apply in_or_app; right; apply in_or_app; left; exact INs)). cbn [fst snd] in F1.
    injection Hr; intros. pose proof (P_range st WF) as (P1 & P2 & P3). unfold PRIM_RES_SIZE, KSPACESIZE in *. lia.
  - rewrite Forall_forall in F2. specialize (F2 (M, M + smapsize nM) ltac:(apply in_or_app; right; apply in_or_app; left; exact INs)). cbn [fst snd] in F2.
    injection Hr; intros. unfold PTRARR_RES_SIZE in *. lia.
  - pose proof (pwdj_app_disj _ _ (M, M + smapsize nM) (M, M + smapsize nM) PW Hr ltac:(apply in_or_app; left; exact INs)) as D. cbn [fst snd] in D. lia.
Qed.
Lemma HZprim : forall a sz, P <= a -> a + sz <= P + PRIM_RES_SIZE -> disjoint_from W a sz.
Proof. intros a sz H1 H2. apply (Hheap (P, P + PRIM_RES_SIZE)); [left; reflexivity| apply head_neq; left; reflexivity| exact H1| exact H2]. Qed.
Lemma HZpa : forall a sz, st_pa st <= a -> a + sz <= st_pa st + PTRARR_RES_SIZE -> disjoint_from W a sz.
Proof. intros a sz H1 H2. apply (Hheap (st_pa st, st_pa st + PTRARR_RES_SIZE)); [right; left; reflexivity| apply head_neq; right; left; reflexivity| exact H1| exact H2]. Qed.
Lemma HZloose : forall b k a sz, In (b, k) (st_loose0 st) -> b <= a -> a + sz <= b + k -> disjoint_from W a sz.
Proof.
  intros b k a sz Hin H1 H2. apply (Hheap (b, b + k)); [| apply head_neq; right; right; apply in_map_iff; exists (b, k); auto| exact H1| exact H2].
  unfold rt_ranges. right; right. apply in_or_app. left. apply in_map_iff. exists (b, k). auto.
Qed.
(* [comment removed for export] *)
Lemma HZsec : forall e a sz, In e (st_sec st) -> fst e <> M -> fst e <= a -> a + sz <= fst e + smapsize (snd e) -> disjoint_from W a sz.
Proof.
  intros e a sz Hin NE H1 H2. apply (Hheap (fst e, fst e + smapsize (snd e))); [| intros E; injection E; intros; exact (NE ltac:(assumption))| exact H1| exact H2].
  unfold rt_ranges. right; right. rewrite !in_app_iff. right. left. apply in_map_iff. exists e. auto.
Qed.
(* [comment removed for export] *)
Lemma HZnb : forall b a sz, In b (d_nblocks (st_depot st)) -> b <= a -> a + sz <= b + NODEBLOCK_SIZE -> disjoint_from W a sz.
Proof.
  intros b a sz Hb H1 H2. pose proof M_range as (R1 & R2 & R3). apply (Hheap (b, b + NODEBLOCK_SIZE)); [| | exact H1| exact H2].
  - unfold rt_ranges. right; right. rewrite !in_app_iff. right. right. left. apply in_map_iff. exists b. auto.
  - intros E. pose proof (wb_pwdj st (wf_base_ok st WF)) as PW. rewrite rt_ranges_nd in PW. apply pwdj_app_r in PW.
    assert (INs : In (M, M + smapsize nM) (rt_nd st)) by (unfold rt_nd; right; right; apply in_or_app; right; apply in_map_iff; exists (M, nM); auto).
    pose proof (wb_pwdj st (wf_base_ok st WF)) as PW2. rewrite rt_ranges_nd in PW2.
    pose proof (pwdj_app_disj _ _ (M, M + smapsize nM) (b, b + NODEBLOCK_SIZE) PW2 INs ltac:(apply in_or_app; left; unfold NBR; apply in_map_iff; exists b; auto)) as D.
    cbn [fst snd] in D. injection E; intros. unfold NODEBLOCK_SIZE in *. lia.
Qed.
(* [comment removed for export] *)
Lemma HZsh : forall x k, 0 <= x -> 0 <= k -> x + 8 * k <= CEIL -> disjoint_from W (SH x) k.
Proof.
  intros x k H0 Hk Hx. apply Hmid; rewrite ?A_DEPOT_END_val; unfold SH, SHADOW_OFFSET, CEIL, KHIGHMEM_BEG, KLOWSHADOW_BEG, AIMG_HI in *; Z.div_mod_to_equations; lia.
Qed.
Lemma HZsh2 : forall lo hi, 0 <= lo -> lo <= hi -> hi <= CEIL -> disjoint_from W (SH lo) (SH hi - SH lo).
Proof.
  intros lo hi H0 H1 H2. apply Hmid; rewrite ?A_DEPOT_END_val; unfold SH, SHADOW_OFFSET, CEIL, KHIGHMEM_BEG, KLOWSHADOW_BEG, AIMG_HI in *; Z.div_mod_to_equations; lia.
Qed.

Local Ltac lowmid := first [ apply Hlow; rewrite ?A_STACKSTORE_val; lia | apply Hmid; rewrite ?A_DEPOT_END_val; unfold KHIGHMEM_BEG, KLOWSHADOW_BEG, AIMG_HI; lia ].

(* [comment removed for export] *)
Lemma HZ_link : WOK_link W.
Proof.
  split; [intros a v Hin; destruct (alink_range a v Hin); lowmid| unfold A_GLOBREC_LO, A_GLOBREC_HI; lowmid].
Qed.
Lemma HZ_consts : WOK_consts W.
Proof.
  unfold WOK_consts.
  unfold A_SHADOW_OFF_CELL, A_UAR_OPTION, A_AFLAGS, A_CFLAGS, A_PAGESIZE_CACHED, A_KHIGHMEMEND, A_KMIDMEMBEG, A_KMIDMEMEND,
    A_ASAN_INITED, A_MCS, A_CAN_POISON, A_TSD_KEY_INITED, A_TSD_KEY, A_MAY_RETURN_NULL, A_ALLOC_OOM, A_DYING, A_VERBOSITY,
    A_MFHOOKS, A_LSAN_DISABLE, A_IA_INITED, AHOOKS, A_LIBC_PAGESIZE, A_MU_GLOBALS, A_GLOBALS_REGD, A_TPCG_INITED, A_TOOLNAME, A_PRINTF_CB, A_EMB, ATP.
  repeat lazymatch goal with |- _ /\ _ => split | _ => idtac end; lowmid.
Qed.
Lemma HZ_alloc : WOK_alloc W.
Proof.
  unfold WOK_alloc, A_ALLOC, A_SECONDARY, A_GSTATS, A_QUAR, A_MAXUSERSZ, A_ALLOC.
  repeat lazymatch goal with |- _ /\ _ => split | _ => idtac end; lowmid.
Qed.
Lemma HZ_ia : WOK_ia W.
Proof. intros i Hi. unfold A_IA_MAP1. lowmid. Qed.
Lemma HZ_lowshadow : WOK_lowshadow W.
Proof.
  intros g Hg. change (SH AIMG_LO) with 0x7fffa000 in Hg. change (SH AIMG_HI) with 0x800b7e00 in Hg. lowmid.
Qed.

(* [comment removed for export] *)
Lemma HZ_rinfo : WOK_rinfo st W.
Proof.
  intros c Hc. pose proof (ris_range st WF) as (X1 & X2 & X3 & X4). unfold KNUMCLASSES in Hc.
  apply HZprim; unfold rinfo; lia.
Qed.
Lemma HZ_regions : WOK_regions st W.
Proof.
  intros c Hc. pose proof (region_facts st WF c Hc) as RF. cbn zeta in RF.
  destruct RF as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10).
  assert (FB : fabeg st c = rbeg st c + KFREEARRAY_OFF) by reflexivity.
  unfold KHIGHMEM_BEG, AIMG_HI, KREGIONSIZE, KFREEARRAY_OFF, KFREEARRAY_SIZE in *.
  split.
  - intros i Hi. pose proof (wc_num_freed st c (wf_class_ok st WF c Hc)) as NF. apply HZprim; lia.
  - apply HZsh; [lia| Z.div_mod_to_equations; lia| unfold CEIL; Z.div_mod_to_equations; lia].
Qed.
Lemma HZ_avail : WOK_avail st W.
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
  unfold KHIGHMEM_BEG, AIMG_HI, KREGIONSIZE, KFREEARRAY_OFF in *.
  apply HZsh; [lia| Z.div_mod_to_equations; lia| unfold CEIL; Z.div_mod_to_equations; lia].
Qed.

(* [comment removed for export] *)
Lemma HZt : forall a sz, st_t st <= a -> a + sz <= st_t st + 4096 -> disjoint_from W a sz.
Proof. intros a sz H1 H2. eapply HZloose; [exact (wb_t_loose st (wf_base_ok st WF))| exact H1| exact H2]. Qed.
Lemma HZ_cache : WOK_cache st W.
Proof.
  intros c Hc. pose proof (wc_cache_max st c (wf_class_ok st WF c Hc)) as CM. pose proof (cmaxcount_le16 c). unfold KNUMCLASSES in Hc.
  split.
  - apply HZt; unfold pcaddr, acache, T_ACACHE; lia.
  - intros i Hi. apply HZt; unfold pcaddr, acache, T_ACACHE; lia.
Qed.
Lemma HZ_thread : WOK_thread st W.
Proof.
  unfold WOK_thread.
  split; [apply HZt; lia|].
  split; [apply HZt; unfold qcache_t, T_QCACHE; lia|].
  split; [apply HZt; unfold T_UNWINDING; lia|].
  destruct (wb_ctx_loose st (wf_base_ok st WF)) as (cb & ck & CL1 & CL2 & CL3).
  split; [eapply HZloose; [exact CL1| unfold CTX_TID; lia| unfold CTX_TID; lia]|].
  split; [eapply HZloose; [exact CL1| unfold CTX_THREAD; lia| unfold CTX_THREAD; lia]|].
  unfold A_TSD_PTR, A_TSD_MAIN, A_DTV_PTR, A_DTV, A_TLSMOD, A_FSTLS_CELL, A_DTLS_OFF, ATP in *.
  split; [lowmid|]. split; [lowmid|]. split; [lowmid|]. split; [lowmid|]. split; [lowmid|]. split; [lowmid|].
  destruct (wb_dtls_loose st (wf_base_ok st WF)) as (db & dk & DL1 & DL2 & DL3).
  eapply HZloose; [exact DL1| lia| lia].
Qed.

(* [comment removed for export] *)
Lemma HZ_block : forall A n, In (A, n) (all_blocks st) -> (bprim n = false -> b_lo A n <> M) -> WOK_block W A n.
Proof.
  intros A n HB NM.
  pose proof (block_geom st WF A n HB) as (Gn & GA & K & X & Y & CE & L16 & H16 & EA & Gp & Gs). unfold usz in Y. unfold KHIGHMEM_BEG, AIMG_HI in K.
  pose proof (rz_size_range n) as (Z1 & Z2).
  assert (OBJ : forall a sz, b_lo A n <= a -> a + sz <= b_hi A n -> disjoint_from W a sz).
  { intros a sz Ha Hs. destruct (bprim n) eqn:EP.
    - destruct (Gp eq_refl) as (_ & _ & _ & Q1 & Q2 & _). apply HZprim; lia.
    - destruct (Gs eq_refl) as (S1 & T1 & _). eapply (HZsec (b_lo A n, n)); [exact S1| cbn [fst]; exact (NM eq_refl)| cbn [fst]; lia| cbn [fst snd]; lia]. }
  apply WOK_block_intro.
  - intros a sz Ha Hs. apply OBJ; lia.
  - unfold sh_tot. assert (EH : b_hi A n = b_lo A n + asz n) by reflexivity.
    assert (ASZ : 0 <= asz n).
    { destruct (bprim n) eqn:EP; [destruct (prim_facts n EP) as (_ & _ & F3 & F4 & F5); rewrite F5 | destruct (sec_facts n EP) as (_ & _ & F3 & _ & F5 & _); rewrite F5]; Z.div_mod_to_equations; lia. }
    apply HZsh; [blia| Z.div_mod_to_equations; lia| unfold CEIL; Z.div_mod_to_equations; lia].
  - rewrite EA at 2. unfold sh_left, SEC_HDR, SEC_RZ. destruct (bprim n) eqn:EP.
    + Z.div_mod_to_equations. lia.
    + destruct (sec_facts n EP) as (_ & F2 & _). rewrite F2. cbn. lia.
Qed.

(* [comment removed for export] *)
Lemma HZ_batches : WOK_batches st W.
Proof.
  intros b Hb.
  destruct (batch_geom st WF b Hb) as (BB & BF & R1 & R2 & AL).
  destruct (wq_batch st (wf_quar_ok st WF) b Hb) as [CNT _].
  pose proof (region_facts st WF 24 ltac:(unfold KNUMCLASSES; lia)) as RF. cbn zeta in RF. destruct RF as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10).
  unfold KHIGHMEM_BEG, AIMG_HI, KREGIONSIZE, KFREEARRAY_OFF, QBATCH_SIZE, QBATCH_CAP in *.
  split; [| split].
  - apply HZprim; lia.
  - intros i Hi. apply HZprim; lia.
  - apply HZsh; [lia| lia| unfold CEIL; lia].
Qed.

(* [comment removed for export] *)
Lemma HZ_ptrarr : (forall i, 0 <= i < nsec st -> disjoint_from W (st_pa st + 8 * i) 8)
  /\ (forall e, In e (st_spend st) -> fst e <> M -> disjoint_from W (fst e) 32).
Proof.
  split.
  - intros i Hi. pose proof (pa_range st WF) as (P1 & P2 & P3 & P4 & P5). apply HZpa; lia.
  - intros e He NE. destruct (ws_spend st (wf_sec_ok st WF) e He) as [HE _].
    destruct e as [mb n]. destruct (ws_entry st (wf_sec_ok st WF) _ HE) as (E1 & _). destruct (sec_facts n E1) as (_ & _ & _ & F4 & _).
    pose proof (usz_le_rounded8 n) as (U1 & _).
    eapply (HZsec (mb, n)); [exact HE| exact NE| cbn [fst]; lia| cbn [fst snd]; unfold usz in *; lia].
Qed.

(* [comment removed for export] *)
Lemma HZ_fs : WOK_fs st W.
Proof.
  pose proof (wb_fs_loose st (wf_base_ok st WF)) as FL.
  assert (OBJ : forall a sz, st_fs st <= a -> a + sz <= st_fs st + FS_TOTAL -> disjoint_from W a sz).
  { intros a sz H1 H2. eapply HZloose; [exact FL| exact H1| exact H2]. }
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
(* [comment removed for export] *)
Lemma hz_wok : WOK_link W /\ WOK_consts W /\ WOK_alloc W /\ WOK_rinfo st W /\ WOK_regions st W /\ WOK_avail st W
  /\ WOK_cache st W /\ WOK_thread st W /\ WOK_batches st W /\ WOK_fs st W /\ WOK_ia W /\ WOK_lowshadow W.
Proof.
  repeat lazymatch goal with |- _ /\ _ => split | _ => idtac end;
  [apply HZ_link| apply HZ_consts| apply HZ_alloc| apply HZ_rinfo| apply HZ_regions| apply HZ_avail| apply HZ_cache| apply HZ_thread
  | apply HZ_batches| apply HZ_fs| apply HZ_ia| apply HZ_lowshadow].
Qed.

(* [comment removed for export] *)
Lemma HZ_depot : WOK_depot st W.
Proof.
  unfold WOK_depot. pose proof M_range as (R1 & R2 & R3).
  split; [intros i Hi; apply HZdisj; left; unfold A_DEPOT, DEPOT_TAB_LOG, KHIGHMEM_BEG, AIMG_HI in *; blia|].
  split; [apply HZdisj; left; unfold A_DEPOT_NIDS, KHIGHMEM_BEG, AIMG_HI in *; blia|].
  split; [intros k Hk; apply HZdisj; left; unfold A_DEPOT_MAP1, KHIGHMEM_BEG, AIMG_HI in *; blia|].
  pose proof (wf_depot_ok st WF) as WD.
  split.
  { intros id Hid.
    set (q := id / DEPOT_L2_NODES). set (bb := nthz (d_nblocks (st_depot st)) q 0).
    assert (Hq : 0 <= q < d_nnb (st_depot st)).
    { pose proof (wd_nnb st WD) as E. unfold d_nnb in *. rewrite E. subst q. unfold DEPOT_L2_NODES. Z.div_mod_to_equations. nia. }
    assert (Hb : In bb (d_nblocks (st_depot st))) by (subst bb; apply nthz_In; unfold d_nnb in Hq; exact Hq).
    assert (ADDR : dnode_addr (st_depot st) id = bb + DEPOT_NODE_SZ * (id mod DEPOT_L2_NODES)) by reflexivity.
    rewrite ADDR. unfold DEPOT_NODE_SZ, DEPOT_L2_NODES, NODEBLOCK_SIZE in *.
    apply (HZnb bb); [exact Hb| Z.div_mod_to_equations; lia| unfold NODEBLOCK_SIZE; Z.div_mod_to_equations; lia]. }
  split; [apply HZdisj; left; unfold A_STACKSTORE, KHIGHMEM_BEG, AIMG_HI in *; blia|].
  intros bb Hb. apply HZdisj. left. unfold A_STACKSTORE, SSTORE_NBLOCKS, KHIGHMEM_BEG, AIMG_HI in *. blia.
Qed.

Variables (m m' : word -> option byte).
Hypothesis MU : munch W m m'.
Hypothesis WM : wmono bsegs m m'.
Theorem hz_xfer : RTREP_nsec st m ->
  R_link m' /\ R_consts st m' /\ R_rinfo st m' /\ R_regions st m' /\ R_avail st m' /\ R_cache st m' /\ R_thread st m'
  /\ R_batches st m' /\ R_depot st m' /\ R_fs st m' /\ R_ia m' /\ R_lowshadow m'
  /\ (forall md A n, In (A, n) (all_blocks st) -> (bprim n = false -> b_lo A n <> M) -> R_block st m md A n -> R_block st m' md A n).
Proof.
  intros (X1 & X2 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X13 & X14 & X15 & X16).
  pose proof hz_wok as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K11 & K14 & K15 & K16).
  pose proof HZ_depot as K13.
  split; [eapply T_link; eassumption|]. split; [eapply T_consts; eassumption|].
  split; [eapply T_rinfo; eassumption|]. split; [eapply T_regions; eassumption|].
  split; [eapply T_avail; eassumption|]. split; [eapply T_cache; eassumption|].
  split; [eapply T_thread; eassumption|]. split; [eapply T_batches; eassumption|].
  split; [eapply T_depot; eassumption|]. split; [eapply T_fs; eassumption|].
  split; [eapply T_ia; eassumption|]. split; [eapply T_lowshadow; eassumption|].
  intros md A n HB NM H. eapply T_block; try eassumption. exact (HZ_block A n HB NM).
Qed.
End HZ.


End CeilWrap.
