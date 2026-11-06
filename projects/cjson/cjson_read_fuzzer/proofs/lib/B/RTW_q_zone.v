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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RTW_m_tpz RTW_m_apz.
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

(* [comment removed for export] *)
(* [comment removed for export] *)

Section G.
Variable st : rtstate.
Hypothesis WF : RTWF st.
Variables (c k : Z).
Hypothesis HcK : 0 <= c < KNUMCLASSES.
Hypothesis Hc1 : 1 <= c.
Hypothesis UK : In k (used_cptrs st c).
Local Abbreviation CH := (cptr_addr st c k).
Local Abbreviation CS := (csize c).

Lemma used_carved : carved_cptr st c k.
Proof. exact (wc_used_carved st c (wf_class_ok st WF c HcK) k UK). Qed.

Lemma used_geom :
  rbeg st c <= CH /\ CH + CS <= rbeg st c + r_allocated (rg st c) /\ r_allocated (rg st c) <= r_mapped (rg st c)
  /\ r_mapped (rg st c) <= KFREEARRAY_OFF /\ KHIGHMEM_BEG <= rbeg st c /\ st_pbase st <= rbeg st c
  /\ rbeg st c + KREGIONSIZE <= st_pbase st + PRIM_RES_SIZE /\ st_pbase st + PRIM_RES_SIZE <= CEIL
  /\ CH mod 32 = 0 /\ 32 <= CS /\ CS mod 32 = 0.
Proof.
  (nelim (carved_chunk st WF c k HcK Hc1 used_carved) 3%nat; intros C1 C2 C3).
  pose proof (region_facts st WF c HcK) as RF. cbn zeta in RF. (nelim RF 10%nat; intros X1 X2 X3 X4 X5 X6 X7 X8 X9 X10).
  (nelim (region_range st WF c HcK) 6%nat; intros R1 R2 R3 R4 R5 R6).
  pose proof (csize_pos c ltac:(unfold KNUMCLASSES in HcK; lia)) as SP. pose proof (csize_mod32 c ltac:(unfold KNUMCLASSES in HcK; lia)) as SM.
  assert (AL : CH mod 32 = 0).
  { apply (mod0_of_sub CH (rbeg st c) 32 ltac:(lia)); [apply (mod0_trans _ 32 CS); [lia|lia|exact SM|exact C3]| apply (mod0_trans _ 32 4096); [lia|lia|reflexivity|exact R4]]. }
  unfold CEIL. repeat split; try lia.
Qed.

(* [comment removed for export] *)
Lemma used_vs_used : forall c' k', 0 <= c' < KNUMCLASSES -> 1 <= c' -> In k' (used_cptrs st c') -> (c', k') <> (c, k) ->
  cptr_addr st c' k' + csize c' <= CH \/ CH + CS <= cptr_addr st c' k'.
Proof.
  intros c' k' Hc' Hc1' UK' NE.
  (nelimp used_geom 11%nat; intros G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11).
  pose proof (wf_class_ok st WF c' Hc') as WC'. pose proof (wc_used_carved st c' WC' k' UK') as CV'.
  (nelim (carved_chunk st WF c' k' Hc' Hc1' CV') 3%nat; intros C1 C2 C3).
  pose proof (wc_mapped_max st c' WC') as MM. pose proof (wc_alloc_mapped st c' WC') as AM.
  destruct (Z.eq_dec c' c) as [->|NC].
  - assert (NK : k' <> k) by (intros ->; apply NE; reflexivity).
    destruct (grid_disj st c k' k HcK Hc1 CV' used_carved NK); [left| right]; lia.
  - destruct (region_disj st c' c (cptr_addr st c' k') CH (cptr_addr st c' k' + csize c') (CH + CS) Hc' HcK NC
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); [left| right]; lia.
Qed.

(* [comment removed for export] *)
Definition chunk_ne (A n : Z) : Prop := bprim n = true -> (pclass n, b_cptr st A n) <> (c, k).
Lemma used_vs_block : forall A n, In (A, n) (all_blocks st) -> chunk_ne A n -> b_hi A n <= CH \/ CH + CS <= b_lo A n.
Proof.
  intros A n HB NE. (nelimp used_geom 11%nat; intros G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11).
  (nelimp (block_geom st WF A n HB) 11%nat; intros _ _ _ _ _ _ _ _ _ Gp Gs).
  destruct (bprim n) eqn:EP.
  - (nelim (Gp eq_refl) 6%nat; intros Hcl RB RE _ _ BH). cbn zeta in *.
    (nelim (prim_block_cptr st WF A n HB EP) 4%nat; intros IN1 IK1 CVb Lb).
    assert (UKb : In (b_cptr st A n) (used_cptrs st (pclass n))) by (rewrite used_cptrs_split, !in_app_iff; right; left; exact IK1).
    rewrite BH, Lb. destruct (used_vs_used (pclass n) (b_cptr st A n) ltac:(unfold KNUMCLASSES; lia) ltac:(lia) UKb (NE EP)); [left| right]; lia.
  - (nelim (Gs eq_refl) 3%nat; intros S1' T1 _).
    destruct (prim_vs_tail st WF (b_lo A n, b_lo A n + smapsize n)) as [D|D].
    { apply in_or_app; right; apply in_or_app; left; apply in_map_iff; exists (b_lo A n, n); split; [reflexivity| exact S1']. }
    + cbn [fst snd] in D. rewrite T1. unfold KREGIONSIZE, KFREEARRAY_OFF, PRIM_RES_SIZE in *. lia.
    + cbn [fst snd] in D. rewrite T1. unfold KREGIONSIZE, KFREEARRAY_OFF, PRIM_RES_SIZE in *. lia.
Qed.

(* [comment removed for export] *)
Definition batch_ne (b : qbatch) : Prop := ~ (c = 24 /\ qb_addr b = CH).
Lemma batch_used : forall b, In b (qall st) -> In ((qb_addr b - rbeg st 24) / 16) (used_cptrs st 24) /\ qb_addr b = cptr_addr st 24 ((qb_addr b - rbeg st 24) / 16).
Proof.
  intros b Hb. destruct (wq_batch st (wf_quar_ok st WF) b Hb) as [_ (kb & CV & EQ)].
  assert (EK : (qb_addr b - rbeg st 24) / 16 = kb) by (rewrite EQ; unfold cptr_addr; Z.div_mod_to_equations; nia).
  rewrite EK. split; [| exact EQ]. rewrite used_cptrs_split, !in_app_iff. right. right. left.
  unfold batch_cptrs. rewrite Z.eqb_refl. apply in_map_iff. exists (qb_addr b). split; [exact EK|]. unfold qbatch_addrs. apply in_map. exact Hb.
Qed.
Lemma used_vs_batch : forall b, In b (qall st) -> batch_ne b -> qb_addr b + QBATCH_SIZE <= CH \/ CH + CS <= qb_addr b.
Proof.
  intros b Hb NE. destruct (batch_used b Hb) as [UKb EQ]. unfold QBATCH_SIZE. change 8192 with (csize 24). rewrite EQ.
  apply (used_vs_used 24 _ ltac:(unfold KNUMCLASSES; lia) ltac:(lia) UKb).
  intros E. injection E as E1 E2. apply NE. split; [symmetry; exact E1|]. rewrite EQ, <- E1, E2. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma used_vs_avail : forall c' k', 0 <= c' < KNUMCLASSES -> In k' (avail_cptrs st c' ++ apend_cptrs st c') -> (c', k') <> (c, k) ->
  cptr_addr st c' k' + csize c' <= CH \/ CH + CS <= cptr_addr st c' k'.
Proof.
  intros c' k' Hc' Hin NE.
  destruct (Z.eq_dec c' 0) as [->|NZ].
  { exfalso. unfold avail_cptrs in Hin. pose proof (wb_class0 st (wf_base_ok st WF)) as [E1 E2]. rewrite E1, E2 in Hin. cbn in Hin.
    unfold apend_cptrs in Hin. apply in_map_iff in Hin as ([c'' k''] & _ & Hf). apply filter_In in Hf as [Hin Hb]. cbn [fst] in Hb.
    apply Z.eqb_eq in Hb. subst c''. pose proof (wq_apend st (wf_quar_ok st WF) _ Hin). cbn [fst] in *. lia. }
  apply (used_vs_used c' k' Hc' ltac:(lia)); [| exact NE]. unfold used_cptrs. rewrite !in_app_iff. apply in_app_iff in Hin. tauto.
Qed.
End G.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition QBC (m : word -> option byte) (b : qbatch) (nxt : Z) : Prop :=
  rw_cells bsegs m (qb_addr b) [W8 nxt; W8 (qb_size b); W8 (qb_count b)] /\ R_qslots m b.
Definition R_qlist_at (m : word -> option byte) (q : list qbatch) : Prop :=
  forall q1 b q2, q = q1 ++ b :: q2 -> QBC m b (qc_first q2).
Lemma R_qlist_iff : forall m q, R_qlist m q <-> R_qlist_at m q.
Proof.
  intros m q. induction q as [|b0 q IH].
  - split; [intros _ q1 b q2 E; destruct q1; discriminate| intros _; exact I].
  - cbn [R_qlist]. split.
    + intros (HL & HS & HQ) q1 b q2 E. destruct q1 as [|x q1].
      * cbn in E. injection E as <- <-. split; [exact HL| exact HS].
      * cbn in E. injection E as <- E. exact (proj1 IH HQ q1 b q2 E).
    + intros H. pose proof (H [] b0 q eq_refl) as [HL HS]. split; [exact HL|]. split; [exact HS|].
      apply (proj2 IH). intros q1 b q2 E. apply (H (b0 :: q1) b q2). rewrite E. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma A_QUAR_val : A_QUAR = 0xa6630.
Proof. reflexivity. Qed.

Definition ucz_ok (st : rtstate) (c k : Z) (iv : Z * Z) : Prop :=
     (cptr_addr st c k <= fst iv /\ snd iv <= cptr_addr st c k + csize c)
  \/ (SH (cptr_addr st c k) <= fst iv /\ snd iv <= SH (cptr_addr st c k + csize c))
  \/ (qcache_t st <= fst iv /\ snd iv <= qcache_t st + 32)
  \/ (A_QUAR + 152 <= fst iv /\ snd iv <= A_QUAR + 192)
  \/ (st_t st + T_STATS <= fst iv /\ snd iv <= st_t st + T_UNWINDING)
  \/ CEIL <= fst iv.

Local Ltac ulia := unfold KHIGHMEM_BEG, AIMG_HI, CEIL, KREGIONSIZE, KFREEARRAY_OFF, PRIM_RES_SIZE, PTRARR_RES_SIZE, QBATCH_SIZE in *; first [lia | blia].

Section UCZ.
Variable st : rtstate.
Hypothesis WF : RTWF st.
Variables (c k : Z).
Hypothesis HcK : 0 <= c < KNUMCLASSES.
Hypothesis Hc1 : 1 <= c.
Hypothesis UK : In k (used_cptrs st c).
Variable W : list (Z * Z).
Hypothesis HW : Forall (ucz_ok st c k) W.
Local Abbreviation CH := (cptr_addr st c k).
Local Abbreviation CS := (csize c).
Local Abbreviation t := (st_t st).

Lemma ucz_disj : forall a sz,
  (a + sz <= CH \/ CH + CS <= a) -> (a + sz <= SH CH \/ SH (CH + CS) <= a) ->
  (a + sz <= t + T_QCACHE \/ (t + T_QCACHE + 32 <= a /\ a + sz <= t + T_STATS) \/ (t + T_UNWINDING <= a /\ a + sz <= CEIL)) ->
  (a + sz <= A_QUAR + 152 \/ A_QUAR + 192 <= a) ->
  disjoint_from W a sz.
Proof.
  intros a sz H1 H2 H3 H4. pose proof (t_range st WF) as TR. induction W as [|[lo hi] W' IH]; [exact I|].
  pose proof (Forall_inv HW) as A1. unfold ucz_ok, qcache_t in A1. cbn [fst snd] in A1. cbn.
  split; [unfold T_QCACHE, T_STATS, T_UNWINDING, CEIL, KHIGHMEM_BEG, AIMG_HI in *; rewrite ?A_QUAR_val in *; lia| apply IH; exact (Forall_inv_tail HW)].
Qed.

Lemma geomU : rbeg st c <= CH /\ CH + CS <= rbeg st c + r_allocated (rg st c) /\ r_allocated (rg st c) <= r_mapped (rg st c)
  /\ r_mapped (rg st c) <= KFREEARRAY_OFF /\ KHIGHMEM_BEG <= rbeg st c /\ st_pbase st <= rbeg st c
  /\ rbeg st c + KREGIONSIZE <= st_pbase st + PRIM_RES_SIZE /\ st_pbase st + PRIM_RES_SIZE <= CEIL
  /\ CH mod 32 = 0 /\ 32 <= CS /\ CS mod 32 = 0.
Proof. exact (used_geom st WF c k HcK Hc1 UK). Qed.

Lemma shU : SH KHIGHMEM_BEG <= SH CH /\ SH (CH + CS) <= SH CEIL /\ SH CH + CS / 8 = SH (CH + CS) /\ SH CEIL < KHIGHMEM_BEG.
Proof.
  (nelimp geomU 11%nat; intros G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11). unfold KREGIONSIZE, KFREEARRAY_OFF in *.
  split; [apply rt_SH_mono; lia|]. split; [apply rt_SH_mono; lia|].
  split; [rewrite rt_SH_aligned_add by (apply (mod0_trans _ 8 32); [lia|lia|reflexivity|exact G9]); reflexivity|].
  rewrite SH_CEIL. unfold KHIGHMEM_BEG, AIMG_HI. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ucz_low : forall a sz, AIMG_LO <= a -> a + sz <= KHIGHMEM_BEG -> (a + sz <= AIMG_HI \/ KLOWSHADOW_BEG <= a) ->
  (a + sz <= SH CH \/ SH (CH + CS) <= a) -> (a + sz <= A_QUAR + 152 \/ A_QUAR + 192 <= a) ->
  disjoint_from W a sz.
Proof.
  intros a sz H0 H1 HZ H2 H3. (nelimp geomU 6%nat; intros G1 G2 G3 G4 G5 _). pose proof (t_range st WF) as [TR _].
  apply ucz_disj; [lia| exact H2| | exact H3]. unfold T_QCACHE, T_STATS, T_UNWINDING, CEIL in *. clear - H0 H1 HZ TR. blia.
Qed.
Lemma ucz_img : forall a sz, AIMG_LO <= a -> a + sz <= AIMG_HI -> (a + sz <= A_QUAR + 152 \/ A_QUAR + 192 <= a) -> disjoint_from W a sz.
Proof.
  intros a sz H0 H H3. pose proof shU as (S1 & _). change (SH KHIGHMEM_BEG) with 0x2008fff7000 in S1.
  apply ucz_low; [exact H0| unfold AIMG_HI, KHIGHMEM_BEG in *; lia| left; exact H| unfold AIMG_LO, AIMG_HI in *; lia| exact H3].
Qed.
Local Ltac img := apply ucz_img; [unfold AIMG_LO, A_ALLOC; cbn -[Z.add Z.mul Z.le Z.lt Z.sub]; lia| unfold AIMG_HI, A_ALLOC; cbn -[Z.add Z.mul Z.le Z.lt Z.sub]; lia| unfold A_QUAR, A_ALLOC; cbn -[Z.add Z.mul Z.le Z.lt Z.sub]; lia].

Lemma ucz_obj : forall lo hi a sz, (hi <= CH \/ CH + CS <= lo) -> (hi <= t \/ t + 4096 <= lo) ->
  (hi <= KLOWSHADOW_BEG \/ KHIGHMEM_BEG <= lo) -> (hi <= AIMG_LO \/ AIMG_HI <= lo) -> hi <= CEIL -> lo <= a -> a + sz <= hi -> disjoint_from W a sz.   (* [comment removed for export] *)
Proof.
  intros lo hi a sz D1 D2 K1 K0 K2 Ha Hs. (nelimp shU 4%nat; intros S1 S2 S3 S4). change (SH KHIGHMEM_BEG) with 0x2008fff7000 in S1.
  apply ucz_disj; [lia| unfold KLOWSHADOW_BEG, KHIGHMEM_BEG in *; lia| unfold T_QCACHE, T_STATS, T_UNWINDING; lia| rewrite A_QUAR_val; unfold KHIGHMEM_BEG, AIMG_LO, AIMG_HI in *; lia].
Qed.
Lemma ucz_sh : forall lo hi a sz, (hi <= CH \/ CH + CS <= lo) -> 0 <= lo -> lo mod 8 = 0 -> hi <= CEIL ->
  SH lo <= a -> a + sz <= SH hi -> disjoint_from W a sz.   (* [comment removed for export] *)
Proof.
  intros lo hi a sz D L0 L8 HC Ha Hs. (nelimp shU 4%nat; intros S1 S2 S3 S4). (nelimp geomU 10%nat; intros G1 G2 G3 G4 G5 G6 G7 G8 G9 _).
  pose proof (rt_SH_mono hi CEIL HC). pose proof (t_range st WF) as [TR _].
  pose proof (rt_SH_mono 0 lo L0) as M0. change (SH 0) with 0x7fff8000 in M0.
  apply ucz_disj; [lia| | unfold T_QCACHE, T_STATS, T_UNWINDING, CEIL in *; blia| rewrite A_QUAR_val; lia].
  destruct D as [D|D].
  - left. pose proof (rt_SH_mono hi CH D). lia.
  - right. assert (E : SH (CH + CS) <= SH lo) by (apply rt_SH_mono; exact D). lia.
Qed.

Lemma t_vs_chunkU : t + 4096 <= CH \/ CH + CS <= t.
Proof. (nelimp geomU 9%nat; intros G1 G2 G3 G4 G5 G6 G7 G8 _). pose proof (t_vs_prim st WF). unfold KREGIONSIZE, KFREEARRAY_OFF in *. lia. Qed.
Lemma loose_vs_chunkU : forall b sz, In (b, sz) (st_loose0 st) -> b + sz <= CH \/ CH + CS <= b.
Proof.
  intros b sz Hb. (nelimp geomU 9%nat; intros G1 G2 G3 G4 G5 G6 G7 G8 _).
  destruct (prim_vs_tail st WF (b, b + sz) ltac:(apply in_or_app; left; apply in_map_iff; exists (b, sz); auto)) as [D|D]; cbn [fst snd] in D;
    unfold KREGIONSIZE, KFREEARRAY_OFF in *; lia.
Qed.
Lemma tail_vs_chunkU : forall r, In r (map (fun e => (fst e, fst e + smapsize (snd e))) (st_sec st)
                                  ++ map (fun b => (b, b + NODEBLOCK_SIZE)) (d_nblocks (st_depot st))
                                  ++ map (fun b => (b, b + STOREBLOCK_SIZE)) (d_sblocks (st_depot st))) ->
  snd r <= CH \/ CH + CS <= fst r.
Proof.
  intros r Hr. (nelimp geomU 9%nat; intros G1 G2 G3 G4 G5 G6 G7 G8 _).
  destruct (prim_vs_tail st WF r ltac:(apply in_or_app; right; exact Hr)) as [D|D]; unfold KREGIONSIZE, KFREEARRAY_OFF in *; lia.
Qed.

(* [comment removed for export] *)
Lemma UZ_link : WOK_link W.
Proof. split; [intros a v Hin; destruct (alink_range a v Hin); img| unfold A_GLOBREC_LO, A_GLOBREC_HI; img]. Qed.
Lemma UZ_consts : WOK_consts W.
Proof.
  unfold WOK_consts.
  unfold A_SHADOW_OFF_CELL, A_UAR_OPTION, A_AFLAGS, A_CFLAGS, A_PAGESIZE_CACHED, A_KHIGHMEMEND, A_KMIDMEMBEG, A_KMIDMEMEND,
    A_ASAN_INITED, A_MCS, A_CAN_POISON, A_TSD_KEY_INITED, A_TSD_KEY, A_MAY_RETURN_NULL, A_ALLOC_OOM, A_DYING, A_VERBOSITY,
    A_MFHOOKS, A_LSAN_DISABLE, A_IA_INITED, AHOOKS, A_LIBC_PAGESIZE, A_MU_GLOBALS, A_GLOBALS_REGD, A_TPCG_INITED, A_TOOLNAME, A_PRINTF_CB, A_EMB, ATP.
  repeat lazymatch goal with |- _ /\ _ => split | _ => idtac end; img.
Qed.
Lemma UZ_ia : WOK_ia W.
Proof. intros i Hi. unfold A_IA_MAP1. img. Qed.
Lemma UZ_lowshadow : WOK_lowshadow W.
Proof.
  intros g Hg. change (SH AIMG_LO) with 0x7fffa000 in Hg. change (SH AIMG_HI) with 0x800b7e00 in Hg.
  pose proof shU as (S1 & _). change (SH KHIGHMEM_BEG) with 0x2008fff7000 in S1.
  apply ucz_low; [unfold AIMG_LO; lia| unfold KHIGHMEM_BEG, AIMG_HI; lia| right; unfold KLOWSHADOW_BEG; lia| lia| rewrite A_QUAR_val; lia].
Qed.
(* [comment removed for export] *)
Lemma UZ_alloc4 : forall m m', munch W m m' -> wmono bsegs m m' -> R_alloc st m ->
  (exists j1 j2 j3, rw_cells bsegs m' A_ALLOC [W8 (st_pbase st); W8 PRIM_RES_SIZE; CB 16 j1; W8 (st_spacebeg st); W4 (2^32 - 1); CB 4 j2; W8 (st_spacebeg st + KSPACESIZE); W1 0; CB 7 j3])
  /\ (exists j1 j2 j3, rw_cells bsegs m' A_SECONDARY [W8 4096; W8 (st_pa st); W8 (st_pa st); W8 PTRARR_RES_SIZE; CB 16 j1; W8 (st_nreserved st); W8 (nsec st); CB 552 j2; W1 0; CB 7 j3])
  /\ (exists j, rw_cells bsegs m' A_GSTATS [CB 40 j])
  /\ cells_at bsegs m' A_MAXUSERSZ [W8 (2^40); W2 16; W2 2048; W1 1].
Proof.
  intros m m' MU WM ((j1 & j2 & j3 & H1) & (i1 & i2 & i3 & H2) & (jg & H3) & _ & H5).
  split; [exists j1, j2, j3; eapply (rwT W m m' MU WM); [exact H1| unfold A_ALLOC; img]|].
  split; [exists i1, i2, i3; eapply (rwT W m m' MU WM); [exact H2| unfold A_SECONDARY, A_ALLOC; img]|].
  split; [exists jg; eapply (rwT W m m' MU WM); [exact H3| unfold A_GSTATS, A_ALLOC; img]|].
  eapply (roT W m m' MU); [exact H5| unfold A_MAXUSERSZ; img].
Qed.
(* [comment removed for export] *)
Lemma UZ_quarcells : forall m m', munch W m m' -> wmono bsegs m m' -> R_alloc st m -> disjoint_from W A_QUAR 256 ->
  exists j1 j2 j3 j4, rw_cells bsegs m' A_QUAR
      [CB 64 j1; W8 QUAR_MAX_SIZE; W8 QUAR_MIN_SIZE; W8 QUAR_MAX_CACHE; CB 64 j2; W1 0; W1 0; CB 6 j3;
       W8 (zlen (st_qglobal st)); W8 (qc_first (st_qglobal st)); W8 (qc_last (st_qglobal st)); W8 (qc_bytes (st_qglobal st)); CB 64 j4].
Proof.
  intros m m' MU WM (_ & _ & _ & (j1 & j2 & j3 & j4 & H4) & _) D. exists j1, j2, j3, j4. eapply (rwT W m m' MU WM); [exact H4| exact D].
Qed.

(* [comment removed for export] *)
Lemma UZ_rinfo : WOK_rinfo st W.
Proof.
  intros c' Hc'. (nelimp (ris_range st WF) 4%nat; intros X1 X2 X3 X4). unfold KNUMCLASSES in Hc'.
  (nelimp geomU 9%nat; intros G1 G2 G3 G4 G5 G6 G7 G8 _). (nelimp (S_range st WF) 3%nat; intros SR1 SR2 SR3).
  pose proof (t_vs_prim st WF) as TP.
  rewrite (rbeg_val st c) in *.
  eapply (ucz_obj (ris st) (ris st + 4096)); unfold rinfo, ris, KSPACESIZE, KREGIONSIZE, KFREEARRAY_OFF, PRIM_RES_SIZE, CEIL, KLOWSHADOW_BEG, KHIGHMEM_BEG, AIMG_LO, AIMG_HI in *; first [lia| nia].
Qed.
Lemma UZ_regions : WOK_regions st W.
Proof.
  intros c' Hc'. pose proof (region_facts st WF c' Hc') as RF. cbn zeta in RF.
  (nelim RF 10%nat; intros X1 X2 X3 X4 X5 X6 X7 X8 X9 X10).
  assert (FB : fabeg st c' = rbeg st c' + KFREEARRAY_OFF) by reflexivity.
  (nelimp geomU 10%nat; intros G1 G2 G3 G4 G5 G6 G7 G8 G9 _).
  pose proof (t_vs_prim st WF) as TP.
  assert (DFA : fabeg st c' + r_mapped_fa (rg st c') <= CH \/ CH + CS <= fabeg st c').
  { destruct (Z.eq_dec c' c) as [->|NC]; [right; rewrite FB; lia|].
    rewrite FB. rewrite (rbeg_val st c') in *. rewrite (rbeg_val st c) in *. unfold KREGIONSIZE, KFREEARRAY_OFF, KFREEARRAY_SIZE, KNUMCLASSES in *.
    destruct (Z_lt_le_dec c' c); [left| right]; nia. }
  unfold KHIGHMEM_BEG, AIMG_HI, KREGIONSIZE, KFREEARRAY_OFF, KFREEARRAY_SIZE, PRIM_RES_SIZE in *.
  split.
  - intros i Hi. pose proof (wc_num_freed st c' (wf_class_ok st WF c' Hc')) as NF.
    eapply (ucz_obj (fabeg st c') (fabeg st c' + r_mapped_fa (rg st c'))); [exact DFA| ulia| ulia| ulia| ulia| ulia| ulia].
  - assert (DT : rbeg st c' + r_mapped (rg st c') <= CH \/ CH + CS <= rbeg st c' + r_allocated (rg st c')).
    { destruct (Z.eq_dec c' c) as [->|NC]; [right; lia|].
      destruct (region_disj st c' c (rbeg st c') CH (rbeg st c' + r_mapped (rg st c')) (CH + CS) Hc' HcK NC); unfold KFREEARRAY_OFF; try lia. }
    eapply (ucz_sh (rbeg st c' + r_allocated (rg st c')) (rbeg st c' + r_mapped (rg st c')));
      [lia| lia| apply mod0_add; [lia| exact X8| exact X9]| unfold CEIL; lia| lia| ].
    rewrite !rt_SH_aligned_add by exact X8. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma UZ_avail_other : forall c' k', 0 <= c' < KNUMCLASSES -> In k' (avail_cptrs st c' ++ apend_cptrs st c') -> (c', k') <> (c, k) ->
  disjoint_from W (SH (cptr_addr st c' k')) (csize c' / 8).
Proof.
  intros c' k' Hc' Hin NE.
  pose proof (used_vs_avail st WF c k HcK Hc1 UK c' k' Hc' Hin NE) as D.
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
  eapply (ucz_sh (cptr_addr st c' k') (cptr_addr st c' k' + csize c')); [ulia| ulia| exact AL| ulia| ulia| ].
  rewrite rt_SH_aligned_add by exact AL. lia.
Qed.

(* [comment removed for export] *)
Lemma UZ_cache : WOK_cache st W.
Proof.
  intros c' Hc'. pose proof (wc_cache_max st c' (wf_class_ok st WF c' Hc')) as CM. pose proof (cmaxcount_le16 c'). unfold KNUMCLASSES in Hc'.
  pose proof (t_range st WF) as [T1 T2]. pose proof t_vs_chunkU as TC. (nelimp shU 4%nat; intros S1 S2 S3 S4).
  assert (D : forall a sz, t + T_ACACHE <= a -> a + sz <= t + T_ACACHE + 2560 -> disjoint_from W a sz).
  { intros a sz H1 H2. change (SH KHIGHMEM_BEG) with 0x2008fff7000 in S1. apply ucz_disj; unfold T_ACACHE, T_QCACHE, T_STATS, CEIL in *; rewrite ?A_QUAR_val in *; blia. }
  split; [apply D; unfold pcaddr, acache; lia|]. intros i Hi. apply D; unfold pcaddr, acache; lia.
Qed.

(* [comment removed for export] *)
Lemma UZ_thread : forall m m', munch W m m' -> wmono bsegs m m' -> R_thread st m -> tpx_ok st ->
  vis m' t (t + 4096)
  /\ (exists j1 j2 j3 j4 j5,
        rw_cells bsegs m' t [W8 (st_ctx st); W8 (ASTACK_TOP (st_sp0 st)); W8 (ASTACK_BOTTOM (st_sp0 st)); CB 16 j1;
                            W1 0; CB 7 j2; C8 j3; C8 j4; C8 j5; W8 (st_fs st)])
  /\ rw_cells bsegs m' (t + T_UNWINDING) [W1 0]
  /\ rw_cells bsegs m' (st_ctx st + CTX_TID) [W4 0]
  /\ rw_cells bsegs m' (st_ctx st + CTX_THREAD) [W8 t]
  /\ cells_at bsegs m' A_TSD_PTR [W8 A_TSD_MAIN]
  /\ cells_at bsegs m' A_TSD_MAIN [W8 (st_ctx st)]
  /\ cells_at bsegs m' A_DTV_PTR [W8 A_DTV]
  /\ cells_at bsegs m' (A_DTV + 8 * A_TLSMOD) [W8 A_TLSBASE]
  /\ cells_at bsegs m' A_FSTLS_CELL [W8 (st_fs st)]
  /\ cells_at bsegs m' (ATP + A_DTLS_OFF) [W8 (tl_dtls_block (st_tls st))]
  /\ cells_at bsegs m' (tl_dtls_block (st_tls st) + 16 * A_TLSMOD + 8) [W8 (tl_dtls_w (st_tls st))].
Proof.
  intros m m' MU WM (TV & (j1 & j2 & j3 & j4 & j5 & TT) & _ & TU & CT1 & CT2 & K1 & K2 & K3 & K4 & K5 & K6 & K7) [CX DX].
  pose proof (t_range st WF) as [T1 T2]. pose proof t_vs_chunkU as TC. (nelimp shU 4%nat; intros S1 S2 S3 S4).
  change (SH KHIGHMEM_BEG) with 0x2008fff7000 in S1.
  (nelim (wb_ctx_loose st (wf_base_ok st WF)) 5%nat; intros cb ck CL1 CL2 CL3). (nelim (loose0_range st WF _ _ CL1) 4%nat; intros R1 R2 R3 R4). olin R1.
  pose proof (loose_vs_chunkU cb ck CL1) as LC.
  (nelim (wb_dtls_loose st (wf_base_ok st WF)) 5%nat; intros db dk DL1 DL2 DL3). (nelim (loose0_range st WF _ _ DL1) 4%nat; intros Q1 Q2 Q3 Q4).
  (nelimp (oclr_lin _ _ Q1 ltac:(lia)) 3%nat; intros _ QLB QLI). unfold KLOWSHADOW_BEG, KHIGHMEM_BEG, AIMG_LO, AIMG_HI in QLB, QLI.
  pose proof (loose_vs_chunkU db dk DL1) as LD.
  unfold A_TSD_PTR, A_TSD_MAIN, A_DTV_PTR, A_DTV, A_TLSMOD, A_FSTLS_CELL, A_DTLS_OFF, ATP in *.
  split; [eapply visTo; [exact WM| exact TV| exact T1| unfold CEIL in *; lia]|].
  split; [exists j1, j2, j3, j4, j5; eapply (rwT W m m' MU WM); [exact TT| cbn; apply ucz_disj; unfold T_QCACHE, T_STATS, CEIL in *; rewrite ?A_QUAR_val in *; blia]|].
  split; [eapply (rwT W m m' MU WM); [exact TU| cbn; apply ucz_disj; unfold T_QCACHE, T_UNWINDING, T_STATS, CEIL in *; rewrite ?A_QUAR_val in *; blia]|].
  split; [eapply (rwT W m m' MU WM); [exact CT1| cbn; eapply (ucz_obj (st_ctx st) (st_ctx st + 160)); unfold CTX_TID, CEIL in *; (cut_on [CX DX TC CL2 CL3 OLx LC DL2 DL3 Q1 Q2 Q3 QLI LD R3] blia)]|].
  split; [eapply (rwT W m m' MU WM); [exact CT2| cbn; eapply (ucz_obj (st_ctx st) (st_ctx st + 160)); unfold CTX_THREAD, CEIL in *; (cut_on [CX DX TC CL2 CL3 OLx LC DL2 DL3 Q1 Q2 Q3 QLI LD R3] blia)]|].
  split; [eapply (roT W m m' MU); [exact K1| cbn; img]|].
  split; [eapply (roT W m m' MU); [exact K2| cbn; img]|].
  split; [eapply (roT W m m' MU); [exact K3| cbn; img]|].
  split; [eapply (roT W m m' MU); [exact K4| cbn; img]|].
  split; [eapply (roT W m m' MU); [exact K5| cbn; img]|].
  split; [eapply (roT W m m' MU); [exact K6| cbn; img]|].
  eapply (roT W m m' MU); [exact K7| cbn]. eapply (ucz_obj (tl_dtls_block (st_tls st) + 24) (tl_dtls_block (st_tls st) + 32));
    [ clear - LD DL2 DL3; lia | exact DX | clear - QLB DL2 DL3 Q2; unfold KLOWSHADOW_BEG, KHIGHMEM_BEG; lia
    | clear - QLI DL2 DL3 Q2; unfold AIMG_LO, AIMG_HI; lia | unfold CEIL; clear - Q3 DL3; lia | lia | lia ].
Qed.
Lemma UZ_qcache : forall m m', munch W m m' -> wmono bsegs m m' -> R_thread st m -> disjoint_from W (qcache_t st) 32 ->
  rw_cells bsegs m' (qcache_t st) [W8 (zlen (st_qthread st)); W8 (qc_first (st_qthread st)); W8 (qc_last (st_qthread st)); W8 (qc_bytes (st_qthread st))].
Proof. intros m m' MU WM (_ & _ & QC & _) D. eapply (rwT W m m' MU WM); [exact QC| exact D]. Qed.

(* [comment removed for export] *)
Lemma UZ_block : forall A n, In (A, n) (all_blocks st) -> chunk_ne st c k A n -> WOK_block W A n.
Proof.
  intros A n HB NE.
  (nelimp (block_geom st WF A n HB) 11%nat; intros Gn GA K X Y CE L16 H16 EA Gp Gs). unfold usz in Y.
  assert (L8 : b_lo A n mod 8 = 0) by (apply (mod0_trans _ 8 16); [lia|lia|reflexivity|exact L16]).
  pose proof (t_vs_block st WF A n HB) as TB. pose proof (used_vs_block st WF c k HcK Hc1 UK A n HB NE) as CB.
  pose proof K as K'. unfold KHIGHMEM_BEG, AIMG_HI in K'. pose proof (rz_size_range n) as (Z1 & Z2).
  assert (OBJ : forall a sz, b_lo A n <= a -> a + sz <= b_hi A n -> disjoint_from W a sz).
  { intros a sz Ha Hs. eapply (ucz_obj (b_lo A n) (b_hi A n)); [ulia| ulia| exact (ablk_disj_band _ _ K)| right; exact (ablk_img _ _ K)| ulia| exact Ha| exact Hs]. }
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
    eapply (ucz_sh (b_lo A n) (b_hi A n)); [exact CB| ulia| exact L8| ulia| ulia| ].
    rewrite EH, rt_SH_aligned_add by exact L8. rewrite ST8. lia.
Qed.
Lemma UZ_live : forall m m', munch W m m' -> wmono bsegs m m' -> R_live st m ->
  forall A n, In (A, n) (st_lb st) -> chunk_ne st c k A n -> R_block st m' BLive A n.
Proof.
  intros m m' MU WM H A n Hin NE. assert (HB : In (A, n) (all_blocks st)) by (unfold all_blocks; rewrite !in_app_iff; left; exact Hin).
  eapply (T_block st WF W m m' MU WM); [exact HB| exact (H A n Hin)| exact (UZ_block A n HB NE)].
Qed.
Lemma UZ_quar : forall m m', munch W m m' -> wmono bsegs m m' -> R_quar st m ->
  (forall A n, In (A, n) (qelems st) -> chunk_ne st c k A n -> R_block st m' BQuar A n)
  /\ (forall A n, In (A, n) (st_qpend st) -> chunk_ne st c k A n -> R_block st m' BPend A n).
Proof.
  intros m m' MU WM [H HP]. split.
  - intros A n Hin NE. assert (HB : In (A, n) (all_blocks st)) by (unfold all_blocks; rewrite !in_app_iff; right; left; exact Hin).
    eapply (T_block st WF W m m' MU WM); [exact HB| exact (H A n Hin)| exact (UZ_block A n HB NE)].
  - intros A n Hin NE. assert (HB : In (A, n) (all_blocks st)) by (unfold all_blocks; rewrite !in_app_iff; right; right; exact Hin).
    eapply (T_block st WF W m m' MU WM); [exact HB| exact (HP A n Hin)| exact (UZ_block A n HB NE)].
Qed.

(* [comment removed for export] *)
Lemma UZ_QBC : forall m m', munch W m m' -> wmono bsegs m m' -> forall b nxt, In b (qall st) -> batch_ne st c k b ->
  QBC m b nxt -> QBC m' b nxt.
Proof.
  intros m m' MU WM b nxt Hb NE (HL & (V & SL & SHD)).
  (nelim (batch_geom st WF b Hb) 5%nat; intros BB BF R1 R2 AL).
  destruct (wq_batch st (wf_quar_ok st WF) b Hb) as [CNT (kb & CV & EQ)].
  pose proof (region_facts st WF 24 ltac:(unfold KNUMCLASSES; lia)) as RF. cbn zeta in RF. (nelim RF 10%nat; intros X1 X2 X3 X4 X5 X6 X7 X8 X9 X10).
  pose proof (used_vs_batch st WF c k HcK Hc1 UK b Hb NE) as CB.
  assert (TB : qb_addr b + QBATCH_SIZE <= t \/ t + 4096 <= qb_addr b).
  { pose proof (t_vs_prim st WF). unfold KREGIONSIZE, KFREEARRAY_OFF, QBATCH_SIZE in *. lia. }
  pose proof (proj2 (wq_cur_count b CNT)) as CNT' || pose proof CNT as CNT'.
  unfold KHIGHMEM_BEG, AIMG_HI, KREGIONSIZE, KFREEARRAY_OFF, QBATCH_SIZE, QBATCH_CAP, PRIM_RES_SIZE in *.
  assert (OBJ : forall a sz, qb_addr b <= a -> a + sz <= qb_addr b + 8192 -> disjoint_from W a sz).
  { intros a sz Ha Hs. eapply (ucz_obj (qb_addr b) (qb_addr b + 8192)); [ulia| ulia| ulia| ulia| ulia| ulia| ulia]. }
  split; [| split; [| split]].
  - eapply (rwT W m m' MU WM); [exact HL| cbn; apply OBJ; lia].
  - eapply visT; [exact WM| exact V| unfold AIMG_HI; lia].
  - intros i Hi. eapply (rwT W m m' MU WM); [exact (SL i Hi)| cbn; apply OBJ; lia].
  - assert (AL8 : qb_addr b mod 8 = 0) by (apply (mod0_trans _ 8 32); [lia|lia|reflexivity|exact AL]).
    eapply (rwT W m m' MU WM); [exact SHD|]. unfold sh_avail. change (csize 24) with 8192. rewrite zcells_zrep_size by lia.
    eapply (ucz_sh (qb_addr b) (qb_addr b + 8192)); [ulia| ulia| exact AL8| ulia| ulia| ].
    rewrite rt_SH_aligned_add by exact AL8. change (8192 / 8) with 1024. lia.
Qed.
Lemma UZ_qlist : forall m m' q, munch W m m' -> wmono bsegs m m' -> (forall b, In b q -> In b (qall st)) -> R_qlist m q ->
  forall q1 b q2, q = q1 ++ b :: q2 -> batch_ne st c k b -> QBC m' b (qc_first q2).
Proof.
  intros m m' q MU WM SUB HQ q1 b q2 E NE. apply (UZ_QBC m m' MU WM); [apply SUB; rewrite E; apply in_or_app; right; left; reflexivity| exact NE|].
  exact (proj1 (R_qlist_iff m q) HQ q1 b q2 E).
Qed.
Lemma UZ_batches : forall m m', munch W m m' -> wmono bsegs m m' -> R_batches st m ->
  (forall q1 b q2, st_qthread st = q1 ++ b :: q2 -> batch_ne st c k b -> QBC m' b (qc_first q2))
  /\ (forall q1 b q2, st_qglobal st = q1 ++ b :: q2 -> batch_ne st c k b -> QBC m' b (qc_first q2))
  /\ (forall q1 b q2, st_qtmp st = q1 ++ b :: q2 -> batch_ne st c k b -> QBC m' b (qc_first q2))
  /\ (forall bd, In bd (st_qcur st) -> batch_ne st c k (fst bd) ->
        (exists nx, rw_cells bsegs m' (qb_addr (fst bd)) [W8 nx; W8 (qb_size (fst bd)); W8 (qb_count (fst bd))]) /\ R_qslots m' (fst bd)).
Proof.
  intros m m' MU WM nelH_; (nelim nelH_ 4%nat; intros H1 H2 H3 H4).
  split; [apply (UZ_qlist m m' _ MU WM); [intros b Hb; unfold qall; rewrite !in_app_iff; tauto| exact H1]|].
  split; [apply (UZ_qlist m m' _ MU WM); [intros b Hb; unfold qall; rewrite !in_app_iff; tauto| exact H2]|].
  split; [apply (UZ_qlist m m' _ MU WM); [intros b Hb; unfold qall; rewrite !in_app_iff; tauto| exact H3]|].
  intros bd Hbd NE. destruct (H4 bd Hbd) as [[nx HL] HS].
  destruct (UZ_QBC m m' MU WM (fst bd) nx ltac:(unfold qall; rewrite !in_app_iff; right; right; right; apply in_map; exact Hbd) NE (conj HL HS)) as [HL' HS'].
  split; [exists nx; exact HL'| exact HS'].
Qed.

(* [comment removed for export] *)
Lemma UZ_ptrarr : WOK_ptrarr st W.
Proof.
  (nelimp geomU 9%nat; intros G1 G2 G3 G4 G5 G6 G7 G8 _).
  split.
  - intros i Hi. (nelimp (pa_range st WF) 5%nat; intros P1 P2 P3 P4 P5). pose proof (t_vs_pa st WF).
    pose proof (wb_pwdj st (wf_base_ok st WF)) as PW. rewrite rt_ranges_tail in PW. cbn [app] in PW. destruct PW as [PF _].
    rewrite Forall_forall in PF. specialize (PF _ ltac:(left; reflexivity)). cbn [fst snd] in PF.
    unfold KHIGHMEM_BEG, AIMG_HI, PTRARR_RES_SIZE, KREGIONSIZE, KFREEARRAY_OFF, PRIM_RES_SIZE in *.
    eapply (ucz_obj (st_pa st) (st_pa st + 0x800000)); [ulia| ulia| ulia| ulia| ulia| ulia| ulia].
  - intros e He. destruct (ws_spend st (wf_sec_ok st WF) e He) as [HE _].
    (nelim (ws_entry st (wf_sec_ok st WF) e HE) 4%nat; intros E1 E2 E3 _).
    pose proof (wb_ranges st (wf_base_ok st WF) (fst e, fst e + smapsize (snd e))) as R. cbn [fst snd] in R.
    specialize (R ltac:(unfold rt_ranges; do 2 right; rewrite !in_app_iff; right; left; apply in_map_iff; exists e; auto)).
    destruct e as [mb n]. cbn [fst snd] in *. (nelim (sec_facts n E1) 5%nat; intros _ _ _ F4 _). pose proof (usz_le_rounded8 n) as (U1 & _).
    pose proof (t_vs_sec st WF mb n HE).
    pose proof (tail_vs_chunkU (mb, mb + smapsize n) ltac:(apply in_or_app; left; apply in_map_iff; exists (mb, n); auto)) as D. cbn [fst snd] in D.
    eapply (ucz_obj mb (mb + smapsize n)); [ulia| ulia| ulia| ulia| ulia| ulia| unfold usz in *; lia].
Qed.
Lemma UZ_depot : WOK_depot st W.
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
    { pose proof (wd_nnb st WD) as E. unfold d_nnb in *. rewrite E. subst q. unfold DEPOT_L2_NODES. Z.div_mod_to_equations. (cut_on [Hid H H0 H4 H5 H9 H10 H11 H12 H13] nia). }
    assert (Hb : In b (d_nblocks (st_depot st))) by (subst b; apply nthz_In; unfold d_nnb in Hq; exact Hq).
    (nelim (nb_range st WF b Hb) 3%nat; intros R1 R2 R3). pose proof (t_vs_nb st WF b Hb) as TB.
    pose proof (tail_vs_chunkU (b, b + NODEBLOCK_SIZE) ltac:(apply in_or_app; right; apply in_or_app; left; apply in_map_iff; exists b; auto)) as D. cbn [fst snd] in D.
    assert (ADDR : dnode_addr (st_depot st) id = b + DEPOT_NODE_SZ * (id mod DEPOT_L2_NODES)) by reflexivity.
    rewrite ADDR. unfold DEPOT_NODE_SZ, DEPOT_L2_NODES, NODEBLOCK_SIZE in *.
    eapply (ucz_obj b (b + 1048576)); [ulia| ulia| ulia| ulia| ulia| Z.div_mod_to_equations; lia| Z.div_mod_to_equations; lia].
  - img.
  - intros b Hb. img.
Qed.
Lemma UZ_fs : WOK_fs st W.
Proof.
  (nelimp (fs_range st WF) 3%nat; intros F1 F2 F3). unfold KHIGHMEM_BEG, AIMG_HI in F1. pose proof (t_vs_fs st WF) as TF.
  pose proof (loose_vs_chunkU _ _ (wb_fs_loose st (wf_base_ok st WF))) as CF.
  assert (OBJ : forall a sz, st_fs st <= a -> a + sz <= st_fs st + FS_TOTAL -> disjoint_from W a sz).
  { intros a sz Ha Hs. eapply (ucz_obj (st_fs st) (st_fs st + FS_TOTAL)); [ulia| ulia| ulia| ulia| exact F2| ulia| ulia]. }
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
Theorem ucz_others : forall m m', munch W m m' -> wmono bsegs m m' -> RTREP st m ->
  R_link m' /\ R_consts st m' /\ R_rinfo st m' /\ R_regions st m' /\ R_cache st m'
  /\ R_ptrarr st m' /\ R_depot st m' /\ R_fs st m' /\ R_ia m' /\ R_lowshadow m'
  /\ (forall c' k', 0 <= c' < KNUMCLASSES -> In k' (avail_cptrs st c' ++ apend_cptrs st c') -> (c', k') <> (c, k) ->
        rw_cells bsegs m' (SH (cptr_addr st c' k')) (zcells (sh_avail c'))).
Proof.
  intros m m' MU WM HR.
  Local Ltac tapp T st WF W m m' MU WM :=
    first [ eapply (T st WF W m m' MU WM) | eapply (T st W m m' MU WM) | eapply (T W m m' MU WM) | eapply (T W m m' MU) ].
  split; [tapp T_link st WF W m m' MU WM; [exact (rr_link st m HR)| exact UZ_link]|].
  split; [tapp T_consts st WF W m m' MU WM; [exact (rr_consts st m HR)| exact UZ_consts]|].
  split; [tapp T_rinfo st WF W m m' MU WM; [exact (rr_rinfo st m HR)| exact UZ_rinfo]|].
  split; [tapp T_regions st WF W m m' MU WM; [exact (rr_regions st m HR)| exact UZ_regions]|].
  split; [tapp T_cache st WF W m m' MU WM; [exact (rr_cache st m HR)| exact UZ_cache]|].
  split; [tapp T_ptrarr st WF W m m' MU WM; [exact (rr_ptrarr st m HR)| exact UZ_ptrarr]|].
  split; [tapp T_depot st WF W m m' MU WM; [exact (rr_depot st m HR)| exact UZ_depot]|].
  split; [tapp T_fs st WF W m m' MU WM; [exact (rr_fs st m HR)| exact UZ_fs]|].
  split; [tapp T_ia st WF W m m' MU WM; [exact (rr_ia st m HR)| exact UZ_ia]|].
  split; [tapp T_lowshadow st WF W m m' MU WM; [exact (rr_lowshadow st m HR)| exact UZ_lowshadow]|].
  intros c' k' Hc' Hin NE. eapply (rwT W m m' MU WM); [exact (rr_avail st m HR c' k' Hc' Hin)|].
  destruct (Z.eq_dec c' 0) as [->|NZ].
  { exfalso. unfold avail_cptrs in Hin. pose proof (wb_class0 st (wf_base_ok st WF)) as [E1 E2]. rewrite E1, E2 in Hin. cbn in Hin.
    unfold apend_cptrs in Hin. apply in_map_iff in Hin as ([c'' k''] & _ & Hf). apply filter_In in Hf as [Hin Hb]. cbn [fst] in Hb.
    apply Z.eqb_eq in Hb. subst c''. pose proof (wq_apend st (wf_quar_ok st WF) _ Hin). cbn [fst] in *. lia. }
  pose proof (csize_pos c' ltac:(unfold KNUMCLASSES in Hc'; lia)) as SP.
  unfold sh_avail. rewrite zcells_zrep_size by (Z.div_mod_to_equations; lia). apply UZ_avail_other; assumption.
Qed.
End UCZ.


End CeilWrap.
