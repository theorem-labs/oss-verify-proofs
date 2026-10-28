(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Mem Frame Cells Step Arr RzCPS. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface D_kit R_cache_defs R_prim_defs R_thread R_m2s R_poison R_setshadow R_leaves R_glue_defs R_sec_defs R_depot_defs R_fs_defs R_tlsgetaddr R_intalloc I_lkit TopA_iodefs RT_state RT_rep RT_frame RT_trans RT_freestate.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma munch_agree : forall W (m m' : mem) a n, munch W m m' -> disjoint_from W a n -> agree_on (fun x => a <= x < a + n) m m'.
Proof. intros W m m' a n MU D x Hx. apply MU. exact (disjoint_outside W a n (bv_unsigned x) D Hx). Qed.

Lemma rwc_nw : forall W (m m' : mem) A cs, rw_cells ctasegs m A cs -> munch W m m' -> disjoint_from W A (Z.of_nat (cells_size cs)) ->
  rw_cells ctasegs m' A cs.
Proof. intros W m m' A cs H MU D. exact (rw_cells_agree_nw ctasegs m m' A cs H (munch_agree W m m' _ _ MU D)). Qed.
Lemma roc_nw : forall W (m m' : mem) A cs, ro_cells ctasegs m A cs -> munch W m m' -> disjoint_from W A (Z.of_nat (cells_size cs)) ->
  ro_cells ctasegs m' A cs.
Proof. intros W m m' A cs H MU D. exact (ro_cells_agree ctasegs m m' A cs H (munch_agree W m m' _ _ MU D)). Qed.
Lemma wr_nw : forall W (m m' : mem) a n, wr_at ctasegs m a n -> munch W m m' -> disjoint_from W a n -> wr_at ctasegs m' a n.
Proof. intros W m m' a n H MU D. exact (wr_at_agree_nw ctasegs m m' a n H (munch_agree W m m' _ _ MU D)). Qed.
Lemma stk_nw : forall W (m m' : mem) lo hi, stk ctasegs m lo hi -> munch W m m' -> disjoint_from W lo (hi - lo) -> stk ctasegs m' lo hi.
Proof.
  intros W m m' lo hi H MU D. apply (stk_agree_nw ctasegs m m' lo hi H). eapply agree_sub; [exact (munch_agree W m m' _ _ MU D)|].
  intros x Hx. cbv beta in *. lia.
Qed.
Lemma u64_nw : forall W (m m' : mem) A ws, u64arr ctasegs m A ws -> munch W m m' -> disjoint_from W A (8 * Z.of_nat (length ws)) ->
  u64arr ctasegs m' A ws.
Proof. intros W m m' A ws H MU D. exact (u64arr_agree_nw ctasegs m m' A ws H (munch_agree W m m' _ _ MU D)). Qed.
Lemma u32_nw : forall W (m m' : mem) A ws, u32arr ctasegs m A ws -> munch W m m' -> disjoint_from W A (4 * Z.of_nat (length ws)) ->
  u32arr ctasegs m' A ws.
Proof.
  intros W m m' A ws [Hb Hw] MU D. split.
  - apply (bytes_at_transport ctasegs W m m' _ _ Hb MU). rewrite u32s_length, Nat2Z.inj_mul. exact D.
  - exact (wr_nw W m m' _ _ Hw MU D).
Qed.
Lemma u8_nw : forall W (m m' : mem) A bs, u8arr ctasegs m A bs -> munch W m m' -> disjoint_from W A (Z.of_nat (length bs)) ->
  u8arr ctasegs m' A bs.
Proof.
  intros W m m' A bs [Hb Hw] MU D. split.
  - exact (bytes_at_transport ctasegs W m m' _ _ Hb MU D).
  - exact (wr_nw W m m' _ _ Hw MU D).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma reg_rep_nw : forall W SB c r (m m' : mem), reg_rep SB c r m -> munch W m m' -> reg_avoid W SB c r ->
  disjoint_from W (rb SB c + ClassSize c * Z.of_nat (length (r_st r))) (r_muser r - ClassSize c * Z.of_nat (length (r_st r))) ->
  disjoint_from W (shad (rb SB c)) (shad (rb SB c + 2 ^ 32) - shad (rb SB c)) ->
  reg_rep SB c r m'.
Proof.
  intros W SB c r m m' H MU (A1 & A2 & A3) S1A S2A.
  destruct H as (L & C & (rand & exh & pad & nal & nfr & r0 & r1 & r2 & r3 & T) & (ws & F & Hws & Hpre) & S1 & B & S2).
  unfold ri_lock, ri_core, ri_tail in *.
  split; [apply (rwc_nw W m m' _ _ L MU); cs_size; eapply dsj_sub; [exact A1| |]; lia|].
  split; [apply (rwc_nw W m m' _ _ C MU); cs_size; eapply dsj_sub; [exact A1| |]; lia|].
  split; [exists rand, exh, pad, nal, nfr, r0, r1, r2, r3; apply (rwc_nw W m m' _ _ T MU); cs_size;
          eapply dsj_sub; [exact A1| |]; lia|].
  split; [exists ws; split; [|split; [exact Hws | exact Hpre]]; unfold fl_arr in *;
          apply (u32_nw W m m' _ _ F MU); rewrite Hws; exact A2|].
  split; [apply (stk_nw W m m' _ _ S1 MU);
          replace (rb SB c + r_muser r - (rb SB c + ClassSize c * Z.of_nat (length (r_st r)))) with (r_muser r - ClassSize c * Z.of_nat (length (r_st r))) by ring;
          exact S1A|].
  split; [apply (bytes_at_transport ctasegs W m m' _ _ B MU); rewrite farun_len; exact A3|].
  exact (stk_nw W m m' _ _ S2 MU S2A).
Qed.

Lemma pclass_rep_nw : forall W T c init l (m m' : mem), pclass_rep T c init l m -> munch W m m' -> pclass_avoid W T c -> pclass_rep T c init l m'.
Proof.
  intros W T c init l m m' (P & chs & U & Hl & Hp) MU A. unfold pc_cells in *.
  split; [apply (rwc_nw W m m' _ _ P MU); cs_size; eapply dsj_sub; [exact A| |]; lia|].
  exists chs. split; [|split; [exact Hl | exact Hp]]. apply (u32_nw W m m' _ _ U MU). rewrite Hl. eapply dsj_sub; [exact A| |]; lia.
Qed.

Lemma ahdr_nw : forall W (m m' : mem) M n, ahdr m M n -> munch W m m' -> disjoint_from W M 16 -> ahdr m' M n.
Proof. intros W m m' M n (b1 & ctx & Hb & H) MU A. exists b1, ctx. split; [exact Hb|]. apply (rwc_nw W m m' _ _ H MU). cs_size. exact A. Qed.
Lemma qhdr3_nw : forall W (m m' : mem) M n, qhdr3 m M n -> munch W m m' -> disjoint_from W M 24 -> qhdr3 m' M n.
Proof. intros W m m' M n (b1 & ctx & fid & Hb & H) MU A. exists b1, ctx, fid. split; [exact Hb|]. apply (rwc_nw W m m' _ _ H MU). cs_size. exact A. Qed.
Lemma lch_nw : forall W (m m' : mem) AB M, lch m AB M -> munch W m m' -> disjoint_from W AB 16 -> lch m' AB M.
Proof. intros W m m' AB M H MU A. apply (rwc_nw W m m' _ _ H MU). cs_size. exact A. Qed.

Lemma pchunk_nw : forall W SB c i st (m m' : mem), pchunk SB c i st m -> munch W m m' -> pchunk_avoid W SB c i st ->
  disjoint_from W (p_abeg SB c i) (ClassSize c) -> pchunk SB c i st m'.
Proof.
  intros W SB c i st m m' H MU A AW. unfold pchunk, pchunk_avoid in *. destruct st as [|n|n|].
  - destruct H as [S B]. split; [apply (stk_nw W m m' _ _ S MU); replace (p_abeg SB c i + ClassSize c - p_abeg SB c i) with (ClassSize c) by ring; exact AW|].
    unfold pshadow_idle in *. apply (bytes_at_transport ctasegs W m m' _ _ B MU). rewrite farun_len. exact A.
  - destruct H as (Wr & Hh & Hl & B1 & B2). destruct A as (A1 & A2 & A3 & A4).
    split; [exact (wr_nw W m m' _ _ Wr MU AW)|]. split; [exact (ahdr_nw W m m' _ _ Hh MU A1)|].
    split; [intros Hr; exact (lch_nw W m m' _ _ (Hl Hr) MU (A2 Hr))|].
    split; [apply (bytes_at_transport ctasegs W m m' _ _ B1 MU); exact A3|].
    apply (bytes_at_transport ctasegs W m m' _ _ B2 MU). rewrite farun_len. exact A4.
  - destruct H as (Wr & Hh & Hl & B1). destruct A as (A1 & A2 & A3).
    split; [exact (wr_nw W m m' _ _ Wr MU AW)|]. split; [exact (qhdr3_nw W m m' _ _ Hh MU A1)|].
    split; [intros Hr; exact (lch_nw W m m' _ _ (Hl Hr) MU (A2 Hr))|].
    unfold pshadow_quar in *. apply (bytes_at_transport ctasegs W m m' _ _ B1 MU). exact A3.
  - unfold pshadow_idle in *. apply (bytes_at_transport ctasegs W m m' _ _ H MU). rewrite farun_len. exact A.
Qed.

Lemma schunk_nw : forall W k s (m m' : mem), schunk k s m -> munch W m m' -> schunk_avoid W s ->
  disjoint_from W (s_mb s) (smsz (s_n s)) -> disjoint_from W (shad (s_mb s)) (shad (s_mb s + smsz (s_n s)) - shad (s_mb s)) ->
  schunk k s m'.
Proof.
  intros W k s m m' H MU (A1 & A2 & A3 & A4 & A5 & A6) AW AS. unfold schunk in *.
  destruct H as (Hs & Wr & Hl & Hh & S & B1 & B2 & B3).
  split; [unfold shdr in *; apply (rwc_nw W m m' _ _ Hs MU); cs_size; exact A1|].
  split; [exact (wr_nw W m m' _ _ Wr MU AW)|]. split; [exact (lch_nw W m m' _ _ Hl MU A2)|].
  split; [destruct (s_quar s); [exact (qhdr3_nw W m m' _ _ Hh MU A3) | exact (ahdr_nw W m m' _ _ Hh MU A3)]|].
  split; [exact (stk_nw W m m' _ _ S MU AS)|].
  split; [apply (bytes_at_transport ctasegs W m m' _ _ B1 MU); rewrite farun_len; exact A4|].
  split; [apply (bytes_at_transport ctasegs W m m' _ _ B2 MU); exact A5|].
  apply (bytes_at_transport ctasegs W m m' _ _ B3 MU). rewrite farun_len. exact A6.
Qed.

(* [comment removed for export] *)
Ltac dsjn_lit H := match goal with |- disjoint_from ?W ?a ?n => eapply (dsj_sub W a _ a n); [eapply (dsjl_in _ _ a _ H); in_lit | lia | lia] end.
Ltac rwcn_litX H X := eapply (rwc_nw _ _ _ _ _ X); [eassumption |]; cs_size; dsjn_lit H.

Lemma sec_rep_nw : forall W Σ (m m' : mem), sec_rep Σ m -> munch W m m' -> sec_avoid W Σ -> sec_rep Σ m'.
Proof.
  intros W Σ m m' H MU (A & AP). unfold sec_rep, sec_core, sec_pad, sec_page, sec_range, sec_junk, name_cells in *.
  destruct H as ((C1 & C2 & C3) & P & (ws & U & Hl & Hf) & G & R & ((b & j & w1 & w2 & w3 & w4 & J1) & (bl & Hbl & J2) & (ga & gm & J3)) & N1 & N2).
  split; [split; [rwcn_litX A C1 | split; [rwcn_litX A C2 | rwcn_litX A C3]]|].
  split; [rwcn_litX A P|].
  split; [exists ws; split; [|split; [exact Hl | exact Hf]]; apply (u64_nw W m m' _ _ U MU); rewrite Hl; exact AP|].
  split; [rwcn_litX A G|]. split; [rwcn_litX A R|].
  split; [split; [exists b, j, w1, w2, w3, w4; rwcn_litX A J1 | split; [exists bl; split; [exact Hbl|] | exists ga, gm; rwcn_litX A J3]]|].
  - apply (u64_nw W m m' _ _ J2 MU). rewrite Hbl. dsjn_lit A.
  - split; [rwcn_litX A N1 | rwcn_litX A N2].
Qed.

Lemma qchain_nw : forall W (m m' : mem) bs, qchain m bs -> munch W m m' -> Forall (fun b => disjoint_from W (fst b) 8192) bs -> qchain m' bs.
Proof.
  intros W m m' bs. induction bs as [|[b ents] bs IH]; intros H MU A; [exact I|].
  apply Forall_cons_iff in A as [A1 A2]. cbn [fst] in A1. destruct H as [(H1 & (ws & U & Hl & Hf) & Hn) H2].
  split; [|exact (IH H2 MU A2)]. split; [apply (rwc_nw W m m' _ _ H1 MU); cs_size; eapply dsj_sub; [exact A1| |]; lia|].
  split; [|exact Hn]. exists ws. split; [|split; [exact Hl | exact Hf]]. apply (u64_nw W m m' _ _ U MU).
  rewrite Hl. eapply dsj_sub; [exact A1| |]; lia.
Qed.

Lemma quar_rep_nw : forall W Σ (m m' : mem), quar_rep Σ m -> munch W m m' -> quar_avoid W Σ -> quar_rep Σ m'.
Proof.
  intros W Σ m m' ((Q1 & C1) & (Q2 & C2) & X) MU (A1 & A2 & A3). apply Forall_app in A3 as [A3 A4].
  split; [split; [apply (rwc_nw W m m' _ _ Q1 MU); cs_size; exact A1 | exact (qchain_nw W m m' _ C1 MU A3)]|].
  split; [split; [rwcn_litX A2 Q2 | exact (qchain_nw W m m' _ C2 MU A4)]|]. rwcn_litX A2 X.
Qed.

Lemma depot_rep_nw : forall D BK DNB SSB lo W (m m' : mem), depot_rep D BK DNB SSB m -> depot_ok D DNB SSB lo ->
  munch W m m' ->
  disjoint_from W d_tab (d_nuniq + 4 - d_tab) -> disjoint_from W d_map1 8 -> disjoint_from W DNB (2 ^ 20) ->
  disjoint_from W s_total 8 -> disjoint_from W s_data0 (s_stored0 + 4 - s_data0) -> disjoint_from W SSB (2 ^ 23) ->
  depot_rep D BK DNB SSB m'.
Proof.
  intros D BK DNB SSB lo W m m' (TB & NU & M1 & ND & FS & TT & DT & SD & FF) OK MU H1 H2 H3 H4 H5 H6.
  destruct OK as (HF & Hn & Ht & HD1 & HD2 & HS1 & HS2 & HDS).
  unfold d_n in *. split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].
  - intros b Hb. destruct (TB b Hb) as [Rb C]. split; [exact Rb|].
    apply (rwc_nw W m m' _ _ C MU). cbn [cells_size csize Nat.add]. eapply dep_disj_sub; [exact H1| |]; lia.
  - apply (rwc_nw W m m' _ _ NU MU). cbn [cells_size csize Nat.add]. eapply dep_disj_sub; [exact H1| |]; lia.
  - apply (rwc_nw W m m' _ _ M1 MU). exact H2.
  - intros i Hi. unfold d_n in Hi. destruct (ND i Hi) as (sid & C). exists sid. apply (rwc_nw W m m' _ _ C MU).
    cbn [cells_size csize Nat.add]. eapply dep_disj_sub; [exact H3| |]; lia.
  - apply (stk_nw W m m' _ _ FS MU). eapply dep_disj_sub; [exact H3| |]; lia.
  - apply (rwc_nw W m m' _ _ TT MU). exact H4.
  - apply (rwc_nw W m m' _ _ DT MU). cbn [cells_size csize Nat.add]. eapply dep_disj_sub; [exact H5| |]; lia.
  - apply (rwc_nw W m m' _ _ SD MU). cbn [cells_size csize Nat.add]. eapply dep_disj_sub; [exact H5| |]; lia.
  - apply (stk_nw W m m' _ _ FF MU). eapply dep_disj_sub; [exact H6| |]; lia.
Qed.

Lemma dep_rep_nw : forall W L d (m m' : mem), dep_rep L d m -> depot_ok d (l_DNB L) (l_SSB L) (l_ACEIL L) ->
  munch W m m' -> dep_avoid W L -> dep_rep L d m'.
Proof.
  intros W L d m m' H OK MU (A & A5 & A6). unfold dep_rep in *.
  apply (depot_rep_nw d _ _ _ _ W m m' H OK MU); [exact (dsjl_in _ _ 0x753f18 _ A ltac:(in_lit)) | exact (dsjl_in _ _ 0xb53f28 _ A ltac:(in_lit)) | exact A5
    | exact (dsjl_in _ _ 0x743f08 _ A ltac:(in_lit)) | exact (dsjl_in _ _ 0x743f18 _ A ltac:(in_lit)) | exact A6].
Qed.

Lemma fs_free_frames_nw : forall FSB c (m m' : mem) fl W,
  fs_free_frames FSB c m fl -> munch W m m' ->
  (forall p, 0 <= p < NF c -> nth (Z.to_nat p) fl 1 = 0 ->
     disjoint_from W (frame_addr FSB c p) (fsz c) /\ disjoint_from W (shad (frame_addr FSB c p)) (fsz c / 8)) ->
  fs_free_frames FSB c m' fl.
Proof.
  intros FSB c m m' fl W H MU HD p Hp Hf.
  destruct (H p Hp Hf) as [[j1 H1] [j2 H2]]. destruct (HD p Hp Hf) as [D1 D2].
  assert (E1 : 0 <= fsz c) by (unfold fsz; pose proof (Z.pow_nonneg 2 c); lia).
  split; [exists j1; apply (rwc_nw W m m' _ _ H1 MU) | exists j2; apply (rwc_nw W m m' _ _ H2 MU)]; cbn [cells_size csize];
    rewrite Nat.add_0_r, Z2Nat.id; auto; apply Z.div_pos; lia.
Qed.

Lemma fs_cls_rep_nw : forall W FSB c f (m m' : mem), fs_cls_rep FSB c f m -> munch W m m' -> fs_cls_avoid W FSB c f -> fs_cls_rep FSB c f m'.
Proof.
  intros W FSB c f m m' (H1 & H2 & H3) MU (A1 & A2 & A3). unfold fs_hint, fs_flags in *.
  split; [apply (rwc_nw W m m' _ _ H1 MU); cs_size; exact A1|].
  split; [apply (u8_nw W m m' _ _ H2 MU); rewrite length_map; exact A2|].
  exact (fs_free_frames_nw FSB c m m' _ W H3 MU A3).
Qed.

Lemma fs_rep_nw : forall W Σ (m m' : mem), fs_rep Σ m -> munch W m m' -> fs_avoid W Σ ->
  Forall (fun fk => disjoint_from W (fst fk) (fs_size (snd fk)) /\ disjoint_from W (shad (fst fk)) (fs_size (snd fk) / 8)) (frames Σ) ->
  fs_rep Σ m'.
Proof.
  intros W Σ m m' H MU (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8) AB. unfold fs_rep, fs_const, tga_cells, dtls_cells, ttls_cells in *.
  destruct H as (F1 & F2 & F3 & F4 & T & (dtvbeg & Hdb & (G1 & G2 & G3 & G4 & (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8))) & (tb & te & TT) & FB).
  split; [apply (rwc_nw W m m' _ _ F1 MU); cs_size; exact A1|].
  split; [exact (fs_cls_rep_nw W _ _ _ m m' F2 MU A2)|].
  split; [exact (fs_cls_rep_nw W _ _ _ m m' F3 MU A3)|].
  split; [destruct F4 as (F4 & F4a & F4b); destruct A4 as (A4 & A4a & A4b); exact (conj (fs_cls_rep_nw W _ _ _ m m' F4 MU A4) (conj (fs_cls_rep_nw W _ _ _ m m' F4a MU A4a) (fs_cls_rep_nw W _ _ _ m m' F4b MU A4b)))|].
  split; [rwcn_litX A5 T|].
  split; [exists dtvbeg; split; [exact Hdb|]|split; [exists tb, te; apply (rwc_nw W m m' _ _ TT MU); cs_size; exact A7|]].
  2: { unfold fs_busy in *. apply Forall_forall. intros fk Hfk. destruct (proj1 (Forall_forall _ _) FB fk Hfk) as (p & Hp & W1 & W2 & Cw).
       destruct (proj1 (Forall_forall _ _) AB fk Hfk) as (B1 & B2).
       exists p. split; [exact Hp|]. split; [exact (wr_nw W m m' _ _ W1 MU B1)|]. split; [exact (wr_nw W m m' _ _ W2 MU B2)|].
       apply (rwc_nw W m m' _ _ Cw MU). cs_size. exact (proj1 (Forall_forall _ _) A8 fk Hfk). }
  split; [rwcn_litX A5 G1|]. split; [rwcn_litX A5 G2|]. split; [rwcn_litX A5 G3|]. split; [rwcn_litX A5 G4|].
  split; [rwcn_litX A5 D1|]. split; [rwcn_litX A5 D2|]. split; [rwcn_litX A5 D3|]. split; [rwcn_litX A5 D4|].
  split; [rwcn_litX A5 D5|]. split; [rwcn_litX A5 D6|]. split; [rwcn_litX A5 D7|].
  apply (rwc_nw W m m' _ _ D8 MU); cs_size; exact A6.
Qed.

Lemma ia_rep_nw : forall W Σ (m m' : mem), ia_rep Σ m -> munch W m m' -> dsjl W ia_lits -> ia_rep Σ m'.
Proof.
  intros W Σ m m' (b & H) MU A. unfold ia_rep, ia_state in *. exists b. destruct b.
  - destruct H as (W1 & MAP). split; [rwcn_litX A W1|].
    apply (u8_nw W m m' _ _ MAP MU). rewrite repeat_length. dsjn_lit A.
  - destruct H as (W1 & (j & J) & (b1 & L1 & B1) & (b2 & L2 & B2) & (b3 & L3 & B3) & (j4 & J4) & G & P).
    split; [rwcn_litX A W1|]. split; [exists j; rwcn_litX A J|].
    split; [exists b1; split; [exact L1|]; apply (u8_nw W m m' _ _ B1 MU); rewrite L1; dsjn_lit A|].
    split; [exists b2; split; [exact L2|]; apply (u8_nw W m m' _ _ B2 MU); rewrite L2; dsjn_lit A|].
    split; [exists b3; split; [exact L3|]; apply (u8_nw W m m' _ _ B3 MU); rewrite L3; dsjn_lit A|].
    split; [exists j4; rwcn_litX A J4|]. split; [rwcn_litX A G | rwcn_litX A P].
Qed.

Lemma shadow_rep_nw : forall W L (m m' : mem), shadow_rep L m -> munch W m m' -> shadow_avoid W L ->
  disjoint_from W (shad (l_ACEIL L)) (shad (2 ^ 47) - shad (l_ACEIL L)) ->
  disjoint_from W (pg_dn (shad 0x10000)) (shad SEGTOP_A - pg_dn (shad 0x10000)) ->
  shadow_rep L m'.
Proof.
  intros W L m m' (B & S1 & S2 & SA & LS) MU (A & AS) D1 D2.
  split; [|split; [exact (stk_nw W m m' _ _ S1 MU D1) | split; [exact (stk_nw W m m' _ _ S2 MU D2)| split]]].
  - apply (bytes_at_transport ctasegs W m m' _ _ B MU). unfold zrun. rewrite repeat_length.
    replace (Z.of_nat (Z.to_nat ((2 ^ 47 - l_ACEIL L) / 8))) with (Z.max 0 ((2 ^ 47 - l_ACEIL L) / 8)) by lia. exact A.
  - unfold static_acc in *. apply Forall_forall. intros r Hr. pose proof (proj1 (Forall_forall _ _) SA r Hr) as X.
    pose proof (proj1 (Forall_forall _ _) AS r (or_intror Hr)) as D. cbv beta in X, D.
    assert (Hlh : fst r < snd r) by (unfold CS_ACC in Hr; repeat (destruct Hr as [Hr|Hr]; [subst r; cbn; lia|]); destruct Hr).
    apply (acc_transport W m m' _ _ X MU ltac:(lia)). replace (fst r + (snd r - fst r) - 1) with (snd r - 1) by lia. exact D.
  - exact (lib_sh_transport W m m' LS MU (proj1 (Forall_forall _ _) AS IMG_HULL (or_introl eq_refl))).
Qed.

(* [comment removed for export] *)
Ltac rwcn_frameX X := eapply (rw_cells_agree_nw ctasegs _ _ _ _ X); eapply agree_sub; [match goal with H : agree_on (in_rngs _) _ _ |- _ => exact H end|];
  let x := fresh "x" in let Hx := fresh "Hx" in
  intros x Hx; cbn [cells_size csize Nat.add] in Hx; unfold consts_rngs; unfold_consts; first [rng_fast Hx | in_rng_search].
Ltac rwcn_frame := eapply rw_cells_agree_nw; [eassumption | eapply agree_sub; [match goal with H : agree_on (in_rngs _) _ _ |- _ => exact H end|]];
  let x := fresh "x" in let Hx := fresh "Hx" in
  intros x Hx; cbn [cells_size csize Nat.add] in Hx; unfold consts_rngs; unfold_consts; first [rng_fast Hx | in_rng_search].

Ltac rocn_frame := eapply ro_cells_agree; [eassumption | eapply agree_sub; [match goal with H : agree_on (in_rngs _) _ _ |- _ => exact H end|]];
  let x := fresh "x" in let Hx := fresh "Hx" in
  intros x Hx; cbn [cells_size csize Nat.add] in Hx; unfold consts_rngs; unfold_consts; first [rng_fast Hx | in_rng_search].
Ltac rocn_frameX X := eapply (ro_cells_agree ctasegs _ _ _ _ X); eapply agree_sub; [match goal with H : agree_on (in_rngs _) _ _ |- _ => exact H end|];
  let x := fresh "x" in let Hx := fresh "Hx" in
  intros x Hx; cbn [cells_size csize Nat.add] in Hx; unfold consts_rngs; unfold_consts; first [rng_fast Hx | in_rng_search].

Lemma consts_rep_nw : forall L (m m' : mem), consts_rep L m -> agree_on (in_rngs (consts_rngs L)) m m' ->
  agree_on (fun x => l_T L + 2768 <= x < l_T L + 3168) m m' -> consts_rep L m'.
Proof.
  intros L m m' H HA HA2.
  destruct H as ((I1 & I2) & (G1 & G2 & G3 & G4 & G5) & ((T1 & T2 & T3 & T4) & T5) & (M1 & M2 & M3) & (P1 & PM & (S1 & S2) & P3 & P4)
                 & (K1 & K2) & (C1 & C2 & C3 & C4 & C5) & (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15 & X16 & X17 & X18 & X19 & X20 & X21 & X22 & X23 & X24
                    & X25 & X26 & X27 & X28 & X29 & X30 & X31 & X32 & X33 & X34 & X35 & X36 & X37 & X38 & X39 & X40 & X41 & XA & X42 & X43)).
  assert (M' : m2s_cells m') by (split; [rwcn_frame | split; [rwcn_frame | rwcn_frame]]).
  split; [split; [rwcn_frame | rwcn_frame]|].
  split; [split; [rwcn_frame | split; [rwcn_frame | split; [rwcn_frame | split; [rwcn_frame | rwcn_frame]]]]|].
  split; [split; [split; [rwcn_frame | split; [rwcn_frame | split; [rwcn_frame | rwcn_frame]]] | rwcn_frame]|].
  split; [exact M'|].
  split; [split; [rwcn_frame | split; [exact M' | split; [split; [rwcn_frame | rwcn_frame] | split; [rwcn_frame | rwcn_frame]]]]|].
  split; [split; [rwcn_frame | rwcn_frame]|].
  split; [split; [rocn_frame | split; [rocn_frame | split; [rocn_frame | split; [rocn_frame |]]]]|].
  { intros a Ha. rewrite <- (C5 a Ha). unfold mrd. rewrite (HA a); [reflexivity|]. unfold RELRO_LO, RELRO_HI in Ha. apply (in_rngs_same _ 0x533000 0x5ac000); [unfold consts_rngs; solve [repeat (first [left; reflexivity | right])] | exact Ha]. }
  split; [rwcn_frameX X1|]. split; [rocn_frameX X2|]. split; [rocn_frameX X3|]. split; [rocn_frameX X4|]. split; [rocn_frameX X5|]. split; [rocn_frameX X6|].
  split; [rocn_frameX X7|]. split; [rwcn_frameX X8|]. split; [rocn_frameX X9|]. split; [rocn_frameX X10|]. split; [rocn_frameX X11|]. split; [rocn_frameX X12|].
  split; [rocn_frameX X13|]. split; [rocn_frameX X14|]. split; [rocn_frameX X15|]. split; [rocn_frameX X16|]. split; [rocn_frameX X17|]. split; [rocn_frameX X18|].
  split; [rwcn_frameX X19|]. split; [rwcn_frameX X20|]. split; [rwcn_frameX X21|]. split; [rwcn_frameX X22|]. split; [rwcn_frameX X23|]. split; [rwcn_frameX X24|].
  split; [rwcn_frameX X25|]. split; [rwcn_frameX X26|]. split; [rwcn_frameX X27|]. split; [rwcn_frameX X28|]. split; [rwcn_frameX X29|]. split; [rwcn_frameX X30|].
  split; [rwcn_frameX X31|].
  split; [exact (stk_agree_nw ctasegs m m' _ _ X32 HA2)|].
  split; [rwcn_frameX X33|]. split; [rwcn_frameX X34|]. split; [rwcn_frameX X35|]. split; [rwcn_frameX X36|].
  split; [rwcn_frameX X37|]. split; [rwcn_frameX X38|]. split; [rwcn_frameX X39|]. split; [rwcn_frameX X40|]. split; [rwcn_frameX X41|].
  split; [rocn_frameX XA|].   (* [comment removed for export] *)
  unfold io_rw, io_ro in *. split.
  - repeat match goal with X : Forall _ (_ :: _) |- Forall _ (_ :: _) =>
      let Y := fresh "Y" in apply Forall_cons_iff in X as [Y X]; apply Forall_cons; [cbn [fst snd] in Y |- *; rwcn_frameX Y|] end.
    apply Forall_nil.
  - repeat match goal with X : Forall _ (_ :: _) |- Forall _ (_ :: _) =>
      let Y := fresh "Y" in apply Forall_cons_iff in X as [Y X]; apply Forall_cons; [cbn [fst snd] in Y |- *; rocn_frameX Y|] end.
    apply Forall_nil.
Qed.

(* [comment removed for export] *)
Lemma vis_rep_nw : forall W L A (m m' : mem), vis_rep L A m -> munch W m m' -> (forall z, shreg z -> outside W z) -> vis_rep L A m'.
Proof.
  intros W L A m m' H MU HW a Hs Hp Hlo Hx. rewrite (MU a (HW _ Hs)). exact (H a Hs Hp Hlo Hx).
Qed.
