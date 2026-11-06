(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX Frame SFModel.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import RSegs RMalloc_iface_stmt HeapSR_iface ECH_Img ECH_Xpres ECH_SR ECH_Kit ECH_Kit2 ECH_KitH ECH_Rep
     ECH_LibState ECH_LibStateMF ECH_LibFrame ECH_LibMid ECH_Rostr ECH_C1_stmt ECH_C1_malloc ECH_C1_dup ECH_C1_free ECH_C3_stmt ECH_C4_stmt ECH_C4_frame ECH_C4_frame2 ECH_C4_raise ECH_C4
     ECH_C5_stmt ECH_C6_stmt ECH_C7_stmt ECH_C9_stmt ECH_C10_stmt ECH_C10 ECH_C13_stmt ECH_C13_ext ECH_C13_entry ECH_C13_store ECH_C14_stmt ECH_KitSeg F_time F_memchr
     ECH_C14_bio2buf ECH_C14_ladder ECH_C14_ladloop ECH_C14_tail ECH_C14_b2b ECH_C14_fcc ECH_C14_decexts_seg ECH_C14_decexts ECH_C14_dec ECH_C14_entry_seg.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc Prog.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition ENT0 (pe : bptr) : entrep := mkENT 0 0 None 0 0 None 0 0 None 0 0 0 None 0 0 0 0 None pe.
Lemma ENT0_cells : forall pe, cells_bytes (entry_cells (ENT0 pe) (zeros 6) (zeros 4) (zeros 6) (zeros 4)) = zeros (Z.to_nat ENTRY_SIZE).
Proof. intros pe. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Lemma F3_cb : forall {HCEIL : HeapCeil} m A v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10,
  rw_cells rsegs m A (F3W v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10) -> rw_cells rsegs m A [CB 88 (cells_bytes (F3W v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10))].
Proof.
  intros HC m A v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 RC. eapply rw_cells_recut; [exact RC| |].
  - cbn [cells_wf cell_wf]. split; [| exact I]. rewrite (cells_bytes_length _ (proj1 (proj1 RC))). reflexivity.
  - reflexivity.
Qed.

Section RC.
  Context {HCEIL : HeapCeil}.
  Variable H : hsr.
  Hypothesis HX : heap_sr_hyps_x H.
  Hypothesis CERTO3 : egs_fresh_stmt H.
  Let HH : heap_sr_hyps H := proj1 HX.
  Let HRE : realloc_sr_stmt H := proj1 (proj2 HX).
  Let STATICS : statics_of_RHEAP H := proj1 (proj2 (proj2 (proj2 (proj2 HX)))).
  Let PERM : RHEAP_perm_law H := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HX))))).

  (* [comment removed for export] *)
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : PState) (LIB LB : list block)
            (M : libmid) (x : ctxinfo) (st mb lo B : Z) (S : storerep) (R : membio) (ds : list byte) (errv : word).
  Hypotheses (A0 : a0 = Z_to_bv 64 st) (A1 : a1 = Z_to_bv 64 mb)
             (SO : STOREobj LB m st S) (SE : es_entries S = 0) (SEO : es_entries_o S = None) (STL : st + STORE_SIZE <= lo)
             (MBO : MEMBIO LB m mb R) (MP0 : mb_pos R = 0) (MN0 : mb_nread R = 0) (MBB : MEMBIO_below mb R lo) (MBS : MEMBIO_sep mb R)
             (DS : bytes_at rsegs m (mb_buf R) ds) (DSL : zlength ds = mb_len R)
             (PAYL : 1 <= mb_len R -> exists pD, In (pD, mb_buf R, mb_len R) LB /\ forall b, In b LIB -> blk_id b <> pD)
             (NDsm : List.NoDup (map blk_id ((es_id S, st, STORE_SIZE) :: blocks_MEMBIO mb R)))
             (LM : LIBMID LIB m M) (SUBL : forall b, In b LIB -> In b LB) (CTX : mid_ctx M = CtxReady x) (MF1 : mid_flag M = 1)
             (DJ6 : forall b b', In b LIB -> In b' ((es_id S, st, STORE_SIZE) :: blocks_MEMBIO mb R) -> blk_id b <> blk_id b')
             (HP : hs_RHEAP H s (mid_errblocks M ++ LB) m) (KREL : hs_KREL H s mo)
             (BUD : lb_bytes (mid_errblocks M ++ LB) + mid_bytes M + DECODE_BYTES + ERRSTR_BYTES <= hs_LIVE_MAX H)
             (BUDC : Z.of_nat (length (mid_errblocks M ++ LB)) + mid_cnt M + DECODE_CNT + ERRSTR_CNT <= hs_LIVE_CNT_MAX H)
             (BUDG : lb_big (mid_errblocks M ++ LB) + mid_big M + DECODE_BIG <= hs_LIVE_BIG_MAX H)
             (AUX : hs_rauxv_ok H m B) (SPB : bv_unsigned sp <= B) (BHI : B < 2^64) (SPA : bv_unsigned sp mod 16 = 0)
             (ST : stk rsegs m lo (bv_unsigned sp)) (CEIL : hceil <= lo) (LO : lo <= bv_unsigned sp - READCFG_STACK M)
             (ERR : rw_cells rsegs m (errno_addr tp) [C4 errv]) (MI : mem_inv rsegs m) (TP : tp = Z_to_bv 64 RATP) (RAE : bv_unsigned ra mod 2 = 0).

  (* [comment removed for export] *)
  Local Notation L0c := (L0 LB M).
  Local Notation SPc := (SP' sp).
  Local Notation RBPc := (RBP sp).
  Local Notation POSTc := (POST H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo s LIB LB M st mb lo B S R ds).
  Local Notation SAVESc := (SAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
  Local Notation XFc := (XF M st mb R).

  (* [comment removed for export] *)
  Variables (p : bptr) (A nA : Z) (pbin : bptr) (Bb nB : Z) (bs : list byte) (R' : membio) (jt : list byte) (bt : Z) (TB : list block).
  Variable BT : mem -> Prop.
  Hypotheses (NAR : 1 <= mb_len R <= nA /\ nA <= 512 * 3)                 (* [comment removed for export] *)
             (NBR : 0 <= zlength bs <= nB /\ nB <= mb_len R /\ mb_len R < OSSL_ECH_MAX_ECHCONFIG_LEN)
             (MST : mb_static R R') (POS : mb_pos R' = mb_len R)
             (BTR : 0 <= bt < 2^64 /\ Z.of_nat (length TB) <= 7 /\ lb_bytes TB <= 3072 /\ lb_big TB <= 1)
             (BT_frame : forall (L : list block) (SP : Z) (X : list (Z * Z)) (m1 m2 : mem),
                 BT m1 -> xpres L SP X m1 m2 -> (forall b, In b TB -> In b L) -> hceil <= SP ->
                 Forall (fun iv : Z * Z => Forall (fun b => blk_addr b + blk_size b <= fst iv \/ snd iv <= blk_addr b) TB) X ->
                 BT m2).
  Local Notation DREST := (drest LB p A nA pbin Bb nB TB).
  Local Notation DFR := (dframe st).
  Local Notation DBUD := (dbud H).
  Local Notation DWK := (dwk H ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m mo LIB LB M st mb lo B S R ds p A nA pbin Bb nB bs R' jt TB BT).
  Local Notation KOKp := (dK_ok H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo s LIB LB M st mb lo B S R ds p A nA pbin Bb nB bs R' jt bt TB BT).
  Local Notation KSKp := (dK_skip H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo s LIB LB M st mb lo B S R ds p A nA pbin Bb nB bs R' jt bt TB BT).
  Local Notation KTAp := (dK_tailA H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo s LIB LB M st mb lo B S R ds p A nA pbin Bb nB bs R' jt bt TB BT).
  Local Notation KTZp := (dK_tailZ H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo s LIB LB M st mb lo B S R ds p A nA pbin Bb nB bs R' jt bt TB BT).
  Local Notation RPES := (rp_entry_stmt H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo s LIB LB M st mb lo B S R ds p A nA pbin Bb nB bs R' jt bt TB BT).
  Local Notation DWK_W := (dwk_w H HX ra sp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m mo s LIB LB M x st mb lo B S R ds errv A0 A1 SO SE SEO STL MBO MP0 MN0 MBB MBS DS DSL PAYL NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC BUDG AUX SPB BHI SPA ST CEIL LO ERR MI TP RAE p A nA pbin Bb nB bs R' jt bt TB BT NAR NBR MST POS BTR BT_frame).
  Local Notation DWK_X := (dwk_x H HX ra sp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m mo s LIB LB M x st mb lo B S R ds errv A0 A1 SO SE SEO STL MBO MP0 MN0 MBB MBS DS DSL PAYL NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC BUDG AUX SPB BHI SPA ST CEIL LO ERR MI TP RAE p A nA pbin Bb nB bs R' jt bt TB BT NAR NBR MST POS BTR BT_frame).
  Local Notation DWK_LIB := (dwk_lib H HX ra sp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m mo s LIB LB M x st mb lo B S R ds errv A0 A1 SO SE SEO STL MBO MP0 MN0 MBB MBS DS DSL PAYL NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC BUDG AUX SPB BHI SPA ST CEIL LO ERR MI TP RAE p A nA pbin Bb nB bs R' jt bt TB BT NAR NBR MST POS BTR BT_frame).
  Local Notation DWK_ES := (dwk_es H ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m mo LIB LB M x st mb lo B S R ds CTX p A nA pbin Bb nB bs R' jt TB BT).
  Local Notation DWK_HF := (dwk_heap_facts H HX ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m mo LIB LB M st mb lo B S R ds p A nA pbin Bb nB bs R' jt TB BT).
  Local Notation DREST_SUB := (drest_sub LIB LB SUBL p A nA pbin Bb nB TB).
  Local Notation DREST_IDS := (drest_ids LB p A nA pbin Bb nB TB).
  Local Notation XOMD := (xpres_of_munch_drest H HX sp m LIB LB M lo SUBL ST CEIL LO p A nA pbin Bb nB TB).

  Local Notation RCFACTS := (rc_facts H HX ra sp tp a0 a1 m mo s LIB LB M x st mb lo B S R ds errv A0 A1 SO SE SEO STL MBO MP0 MN0 MBB MBS DS DSL PAYL NDsm LM SUBL CTX MF1 DJ6
                              HP KREL BUD BUDC BUDG AUX SPB BHI SPA ST CEIL LO ERR MI TP RAE).

  Let EGS : egs_stmt H := ECH_C4_egs.egs_spec H HH CERTO3.

  (* [comment removed for export] *)
  Lemma de_facts : forall Lx NB S' M' LE w0 w1 w3 w4 w5 w6 w9 w10 j3 m' mo' s',
    DWK Lx NB S' M' LE w0 w1 w3 w4 w5 w6 w9 w10 j3 m' mo' s' ->
       hceil <= bv_unsigned sp + -2352 /\ SPc = bv_unsigned sp + -2352 /\ SPc + O_F3 = bv_unsigned sp + -192
    /\ 0 < Bb /\ Bb + zlength bs <= hceil /\ In (pbin, Bb, nB) (mid_errblocks M' ++ DREST Lx NB LE) /\ zlength bs <= nB /\ nB < 2^11
    /\ (forall b, In b Lx -> Bb + zlength bs <= blk_addr b \/ blk_addr b + blk_size b <= Bb)
    /\ (forall b, In b (mid_errblocks M' ++ DREST Lx NB LE) -> blk_addr b + blk_size b <= hceil)
    /\ mid_flag M' = 1 /\ MEMFLAG m' 1 /\ IMPL_mem m' /\ GOT_mem m' /\ GOT_echfree m'.
  Proof.
    intros until s'. intros DW.
    pose proof DW as (HP1 & KREL1 & MP1 & LM1 & STP & NEW & CTX1 & EC & EB & EG & LC & LBY & LG & SO1 & SID & SPM & SND & SKI & MBO1 & DSm1 & DSb1 & BT1
                      & FR0 & FR2 & FR3 & FR4 & [errv1 ERR1] & MI1 & ST1 & AUX1 & XA1 & DNB1).
    destruct (DWK_HF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ DW) as (HB & ND & DISJ & BRS & D2 & D1).
    pose proof (DREST_SUB Lx NB LE) as (SLB & S0 & SLE & SNB & STB & IB & IA & SLX & S3 & SLL).
    hcb. pose proof (readcfg_stack_lo M) as STK0. pose proof LM1 as (IM & MF & _ & _ & _ & _ & _ & _ & G1 & G2 & _). pose proof STP as (F1 & _). rewrite F1 in MF.
    assert (IB2 : In (pbin, Bb, nB) (mid_errblocks M' ++ DREST Lx NB LE)) by (apply in_or_app; right; exact IB).
    pose proof (HB _ IB2) as BH. pose proof (BRS _ IB2) as (BP & _). cbn [blk_addr blk_size fst snd] in BH, BP.
    repeat match goal with |- _ /\ _ => split end; try assumption.
    - unfold SP'. clear - CEIL LO STK0. lia.
    - unfold SP'. clear. lia.
    - unfold SP', O_F3. clear. lia.
    - clear - BH NBR. lia.
    - clear - NBR. lia.
    - unfold OSSL_ECH_MAX_ECHCONFIG_LEN in NBR. clear - NBR. lia.
    - intros b Hb. pose proof (DISJ b (pbin, Bb, nB) ltac:(apply in_or_app; right; apply SLX; exact Hb) IB2 ltac:(apply (D2 b (pbin, Bb, nB) Hb); exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (DREST_SUB [] NB LE))))))))) as K.
      cbn [blk_addr blk_size fst snd] in K. clear - K NBR. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma lx_not_client : forall Lx NB LE M' s' m' b a X,
    hs_RHEAP H s' (mid_errblocks M' ++ DREST Lx NB LE) m' -> In b Lx -> blk_addr b <= a < blk_addr b + blk_size b ->
    xclient (DREST [] NB LE) SPc X a -> False.
  Proof.
    intros Lx NB LE M' s' m' b a X HP' Hb Ha [HC _]. hcb. pose proof (readcfg_stack_lo M) as STK0.
    assert (BIN' : In b (mid_errblocks M' ++ DREST Lx NB LE)) by (apply in_or_app; right; rewrite drest_app; apply in_or_app; left; exact Hb).
    pose proof (HH_blocks_below H HH _ _ _ HP' _ BIN') as BH. pose proof (HH_RHEAP_block_range H HH _ _ _ _ HP' BIN') as BR.
    destruct HC as [HC|[[HC _]|(b' & Hb' & Hr')]].
    - unfold SP' in HC. clear - HC BH Ha CEIL LO STK0. lia.
    - pose proof (block_cell_off_image _ _ BR Ha) as K. unfold IMG_LO, IMG_HI in K. clear - K HC. lia.
    - pose proof (HH_RHEAP_blocks_nodup H HH _ _ _ HP') as ND. destruct (DREST_IDS _ _ _ _ ND) as (_ & D2 & _).
      pose proof (HH_RHEAP_blocks_disjoint H HH _ _ _ _ _ HP' BIN' ltac:(apply in_or_app; right; rewrite drest_app; apply in_or_app; right; exact Hb') (D2 _ _ Hb Hb')) as DJ.
      clear - DJ Ha Hr'. lia.
  Qed.

  (* [comment removed for export] *)
  Definition ENT1 (pe : bptr) : entrep := mkENT ECH_VERSION 0 None 0 0 None 0 0 None 0 0 0 None 0 0 0 0 None pe.

  (* [comment removed for export] *)
  Lemma F3_words : forall m A1 j3, rw_cells rsegs m A1 [CB 88 j3] ->
    exists v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10, rw_cells rsegs m A1 (F3W v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10).
  Proof.
    clear. intros m A1 j3 FR3. change 88%nat with (8 * 11)%nat in FR3. destruct (CB_words 11 _ _ _ _ FR3) as (ws & LW & F3w). rewrite app_nil_r in F3w.
    destruct ws as [|v0 [|v1 [|v2 [|v3 [|v4 [|v5 [|v6 [|v7 [|v8 [|v9 [|v10 [|? ?]]]]]]]]]]]]; try (cbn in LW; discriminate LW). cbn [map] in F3w.
    exists v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10. exact F3w.
  Qed.
  Lemma F3_pk : forall m A1 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10,
    rw_cells rsegs m A1 (F3W v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10) -> rw_cells rsegs m (A1 + 48) [C8 v6; C8 v7; C8 v8].
  Proof.
    clear. intros until v10. intros RC. change (F3W v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10) with ([C8 v0; C8 v1; C8 v2; C8 v3; C8 v4; C8 v5] ++ [C8 v6; C8 v7; C8 v8] ++ [C8 v9; C8 v10]) in RC.
    apply rw_cells_app in RC as [_ RC]. apply rw_cells_app in RC as [RC _]. cbn [cells_size csize Nat.add Nat.mul Z.of_nat Pos.of_succ_nat Pos.succ] in RC. exact RC.
  Qed.

  (* [comment removed for export] *)
  Definition upd_pub (E : entrep) (len P : Z) (o : oblk) : entrep :=
    mkENT (en_version E) (en_pname E) (en_pname_o E) len P o (en_nsuites E) (en_suites E) (en_suites_o E) (en_maxname E) (en_cfgid E)
          (en_exts E) (en_exts_o E) (en_loadtime E) (en_forretry E) (en_enclen E) (en_encoded E) (en_encoded_o E) (en_id E).
  Definition entry_pre (E : entrep) (pad1 : list byte) : list cell := [C2 (wz (en_version E)); CB 6 pad1; C8 (wz (en_pname E))].
  Definition entry_suf (E : entrep) (pad2 pad3 pad4 : list byte) : list cell :=
    [C4 (wz (en_nsuites E)); CB 4 pad2; C8 (wz (en_suites E)); C1 (b8 (en_maxname E)); C1 (b8 (en_cfgid E)); CB 6 pad3;
     C8 (wz (en_exts E)); C8 (wz (en_loadtime E)); C8 (wz 0); C4 (wz (en_forretry E)); CB 4 pad4; C8 (wz (en_enclen E)); C8 (wz (en_encoded E))].
  Lemma entry_split_pub : forall m ee E pad1 pad2 pad3 pad4,
    rw_cells rsegs m ee (entry_cells E pad1 pad2 pad3 pad4) ->
    rw_cells rsegs m ee (entry_pre E pad1) /\ rw_cells rsegs m (ee + 16) [C8 (wz (en_publen E))] /\ rw_cells rsegs m (ee + 24) [C8 (wz (en_pub E))]
    /\ rw_cells rsegs m (ee + 32) (entry_suf E pad2 pad3 pad4).
  Proof.
    clear. intros until pad4. intros RC.
    change (entry_cells E pad1 pad2 pad3 pad4) with (entry_pre E pad1 ++ [C8 (wz (en_publen E))] ++ [C8 (wz (en_pub E))] ++ entry_suf E pad2 pad3 pad4) in RC.
    apply rw_cells_app in RC as [P RC]. apply rw_cells_app in RC as [L RC]. apply rw_cells_app in RC as [D RC].
    cbn [entry_pre entry_suf cells_size csize Nat.add Nat.mul Z.of_nat Pos.of_succ_nat Pos.succ] in L, D, RC.
    replace (ee + 16 + 8) with (ee + 24) in D by lia. replace (ee + 16 + 8 + 8) with (ee + 32) in RC by lia.
    split; [exact P|]. split; [exact L|]. split; [exact D| exact RC].
  Qed.
  Lemma entry_join_pub : forall m ee E pad1 pad2 pad3 pad4 len P o,
    rw_cells rsegs m ee (entry_pre E pad1) -> rw_cells rsegs m (ee + 16) [C8 (wz len)] -> rw_cells rsegs m (ee + 24) [C8 (wz P)] ->
    rw_cells rsegs m (ee + 32) (entry_suf E pad2 pad3 pad4) ->
    rw_cells rsegs m ee (entry_cells (upd_pub E len P o) pad1 pad2 pad3 pad4).
  Proof.
    clear. intros until o. intros P1 L1 D1 S1.
    change (entry_cells (upd_pub E len P o) pad1 pad2 pad3 pad4) with (entry_pre E pad1 ++ [C8 (wz len)] ++ [C8 (wz P)] ++ entry_suf E pad2 pad3 pad4).
    apply rw_cells_app. split; [exact P1|]. apply rw_cells_app. cbn [entry_pre entry_suf cells_size csize Nat.add Nat.mul Z.of_nat Pos.of_succ_nat Pos.succ]. split; [exact L1|].
    apply rw_cells_app. cbn [entry_pre entry_suf cells_size csize Nat.add Nat.mul Z.of_nat Pos.of_succ_nat Pos.succ].
    replace (ee + 16 + 8) with (ee + 24) by lia. replace (ee + 24 + 8) with (ee + 32) by lia. split; [exact D1| exact S1].
  Qed.

  (* [comment removed for export] *)
  Lemma F3_uncb : forall m A1 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10,
    rw_cells rsegs m A1 [CB 88 (cells_bytes (F3W v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10))] -> rw_cells rsegs m A1 (F3W v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10).
  Proof. clear. intros until v10. intros RC. eapply rw_cells_recut; [exact RC| cbn; repeat split| reflexivity]. Qed.
  Lemma F3_split3 : forall m A1 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10,
    rw_cells rsegs m A1 (F3W v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10) ->
    rw_cells rsegs m A1 [C8 v0; C8 v1; C8 v2] /\ rw_cells rsegs m (A1 + 24) [C8 v3; C8 v4; C8 v5; C8 v6; C8 v7; C8 v8; C8 v9; C8 v10].
  Proof.
    clear. intros until v10. intros RC. change (F3W v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10) with ([C8 v0; C8 v1; C8 v2] ++ [C8 v3; C8 v4; C8 v5; C8 v6; C8 v7; C8 v8; C8 v9; C8 v10]) in RC.
    apply rw_cells_app in RC as [R1 R2]. cbn [cells_size csize Nat.add Nat.mul Z.of_nat Pos.of_succ_nat Pos.succ] in R2. split; [exact R1| exact R2].
  Qed.
  Lemma F3_join3 : forall m A1 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10,
    rw_cells rsegs m A1 [C8 v0; C8 v1; C8 v2] -> rw_cells rsegs m (A1 + 24) [C8 v3; C8 v4; C8 v5; C8 v6; C8 v7; C8 v8; C8 v9; C8 v10] ->
    rw_cells rsegs m A1 (F3W v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10).
  Proof.
    clear. intros until v10. intros R1 R2. change (F3W v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10) with ([C8 v0; C8 v1; C8 v2] ++ [C8 v3; C8 v4; C8 v5; C8 v6; C8 v7; C8 v8; C8 v9; C8 v10]).
    apply rw_cells_app. cbn [cells_size csize Nat.add Nat.mul Z.of_nat Pos.of_succ_nat Pos.succ]. split; [exact R1| exact R2].
  Qed.

  (* [comment removed for export] *)
  Definition upd_pname (E : entrep) (P : Z) (o : oblk) : entrep :=
    mkENT (en_version E) P o (en_publen E) (en_pub E) (en_pub_o E) (en_nsuites E) (en_suites E) (en_suites_o E) (en_maxname E) (en_cfgid E)
          (en_exts E) (en_exts_o E) (en_loadtime E) (en_forretry E) (en_enclen E) (en_encoded E) (en_encoded_o E) (en_id E).
  Definition entry_pre0 (E : entrep) (pad1 : list byte) : list cell := [C2 (wz (en_version E)); CB 6 pad1].
  Definition entry_suf16 (E : entrep) (pad2 pad3 pad4 : list byte) : list cell := [C8 (wz (en_publen E))] ++ [C8 (wz (en_pub E))] ++ entry_suf E pad2 pad3 pad4.
  Lemma entry_split_pname : forall m ee E pad1 pad2 pad3 pad4,
    rw_cells rsegs m ee (entry_cells E pad1 pad2 pad3 pad4) ->
    rw_cells rsegs m ee (entry_pre0 E pad1) /\ rw_cells rsegs m (ee + 8) [C8 (wz (en_pname E))] /\ rw_cells rsegs m (ee + 16) (entry_suf16 E pad2 pad3 pad4).
  Proof.
    clear. intros until pad4. intros RC.
    change (entry_cells E pad1 pad2 pad3 pad4) with (entry_pre0 E pad1 ++ [C8 (wz (en_pname E))] ++ entry_suf16 E pad2 pad3 pad4) in RC.
    apply rw_cells_app in RC as [P RC]. apply rw_cells_app in RC as [L RC].
    cbn [entry_pre0 cells_size csize Nat.add Nat.mul Z.of_nat Pos.of_succ_nat Pos.succ] in L, RC. replace (ee + 8 + 8) with (ee + 16) in RC by lia.
    split; [exact P|]. split; [exact L| exact RC].
  Qed.
  Lemma entry_join_pname : forall m ee E pad1 pad2 pad3 pad4 P o,
    rw_cells rsegs m ee (entry_pre0 E pad1) -> rw_cells rsegs m (ee + 8) [C8 (wz P)] -> rw_cells rsegs m (ee + 16) (entry_suf16 E pad2 pad3 pad4) ->
    rw_cells rsegs m ee (entry_cells (upd_pname E P o) pad1 pad2 pad3 pad4).
  Proof.
    clear. intros until o. intros P1 L1 S1.
    change (entry_cells (upd_pname E P o) pad1 pad2 pad3 pad4) with (entry_pre0 E pad1 ++ [C8 (wz P)] ++ entry_suf16 E pad2 pad3 pad4).
    apply rw_cells_app. split; [exact P1|]. apply rw_cells_app. cbn [entry_pre0 cells_size csize Nat.add Nat.mul Z.of_nat Pos.of_succ_nat Pos.succ]. split; [exact L1|].
    replace (ee + 8 + 8) with (ee + 16) by lia. exact S1.
  Qed.

  (* [comment removed for export] *)
  Lemma strnlen_full' : forall ns, ~ In (Z_to_bv 8 0) ns -> strnlen ns = length ns.
  Proof.
    clear. induction ns as [|b ns IH]; intros NI; [reflexivity|]. cbn [strnlen length].
    destruct (bv_unsigned b =? 0) eqn:E.
    - exfalso. apply NI. left. apply Z.eqb_eq in E. apply bv_eq. rewrite E. reflexivity.
    - f_equal. apply IH. intros K. apply NI. right. exact K.
  Qed.
  (* [comment removed for export] *)
  Lemma strndup_bytes : forall m D ns, rw_cells rsegs m D [CB (length ns) ns; C1 (b8 0)] -> bytes_at rsegs m D (ns ++ [Z_to_bv 8 0]).
  Proof. clear. intros m D ns [[_ BA] _]. cbn [cells_bytes cbytes app] in BA. rewrite app_nil_r in BA || idtac. exact BA. Qed.

  (* [comment removed for export] *)
  Lemma drest_newlib_perm : forall Lx NB LBN LE, Permutation (DREST Lx NB (LBN ++ LE)) (LBN ++ DREST Lx NB LE).
  Proof.
    clear. intros. unfold drest. rewrite <- (app_assoc LBN LE LB).
    eapply Permutation_trans. { do 3 apply Permutation_app_head. apply (Permutation_app_swap_app [(pbin, Bb, nB); (p, A, nA)] LBN (LE ++ LB)). }
    eapply Permutation_trans. { do 2 apply Permutation_app_head. apply (Permutation_app_swap_app TB LBN). }
    eapply Permutation_trans. { apply Permutation_app_head. apply (Permutation_app_swap_app NB LBN). }
    apply (Permutation_app_swap_app Lx LBN).
  Qed.
  Lemma newlib_len : forall M' M'' LEn, mid_step M' M'' -> mid_newlib_ok M' M'' LEn -> mid_ctx M' = mid_ctx M ->
       Z.of_nat (length LEn) + errph_cnt (mid_err M'') <= errph_cnt (mid_err M')
    /\ lb_bytes LEn + errph_bytes (mid_err M'') <= errph_bytes (mid_err M') /\ lb_big LEn + errph_big (mid_err M'') <= errph_big (mid_err M').
  Proof using CTX.
    clear - CTX. intros M' M'' LEn STP2 NEW2 CTX1. destruct NEW2 as (LA & LE2 & PM & CA & CE). rewrite CTX1, CTX in CA. destruct STP2 as (_ & _ & SE2 & _).
    subst LA. cbn [app] in PM.
    destruct (mid_err M') as [|c1] eqn:E1; destruct (mid_err M'') as [|c2] eqn:E2.
    - rewrite CE in PM. apply Permutation_sym in PM. apply Permutation_nil in PM. subst LEn. cbn. clear. lia.
    - cbn [errph_delta] in CE. destruct CE as (Q1 & Q2 & Q3 & _). rewrite (Permutation_length PM), (lb_bytes_perm _ _ PM), (lb_big_perm _ _ PM).
      cbn [errph_cnt errph_bytes errph_big]. unfold ERRINIT_BIG in *. pose proof (lb_big_nonneg LE2) as NN0. clear - Q1 Q2 Q3 NN0. lia.
    - discriminate (SE2 c1 eq_refl).
    - rewrite CE in PM. apply Permutation_sym in PM. apply Permutation_nil in PM. subst LEn. cbn. clear. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma de_phase7 : forall (cur rem elen xp xl : Z) (Lx NB : list block) (S' : storerep) (M' : libmid) (LE : list block) (w0 w1 w3 w5 w6 : word) (j3 : list byte)
           (m' : mem) (mo' : Model) (s' : PState) (ee : Z) (E : entrep) (rows : list (Z * Z * Z)) (nm : list byte) (pS : bptr) (sn : Z) (pn : bptr)
           (rax u0 u1 u2 g0 g1 g2 g3 g4 g5 g6 g7 s6w s8w s9w s11w u3 u4 u5 u6 : word),
      DWK Lx NB S' M' LE w0 w1 w3 (Z_to_bv 64 (cur + 4)) w5 w6 (Z_to_bv 64 (rem - 4)) (Z_to_bv 64 elen) j3 m' mo' s' ->
      ENTRYobj (DREST Lx NB LE) m' ee E -> Permutation (blocks_ENTRY ee E) Lx ->
      en_encoded_o E = None -> en_loadtime E = 0 -> en_forretry E = 0 ->
      1 <= en_nsuites E < 2^31 -> en_suites_o E = Some (pS, sn) -> rw_cells rsegs m' (en_suites E) (suite_cells rows) -> zlength rows = en_nsuites E -> 6 * en_nsuites E <= sn -> Forall row_ok rows ->
      en_pname_o E = Some (pn, zlength nm + 1) -> bytes_at rsegs m' (en_pname E) (nm ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) nm -> 1 <= zlength nm <= 255 ->
      5 * Z.of_nat (length Lx) + 5 <= 2 * (elen + 4) -> lb_bytes Lx + (elen + 4) <= ENTRY_KEPT elen -> lb_big Lx <= elen / 600 ->
      19 <= elen -> 4 + elen <= rem -> Bb + 2 <= cur -> cur + rem <= Bb + zlength bs -> cur < xp + xl <= cur + 4 + elen ->
      DBUD (DREST Lx NB LE) M' (elen + 4) 1 0 ->
      KOKp cur rem NB S' -> KTZp ->
      hs_SR H POSTc (mkCfg (MS (mkR rax (Z_to_bv 64 SPc) gp (Z_to_bv 64 RATP) u0 u1 u2 sp (Z_to_bv 64 A) g0 g1 g2 g3 g4 g5 g6 g7
                                  (Z_to_bv 64 bt) (Z_to_bv 64 Bb) (Z_to_bv 64 xl) (Z_to_bv 64 xp) s6w (Z_to_bv 64 ee) s8w s9w (Z_to_bv 64 cur) s11w u3 u4 u5 u6)
                             F (Z_to_bv 64 DE_J3) fc None m' (seg_rom rsegs)) mo').
  Proof.
    intros until u6. intros DW EO PBL ENo LT0 FRy NSR SUo SC RWL SN6 RWO PNo NMB NONUL NMR LGC LGB LGG E19 ELR BC CR XPR DB KOK KTZ.
    pose proof KOK as KOK'. unfold dK_ok in KOK'.
    pose proof DW as (HP1 & KREL1 & MP1 & LM1 & STP & NEW & CTX1 & EC & EB & EG & LC & LBY & LG & SO1 & SID & SPM & SND & SKI & MBO1 & DSm1 & DSb1 & BT1
                      & FR0 & FR2 & FR3 & FR4 & [errv1 ERR1] & MI1 & ST1 & AUX1 & XA1 & DNB1).
    destruct (de_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ DW) as (HSP & SPE & F3E & BP & BH & IB2 & NBL & NB11 & BLX & HB & F1 & MF & IM & GM & GE).
    destruct (DWK_HF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ DW) as (_ & ND & DISJ & BRS & D2 & D1).
    destruct RCFACTS as (SEQ & SIN & SBR & BEL0 & SUB0 & ND0 & STK0 & LO0 & MF0 & OBJ0 & DJA).
    pose proof (DREST_SUB Lx NB LE) as (SLB & S0 & SLE & SNB & STB & IB & IA & SLX & S3 & SLL).
    hcb. pose proof (word_range sp) as SPR. unfold zlength in *. assert (NB15 : nB < 1500) by (unfold OSSL_ECH_MAX_ECHCONFIG_LEN in NBR; clear - NBR; lia).
    pose proof EO as ((pad1 & pad2 & pad3 & pad4 & L1 & L2 & L3 & L4 & ECc) & EIN' & O1 & O2 & O3 & O4 & XS).
    assert (INLX : forall b, In b (blocks_ENTRY ee E) -> In b Lx) by (intros b Hb; eapply Permutation_in; [exact PBL| exact Hb]).
    assert (ELX : In (en_id E, ee, ENTRY_SIZE) Lx) by (apply INLX; left; reflexivity).
    assert (EIN : In (en_id E, ee, ENTRY_SIZE) (mid_errblocks M' ++ DREST Lx NB LE)) by (apply in_or_app; right; exact EIN').
    pose proof (HB _ EIN) as EEH. pose proof (BRS _ EIN) as (EEP & _ & _ & _ & OFFE). cbn [blk_addr blk_size fst snd] in EEH, EEP, OFFE. unfold ENTRY_SIZE in EEH, OFFE.
    pose proof (BLX _ ELX) as EBA. cbn [blk_addr blk_size fst snd] in EBA. unfold ENTRY_SIZE in EBA.
    destruct DB as (DB1 & DB2 & DB3). pose proof (dec_stack M M' STP) as DSK. pose proof (errph_nonneg (mid_err M')) as (EB0 & EN0 & EG0).
    (* [comment removed for export] *)
    set (ETAIL := blocks_of (en_pname E) (en_pname_o E) ++ blocks_of (en_pub E) (en_pub_o E) ++ blocks_of (en_suites E) (en_suites_o E) ++ blocks_of (en_encoded E) (en_encoded_o E)
                  ++ blocks_EXTS (en_exts E) (en_exts_o E)).
    assert (BE : blocks_ENTRY ee E = (en_id E, ee, ENTRY_SIZE) :: ETAIL) by reflexivity.
    assert (NDE : List.NoDup (map blk_id (blocks_ENTRY ee E))).
    { eapply Permutation_NoDup; [apply Permutation_map; apply Permutation_sym; exact PBL|].
      destruct (nd_app _ _ ND) as [_ N1]. rewrite drest_app, map_app in N1. exact (NoDup_app_remove_r _ _ N1). }
    assert (TNE : forall b, In b ETAIL -> blk_id b <> blk_id (en_id E, ee, ENTRY_SIZE)).
    { intros b Hb K. rewrite BE, map_cons in NDE. apply NoDup_cons_iff in NDE as [NI _]. apply NI. cbn [blk_id fst snd] in K |- *. rewrite <- K. apply in_map. exact Hb. }
    assert (TIN : forall b, In b ETAIL -> In b (mid_errblocks M' ++ DREST Lx NB LE)) by (intros b Hb; apply in_or_app; right; apply SLX; apply INLX; rewrite BE; right; exact Hb).
    assert (TDJ : forall b, In b ETAIL -> blk_addr b + blk_size b <= ee \/ ee + 104 <= blk_addr b).
    { intros b Hb. pose proof (DISJ _ _ (TIN _ Hb) EIN (TNE _ Hb)) as K. cbn [blk_addr blk_size fst snd] in K. unfold ENTRY_SIZE in K. exact K. }
    assert (SUT : In (pS, en_suites E, sn) ETAIL) by (unfold ETAIL; rewrite SUo; apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; left; reflexivity).
    assert (PNT : In (pn, en_pname E, Z.of_nat (length nm) + 1) ETAIL) by (unfold ETAIL; rewrite PNo; left; reflexivity).
    assert (BXT : forall b, In b (blocks_EXTS (en_exts E) (en_exts_o E)) -> In b ETAIL) by (intros b Hb; unfold ETAIL; do 4 (apply in_or_app; right); exact Hb).
    pose proof (HB _ (TIN _ SUT)) as SAH. pose proof (BRS _ (TIN _ SUT)) as (SAP & _ & _ & _ & OFFS). pose proof (TDJ _ SUT) as SEA. cbn [blk_addr blk_size fst snd] in SAH, SAP, OFFS, SEA.
    pose proof (HB _ (TIN _ PNT)) as NAH. pose proof (BRS _ (TIN _ PNT)) as (NAP & _ & _ & _ & OFFN). pose proof (TDJ _ PNT) as NEA. cbn [blk_addr blk_size fst snd] in NAH, NAP, OFFN, NEA.
    pose proof (suite_cells_size rows) as SSZ. unfold zlength in SSZ. rewrite RWL in SSZ.
    (* [comment removed for export] *)
    set (BX := blocks_EXTS (en_exts E) (en_exts_o E)) in *.
    assert (XSW : forall ma mq W, EXTS BX ma (en_exts E) (en_exts_o E) -> munch W ma mq -> wmono rsegs ma mq ->
                   Forall (fun iv : Z * Z => ee <= fst iv /\ snd iv <= ee + 104) W -> EXTS BX mq (en_exts E) (en_exts_o E)).
    { intros ma mq W X0 MU WM FW. eapply (EXTS_keep BX BX SPc ma mq); [exact X0| intros b Hb; exact Hb| | intros b Hb; pose proof (HB _ (TIN _ (BXT _ Hb))) as K; unfold SP'; clear - K CEIL LO STK0; lia].
      eapply xpres_of_munch_gen; [exact MU| exact WM|]. intros a Ha [HC _]. clear MU WM X0. induction W as [|[u v] W IH]; [exact I|]. cbn.
      pose proof (Forall_inv FW) as K. cbn in K. split; [| apply IH; eapply Forall_inv_tail; exact FW].
      destruct HC as [HC|[[HC1 HC2]|(b & Hb & Hr)]]; [unfold SP' in HC; clear - HC K EEH CEIL LO STK0; lia| clear - HC1 K OFFE; lia|].
      pose proof (TDJ _ (BXT _ Hb)) as DJ. clear - DJ K Hr. lia. }
    assert (XS0 : EXTS BX m' (en_exts E) (en_exts_o E)).
    { eapply (EXTS_keep (DREST Lx NB LE) BX SPc m' m'); [exact XS| intros b Hb; exact Hb| apply xpres_refl| intros b Hb; pose proof (HB _ (TIN _ (BXT _ Hb))) as K; unfold SP'; clear - K CEIL LO STK0; lia]. }
    clear XS.
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL1| eapply de_seg11 with (E := E); [exact ECc| exact EEP| unfold ENTRY_SIZE; exact EEH| clear - XPR; lia| clear - BC BP; lia| clear - XPR ELR CR BH; lia| exact HSP| exact MI1]|].
    cbv beta. intros ms1 (m1 & MU1 & WM1 & MI2 & EC1 & ->).
    assert (DW1 : DWK Lx NB S' M' LE w0 w1 w3 (Z_to_bv 64 (cur + 4)) w5 w6 (Z_to_bv 64 (rem - 4)) (Z_to_bv 64 elen) j3 m1 mo' s').
    { eapply (DWK_W Lx NB S' M' LE); [exact DW| exact MU1| exact WM1| exact MI2| | | |].
      - eapply stk_transport_disjoint; [exact ST1| exact MU1| exact WM1| unfold SP'; cbn; clear - EEH CEIL LO STK0; lia].
      - apply Forall_cons; [| apply Forall_nil]. right; right; right; exists (en_id E, ee, ENTRY_SIZE); split; [exact ELX| cbn; unfold ENTRY_SIZE; clear; lia].
      - eapply rw_cells_transport; [exact FR0| exact MU1| exact WM1| unfold SP'; cbn; clear - EEH CEIL LO STK0; lia].
      - eapply rw_cells_transport; [exact FR3| exact MU1| exact WM1| unfold SP', O_F3; cbn; clear - EEH HSP; lia]. }
    pose proof MU1 as MU1'. apply (rw_cells_transport rsegs _ m' m1 _ _ SC) in MU1' as SC1; [| exact WM1| rewrite SSZ; cbn; clear - SEA NSR SN6; lia].
    pose proof MU1 as MU1''. apply (bytes_at_transport rsegs _ m' m1 _ _ NMB) in MU1'' as NMB1; [| rewrite length_app, Nat2Z.inj_add; cbn [length Z.of_nat Pos.of_succ_nat disjoint_from fst snd]; clear - NEA NMR; lia].
    pose proof (XSW _ _ _ XS0 MU1 WM1 ltac:(apply Forall_cons; [cbn; clear; lia| apply Forall_nil])) as XS1.
    clear MU1 WM1 MU1' MU1''.
    (* [comment removed for export] *)
    pose proof DW1 as (HPb & _ & _ & _ & _ & _ & _ & ECb & EBb & EGb & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & DSbb & _ & _ & _ & _ & _ & [errvb ERRb] & MIb & STb & AUXb & _).
    destruct (de_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ DW1) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MFb & IMb & GMb & _).
    destruct (bytes_at_sub m1 Bb bs (cur - Bb) (xp + xl - cur) DSbb ltac:(clear - BC; lia) ltac:(clear - XPR; lia) ltac:(clear - BC CR XPR ELR; lia)) as [BSE ENL].
    replace (Bb + (cur - Bb)) with cur in BSE by lia.
    set (encb := firstn (Z.to_nat (xp + xl - cur)) (skipn (Z.to_nat (cur - Bb)) bs)) in *.
    pose proof (BRS _ IB2) as (_ & _ & _ & _ & OFFB). cbn [blk_addr blk_size fst snd] in OFFB.
    pose proof (cmemdup_spec H HH) as CD. unfold cmemdup_stmt in CD.
    eapply (sr_seq H HH).
    { eapply CD with (lo := lo) (B := B) (LB := mid_errblocks M' ++ DREST Lx NB LE) (s := s') (D := cur) (bs := encb) (v := 1) (errv := errvb); unfold zlength; rewrite ?ENL; try reflexivity.
      all: try first [exact HPb| exact KREL1| exact AUXb| exact CEIL| exact MIb| exact MFb| exact IMb| exact GMb| exact BSE].
      all: lazymatch goal with
           | |- 1 <= _ < _ => clear - XPR E19 ELR CR NBL NB15 BC; lia
           | |- xclient_range _ _ _ _ _ =>
               split; [eapply (rclient_range_block _ _ (pbin, Bb, nB)); [exact IB2| cbn; clear - BC; lia| cbn; clear - BC CR XPR ELR NBL; lia]|];
               unfold memflag_foot, A_mem_inited; apply Forall_cons; [cbn; clear - OFFB BC CR XPR ELR BP NBL; lia| apply Forall_nil]
           | |- lb_bytes _ + _ <= _ => rewrite lb_bytes_app; unfold dbud in *; clear - DB1 EBb EB0 XPR; lia
           | |- Z.of_nat (length _) + _ <= _ => rewrite length_app, Nat2Z.inj_add; unfold dbud in *; clear - DB2 ECb EN0; lia
           | |- lb_big _ + big1 ?n1 <= _ => rewrite lb_big_app; rewrite (big1_small n1) by (unfold BIGB; clear - XPR E19 ELR CR NBL NB15 BC; lia); unfold dbud in *; clear - DB3 EGb EG0; lia
           | |- bv_unsigned _ <= B => unfold SP'; rewrite unsigned_lit by lia; clear - SPB SPR HSP HCEILB; lia
           | |- _ <= _ - CMEMDUP_STACK => unfold SP'; rewrite unsigned_lit by lia; clear - DSK LO; lia
           | |- rw_cells _ _ (errno_addr _) _ => rewrite errno_RATP; exact ERRb
           | |- stk _ _ _ _ => unfold SP'; rewrite unsigned_lit by lia; exact STb
           | |- ?G => idtac "CDPRE" G
           end. }
    clear CD. intros [ms2 mo2] PO. unfold cmemdup_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (z0 & z1 & z2 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & z3 & z4 & z5 & z6 & m2 & errv2 & EA & pv & s2' &
                    -> & KREL2 & MP2 & MI3 & ST2 & ERR2 & AUX2 & XP2 & EBR & HP2 & ECB & MF2 & IM2 & GM2).
    unfold SP' in ST2, XP2. rewrite (unsigned_lit (bv_unsigned sp + -2352)) in ST2, XP2 by lia. fold (SP' sp) in ST2, XP2.
    unfold zlength in EBR, HP2. rewrite ENL in EBR, HP2. pose proof EBR as (EAP & _ & _ & EAH & OFFA).
    assert (XP2' : xpres (DREST [] NB LE) SPc [] m1 m2).
    { intros a Ha [HC _]. destruct (Z.eq_dec a A_mem_inited) as [->|NE]; [apply memflag_same; [exact MFb| exact MF2]|].
      apply XP2; [exact Ha|]. split.
      - destruct HC as [K|[K|(b & Hb & Hr)]]; [left; exact K| right; left; exact K| right; right; exists b; split; [apply in_or_app; right; apply S0; exact Hb| exact Hr]].
      - unfold memflag_foot. cbn [rin_ivs fst snd]. clear - NE. lia. }
    set (Lx3 := @cons block (pv, EA, xp + xl - cur) Lx).
    assert (DW2 : DWK Lx3 NB S' M' LE w0 w1 w3 (Z_to_bv 64 (cur + 4)) w5 w6 (Z_to_bv 64 (rem - 4)) (Z_to_bv 64 elen) j3 m2 mo2 s2').
    { eapply (DWK_X Lx Lx3); [exact DW1| exact XP2'| | exact KREL2| eapply (mpres_trans H HH); [exact MP1| exact MP2]| exists errv2; rewrite <- errno_RATP; exact ERR2| exact MI3| exact ST2| exact AUX2].
      eapply PERM; [exact HP2|]. apply Permutation_middle. }
    assert (AVM : forall a n, (a + n <= 0x10000 \/ 0x311000 <= a) -> Forall (fun iv : Z * Z => a + n <= fst iv \/ snd iv <= a) memflag_foot).
    { intros a n Ha. unfold memflag_foot, A_mem_inited. apply Forall_cons; [cbn; clear - Ha; lia| apply Forall_nil]. }
    eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP2) in EC1; [| eapply (rclient_range_block _ _ (en_id E, ee, ENTRY_SIZE)); [exact EIN| cbn; clear; lia| cbn; unfold ENTRY_SIZE; clear; lia]| apply AVM; cbn; clear - OFFE; lia].
    eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP2) in SC1; [| eapply (rclient_range_block _ _ (pS, en_suites E, sn)); [exact (TIN _ SUT)| cbn; clear; lia| rewrite SSZ; cbn; clear - SN6; lia]| apply AVM; rewrite SSZ; clear - OFFS SN6 NSR; lia].
    eapply (xpres_bytes_at' _ _ _ _ _ _ _ XP2) in NMB1; [| eapply (rclient_range_block _ _ (pn, en_pname E, Z.of_nat (length nm) + 1)); [exact (TIN _ PNT)| cbn; clear; lia| rewrite length_app, Nat2Z.inj_add; cbn; clear; lia]
                                                     | apply AVM; rewrite length_app, Nat2Z.inj_add; cbn [length Z.of_nat Pos.of_succ_nat]; clear - OFFN; lia].
    assert (XS2 : EXTS BX m2 (en_exts E) (en_exts_o E)).
    { eapply (EXTS_keep BX BX SPc m1 m2); [exact XS1| intros b Hb; exact Hb| | intros b Hb; pose proof (HB _ (TIN _ (BXT _ Hb))) as K; unfold SP'; clear - K CEIL LO STK0; lia].
      intros a Ha [HC _]. destruct (Z.eq_dec a A_mem_inited) as [->|NE]; [apply memflag_same; [exact MFb| exact MF2]|].
      apply XP2; [exact Ha|]. split.
      - destruct HC as [K|[K|(b & Hb & Hr)]]; [left; exact K| right; left; exact K| right; right; exists b; split; [exact (TIN _ (BXT _ Hb))| exact Hr]].
      - unfold memflag_foot. cbn [rin_ivs fst snd]. clear - NE. lia. }
    (* [comment removed for export] *)
    pose proof DW2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FR0c & _ & FR3c & _ & _ & MIc & STc & _).
    rewrite SPE in FR0c. unfold dframe in FR0c.
    eapply (sr_evt_krel H HH); [exact KREL2| eapply de_seg12 with (E := upd_enclen E (xp + xl - cur)) (o := Some (pv, xp + xl - cur));
      [exact FR0c| exact EC1| exact EEP| unfold ENTRY_SIZE; exact EEH| clear - EAP EAH HCEILB XPR; lia| exact HSP| exact MIc]|].
    cbv beta. intros ms3 (a0' & m3 & MU3 & WM3 & MI4 & EC3 & [[Z0 _]|[_ ->]]); [exfalso; clear - Z0 EAP; lia|].
    assert (DW3 : DWK Lx3 NB S' M' LE w0 w1 w3 (Z_to_bv 64 (cur + 4)) w5 w6 (Z_to_bv 64 (rem - 4)) (Z_to_bv 64 elen) j3 m3 mo2 s2').
    { eapply (DWK_W Lx3 NB S' M' LE); [exact DW2| exact MU3| exact WM3| exact MI4| | | |].
      - eapply stk_transport_disjoint; [exact STc| exact MU3| exact WM3| unfold SP'; cbn; clear - EEH CEIL LO STK0; lia].
      - apply Forall_cons; [| apply Forall_nil]. right; right; right; exists (en_id E, ee, ENTRY_SIZE); split; [right; exact ELX| cbn; unfold ENTRY_SIZE; clear; lia].
      - rewrite SPE. unfold dframe. eapply rw_cells_transport; [exact FR0c| exact MU3| exact WM3| cbn; clear - EEH CEIL LO STK0; lia].
      - eapply rw_cells_transport; [exact FR3c| exact MU3| exact WM3| unfold SP', O_F3; cbn; clear - EEH HSP; lia]. }
    pose proof MU3 as MU3'. apply (rw_cells_transport rsegs _ m2 m3 _ _ SC1) in MU3' as SC3; [| exact WM3| rewrite SSZ; cbn; clear - SEA NSR SN6; lia].
    pose proof MU3 as MU3''. apply (bytes_at_transport rsegs _ m2 m3 _ _ NMB1) in MU3'' as NMB3; [| rewrite length_app, Nat2Z.inj_add; cbn [length Z.of_nat Pos.of_succ_nat disjoint_from fst snd]; clear - NEA NMR; lia].
    pose proof (XSW _ _ _ XS2 MU3 WM3 ltac:(apply Forall_cons; [cbn; clear; lia| apply Forall_nil])) as XS3.
    set (E3 := upd_encoded (upd_enclen E (xp + xl - cur)) EA (Some (pv, xp + xl - cur))) in EC3.
    (* [comment removed for export] *)
    eapply (KOK' Lx3 M' LE w0 w1 w3 w5 w6 j3 m3 mo2 s2' ee elen E3 rows pS sn pn nm);
      [exact DW3| exact E19| exact ELR| | | | | | | | unfold zlength; rewrite RWL| exact SN6 || idtac| exact RWO| | | exact NONUL| unfold zlength; exact NMR| | | ].
    all: try (subst E3; cbn [en_id en_pname en_pname_o en_pub en_pub_o en_suites en_suites_o en_nsuites en_encoded en_encoded_o en_exts en_exts_o en_loadtime en_forretry en_enclen upd_enclen upd_encoded];
              unfold zlength; first [reflexivity| assumption]).
    - (* [comment removed for export] *)
      unfold ENTRYobj. subst E3. cbn [en_id en_pname en_pname_o en_pub en_pub_o en_suites en_suites_o en_encoded en_encoded_o en_exts en_exts_o upd_enclen upd_encoded].
      split; [exists pad1, pad2, pad3, pad4; split; [exact L1|]; split; [exact L2|]; split; [exact L3|]; split; [exact L4| exact EC3]|].
      split; [right; exact EIN'|]. split; [eapply ofield_LB_mono; [exact O1| intros b Hb; right; exact Hb]|]. split; [eapply ofield_LB_mono; [exact O2| intros b Hb; right; exact Hb]|].
      split; [eapply ofield_LB_mono; [exact O3| intros b Hb; right; exact Hb]|]. split; [cbn [ofield]; split; [exact EAP|]; split; [clear - XPR; lia| left; reflexivity]|].
      eapply (EXTS_keep BX (DREST Lx3 NB LE) SPc m3 m3); [exact XS3| intros b Hb; right; apply SLX; apply INLX; rewrite BE; right; apply BXT; exact Hb| apply xpres_refl
        | intros b Hb; pose proof (HB _ (TIN _ (BXT _ Hb))) as K; unfold SP'; clear - K CEIL LO STK0; lia].
    - (* [comment removed for export] *)
      subst E3 Lx3. unfold blocks_ENTRY in PBL |- *. rewrite ENo in PBL.
      cbn [en_id en_pname en_pname_o en_pub en_pub_o en_suites en_suites_o en_encoded en_encoded_o en_exts en_exts_o upd_enclen upd_encoded blocks_of app] in PBL |- *.
      eapply Permutation_trans; [| apply perm_skip; exact PBL].
      rewrite !app_assoc. change (?a :: ?l ++ (pv, EA, xp + xl - cur) :: ?r) with ((a :: l) ++ (pv, EA, xp + xl - cur) :: r).
      eapply Permutation_trans; [apply Permutation_sym; apply Permutation_middle|]. cbn [app]. rewrite <- !app_assoc. apply Permutation_refl.
    - (* [comment removed for export] *)
      subst Lx3. cbn [length]. rewrite Nat2Z.inj_succ. clear - LGC. lia.
    - subst Lx3. change (lb_bytes ((pv, EA, xp + xl - cur) :: Lx)) with (xp + xl - cur + lb_bytes Lx). clear - LGB XPR. lia.
    - subst Lx3. change (lb_big ((pv, EA, xp + xl - cur) :: Lx)) with (big1 (xp + xl - cur) + lb_big Lx). rewrite (big1_small (xp + xl - cur)) by (unfold BIGB; clear - XPR E19 ELR CR NBL NB15 BC; lia). clear - LGG. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma de_phase6 : forall (cur rem elen publen so ns nl : Z) (Lx NB : list block) (S' : storerep) (M' : libmid) (LE : list block) (w0 w1 w3 w5 w6 v0 v1 v2 v6 v7 v8 v9 v10 : word)
           (m' : mem) (mo' : Model) (s' : PState) (ee SA : Z) (pS : bptr) (E : entrep) (rows : list (Z * Z * Z)) (nm : list byte)
           (u0 u1 u2 g2 g3 g4 g5 g6 g7 s5w s6w u3 u4 u5 u6 : word),
      let np := cur + 9 + publen + 2 + so + 2 in
      DWK Lx NB S' M' LE w0 w1 w3 (Z_to_bv 64 (cur + 4)) w5 w6 (Z_to_bv 64 (rem - 4)) (Z_to_bv 64 elen)
          (cells_bytes (F3W v0 v1 v2 (Z_to_bv 64 np) (Z_to_bv 64 Bb) (Z_to_bv 64 nl) v6 v7 v8 v9 v10)) m' mo' s' ->
      ENTRYobj (DREST Lx NB LE) m' ee E -> Permutation (blocks_ENTRY ee E) Lx ->
      en_suites_o E = Some (pS, 6 * ns) -> en_suites E = SA -> en_nsuites E = ns -> en_pname_o E = None -> en_encoded_o E = None -> en_exts E = 0 -> en_exts_o E = None ->
      en_loadtime E = 0 -> en_forretry E = 0 ->
      rw_cells rsegs m' SA (suite_cells rows) -> zlength rows = ns -> Forall row_ok rows -> 1 <= ns -> 4 * ns <= so ->
      nm = firstn (Z.to_nat nl) (skipn (Z.to_nat (np - Bb)) bs) -> zlength nm = nl -> ~ In (Z_to_bv 8 0) nm -> 4 <= nl < 256 ->
      lb_bytes Lx <= ENTRY_SIZE + publen + 6 * ns -> Z.of_nat (length Lx) <= 3 -> lb_big Lx = big1 (6 * ns) ->
      Bb + 2 <= cur -> 0 <= publen -> 2 <= so -> 5 + publen + 2 + so + 2 + nl <= elen -> 4 + elen <= rem -> cur + rem <= Bb + zlength bs ->
      DBUD (DREST [] NB LE) M' (ENTRY_BYTES rem) (ENTRY_CNT rem) (ENTRY_BIG rem) ->
      KOKp cur rem NB S' -> KTAp -> KTZp ->
      hs_SR H POSTc (mkCfg (MS (mkR (Z_to_bv 64 DE_R6) (Z_to_bv 64 SPc) gp (Z_to_bv 64 RATP) u0 u1 u2 sp (Z_to_bv 64 A) (Z_to_bv 64 (bv_unsigned sp + -168)) (Z_to_bv 64 (ee + 8)) g2 g3 g4 g5 g6 g7
                                  (Z_to_bv 64 bt) (Z_to_bv 64 Bb) (Z_to_bv 64 (elen - 5 - publen - 2 - so - 2)) s5w s6w (Z_to_bv 64 ee) (Z_to_bv 64 np) (Z_to_bv 64 nl) (Z_to_bv 64 cur) (Z_to_bv 64 431) u3 u4 u5 u6)
                             F (Z_to_bv 64 P_PACKET_strndup) fc None m' (seg_rom rsegs)) mo').
  Proof.
    intros until u6. cbv zeta. intros DW EO PBL SUo SUE NSE PNo ENo EX0 EXo LT0 FRy SC RWL RWO NS1 SO4 NMD NML NONUL NLR LB1 LBN LB3 BC PL0 S2 ES ELR CR DB0 KOK KTA KTZ.
    pose proof KTA as KTA'. unfold dK_tailA in KTA'.
    pose proof DW as (HP1 & KREL1 & MP1 & LM1 & STP & NEW & CTX1 & EC & EB & EG & LC & LBY & LG & SO1 & SID & SPM & SND & SKI & MBO1 & DSm1 & DSb1 & BT1
                      & FR0 & FR2 & FR3 & FR4 & [errv1 ERR1] & MI1 & ST1 & AUX1 & XA1 & DNB1).
    destruct (de_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ DW) as (HSP & SPE & F3E & BP & BH & IB2 & NBL & NB11 & BLX & HB & F1 & MF & IM & GM & GE).
    destruct (DWK_HF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ DW) as (_ & ND & DISJ & BRS & D2 & D1).
    destruct RCFACTS as (SEQ & SIN & SBR & BEL0 & SUB0 & ND0 & STK0 & LO0 & MF0 & OBJ0 & DJA).
    pose proof (DREST_SUB Lx NB LE) as (SLB & S0 & SLE & SNB & STB & IB & IA & SLX & S3 & SLL).
    hcb. pose proof (word_range sp) as SPR. unfold zlength in *. assert (NB15 : nB < 1500) by (unfold OSSL_ECH_MAX_ECHCONFIG_LEN in NBR; clear - NBR; lia).
    pose proof EO as ((pad1 & pad2 & pad3 & pad4 & L1 & L2 & L3 & L4 & ECc) & EIN' & O1 & O2 & O3 & O4 & XS).
    assert (ELX : In (en_id E, ee, ENTRY_SIZE) Lx) by (eapply Permutation_in; [exact PBL| left; reflexivity]).
    assert (SLXi : In (pS, SA, 6 * ns) Lx).
    { eapply Permutation_in; [exact PBL|]. unfold blocks_ENTRY. rewrite SUo, SUE. right. apply in_or_app; right. apply in_or_app; right. apply in_or_app; left. left. reflexivity. }
    assert (EIN : In (en_id E, ee, ENTRY_SIZE) (mid_errblocks M' ++ DREST Lx NB LE)) by (apply in_or_app; right; exact EIN').
    assert (SIN' : In (pS, SA, 6 * ns) (mid_errblocks M' ++ DREST Lx NB LE)) by (apply in_or_app; right; apply SLX; exact SLXi).
    pose proof (HB _ EIN) as EEH. pose proof (BRS _ EIN) as (EEP & _ & _ & _ & OFFE). cbn [blk_addr blk_size fst snd] in EEH, EEP, OFFE. unfold ENTRY_SIZE in EEH, OFFE.
    pose proof (BLX _ ELX) as EBA. cbn [blk_addr blk_size fst snd] in EBA. unfold ENTRY_SIZE in EBA.
    pose proof (HB _ SIN') as SAH. pose proof (BRS _ SIN') as (SAP & _ & _ & _ & OFFS). cbn [blk_addr blk_size fst snd] in SAH, SAP, OFFS.
    assert (NES : en_id E <> pS).
    { intros EQ. pose proof (nodup_id_inj _ (en_id E, ee, ENTRY_SIZE) (pS, SA, 6 * ns) ND EIN SIN' EQ) as K. injection K as E1q E2q E3q. unfold ENTRY_SIZE in E3q. clear - E3q. lia. }
    pose proof (DISJ _ _ SIN' EIN ltac:(cbn [blk_id fst snd]; intros K; exact (NES (eq_sym K)))) as SEA. cbn [blk_addr blk_size fst snd] in SEA. unfold ENTRY_SIZE in SEA.
    pose proof (suite_cells_size rows) as SSZ. unfold zlength in SSZ. rewrite RWL in SSZ.
    destruct DB0 as (DB1 & DB2 & DB3). pose proof (dec_stack M M' STP) as DSK. pose proof (errph_nonneg (mid_err M')) as (EB0 & EN0 & EG0).
    assert (B1 : big1 (6 * ns) <= 1) by (unfold big1; destruct (BIGB <? 6 * ns); clear; lia).
    (* [comment removed for export] *)
    destruct (entry_split_pname _ _ _ _ _ _ _ ECc) as (EP0 & EL & ES16). rewrite PNo in O1. cbn [ofield] in O1. rewrite O1 in EL.
    rewrite F3E in FR3. pose proof (F3_uncb _ _ _ _ _ _ _ _ _ _ _ _ _ FR3) as F3w. destruct (F3_split3 _ _ _ _ _ _ _ _ _ _ _ _ _ F3w) as [F3a F3r].
    pose proof F3r as F3m. change ([C8 (Z_to_bv 64 (cur + 9 + publen + 2 + so + 2)); C8 (Z_to_bv 64 Bb); C8 (Z_to_bv 64 nl); C8 v6; C8 v7; C8 v8; C8 v9; C8 v10])
      with ([C8 (Z_to_bv 64 (cur + 9 + publen + 2 + so + 2)); C8 (Z_to_bv 64 Bb); C8 (Z_to_bv 64 nl)] ++ [C8 v6; C8 v7; C8 v8; C8 v9; C8 v10]) in F3m.
    apply rw_cells_app in F3m as [F3m _].
    destruct (bytes_at_sub m' Bb bs (cur + 9 + publen + 2 + so + 2 - Bb) nl DSb1 ltac:(clear - BC PL0 S2; lia) ltac:(clear - NLR; lia) ltac:(clear - BC CR ES ELR; lia)) as [BSN _].
    rewrite <- NMD in BSN. replace (Bb + (cur + 9 + publen + 2 + so + 2 - Bb)) with (cur + 9 + publen + 2 + so + 2) in BSN by lia.
    (* [comment removed for export] *)
    pose proof (pkstrndup_spec H HH) as PS. unfold pkstrndup_stmt in PS.
    eapply (sr_seq H HH).
    { eapply PS with (lo := lo) (B := B) (LB := mid_errblocks M' ++ DREST Lx NB LE) (s := s') (pkt := bv_unsigned sp + -168) (cur := cur + 9 + publen + 2 + so + 2) (ms := Bb)
                       (dptr := ee + 8) (v := 1) (bs := nm) (errv := errv1); unfold zlength; rewrite ?NML; try reflexivity.
      all: try first [exact HP1| exact KREL1| exact AUX1| exact CEIL| exact MI1| exact MF| exact IM| exact GM| exact BSN| exact EL].
      all: lazymatch goal with
           | |- rw_cells _ _ (bv_unsigned sp + -168) _ => unfold pk_cells; replace (bv_unsigned sp + -168) with (bv_unsigned sp + -192 + 24) by lia; exact F3m
           | |- bv_unsigned _ <= bv_unsigned sp + -168 => unfold SP'; rewrite unsigned_lit by lia; clear; lia
           | |- 0 < _ < _ => clear - BC BP BH HCEILB PL0 S2 CR ES ELR NLR; lia
           | |- outcell_ok _ _ _ _ => unfold SP'; rewrite unsigned_lit by lia;
                                      split; [eapply (rclient_range_block _ _ (en_id E, ee, ENTRY_SIZE)); [exact EIN| cbn; clear; lia| cbn; unfold ENTRY_SIZE; clear; lia]|];
                                      split; [unfold off_image, IMG_LO, IMG_HI; clear - OFFE; lia| clear - EEH HSP SPB; lia]
           | |- apart (bv_unsigned sp + -168) _ _ _ => unfold apart; clear - EEH HSP; lia
           | |- apart _ _ _ _ => unfold apart; clear - EBA BC CR ES ELR PL0 S2; lia
           | |- xclient_range _ _ _ _ _ =>
               split; [eapply (rclient_range_block _ _ (pbin, Bb, nB)); [exact IB2| cbn; clear - BC PL0 S2; lia| cbn; clear - BC CR ES ELR NBL; lia]|];
               unfold memflag_foot, A_mem_inited; apply Forall_cons; [cbn; pose proof (BRS _ IB2) as (_ & _ & _ & _ & OFFB); cbn [blk_addr blk_size fst snd] in OFFB; clear - OFFB BC CR ES ELR BP NBL PL0 S2; lia| apply Forall_nil]
           | |- _ < 2 ^ 31 => clear - NLR; lia
           | |- lb_bytes _ + _ <= _ => rewrite lb_bytes_app, drest_app, lb_bytes_app; unfold dbud, ENTRY_BYTES, ENTRY_SIZE in *; clear - DB1 EB EB0 ES ELR PL0 S2 SO4 LB1 NLR; lia
           | |- Z.of_nat (length _) + _ <= _ => rewrite length_app, drest_app, length_app, !Nat2Z.inj_add; unfold dbud, ENTRY_CNT in *;
                                                 pose proof (Z.div_pos (2 * rem) 5 ltac:(clear - ELR ES PL0 S2 NLR; lia) ltac:(lia)) as DP; clear - DB2 EC DP EN0 LBN; lia
           | |- lb_big _ + big1 ?n1 <= _ => rewrite lb_big_app, drest_app, lb_big_app; rewrite (big1_small n1) by (unfold BIGB; clear - NLR; lia); unfold dbud, ENTRY_BIG in *;
                                           pose proof (Z.div_pos rem 1024 ltac:(clear - ELR ES PL0 S2 NLR; lia) ltac:(lia)) as DP; clear - DB3 EG DP EG0 LB3 B1; lia
           | |- bv_unsigned _ <= B => unfold SP'; rewrite unsigned_lit by lia; clear - SPB SPR HSP HCEILB; lia
           | |- _ <= _ - PKSTRNDUP_STACK => unfold SP'; rewrite unsigned_lit by lia; clear - DSK LO; lia
           | |- rw_cells _ _ (errno_addr _) _ => rewrite errno_RATP; exact ERR1
           | |- stk _ _ _ _ => unfold SP'; rewrite unsigned_lit by lia; exact ST1
           | |- ?G => idtac "PSPRE" G
           end. }
    clear PS. intros [ms2 mo2] PO. unfold pkstrndup_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (z0 & z1 & z2 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & z3 & z4 & z5 & z6 & m2 & errv2 & s2' & D & pN &
                    -> & KREL2 & MP2 & MI3 & ST2 & ERR2 & AUX2 & NBR2 & HP2 & NC2 & PK2 & DP2 & XP2 & MF2 & IM2 & GM2).
    unfold SP' in ST2, XP2. rewrite (unsigned_lit (bv_unsigned sp + -2352)) in ST2, XP2 by lia. fold (SP' sp) in ST2, XP2.
    rewrite (strnlen_full' nm NONUL) in NBR2, HP2, NC2. rewrite firstn_all in NC2. unfold zlength in NML. rewrite NML in NBR2, HP2.
    pose proof (strndup_bytes _ _ _ NC2) as NMB2. pose proof NBR2 as (DPOS & _ & _ & DH & OFFD).
    assert (XP2' : xpres (DREST [] NB LE) SPc [] m' m2).
    { intros a Ha [HC _]. destruct (Z.eq_dec a A_mem_inited) as [->|NE]; [apply memflag_same; [exact MF| exact MF2]|].
      apply XP2; [exact Ha|]. split.
      - destruct HC as [K|[K|(b & Hb & Hr)]]; [left; exact K| right; left; exact K| right; right; exists b; split; [apply in_or_app; right; apply S0; exact Hb| exact Hr]].
      - intros [K|K].
        + cbn [fst snd] in K. eapply (lx_not_client Lx NB LE M' s' m' (en_id E, ee, ENTRY_SIZE) a []); [exact HP1| exact ELX| cbn; unfold ENTRY_SIZE; clear - K; lia| split; [exact HC| intros []]].
        + unfold memflag_foot in K. cbn [rin_ivs fst snd] in K. clear - K NE. lia. }
    set (E2 := upd_pname E D (Some (pN, nl + 1))). set (Lx2 := @cons block (pN, D, nl + 1) Lx).
    assert (DW2 : DWK Lx2 NB S' M' LE w0 w1 w3 (Z_to_bv 64 (cur + 4)) w5 w6 (Z_to_bv 64 (rem - 4)) (Z_to_bv 64 elen)
                      (cells_bytes (F3W v0 v1 v2 (Z_to_bv 64 (cur + 9 + publen + 2 + so + 2)) (Z_to_bv 64 Bb) (Z_to_bv 64 nl) v6 v7 v8 v9 v10)) m2 mo2 s2').
    { eapply (DWK_X Lx Lx2); [exact DW| exact XP2'| | exact KREL2| eapply (mpres_trans H HH); [exact MP1| exact MP2]| exists errv2; rewrite <- errno_RATP; exact ERR2| exact MI3| exact ST2| exact AUX2].
      eapply PERM; [exact HP2|]. apply Permutation_middle. }
    (* [comment removed for export] *)
    assert (AVE : forall a n, ee <= a -> a + n <= ee + 104 -> (a + n <= ee + 8 \/ ee + 16 <= a) -> Forall (fun iv : Z * Z => a + n <= fst iv \/ snd iv <= a) ((ee + 8, ee + 8 + 8) :: memflag_foot)).
    { intros a n H1 H2 H3. unfold memflag_foot, A_mem_inited. apply Forall_cons; [cbn; clear - H3; lia|]. apply Forall_cons; [cbn; clear - H1 H2 OFFE; lia| apply Forall_nil]. }
    eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP2) in EP0; [| eapply (rclient_range_block _ _ (en_id E, ee, ENTRY_SIZE)); [exact EIN| cbn; clear; lia| cbn; unfold ENTRY_SIZE; clear; lia]| apply AVE; cbn; clear; lia].
    eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP2) in ES16; [| eapply (rclient_range_block _ _ (en_id E, ee, ENTRY_SIZE)); [exact EIN| cbn; clear; lia| cbn; unfold ENTRY_SIZE; clear; lia]| apply AVE; cbn; clear; lia].
    pose proof (entry_join_pname _ _ _ _ _ _ _ _ (Some (pN, nl + 1)) EP0 DP2 ES16) as EC2. fold E2 in EC2.
    eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP2) in SC; [| eapply (rclient_range_block _ _ (pS, SA, 6 * ns)); [exact SIN'| cbn; clear; lia| rewrite SSZ; cbn; clear; lia]
      | rewrite SSZ; unfold memflag_foot, A_mem_inited; apply Forall_cons; [cbn; clear - SEA NS1; lia| apply Forall_cons; [cbn; clear - OFFS NS1; lia| apply Forall_nil]]].
    eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP2) in F3w; [| left; unfold SP'; cbn; clear; lia| unfold memflag_foot, A_mem_inited; apply Forall_cons; [cbn; clear - EEH HSP; lia| apply Forall_cons; [cbn; clear - HSP HCEILB; unfold IMG_HI in *; lia| apply Forall_nil]]].
    rename F3w into F3w2.
    (* [comment removed for export] *)
    assert (EOK2 : forall mm, rw_cells rsegs mm ee (entry_cells E2 pad1 pad2 pad3 pad4) -> ENTRYobj (DREST Lx2 NB LE) mm ee E2).
    { intros mm ECm. unfold ENTRYobj. subst E2. cbn [en_id en_pname en_pname_o en_pub en_pub_o en_suites en_suites_o en_encoded en_encoded_o en_exts en_exts_o upd_pname].
      split; [exists pad1, pad2, pad3, pad4; split; [exact L1|]; split; [exact L2|]; split; [exact L3|]; split; [exact L4| exact ECm]|].
      split; [right; exact EIN'|]. split; [cbn [ofield]; split; [exact DPOS|]; split; [clear - NLR; lia| left; reflexivity]|].
      split; [eapply ofield_LB_mono; [exact O2| intros b Hb; right; exact Hb]|]. split; [eapply ofield_LB_mono; [exact O3| intros b Hb; right; exact Hb]|].
      split; [eapply ofield_LB_mono; [exact O4| intros b Hb; right; exact Hb]|]. rewrite EXo in XS |- *. exact XS. }
    assert (PBL2 : Permutation (blocks_ENTRY ee E2) Lx2).
    { unfold blocks_ENTRY in PBL |- *. subst E2 Lx2. rewrite PNo in PBL.
      cbn [en_id en_pname en_pname_o en_pub en_pub_o en_suites en_suites_o en_encoded en_encoded_o en_exts en_exts_o upd_pname blocks_of app] in PBL |- *.
      eapply Permutation_trans; [apply perm_swap|]. apply perm_skip. exact PBL. }
    assert (ELX2 : In (en_id E, ee, ENTRY_SIZE) Lx2) by (right; exact ELX). assert (SLX2 : In (pS, SA, 6 * ns) Lx2) by (right; exact SLXi). assert (NLX2 : In (pN, D, nl + 1) Lx2) by (left; reflexivity).
    assert (LB1' : lb_bytes Lx2 <= ENTRY_SIZE + publen + 6 * ns + nl + 1) by (subst Lx2; change (lb_bytes ((pN, D, nl + 1) :: Lx)) with (nl + 1 + lb_bytes Lx); clear - LB1; lia).
    assert (LBN' : Z.of_nat (length Lx2) <= 4) by (subst Lx2; cbn [length]; rewrite Nat2Z.inj_succ; clear - LBN; lia).
    assert (LB3' : lb_big Lx2 = big1 (6 * ns)) by (subst Lx2; change (lb_big ((pN, D, nl + 1) :: Lx)) with (big1 (nl + 1) + lb_big Lx); rewrite (big1_small (nl + 1)) by (unfold BIGB; clear - NLR; lia); clear - LB3; lia).
    assert (TAILB2 : DBUD (DREST Lx2 NB LE) M' ERRDEBUG_BYTES 2 0).
    { unfold dbud. rewrite drest_app, lb_bytes_app, length_app, lb_big_app, Nat2Z.inj_add. unfold dbud, ENTRY_BYTES, ENTRY_CNT, ENTRY_BIG, ENTRY_SIZE, ERRDEBUG_BYTES in *.
      pose proof (Z.div_pos (2 * rem) 5 ltac:(clear - ELR ES PL0 S2 NLR; lia) ltac:(lia)) as DQ1. pose proof (Z.div_pos rem 1024 ltac:(clear - ELR ES PL0 S2 NLR; lia) ltac:(lia)) as DQ2.
      clear - DB1 DB2 DB3 DQ1 DQ2 ELR ES PL0 S2 SO4 NLR LB1' LBN' LB3' B1. lia. }
    (* [comment removed for export] *)
    pose proof DW2 as (HPc & _ & _ & LMc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & DSbc & _ & FR0c & _ & FR3c & _ & _ & MIc & STc & _).
    eapply (sr_evt_krel H HH); [exact KREL2| eapply de_seg9 with (np := cur + 9 + publen + 2 + so + 2) (nl := nl) (left := elen - 5 - publen - 2 - so - 2) (cur := cur);
      [exact F3w2| exact DSbc| clear - BC PL0 S2; lia| clear - NLR; lia| clear - ES; lia| unfold zlength; clear - BC CR ES ELR; lia| exact BP| exact BH| clear - ES ELR CR NBL NB15 BC PL0 S2 NLR; lia
      | exact EEP| unfold ENTRY_SIZE; exact EEH| exact HSP| exact MIc]|].
    cbv beta. intros ms3 (a0' & a1' & a2' & s4' & s5' & m3 & f0 & f1 & f2 & MU3 & WM3 & MI4 & F3w3 & CASES).
    assert (DW3 : DWK Lx2 NB S' M' LE w0 w1 w3 (Z_to_bv 64 (cur + 4)) w5 w6 (Z_to_bv 64 (rem - 4)) (Z_to_bv 64 elen)
                      (cells_bytes (F3W f0 f1 f2 (Z_to_bv 64 (cur + 9 + publen + 2 + so + 2)) (Z_to_bv 64 Bb) (Z_to_bv 64 nl) v6 v7 v8 v9 v10)) m3 mo2 s2').
    { eapply (DWK_W Lx2 NB S' M' LE); [exact DW2| exact MU3| exact WM3| exact MI4| | | |].
      - eapply stk_transport_disjoint; [exact STc| exact MU3| exact WM3| unfold SP'; cbn; clear; lia].
      - apply Forall_cons; [| apply Forall_nil]. right; right; left. unfold SP', O_F3, O_SAVES. cbn. clear; lia.
      - eapply rw_cells_transport; [exact FR0c| exact MU3| exact WM3| unfold SP'; cbn; clear; lia].
      - rewrite F3E. apply F3_cb. exact F3w3. }
    apply (rw_cells_transport rsegs _ m2 m3 _ _ EC2) in MU3 as EC3; [| exact WM3| cbn; clear - EEH HSP; lia].
    pose proof MU3 as MU3'. apply (rw_cells_transport rsegs _ m2 m3 _ _ SC) in MU3' as SC3; [| exact WM3| rewrite SSZ; cbn; clear - SAH HSP NS1; lia].
    apply (bytes_at_transport rsegs _ m2 m3 _ _ NMB2) in MU3 as NMB3; [| rewrite length_app, Nat2Z.inj_add, NML; cbn [length Z.of_nat Pos.of_succ_nat disjoint_from fst snd]; clear - DH HSP NLR; lia].
    clear WM3 MU3'.
    assert (NSR : ns < 2 ^ 16) by (clear - SO4 ES ELR CR NBL NB15 BC PL0 NLR; lia).
    destruct CASES as [->|(xl & XL0 & XLB & -> & -> & -> & REST)].
    { (* [comment removed for export] *)
      eapply KTA' with (E := E2); [exact DW3| exact (EOK2 _ EC3)| exact PBL2| clear; lia| exact TAILB2]. }
    assert (E19 : 19 <= elen) by (clear - ES XLB XL0 SO4 NS1 NLR PL0; lia).
    destruct REST as [[X0 ->]|[X1 ->]].
    - (* [comment removed for export] *)
      eapply (de_phase7 cur rem elen (cur + 9 + publen + 2 + so + 2 + nl + 2) xl Lx2 NB S' M' LE) with (E := E2) (rows := rows) (nm := nm) (pS := pS) (sn := 6 * ns) (pn := pN);
        [exact DW3| exact (EOK2 _ EC3)| exact PBL2| | exact LT0 || (subst E2; exact LT0)| | | | | unfold zlength; rewrite RWL| | exact RWO| | | exact NONUL| unfold zlength; rewrite NML; clear - NLR; lia
        | clear - LBN' E19; lia| unfold ENTRY_KEPT, ENTRY_SIZE in *; clear - LB1' ES XLB XL0 SO4 NS1 NLR PL0; lia| | exact E19| exact ELR| exact BC| unfold zlength; exact CR| clear - XL0 XLB ES PL0 S2 NLR; lia
        | | exact KOK| exact KTZ].
      all: try (subst E2; cbn [en_id en_pname en_pname_o en_pub en_pub_o en_suites en_suites_o en_nsuites en_encoded en_encoded_o en_exts en_exts_o en_loadtime en_forretry upd_pname];
                unfold zlength; rewrite ?NSE, ?SUE, ?NML; first [reflexivity| assumption| clear - NS1 NSR; lia]).
      + rewrite LB3'. unfold big1. destruct (BIGB <? 6 * ns) eqn:BB; [| apply Z.div_pos; clear - E19; lia]. apply Z.ltb_lt in BB. unfold BIGB in BB.
        apply Z.div_le_lower_bound; [lia|]. clear - BB SO4 ES XLB XL0 NLR PL0. lia.
      + unfold dbud. rewrite drest_app, lb_bytes_app, length_app, lb_big_app, Nat2Z.inj_add. unfold dbud, ENTRY_BYTES, ENTRY_CNT, ENTRY_BIG, ENTRY_SIZE in *.
        pose proof (Z.div_pos (2 * rem) 5 ltac:(clear - ELR E19; lia) ltac:(lia)) as DQ1. pose proof (Z.div_pos rem 1024 ltac:(clear - ELR E19; lia) ltac:(lia)) as DQ2.
        clear - DB1 DB2 DB3 DQ1 DQ2 ELR ES PL0 S2 SO4 NLR LB1' LBN' LB3' B1. lia.
    - (* [comment removed for export] *)
      pose proof DW3 as (HPd & _ & _ & LMd & _ & _ & _ & ECd & EBd & EGd & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & DSbd & _ & FR0d & _ & FR3d & _ & [errvd ERRd] & MId & STd & AUXd & _).
      destruct (DWK_HF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ DW3) as (HB3 & ND3 & DISJ3 & BRS3 & D23 & D13).
      pose proof (DREST_SUB Lx2 NB LE) as (SLB2 & S02 & SLE2 & SNB2 & STB2 & IBq & IAq & SLXq & S32 & SLL2).
      destruct (F3_split3 _ _ _ _ _ _ _ _ _ _ _ _ _ F3w3) as [PKX F3r3].
      pose proof (decexts_spec H HX EGS) as DX. unfold decexts_stmt in DX.
      eapply (sr_seq H HH).
      { eapply DX with (lo := lo) (B := B) (LIB := LE ++ LIB) (LB := DREST Lx2 NB LE) (M := M') (x := x) (ee := ee) (pk := bv_unsigned sp + -192) (base := Bb) (len := nB)
                         (cur := cur + 9 + publen + 2 + so + 2 + nl + 2) (rem := xl) (E := E2) (bs := bs) (pbin := pbin) (errv := errvd); try reflexivity.
        all: try first [exact (EOK2 _ EC3)| exact HPd| exact KREL2| exact AUXd| exact CEIL| exact MId| exact DSbd| exact LMd| exact SLL2| exact BHI| exact IBq].
        all: lazymatch goal with
             | |- en_exts _ = 0 => subst E2; cbn [en_exts upd_pname]; exact EX0
             | |- en_exts_o _ = None => subst E2; cbn [en_exts_o upd_pname]; exact EXo
             | |- Forall _ (blocks_ENTRY _ _) => apply Forall_forall; intros b Hb; pose proof (HB3 b ltac:(apply in_or_app; right; apply SLXq; eapply Permutation_in; [exact PBL2| exact Hb])) as Kb; clear - Kb CEIL; lia
             | |- rw_cells _ _ (bv_unsigned sp + -192) _ => unfold pk_cells; exact PKX
             | |- pk_in _ _ _ _ => unfold pk_in; unfold zlength in *; clear - BC PL0 S2 NLR XL0 XLB ES ELR CR NBL; lia
             | |- 1 <= _ => exact X1
             | |- _ <= 1499 => clear - XLB ES ELR CR NBL NB15 BC PL0 S2 NLR; lia
             | |- bv_unsigned _ <= bv_unsigned sp + -192 => unfold SP'; rewrite unsigned_lit by lia; clear; lia
             | |- _ + 24 <= B => clear - SPB; lia
             | |- en_id _ <> pbin => subst E2; cbn [en_id upd_pname]; intros K; exact (D2 _ _ ELX (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (DREST_SUB [] NB LE))))))) ltac:(cbn; exact K))
             | |- Z.of_nat (length bs) <= nB => exact NBL
             | |- zlength bs <= nB => unfold zlength; exact NBL
             | |- forall b, In b (_ ++ LIB) -> In b _ => intros b Hb; apply S02; apply SLL; exact Hb
             | |- _ <= Bb + zlength bs => unfold zlength; clear - XLB ES ELR CR; lia
             | |- _ <= Bb + Z.of_nat (length bs) => clear - XLB ES ELR CR; lia
             | |- mid_ctx _ = CtxReady x => rewrite CTX1; exact CTX
             | |- mid_flag _ = 1 => exact F1
             | |- forall b b', In b _ -> In b' _ -> _ => intros b b' Hb Hb' K; exact (D23 _ _ ltac:(eapply Permutation_in; [exact PBL2| exact Hb']) (SLL _ Hb) (eq_sym K))
             | |- forall b, In b _ -> blk_id b <> pbin =>
                 intros b Hb K; destruct (DREST_IDS [] Lx2 NB LE ltac:(cbn [app]; destruct (nd_app _ _ ND3) as [_ K2]; exact K2)) as (_ & _ & _ & _ & D5 & _ & _);
                 refine (D5 (pbin, Bb, nB) b (or_introl eq_refl) _ (eq_sym K)); right; apply in_app_or in Hb; destruct Hb as [Hb|Hb]; apply in_or_app; [left; exact Hb| right; exact (SUBL _ Hb)]
             | |- lb_bytes _ + _ + _ + _ <= _ => rewrite lb_bytes_app, drest_app, lb_bytes_app; unfold dbud, DECEXTS_BYTES, ENTRY_BYTES, ENTRY_SIZE, ERRDEBUG_BYTES in *; clear - DB1 EBd EB0 ES ELR PL0 S2 SO4 LB1' NLR XLB XL0; lia
             | |- Z.of_nat (length _) + _ + _ + _ <= _ => rewrite length_app, drest_app, length_app, !Nat2Z.inj_add; unfold dbud, ENTRY_CNT in *;
                   pose proof (Z.div_le_mono (2 * xl) (2 * rem) 5 ltac:(lia) ltac:(clear - XLB ES ELR PL0 S2 NLR; lia)) as DM; clear - DB2 ECd DM EN0 LBN'; lia
             | |- lb_big _ + _ + _ <= _ => rewrite lb_big_app, drest_app, lb_big_app; unfold dbud, ENTRY_BIG in *; rewrite LB3';
                   assert (BR : big1 (6 * ns) <= rem / 1024) by (unfold big1; destruct (BIGB <? 6 * ns) eqn:BB; [apply Z.ltb_lt in BB; unfold BIGB in BB; apply Z.div_le_lower_bound; [lia| clear - BB SO4 ES ELR XLB NLR PL0; lia]| apply Z.div_pos; clear - ELR E19; lia]);
                   clear - DB3 EGd EG0 BR; lia
             | |- bv_unsigned _ <= B => unfold SP'; rewrite unsigned_lit by lia; clear - SPB SPR HSP HCEILB; lia
             | |- bv_unsigned _ mod 16 = 0 => unfold SP'; rewrite unsigned_lit by lia; clear - SPA SPR HSP HCEILB; rewrite Z.add_mod, SPA by lia; reflexivity
             | |- stk _ _ _ _ => unfold SP'; rewrite unsigned_lit by lia; exact STd
             | |- _ <= _ - DECEXTS_STACK _ => unfold SP'; rewrite unsigned_lit by lia; clear - DSK LO; lia
             | |- rw_cells _ _ (errno_addr _) _ => rewrite errno_RATP; exact ERRd
             | |- bv_unsigned _ mod 2 = 0 => unfold DE_R7; rewrite unsigned_lit by lia; reflexivity
             | |- ?G => idtac "DXPRE" G
             end. }
      clear DX. intros [ms4 mo4] PO. unfold decexts_post in PO. cbn [cfg_ms cfg_model] in PO.
      destruct PO as (z7 & z8 & z9 & k1 & k2 & k3 & k4 & k5 & k6 & k7 & z10 & z11 & z12 & z13 & m4 & errv4 & s4q & rv & M'' & xs & exp & NBx & LBN2 & cur' & rem' &
                      -> & KREL4 & MP4 & MI5 & ST4 & ERR4 & AUX4 & HP4 & LM4 & STP4 & NEW4 & CTX4 & VD4 & EC4 & EB4 & EG4 & EO4 & PBX & RV & LGC & LGB & LGG & PK4 & BS4 & PIN4 & CR4 & XP4).
      unfold SP' in ST4, XP4. rewrite (unsigned_lit (bv_unsigned sp + -2352)) in ST4, XP4 by lia. fold (SP' sp) in ST4, XP4.
      pose proof (newlib_len M' M'' LBN2 STP4 NEW4 CTX1) as (LEc & LEb & LEg).
      (* [comment removed for export] *)
      assert (AVX : forall b, In b Lx2 -> b <> (en_id E, ee, ENTRY_SIZE) ->
                 Forall (fun iv : Z * Z => blk_addr b + blk_size b <= fst iv \/ snd iv <= blk_addr b) ((bv_unsigned sp + -192, bv_unsigned sp + -192 + 24) :: (ee, ee + ENTRY_SIZE) :: ERR_X ++ errph_foot (mid_err M'))).
      { intros b Hb NEb. pose proof (HB3 b ltac:(apply in_or_app; right; apply SLXq; exact Hb)) as Kb. pose proof (BRS3 b ltac:(apply in_or_app; right; apply SLXq; exact Hb)) as (_ & _ & _ & _ & OFFb).
        apply Forall_cons; [cbn [fst snd]; clear - Kb HSP; lia|]. apply Forall_cons.
        { cbn [fst snd]. assert (NE : blk_id b <> blk_id (en_id E, ee, ENTRY_SIZE)).
          { intros EQ. apply NEb. exact (nodup_id_inj _ b (en_id E, ee, ENTRY_SIZE) ND3 ltac:(apply in_or_app; right; apply SLXq; exact Hb) ltac:(apply in_or_app; right; apply SLXq; exact ELX2) EQ). }
          pose proof (DISJ3 _ _ ltac:(apply in_or_app; right; apply SLXq; exact Hb) ltac:(apply in_or_app; right; apply SLXq; exact ELX2) NE) as DJ. cbn [blk_addr blk_size fst snd] in DJ. clear - DJ. lia. }
        apply Forall_app. split; [apply avoid_of_img; [apply img_ERR_X| unfold IMG_LO, IMG_HI; clear - OFFb; lia]|].
        destruct (mid_err M') as [|c] eqn:EQ; [apply Forall_nil|]. cbn [errph_foot]. apply Forall_cons; [| apply Forall_nil]. cbn [fst snd].
        destruct (DWK_ES _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ c DW3 EQ) as [I5 Z5].
        pose proof (DISJ3 (ec_es c) b ltac:(apply in_or_app; right; apply S02; apply SLL; exact I5) ltac:(apply in_or_app; right; apply SLXq; exact Hb) ltac:(intros K; exact (D23 _ _ Hb (SLL _ I5) (eq_sym K)))) as DJ.
        rewrite Z5 in DJ. clear - DJ. lia. }
      assert (NEs : (pS, SA, 6 * ns) <> (en_id E, ee, ENTRY_SIZE)) by (intros K; injection K as K1 K2 K3; exact (NES (eq_sym K1))).
      assert (NEn : (pN, D, nl + 1) <> (en_id E, ee, ENTRY_SIZE)).
      { intros K. injection K as K1 K2 K3. destruct (nd_app _ _ ND3) as [_ N1]. subst Lx2. rewrite drest_app in N1. cbn [app] in N1. rewrite map_cons in N1.
        apply NoDup_cons_iff in N1 as [NI _]. apply NI. rewrite map_app. apply in_or_app. left.
        replace (blk_id (pN, D, nl + 1)) with (blk_id (en_id E, ee, ENTRY_SIZE)) by (cbn; symmetry; exact K1). apply in_map. exact ELX. }
      eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP4) in SC3; [| eapply (rclient_range_block _ _ (pS, SA, 6 * ns)); [apply SLXq; exact SLX2| cbn; clear; lia| rewrite SSZ; cbn; clear; lia]| rewrite SSZ; exact (AVX _ SLX2 NEs)].
      eapply (xpres_bytes_at' _ _ _ _ _ _ _ XP4) in NMB3; [| eapply (rclient_range_block _ _ (pN, D, nl + 1)); [apply SLXq; exact NLX2| cbn; clear; lia| rewrite length_app, Nat2Z.inj_add, NML; cbn; clear; lia]
                                                       | rewrite length_app, Nat2Z.inj_add, NML; cbn [length Z.of_nat Pos.of_succ_nat]; exact (AVX _ NLX2 NEn)].
      (* [comment removed for export] *)
      assert (AVF : (forall a n, bv_unsigned sp + -168 <= a -> Forall (fun iv : Z * Z => a + n <= fst iv \/ snd iv <= a) ((bv_unsigned sp + -192, bv_unsigned sp + -192 + 24) :: (ee, ee + ENTRY_SIZE) :: ERR_X ++ errph_foot (mid_err M')))
                 /\ (forall a' n', SPc <= a' -> a' + n' <= SPc + 112 -> Forall (fun iv : Z * Z => a' + n' <= fst iv \/ snd iv <= a') ((bv_unsigned sp + -192, bv_unsigned sp + -192 + 24) :: (ee, ee + ENTRY_SIZE) :: ERR_X ++ errph_foot (mid_err M')))).
      { assert (TAIL : forall a n, SPc <= a -> Forall (fun iv : Z * Z => a + n <= fst iv \/ snd iv <= a) ((ee, ee + ENTRY_SIZE) :: ERR_X ++ errph_foot (mid_err M'))).
        { intros a n Ha. apply Forall_cons; [cbn [fst snd]; unfold SP' in Ha; unfold ENTRY_SIZE; clear - Ha EEH HSP; lia|].
          apply Forall_app. split; [apply avoid_of_img; [apply img_ERR_X| right; unfold SP', IMG_HI in *; clear - Ha HSP HCEILB; lia]|].
          destruct (mid_err M') as [|c] eqn:EQ; [apply Forall_nil|]. cbn [errph_foot]. apply Forall_cons; [| apply Forall_nil]. cbn [fst snd].
          destruct (DWK_ES _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ c DW3 EQ) as [I5 Z5].
          pose proof (HB3 (ec_es c) ltac:(apply in_or_app; right; apply S02; apply SLL; exact I5)) as Kc. rewrite Z5 in Kc. right. unfold SP' in Ha. clear - Kc Ha HSP. lia. }
        split; [intros a n Ha; apply Forall_cons; [cbn [fst snd]; clear - Ha; lia| apply TAIL; unfold SP'; clear - Ha; lia]|].
        intros a' n' H1 H2. apply Forall_cons; [cbn [fst snd]; unfold SP' in H2; clear - H2; lia| apply TAIL; exact H1]. }
      destruct AVF as [AVF AVF0].
      eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP4) in F3r3; [| left; unfold SP'; clear; lia| apply AVF; clear; lia].
      pose proof (F3_join3 _ _ _ _ _ _ _ _ _ _ _ _ _ PK4 F3r3) as F3w4.
      eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP4) in FR0d; [| left; clear; lia| apply AVF0; [clear; lia| unfold dframe; cbn; clear; lia]].
      assert (DAPP : forall L LE', DREST (NBx ++ L) NB LE' = NBx ++ DREST L NB LE') by (intros; unfold drest; rewrite <- app_assoc; reflexivity).
      assert (DW4 : DWK (NBx ++ Lx2) NB S' M'' (LBN2 ++ LE) w0 w1 w3 (Z_to_bv 64 (cur + 4)) w5 w6 (Z_to_bv 64 (rem - 4)) (Z_to_bv 64 elen)
                        (cells_bytes (F3W (Z_to_bv 64 cur') (Z_to_bv 64 Bb) (Z_to_bv 64 rem') (Z_to_bv 64 (cur + 9 + publen + 2 + so + 2)) (Z_to_bv 64 Bb) (Z_to_bv 64 nl) v6 v7 v8 v9 v10)) m4 mo4 s4q).
      { eapply (DWK_LIB Lx2 (NBx ++ Lx2) NB S' M' M'' LE LBN2) with (X := [(bv_unsigned sp + -192, bv_unsigned sp + -192 + 24); (ee, ee + ENTRY_SIZE)]);
          [exact DW3| exact LM4| exact STP4| exact NEW4| rewrite CTX4; reflexivity| exact EC4| exact EB4| exact EG4| exact XP4| | | exact KREL4| eapply (mpres_trans H HH); [eapply (mpres_trans H HH); [exact MP1| exact MP2]| exact MP4]
          | exists errv4; rewrite <- errno_RATP; exact ERR4| exact MI5| exact ST4| exact AUX4| exact FR0d| rewrite F3E; apply F3_cb; exact F3w4].
        - apply Forall_cons; [right; left; unfold SP', O_F3, O_SAVES; cbn; clear; lia|]. apply Forall_cons; [| apply Forall_nil].
          right; right. exists (en_id E, ee, ENTRY_SIZE). split; [exact ELX2| cbn; clear; lia].
        - eapply PERM; [exact HP4|]. apply Permutation_app_head. rewrite DAPP. apply Permutation_app_head. apply Permutation_sym. apply drest_newlib_perm. }
      assert (SUB4 : forall b, In b (NBx ++ LBN2 ++ DREST Lx2 NB LE) -> In b (DREST (NBx ++ Lx2) NB (LBN2 ++ LE))).
      { intros b Hb. eapply Permutation_in; [| exact Hb]. rewrite DAPP. apply Permutation_app_head. apply Permutation_sym. apply drest_newlib_perm. }
      pose proof (ENTRYobj_LB_mono _ _ _ _ _ EO4 SUB4) as EO4'. clear EO4.
      (* [comment removed for export] *)
      assert (DBX : forall hb hc hg, DBUD (DREST Lx2 NB LE) M' (lb_bytes NBx + hb) (Z.of_nat (length NBx) + hc) (lb_big NBx + hg) -> DBUD (DREST (NBx ++ Lx2) NB (LBN2 ++ LE)) M'' hb hc hg).
      { intros hb hc hg (Q1 & Q2 & Q3). unfold dbud. rewrite DAPP.
        rewrite (lb_bytes_perm _ _ (Permutation_app_head NBx (drest_newlib_perm Lx2 NB LBN2 LE))), (Permutation_length (Permutation_app_head NBx (drest_newlib_perm Lx2 NB LBN2 LE))),
                (lb_big_perm _ _ (Permutation_app_head NBx (drest_newlib_perm Lx2 NB LBN2 LE))).
        rewrite (lb_bytes_app NBx), (lb_bytes_app LBN2), (length_app NBx), (length_app LBN2), (lb_big_app NBx), (lb_big_app LBN2), !Nat2Z.inj_add. clear - Q1 Q2 Q3 LEc LEb LEg. lia. }
      (* [comment removed for export] *)
      eapply (sr_evt_krel H HH); [exact KREL4| eapply de_seg10; [clear - RV; destruct RV as [(Rq & _)|(Rq & _)]; [right| left]; exact Rq| exact MI5]|].
      cbv beta. intros ms5 [[R0 ->]|[R1 ->]].
      + (* [comment removed for export] *)
        destruct RV as [(Rq & _)|(_ & XS0 & EXP0 & NB0)]; [exfalso; clear - Rq R0; lia|]. subst xs exp NBx. cbn [app] in DW4, EO4', DBX.
        eapply KTA' with (E := E2); [exact DW4| | exact PBL2| clear; lia| apply DBX; cbn [lb_bytes lb_big length fold_right Z.of_nat Z.add]; exact TAILB2].
        revert EO4'. subst E2. unfold upd_pname. cbn [en_version en_id en_pname en_pname_o en_publen en_pub en_pub_o en_nsuites en_suites en_suites_o en_maxname en_cfgid en_enclen en_encoded en_encoded_o en_exts en_exts_o en_loadtime en_forretry].
        rewrite EX0, EXo. intros EO4'. exact EO4'.
      + (* [comment removed for export] *)
        destruct RV as [(_ & XSS & RM0)|(Rq & _)]; [| exfalso; clear - Rq R1; lia]. subst rem'.
        match type of EO4' with ENTRYobj _ _ _ ?Ex => set (E4 := Ex) in EO4' end.
        assert (PBL4 : Permutation (blocks_ENTRY ee E4) (NBx ++ Lx2)).
        { subst E4. unfold blocks_ENTRY in PBL2 |- *. revert PBL2. subst E2.
          cbn [en_id en_pname en_pname_o en_pub en_pub_o en_suites en_suites_o en_encoded en_encoded_o en_exts en_exts_o upd_pname]. rewrite EX0, EXo. cbn [blocks_EXTS]. rewrite app_nil_r. intros PBL2.
          eapply Permutation_trans; [| apply Permutation_app_comm]. rewrite !app_assoc. change (?a :: ?l ++ blocks_EXTS exp xs) with ((a :: l) ++ blocks_EXTS exp xs). apply Permutation_app; [| exact PBX].
          rewrite <- !app_assoc. exact PBL2. }
        eapply (de_phase7 cur rem elen (cur + 9 + publen + 2 + so + 2 + nl + 2) xl (NBx ++ Lx2) NB S' M'' (LBN2 ++ LE)) with (E := E4) (rows := rows) (nm := nm) (pS := pS) (sn := 6 * ns) (pn := pN);
          [exact DW4| exact EO4'| exact PBL4| | | | | | | unfold zlength; rewrite RWL| | exact RWO| | | exact NONUL| unfold zlength; rewrite NML; clear - NLR; lia
          | | | | exact E19| exact ELR| exact BC| unfold zlength; exact CR| clear - XL0 XLB ES PL0 S2 NLR; lia| | exact KOK| exact KTZ].
        all: try (subst E4 E2; cbn [en_id en_pname en_pname_o en_pub en_pub_o en_suites en_suites_o en_nsuites en_encoded en_encoded_o en_exts en_exts_o en_loadtime en_forretry upd_pname];
                  unfold zlength; rewrite ?NSE, ?SUE, ?NML; first [reflexivity| assumption| clear - NS1 NSR; lia]).
        * rewrite length_app, Nat2Z.inj_add. clear - LGC LBN' E19 XLB ES SO4 NS1 NLR PL0. lia.
        * rewrite lb_bytes_app. unfold ENTRY_KEPT, ENTRY_SIZE, SK_SIZE in *. clear - LGB LB1' ES XLB XL0 SO4 NS1 NLR PL0. lia.
        * rewrite lb_big_app, LB3'. unfold big1. destruct (BIGB <? 6 * ns) eqn:BB.
          -- apply Z.ltb_lt in BB. unfold BIGB in BB. assert (XE : 1200 + xl <= elen) by (clear - BB SO4 ES XLB NLR PL0; lia).
             pose proof (Z.div_le_mono (1200 + xl) elen 600 ltac:(lia) XE) as DM. replace (1200 + xl) with (2 * 600 + xl) in DM by lia. rewrite (Z.div_add_l 2 600 xl) in DM by lia. clear - DM LGG. lia.
          -- pose proof (Z.div_le_mono xl elen 600 ltac:(lia) ltac:(clear - XLB ES PL0 S2 NLR; lia)) as DM. clear - DM LGG. lia.
        * apply DBX. unfold dbud. rewrite drest_app, lb_bytes_app, length_app, lb_big_app, Nat2Z.inj_add. unfold dbud, ENTRY_BYTES, ENTRY_CNT, ENTRY_BIG, ENTRY_SIZE, SK_SIZE in *.
          pose proof (Z.div_le_mono (2 * xl) (2 * rem) 5 ltac:(lia) ltac:(clear - XLB ES ELR PL0 S2 NLR; lia)) as DM.
          assert (BR : big1 (6 * ns) <= rem / 1024) by (unfold big1; destruct (BIGB <? 6 * ns) eqn:BB; [apply Z.ltb_lt in BB; unfold BIGB in BB; apply Z.div_le_lower_bound; [lia| clear - BB SO4 ES ELR XLB NLR PL0; lia]| apply Z.div_pos; clear - ELR E19; lia]).
          assert (XG : xl / 600 < 3) by (apply Z.div_lt_upper_bound; [lia|]; clear - XLB ES ELR CR NBL NB15 BC PL0 S2 NLR; lia).
          clear - DB1 DB2 DB3 DM BR XG ELR ES PL0 S2 SO4 NLR LB1' LBN' LB3' B1 LGC LGB LGG XLB XL0. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma memchr_ok_all : forall A1 c n buf, Z.of_nat (length buf) = n -> memchr_ok A1 c n buf.
  Proof. clear. intros A1 c n buf L. unfold memchr_ok. destruct (find_byte c (firstn (Z.to_nat n) buf)); lia. Qed.
  Lemma memchr_res_range : forall A1 c n buf, 0 <= A1 -> 0 <= memchr_res A1 c n buf <= A1 + Z.of_nat (length buf) /\ (memchr_res A1 c n buf = 0 -> 0 < A1 -> find_byte c (firstn (Z.to_nat n) buf) = None).
  Proof.
    clear. intros A1 c n buf A0. unfold memchr_res. destruct (find_byte c (firstn (Z.to_nat n) buf)) as [i|] eqn:FB.
    - pose proof (find_byte_Some _ _ _ FB) as (Hi & _). rewrite length_firstn in Hi. split; [lia|]. intros E P. exfalso. lia.
    - split; [lia|]. intros _ _. reflexivity.
  Qed.
  Lemma find_byte_None_notin : forall c l, find_byte c l = None -> 0 <= c < 256 -> ~ In (Z_to_bv 8 c) l.
  Proof.
    clear. intros c l FB CR IN. apply In_nth_error in IN. destruct IN as [j Hj].
    apply (find_byte_None _ _ FB _ _ Hj). rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8%N) with 256. rewrite Z.mod_small by lia. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma de_phase5 : forall (cur rem elen publen kemhi kemlo so sohi solo ns : Z) (Lx NB : list block) (S' : storerep) (M' : libmid) (LE : list block) (w0 w1 w3 : word) (j3 : list byte)
           (m' : mem) (mo' : Model) (s' : PState) (ee SA : Z) (pS : bptr) (E : entrep) (junk : list byte)
           (u0 u1 u2 g1 g2 g3 g4 g5 g6 g7 u3 u4 u5 u6 : word),
      DWK Lx NB S' M' LE w0 w1 w3 (Z_to_bv 64 (cur + 4)) (Z_to_bv 64 (elen - 5 - publen - 2)) (Z_to_bv 64 kemlo) (Z_to_bv 64 (rem - 4)) (Z_to_bv 64 elen) j3 m' mo' s' ->
      ENTRYobj (DREST Lx NB LE) m' ee E -> Permutation ((pS, SA, 6 * ns) :: blocks_ENTRY ee E) Lx ->
      en_suites_o E = None -> en_pname_o E = None -> en_encoded_o E = None -> en_exts E = 0 -> en_exts_o E = None -> en_loadtime E = 0 -> en_forretry E = 0 ->
      en_nsuites E = ns -> rw_cells rsegs m' SA [CB (Z.to_nat (6 * ns)) junk] -> 0 < SA ->
      lb_bytes Lx <= ENTRY_SIZE + publen + 6 * ns -> Z.of_nat (length Lx) <= 3 -> lb_big Lx = big1 (6 * ns) ->
      Bb + 2 <= cur -> 0 <= publen -> 0 <= solo < 256 -> 0 <= sohi < 256 -> so = solo + 256 * sohi -> 2 <= so -> so mod 2 = 0 -> ns = so / 4 -> 1 <= ns ->
      5 + publen + 2 + so <= elen -> 4 + elen <= rem -> cur + rem <= Bb + zlength bs -> 0 <= kemhi < 256 -> 0 <= kemlo < 256 ->
      DBUD (DREST [] NB LE) M' (ENTRY_BYTES rem) (ENTRY_CNT rem) (ENTRY_BIG rem) ->
      KOKp cur rem NB S' -> KTAp -> KTZp ->
      hs_SR H POSTc (mkCfg (MS (mkR (Z_to_bv 64 DE_R4) (Z_to_bv 64 SPc) gp (Z_to_bv 64 RATP) u0 u1 u2 sp (Z_to_bv 64 A) (Z_to_bv 64 SA) g1 g2 g3 g4 g5 g6 g7
                                  (Z_to_bv 64 bt) (Z_to_bv 64 Bb) (Z_to_bv 64 so) (Z_to_bv 64 (cur + 9 + publen)) (Z_to_bv 64 solo) (Z_to_bv 64 ee) (Z_to_bv 64 ns) (Z_to_bv 64 kemhi) (Z_to_bv 64 cur) (Z_to_bv 64 400) u3 u4 u5 u6)
                             F (ret_pc (Z_to_bv 64 DE_R4)) fc None m' (seg_rom rsegs)) mo').
  Proof.
    intros until u6. intros DW EO PBL SUo PNo ENo EX0 EXo LT0 FRy NSE SC SAP LB1 LBN LB3 BC PL0 SOL SOH SOE S2 EVN NSQ NS1 ES ELR CR KH KL DB0 KOK KTA KTZ.
    pose proof KTA as KTA'. unfold dK_tailA in KTA'.
    pose proof DW as (HP1 & KREL1 & MP1 & LM1 & STP & NEW & CTX1 & EC & EB & EG & LC & LBY & LG & SO1 & SID & SPM & SND & SKI & MBO1 & DSm1 & DSb1 & BT1
                      & FR0 & FR2 & FR3 & FR4 & [errv1 ERR1] & MI1 & ST1 & AUX1 & XA1 & DNB1).
    destruct (de_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ DW) as (HSP & SPE & F3E & BP & BH & IB2 & NBL & NB11 & BLX & HB & F1 & MF & IM & GM & GE).
    destruct (DWK_HF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ DW) as (_ & ND & DISJ & BRS & D2 & D1).
    destruct RCFACTS as (SEQ & SIN & SBR & BEL0 & SUB0 & ND0 & STK0 & LO0 & MF0 & OBJ0 & DJA).
    pose proof (DREST_SUB Lx NB LE) as (SLB & S0 & SLE & SNB & STB & IB & IA & SLX & S3 & SLL).
    hcb. pose proof (word_range sp) as SPR. unfold zlength in *. assert (NB15 : nB < 1500) by (unfold OSSL_ECH_MAX_ECHCONFIG_LEN in NBR; clear - NBR; lia).
    pose proof EO as ((pad1 & pad2 & pad3 & pad4 & L1 & L2 & L3 & L4 & ECc) & EIN' & O1 & O2 & O3 & O4 & XS).
    assert (ELX : In (en_id E, ee, ENTRY_SIZE) Lx) by (eapply Permutation_in; [exact PBL| right; left; reflexivity]).
    assert (SLXi : In (pS, SA, 6 * ns) Lx) by (eapply Permutation_in; [exact PBL| left; reflexivity]).
    assert (EIN : In (en_id E, ee, ENTRY_SIZE) (mid_errblocks M' ++ DREST Lx NB LE)) by (apply in_or_app; right; exact EIN').
    assert (SIN' : In (pS, SA, 6 * ns) (mid_errblocks M' ++ DREST Lx NB LE)) by (apply in_or_app; right; apply SLX; exact SLXi).
    pose proof (HB _ EIN) as EEH. pose proof (BRS _ EIN) as (EEP & _ & _ & _ & OFFE). cbn [blk_addr blk_size fst snd] in EEH, EEP, OFFE. unfold ENTRY_SIZE in EEH, OFFE.
    pose proof (BLX _ ELX) as EBA. cbn [blk_addr blk_size fst snd] in EBA. unfold ENTRY_SIZE in EBA.
    pose proof (HB _ SIN') as SAH. cbn [blk_addr blk_size fst snd] in SAH. pose proof (BLX _ SLXi) as SBA. cbn [blk_addr blk_size fst snd] in SBA.
    assert (NES : en_id E <> pS).
    { intros EQ. pose proof (nodup_id_inj _ (en_id E, ee, ENTRY_SIZE) (pS, SA, 6 * ns) ND EIN SIN' EQ) as K. injection K as E1q E2q E3q. unfold ENTRY_SIZE in E3q. clear - E3q. lia. }
    pose proof (DISJ _ _ SIN' EIN ltac:(cbn [blk_id fst snd]; intros K; exact (NES (eq_sym K)))) as SEA. cbn [blk_addr blk_size fst snd] in SEA. unfold ENTRY_SIZE in SEA.
    destruct DB0 as (DB1 & DB2 & DB3). pose proof (dec_stack M M' STP) as DSK. pose proof (errph_nonneg (mid_err M')) as (EB0 & EN0 & EG0).
    assert (SO4 : 4 * ns <= so) by (rewrite NSQ; clear - S2; pose proof (Z.mul_div_le so 4 ltac:(lia)); lia).
    (* [comment removed for export] *)
    rewrite SPE in FR0. unfold dframe in FR0.
    replace (cur + 9 + publen) with (Bb + (cur + 9 + publen - Bb)) by lia.
    eapply (sr_evt_krel H HH); [exact KREL1| eapply (de_seg5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Bb cur ee so (cur + 9 + publen - Bb) solo ns kemhi kemlo SA (Z.of_nat (length bs)) E (Some (pS, 6 * ns)));
      [exact FR0| exact ECc| exact EEP| unfold ENTRY_SIZE; exact EEH| clear - SAP; lia| exact SAH| exact KH| exact KL| clear - NS1 NSQ SOL SOH SOE; lia| clear - SOL SOH SOE; lia| exact BP
      | clear - BC CR ES ELR; lia| exact BH| exact HSP| exact MI1]|].
    cbv beta. intros ms1 (m1 & MU1 & WM1 & MI2 & EC2 & [[K _]|[_ ->]]); [exfalso; clear - K SAP; lia|].
    assert (DW1 : DWK Lx NB S' M' LE w0 w1 w3 (Z_to_bv 64 (cur + 4)) (Z_to_bv 64 (elen - 5 - publen - 2)) (Z_to_bv 64 kemlo) (Z_to_bv 64 (rem - 4)) (Z_to_bv 64 elen) j3 m1 mo' s').
    { eapply (DWK_W Lx NB S' M' LE); [exact DW| exact MU1| exact WM1| exact MI2| | | |].
      - eapply stk_transport_disjoint; [exact ST1| exact MU1| exact WM1| unfold SP'; cbn; clear - EEH CEIL LO STK0; lia].
      - apply Forall_cons; [| apply Forall_nil]. right; right; right; exists (en_id E, ee, ENTRY_SIZE); split; [exact ELX| cbn; unfold ENTRY_SIZE; clear; lia].
      - rewrite SPE. unfold dframe. eapply rw_cells_transport; [exact FR0| exact MU1| exact WM1| cbn; clear - EEH CEIL LO STK0; lia].
      - eapply rw_cells_transport; [exact FR3| exact MU1| exact WM1| rewrite F3E; cbn; clear - EEH HSP; lia]. }
    apply (rw_cells_transport rsegs _ m' m1 _ _ SC) in MU1 as SC1; [| exact WM1| cbn; clear - SEA NS1; lia].
    set (E1 := upd_suites E SA (Some (pS, 6 * ns))) in EC2.
    assert (PBL1 : Permutation (blocks_ENTRY ee E1) Lx).
    { eapply Permutation_trans; [| exact PBL]. unfold blocks_ENTRY. subst E1.
      cbn [en_id en_pname en_pname_o en_pub en_pub_o en_suites en_suites_o en_encoded en_encoded_o en_exts en_exts_o upd_suites]. rewrite SUo, PNo, ENo, EXo, EX0.
      cbn [blocks_of blocks_EXTS app]. rewrite !app_nil_r.
      change ((en_id E, ee, ENTRY_SIZE) :: blocks_of (en_pub E) (en_pub_o E) ++ [(pS, SA, 6 * ns)]) with (((en_id E, ee, ENTRY_SIZE) :: blocks_of (en_pub E) (en_pub_o E)) ++ [(pS, SA, 6 * ns)]).
      apply Permutation_sym. apply Permutation_cons_append. }
    assert (EOK : forall mm mx, rw_cells rsegs mm ee (entry_cells (upd_maxname E1 mx) pad1 pad2 pad3 pad4) -> ENTRYobj (DREST Lx NB LE) mm ee (upd_maxname E1 mx)).
    { intros mm mx ECm. unfold ENTRYobj. subst E1. cbn [en_id en_pname en_pname_o en_pub en_pub_o en_suites en_suites_o en_encoded en_encoded_o en_exts en_exts_o upd_suites upd_maxname].
      split; [exists pad1, pad2, pad3, pad4; split; [exact L1|]; split; [exact L2|]; split; [exact L3|]; split; [exact L4| exact ECm]|].
      split; [exact EIN'|]. split; [exact O1|]. split; [exact O2|]. split; [cbn [ofield]; split; [exact SAP|]; split; [clear - NS1; lia| apply SLX; exact SLXi]|]. split; [exact O4|].
      rewrite EXo in XS |- *. exact XS. }
    assert (TAILB : DBUD (DREST Lx NB LE) M' ERRDEBUG_BYTES 2 0).
    { unfold dbud. rewrite drest_app, lb_bytes_app, length_app, lb_big_app, Nat2Z.inj_add. unfold dbud, ENTRY_BYTES, ENTRY_CNT, ENTRY_BIG, ENTRY_SIZE, ERRDEBUG_BYTES in *.
      pose proof (Z.div_pos (2 * rem) 5 ltac:(clear - ELR ES PL0 S2; lia) ltac:(lia)) as DP1. pose proof (Z.div_pos rem 1024 ltac:(clear - ELR ES PL0 S2; lia) ltac:(lia)) as DP2.
      assert (B1 : big1 (6 * ns) <= 1) by (unfold big1; destruct (BIGB <? 6 * ns); clear; lia).
      clear - DB1 DB2 DB3 DP1 DP2 ELR ES PL0 S2 LB1 LBN LB3 B1 SO4. lia. }
    clear MU1 WM1.
    (* [comment removed for export] *)
    pose proof DW1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & DSbb & _ & _ & _ & _ & _ & _ & MIb & STb & _).
    replace (Z_to_bv 64 (SA + 4)) with (Z_to_bv 64 (SA + 4 + 6 * 0)) by (f_equal; lia).
    replace (Z_to_bv 64 (Bb + (cur + 9 + publen - Bb) + 2)) with (Z_to_bv 64 (Bb + (cur + 9 + publen - Bb) + 2 + 4 * 0)) by (f_equal; lia).
    eapply (sr_evt_krel H HH); [exact KREL1| eapply (de_loop (Z.to_nat ns) 0) with (E := E1);
      [clear - NS1; lia| clear - NS1; lia| | clear - NS1 NSQ SOL SOH SOE; lia| clear - KH KL; lia| replace (SA + 6 * 0) with SA by lia; replace (6 * (ns - 0)) with (6 * ns) by lia; exact SC1| exact SAP| exact SAH
      | exact DSbb| exact BP| clear - BC PL0; lia| | exact BH| unfold zlength; clear - SBA NBL; lia| exact EC2| exact EEP| unfold ENTRY_SIZE; exact EEH| unfold ENTRY_SIZE; clear - SEA; lia| exact HSP| exact MIb]|].
    { subst E1. cbn [en_nsuites upd_suites]. exact NSE. }
    { unfold zlength. clear - BC CR ES ELR SO4; lia. }
    cbv beta. intros ms2 (t0' & a5' & a6' & a7' & m2 & junk' & MU2 & WM2 & MI3 & SC2 & BS2 & EC3 & ->).
    assert (DW2 : DWK Lx NB S' M' LE w0 w1 w3 (Z_to_bv 64 (cur + 4)) (Z_to_bv 64 (elen - 5 - publen - 2)) (Z_to_bv 64 kemlo) (Z_to_bv 64 (rem - 4)) (Z_to_bv 64 elen) j3 m2 mo' s').
    { pose proof DW1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FR0b & _ & FR3b & _).
      eapply (DWK_W Lx NB S' M' LE); [exact DW1| exact MU2| exact WM2| exact MI3| | | |].
      - eapply stk_transport_disjoint; [exact STb| exact MU2| exact WM2| unfold SP'; cbn; clear - SAH CEIL LO STK0; lia].
      - apply Forall_cons; [| apply Forall_nil]. right; right; right; exists (pS, SA, 6 * ns); split; [exact SLXi| cbn; clear; lia].
      - eapply rw_cells_transport; [exact FR0b| exact MU2| exact WM2| unfold SP'; cbn; clear - SAH CEIL LO STK0; lia].
      - eapply rw_cells_transport; [exact FR3b| exact MU2| exact WM2| unfold SP', O_F3; cbn; clear - SAH HSP; lia]. }
    apply rw_cells_app in SC2 as [SC2 _]. replace (SA + 6 * 0) with SA in SC2 by lia.
    match type of SC2 with rw_cells _ _ _ (suite_cells ?r) => set (rows := r) in SC2 end.
    assert (ROWS : Z.of_nat (length rows) = ns /\ Forall row_ok rows) by (subst rows; split; [rewrite srows_length; clear - NS1; lia| apply srows_ok; clear - KH KL; lia]). clearbody rows.
    pose proof (suite_cells_size rows) as SSZ. unfold zlength in SSZ. rewrite (proj1 ROWS) in SSZ.
    clear MU2 WM2.
    (* [comment removed for export] *)
    pose proof DW2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & DSbc & _ & FR0c & _ & FR3c & _ & _ & MIc & STc & _).
    rewrite SPE in FR0c. unfold dframe in FR0c. rewrite F3E in FR3c. destruct (F3_words _ _ _ FR3c) as (v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & F3w).
    eapply (sr_evt_krel H HH); [exact KREL1| eapply de_seg7 with (E := E1) (q := cur + 9 + publen - Bb) (cur := cur);
      [exact FR0c| exact F3w| exact DSbc| clear - BC PL0; lia| clear - S2; lia| clear - ES; lia| unfold zlength; clear - BC CR ES ELR; lia| exact BP| exact BH
      | clear - SOL SOH SOE; subst so; lia| exact SOL| exact EVN| exact EC3| exact EEP| unfold ENTRY_SIZE; exact EEH| unfold ENTRY_SIZE; exact EBA| exact HSP| exact MIc]|].
    cbv beta. intros ms3 (a0' & a1' & a2' & s4' & s8' & s9' & m3 & f3 & f4 & f5 & mx & line & MU3 & WM3 & MI4 & F3w3 & EC4 & MXR & CASES).
    assert (DW3 : DWK Lx NB S' M' LE w0 w1 w3 (Z_to_bv 64 (cur + 4)) (Z_to_bv 64 (elen - 5 - publen - 2)) (Z_to_bv 64 kemlo) (Z_to_bv 64 (rem - 4)) (Z_to_bv 64 elen) (cells_bytes (F3W v0 v1 v2 f3 f4 f5 v6 v7 v8 v9 v10)) m3 mo' s').
    { eapply (DWK_W Lx NB S' M' LE); [exact DW2| exact MU3| exact WM3| exact MI4| | | |].
      - eapply stk_transport_disjoint; [exact STc| exact MU3| exact WM3| unfold SP'; cbn; clear - EEH CEIL LO STK0; lia].
      - apply Forall_cons; [right; right; right; exists (en_id E, ee, ENTRY_SIZE); split; [exact ELX| cbn; unfold ENTRY_SIZE; clear; lia]|].
        apply Forall_cons; [| apply Forall_nil]. right; right; left. unfold SP', O_F3, O_SAVES. cbn. clear; lia.
      - rewrite SPE. unfold dframe. eapply rw_cells_transport; [exact FR0c| exact MU3| exact WM3| cbn; clear - EEH CEIL LO STK0; lia].
      - rewrite F3E. apply F3_cb. exact F3w3. }
    apply (rw_cells_transport rsegs _ m2 m3 _ _ SC2) in MU3 as SC3; [| exact WM3| rewrite SSZ; cbn [disjoint_from]; clear - SEA SAH HSP NS1; lia].
    clear WM3.
    destruct CASES as [(LN & ->)|(nl & SO2 & [NL0 NL8] & SNL & MX & NQ & NN & -> & -> & -> & ->)].
    - (* [comment removed for export] *)
      eapply KTA' with (E := upd_maxname E1 mx); [exact DW3| exact (EOK _ _ EC4)| unfold blocks_ENTRY in PBL1 |- *; exact PBL1| clear - LN; lia| exact TAILB].
    - (* [comment removed for export] *)
      pose proof DW3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & DSbd & _ & FR0d & _ & FR3d & _ & _ & MId & STd & _).
      destruct (bytes_at_sub m3 Bb bs (cur + 9 + publen + 2 + so + 2 - Bb) nl DSbd ltac:(clear - BC PL0 S2; lia) ltac:(exact NL0) ltac:(clear - BC CR ES ELR SNL; lia)) as [BSN NML].
      set (nm := firstn (Z.to_nat nl) (skipn (Z.to_nat (cur + 9 + publen + 2 + so + 2 - Bb)) bs)) in *.
      replace (Bb + (cur + 9 + publen + 2 + so + 2 - Bb)) with (Bb + (cur + 9 + publen - Bb) + 2 + so + 2) in BSN by lia.
      eapply (sr_evt_krel H HH); [exact KREL1| eapply memchr_spec with (buf := nm); [rewrite unsigned_lit by lia; exact BSN| apply memchr_ok_all; rewrite unsigned_lit by lia; exact NML| exact MId]|].
      cbv beta. intros ms4 (z0 & z1 & z2 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & z3 & z4 & z5 & z6 & m4 & -> & MU4 & WM4 & MI5 & BS4).
      rewrite (unsigned_lit 0) by lia. rewrite (unsigned_lit nl) by lia. rewrite (unsigned_lit (Bb + (cur + 9 + publen - Bb) + 2 + so + 2)) by lia. change (0 mod 256) with 0.
      destruct (memchr_res_range (Bb + (cur + 9 + publen - Bb) + 2 + so + 2) 0 nl nm ltac:(clear - BP BC PL0 S2; lia)) as [RR RZ]. rewrite NML in RR.
      set (res := memchr_res (Bb + (cur + 9 + publen - Bb) + 2 + so + 2) 0 nl nm) in *.
      assert (DW4 : DWK Lx NB S' M' LE w0 w1 w3 (Z_to_bv 64 (cur + 4)) (Z_to_bv 64 (elen - 5 - publen - 2)) (Z_to_bv 64 kemlo) (Z_to_bv 64 (rem - 4)) (Z_to_bv 64 elen) (cells_bytes (F3W v0 v1 v2 (Z_to_bv 64 (Bb + (cur + 9 + publen - Bb) + 2 + so + 2)) (Z_to_bv 64 Bb) (Z_to_bv 64 nl) v6 v7 v8 v9 v10)) m4 mo' s').
      { eapply (DWK_W Lx NB S' M' LE); [exact DW3| exact MU4| exact WM4| exact MI5| | apply Forall_nil| |].
        - eapply stk_transport_disjoint; [exact STd| exact MU4| exact WM4| cbn; exact I].
        - eapply rw_cells_transport; [exact FR0d| exact MU4| exact WM4| cbn; exact I].
        - eapply rw_cells_transport; [exact FR3d| exact MU4| exact WM4| cbn; exact I]. }
      apply (rw_cells_transport rsegs _ m3 m4 _ _ SC3) in MU4 as SC4; [| exact WM4| cbn; exact I].
      pose proof MU4 as MU4'. apply (rw_cells_transport rsegs _ m3 m4 _ _ EC4) in MU4' as EC5; [| exact WM4| cbn; exact I].
      clear WM4.
      (* [comment removed for export] *)
      eapply (sr_evt_krel H HH); [exact KREL1| eapply de_seg8; [clear - RR BH HCEILB BC PL0 S2 CR ES ELR SNL; lia| clear - NL0 NL8; lia| exact EEP| unfold ENTRY_SIZE; exact EEH| exact HSP| exact MI5]|].
      cbv beta. intros ms5 [[_ ->]|(N4 & R0 & ->)].
      + (* [comment removed for export] *)
        eapply KTA' with (E := upd_maxname E1 mx); [exact DW4| exact (EOK _ _ EC5)| unfold blocks_ENTRY in PBL1 |- *; exact PBL1| clear; lia| exact TAILB].
      + (* [comment removed for export] *)
        replace (Bb + (cur + 9 + publen - Bb) + 2 + so + 2) with (cur + 9 + publen + 2 + so + 2) in DW4 |- * by lia.
        eapply (de_phase6 cur rem elen publen so ns nl Lx NB S' M' LE) with (E := upd_maxname E1 mx) (rows := rows) (nm := nm);
          [exact DW4| exact (EOK _ _ EC5)| unfold blocks_ENTRY in PBL1 |- *; exact PBL1| | | | | | | | | | exact SC4| exact (proj1 ROWS)| exact (proj2 ROWS)| exact NS1
          | exact SO4| subst nm; reflexivity| unfold zlength; exact NML| | clear - N4 NL8; lia
          | exact LB1| exact LBN| exact LB3| exact BC| exact PL0| exact S2| clear - ES SNL; lia| exact ELR| unfold zlength; exact CR
          | split; [exact DB1| split; [exact DB2| exact DB3]]| exact KOK| exact KTA| exact KTZ].
        all: try (subst E1; cbn [en_id en_pname en_pname_o en_pub en_pub_o en_suites en_suites_o en_nsuites en_encoded en_encoded_o en_exts en_exts_o en_loadtime en_forretry upd_suites upd_maxname]; first [reflexivity| assumption]).
        apply find_byte_None_notin; [| clear; lia]. rewrite <- (firstn_all2 nm (n := Z.to_nat nl)) at 1 by (clear - NML; lia). apply RZ; [exact R0| clear - BP BC PL0 S2; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma de_phase4 : forall (cur rem elen publen kemhi kemlo : Z) (Lx NB : list block) (S' : storerep) (M' : libmid) (LE : list block) (w0 w1 w3 w5 : word) (j3 : list byte)
           (m' : mem) (mo' : Model) (s' : PState) (ee : Z) (E : entrep)
           (u0 u1 u2 g1 g2 g3 g4 g5 g6 g7 s8w u3 u4 u5 u6 : word),
      DWK Lx NB S' M' LE w0 w1 w3 (Z_to_bv 64 (cur + 4)) w5 (Z_to_bv 64 kemlo) (Z_to_bv 64 (rem - 4)) (Z_to_bv 64 elen) j3 m' mo' s' ->
      ENTRYobj (DREST Lx NB LE) m' ee E -> Permutation (blocks_ENTRY ee E) Lx ->
      en_suites_o E = None -> en_pname_o E = None -> en_encoded_o E = None -> en_exts E = 0 -> en_exts_o E = None -> en_loadtime E = 0 -> en_forretry E = 0 ->
      lb_bytes Lx <= ENTRY_SIZE + publen -> Z.of_nat (length Lx) <= 2 -> lb_big Lx = 0 ->
      Bb + 2 <= cur -> 0 <= publen -> 5 + publen <= elen -> 4 + elen <= rem -> cur + rem <= Bb + zlength bs -> 0 <= kemhi < 256 -> 0 <= kemlo < 256 ->
      DBUD (DREST [] NB LE) M' (ENTRY_BYTES rem) (ENTRY_CNT rem) (ENTRY_BIG rem) ->
      KOKp cur rem NB S' -> KTAp -> KTZp ->
      hs_SR H POSTc (mkCfg (MS (mkR (Z_to_bv 64 DE_R3) (Z_to_bv 64 SPc) gp (Z_to_bv 64 RATP) u0 u1 u2 sp (Z_to_bv 64 A) (Z_to_bv 64 1) g1 g2 g3 g4 g5 g6 g7
                                  (Z_to_bv 64 bt) (Z_to_bv 64 Bb) (Z_to_bv 64 (elen - 5)) (Z_to_bv 64 publen) (Z_to_bv 64 (cur + 9)) (Z_to_bv 64 ee) s8w (Z_to_bv 64 kemhi) (Z_to_bv 64 cur) (Z_to_bv 64 400) u3 u4 u5 u6)
                             F (ret_pc (Z_to_bv 64 DE_R3)) fc None m' (seg_rom rsegs)) mo').
  Proof.
    intros until u6. intros DW EO PBL SUo PNo ENo EX0 EXo LT0 FRy LB1 LBN LB3 BC PL0 EP ELR CR KH KL DB0 KOK KTA KTZ.
    pose proof KTA as KTA'. unfold dK_tailA in KTA'. pose proof KTZ as KTZ'. unfold dK_tailZ in KTZ'.
    pose proof DW as (HP1 & KREL1 & MP1 & LM1 & STP & NEW & CTX1 & EC & EB & EG & LC & LBY & LG & SO1 & SID & SPM & SND & SKI & MBO1 & DSm1 & DSb1 & BT1
                      & FR0 & FR2 & FR3 & FR4 & [errv1 ERR1] & MI1 & ST1 & AUX1 & XA1 & DNB1).
    destruct (de_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ DW) as (HSP & SPE & F3E & BP & BH & IB2 & NBL & NB11 & BLX & HB & F1 & MF & IM & GM & GE).
    destruct (DWK_HF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ DW) as (_ & ND & DISJ & BRS & D2 & D1).
    destruct RCFACTS as (SEQ & SIN & SBR & BEL0 & SUB0 & ND0 & STK0 & LO0 & MF0 & OBJ0 & DJA).
    pose proof (DREST_SUB Lx NB LE) as (SLB & S0 & SLE & SNB & STB & IB & IA & SLX & S3 & SLL).
    hcb. pose proof (word_range sp) as SPR. unfold zlength in *. assert (NB15 : nB < 1500) by (unfold OSSL_ECH_MAX_ECHCONFIG_LEN in NBR; clear - NBR; lia).
    pose proof EO as ((pad1 & pad2 & pad3 & pad4 & L1 & L2 & L3 & L4 & ECc) & EIN' & O1 & O2 & O3 & O4 & XS).
    assert (ELX : In (en_id E, ee, ENTRY_SIZE) Lx) by (eapply Permutation_in; [exact PBL| left; reflexivity]).
    assert (EIN : In (en_id E, ee, ENTRY_SIZE) (mid_errblocks M' ++ DREST Lx NB LE)) by (apply in_or_app; right; exact EIN').
    pose proof (HB _ EIN) as EEH. pose proof (BRS _ EIN) as (EEP & _ & _ & _ & OFFE). cbn [blk_addr blk_size fst snd] in EEH, EEP, OFFE. unfold ENTRY_SIZE in EEH, OFFE.
    pose proof (BLX _ ELX) as EBA. cbn [blk_addr blk_size fst snd] in EBA. unfold ENTRY_SIZE in EBA.
    destruct DB0 as (DB1 & DB2 & DB3). pose proof (dec_stack M M' STP) as DSK. pose proof (errph_nonneg (mid_err M')) as (EB0 & EN0 & EG0).
    (* [comment removed for export] *)
    rewrite SPE in FR0. unfold dframe in FR0.
    eapply (sr_evt_krel H HH); [exact KREL1| eapply de_seg4 with (E := E);
      [exact FR0| exact DSb1| clear - BC; lia| exact PL0| exact EP| exact ELR| exact CR| exact BP| exact BH| exact ECc| exact EEP
      | unfold ENTRY_SIZE; exact EEH| unfold ENTRY_SIZE; exact EBA| exact HSP| exact MI1]|].
    cbv beta. intros ms1 (a0' & a1' & s4' & s5' & s6' & m1 & w5' & ns & MU1 & WM1 & MI2 & FR1 & EC2 & NSR & CASES).
    assert (DW1 : DWK Lx NB S' M' LE w0 w1 w3 (Z_to_bv 64 (cur + 4)) w5' (Z_to_bv 64 kemlo) (Z_to_bv 64 (rem - 4)) (Z_to_bv 64 elen) j3 m1 mo' s').
    { eapply (DWK_W Lx NB S' M' LE w0 w1 w3 _ w5 _ _ _ j3 m' mo' s' m1); [exact DW| exact MU1| exact WM1| exact MI2| | | |].
      - eapply stk_transport_disjoint; [exact ST1| exact MU1| exact WM1| unfold SP'; cbn; clear - EEH CEIL LO STK0; lia].
      - apply Forall_cons; [right; left; unfold SP'; cbn; clear; lia|].
        apply Forall_cons; [| apply Forall_nil]. right; right; right; exists (en_id E, ee, ENTRY_SIZE); split; [exact ELX| cbn; unfold ENTRY_SIZE; clear; lia].
      - rewrite SPE. unfold dframe. exact FR1.
      - eapply rw_cells_transport; [exact FR3| exact MU1| exact WM1| rewrite F3E; cbn; clear - EEH HSP; lia]. }
    (* [comment removed for export] *)
    assert (EO1 : ENTRYobj (DREST Lx NB LE) m1 ee (upd_nsuites E ns)).
    { unfold ENTRYobj. cbn [en_id en_pname en_pname_o en_pub en_pub_o en_suites en_suites_o en_encoded en_encoded_o en_exts en_exts_o upd_nsuites].
      split; [exists pad1, pad2, pad3, pad4; split; [exact L1|]; split; [exact L2|]; split; [exact L3|]; split; [exact L4| exact EC2]|].
      split; [exact EIN'|]. split; [exact O1|]. split; [exact O2|]. split; [exact O3|]. split; [exact O4|]. rewrite EXo in XS |- *. exact XS. }
    assert (PBL1 : Permutation (blocks_ENTRY ee (upd_nsuites E ns)) Lx) by (unfold blocks_ENTRY in PBL |- *; cbn [en_id en_pname en_pname_o en_pub en_pub_o en_suites en_suites_o en_encoded en_encoded_o en_exts en_exts_o upd_nsuites]; exact PBL).
    clear MU1 WM1.
    destruct CASES as [->|(so & sohi & solo & SOL & SOH & SOE & S2 & EVN & ES & NSE & NS0 & -> & N9 & N10 & ->)].
    - (* [comment removed for export] *)
      eapply KTA' with (E := upd_nsuites E ns); [exact DW1| exact EO1| exact PBL1| clear; lia|].
      unfold dbud. rewrite drest_app, lb_bytes_app, length_app, lb_big_app, Nat2Z.inj_add. unfold ENTRY_BYTES, ENTRY_CNT, ENTRY_BIG, ENTRY_SIZE, ERRDEBUG_BYTES in *.
      pose proof (Z.div_pos (2 * rem) 5 ltac:(clear - ELR EP PL0; lia) ltac:(lia)) as DP1. pose proof (Z.div_pos rem 1024 ltac:(clear - ELR EP PL0; lia) ltac:(lia)) as DP2.
      clear - DB1 DB2 DB3 DP1 DP2 ELR EP PL0 LB1 LBN LB3. lia.
    - pose proof DW1 as (HPb & _ & _ & LMb & _ & _ & _ & ECb & EBb & EGb & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & DSbb & _ & FR0b & _ & FR3b & _ & [errvb ERRb] & MIb & STb & AUXb & _).
      destruct (de_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ DW1) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HBb & _ & MFb & IMb & GMb & _).
      assert (SO4 : 4 * ns <= so) by (subst ns; clear - S2; pose proof (Z.mul_div_le so 4 ltac:(lia)); lia).
      destruct (Z.eq_dec ns 0) as [NZ|NZ].
      + (* [comment removed for export] *)
        rewrite NZ. eapply (sr_evt_krel H HH); [exact KREL1| eapply cmalloc_array0_spec with (lo := lo);
          [unfold SP'; rewrite unsigned_lit by lia; exact STb| exact CEIL| unfold SP'; rewrite unsigned_lit by lia; unfold FR_CRYPTO_array, FR_CRYPTO_malloc; clear - DSK LO; lia| exact MIb| exact IMb| exact GMb]|].
        cbv beta. intros ms2 (z0 & z1 & z2 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & z3 & z4 & z5 & z6 & m2 & -> & MU2 & WM2 & MI3 & ST2).
        unfold SP' in MU2, ST2. rewrite (unsigned_lit (bv_unsigned sp + -2352)) in MU2, ST2 by lia.
        assert (DW2 : DWK Lx NB S' M' LE w0 w1 w3 (Z_to_bv 64 (cur + 4)) (Z_to_bv 64 (elen - 5 - publen - 2)) (Z_to_bv 64 kemlo) (Z_to_bv 64 (rem - 4)) (Z_to_bv 64 elen) j3 m2 mo' s').
        { eapply (DWK_W Lx NB S' M' LE); [exact DW1| exact MU2| exact WM2| exact MI3| exact ST2| | |].
          - apply Forall_cons; [left; unfold SP'; cbn; clear; lia| apply Forall_nil].
          - eapply rw_cells_transport; [exact FR0b| exact MU2| exact WM2| unfold SP'; cbn; clear; lia].
          - eapply rw_cells_transport; [exact FR3b| exact MU2| exact WM2| unfold SP', O_F3; cbn; clear; lia]. }
        pose proof DW2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FR0c & _ & _ & _ & _ & MIc & STc & _).
        apply (rw_cells_transport rsegs _ m1 m2 _ _ EC2) in MU2 as EC3; [| exact WM2| cbn; clear - EEH CEIL LO STK0; lia].
        rewrite SPE in FR0c. unfold dframe in FR0c.
        replace (cur + 9 + publen) with (Bb + (cur + 9 + publen - Bb)) by lia.
        eapply (sr_evt_krel H HH); [exact KREL1| eapply (de_seg5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Bb cur ee so _ solo 0 kemhi kemlo 0 (Z.of_nat (length bs)) (upd_nsuites E 0) None);
          [exact FR0c| rewrite <- NZ; exact EC3| exact EEP| unfold ENTRY_SIZE; exact EEH| clear; lia| clear - HCEILB; lia| exact KH| exact KL| clear; lia| clear - SOL SOH SOE; lia| exact BP
          | clear - BC CR ES ELR; lia| exact BH| exact HSP| exact MIc]|].
        cbv beta. intros ms3 (m3 & MU3 & WM3 & MI4 & EC4 & [[_ ->]|[K _]]); [| exfalso; clear - K; lia].
        assert (DW3 : DWK Lx NB S' M' LE w0 w1 w3 (Z_to_bv 64 (cur + 4)) (Z_to_bv 64 (elen - 5 - publen - 2)) (Z_to_bv 64 kemlo) (Z_to_bv 64 (rem - 4)) (Z_to_bv 64 elen) j3 m3 mo' s').
        { pose proof DW2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FR0d & _ & FR3d & _ & _ & _ & STd & _).
          eapply (DWK_W Lx NB S' M' LE); [exact DW2| exact MU3| exact WM3| exact MI4| | | |].
          - eapply stk_transport_disjoint; [exact STd| exact MU3| exact WM3| unfold SP'; cbn; clear - EEH CEIL LO STK0; lia].
          - apply Forall_cons; [| apply Forall_nil]. right; right; right; exists (en_id E, ee, ENTRY_SIZE); split; [exact ELX| cbn; unfold ENTRY_SIZE; clear; lia].
          - eapply rw_cells_transport; [exact FR0d| exact MU3| exact WM3| unfold SP'; cbn; clear - EEH CEIL LO STK0; lia].
          - eapply rw_cells_transport; [exact FR3d| exact MU3| exact WM3| unfold SP', O_F3; cbn; clear - EEH HSP; lia]. }
        eapply KTZ' with (E := upd_suites (upd_nsuites E 0) 0 None); [exact DW3| | | ].
        * unfold ENTRYobj. cbn [en_id en_pname en_pname_o en_pub en_pub_o en_suites en_suites_o en_encoded en_encoded_o en_exts en_exts_o upd_nsuites upd_suites ofield].
          split; [exists pad1, pad2, pad3, pad4; split; [exact L1|]; split; [exact L2|]; split; [exact L3|]; split; [exact L4| exact EC4]|].
          split; [exact EIN'|]. split; [exact O1|]. split; [exact O2|]. split; [reflexivity|]. split; [exact O4|]. rewrite EXo in XS |- *. exact XS.
        * unfold blocks_ENTRY in PBL |- *. rewrite SUo in PBL. cbn [en_id en_pname en_pname_o en_pub en_pub_o en_suites en_suites_o en_encoded en_encoded_o en_exts en_exts_o upd_nsuites upd_suites blocks_of] in PBL |- *. exact PBL.
        * unfold dbud. rewrite drest_app, lb_bytes_app, length_app, lb_big_app, Nat2Z.inj_add. unfold ENTRY_BYTES, ENTRY_CNT, ENTRY_BIG, ENTRY_SIZE, ERRDEBUG_BYTES in *.
          pose proof (Z.div_pos (2 * rem) 5 ltac:(clear - ELR EP PL0; lia) ltac:(lia)) as DP1. pose proof (Z.div_pos rem 1024 ltac:(clear - ELR EP PL0; lia) ltac:(lia)) as DP2.
          clear - DB1 DB2 DB3 DP1 DP2 ELR EP PL0 LB1 LBN LB3. lia.
      + (* [comment removed for export] *)
        assert (NS1 : 1 <= ns) by (clear - NZ NS0; lia).
        pose proof (cmalloc_array_spec H HH) as CA. unfold cmalloc_array_stmt in CA.
        eapply (sr_seq H HH).
        { eapply CA with (lo := lo) (B := B) (LB := mid_errblocks M' ++ DREST Lx NB LE) (s := s') (num := ns) (size := 6) (v := 1) (errv := errvb); try reflexivity.
          all: try first [exact HPb| exact KREL1| exact AUXb| exact CEIL| exact MIb| exact MFb| exact IMb| exact GMb].
          all: lazymatch goal with
               | |- 0 <= _ < _ => clear - NS0 NSE SOL SOH SOE; lia
               | |- 1 <= _ < _ => clear - NS1 NSE SOL SOH SOE; lia
               | |- lb_bytes _ + _ <= _ => rewrite lb_bytes_app, drest_app, lb_bytes_app; unfold dbud, ENTRY_BYTES, ENTRY_SIZE in *; clear - DB1 EBb EB0 EP ELR ES PL0 SO4 LB1; lia
               | |- Z.of_nat (length _) + _ <= _ => rewrite length_app, drest_app, length_app, !Nat2Z.inj_add; unfold dbud, ENTRY_CNT in *;
                                                     pose proof (Z.div_pos (2 * rem) 5 ltac:(clear - ELR EP PL0; lia) ltac:(lia)) as DP; clear - DB2 ECb DP EN0 LBN; lia
               | |- lb_big _ + big1 ?n6 <= _ => rewrite lb_big_app, drest_app, lb_big_app; assert (B1 : big1 n6 <= 1) by (unfold big1; destruct (BIGB <? n6); clear; lia); unfold dbud, ENTRY_BIG in *;
                                         pose proof (Z.div_pos rem 1024 ltac:(clear - ELR EP PL0; lia) ltac:(lia)) as DP; clear - DB3 EGb DP EG0 LB3 B1; lia
               | |- bv_unsigned _ <= B => unfold SP'; rewrite unsigned_lit by lia; clear - SPB SPR HSP HCEILB; lia
               | |- _ <= _ - CARRAY_STACK => unfold SP'; rewrite unsigned_lit by lia; clear - DSK LO; lia
               | |- rw_cells _ _ (errno_addr _) _ => rewrite errno_RATP; exact ERRb
               | |- stk _ _ _ _ => unfold SP'; rewrite unsigned_lit by lia; exact STb
               | |- ?G => idtac "CAPRE" G
               end. }
        clear CA. intros [ms2 mo2] PO. unfold cmalloc_post in PO. cbn [cfg_ms cfg_model] in PO.
        destruct PO as (z0 & z1 & z2 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & z3 & z4 & z5 & z6 & m2 & errv2 & SA & junk & pS & s2' &
                        -> & KREL2 & MP2 & MI3 & ST2 & ERR2 & AUX2 & XP2 & SABR & HP2 & SC2 & MF2 & IM2 & GM2).
        unfold SP' in ST2, XP2. rewrite (unsigned_lit (bv_unsigned sp + -2352)) in ST2, XP2 by lia. fold (SP' sp) in ST2, XP2.
        replace (ns * 6) with (6 * ns) in SABR, HP2, SC2 by lia. pose proof SABR as (SAP & _ & _ & SAH & OFFS).
        assert (XP2' : xpres (DREST [] NB LE) SPc [] m1 m2).
        { intros a Ha [HC _]. destruct (Z.eq_dec a A_mem_inited) as [->|NE]; [apply memflag_same; [exact MFb| exact MF2]|].
          apply XP2; [exact Ha|]. split.
          - destruct HC as [K|[K|(b & Hb & Hr)]]; [left; exact K| right; left; exact K| right; right; exists b; split; [apply in_or_app; right; apply S0; exact Hb| exact Hr]].
          - unfold memflag_foot. cbn [rin_ivs fst snd]. clear - NE. lia. }
        assert (DW2 : DWK ((pS, SA, 6 * ns) :: Lx) NB S' M' LE w0 w1 w3 (Z_to_bv 64 (cur + 4)) (Z_to_bv 64 (elen - 5 - publen - 2)) (Z_to_bv 64 kemlo) (Z_to_bv 64 (rem - 4)) (Z_to_bv 64 elen) j3 m2 mo2 s2').
        { eapply (DWK_X Lx ((pS, SA, 6 * ns) :: Lx)); [exact DW1| exact XP2'| | exact KREL2| eapply (mpres_trans H HH); [exact MP1| exact MP2]| exists errv2; rewrite <- errno_RATP; exact ERR2| exact MI3| exact ST2| exact AUX2].
          eapply PERM; [exact HP2|]. apply Permutation_middle. }
        assert (EO2 : ENTRYobj (DREST ((pS, SA, 6 * ns) :: Lx) NB LE) m2 ee (upd_nsuites E ns)).
        { eapply ENTRYobj_LB_mono; [| intros b Hb; right; exact Hb].
          eapply (ENTRYobj_frameX _ SPc memflag_foot m1 m2); [exact EO1| eapply xpres_weaken; [exact XP2| clear; lia| intros b Hb; apply in_or_app; right; exact Hb| intros q Hq; exact Hq]|].
          intros b Hb. pose proof (BRS b ltac:(apply in_or_app; right; apply SLX; eapply Permutation_in; [exact PBL1| exact Hb])) as (_ & _ & _ & _ & OFFb).
          unfold avoids, memflag_foot, A_mem_inited. apply Forall_cons; [cbn [fst snd]; clear - OFFb; lia| apply Forall_nil]. }
        eapply (de_phase5 cur rem elen publen kemhi kemlo so sohi solo ns ((pS, SA, 6 * ns) :: Lx) NB S' M' LE) with (E := upd_nsuites E ns);
          [exact DW2| exact EO2| apply perm_skip; exact PBL1| exact SUo| exact PNo| exact ENo| exact EX0| exact EXo| exact LT0| exact FRy| reflexivity| exact SC2| exact SAP
          | change (lb_bytes ((pS, SA, 6 * ns) :: Lx)) with (6 * ns + lb_bytes Lx); clear - LB1 NS1; lia| cbn [length]; rewrite Nat2Z.inj_succ; clear - LBN; lia
          | change (lb_big ((pS, SA, 6 * ns) :: Lx)) with (big1 (6 * ns) + lb_big Lx); clear - LB3; lia
          | exact BC| exact PL0| exact SOL| exact SOH| exact SOE| exact S2| exact EVN| exact NSE| exact NS1| exact ES| exact ELR| unfold zlength; exact CR| exact KH| exact KL
          | split; [exact DB1| split; [exact DB2| exact DB3]]| exact KOK| exact KTA| exact KTZ].
  Qed.

  (* [comment removed for export] *)
  Lemma de_phase3 : forall (cur rem elen : Z) (NB : list block) (S' : storerep) (M' : libmid) (LE : list block) (w0 w1 w3 w4 w5 w6 : word) (j3 : list byte)
           (m' : mem) (mo' : Model) (s' : PState) (ee : Z) (pe : bptr)
           (u0 u1 u2 b2 b3 b4 b5 b6 b7 s6w s8w s9w u3 u4 u5 u6 : word),
      DWK [(pe, ee, ENTRY_SIZE)] NB S' M' LE w0 w1 w3 w4 w5 w6 (Z_to_bv 64 (rem - 4)) (Z_to_bv 64 elen) j3 m' mo' s' ->
      rw_cells rsegs m' ee (entry_cells (ENT1 pe) (zeros 6) (zeros 4) (zeros 6) (zeros 4)) ->
      Bb + 2 <= cur -> 0 <= elen -> 4 + elen <= rem -> cur + rem <= Bb + zlength bs ->
      DBUD (DREST [(pe, ee, ENTRY_SIZE)] NB LE) M' (ENTRY_BYTES rem - ENTRY_SIZE) (ENTRY_CNT rem - 1) (ENTRY_BIG rem) ->
      KOKp cur rem NB S' -> KTAp -> KTZp ->
      hs_SR H POSTc (mkCfg (MS (mkR (Z_to_bv 64 DE_R1) (Z_to_bv 64 SPc) gp (Z_to_bv 64 RATP) u0 u1 u2 sp (Z_to_bv 64 A) (Z_to_bv 64 ECH_VERSION) (Z_to_bv 64 ECH_VERSION) b2 b3 b4 b5 b6 b7
                                  (Z_to_bv 64 bt) (Z_to_bv 64 Bb) (Z_to_bv 64 (rem - 4)) (Z_to_bv 64 (cur + 4)) s6w (Z_to_bv 64 ee) s8w s9w (Z_to_bv 64 cur) (Z_to_bv 64 374) u3 u4 u5 u6)
                             F (Z_to_bv 64 DE_J1) fc None m' (seg_rom rsegs)) mo').
  Proof.
    intros until u6. intros DW EC1 BC EL0 ELR CR DB KOK KTA KTZ. pose proof KTA as KTA'. unfold dK_tailA in KTA'.
    pose proof DW as (HP1 & KREL1 & MP1 & LM1 & STP & NEW & CTX1 & EC & EB & EG & LC & LBY & LG & SO1 & SID & SPM & SND & SKI & MBO1 & DSm1 & DSb1 & BT1
                      & FR0 & FR2 & FR3 & FR4 & [errv1 ERR1] & MI1 & ST1 & AUX1 & XA1 & DNB1).
    destruct (de_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ DW) as (HSP & SPE & F3E & BP & BH & IB2 & NBL & NB11 & BLX & HB & F1 & MF & IM & GM & GE).
    destruct (DWK_HF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ DW) as (_ & ND & DISJ & BRS & D2 & D1).
    destruct RCFACTS as (SEQ & SIN & SBR & BEL0 & SUB0 & ND0 & STK0 & LO0 & MF0 & OBJ0 & DJA).
    pose proof (DREST_SUB [(pe, ee, ENTRY_SIZE)] NB LE) as (SLB & S0 & SLE & SNB & STB & IB & IA & SLX & S3 & SLL).
    hcb. pose proof (word_range sp) as SPR. unfold zlength in *. assert (NB15 : nB < 1500) by (unfold OSSL_ECH_MAX_ECHCONFIG_LEN in NBR; clear - NBR; lia).
    assert (EIN : In (pe, ee, ENTRY_SIZE) (mid_errblocks M' ++ DREST [(pe, ee, ENTRY_SIZE)] NB LE)) by (apply in_or_app; right; left; reflexivity).
    pose proof (HB _ EIN) as EEH. pose proof (BRS _ EIN) as (EEP & _ & _ & _ & OFFE). cbn [blk_addr blk_size fst snd] in EEH, EEP, OFFE. unfold ENTRY_SIZE in EEH, OFFE.
    pose proof (BLX _ ltac:(left; reflexivity)) as EBA. cbn [blk_addr blk_size fst snd] in EBA. unfold ENTRY_SIZE in EBA.
    pose proof (BRS _ IB2) as (_ & _ & _ & _ & OFFB). cbn [blk_addr blk_size fst snd] in OFFB.
    destruct DB as (DB1 & DB2 & DB3). pose proof (dec_stack M M' STP) as DSK. pose proof (errph_nonneg (mid_err M')) as (EB0 & EN0 & EG0).
    assert (DB0 : DBUD (DREST [] NB LE) M' (ENTRY_BYTES rem) (ENTRY_CNT rem) (ENTRY_BIG rem)).
    { unfold dbud in DB1, DB2, DB3 |- *. rewrite drest_app in DB1, DB2, DB3. rewrite lb_bytes_app in DB1. rewrite length_app, Nat2Z.inj_add in DB2. rewrite lb_big_app in DB3.
      cbn [lb_bytes lb_big length fold_right app blk_size snd Z.of_nat Pos.of_succ_nat] in DB1, DB2, DB3.
      rewrite (big1_small ENTRY_SIZE) in DB3 by (unfold ENTRY_SIZE, BIGB; lia). clear - DB1 DB2 DB3. lia. }
    (* [comment removed for export] *)
    rewrite SPE in FR0. unfold dframe in FR0. rewrite F3E in FR3. destruct (F3_words _ _ _ FR3) as (v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & F3w).
    eapply (sr_evt_krel H HH); [exact KREL1| eapply de_seg3 with (E := ENT1 pe);
      [replace (rem + -4) with (rem - 4) by lia; exact FR0| exact F3w| exact DSb1| clear - BC; lia| exact EL0| exact ELR| exact CR| exact BP| exact BH| exact EC1| exact EEP
      | unfold ENTRY_SIZE; exact EEH| unfold ENTRY_SIZE; exact EBA| exact HSP| exact MI1]|].
    cbv beta. intros ms1 (a0' & a1' & s4' & s5' & m1 & w1' & w3' & w4' & w6' & f6 & f7 & f8 & c & MU1 & WM1 & MI2 & FR1 & F3w1 & EC2 & CRG & CASES).
    assert (DW1 : DWK [(pe, ee, ENTRY_SIZE)] NB S' M' LE w0 w1' w3' w4' w5 w6' (Z_to_bv 64 (rem - 4)) (Z_to_bv 64 elen) (cells_bytes (F3W v0 v1 v2 v3 v4 v5 f6 f7 f8 v9 v10)) m1 mo' s').
    { eapply (DWK_W [(pe, ee, ENTRY_SIZE)] NB S' M' LE w0 w1 w3 w4 w5 w6 _ _ j3 m' mo' s' m1); [exact DW| exact MU1| exact WM1| exact MI2| | | |].
      - eapply stk_transport_disjoint; [exact ST1| exact MU1| exact WM1| unfold SP'; cbn; clear - EEH CEIL LO STK0; lia].
      - apply Forall_cons; [right; left; unfold SP'; cbn; clear; lia|]. apply Forall_cons; [right; left; unfold SP'; cbn; clear; lia|].
        apply Forall_cons; [right; left; unfold SP'; cbn; clear; lia|].
        apply Forall_cons; [right; right; right; exists (pe, ee, ENTRY_SIZE); split; [left; reflexivity| cbn; unfold ENTRY_SIZE; clear; lia]|].
        apply Forall_cons; [| apply Forall_nil]. right; right; left. unfold SP', O_F3, O_SAVES. cbn. clear; lia.
      - rewrite SPE. unfold dframe. replace (rem - 4) with (rem + -4) by lia. exact FR1.
      - rewrite F3E. apply F3_cb. exact F3w1. }
    clear MU1 WM1.
    destruct CASES as [->|(publen & kemhi & kemlo & E5 & PL0 & EP & KH & KL & C8R & N4 & N5 & N6 & -> & -> & -> & -> & -> & ->)].
    - (* [comment removed for export] *)
      eapply KTA' with (E := upd_cfgid (ENT1 pe) c); [exact DW1| | cbn; apply Permutation_refl| clear; lia|].
      + unfold ENTRYobj. cbn [en_id en_pname en_pname_o en_pub en_pub_o en_suites en_suites_o en_encoded en_encoded_o en_exts en_exts_o upd_cfgid ENT1 ofield EXTS].
        split; [exists (zeros 6), (zeros 4), (zeros 6), (zeros 4); split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity| exact EC2]|].
        split; [apply in_or_app; left; left; reflexivity|]. repeat split; reflexivity.
      + unfold dbud. unfold ENTRY_BYTES, ENTRY_CNT, ENTRY_BIG, ENTRY_SIZE, ERRDEBUG_BYTES in *.
        pose proof (Z.div_pos (2 * rem) 5 ltac:(clear - ELR EL0; lia) ltac:(lia)) as DP1. pose proof (Z.div_pos rem 1024 ltac:(clear - ELR EL0; lia) ltac:(lia)) as DP2. clear - DB1 DB2 DB3 DP1 DP2 ELR EL0. lia.
    - (* [comment removed for export] *)
      pose proof DW1 as (HPb & _ & _ & LMb & _ & _ & _ & ECb & EBb & EGb & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & DSbb & _ & _ & _ & _ & _ & [errvb ERRb] & MIb & STb & AUXb & _).
      destruct (de_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ DW1) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HBb & _ & MFb & IMb & GMb & _).
      destruct (bytes_at_sub m1 Bb bs (cur + 9 - Bb) publen DSbb ltac:(clear - BC; lia) ltac:(exact PL0) ltac:(clear - BC CR EP ELR; lia)) as [BSX XBL].
      replace (Bb + (cur + 9 - Bb)) with (cur + 9) in BSX by lia.
      set (xb := firstn (Z.to_nat publen) (skipn (Z.to_nat (cur + 9 - Bb)) bs)) in *.
      destruct (entry_split_pub _ _ _ _ _ _ _ EC2) as (EP1 & EL1 & ED1 & ES1). cbn [en_publen en_pub upd_cfgid ENT1] in EL1, ED1.
      pose proof (pkmemdup_spec H HH) as PM. unfold pkmemdup_stmt in PM.
      eapply (sr_seq H HH).
      { eapply PM with (lo := lo) (B := B) (LB := mid_errblocks M' ++ DREST [(pe, ee, ENTRY_SIZE)] NB LE) (s := s') (pkt := bv_unsigned sp + -144) (cur := cur + 9) (ms := Bb)
                         (dptr := ee + 24) (lptr := ee + 16) (oldlen := 0) (v := 1) (bs := xb) (errv := errvb); unfold zlength; rewrite ?XBL; try reflexivity.
        all: try first [exact HPb| exact KREL1| exact AUXb| exact CEIL| exact MIb| exact MFb| exact IMb| exact GMb| exact BSX| exact EL1| exact ED1].
        all: lazymatch goal with
             | |- rw_cells _ _ (bv_unsigned sp + -144) _ => unfold pk_cells; replace (bv_unsigned sp + -144) with (bv_unsigned sp + -192 + 48) by lia; exact (F3_pk _ _ _ _ _ _ _ _ _ _ _ _ _ F3w1)
             | |- bv_unsigned _ <= bv_unsigned sp + -144 => unfold SP'; rewrite unsigned_lit by lia; clear; lia
             | |- cells_apart _ _ => unfold cells_apart, apart; clear; lia
             | |- outcell_ok _ _ _ _ => unfold SP'; rewrite unsigned_lit by lia;
                                        split; [eapply (rclient_range_block _ _ (pe, ee, ENTRY_SIZE)); [exact EIN| cbn; clear; lia| cbn; unfold ENTRY_SIZE; clear; lia]|];
                                        split; [unfold off_image, IMG_LO, IMG_HI; clear - OFFE; lia| clear - EEH HSP SPB; lia]
             | |- apart (bv_unsigned sp + -144) _ _ _ => unfold apart; clear - EEH HSP; lia
             | |- apart _ _ _ _ => unfold apart; clear - EBA BC CR EP ELR; lia
             | |- xclient_range _ _ _ _ _ =>
                 split; [eapply (rclient_range_block _ _ (pbin, Bb, nB)); [exact IB2| cbn; clear - BC; lia| cbn; clear - BC CR EP ELR NBL; lia]|];
                 unfold memflag_foot, A_mem_inited; apply Forall_cons; [cbn; clear - OFFB BC CR EP ELR BP NBL; lia| apply Forall_nil]
             | |- _ < 0x7ffffffc => clear - EP ELR CR NBL NB15 BC; lia
             | |- lb_bytes _ + _ <= _ => rewrite lb_bytes_app; unfold dbud, ENTRY_BYTES, ENTRY_SIZE in *; clear - DB1 EBb EB0 EP ELR EL0 PL0; lia
             | |- Z.of_nat (length _) + _ <= _ => rewrite length_app, Nat2Z.inj_add; unfold dbud, ENTRY_CNT in *;
                                                   pose proof (Z.div_pos (2 * rem) 5 ltac:(clear - ELR EL0; lia) ltac:(lia)) as DP; clear - DB2 ECb DP EN0; lia
             | |- lb_big _ + _ <= _ => rewrite lb_big_app; rewrite (big1_small publen) by (unfold BIGB; clear - EP ELR CR NBL NB15 BC; lia); unfold dbud, ENTRY_BIG in *;
                                       pose proof (Z.div_pos rem 1024 ltac:(clear - ELR EL0; lia) ltac:(lia)) as DP; clear - DB3 EGb DP EG0; lia
             | |- bv_unsigned _ <= B => unfold SP'; rewrite unsigned_lit by lia; clear - SPB SPR HSP HCEILB; lia
             | |- _ <= _ - PKMEMDUP_STACK => unfold SP'; rewrite unsigned_lit by lia; clear - DSK LO; lia
             | |- rw_cells _ _ (errno_addr _) _ => rewrite errno_RATP; exact ERRb
             | |- stk _ _ _ _ => unfold SP'; rewrite unsigned_lit by lia; exact STb
             | |- ?G => idtac "PMPRE" G
             end. }
      clear PM. intros [ms2 mo2] PO. unfold pkmemdup_post in PO. cbn [cfg_ms cfg_model] in PO.
      destruct PO as (z0 & z1 & z2 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & z3 & z4 & z5 & z6 & m2 & errv2 & s2' & LB2 & D &
                      -> & KREL2 & MP2 & MI3 & ST2 & ERR2 & AUX2 & HP2 & PK2 & DP2 & LP2 & PCASE & XP2 & [v' [MF2 VV]] & IM2 & GM2).
      unfold SP' in ST2, XP2. rewrite (unsigned_lit (bv_unsigned sp + -2352)) in ST2, XP2 by lia. fold (SP' sp) in ST2, XP2.
      unfold zlength in LP2, PCASE. rewrite XBL in LP2, PCASE.
      replace (if publen =? 0 then 0 else publen) with publen in LP2 by (destruct (Z.eqb_spec publen 0); lia).
      assert (V1 : v' = 1) by (destruct MF2 as (fb & _ & _ & VR); clear - VR VV; lia). subst v'.
      assert (XP2' : xpres (DREST [] NB LE) SPc [] m1 m2).
      { intros a Ha [HC _]. destruct (Z.eq_dec a A_mem_inited) as [->|NE]; [apply memflag_same; [exact MFb| exact MF2]|].
        apply XP2; [exact Ha|]. split.
        - destruct HC as [K|[K|(b & Hb & Hr)]]; [left; exact K| right; left; exact K| right; right; exists b; split; [apply in_or_app; right; apply S0; exact Hb| exact Hr]].
        - intros K. apply rin_ivs_app in K. destruct K as [K|K].
          + cbn [rin_ivs fst snd app] in K. eapply (lx_not_client [(pe, ee, ENTRY_SIZE)] NB LE M' s' m1 (pe, ee, ENTRY_SIZE) a []); [exact HPb| left; reflexivity| cbn; unfold ENTRY_SIZE; clear - K; lia| split; [exact HC| intros []]].
          + unfold memflag_foot in K. cbn [rin_ivs fst snd] in K. clear - K NE. lia. }
      (* [comment removed for export] *)
      eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP2) in EP1; [| eapply (rclient_range_block _ _ (pe, ee, ENTRY_SIZE)); [exact EIN| cbn; clear; lia| cbn; unfold ENTRY_SIZE; clear; lia]
                                                      | unfold memflag_foot, A_mem_inited; apply Forall_cons; [cbn; clear; lia|]; apply Forall_cons; [cbn; clear; lia|]; apply Forall_cons; [cbn; clear - OFFE; lia| apply Forall_nil]].
      eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP2) in ES1; [| eapply (rclient_range_block _ _ (pe, ee, ENTRY_SIZE)); [exact EIN| cbn; clear; lia| cbn; unfold ENTRY_SIZE; clear; lia]
                                                      | unfold memflag_foot, A_mem_inited; apply Forall_cons; [cbn; clear; lia|]; apply Forall_cons; [cbn; clear; lia|]; apply Forall_cons; [cbn; clear - OFFE; lia| apply Forall_nil]].
      (* [comment removed for export] *)
      assert (FIN : forall Lx o, hs_RHEAP H s2' (mid_errblocks M' ++ DREST Lx NB LE) m2 ->
                 Permutation ((pe, ee, ENTRY_SIZE) :: blocks_of D o) Lx -> ofield (DREST Lx NB LE) D o ->
                 lb_bytes Lx <= ENTRY_SIZE + publen -> Z.of_nat (length Lx) <= 2 -> lb_big Lx = 0 ->
                 hs_SR H POSTc (mkCfg (MS (mkR (Z_to_bv 64 DE_R3) (Z_to_bv 64 SPc) gp (Z_to_bv 64 RATP) z0 z1 z2 sp (Z_to_bv 64 A) (Z_to_bv 64 1) g1 g2 g3 g4 g5 g6 g7
                                  (Z_to_bv 64 bt) (Z_to_bv 64 Bb) (Z_to_bv 64 (elen - 5)) (Z_to_bv 64 publen) (Z_to_bv 64 (cur + 9)) (Z_to_bv 64 ee) s8w (Z_to_bv 64 kemhi) (Z_to_bv 64 cur) (Z_to_bv 64 400) z3 z4 z5 z6)
                             F (ret_pc (Z_to_bv 64 DE_R3)) fc None m2 (seg_rom rsegs)) mo2)).
      { intros Lx o HP2' PBL OFD LB1 LBN LB3.
        assert (DW2 : DWK Lx NB S' M' LE w0 w1' w3' (Z_to_bv 64 (cur + 4)) w5 (Z_to_bv 64 kemlo) (Z_to_bv 64 (rem - 4)) (Z_to_bv 64 elen)
                          (cells_bytes (F3W v0 v1 v2 v3 v4 v5 (Z_to_bv 64 (cur + 9)) (Z_to_bv 64 Bb) (Z_to_bv 64 publen) v9 v10)) m2 mo2 s2').
        { eapply (DWK_X [(pe, ee, ENTRY_SIZE)] Lx); [exact DW1| exact XP2'| exact HP2'| exact KREL2| eapply (mpres_trans H HH); [exact MP1| exact MP2]| exists errv2; rewrite <- errno_RATP; exact ERR2| exact MI3| exact ST2| exact AUX2]. }
        eapply (de_phase4 cur rem elen publen kemhi kemlo Lx NB S' M' LE) with (E := upd_pub (upd_cfgid (ENT1 pe) c) publen D o);
          [exact DW2| | | reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| exact LB1| exact LBN| exact LB3
          | exact BC| exact PL0| exact EP| exact ELR| unfold zlength; exact CR| exact KH| exact KL| exact DB0| exact KOK| exact KTA| exact KTZ].
        - unfold ENTRYobj. cbn [en_id en_pname en_pname_o en_pub en_pub_o en_suites en_suites_o en_encoded en_encoded_o en_exts en_exts_o upd_pub upd_cfgid ENT1 EXTS].
          split; [exists (zeros 6), (zeros 4), (zeros 6), (zeros 4); split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity| exact (entry_join_pub _ _ _ _ _ _ _ _ _ o EP1 LP2 DP2 ES1)]|].
          split; [apply (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (DREST_SUB Lx NB LE))))))))); eapply Permutation_in; [exact PBL| left; reflexivity]|].
          split; [reflexivity|]. split; [exact OFD|]. split; [reflexivity|]. split; reflexivity.
        - cbn [blocks_ENTRY en_id en_pname en_pname_o en_pub en_pub_o en_suites en_suites_o en_encoded en_encoded_o en_exts en_exts_o upd_pub upd_cfgid ENT1 blocks_EXTS app].
          destruct o as [[? ?]|]; cbn [blocks_of app] in PBL |- *; exact PBL. }
      destruct PCASE as [(P0 & D0 & ->)|(P1 & pD & DBR & -> & DC2)].
      + (* [comment removed for export] *)
        apply (FIN [(pe, ee, ENTRY_SIZE)] None); [exact HP2| apply Permutation_refl| exact D0| cbn; clear - PL0; lia| cbn; clear; lia| cbn; reflexivity].
      + (* [comment removed for export] *)
        pose proof DBR as (DPOS & _).
        apply (FIN [(pD, D, publen); (pe, ee, ENTRY_SIZE)] (Some (pD, publen))).
        * eapply PERM; [exact HP2|]. apply Permutation_middle.
        * apply perm_swap.
        * cbn [ofield]. split; [exact DPOS|]. split; [exact PL0|]. apply in_or_app; left; left; reflexivity.
        * cbn [lb_bytes fold_right blk_size snd]. clear - PL0. lia.
        * cbn; clear; lia.
        * cbn [lb_big fold_right blk_size snd]. rewrite (big1_small ENTRY_SIZE) by (unfold ENTRY_SIZE, BIGB; lia). rewrite (big1_small publen) by (unfold BIGB; clear - EP ELR CR NBL NB15 BC; lia). reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma de_phase2 : forall (cur rem : Z) (NB : list block) (S' : storerep) (M' : libmid) (LE : list block) (w0 w1 w3 w4 w5 w6 w9 w10 : word) (j3 : list byte)
           (m' : mem) (mo' : Model) (s' : PState) (ee : Z) (pe : bptr)
           (u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 s5w s6w s7w s8w s9w s11w u3 u4 u5 u6 : word),
      DWK [(pe, ee, ENTRY_SIZE)] NB S' M' LE w0 w1 w3 w4 w5 w6 w9 w10 j3 m' mo' s' ->
      rw_cells rsegs m' ee (entry_cells (ENT0 pe) (zeros 6) (zeros 4) (zeros 6) (zeros 4)) ->
      Bb + 2 <= cur -> 1 <= rem -> cur + rem <= Bb + zlength bs ->
      DBUD (DREST [(pe, ee, ENTRY_SIZE)] NB LE) M' (ENTRY_BYTES rem - ENTRY_SIZE) (ENTRY_CNT rem - 1) (ENTRY_BIG rem) ->
      KOKp cur rem NB S' -> KSKp cur rem NB S' -> KTAp -> KTZp ->
      hs_SR H POSTc (mkCfg (MS (mkR (Z_to_bv 64 DE_R1) (Z_to_bv 64 SPc) gp (Z_to_bv 64 RATP) u0 u1 u2 sp (Z_to_bv 64 A) (Z_to_bv 64 ee) b1 b2 b3 b4 b5 b6 b7
                                  (Z_to_bv 64 bt) (Z_to_bv 64 Bb) (Z_to_bv 64 rem) s5w s6w s7w s8w s9w (Z_to_bv 64 cur) s11w u3 u4 u5 u6)
                             F (ret_pc (Z_to_bv 64 DE_R1)) fc None m' (seg_rom rsegs)) mo').
  Proof.
    intros until u6. intros DW EC0 BC R1 CR DB KOK KSK KTA KTZ. pose proof KSK as KSK'. unfold dK_skip in KSK'. pose proof KTA as KTA'. unfold dK_tailA in KTA'.
    pose proof DW as (HP1 & KREL1 & MP1 & LM1 & STP & NEW & CTX1 & EC & EB & EG & LC & LBY & LG & SO1 & SID & SPM & SND & SKI & MBO1 & DSm1 & DSb1 & BT1
                      & FR0 & FR2 & FR3 & FR4 & [errv1 ERR1] & MI1 & ST1 & AUX1 & XA1 & DNB1).
    destruct (de_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ DW) as (HSP & SPE & F3E & BP & BH & IB2 & NBL & NB11 & BLX & HB & F1 & MF & IM & GM & GE).
    destruct (DWK_HF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ DW) as (_ & ND & DISJ & BRS & D2 & D1).
    destruct RCFACTS as (SEQ & SIN & SBR & BEL0 & SUB0 & ND0 & STK0 & LO0 & MF0 & OBJ0 & DJA).
    hcb. pose proof (word_range sp) as SPR. unfold zlength in *.
    assert (EIN : In (pe, ee, ENTRY_SIZE) (mid_errblocks M' ++ DREST [(pe, ee, ENTRY_SIZE)] NB LE)) by (apply in_or_app; right; left; reflexivity).
    pose proof (HB _ EIN) as EEH. pose proof (BRS _ EIN) as (EEP & _). cbn [blk_addr blk_size fst snd] in EEH, EEP. unfold ENTRY_SIZE in EEH.
    pose proof (BLX _ ltac:(left; reflexivity)) as EBA. cbn [blk_addr blk_size fst snd] in EBA. unfold ENTRY_SIZE in EBA.
    destruct DB as (DB1 & DB2 & DB3). pose proof (dec_stack M M' STP) as DSK. pose proof (errph_nonneg (mid_err M')) as (EB0 & EN0 & EG0).
    (* [comment removed for export] *)
    rewrite SPE in FR0. unfold dframe in FR0.
    eapply (sr_evt_krel H HH); [exact KREL1| eapply de_seg2 with (E := ENT0 pe); [exact FR0| exact DSb1| clear - BC; lia| exact R1| exact CR| exact BP| exact BH| exact EC0| exact EEP| unfold ENTRY_SIZE; exact EEH| unfold ENTRY_SIZE; exact EBA| exact HSP| exact MI1]|].
    cbv beta. intros ms1 (a0' & a1' & a2' & s4' & m1 & w9' & w10' & v & MU1 & WM1 & MI2 & FR1 & EC1 & VR & CASES).
    assert (DW1 : DWK [(pe, ee, ENTRY_SIZE)] NB S' M' LE w0 w1 w3 w4 w5 w6 w9' w10' j3 m1 mo' s').
    { eapply (DWK_W [(pe, ee, ENTRY_SIZE)] NB S' M' LE w0 w1 w3 w4 w5 w6 w9 w10 j3 m' mo' s' m1); [exact DW| exact MU1| exact WM1| exact MI2| | | |].
      - eapply stk_transport_disjoint; [exact ST1| exact MU1| exact WM1| unfold SP'; cbn; clear - EEH CEIL LO STK0; lia].
      - apply Forall_cons; [right; left; unfold SP'; cbn; clear; lia|]. apply Forall_cons; [| apply Forall_nil]. right; right; right. exists (pe, ee, ENTRY_SIZE). split; [left; reflexivity| cbn; unfold ENTRY_SIZE; clear; lia].
      - rewrite SPE. unfold dframe. exact FR1.
      - eapply rw_cells_transport; [exact FR3| exact MU1| exact WM1| rewrite F3E; cbn; clear - EEH HSP; lia]. }
    clear MU1 WM1.
    destruct CASES as [(line & LN & ->)|(elen & EL0 & ELR & -> & -> & [[NV ->]|[EV ->]])].
    - (* [comment removed for export] *)
      eapply KTA' with (E := upd_version (ENT0 pe) v); [exact DW1| | cbn; apply Permutation_refl| clear - LN; lia|].
      + unfold ENTRYobj. cbn [en_id en_pname en_pname_o en_pub en_pub_o en_suites en_suites_o en_encoded en_encoded_o en_exts en_exts_o upd_version ENT0 ofield EXTS].
        split; [exists (zeros 6), (zeros 4), (zeros 6), (zeros 4); split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity| exact EC1]|].
        split; [apply in_or_app; left; left; reflexivity|]. repeat split; reflexivity.
      + unfold dbud. unfold ENTRY_BYTES, ENTRY_CNT, ENTRY_BIG, ENTRY_SIZE, ERRDEBUG_BYTES in *.
        pose proof (Z.div_pos (2 * rem) 5 ltac:(clear - R1; lia) ltac:(lia)) as DP1. pose proof (Z.div_pos rem 1024 ltac:(clear - R1; lia) ltac:(lia)) as DP2. clear - DB1 DB2 DB3 DP1 DP2 R1. lia.
    - (* [comment removed for export] *)
      pose proof DW1 as (HPb & _ & _ & LMb & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FR3b & _ & [errvb ERRb] & MIb & STb & AUXb & _).
      destruct (de_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ DW1) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HBb & _ & MFb & IMb & GMb & GEb).
      pose proof (entryfree_spec H HH) as EF. unfold entryfree_stmt, efree_stmt_at in EF.
      eapply (sr_seq H HH).
      { eapply EF with (lo := lo) (B := B) (LB := mid_errblocks M' ++ DREST [(pe, ee, ENTRY_SIZE)] NB LE) (s := s') (p := ee) (x := upd_version (ENT0 pe) v) (errv := errvb); try reflexivity.
        all: try first [exact HPb| exact KREL1| exact AUXb| exact CEIL| exact MIb| exact IMb| exact GMb| exact GEb].
        all: lazymatch goal with
             | |- ENTRYobj _ _ _ _ =>
                 unfold ENTRYobj; cbn [en_id en_pname en_pname_o en_pub en_pub_o en_suites en_suites_o en_encoded en_encoded_o en_exts en_exts_o upd_version ENT0 ofield EXTS];
                 split; [exists (zeros 6), (zeros 4), (zeros 6), (zeros 4); split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity| exact EC1]|];
                 split; [exact EIN|]; repeat split; reflexivity
             | |- List.NoDup _ => cbn; constructor; [intros []| constructor]
             | |- bv_unsigned _ <= B => unfold SP'; rewrite unsigned_lit by lia; clear - SPB SPR HSP HCEILB; lia
             | |- stk _ _ _ _ => unfold SP'; rewrite unsigned_lit by lia; exact STb
             | |- _ <= _ - ENTRYFREE_STACK => unfold SP'; rewrite unsigned_lit by lia; clear - DSK LO; lia
             | |- rw_cells _ _ (errno_addr _) _ => rewrite errno_RATP; exact ERRb
             | |- _ mod 2 = 0 => unfold DE_R2; rewrite unsigned_lit by lia; reflexivity
             | |- ?G => idtac "EFPRE" G
             end. }
      clear EF. intros [ms2 mo2] PO. unfold efree_post in PO. cbn [cfg_ms cfg_model] in PO.
      destruct PO as (y0 & y1 & y2 & e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & y3 & y4 & y5 & y6 & m2 & s2' & LB2 &
                      -> & KREL2 & MP2 & MI3 & ST2 & ERR2 & AUX2 & PERM2 & HP2 & XP2 & IM2 & GM2 & GE2).
      unfold SP' in ST2, XP2. rewrite (unsigned_lit (bv_unsigned sp + -2352)) in ST2, XP2 by lia. fold (SP' sp) in ST2, XP2.
      cbn [blocks_ENTRY en_id en_pname en_pname_o en_pub en_pub_o en_suites en_suites_o en_encoded en_encoded_o en_exts en_exts_o upd_version ENT0 blocks_of blocks_EXTS app] in PERM2.
      assert (PL2 : Permutation LB2 (mid_errblocks M' ++ DREST [] NB LE)).
      { apply (@Permutation_cons_inv _ _ _ (pe, ee, ENTRY_SIZE)). etransitivity; [exact PERM2|]. rewrite drest_app. cbn [app]. apply Permutation_sym. apply Permutation_middle. }
      assert (DW3 : DWK [] NB S' M' LE w0 w1 w3 w4 w5 w6 (Z_to_bv 64 (rem - 4)) (Z_to_bv 64 elen) j3 m2 mo2 s2').
      { eapply (DWK_X [(pe, ee, ENTRY_SIZE)] []); [exact DW1| | eapply PERM; [exact HP2| exact PL2]| exact KREL2| eapply (mpres_trans H HH); [exact MP1| exact MP2]| exists errvb; rewrite <- errno_RATP; exact ERR2| exact MI3| exact ST2| exact AUX2].
        eapply xpres_weaken; [exact XP2| clear; lia| | auto]. intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact PL2| apply in_or_app; right; exact Hb]. }
      eapply (sr_evt_krel H HH); [exact KREL2| eapply de_skipret; exact MI3|]. cbv beta. intros ms3 ->.
      eapply KSK'; [exact DW3| exact EL0| exact ELR].
    - (* [comment removed for export] *)
      subst v. eapply de_phase3; [exact DW1| | exact BC| exact EL0| exact ELR| exact CR| split; [exact DB1| split; [exact DB2| exact DB3]]| exact KOK| exact KTA| exact KTZ].
      unfold ENT1. exact EC1.
  Qed.

  (* [comment removed for export] *)
  Lemma rp_entry : RPES.
  Proof.
    unfold rp_entry_stmt. intros cur rem NB S' M' LE w0 w1 w3 w4 w5 w6 w9 w10 j3 m' mo' s' rax u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 s5w s6w s7w s8w s9w s11w u3 u4 u5 u6 DW BC R1 CR DB KOK KSK KTA KTZ.
    pose proof DW as (HP1 & KREL1 & MP1 & LM1 & STP & NEW & CTX1 & EC & EB & EG & LC & LBY & LG & SO1 & SID & SPM & SND & SKI & MBO1 & DSm1 & DSb1 & BT1
                      & FR0 & FR2 & FR3 & FR4 & [errv1 ERR1] & MI1 & ST1 & AUX1 & XA1 & DNB1).
    destruct (de_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ DW) as (HSP & SPE & F3E & BP & BH & IB2 & NBL & NB11 & BLX & HB & F1 & MF & IM & GM & GE).
    destruct RCFACTS as (SEQ & SIN & SBR & BEL0 & SUB0 & ND0 & STK0 & LO0 & MF0 & OBJ0 & DJA).
    hcb. pose proof (word_range sp) as SPR. unfold zlength in *.
    (* [comment removed for export] *)
    rewrite F3E in FR3. change 88%nat with (8 * 11)%nat in FR3. destruct (CB_words 11 _ _ _ _ FR3) as (ws & LW & F3w). rewrite app_nil_r in F3w.
    destruct ws as [|v0 [|v1 [|v2 [|v3 [|v4 [|v5 [|v6 [|v7 [|v8 [|v9 [|v10 [|? ?]]]]]]]]]]]]; try (cbn in LW; discriminate LW). cbn [map] in F3w.
    (* [comment removed for export] *)
    rewrite SPE in FR0. unfold dframe in FR0.
    eapply (sr_evt_krel H HH); [exact KREL1| eapply de_seg1; [exact FR0| exact F3w| clear - HSP HCEILB; lia| exact MI1]|].
    cbv beta. intros ms1 (m1 & MU1 & WM1 & MI2 & F3w1 & ->).
    assert (DW1 : DWK [] NB S' M' LE w0 w1 w3 w4 w5 w6 w9 w10 (cells_bytes (F3W v0 v1 v2 v3 v4 v5 v6 v7 v8 (Z_to_bv 64 0) v10)) m1 mo' s').
    { eapply (DWK_W [] NB S' M' LE w0 w1 w3 w4 w5 w6 w9 w10 j3 m' mo' s' m1); [exact DW| exact MU1| exact WM1| exact MI2| | | |].
      - eapply stk_transport_disjoint; [exact ST1| exact MU1| exact WM1| unfold SP'; cbn; clear; lia].
      - apply Forall_cons; [| apply Forall_nil]. right; right; left. unfold SP', O_F3, O_SAVES. cbn. clear; lia.
      - rewrite SPE. unfold dframe. eapply rw_cells_transport; [exact FR0| exact MU1| exact WM1| cbn; clear; lia].
      - rewrite F3E. apply F3_cb. exact F3w1. }
    clear MU1 WM1 F3w1 F3w FR0.
    (* [comment removed for export] *)
    pose proof DW1 as (HPa & _ & _ & LMa & _ & _ & _ & ECa & EBa & EGa & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & [errva ERRa] & MIa & STa & AUXa & _).
    destruct (de_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ DW1) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HBa & _ & MFa & IMa & GMa & _).
    destruct DB as (DB1 & DB2 & DB3). pose proof (dec_stack M M' STP) as DSK. pose proof (errph_nonneg (mid_err M')) as (EB0 & EN0 & EG0).
    pose proof (czalloc_spec H HH) as CZ. unfold czalloc_stmt, czalloc_stmt_gen in CZ.
    eapply (sr_seq H HH).
    { eapply CZ with (lo := lo) (B := B) (LB := mid_errblocks M' ++ DREST [] NB LE) (s := s') (num := ENTRY_SIZE) (size := 1) (v := 1); try reflexivity.
      all: try first [exact HPa| exact KREL1| exact AUXa| exact STa| exact CEIL| exact MIa| exact MFa| exact IMa| exact GMa].
      all: lazymatch goal with
           | |- 1 <= ENTRY_SIZE * 1 < _ => unfold ENTRY_SIZE; lia
           | |- lb_bytes _ + _ <= _ => rewrite lb_bytes_app; unfold ENTRY_BYTES, ENTRY_SIZE, ERRSTR_BYTES in *; clear - DB1 EBa R1 EB0; lia
           | |- Z.of_nat (length _) + _ <= _ => rewrite length_app, Nat2Z.inj_add; unfold ENTRY_CNT, ERRSTR_CNT in *; pose proof (Z.div_pos (2 * rem) 5 ltac:(clear - R1; lia) ltac:(lia)) as DP; clear - DB2 ECa DP EN0; lia
           | |- lb_big _ + _ <= _ => rewrite lb_big_app; rewrite (big1_small (ENTRY_SIZE * 1)) by (unfold ENTRY_SIZE, BIGB; lia); unfold ENTRY_BIG in *; pose proof (Z.div_pos rem 1024 ltac:(clear - R1; lia) ltac:(lia)) as DP; clear - DB3 EGa DP EG0; lia
           | |- bv_unsigned _ <= B => unfold SP'; rewrite unsigned_lit by lia; clear - SPB SPR HSP HCEILB; lia
           | |- _ <= _ - CZALLOC_STACK => unfold SP'; rewrite unsigned_lit by lia; clear - DSK LO; lia
           | |- rw_cells _ _ (errno_addr _) _ => rewrite errno_RATP; exact ERRa
           | |- stk _ _ _ _ => rewrite unsigned_lit by lia; exact STa
           | |- ?G => idtac "CZPRE" G
           end. }
    clear CZ. intros [ms2 mo2] PO. unfold czalloc_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (z0 & z1 & z2 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & z3 & z4 & z5 & z6 & m2 & errv2 & ee & pe & s2' &
                    -> & KREL2 & MP2 & MI3 & ST2 & ERR2 & AUX2 & XP2 & EBR & HP2 & EC0 & MF2 & IM2 & GM2).
    unfold SP' in ST2, XP2. rewrite (unsigned_lit (bv_unsigned sp + -2352)) in ST2, XP2 by lia. fold (SP' sp) in ST2, XP2.
    replace (ENTRY_SIZE * 1) with ENTRY_SIZE in EBR, HP2, EC0 by lia.
    assert (DW2 : DWK [(pe, ee, ENTRY_SIZE)] NB S' M' LE w0 w1 w3 w4 w5 w6 w9 w10 (cells_bytes (F3W v0 v1 v2 v3 v4 v5 v6 v7 v8 (Z_to_bv 64 0) v10)) m2 mo2 s2').
    { eapply (DWK_X [] [(pe, ee, ENTRY_SIZE)]); [exact DW1| | | exact KREL2| eapply (mpres_trans H HH); [exact MP1| exact MP2]| exists errv2; rewrite <- errno_RATP; exact ERR2| exact MI3| exact ST2| exact AUX2].
      - change (@nil (Z * Z)) with (@nil (Z * Z) ++ []). eapply xpres_drop_memflag; [exact MFa| exact MF2|]. cbn [app]. eapply xpres_weaken; [exact XP2| clear; lia| intros b Hb; apply in_or_app; right; exact Hb| auto].
      - eapply PERM; [exact HP2|]. rewrite drest_app. apply Permutation_middle. }
    eapply de_phase2; [exact DW2| | exact BC| exact R1| exact CR| | exact KOK| exact KSK| exact KTA| exact KTZ].
    - eapply rw_cells_recut; [exact EC0| vm_compute; repeat split; reflexivity| rewrite ENT0_cells; reflexivity].
    - unfold dbud. rewrite drest_app, lb_bytes_app, length_app, lb_big_app, Nat2Z.inj_add. cbn [lb_bytes lb_big length fold_right app blk_size snd Z.of_nat Pos.of_succ_nat].
      rewrite (big1_small ENTRY_SIZE) by (unfold ENTRY_SIZE, BIGB; lia). clear - DB1 DB2 DB3. unfold ENTRY_SIZE in *. lia.
  Qed.
End RC.
