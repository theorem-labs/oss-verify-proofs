(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX Frame.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import RSegs RMalloc_iface_stmt HeapSR_iface ECH_Img ECH_Xpres ECH_SR ECH_Kit ECH_Kit2 ECH_KitH ECH_Rep
     ECH_LibState ECH_LibStateMF ECH_LibFrame ECH_Rostr ECH_C1_stmt ECH_C1_malloc ECH_C1_free ECH_C3_stmt ECH_C4_stmt ECH_C4_frame ECH_C4_frame2 ECH_C4_raise ECH_C4
     ECH_C5_stmt ECH_C5_small ECH_C5_new ECH_C5_push ECH_C6_stmt ECH_C7_stmt ECH_C9_stmt ECH_C10_stmt ECH_C13_stmt ECH_C13_small ECH_C13_ext ECH_C13_entry ECH_C13_store
     ECH_C14_stmt ECH_KitSeg ECH_LibMid F_time ECH_C14_bio2buf ECH_C14_ladder ECH_C14_ladloop ECH_C14_tail ECH_C14_b2b ECH_C14_fcc ECH_C14_dec ECH_C14_decexts
     ECH_C14_flat_seg.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc Prog.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
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
  Hypothesis PAYS : 1 <= mb_len R -> forall pD, In (pD, mb_buf R, mb_len R) LB -> pD <> es_id S.

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

  (* [comment removed for export] *)
  Hypothesis TIME : time_sr_stmt H.
  Let EGS : egs_stmt H := proj1 (proj2 (C4_spec H HX CERTO3)).

  (* [comment removed for export] *)
  Local Notation DWK := (dwk H ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m mo LIB LB M st mb lo B S R ds p A nA pbin Bb nB bs R' jt TB BT).
  Local Notation DWKG := (dwkG H ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m mo LIB LB M st mb lo B S R ds p A nA pbin Bb nB bs R' jt TB BT).
  Local Notation DREST := (drest LB p A nA pbin Bb nB TB).
  Local Notation DBUD := (dbud H).
  Local Notation DK_OK := (dK_ok H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo s LIB LB M st mb lo B S R ds p A nA pbin Bb nB bs R' jt bt TB BT).
  Local Notation DK_SKIP := (dK_skip H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo s LIB LB M st mb lo B S R ds p A nA pbin Bb nB bs R' jt bt TB BT).
  Local Notation DK_TA := (dK_tailA H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo s LIB LB M st mb lo B S R ds p A nA pbin Bb nB bs R' jt bt TB BT).
  Local Notation DK_TZ := (dK_tailZ H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo s LIB LB M st mb lo B S R ds p A nA pbin Bb nB bs R' jt bt TB BT).
  Local Notation RPE_STMT := (rp_entry_stmt H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo s LIB LB M st mb lo B S R ds p A nA pbin Bb nB bs R' jt bt TB BT).
  Local Notation RCFACTS := (rc_facts H HX ra sp tp a0 a1 m mo s LIB LB M x st mb lo B S R ds errv A0 A1 SO SE SEO STL MBO MP0 MN0 MBB MBS DS DSL PAYL NDsm LM SUBL CTX MF1 DJ6
                              HP KREL BUD BUDC BUDG AUX SPB BHI SPA ST CEIL LO ERR MI TP RAE).
  Local Notation DWKX := (dwk_x H HX ra sp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m mo s LIB LB M x st mb lo B S R ds errv A0 A1 SO SE SEO STL MBO MP0 MN0 MBB MBS DS DSL PAYL NDsm LM SUBL CTX MF1 DJ6
                              HP KREL BUD BUDC BUDG AUX SPB BHI SPA ST CEIL LO ERR MI TP RAE p A nA pbin Bb nB bs R' jt bt TB BT NAR NBR MST POS BTR BT_frame).
  Local Notation DWKGX := (dwkG_x H HX ra sp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m mo s LIB LB M x st mb lo B S R ds errv A0 A1 SO SE SEO STL MBO MP0 MN0 MBB MBS DS DSL PAYL NDsm LM SUBL CTX MF1 DJ6
                              HP KREL BUD BUDC BUDG AUX SPB BHI SPA ST CEIL LO ERR MI TP RAE p A nA pbin Bb nB bs R' jt bt TB BT NAR NBR MST POS BTR BT_frame).
  Local Notation DWKF := (dwk_heap_facts H HX ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m mo LIB LB M st mb lo B S R ds p A nA pbin Bb nB bs R' jt TB BT).
  Local Notation DWKGF := (dwkG_heap_facts H HX ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m mo LIB LB M st mb lo B S R ds p A nA pbin Bb nB bs R' jt TB BT).
  Local Notation DWKW := (dwk_w H HX ra sp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m mo s LIB LB M x st mb lo B S R ds errv A0 A1 SO SE SEO STL MBO MP0 MN0 MBB MBS DS DSL PAYL NDsm LM SUBL CTX MF1 DJ6
                              HP KREL BUD BUDC BUDG AUX SPB BHI SPA ST CEIL LO ERR MI TP RAE p A nA pbin Bb nB bs R' jt bt TB BT NAR NBR MST POS BTR BT_frame).
  Local Notation DWKGW := (dwkG_w H HX ra sp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m mo s LIB LB M x st mb lo B S R ds errv A0 A1 SO SE SEO STL MBO MP0 MN0 MBB MBS DS DSL PAYL NDsm LM SUBL CTX MF1 DJ6
                              HP KREL BUD BUDC BUDG AUX SPB BHI SPA ST CEIL LO ERR MI TP RAE p A nA pbin Bb nB bs R' jt bt TB BT NAR NBR MST POS BTR BT_frame).
  Local Notation DWKL := (dwk_lib H HX ra sp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m mo s LIB LB M x st mb lo B S R ds errv A0 A1 SO SE SEO STL MBO MP0 MN0 MBB MBS DS DSL PAYL NDsm LM SUBL CTX MF1 DJ6
                              HP KREL BUD BUDC BUDG AUX SPB BHI SPA ST CEIL LO ERR MI TP RAE p A nA pbin Bb nB bs R' jt bt TB BT NAR NBR MST POS BTR BT_frame).
  Local Notation DWKGL := (dwkG_libX H HX ra sp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m mo s LIB LB M x st mb lo B S R ds errv A0 A1 SO SE SEO STL MBO MP0 MN0 MBB MBS DS DSL PAYL NDsm LM SUBL CTX MF1 DJ6
                              HP KREL BUD BUDC BUDG AUX SPB BHI SPA ST CEIL LO ERR MI TP RAE p A nA pbin Bb nB bs R' jt bt TB BT NAR NBR MST POS BTR BT_frame).
  Local Notation DWKES := (dwk_es H ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m mo LIB LB M x st mb lo B S R ds CTX p A nA pbin Bb nB bs R' jt TB BT).
  Local Notation DWKGES := (dwkG_es H ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m mo LIB LB M x st mb lo B S R ds CTX p A nA pbin Bb nB bs R' jt TB BT).
  Local Notation DRESTSUB := (drest_sub LIB LB SUBL p A nA pbin Bb nB TB).
  Local Notation DRESTIDS := (drest_ids LB p A nA pbin Bb nB TB).
  Local Notation MBLB := (mb_blocks_LB' m LB mb R MBO R' MST).
  Local Ltac img_static := unfold RERRNO, A_malloc_impl, A_got_CRYPTO_malloc, A_mem_buf_method, O_METH_BREAD, A_mem_inited; cbn; lia.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.
  (* [comment removed for export] *)
  Local Ltac lbnorm := unfold drest; rewrite ?app_nil_l;
                     repeat first [rewrite lb_bytes_app| rewrite lb_bytes_cons| rewrite lb_big_app| rewrite lb_big_cons| rewrite length_app| progress (cbn [length blk_size snd app])];
                     rewrite ?Nat2Z.inj_add, ?Nat2Z.inj_succ.

  (* [comment removed for export] *)
  Definition SKB (S' : storerep) : list block := match es_entries_o S' with None => [] | Some (K, _) => blocks_SK (es_entries S') K end.
  Definition EBS (S' : storerep) : list block :=
    match es_entries_o S' with None => [] | Some (K, es) => concat (map (fun pe => blocks_ENTRY (fst pe) (snd pe)) (combine (sk_elems K) es)) end.
  Definition nent (S' : storerep) : Z := match es_entries_o S' with Some (_, es) => Z.of_nat (length es) | None => 0 end.
  Lemma blocks_STORE_split : forall S', blocks_STORE st S' = (es_id S', st, STORE_SIZE) :: SKB S' ++ EBS S'.
  Proof. clear. intros [e [[K es]|] i]; reflexivity. Qed.
  (* [comment removed for export] *)
  Definition dledger (S' : storerep) (c : Z) : Prop :=
       5 * Z.of_nat (length (EBS S')) <= 2 * c /\ lb_bytes (EBS S') <= 13 * c + 512 * nent S' /\ lb_big (EBS S') <= c / 600 /\ 23 * nent S' <= c /\ 0 <= c.
  (* [comment removed for export] *)
  Definition DLOOP_BYTES : Z := 124000.  Definition DLOOP_CNT : Z := 700.  Definition DLOOP_BIG : Z := 5.

  (* [comment removed for export] *)
  Definition rp_errl_stmt : Prop :=
    forall (NB : list block) (S' : storerep) (M' : libmid) (LE : list block) (fr : list cell) (j3 : list byte)
           (m' : mem) (mo' : Model) (s' : PState) (rv : Z)
           (rax u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 s5w s6w s7w s8w s9w s10w s11w u3 u4 u5 u6 : word),
      DWKG [] NB S' M' LE fr j3 m' mo' s' -> cells_size fr = 112%nat -> (rv = 0 \/ rv = 1) ->
      hs_SR H POSTc (mkCfg (MS (mkR rax (Z_to_bv 64 SPc) gp (Z_to_bv 64 RATP) u0 u1 u2 sp (Z_to_bv 64 A) b0 b1 b2 b3 b4 b5 b6 b7
                                  (Z_to_bv 64 bt) (Z_to_bv 64 Bb) (Z_to_bv 64 rv) s5w s6w s7w s8w s9w s10w s11w u3 u4 u5 u6)
                             F (Z_to_bv 64 RP_ERRL) fc None m' (seg_rom rsegs)) mo').
  Hypothesis RPE : RPE_STMT.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition btfree_stmt : Prop :=
    forall (NB : list block) (S' : storerep) (M' : libmid) (LE : list block) (fr : list cell) (j3 : list byte) (m1 : mem) (mo1 : Model) (s1' : PState)
           (ra0 : Z) (u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 s2w s3w s4w s5w s6w s7w s8w s9w s10w s11w u3 u4 u5 u6 : word) (Q : config -> Prop),
      DWKG [] NB S' M' LE fr j3 m1 mo1 s1' -> 0 <= ra0 < 2^64 -> ra0 mod 2 = 0 ->
      (forall (m2 : mem) (mo2 : Model) (s2' : PState) (errv2 : word) (v0 v1 v2 c0 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 : word),
         hs_RHEAP H s2' (mid_errblocks M' ++ NB ++ (pbin, Bb, nB) :: (p, A, nA) :: LE ++ LB) m2 -> hs_KREL H s2' mo2 -> hs_MPRES H mo mo2 ->
         mem_inv rsegs m2 -> stk rsegs m2 lo SPc -> rw_cells rsegs m2 RERRNO [C4 errv2] -> hs_rauxv_ok H m2 B ->
         xpres (NB ++ (pbin, Bb, nB) :: (p, A, nA) :: LE ++ LB) SPc [] m1 m2 ->
         hs_SR H Q (mkCfg (MS (mkR (Z_to_bv 64 ra0) (Z_to_bv 64 SPc) gp (Z_to_bv 64 RATP) v0 v1 v2 sp (Z_to_bv 64 A) c0 c1 c2 c3 c4 c5 c6 c7
                               s2w s3w s4w s5w s6w s7w s8w s9w s10w s11w v3 v4 v5 v6) F (ret_pc (Z_to_bv 64 ra0)) fc None m2 (seg_rom rsegs)) mo2)) ->
      hs_SR H Q (mkCfg (MS (mkR (Z_to_bv 64 ra0) (Z_to_bv 64 SPc) gp (Z_to_bv 64 RATP) u0 u1 u2 sp (Z_to_bv 64 A) (Z_to_bv 64 bt) b1 b2 b3 b4 b5 b6 b7
                            s2w s3w s4w s5w s6w s7w s8w s9w s10w s11w u3 u4 u5 u6) F (Z_to_bv 64 P_BIO_free_all) fc None m1 (seg_rom rsegs)) mo1).
  Hypothesis BTFREE : btfree_stmt.

  (* [comment removed for export] *)
  Lemma rp_post : forall NB S' M' LE m' mo' (s' : PState) (rv : Z) (u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 errv' : word),
    (rv = 0 \/ rv = 1) -> hs_KREL H s' mo' -> hs_MPRES H mo mo' -> mem_inv rsegs m' -> stk rsegs m' lo (bv_unsigned sp) ->
    rw_cells rsegs m' RERRNO [C4 errv'] -> hs_rauxv_ok H m' B ->
    hs_RHEAP H s' (mid_errblocks M' ++ NB ++ LE ++ LB) m' -> LIBMID (LE ++ LIB) m' M' -> mid_step M M' -> mid_newlib_ok M M' LE -> mid_ctx M' = mid_ctx M ->
    STOREobj (NB ++ LE ++ LB) m' st S' -> es_id S' = es_id S -> Permutation (blocks_STORE st S') ((es_id S, st, STORE_SIZE) :: NB) -> dnb NB ->
    Z.of_nat (length (mid_errblocks M')) <= ERRSTR_CNT -> lb_bytes (mid_errblocks M') <= ERRSTR_BYTES -> lb_big (mid_errblocks M') = 0 ->
    List.NoDup (map blk_id (blocks_STORE st S')) ->
    MEMBIO LB m' mb R' -> bytes_at rsegs m' (mb_buf R) ds -> xpres LB (bv_unsigned sp) XFc m m' ->
    hs_SR H POSTc (mkCfg (MS (mkR ra sp gp (Z_to_bv 64 RATP) u0 u1 u2 s0 s1 (Z_to_bv 64 rv) b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
                              F (ret_pc ra) fc None m' (seg_rom rsegs)) mo').
  Proof using TP MST HH.
    intros until errv'. intros RV KREL' MP' MI' ST' ERR' AUX' HP' LM' STEP' NEW' CTX' SO' SID' SPM' (N1 & N2 & N3) EC' EB' EG' ND' MBO' DS' XP'.
    apply (sr_done H HH). unfold POST, readcfg_post. cbn [cfg_ms cfg_model]. rewrite TP, errno_RATP.
    exists u0, u1, u2, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m', errv', s', rv, M', S', R', LE, NB.
    cbv zeta.
    split; [reflexivity|]. split; [exact RV|]. split; [exact KREL'|]. split; [exact MP'|].
    split; [exact MI'|]. split; [exact ST'|]. split; [exact ERR'|]. split; [exact AUX'|]. split; [exact HP'|].
    split; [exact LM'|]. split; [exact STEP'|]. split; [exact NEW'|]. split; [exact CTX'|].
    split; [exact SO'|]. split; [exact SID'|]. split; [exact SPM'|].
    split; [exact N1|]. split; [exact N2|]. split; [exact N3|].
    split; [exact EC'|]. split; [exact EB'|]. split; [exact EG'|]. split; [exact ND'|].
    split; [eapply MEMBIO_mono; [exact MBO'| intros b Hb; apply in_or_app; right; apply in_or_app; right; exact Hb]|].
    split; [exact (mb_static_blocks mb R R' MST)|]. split; [exact DS'| exact XP'].
  Qed.

  (* [comment removed for export] *)
  Lemma ERRL : rp_errl_stmt.
  Proof using A0 A1 SO SE SEO STL MBO MP0 MN0 MBB MBS DS DSL PAYL NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC BUDG AUX SPB BHI SPA ST CEIL LO ERR MI TP RAE HH HX NAR NBR MST POS BTR BT_frame PERM BTFREE.
    unfold rp_errl_stmt. intros NB S' M' LE fr j3 m1 mo1 s1' rv rax u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 s5w s6w s7w s8w s9w s10w s11w u3 u4 u5 u6 DW FSZ RV.
    pose proof DW as (HP1 & KREL1 & MP1 & LM1 & STP1 & NEW1 & CTX1 & EC1 & EB1 & EG1 & _ & _ & _ & SO1 & SID1 & SPM1 & SND1 & _ & MBO1 & DSm1 & _ & _
                      & FR0 & FR2 & FR3 & FR4 & _ & MI1 & ST1 & _ & XA1 & DNB1).
    destruct RCFACTS as (SEQ & SIN & SBR & BEL0 & SUB0 & ND0 & STK0 & LO0 & MF0 & OBJ0 & DJA). hcb. pose proof (word_range sp) as SPR.
    pose proof (dec_stack M M' STP1) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & STKC & K11).
    set (Lr := NB ++ LE ++ LB).
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL1| eapply rp_errl1; exact MI1|]. intros ms2 ->.
    eapply (BTFREE NB S' M' LE fr j3 m1 mo1 s1' RP_ERRL_R1); [exact DW| unfold RP_ERRL_R1; clear; lia| reflexivity|].
    intros m2 mo2 s2' errv2 v0 v1 v2 c0 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 HP2 KREL2 MP2 MI2 ST2 ERR2 AUX2 XP2.
    assert (SUB2 : forall b, In b (LE ++ LIB) -> In b (NB ++ (pbin, Bb, nB) :: (p, A, nA) :: LE ++ LB)).
    { intros b Hb. apply in_or_app; right. right; right. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; apply in_or_app; [left; exact Hb| right; apply SUBL; exact Hb]. }
    pose proof (LIBMID_xpres0 _ _ _ _ _ _ LM1 XP2 SUB2) as LM2. pose proof LM2 as (IM2 & _ & _ & _ & _ & _ & _ & _ & GM2 & _).
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL2| eapply rp_errl2; exact MI2|]. intros ms3 ->.
    assert (HP2' : hs_RHEAP H s2' ((pbin, Bb, nB) :: mid_errblocks M' ++ NB ++ (p, A, nA) :: LE ++ LB) m2).
    { eapply PERM; [exact HP2|]. rewrite !(app_assoc (mid_errblocks M') NB). apply Permutation_sym. apply Permutation_middle. }
    pose proof (HH_RHEAP_blocks_nodup H HH _ _ _ HP2') as ND2. cbn [map] in ND2. apply List.NoDup_cons_iff in ND2. destruct ND2 as [NIB _].
    pose proof (cfree_spec H HH) as CF. unfold cfree_stmt in CF.
    eapply (sr_seq H HH).
    { eapply CF with (lo := lo) (B := B) (s := s2') (p := pbin) (A := Bb) (n := nB) (errv := errv2); [reflexivity| exact HP2'| exact KREL2| left; reflexivity| exact AUX2| | | exact CEIL| | | exact MI2| reflexivity| exact IM2| exact GM2].
      - unfold SP'. rewrite unsigned_lit by (clear - SPR LO STK0 LO0; lia). clear - SPB; lia.
      - unfold SP'. rewrite unsigned_lit by (clear - SPR LO STK0 LO0; lia). exact ST2.
      - unfold SP'. rewrite unsigned_lit by (clear - SPR LO STK0 LO0; lia). clear - LO STKC. lia.
      - rewrite errno_RATP. exact ERR2. }
    clear CF. intros [ms4 mo4] PO. unfold cfree_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (w0' & w1' & w2' & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3' & w4' & w5' & w6' & m4 & s4' & -> & KREL4 & MP4 & MI4 & ST4 & ERR4 & AUX4 & XP4 & HP4 & IM4 & GM4).
    rewrite (proj1 (HH_lb_remove H HH)) in XP4, HP4 by exact NIB.
    unfold SP' in ST4, XP4. rewrite (unsigned_lit (bv_unsigned sp + -2352)) in ST4, XP4 by (clear - SPR LO STK0 LO0; lia). rewrite errno_RATP in ERR4. fold (SP' sp) in ST4, XP4.
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL4| eapply rp_errl3; exact MI4|]. intros ms5 ->.
    assert (HP4' : hs_RHEAP H s4' ((p, A, nA) :: mid_errblocks M' ++ NB ++ LE ++ LB) m4).
    { eapply PERM; [exact HP4|]. rewrite !(app_assoc (mid_errblocks M') NB). apply Permutation_sym. apply Permutation_middle. }
    pose proof (HH_RHEAP_blocks_nodup H HH _ _ _ HP4') as ND4. cbn [map] in ND4. apply List.NoDup_cons_iff in ND4. destruct ND4 as [NIA _].
    pose proof (cfree_spec H HH) as CF. unfold cfree_stmt in CF.
    eapply (sr_seq H HH).
    { eapply CF with (lo := lo) (B := B) (s := s4') (p := p) (A := A) (n := nA) (errv := errv2); [reflexivity| exact HP4'| exact KREL4| left; reflexivity| exact AUX4| | | exact CEIL| | | exact MI4| reflexivity| exact IM4| exact GM4].
      - unfold SP'. rewrite unsigned_lit by (clear - SPR LO STK0 LO0; lia). clear - SPB; lia.
      - unfold SP'. rewrite unsigned_lit by (clear - SPR LO STK0 LO0; lia). exact ST4.
      - unfold SP'. rewrite unsigned_lit by (clear - SPR LO STK0 LO0; lia). clear - LO STKC. lia.
      - rewrite errno_RATP. exact ERR4. }
    clear CF. intros [ms6 mo6] PO. unfold cfree_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (x0 & x1 & x2 & e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & x3 & x4 & x5 & x6 & m6 & s6' & -> & KREL6 & MP6 & MI6 & ST6 & ERR6 & AUX6 & XP6 & HP6 & IM6 & GM6).
    rewrite (proj1 (HH_lb_remove H HH)) in XP6, HP6 by exact NIA.
    unfold SP' in ST6, XP6. rewrite (unsigned_lit (bv_unsigned sp + -2352)) in ST6, XP6 by (clear - SPR LO STK0 LO0; lia). rewrite errno_RATP in ERR6. fold (SP' sp) in ST6, XP6.
    (* [comment removed for export] *)
    assert (XP16 : xpres Lr SPc [] m1 m6).
    { eapply xpres_trans; [eapply xpres_weaken; [exact XP2| clear; lia| | intros q Hq; exact Hq]|].
      { intros b Hb. subst Lr. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; apply in_or_app; [left; exact Hb| right; right; right; exact Hb]. }
      eapply xpres_trans; [eapply xpres_weaken; [exact XP4| clear; lia| | intros q Hq; exact Hq]|].
      { intros b Hb. subst Lr. apply in_or_app; right. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; apply in_or_app; [left; exact Hb| right; right; exact Hb]. }
      eapply xpres_weaken; [exact XP6| clear; lia| intros b Hb; apply in_or_app; right; exact Hb| intros q Hq; exact Hq]. }
    assert (FRall : rw_cells rsegs m6 SPc (fr ++ [CB 2048 jt] ++ [CB 88 j3] ++ SAVESc)).
    { pose proof FR0 as [[WF0 _] _].
      assert (SZ0 : Z.of_nat (cells_size fr) = 112) by (rewrite FSZ; reflexivity).
      apply (proj2 (rw_cells_app rsegs m6 SPc fr _)). split; [eapply xpres_rw_cells'; [exact XP16| exact FR0| left; clear; lia| apply Forall_nil]|].
      rewrite SZ0. apply (proj2 (rw_cells_app rsegs m6 _ [CB 2048 jt] _)). split; [eapply xpres_rw_cells'; [exact XP16| unfold RBP, SP' in FR2 |- *; replace (bv_unsigned sp + -2352 + 112) with (bv_unsigned sp + -2240) by (clear; lia); exact FR2| left; clear; lia| apply Forall_nil]|].
      cbn [cells_size csize Nat.add]. apply (proj2 (rw_cells_app rsegs m6 _ [CB 88 j3] _)). split; [eapply xpres_rw_cells'; [exact XP16| unfold O_F3 in FR3; replace (SPc + 112 + Z.of_nat 2048) with (SPc + 2160) by (clear; lia); exact FR3| left; clear; lia| apply Forall_nil]|].
      cbn [cells_size csize Nat.add]. eapply xpres_rw_cells'; [exact XP16| unfold O_SAVES in FR4; replace (SPc + 112 + Z.of_nat 2048 + Z.of_nat 88) with (SPc + 2248) by (clear; lia); exact FR4| left; clear; lia| apply Forall_nil]. }
    pose proof (stk_release rsegs m6 lo _ _ ST6 FRall ltac:(unfold SP'; clear - LO STK0; lia)) as STf.
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL6| unfold SP'; eapply rp_errl4; [clear - SPR LO STK0 LO0; lia| | exact MI6]|].
    { unfold SAVES in FR4. eapply xpres_rw_cells'; [exact XP16| unfold O_SAVES, SP' in FR4; replace (bv_unsigned sp + -2352 + 2248) with (bv_unsigned sp + -104) in FR4 by (clear; lia); exact FR4| left; unfold SP'; clear; lia| apply Forall_nil]. }
    intros ms7 ->.
    assert (STf' : stk rsegs m6 lo (bv_unsigned sp)).
    { revert STf. rewrite !cells_size_app. unfold SAVES, rp_saves. cbn [cells_size csize Nat.add length]. rewrite FSZ. unfold SP'.
      match goal with |- stk _ _ _ ?a -> _ => replace a with (bv_unsigned sp) by (clear; lia) end. intros K0; exact K0. }
    assert (SUBr : forall b, In b LB -> In b Lr) by (intros b Hb; subst Lr; apply in_or_app; right; apply in_or_app; right; exact Hb).
    eapply (rp_post NB S' M' LE m6 mo6 s6' rv); try eassumption.
    - eapply (mpres_trans H HH); [exact MP2|]. eapply (mpres_trans H HH); [exact MP4| exact MP6].
    - eapply (LIBMID_xpres0 (LE ++ LIB) Lr SPc); [exact LM2| | intros b Hb; subst Lr; apply in_app_or in Hb; destruct Hb as [Hb|Hb]; apply in_or_app; right; apply in_or_app; [left; exact Hb| right; apply SUBL; exact Hb]].
      eapply xpres_trans; [eapply xpres_weaken; [exact XP4| clear; lia| | intros q Hq; exact Hq]| eapply xpres_weaken; [exact XP6| clear; lia| intros b Hb; apply in_or_app; right; exact Hb| intros q Hq; exact Hq]].
      intros b Hb. subst Lr. apply in_or_app; right. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; apply in_or_app; [left; exact Hb| right; right; exact Hb].
    - eapply (STOREobj_frameX Lr SPc []); [exact SO1| exact XP16| intros b Hb; apply Forall_nil].
    - eapply (MEMBIO_frame0 LB LB SPc); [exact MBO1| exact MBLB| eapply xpres_weaken; [exact XP16| clear; lia| exact SUBr| intros q Hq; exact Hq]].
    - destruct (PAYL ltac:(clear - NAR; lia)) as [pD [PIN _]]. pose proof DSL as DSL1. unfold zlength in DSL1.
      eapply xpres_bytes_at'; [exact XP16| exact DSm1| right; right; exists (pD, mb_buf R, mb_len R); split; [apply SUBr; exact PIN| cbn; rewrite DSL1; clear; lia]| apply Forall_nil].
    - eapply xpres_trans; [exact XA1|]. eapply xpres_weaken; [exact XP16| unfold SP'; clear; lia| exact SUBr| intros q Hq; destruct Hq].
  Qed.

  (* [comment removed for export] *)
  Lemma rp_raise2 :
    forall (spq gpq t0q t1q t2q s0q s1q a0q a1q a2q a3q a4q a5q a6q a7q s2q s3q s4q s5q s6q s7q s8q s9q s10q s11q t3q t4q t5q t6q : word)
           (Fq : bvmap 5 word) (fcq : bv 32) (mq : mem) (moq : Model) (sq : PState) (LIBc Lc : list block) (Mq : libmid) (xq : ctxinfo)
           (loq Bq : Z) (errvq : word) (ra1 ra2 ra3 line reason func : Z) (gs gsl : list byte) (Q : config -> Prop),
      hs_RHEAP H sq (mid_errblocks Mq ++ Lc) mq -> hs_KREL H sq moq ->
      LIBMID LIBc mq Mq -> (forall b, In b LIBc -> In b Lc) -> mid_ctx Mq = CtxReady xq -> mid_flag Mq = 1 ->
      lb_bytes (mid_errblocks Mq ++ Lc) + errph_bytes (mid_err Mq) + ERRDEBUG_BYTES <= hs_LIVE_MAX H ->
      Z.of_nat (length (mid_errblocks Mq ++ Lc)) + errph_cnt (mid_err Mq) + 2 <= hs_LIVE_CNT_MAX H ->
      lb_big (mid_errblocks Mq ++ Lc) + errph_big (mid_err Mq) <= hs_LIVE_BIG_MAX H ->
      hs_rauxv_ok H mq Bq -> bv_unsigned spq <= Bq -> bv_unsigned spq mod 16 = 0 ->
      stk rsegs mq loq (bv_unsigned spq) -> hceil <= loq -> loq <= bv_unsigned spq - RAISE_STACK (mid_err Mq) ->
      rw_cells rsegs mq RERRNO [C4 errvq] -> mem_inv rsegs mq ->
      0 <= line < 2^31 -> 0 < reason < 2^23 ->
      0 <= ra1 < 2^64 -> ra1 mod 2 = 0 -> 0 <= ra2 < 2^64 -> ra2 mod 2 = 0 -> 0 <= ra3 < 2^64 -> ra3 mod 2 = 0 ->
      ROSTR func gs gsl -> gs <> [] -> Z.of_nat (length gs) < 32 -> 0 < func ->
      rglue ra1 ra2 P_ERR_set_debug (Z_to_bv 64 A_ECHS_FILE_RP) (Z_to_bv 64 line) (Z_to_bv 64 func) spq gpq (Z_to_bv 64 RATP) s0q s1q s2q s3q s4q s5q s6q s7q s8q s9q s10q s11q Fq fcq ->
      rglue ra2 ra3 P_ERR_set_error (Z_to_bv 64 ERR_LIB_SSL) (Z_to_bv 64 reason) (Z_to_bv 64 0) spq gpq (Z_to_bv 64 RATP) s0q s1q s2q s3q s4q s5q s6q s7q s8q s9q s10q s11q Fq fcq ->
      (forall (u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 : word) (mq' : mem) (moq' : Model) (sq' : PState) (errvq' : word) (LE : list block) (Mq' : libmid) (c : errchain),
         hs_KREL H sq' moq' -> hs_MPRES H moq moq' -> mem_inv rsegs mq' -> stk rsegs mq' loq (bv_unsigned spq) -> hs_rauxv_ok H mq' Bq ->
         hs_RHEAP H sq' (mid_errblocks Mq' ++ LE ++ Lc) mq' ->
         LIBMID (LE ++ LIBc) mq' Mq' -> mid_step Mq Mq' -> mid_newlib_ok Mq Mq' LE ->
         mid_flag Mq' = 1 -> mid_ctx Mq' = CtxReady xq -> mid_err Mq' = ErrReady c -> mid_vdso Mq' = mid_vdso Mq -> errph_delta (mid_err Mq) LE c ->
         Z.of_nat (length (mid_errblocks Mq')) <= ERRSTR_CNT -> lb_bytes (mid_errblocks Mq') <= ERRSTR_BYTES -> lb_big (mid_errblocks Mq') = 0 ->
         rw_cells rsegs mq' RERRNO [C4 errvq'] ->
         xpres Lc (bv_unsigned spq) (ERR_X ++ memflag_foot ++ errph_foot (mid_err Mq)) mq mq' ->
         hs_SR H Q (mkCfg (MS (mkR (Z_to_bv 64 ra3) spq gpq (Z_to_bv 64 RATP) u0 u1 u2 s0q s1q b0 b1 b2 b3 b4 b5 b6 b7 s2q s3q s4q s5q s6q s7q s8q s9q s10q s11q u3 u4 u5 u6)
                              Fq (ret_pc (Z_to_bv 64 ra3)) fcq None mq' (seg_rom rsegs)) moq')) ->
      hs_SR H Q (mkCfg (MS (mkR (Z_to_bv 64 ra1) spq gpq (Z_to_bv 64 RATP) t0q t1q t2q s0q s1q a0q a1q a2q a3q a4q a5q a6q a7q s2q s3q s4q s5q s6q s7q s8q s9q s10q s11q t3q t4q t5q t6q)
                           Fq (Z_to_bv 64 P_ERR_new) fcq None mq (seg_rom rsegs)) moq).
  Proof using HH EGS CERTO3 HX.
    intros until Q. intros HPq KRELq LMq SUBq CXq F1 BY CN BG AUXq SPBq SPAq STq CEILq LOq ERRq MIq LNR REAS R1 R1E R2 R2E R3 R3E RSG GSN GSL GPOS G1 G2 K.
    pose proof LMq as (IM & MFq & CPq & EPm & EXq & VDq & CLq & FITq & GMq & GE & GX & MM & MB & HT & RL).
    destruct Mq as [f cph eph E v]. cbn [mid_flag mid_ctx mid_err mid_E mid_vdso] in *. subst cph f.
    unfold mid_errblocks in *. cbn [mid_flag mid_ctx mid_err mid_E mid_vdso] in *. cbn [ERRPH_mid] in EPm.
    assert (EPq : ERRPH Lc mq eph) by (eapply ERRPH_mono; [exact EPm| exact SUBq]).
    assert (CPc : CTXPH Lc mq (CtxReady xq)) by (eapply CTXPH_mono; [exact CPq| exact SUBq]).
    assert (EB : errph_below eph loq).
    { destruct eph as [|c0]; [exact I|]. cbn [errph_below]. cbn [ERRPH] in EPm. destruct EPm as [_ CH].
      eapply (chain_below_of_RHEAP H HH); [exact HPq| intros b Hb; apply in_or_app; right; exact (SUBq _ Hb)| exact CH| exact CEILq]. }
    unfold rglue in G1, G2.
    eapply (raise_spec H HX EGS) with (lo := loq) (B := Bq) (LB := Lc) (s := sq) (ph := eph) (E := E) (x := xq) (errv := errvq)
      (file := A_ECHS_FILE_RP) (fs := S_echs_file) (fsl := K_echs_file) (func := func) (gs := gs) (gsl := gsl)
      (line := line) (lib := ERR_LIB_SSL) (reason := reason) (ra2 := ra2) (ra3 := ra3).
    all: try first [exact HPq| exact KRELq| exact AUXq| exact SPBq| exact SPAq| exact STq| exact CEILq| exact LOq| exact MIq| exact MFq| exact IM| exact GMq| exact RL| exact EPq| exact EXq| exact EB| exact CPc
                    | exact R_echs_file| exact RSG| exact GSN| exact GSL| exact GPOS| exact LNR| exact REAS| exact R1| exact R1E| exact R2| exact R2E| exact R3| exact R3E].
    all: lazymatch goal with
         | |- lb_bytes _ + raise_bytes _ <= _ => unfold raise_bytes; clear - BY; lia
         | |- Z.of_nat _ + raise_cnt _ <= _ => unfold raise_cnt; clear - CN; lia
         | |- lb_big _ + _ <= _ => exact BG
         | |- rw_cells _ _ (errno_addr _) _ => rewrite errno_RATP; exact ERRq
         | |- Z_to_bv 64 RATP = _ => reflexivity
         | |- _ <> [] => discriminate
         | |- Z.of_nat (length S_echs_file) < _ => vm_compute; reflexivity
         | |- 0 < A_ECHS_FILE_RP => unfold A_ECHS_FILE_RP; lia
         | |- 0 < ERR_LIB_SSL < 256 => unfold ERR_LIB_SSL; lia
         | |- ERR_LIB_SSL <> 2 => unfold ERR_LIB_SSL; lia
         | |- forall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, mem_inv _ _ -> evt _ (fun _ => exists _ _ _ _ _ _ _ _ _ _ _ _, _ = MS _ _ (Z_to_bv 64 P_ERR_set_debug) _ _ _ _) _ =>
             exact G1
         | |- forall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, mem_inv _ _ -> evt _ (fun _ => exists _ _ _ _ _ _ _ _ _ _ _ _, _ = MS _ _ (Z_to_bv 64 P_ERR_set_error) _ _ _ _) _ =>
             exact G2
         | _ => idtac
         end.
    (* [comment removed for export] *)
    intros u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 mq' moq' sq' errvq' LBN c p1 p2 A1q A2q n1 n2 E'
           KRELq' MP' MIq' STq' AUXq' HPq' MFq' IM' GMq' RL' ERRq' DL RSZ EPq' CPq' EST' XP'.
    pose proof (errst_fits_raise E A1q p1 n1 line A2q p2 n2 ERR_LIB_SSL reason FITq RSZ) as FITq'. change (errst_fits E') in FITq'.
    pose proof (LIBMID_errcall_mf LIBc Lc (LBN ++ Lc) LBN (bv_unsigned spq) mq mq' (mkMID 1 (CtxReady xq) eph E v) xq c E' LMq eq_refl XP' SUBq CPq' EPq' DL EST' FITq' MFq') as LMq'.
    cbn [mid_vdso] in LMq'.
    pose proof EST' as (LEN' & _).
    pose proof (errst_fits_bounds E' LEN' FITq') as (EC' & EB' & EG').
    rewrite errno_RATP in ERRq'.
    eapply (K u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 mq' moq' sq' errvq' LBN (mkMID 1 (CtxReady xq) (ErrReady c) E' v) c);
      cbn [mid_flag mid_ctx mid_err mid_E mid_vdso mid_errblocks]; try reflexivity.
    all: try first [exact KRELq'| exact MP'| exact MIq'| exact STq'| exact AUXq'| exact HPq'| exact LMq'| exact DL| exact EC'| exact EB'| exact EG'| exact ERRq'| exact XP'].
    - (* [comment removed for export] *) unfold mid_step. cbn [mid_flag mid_ctx mid_err mid_vdso]. split; [reflexivity|]. split; [intros b Hb; exact Hb|].
      split; [| intros Hv; exact Hv]. intros c0 ->. cbn [errph_delta] in DL. destruct DL as [-> _]. reflexivity.
    - (* [comment removed for export] *) unfold mid_newlib_ok. cbn [mid_ctx mid_err]. exists [], LBN. split; [apply Permutation_refl|]. split; [reflexivity|].
      destruct eph as [|c0]; [exact DL|]. cbn [errph_delta] in DL. destruct DL as [_ ->]. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma dwk_lib_facts : forall Lx NB S' M' LE fr j3 m' mo' s',
    DWKG Lx NB S' M' LE fr j3 m' mo' s' ->
    MEMFLAG m' 1 /\ IMPL_mem m' /\ GOT_mem m' /\ GOT_echfree m' /\ METH_mem m' /\ METH_b64 m' /\ relro_lib m' /\ mid_flag M' = 1 /\ mid_ctx M' = CtxReady x.
  Proof using CTX.
    intros until s'. intros DW. pose proof DW as (_ & _ & _ & LM1 & STP & _ & CTX1 & _).
    pose proof LM1 as (IM & MF & _ & _ & _ & _ & _ & _ & GM & GE & _ & MM & MB & _ & RL). destruct STP as (F1 & _). rewrite F1 in MF.
    split; [exact MF|]. split; [exact IM|]. split; [exact GM|]. split; [exact GE|]. split; [exact MM|]. split; [exact MB|]. split; [exact RL|]. split; [exact F1|]. rewrite CTX1. exact CTX.
  Qed.

  (* [comment removed for export] *)
  Lemma dwk_after_efree : forall Lx NB S' M' LE fr j3 m1 mo1 s1' ee E m2 mo2 s2' LB2,
    DWKG Lx NB S' M' LE fr j3 m1 mo1 s1' ->
    Permutation (blocks_ENTRY ee E) Lx ->
    Permutation (blocks_ENTRY ee E ++ LB2) (mid_errblocks M' ++ DREST Lx NB LE) -> hs_RHEAP H s2' LB2 m2 -> xpres LB2 SPc [] m1 m2 ->
    hs_KREL H s2' mo2 -> hs_MPRES H mo mo2 -> (exists errv', rw_cells rsegs m2 RERRNO [C4 errv']) -> mem_inv rsegs m2 -> stk rsegs m2 lo SPc -> hs_rauxv_ok H m2 B ->
    DWKG [] NB S' M' LE fr j3 m2 mo2 s2'.
  Proof using A0 A1 SO SE SEO STL MBO MP0 MN0 MBB MBS DS DSL PAYL NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC BUDG AUX SPB BHI SPA ST CEIL LO ERR MI TP RAE HH HX NAR NBR MST POS BTR BT_frame PERM.
    intros until LB2. intros DW PE PL HP2 XP2 KREL2 MP2 ERR2 MI2 ST2 AUX2.
    destruct (DWKGF _ _ _ _ _ _ _ _ _ _ DW) as (HB & ND & DISJ & BRS & D2 & D1).
    assert (SUB2 : forall b, In b (mid_errblocks M' ++ DREST [] NB LE) -> In b LB2).
    { intros b Hb. eapply perm_in_rest; [exact PL| |].
      - apply in_app_or in Hb. destruct Hb as [Hb|Hb]; apply in_or_app; [left; exact Hb| right; rewrite drest_app; apply in_or_app; right; exact Hb].
      - intros K. pose proof (Permutation_in _ PE K) as KX. apply in_app_or in Hb. destruct Hb as [Hb|Hb].
        + exact (D1 _ _ Hb ltac:(rewrite drest_app; apply in_or_app; left; exact KX) eq_refl).
        + exact (D2 _ _ KX Hb eq_refl). }
    assert (PL2 : Permutation LB2 (mid_errblocks M' ++ DREST [] NB LE)).
    { eapply Permutation_app_inv_l. eapply Permutation_trans; [exact PL|]. rewrite (drest_app LB p A nA pbin Bb nB TB Lx NB LE).
      rewrite (app_assoc (mid_errblocks M') Lx). eapply Permutation_trans; [apply Permutation_app_tail; apply Permutation_app_comm|].
      rewrite <- app_assoc. apply Permutation_app; [apply Permutation_sym; exact PE| apply Permutation_refl]. }
    eapply (DWKGX Lx []); [exact DW| | | exact KREL2| exact MP2| exact ERR2| exact MI2| exact ST2| exact AUX2].
    - eapply xpres_weaken; [exact XP2| clear; lia| intros b Hb; apply SUB2; apply in_or_app; right; exact Hb| intros q Hq; exact Hq].
    - eapply PERM; [exact HP2| exact PL2].
  Qed.

  (* [comment removed for export] *)
  Lemma drest_LEn_perm : forall Lx NB LE LEn, Permutation (LEn ++ DREST Lx NB LE) (DREST Lx NB (LEn ++ LE)).
  Proof.
    clear. intros Lx NB LE LEn. unfold drest.
    transitivity ((LEn ++ (Lx ++ NB ++ TB ++ [(pbin, Bb, nB); (p, A, nA)])) ++ (LE ++ LB)).
    { rewrite <- !app_assoc. cbn [app]. apply Permutation_refl. }
    transitivity (((Lx ++ NB ++ TB ++ [(pbin, Bb, nB); (p, A, nA)]) ++ LEn) ++ (LE ++ LB)).
    { apply Permutation_app_tail. apply Permutation_app_comm. }
    rewrite <- !app_assoc. cbn [app]. apply Permutation_refl.
  Qed.

  (* [comment removed for export] *)
  Lemma dwk_after_raise : forall Lx NB S' M' LE fr j3 m1 mo1 s1' m2 mo2 s2' LEn M'' errv2,
    DWKG Lx NB S' M' LE fr j3 m1 mo1 s1' ->
    hs_KREL H s2' mo2 -> hs_MPRES H mo1 mo2 -> mem_inv rsegs m2 -> stk rsegs m2 lo SPc -> hs_rauxv_ok H m2 B ->
    hs_RHEAP H s2' (mid_errblocks M'' ++ LEn ++ DREST Lx NB LE) m2 ->
    LIBMID (LEn ++ LE ++ LIB) m2 M'' -> mid_step M' M'' -> mid_newlib_ok M' M'' LEn ->
    mid_flag M'' = 1 -> mid_ctx M'' = CtxReady x ->
    Z.of_nat (length (mid_errblocks M'')) <= ERRSTR_CNT -> lb_bytes (mid_errblocks M'') <= ERRSTR_BYTES -> lb_big (mid_errblocks M'') = 0 ->
    rw_cells rsegs m2 RERRNO [C4 errv2] ->
    xpres (DREST Lx NB LE) SPc (ERR_X ++ memflag_foot ++ errph_foot (mid_err M')) m1 m2 ->
    DWKG Lx NB S' M'' (LEn ++ LE) fr j3 m2 mo2 s2'.
  Proof using A0 A1 SO SE SEO STL MBO MP0 MN0 MBB MBS DS DSL PAYL NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC BUDG AUX SPB BHI SPA ST CEIL LO ERR MI TP RAE HH HX NAR NBR MST POS BTR BT_frame PERM.
    intros until errv2. intros DW KREL2 MP2 MI2 ST2 AUX2 HP2 LM2 STP2 NEW2 F2 CTX2 EC2 EB2 EG2 ERR2 XP2.
    pose proof DW as (HP1 & KREL1 & MP1 & LM1 & STP & NEW & CTX1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FR0 & FR2 & FR3 & FR4 & _ & MI1 & _).
    destruct (DWKGF _ _ _ _ _ _ _ _ _ _ DW) as (HB & ND & DISJ & BRS & D2 & D1).
    destruct RCFACTS as (SEQ & SIN & SBR & BEL0 & SUB0 & ND0 & STK0 & LO0 & MF0 & OBJ0 & DJA). hcb.
    pose proof (DRESTSUB Lx NB LE) as (SLB & S0 & SLE & SNB & STB & IB & IA & SLX & S3 & SLL).
    destruct (dwk_lib_facts _ _ _ _ _ _ _ _ _ _ DW) as (MFa & _).
    assert (MFb : MEMFLAG m2 1) by (destruct LM2 as (_ & MFb & _); rewrite F2 in MFb; exact MFb).
    pose proof (ECH_C14_fcc.xpres_drop_memflag _ _ ERR_X (errph_foot (mid_err M')) m1 m2 MFa MFb XP2) as XP.
    (* [comment removed for export] *)
    assert (AVS : forall a n, SPc <= a -> avoids ([] ++ ERR_X ++ errph_foot (mid_err M')) a n).
    { intros a n Ha. unfold avoids. cbn [app]. apply Forall_app. split.
      - apply avoid_of_img; [apply img_ERR_X| right; unfold IMG_HI, SP' in *; clear - Ha CEIL HCEILB LO STK0; lia].
      - destruct (mid_err M') as [|c1] eqn:EQ; [apply Forall_nil|]. cbn [errph_foot]. apply Forall_cons; [| apply Forall_nil]. cbn [fst snd].
        destruct (DWKGES _ _ _ _ _ _ _ _ _ _ c1 DW EQ) as [I5 Z5].
        pose proof (HB (ec_es c1) ltac:(apply in_or_app; right; apply S0; apply SLL; exact I5)) as E. rewrite Z5 in E. right. unfold SP' in *. clear - E Ha CEIL LO STK0. lia. }
    eapply (DWKGL Lx Lx NB S' M' M'' LE LEn fr j3 m1 mo1 s1' m2 mo2 s2' [] fr j3);
      [exact DW| exact LM2| exact STP2| exact NEW2| rewrite CTX2, CTX1, CTX; reflexivity| exact EC2| exact EB2| exact EG2| cbn [app]; exact XP| apply Forall_nil
      | | exact KREL2| eapply (mpres_trans H HH); [exact MP1| exact MP2]| exists errv2; exact ERR2| exact MI2| exact ST2| exact AUX2| |].
    - eapply PERM; [exact HP2|]. apply Permutation_app_head. apply drest_LEn_perm.
    - eapply xpres_rw_cells'; [exact XP| exact FR0| left; clear; lia| cbn [app] in AVS |- *; apply AVS; clear; lia].
    - eapply xpres_rw_cells'; [exact XP| exact FR3| left; unfold O_F3; clear; lia| cbn [app] in AVS |- *; apply AVS; unfold O_F3; clear; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma rp_efree : forall Lx NB S' M' LE fr j3 m1 mo1 s1' (ee : Z) (oe : option entrep) (rax : Z)
      (gpx u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 s2w s3w s4w s5w s6w s7w s8w s9w s10w s11w u3 u4 u5 u6 : word) (Q : config -> Prop),
    DWKG Lx NB S' M' LE fr j3 m1 mo1 s1' ->
    match oe with None => ee = 0 /\ Lx = [] | Some E => ENTRYobj (DREST Lx NB LE) m1 ee E /\ Permutation (blocks_ENTRY ee E) Lx end ->
    0 <= rax < 2^64 -> rax mod 2 = 0 ->
    (forall m2 mo2 s2' (v0 v1 v2 c0 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 : word),
       DWKG [] NB S' M' LE fr j3 m2 mo2 s2' ->
       hs_SR H Q (mkCfg (MS (mkR (Z_to_bv 64 rax) (Z_to_bv 64 SPc) gpx (Z_to_bv 64 RATP) v0 v1 v2 sp (Z_to_bv 64 A) c0 c1 c2 c3 c4 c5 c6 c7
                                s2w s3w s4w s5w s6w s7w s8w s9w s10w s11w v3 v4 v5 v6) F (ret_pc (Z_to_bv 64 rax)) fc None m2 (seg_rom rsegs)) mo2)) ->
    hs_SR H Q (mkCfg (MS (mkR (Z_to_bv 64 rax) (Z_to_bv 64 SPc) gpx (Z_to_bv 64 RATP) u0 u1 u2 sp (Z_to_bv 64 A) (Z_to_bv 64 ee) b1 b2 b3 b4 b5 b6 b7
                             s2w s3w s4w s5w s6w s7w s8w s9w s10w s11w u3 u4 u5 u6) F (Z_to_bv 64 P_ossl_echstore_entry_free) fc None m1 (seg_rom rsegs)) mo1).
  Proof using A0 A1 SO SE SEO STL MBO MP0 MN0 MBB MBS DS DSL PAYL NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC BUDG AUX SPB BHI SPA ST CEIL LO ERR MI TP RAE HH HX NAR NBR MST POS BTR BT_frame PERM.
    intros until Q. intros DW OE RAXR RAXE K.
    pose proof DW as (HP1 & KREL1 & MP1 & LM1 & STP & NEW & CTX1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FR0 & FR2 & FR3 & FR4 & [errv1 ERR1] & MI1 & ST1 & AUX1 & XA1 & _).
    destruct (DWKGF _ _ _ _ _ _ _ _ _ _ DW) as (HB & ND & DISJ & BRS & D2 & D1).
    destruct RCFACTS as (SEQ & SIN & SBR & BEL0 & SUB0 & ND0 & STK0 & LO0 & MF0 & OBJ0 & DJA). hcb. pose proof (word_range sp) as SPR.
    destruct (dwk_lib_facts _ _ _ _ _ _ _ _ _ _ DW) as (MFa & IMa & GMa & GEa & _).
    pose proof (dec_stack M M' STP) as (_ & _ & _ & _ & STKE & _).
    destruct oe as [E|].
    - destruct OE as [EO PE].
      pose proof (entryfree_spec H HH) as EF. unfold entryfree_stmt, efree_stmt_at in EF.
      eapply (sr_seq H HH).
      { eapply EF with (lo := lo) (B := B) (LB := mid_errblocks M' ++ DREST Lx NB LE) (s := s1') (p := ee) (x := E) (errv := errv1); clear EF; try reflexivity.
        all: try first [exact HP1| exact KREL1| exact AUX1| exact MI1| exact IMa| exact GMa| exact GEa| exact CEIL| exact RAXE].
        all: lazymatch goal with
             | |- ENTRYobj _ _ _ _ => eapply ENTRYobj_LB_mono; [exact EO| intros b Hb; apply in_or_app; right; exact Hb]
             | |- List.NoDup _ => eapply Permutation_NoDup; [apply Permutation_map; apply Permutation_sym; exact PE|];
                                  destruct (nd_app _ _ ND) as [_ ND1]; rewrite drest_app, map_app in ND1; exact (NoDup_app_remove_r _ _ ND1)
             | |- bv_unsigned _ <= B => unfold SP'; rewrite unsigned_lit by (clear - SPR LO STK0 LO0; lia); clear - SPB; lia
             | |- stk _ _ _ _ => unfold SP'; rewrite unsigned_lit by (clear - SPR LO STK0 LO0; lia); exact ST1
             | |- lo <= _ => unfold SP'; rewrite unsigned_lit by (clear - SPR LO STK0 LO0; lia); clear - LO STKE; lia
             | |- rw_cells _ _ (errno_addr _) _ => rewrite errno_RATP; exact ERR1
             | |- _ mod 2 = 0 => rewrite unsigned_lit by (clear - RAXR; lia); exact RAXE
             | |- _ => idtac
             end. }
      clear EF. intros [ms2 mo2] PO. unfold efree_post in PO. cbn [cfg_ms cfg_model] in PO.
      destruct PO as (v0 & v1 & v2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m2 & s2' & LB2 & -> & KREL2 & MP2 & MI2 & ST2 & ERR2 & AUX2 & PL & HP2 & XP2 & _).
      unfold SP' in ST2, XP2. rewrite (unsigned_lit (bv_unsigned sp + -2352)) in ST2, XP2 by (clear - SPR LO STK0 LO0; lia). rewrite errno_RATP in ERR2.
      change (bv_unsigned sp + -2352) with SPc in ST2, XP2.
      eapply K. eapply (dwk_after_efree Lx); [exact DW| exact PE| exact PL| exact HP2| exact XP2| exact KREL2| eapply (mpres_trans H HH); [exact MP1| exact MP2]
                                          | exists errv1; exact ERR2| exact MI2| exact ST2| exact AUX2].
    - destruct OE as [-> ->].
      eapply (sr_evt_krel H HH); [exact KREL1| eapply entryfree_null_spec with (lo := lo)|].
      { unfold SP'; rewrite unsigned_lit by (clear - SPR LO STK0 LO0; lia). exact ST1. }
      { unfold SP'; rewrite unsigned_lit by (clear - SPR LO STK0 LO0; lia). clear - LO STK0; lia. }
      { exact MI1. }
      { rewrite unsigned_lit by (clear - RAXR; lia). exact RAXE. }
      intros ms2 PO. unfold sknull_post in PO.
      destruct PO as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m2 & -> & MU2 & WM2 & MI2 & ST2).
      unfold SP' in MU2, ST2. rewrite (unsigned_lit (bv_unsigned sp + -2352)) in MU2, ST2 by (clear - SPR LO STK0 LO0; lia). change (bv_unsigned sp + -2352) with SPc in MU2, ST2.
      eapply K. eapply (DWKGW [] NB S' M' LE fr j3 m1 mo1 s1' m2); [exact DW| exact MU2| exact WM2| exact MI2| exact ST2| | |].
      + apply Forall_cons; [left; cbn; clear; lia| apply Forall_nil].
      + eapply rw_cells_transport; [exact FR0| exact MU2| exact WM2| cbn; clear; lia].
      + eapply rw_cells_transport; [exact FR3| exact MU2| exact WM2| cbn; unfold O_F3; clear; lia].
  Qed.

  Lemma lb_bytes_nonneg_of : forall L : list block, (forall b, In b L -> 0 <= blk_size b) -> 0 <= lb_bytes L.
  Proof. clear. induction L as [|b L IH]; intros K; [cbn; lia|]. rewrite lb_bytes_cons. pose proof (K b (or_introl eq_refl)). pose proof (IH ltac:(intros c Hc; apply K; right; exact Hc)). lia. Qed.
  Lemma lb_big_nonneg : forall L : list block, 0 <= lb_big L.
  Proof. clear. induction L as [|b L IH]; [cbn; lia|]. rewrite lb_big_cons. pose proof (big1_range (blk_size b)). lia. Qed.

  (* [comment removed for export] *)
  Lemma errph_delta_bounds : forall eph LEn c, errph_delta eph LEn c ->
    Z.of_nat (length LEn) + errph_cnt (ErrReady c) <= errph_cnt eph /\ lb_bytes LEn + errph_bytes (ErrReady c) <= errph_bytes eph /\ lb_big LEn + errph_big (ErrReady c) <= errph_big eph.
  Proof.
    clear. intros [|c0] LEn c DL; cbn [errph_delta errph_cnt errph_bytes errph_big] in *.
    - destruct DL as (Q1 & Q2 & Q3 & _). unfold ERRINIT_BIG. lia.
    - destruct DL as [_ ->]. cbn. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma dbud_raise : forall Lx NB S' M' LE fr j3 m' mo' s' hb hc hg,
    DWKG Lx NB S' M' LE fr j3 m' mo' s' -> DBUD (DREST Lx NB LE) M' hb hc hg -> 0 <= hb -> 0 <= hc -> 0 <= hg ->
       lb_bytes (mid_errblocks M' ++ DREST [] NB LE) + errph_bytes (mid_err M') + hb <= hs_LIVE_MAX H
    /\ Z.of_nat (length (mid_errblocks M' ++ DREST [] NB LE)) + errph_cnt (mid_err M') + hc <= hs_LIVE_CNT_MAX H
    /\ lb_big (mid_errblocks M' ++ DREST [] NB LE) + errph_big (mid_err M') + hg <= hs_LIVE_BIG_MAX H
    /\ lb_bytes (mid_errblocks M' ++ DREST Lx NB LE) + errph_bytes (mid_err M') + hb <= hs_LIVE_MAX H
    /\ Z.of_nat (length (mid_errblocks M' ++ DREST Lx NB LE)) + errph_cnt (mid_err M') + hc <= hs_LIVE_CNT_MAX H
    /\ lb_big (mid_errblocks M' ++ DREST Lx NB LE) + errph_big (mid_err M') + hg <= hs_LIVE_BIG_MAX H
    /\ DBUD (DREST [] NB LE) M' hb hc hg.
  Proof using HH.
    intros until hg. intros DW (B1 & B2 & B3) P1 P2 P3. pose proof DW as (_ & _ & _ & _ & _ & _ & _ & EC & EB & EG & _).
    destruct (DWKGF _ _ _ _ _ _ _ _ _ _ DW) as (HB & ND & DISJ & BRS & D2 & D1).
    assert (LX0 : 0 <= lb_bytes Lx) by (apply lb_bytes_nonneg_of; intros b Hb; pose proof (BRS b ltac:(apply in_or_app; right; rewrite drest_app; apply in_or_app; left; exact Hb)) as (_ & _ & K & _); exact K).
    pose proof (lb_big_nonneg Lx) as LG0.
    rewrite (drest_app LB p A nA pbin Bb nB TB Lx NB LE) in B1, B2, B3 |- *. unfold dbud.
    rewrite ?lb_bytes_app, ?lb_big_app, ?length_app, ?Nat2Z.inj_add in B1. rewrite ?lb_bytes_app, ?lb_big_app, ?length_app, ?Nat2Z.inj_add in B2. rewrite ?lb_bytes_app, ?lb_big_app, ?length_app, ?Nat2Z.inj_add in B3.
    rewrite ?lb_bytes_app, ?lb_big_app, ?length_app, ?Nat2Z.inj_add.
    unfold ERRSTR_BYTES, ERRSTR_CNT in *.
    repeat split; clear - B1 B2 B3 P1 P2 P3 EC EB EG LX0 LG0; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma lx_avoids : forall Lx NB S' M' LE fr j3 m' mo' s' b,
    DWKG Lx NB S' M' LE fr j3 m' mo' s' -> In b Lx ->
    avoids (ERR_X ++ memflag_foot ++ errph_foot (mid_err M')) (blk_addr b) (blk_size b).
  Proof using CTX SUBL HH.
    intros until b. intros DW Hb.
    destruct (DWKGF _ _ _ _ _ _ _ _ _ _ DW) as (HB & ND & DISJ & BRS & D2 & D1).
    pose proof (DRESTSUB Lx NB LE) as (SLB & S0 & SLE & SNB & STB & IB & IA & SLX & S3 & SLL).
    pose proof (DRESTSUB ([] : list block) NB LE) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & SLL0).
    pose proof (BRS b ltac:(apply in_or_app; right; apply SLX; exact Hb)) as (_ & _ & _ & _ & O).
    unfold avoids. apply Forall_app; split; [| apply Forall_app; split].
    - apply avoid_of_img; [apply img_ERR_X| unfold IMG_LO, IMG_HI; clear - O; lia].
    - apply avoid_of_img; [apply img_memflag| unfold IMG_LO, IMG_HI; clear - O; lia].
    - destruct (mid_err M') as [|c1] eqn:EQ; [apply Forall_nil|]. cbn [errph_foot]. apply Forall_cons; [| apply Forall_nil]. cbn [fst snd].
      destruct (DWKGES _ _ _ _ _ _ _ _ _ _ c1 DW EQ) as [I5 Z5].
      pose proof (DISJ b (ec_es c1) ltac:(apply in_or_app; right; apply SLX; exact Hb) ltac:(apply in_or_app; right; apply S0; apply SLL0; exact I5) (D2 _ _ Hb (SLL0 _ I5))) as E.
      rewrite Z5 in E. clear - E. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma rp_tailX : forall Lx NB S' M' LE fr j3 m1 mo1 s1' (ee : Z) (oe : option entrep)
      (rax u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 s4w s5w s6w s8w s9w s10w s11w u3 u4 u5 u6 : word),
    DWKG Lx NB S' M' LE fr j3 m1 mo1 s1' -> cells_size fr = 112%nat ->
    match oe with None => ee = 0 /\ Lx = [] | Some E => ENTRYobj (DREST Lx NB LE) m1 ee E /\ Permutation (blocks_ENTRY ee E) Lx end ->
    DBUD (DREST Lx NB LE) M' ERRDEBUG_BYTES 2 0 ->
    hs_SR H POSTc (mkCfg (MS (mkR rax (Z_to_bv 64 SPc) gp (Z_to_bv 64 RATP) u0 u1 u2 sp (Z_to_bv 64 A) b0 b1 b2 b3 b4 b5 b6 b7
                                (Z_to_bv 64 bt) (Z_to_bv 64 Bb) s4w s5w s6w (Z_to_bv 64 ee) s8w s9w s10w s11w u3 u4 u5 u6)
                           F (Z_to_bv 64 DF_TX) fc None m1 (seg_rom rsegs)) mo1).
  Proof using A0 A1 SO SE SEO STL MBO MP0 MN0 MBB MBS DS DSL PAYL NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC BUDG AUX SPB BHI SPA ST CEIL LO ERR MI TP RAE HH HX NAR NBR MST POS BTR BT_frame PERM BTFREE CERTO3.
    intros until u6. intros DW FSZ OE BD.
    pose proof DW as (_ & KREL1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MI1 & _).
    destruct RCFACTS as (SEQ & SIN & SBR & BEL0 & SUB0 & ND0 & STK0 & LO0 & MF0 & OBJ0 & DJA). hcb. pose proof (word_range sp) as SPR.
    destruct (dbud_raise _ _ _ _ _ _ _ _ _ _ _ _ _ DW BD ltac:(unfold ERRDEBUG_BYTES; clear; lia) ltac:(clear; lia) ltac:(clear; lia)) as (RB1 & RB2 & RB3 & _ & _ & _ & BD0).
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL1| eapply ft_x1; exact MI1|]. intros ms2 ->.
    eapply (rp_efree Lx); [exact DW| exact OE| unfold DF_TX_R0; clear; lia| reflexivity|].
    clear DW OE KREL1 MI1. intros m2 mo2 s2' v0 v1 v2 c0 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 DW2.
    pose proof DW2 as (HP2 & KREL2 & MP2 & LM2 & STP2 & _ & CTX2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & [errv2 ERR2] & MI2 & ST2 & AUX2 & _).
    destruct (dwk_lib_facts _ _ _ _ _ _ _ _ _ _ DW2) as (MF2 & IM2 & GM2 & GE2 & MM2 & MB2 & RL2 & F2 & CX2).
    pose proof (dec_stack M M' STP2) as (_ & _ & STKR & _).
    pose proof (DRESTSUB ([] : list block) NB LE) as (SLB0 & _ & SLE0 & SNB0 & STB0 & IB0 & IA0 & _ & S30 & SLL0).
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL2| eapply ft_x2; exact MI2|]. intros ms3 ->.
    eapply (rp_raise H HX CERTO3) with (LIBc := LE ++ LIB) (Lc := DREST [] NB LE) (M := M') (x := x) (lo := lo) (B := B) (line := 637) (reason := R_INTERNAL_ERROR)
                                        (ra2 := DF_TX_R2) (ra3 := DF_TX_R3).
    all: try first [exact HP2| exact KREL2| exact LM2| exact SLL0| exact CX2| exact F2| exact AUX2| exact ERR2| exact MI2| exact CEIL| exact ft_x3| exact ft_x4| exact RB1| exact RB2| exact RB3].
    all: lazymatch goal with
         | |- bv_unsigned _ <= B => unfold SP'; rewrite unsigned_lit by (clear - SPR LO STK0 LO0; lia); clear - SPB; lia
         | |- bv_unsigned _ mod 16 = 0 => unfold SP'; rewrite unsigned_lit by (clear - SPR LO STK0 LO0; lia); clear - SPA; lia
         | |- stk _ _ _ _ => unfold SP'; rewrite unsigned_lit by (clear - SPR LO STK0 LO0; lia); exact ST2
         | |- lo <= _ => unfold SP'; rewrite unsigned_lit by (clear - SPR LO STK0 LO0; lia); clear - LO STKR; lia
         | |- 0 <= 637 < _ => clear; lia
         | |- 0 < R_INTERNAL_ERROR < _ => unfold R_INTERNAL_ERROR; clear; lia
         | |- 0 <= _ < 2 ^ 64 => unfold DF_TX_R1, DF_TX_R2, DF_TX_R3; clear; lia
         | |- _ mod 2 = 0 => reflexivity
         | |- lb_big _ + _ <= _ => clear - RB3; lia
         | |- _ => idtac
         end.
    intros u7 u8 u9 d0 d1 d2 d3 d4 d5 d6 d7 u10 u11 u12 u13 m3 mo3 s3' errv3 LEn M'' c KREL3 MP3 MI3 ST3 AUX3 HP3 LM3 STP3 NEW3 F3 CTX3 ME3 VD3 DL3 EC3 EB3 EG3 ERR3 XP3.
    unfold SP' in ST3, XP3. rewrite (unsigned_lit (bv_unsigned sp + -2352)) in ST3, XP3 by (clear - SPR LO STK0 LO0; lia). change (bv_unsigned sp + -2352) with SPc in ST3, XP3.
    pose proof (dwk_after_raise [] NB S' M' LE fr j3 m2 mo2 s2' m3 mo3 s3' LEn M'' errv3 DW2 KREL3 MP3 MI3 ST3 AUX3 HP3 LM3 STP3 NEW3 F3 CTX3 EC3 EB3 EG3 ERR3 XP3) as DW3.
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL3| eapply ft_x5; exact MI3|]. intros ms4 ->.
    eapply ERRL; [exact DW3| exact FSZ| left; reflexivity].
  Qed.

  (* [comment removed for export] *)
  Lemma rp_tailXg : forall NB S' M' LE fr j3 m2 mo2 s2' (ra1 line : Z)
      (v0 v1 v2 c0 c1 c2 c3 c4 c5 c6 c7 s4w s5w s6w s7w s8w s9w s10w s11w v3 v4 v5 v6 : word),
    DWKG [] NB S' M' LE fr j3 m2 mo2 s2' -> cells_size fr = 112%nat -> 0 <= line < 2^31 -> 0 <= ra1 < 2^64 -> ra1 mod 2 = 0 ->
    rp_glue ra1 DF_TX_R2 P_ERR_set_debug A_ECHS_FILE_RP line A_ECHS_FUNC_RP ->
    DBUD (DREST [] NB LE) M' ERRDEBUG_BYTES 2 0 ->
    hs_SR H POSTc (mkCfg (MS (mkR (Z_to_bv 64 ra1) (Z_to_bv 64 SPc) gp (Z_to_bv 64 RATP) v0 v1 v2 sp (Z_to_bv 64 A) c0 c1 c2 c3 c4 c5 c6 c7
                                (Z_to_bv 64 bt) (Z_to_bv 64 Bb) s4w s5w s6w s7w s8w s9w s10w s11w v3 v4 v5 v6)
                           F (Z_to_bv 64 P_ERR_new) fc None m2 (seg_rom rsegs)) mo2).
  Proof using A0 A1 SO SE SEO STL MBO MP0 MN0 MBB MBS DS DSL PAYL NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC BUDG AUX SPB BHI SPA ST CEIL LO ERR MI TP RAE HH HX NAR NBR MST POS BTR BT_frame PERM BTFREE CERTO3.
    intros until v6. intros DW2 FSZ LNR R1 R1E G1 BD.
    destruct RCFACTS as (SEQ & SIN & SBR & BEL0 & SUB0 & ND0 & STK0 & LO0 & MF0 & OBJ0 & DJA). hcb. pose proof (word_range sp) as SPR.
    destruct (dbud_raise _ _ _ _ _ _ _ _ _ _ _ _ _ DW2 BD ltac:(unfold ERRDEBUG_BYTES; clear; lia) ltac:(clear; lia) ltac:(clear; lia)) as (RB1 & RB2 & RB3 & _).
    pose proof DW2 as (HP2 & KREL2 & MP2 & LM2 & STP2 & _ & CTX2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & [errv2 ERR2] & MI2 & ST2 & AUX2 & _).
    destruct (dwk_lib_facts _ _ _ _ _ _ _ _ _ _ DW2) as (MF2 & IM2 & GM2 & GE2 & MM2 & MB2 & RL2 & F2 & CX2).
    pose proof (dec_stack M M' STP2) as (_ & _ & STKR & _).
    pose proof (DRESTSUB ([] : list block) NB LE) as (SLB0 & _ & SLE0 & SNB0 & STB0 & IB0 & IA0 & _ & S30 & SLL0).
    eapply (rp_raise H HX CERTO3) with (LIBc := LE ++ LIB) (Lc := DREST [] NB LE) (M := M') (x := x) (lo := lo) (B := B) (line := line) (reason := R_INTERNAL_ERROR)
                                        (ra2 := DF_TX_R2) (ra3 := DF_TX_R3).
    all: try first [exact HP2| exact KREL2| exact LM2| exact SLL0| exact CX2| exact F2| exact AUX2| exact ERR2| exact MI2| exact CEIL| exact G1| exact ft_x4| exact RB1| exact RB2| exact RB3| exact LNR| exact R1| exact R1E].
    all: lazymatch goal with
         | |- bv_unsigned _ <= B => unfold SP'; rewrite unsigned_lit by (clear - SPR LO STK0 LO0; lia); clear - SPB; lia
         | |- bv_unsigned _ mod 16 = 0 => unfold SP'; rewrite unsigned_lit by (clear - SPR LO STK0 LO0; lia); clear - SPA; lia
         | |- stk _ _ _ _ => unfold SP'; rewrite unsigned_lit by (clear - SPR LO STK0 LO0; lia); exact ST2
         | |- lo <= _ => unfold SP'; rewrite unsigned_lit by (clear - SPR LO STK0 LO0; lia); clear - LO STKR; lia
         | |- 0 < R_INTERNAL_ERROR < _ => unfold R_INTERNAL_ERROR; clear; lia
         | |- 0 <= _ < 2 ^ 64 => unfold DF_TX_R2, DF_TX_R3; clear; lia
         | |- _ mod 2 = 0 => reflexivity
         | |- lb_big _ + _ <= _ => clear - RB3; lia
         | |- _ => idtac
         end.
    intros u7 u8 u9 d0 d1 d2 d3 d4 d5 d6 d7 u10 u11 u12 u13 m3 mo3 s3' errv3 LEn M'' c KREL3 MP3 MI3 ST3 AUX3 HP3 LM3 STP3 NEW3 F3 CTX3 ME3 VD3 DL3 EC3 EB3 EG3 ERR3 XP3.
    unfold SP' in ST3, XP3. rewrite (unsigned_lit (bv_unsigned sp + -2352)) in ST3, XP3 by (clear - SPR LO STK0 LO0; lia). change (bv_unsigned sp + -2352) with SPc in ST3, XP3.
    pose proof (dwk_after_raise [] NB S' M' LE fr j3 m2 mo2 s2' m3 mo3 s3' LEn M'' errv3 DW2 KREL3 MP3 MI3 ST3 AUX3 HP3 LM3 STP3 NEW3 F3 CTX3 EC3 EB3 EG3 ERR3 XP3) as DW3.
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL3| eapply ft_x5; exact MI3|]. intros ms4 ->.
    eapply ERRL; [exact DW3| exact FSZ| left; reflexivity].
  Qed.

  (* [comment removed for export] *)
  Lemma rp_tailYn : forall Lx NB S' M' LE fr j3 m1 mo1 s1' (line reason ee : Z) (oe : option entrep)
      (u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 s6w s8w s9w s10w s11w u3 u4 u5 u6 : word),
    DWKG Lx NB S' M' LE fr j3 m1 mo1 s1' -> cells_size fr = 112%nat -> 0 <= line < 2^31 -> 0 < reason < 2^23 ->
    match oe with None => ee = 0 /\ Lx = [] | Some E => ENTRYobj (DREST Lx NB LE) m1 ee E /\ Permutation (blocks_ENTRY ee E) Lx end ->
    DBUD (DREST Lx NB LE) M' ERRDEBUG_BYTES 2 0 ->
    hs_SR H POSTc (mkCfg (MS (mkR (Z_to_bv 64 DF_TY_R1) (Z_to_bv 64 SPc) gp (Z_to_bv 64 RATP) u0 u1 u2 sp (Z_to_bv 64 A) b0 b1 b2 b3 b4 b5 b6 b7
                                (Z_to_bv 64 bt) (Z_to_bv 64 Bb) (Z_to_bv 64 line) (Z_to_bv 64 reason) s6w (Z_to_bv 64 ee) s8w s9w s10w s11w u3 u4 u5 u6)
                           F (Z_to_bv 64 P_ERR_new) fc None m1 (seg_rom rsegs)) mo1).
  Proof using A0 A1 SO SE SEO STL MBO MP0 MN0 MBB MBS DS DSL PAYL NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC BUDG AUX SPB BHI SPA ST CEIL LO ERR MI TP RAE HH HX NAR NBR MST POS BTR BT_frame PERM BTFREE CERTO3.
    intros until u6. intros DW FSZ LNR REAS OE BD.
    pose proof DW as (HP1 & KREL1 & MP1 & LM1 & STP1 & _ & CTX1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & [errv1 ERR1] & MI1 & ST1 & AUX1 & _).
    destruct RCFACTS as (SEQ & SIN & SBR & BEL0 & SUB0 & ND0 & STK0 & LO0 & MF0 & OBJ0 & DJA). hcb. pose proof (word_range sp) as SPR.
    destruct (dbud_raise _ _ _ _ _ _ _ _ _ _ _ _ _ DW BD ltac:(unfold ERRDEBUG_BYTES; clear; lia) ltac:(clear; lia) ltac:(clear; lia)) as (_ & _ & _ & RB1 & RB2 & RB3 & _).
    destruct (dwk_lib_facts _ _ _ _ _ _ _ _ _ _ DW) as (MFa & IMa & GMa & GEa & MMa & MBa & RLa & Fa & CXa).
    pose proof (dec_stack M M' STP1) as (_ & _ & STKR & _).
    pose proof (DRESTSUB Lx NB LE) as (SLB & S0 & SLE & SNB & STB & IB & IA & SLX & S3 & SLL).
    pose proof S_echs_func_lens as [_ FL].
    eapply rp_raise2 with (LIBc := LE ++ LIB) (Lc := DREST Lx NB LE) (Mq := M') (xq := x) (loq := lo) (Bq := B) (line := line) (reason := reason)
                               (func := A_ECHS_FUNC_DF) (gs := S_echs_func_df) (gsl := K_echs_func_df) (ra2 := DF_TY_R2) (ra3 := DF_TX).
    all: try first [exact HP1| exact KREL1| exact LM1| exact (fun b Hb => S0 b (SLL b Hb))| exact CXa| exact Fa| exact AUX1| exact ERR1| exact MI1| exact CEIL| exact R_echs_func_df| exact RB1| exact RB2| exact RB3| exact LNR| exact REAS].
    all: lazymatch goal with
         | |- bv_unsigned _ <= B => unfold SP'; rewrite unsigned_lit by (clear - SPR LO STK0 LO0; lia); clear - SPB; lia
         | |- bv_unsigned _ mod 16 = 0 => unfold SP'; rewrite unsigned_lit by (clear - SPR LO STK0 LO0; lia); clear - SPA; lia
         | |- stk _ _ _ _ => unfold SP'; rewrite unsigned_lit by (clear - SPR LO STK0 LO0; lia); exact ST1
         | |- lo <= _ => unfold SP'; rewrite unsigned_lit by (clear - SPR LO STK0 LO0; lia); clear - LO STKR; lia
         | |- _ <> [] => vm_compute; discriminate
         | |- Z.of_nat (length S_echs_func_df) < 32 => rewrite FL; clear; lia
         | |- 0 < A_ECHS_FUNC_DF => unfold A_ECHS_FUNC_DF; clear; lia
         | |- 0 <= _ < 2 ^ 64 => unfold DF_TY_R1, DF_TY_R2, DF_TX; clear; lia
         | |- _ mod 2 = 0 => reflexivity
         | |- lb_big _ + _ <= _ => clear - RB3; lia
         | |- rglue _ _ P_ERR_set_debug _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => apply ft_y2
         | |- rglue _ _ P_ERR_set_error _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => apply ft_y3
         | |- _ => idtac
         end.
    intros u7 u8 u9 d0 d1 d2 d3 d4 d5 d6 d7 u10 u11 u12 u13 m3 mo3 s3' errv3 LEn M'' c KREL3 MP3 MI3 ST3 AUX3 HP3 LM3 STP3 NEW3 F3 CTX3 ME3 VD3 DL3 EC3 EB3 EG3 ERR3 XP3.
    unfold SP' in ST3, XP3. rewrite (unsigned_lit (bv_unsigned sp + -2352)) in ST3, XP3 by (clear - SPR LO STK0 LO0; lia). change (bv_unsigned sp + -2352) with SPc in ST3, XP3.
    pose proof (dwk_after_raise Lx NB S' M' LE fr j3 m1 mo1 s1' m3 mo3 s3' LEn M'' errv3 DW KREL3 MP3 MI3 ST3 AUX3 HP3 LM3 STP3 NEW3 F3 CTX3 EC3 EB3 EG3 ERR3 XP3) as DW3.
    replace (ret_pc (Z_to_bv 64 DF_TX)) with (Z_to_bv 64 DF_TX) by (symmetry; apply ret_pc_even; [unfold DF_TX; lia| reflexivity]).
    eapply (rp_tailX Lx NB S' M'' (LEn ++ LE) fr j3 m3 mo3 s3' ee oe); [exact DW3| exact FSZ| |].
    - (* [comment removed for export] *)
      destruct oe as [E|]; [| exact OE]. destruct OE as [EO PE]. split; [| exact PE].
      eapply ENTRYobj_LB_mono.
      + eapply ENTRYobj_frameX; [exact EO| exact XP3|]. intros b Hb. eapply (lx_avoids Lx); [exact DW|]. eapply Permutation_in; [exact PE| exact Hb].
      + intros b Hb. eapply Permutation_in; [apply drest_LEn_perm|]. apply in_or_app. right. exact Hb.
    - (* [comment removed for export] *)
      pose proof (errph_delta_bounds _ _ _ DL3) as (LEc & LEb & LEg). rewrite <- ME3 in LEc, LEb, LEg.
      revert BD LEc LEb LEg. unfold dbud. lbnorm. clear. intros (B1 & B2 & B3) LEc LEb LEg. lia.
  Qed.


  (* [comment removed for export] *)
  Lemma rp_tailY : forall NB S' M' LE fr j3 m1 mo1 s1' (line reason : Z)
      (rax u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 s6w s8w s9w s10w s11w u3 u4 u5 u6 : word),
    DWKG [] NB S' M' LE fr j3 m1 mo1 s1' -> cells_size fr = 112%nat -> 0 <= line < 2^31 -> 0 < reason < 2^23 ->
    DBUD (DREST [] NB LE) M' ERRDEBUG_BYTES 2 0 ->
    hs_SR H POSTc (mkCfg (MS (mkR rax (Z_to_bv 64 SPc) gp (Z_to_bv 64 RATP) u0 u1 u2 sp (Z_to_bv 64 A) b0 b1 b2 b3 b4 b5 b6 b7
                                (Z_to_bv 64 bt) (Z_to_bv 64 Bb) (Z_to_bv 64 line) (Z_to_bv 64 reason) s6w (Z_to_bv 64 0) s8w s9w s10w s11w u3 u4 u5 u6)
                           F (Z_to_bv 64 DF_TY) fc None m1 (seg_rom rsegs)) mo1).
  Proof using A0 A1 SO SE SEO STL MBO MP0 MN0 MBB MBS DS DSL PAYL NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC BUDG AUX SPB BHI SPA ST CEIL LO ERR MI TP RAE HH HX NAR NBR MST POS BTR BT_frame PERM BTFREE CERTO3.
    intros until u6. intros DW FSZ LNR REAS BD.
    pose proof DW as (_ & KREL1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MI1 & _).
    eapply (sr_evt_krel H HH); [exact KREL1| eapply ft_y1; exact MI1|]. intros ms2 ->.
    eapply (rp_tailYn [] NB S' M' LE fr j3 m1 mo1 s1' line reason 0 None); [exact DW| exact FSZ| exact LNR| exact REAS| split; reflexivity| exact BD].
  Qed.

  (* [comment removed for export] *)
  Lemma rp_tailZ : DK_TZ.
  Proof using A0 A1 SO SE SEO STL MBO MP0 MN0 MBB MBS DS DSL PAYL NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC BUDG AUX SPB BHI SPA ST CEIL LO ERR MI TP RAE HH HX NAR NBR MST POS BTR BT_frame PERM BTFREE CERTO3.
    unfold dK_tailZ.
    intros Lx NB S' M' LE w0 w1 w3 w4 w5 w6 w9 w10 j3 m1 mo1 s1' ee E rax u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 s4w s5w s6w s8w s9w s10w s11w u3 u4 u5 u6 DW EO PE BD.
    pose proof DW as (_ & KREL1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MI1 & _).
    destruct (dbud_raise _ _ _ _ _ _ _ _ _ _ _ _ _ DW BD ltac:(unfold ERRDEBUG_BYTES; clear; lia) ltac:(clear; lia) ltac:(clear; lia)) as (_ & _ & _ & _ & _ & _ & BD0).
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL1| eapply ft_z1; exact MI1|]. intros ms2 ->.
    eapply (rp_efree Lx NB S' M' LE (dframe st w0 w1 w3 w4 w5 w6 w9 w10) j3 m1 mo1 s1' ee (Some E) DF_TZ_R); [exact DW| split; [exact EO| exact PE]| unfold DF_TZ_R; clear; lia| reflexivity|].
    clear DW KREL1 MI1. intros m2 mo2 s2' v0 v1 v2 c0 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 DW2.
    pose proof DW2 as (_ & KREL2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MI2 & _).
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL2| eapply ft_z2; exact MI2|]. intros ms3 [a0' ->].
    eapply (rp_tailYn [] NB S' M' LE (dframe st w0 w1 w3 w4 w5 w6 w9 w10) j3 m2 mo2 s2' 520 R_INTERNAL_ERROR 0 None); [exact DW2| reflexivity| clear; lia| unfold R_INTERNAL_ERROR; clear; lia| split; reflexivity| exact BD0].
  Qed.

  (* [comment removed for export] *)
  Lemma rp_tailA : DK_TA.
  Proof using A0 A1 SO SE SEO STL MBO MP0 MN0 MBB MBS DS DSL PAYL NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC BUDG AUX SPB BHI SPA ST CEIL LO ERR MI TP RAE HH HX NAR NBR MST POS BTR BT_frame PERM BTFREE CERTO3.
    unfold dK_tailA.
    intros Lx NB S' M' LE w0 w1 w3 w4 w5 w6 w9 w10 j3 m1 mo1 s1' ee line E rax u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 s4w s5w s6w s8w s9w s10w u3 u4 u5 u6 DW EO PE LNR BD.
    pose proof DW as (HP1 & KREL1 & MP1 & LM1 & STP1 & _ & CTX1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & [errv1 ERR1] & MI1 & ST1 & AUX1 & _).
    destruct RCFACTS as (SEQ & SIN & SBR & BEL0 & SUB0 & ND0 & STK0 & LO0 & MF0 & OBJ0 & DJA). hcb. pose proof (word_range sp) as SPR.
    destruct (dbud_raise _ _ _ _ _ _ _ _ _ _ _ _ _ DW BD ltac:(unfold ERRDEBUG_BYTES; clear; lia) ltac:(clear; lia) ltac:(clear; lia)) as (_ & _ & _ & RB1 & RB2 & RB3 & _).
    destruct (dwk_lib_facts _ _ _ _ _ _ _ _ _ _ DW) as (MFa & IMa & GMa & GEa & MMa & MBa & RLa & Fa & CXa).
    pose proof (dec_stack M M' STP1) as (_ & _ & STKR & _).
    pose proof (DRESTSUB Lx NB LE) as (SLB & S0 & SLE & SNB & STB & IB & IA & SLX & S3 & SLL).
    pose proof S_echs_func_lens as [FL _].
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL1| eapply ft_a1; exact MI1|]. intros ms2 ->.
    eapply rp_raise2 with (LIBc := LE ++ LIB) (Lc := DREST Lx NB LE) (Mq := M') (xq := x) (loq := lo) (Bq := B) (line := line) (reason := R_ECH_DECODE_ERROR)
                               (func := A_ECHS_FUNC_D1) (gs := S_echs_func_d1) (gsl := K_echs_func_d1) (ra2 := DF_TA_R2) (ra3 := DF_TZ).
    all: try first [exact HP1| exact KREL1| exact LM1| exact (fun b Hb => S0 b (SLL b Hb))| exact CXa| exact Fa| exact AUX1| exact ERR1| exact MI1| exact CEIL| exact R_echs_func_d1| exact RB1| exact RB2| exact RB3| exact LNR].
    all: lazymatch goal with
         | |- bv_unsigned _ <= B => unfold SP'; rewrite unsigned_lit by (clear - SPR LO STK0 LO0; lia); clear - SPB; lia
         | |- bv_unsigned _ mod 16 = 0 => unfold SP'; rewrite unsigned_lit by (clear - SPR LO STK0 LO0; lia); clear - SPA; lia
         | |- stk _ _ _ _ => unfold SP'; rewrite unsigned_lit by (clear - SPR LO STK0 LO0; lia); exact ST1
         | |- lo <= _ => unfold SP'; rewrite unsigned_lit by (clear - SPR LO STK0 LO0; lia); clear - LO STKR; lia
         | |- _ <> [] => vm_compute; discriminate
         | |- Z.of_nat (length S_echs_func_d1) < 32 => rewrite FL; clear; lia
         | |- 0 < A_ECHS_FUNC_D1 => unfold A_ECHS_FUNC_D1; clear; lia
         | |- 0 < R_ECH_DECODE_ERROR < _ => unfold R_ECH_DECODE_ERROR; clear; lia
         | |- 0 <= _ < 2 ^ 64 => unfold DF_TA_R1, DF_TA_R2, DF_TZ; clear; lia
         | |- _ mod 2 = 0 => reflexivity
         | |- lb_big _ + _ <= _ => clear - RB3; lia
         | |- rglue _ _ P_ERR_set_debug _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => apply ft_a2
         | |- rglue _ _ P_ERR_set_error _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => apply ft_a3
         | |- _ => idtac
         end.
    intros u7 u8 u9 d0 d1 d2 d3 d4 d5 d6 d7 u10 u11 u12 u13 m3 mo3 s3' errv3 LEn M'' c KREL3 MP3 MI3 ST3 AUX3 HP3 LM3 STP3 NEW3 F3 CTX3 ME3 VD3 DL3 EC3 EB3 EG3 ERR3 XP3.
    unfold SP' in ST3, XP3. rewrite (unsigned_lit (bv_unsigned sp + -2352)) in ST3, XP3 by (clear - SPR LO STK0 LO0; lia). change (bv_unsigned sp + -2352) with SPc in ST3, XP3.
    pose proof (dwk_after_raise Lx NB S' M' LE (dframe st w0 w1 w3 w4 w5 w6 w9 w10) j3 m1 mo1 s1' m3 mo3 s3' LEn M'' errv3 DW KREL3 MP3 MI3 ST3 AUX3 HP3 LM3 STP3 NEW3 F3 CTX3 EC3 EB3 EG3 ERR3 XP3) as DW3.
    replace (ret_pc (Z_to_bv 64 DF_TZ)) with (Z_to_bv 64 DF_TZ) by (symmetry; apply ret_pc_even; [unfold DF_TZ; lia| reflexivity]).
    pose proof rp_tailZ as TZ. unfold dK_tailZ in TZ.
    eapply (TZ Lx NB S' M'' (LEn ++ LE) w0 w1 w3 w4 w5 w6 w9 w10 j3 m3 mo3 s3' ee E); clear TZ; [exact DW3| | exact PE|].
    - (* [comment removed for export] *)
      eapply ENTRYobj_LB_mono.
      + eapply ENTRYobj_frameX; [exact EO| exact XP3|]. intros b Hb. eapply (lx_avoids Lx); [exact DW|]. eapply Permutation_in; [exact PE| exact Hb].
      + intros b Hb. eapply Permutation_in; [apply drest_LEn_perm|]. apply in_or_app. right. exact Hb.
    - pose proof (errph_delta_bounds _ _ _ DL3) as (LEc & LEb & LEg). rewrite <- ME3 in LEc, LEb, LEg.
      revert BD LEc LEb LEg. unfold dbud. lbnorm. clear. intros (B1 & B2 & B3) LEc LEb LEg. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition eframe (u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 : word) : list cell :=
    [C8 u0; C8 u1; C8 u2; C8 u3; C8 u4; C8 u5; C8 u6; C8 u7; C8 u8; C8 u9; C8 u10; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 st); C8 (Z_to_bv 64 0)].
  Lemma dframe_eframe : forall w0 w1 w3 w4 w5 w6 w9 w10,
    dframe st w0 w1 w3 w4 w5 w6 w9 w10 = eframe w0 w1 (wz R_INTERNAL_ERROR) w3 w4 w5 w6 (wz ECH_VERSION) (wz A_ECHS_FILE_RP) w9 w10.
  Proof. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma dwkG_fr : forall Lx NB S' M' LE fr fr' j3 m' mo' s',
    DWKG Lx NB S' M' LE fr j3 m' mo' s' -> rw_cells rsegs m' SPc fr' -> DWKG Lx NB S' M' LE fr' j3 m' mo' s'.
  Proof.
    clear. intros until s'. intros DW FR'.
    pose proof DW as (HP1 & KREL1 & MP1 & LM1 & STP & NEW & CTX1 & EC & EB & EG & LC & LBY & LG & SO1 & SID & SPM & SND & SKI & MBO1 & DSm1 & DSb1 & BT1
                      & FR0 & FR2 & FR3 & FR4 & ERR1 & MI1 & ST1 & AUX1 & XA1 & DNB1).
    unfold dwkG. repeat match goal with |- _ /\ _ => split end; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma skb_facts : forall Lx NB S' M' LE fr j3 m' mo' s',
    DWKG Lx NB S' M' LE fr j3 m' mo' s' ->
    Permutation NB (SKB S' ++ EBS S') /\ Z.of_nat (length (SKB S')) <= 2 /\ 0 <= lb_bytes (SKB S') <= 88 + 16 * nent S' /\ (nent S' <= 100 -> lb_big (SKB S') = 0) /\ 0 <= nent S'.
  Proof.
    clear. intros until s'. intros DW.
    pose proof DW as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SO1 & SID & SPM & SND & SKI & _).
    split.
    { rewrite blocks_STORE_split, SID in SPM. exact (Permutation_sym (Permutation_cons_inv SPM)). }
    unfold SKB, EBS, nent. destruct SO1 as (_ & _ & EN). destruct (es_entries_o S') as [[K es]|] eqn:EO.
    - destruct EN as (PP & SO & LEN & _). pose proof SO as (_ & _ & _ & (N1 & N2) & C20 & _ & _ & KD).
      destruct (SKI K es eq_refl) as [_ CAP]. rewrite <- LEN in CAP. unfold sk_num, zlength in N1, N2.
      unfold blocks_SK. destruct (Z.eqb_spec (sk_cap K) 0) as [C0|CN]; rewrite ?lb_bytes_cons, ?lb_big_cons; cbn [length blk_size snd lb_bytes lb_big fold_right app Z.add];
        rewrite (big1_small SK_SIZE) by (unfold SK_SIZE, BIGB; clear; lia); unfold SK_SIZE.
      + clear - N1. lia.
      + split; [clear; lia|]. split; [clear - CAP N1 N2 CN; lia|]. split; [| clear; lia]. intros NE. rewrite (big1_small (8 * sk_cap K)) by (unfold BIGB; clear - CAP NE N1; lia). reflexivity.
    - cbn. clear. lia.
  Qed.

  Lemma nb_ledger : forall Lx NB S' M' LE fr j3 m' mo' s' c,
    DWKG Lx NB S' M' LE fr j3 m' mo' s' -> dledger S' c -> c <= 1500 ->
    lb_bytes NB <= 36 * c + 88 /\ 5 * Z.of_nat (length NB) <= 2 * c + 10 /\ lb_big NB <= c / 600 /\ 0 <= c /\ 0 <= nent S' /\ 23 * nent S' <= c.
  Proof.
    clear. intros until c. intros DW (L1 & L2 & L3 & L4 & L5) CLE.
    destruct (skb_facts _ _ _ _ _ _ _ _ _ _ DW) as (PNB & KL & KB & KG & N0).
    rewrite (lb_bytes_perm _ _ PNB), (lb_big_perm _ _ PNB), (Permutation_length PNB), lb_bytes_app, lb_big_app, length_app, Nat2Z.inj_add.
    assert (NE : nent S' <= 100) by (clear - L4 L5 N0 CLE; lia). rewrite (KG NE). clear - L1 L2 L3 L4 L5 KL KB N0. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma rp_done : forall NB S' M' LE u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 j3 m1 mo1 s1'
      (rax a0w v0 v1 v2 b1 b2 b3 b4 b5 b6 b7 s4w s5w s6w s7w s8w s9w s10w s11w v3 v4 v5 v6 : word),
    DWKG [] NB S' M' LE (eframe u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10) j3 m1 mo1 s1' ->
    hs_SR H POSTc (mkCfg (MS (mkR rax (Z_to_bv 64 SPc) gp (Z_to_bv 64 RATP) v0 v1 v2 sp (Z_to_bv 64 A) a0w b1 b2 b3 b4 b5 b6 b7
                                (Z_to_bv 64 bt) (Z_to_bv 64 Bb) s4w s5w s6w s7w s8w s9w s10w s11w v3 v4 v5 v6)
                           F (Z_to_bv 64 DF_DONE) fc None m1 (seg_rom rsegs)) mo1).
  Proof using A0 A1 SO SE SEO STL MBO MP0 MN0 MBB MBS DS DSL PAYL NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC BUDG AUX SPB BHI SPA ST CEIL LO ERR MI TP RAE HH HX NAR NBR MST POS BTR BT_frame PERM BTFREE CERTO3.
    intros until v6. intros DW.
    pose proof DW as (_ & KREL1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MI1 & _).
    destruct RCFACTS as (SEQ & SIN & SBR & BEL0 & SUB0 & ND0 & STK0 & LO0 & MF0 & OBJ0 & DJA). pose proof (word_range sp) as SPR.
    eapply (sr_evt_krel H HH); [exact KREL1| eapply fs_done; exact MI1|]. intros ms2 ->.
    eapply (rp_efree [] NB S' M' LE _ j3 m1 mo1 s1' 0 None DF_R_DONE); [exact DW| split; reflexivity| unfold DF_R_DONE; clear; lia| reflexivity|].
    clear DW KREL1 MI1. intros m2 mo2 s2' t0' t1' t2' c0 c1 c2 c3 c4 c5 c6 c7 t3' t4' t5' t6' DW2.
    pose proof DW2 as (_ & KREL2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FR0 & _ & _ & _ & _ & MI2 & _).
    eapply (sr_evt_krel H HH); [exact KREL2| unfold SP'; eapply fs_done2g; [clear - SPR LO STK0 LO0; lia| exact FR0| exact MI2]|]. intros ms3 ->. fold (SP' sp).
    eapply ERRL; [exact DW2| reflexivity| right; reflexivity].
  Qed.

  (* [comment removed for export] *)
  Lemma dledger_mono : forall S' c c', dledger S' c -> c <= c' -> dledger S' c'.
  Proof.
    clear. intros S' c c' (L1 & L2 & L3 & L4 & L5) LE'. pose proof (lb_big_nonneg (EBS S')).
    unfold dledger. pose proof (Z.div_le_mono c c' 600 ltac:(lia) LE'). repeat split; lia.
  Qed.

  Section LOOP.
    (* [comment removed for export] *)
    Hypothesis TR : 32 <= zlength bs < 1500.
    Hypothesis OLEN : 1 <= olen_of bs <= zlength bs - 2.
    (* [comment removed for export] *)
    Hypothesis BUD0 : lb_bytes TB + nB + nA + lb_bytes LB + errph_bytes (mid_err M) + ERRSTR_BYTES + DLOOP_BYTES <= hs_LIVE_MAX H.
    Hypothesis CNT0 : Z.of_nat (length TB) + 2 + Z.of_nat (length LB) + errph_cnt (mid_err M) + ERRSTR_CNT + DLOOP_CNT <= hs_LIVE_CNT_MAX H.
    Hypothesis BIG0 : lb_big TB + big1 nB + big1 nA + lb_big LB + errph_big (mid_err M) + DLOOP_BIG <= hs_LIVE_BIG_MAX H.

    (* [comment removed for export] *)
    Lemma dbud_now : forall Lx NB S' M' LE fr j3 m' mo' s' hb hc hg,
      DWKG Lx NB S' M' LE fr j3 m' mo' s' ->
      lb_bytes Lx + lb_bytes NB + hb <= DLOOP_BYTES -> Z.of_nat (length Lx) + Z.of_nat (length NB) + hc <= DLOOP_CNT -> lb_big Lx + lb_big NB + hg <= DLOOP_BIG ->
      DBUD (DREST Lx NB LE) M' hb hc hg.
    Proof using BUD0 CNT0 BIG0.
      intros until hg. intros DW B1 B2 B3.
      pose proof DW as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LC & LBY & LG & _).
      revert B1 B2 B3 LC LBY LG BUD0 CNT0 BIG0. unfold dbud. lbnorm. clear. intros. lia.
    Qed.

    (* [comment removed for export] *)
    Definition LOOPAT (n : nat) : Prop :=
      forall (cur rem c : Z) NB S' M' LE w0 w1 w3 w4 w5 w6 w9 w10 j3 m' mo' s'
             (rax u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 s5w s6w s7w s8w s9w s11w u3 u4 u5 u6 : word),
        rem <= Z.of_nat n ->
        DWK [] NB S' M' LE w0 w1 w3 w4 w5 w6 w9 w10 j3 m' mo' s' -> dledger S' c -> cur = Bb + 2 + c -> c + rem = olen_of bs -> 1 <= rem ->
        hs_SR H POSTc (mkCfg (MS (mkR rax (Z_to_bv 64 SPc) gp (Z_to_bv 64 RATP) u0 u1 u2 sp (Z_to_bv 64 A) b0 b1 b2 b3 b4 b5 b6 b7
                                    (Z_to_bv 64 bt) (Z_to_bv 64 Bb) (Z_to_bv 64 rem) s5w s6w s7w s8w s9w (Z_to_bv 64 cur) s11w u3 u4 u5 u6)
                               F (Z_to_bv 64 DF_LOOP) fc None m' (seg_rom rsegs)) mo').

    (* [comment removed for export] *)
    Lemma rp_trip_adv : forall n (cur rem c elen : Z) NB S' M' LE w0 w1 w3 w4 w5 w6 j3 m' mo' s'
        (rax u0 u1 u2 a0w b1 b2 b3 b4 b5 b6 b7 s4w s6w s7w s8w s9w s10w s11w u3 u4 u5 u6 : word),
      LOOPAT n -> rem - 4 - elen <= Z.of_nat n ->
      DWK [] NB S' M' LE w0 w1 w3 w4 w5 w6 (Z_to_bv 64 (rem - 4)) (Z_to_bv 64 elen) j3 m' mo' s' ->
      dledger S' (c + 4 + elen) -> cur = Bb + 2 + c -> c + rem = olen_of bs -> 0 <= elen -> 4 + elen <= rem -> 0 <= c ->
      hs_SR H POSTc (mkCfg (MS (mkR rax (Z_to_bv 64 SPc) gp (Z_to_bv 64 RATP) u0 u1 u2 sp (Z_to_bv 64 A) a0w b1 b2 b3 b4 b5 b6 b7
                                  (Z_to_bv 64 bt) (Z_to_bv 64 Bb) s4w (Z_to_bv 64 (cur + 4)) s6w s7w s8w s9w s10w s11w u3 u4 u5 u6)
                             F (Z_to_bv 64 DF_ADV) fc None m' (seg_rom rsegs)) mo').
    Proof using TR OLEN BUD0 CNT0 BIG0 A0 A1 SO SE SEO STL MBO MP0 MN0 MBB MBS DS DSL PAYL NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC BUDG AUX SPB BHI SPA ST CEIL LO ERR MI TP RAE HH HX NAR NBR MST POS BTR BT_frame PERM BTFREE RPE CERTO3 TIME.
      intros until u6. intros LP REM DW LED CUR CR E0 ER C0.
      pose proof DW as (HP1 & KREL1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FR0 & _ & _ & _ & _ & MI1 & _).
      destruct RCFACTS as (SEQ & SIN & SBR & BEL0 & SUB0 & ND0 & STK0 & LO0 & MF0 & OBJ0 & DJA). hcb. pose proof (word_range sp) as SPR.
      destruct (DWKGF _ _ _ _ _ _ _ _ _ _ DW) as (HB & ND & DISJ & BRS & D2 & D1).
      pose proof (DRESTSUB ([] : list block) NB LE) as (_ & _ & _ & _ & _ & IB0 & _).
      pose proof (BRS _ ltac:(apply in_or_app; right; exact IB0)) as (BP & _ & _ & BH & _). cbn [blk_addr blk_size fst snd] in BP, BH.
      eapply (sr_evt_krel H HH); [exact KREL1| unfold SP'; eapply fs_adv with (cur := cur) (rem := rem) (elen := elen);
        [exact E0| exact ER| clear - CR OLEN TR C0; lia| clear - CUR C0 BP; lia| unfold zlength in NBR; clear - CUR CR OLEN TR BH NBR HCEILB C0; lia
        | clear - SPR LO STK0 LO0; lia| exact FR0| exact MI1]|].
      cbv beta. intros ms2 [a0' ->]. fold (SP' sp).
      destruct (Z.eqb_spec (rem - 4 - elen) 0) as [Z0|NZ].
      - eapply rp_done. exact DW.
      - eapply (LP (cur + 4 + elen) (rem - 4 - elen) (c + 4 + elen)); [exact REM| exact DW| exact LED| clear - CUR; lia| clear - CR; lia| clear - NZ ER; lia].
    Qed.

    (* [comment removed for export] *)
    Lemma rp_trip_skip : forall n cur rem c NB S',
      LOOPAT n -> rem - 4 <= Z.of_nat n -> dledger S' c -> cur = Bb + 2 + c -> c + rem = olen_of bs -> DK_SKIP cur rem NB S'.
    Proof using TR OLEN BUD0 CNT0 BIG0 A0 A1 SO SE SEO STL MBO MP0 MN0 MBB MBS DS DSL PAYL NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC BUDG AUX SPB BHI SPA ST CEIL LO ERR MI TP RAE HH HX NAR NBR MST POS BTR BT_frame PERM BTFREE RPE CERTO3 TIME.
      intros n cur rem c NB S' LP REM LED CUR CR. unfold dK_skip.
      intros M' LE w0 w1 w3 w4 w5 w6 j3 m' mo' s' elen rax u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 s4w s6w s7w s8w s9w s10w s11w u3 u4 u5 u6 DW E0 ER.
      pose proof LED as (_ & _ & _ & _ & C0).
      eapply (rp_trip_adv n cur rem c elen); [exact LP| clear - REM E0; lia| exact DW| eapply dledger_mono; [exact LED| clear - E0; lia]| exact CUR| exact CR| exact E0| exact ER| exact C0].
    Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma xpres_time : forall Lx NB S' M' LE fr j3 m1 mo1 s1' m2,
    DWKG Lx NB S' M' LE fr j3 m1 mo1 s1' ->
    munch [(SPc - TIME_STACK, SPc); (A_vdso_func, A_vdso_func + 8); (RERRNO, RERRNO + 4)] m1 m2 -> wmono rsegs m1 m2 ->
    xpres (DREST Lx NB LE) SPc VDSO_X m1 m2.
  Proof using HH SUBL CEIL LO.
    intros until m2. intros DW MU WM.
    pose proof DW as (_ & _ & _ & _ & STP & _).
    destruct (DWKGF _ _ _ _ _ _ _ _ _ _ DW) as (HB & ND & DISJ & BRS & D2 & D1). hcb. pose proof (readcfg_stack_lo M) as STK0.
    pose proof (dec_stack M M' STP) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & K11).
    eapply xpres_of_munch_gen; [exact MU| exact WM|]. intros a Ha [HC HXv]. cbn [outside fst snd].
    assert (NV : ~ (ECH_Img.A_vdso_func <= a < ECH_Img.A_vdso_func + 8)) by (intros K; apply HXv; unfold VDSO_X; cbn [rin_ivs fst snd]; left; exact K).
    destruct HC as [HC|[[HC NS]|(b & Hb & Hr)]].
    - unfold SP', ECH_Img.A_vdso_func, F_time.A_vdso_func, RERRNO, TIME_STACK in *. clear - HC NV LO STK0 CEIL HCEILB. repeat split; lia.
    - unfold ralloc_static, RERRNO, ECH_Img.A_vdso_func, F_time.A_vdso_func, SP', TIME_STACK in *. clear - HC NS NV LO STK0 CEIL HCEILB. repeat split; lia.
    - pose proof (HB b ltac:(apply in_or_app; right; exact Hb)) as E. pose proof (BRS b ltac:(apply in_or_app; right; exact Hb)) as (_ & _ & _ & _ & O).
      unfold SP', ECH_Img.A_vdso_func, F_time.A_vdso_func, RERRNO, TIME_STACK, READCFG_STACK in *. clear - Hr E O LO K11 STK0 CEIL. repeat split; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma dwk_time : forall Lx NB S' M' LE fr j3 m1 mo1 s1' m2 mo2 errv2,
    DWKG Lx NB S' M' LE fr j3 m1 mo1 s1' ->
    hs_KREL H s1' mo2 -> hs_MPRES H mo1 mo2 -> mem_inv rsegs m2 -> stk rsegs m2 lo SPc -> hs_rauxv_ok H m2 B ->
    hs_RHEAP H s1' (mid_errblocks M' ++ DREST Lx NB LE) m2 ->
    munch [(SPc - TIME_STACK, SPc); (A_vdso_func, A_vdso_func + 8); (RERRNO, RERRNO + 4)] m1 m2 -> wmono rsegs m1 m2 ->
    rw_cells rsegs m2 A_vdso_func [C8 (Z_to_bv 64 0)] -> rw_cells rsegs m2 RERRNO [C4 errv2] ->
    DWKG Lx NB S' (mkMID (mid_flag M') (mid_ctx M') (mid_err M') (mid_E M') true) LE fr j3 m2 mo2 s1'.
  Proof using A0 A1 SO SE SEO STL MBO MP0 MN0 MBB MBS DS DSL PAYL NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC BUDG AUX SPB BHI SPA ST CEIL LO ERR MI TP RAE HH HX NAR NBR MST POS BTR BT_frame PERM.
    intros until errv2. intros DW KREL2 MP2 MI2 ST2 AUX2 HP2 MU WM VD2 ERR2.
    pose proof DW as (HP1 & KREL1 & MP1 & LM1 & STP & NEW & CTX1 & EC & EB & EG & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FR0 & FR2 & FR3 & FR4 & _ & MI1 & _).
    destruct (DWKGF _ _ _ _ _ _ _ _ _ _ DW) as (HB & ND & DISJ & BRS & D2 & D1).
    destruct RCFACTS as (SEQ & SIN & SBR & BEL0 & SUB0 & ND0 & STK0 & LO0 & MF0 & OBJ0 & DJA). hcb. pose proof (word_range sp) as SPR.
    pose proof (DRESTSUB Lx NB LE) as (SLB & S0 & SLE & SNB & STB & IB & IA & SLX & S3 & SLL).
    pose proof (dec_stack M M' STP) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & K11).
    (* [comment removed for export] *)
    pose proof (xpres_time _ _ _ _ _ _ _ _ _ _ m2 DW MU WM) as XPv.
    assert (DJF : forall a n, SPc <= a -> disjoint_from [(SPc - TIME_STACK, SPc); (A_vdso_func, A_vdso_func + 8); (RERRNO, RERRNO + 4)] a n).
    { intros a n Ha. cbn. unfold SP', ECH_Img.A_vdso_func, F_time.A_vdso_func, RERRNO, TIME_STACK in *. clear - Ha LO STK0 CEIL HCEILB. repeat split; lia. }
    eapply (DWKGL Lx Lx NB S' M' _ LE [] fr j3 m1 mo1 s1' m2 mo2 s1' VDSO_X fr j3); [exact DW| | | | reflexivity| exact EC| exact EB| exact EG| | | exact HP2| exact KREL2
      | eapply (mpres_trans H HH); [exact MP1| exact MP2]| exists errv2; exact ERR2| exact MI2| exact ST2| exact AUX2| |].
    - cbn [app]. eapply LIBMID_agree_vdso; [exact LM1| | exact VD2].
      eapply magree_mono; [eapply magree_mid_of_xpres; [exact XPv| exact (fun b Hb => S0 b (SLL b Hb))]|]. intros a [Ha Hn]. split; [exact Ha|].
      intros K. apply Hn. unfold VDSO_X in K. cbn [rin_ivs fst snd] in K. unfold ECH_Img.A_vdso_func, F_time.A_vdso_func in *. clear - K. lia.
    - destruct STP as (F1 & _). unfold mid_step. cbn [mid_flag mid_ctx mid_err mid_vdso]. repeat split; auto.
    - exists [], []. cbn [mid_ctx mid_err app]. split; [apply Permutation_refl|]. split; [destruct (mid_ctx M'); reflexivity| destruct (mid_err M'); reflexivity].
    - eapply xpres_weaken; [exact XPv| clear; lia| intros b Hb; exact Hb| intros q Hq; apply rin_ivs_app; left; exact Hq].
    - apply Forall_cons; [right; right; right; reflexivity| apply Forall_nil].
    - eapply rw_cells_transport; [exact FR0| exact MU| exact WM| apply DJF; clear; lia].
    - eapply rw_cells_transport; [exact FR3| exact MU| exact WM| apply DJF; unfold O_F3; clear; lia].
  Qed.


  (* [comment removed for export] *)
  Lemma ent_blocks : forall Lx NB S' M' LE fr j3 m' mo' s' ee E,
    DWKG Lx NB S' M' LE fr j3 m' mo' s' -> Permutation (blocks_ENTRY ee E) Lx ->
       (forall b, In b (blocks_ENTRY ee E) -> In b (DREST Lx NB LE) /\ blk_addr b + blk_size b <= hceil /\ (blk_addr b + blk_size b <= IMG_LO \/ IMG_HI <= blk_addr b) /\ 0 < blk_addr b)
    /\ (forall b, In b (blocks_ENTRY ee E) -> b <> (en_id E, ee, ENTRY_SIZE) -> blk_addr b + blk_size b <= ee \/ ee + ENTRY_SIZE <= blk_addr b)
    /\ List.NoDup (map blk_id (blocks_ENTRY ee E)).
  Proof using HH SUBL.
    intros until E. intros DW PE.
    destruct (DWKGF _ _ _ _ _ _ _ _ _ _ DW) as (HB & ND & DISJ & BRS & D2 & D1).
    pose proof (DRESTSUB Lx NB LE) as (_ & _ & _ & _ & _ & _ & _ & SLX & _).
    assert (INE : forall b, In b (blocks_ENTRY ee E) -> In b (DREST Lx NB LE)) by (intros b Hb; apply SLX; eapply Permutation_in; [exact PE| exact Hb]).
    assert (NDE : List.NoDup (map blk_id (blocks_ENTRY ee E))).
    { eapply Permutation_NoDup; [apply Permutation_map; apply Permutation_sym; exact PE|].
      destruct (nd_app _ _ ND) as [_ ND1]. rewrite drest_app, map_app in ND1. exact (NoDup_app_remove_r _ _ ND1). }
    split; [| split; [| exact NDE]].
    - intros b Hb. pose proof (BRS b ltac:(apply in_or_app; right; apply INE; exact Hb)) as (P & _ & _ & _ & O).
      split; [apply INE; exact Hb|]. split; [apply HB; apply in_or_app; right; apply INE; exact Hb|]. unfold IMG_LO, IMG_HI. split; [exact O| exact P].
    - intros b Hb NE. assert (NI : blk_id b <> blk_id (en_id E, ee, ENTRY_SIZE)).
      { intros EQ. apply NE. eapply nodup_id_inj; [exact ND| apply in_or_app; right; apply INE; exact Hb| apply in_or_app; right; apply INE; left; reflexivity| exact EQ]. }
      pose proof (DISJ b (en_id E, ee, ENTRY_SIZE) ltac:(apply in_or_app; right; apply INE; exact Hb) ltac:(apply in_or_app; right; apply INE; left; reflexivity) NI) as D.
      cbn [blk_addr blk_size fst snd] in D. exact D.
  Qed.

  Lemma nodup_head_ne : forall (b0 b : block) l, List.NoDup (map blk_id (b0 :: l)) -> In b l -> b <> b0.
  Proof. clear. intros b0 b l ND Hb ->. cbn in ND. inversion ND as [|i l' NI ND1]; subst. apply NI. apply in_map. exact Hb. Qed.

  (* [comment removed for export] *)
  Lemma ent_sub : forall ee E ps sn pn nn,
    en_suites_o E = Some (ps, sn) -> en_pname_o E = Some (pn, nn) -> List.NoDup (map blk_id (blocks_ENTRY ee E)) ->
       In (ps, en_suites E, sn) (blocks_ENTRY ee E) /\ (ps, en_suites E, sn) <> (en_id E, ee, ENTRY_SIZE)
    /\ In (pn, en_pname E, nn) (blocks_ENTRY ee E) /\ (pn, en_pname E, nn) <> (en_id E, ee, ENTRY_SIZE).
  Proof.
    clear. intros ee E ps sn pn nn SUO PNO ND. unfold blocks_ENTRY in *. rewrite SUO, PNO in *. cbn [blocks_of app] in ND |- *.
    assert (K1 : In (ps, en_suites E, sn) ((pn, en_pname E, nn) :: blocks_of (en_pub E) (en_pub_o E) ++ (ps, en_suites E, sn) :: blocks_of (en_encoded E) (en_encoded_o E) ++ blocks_EXTS (en_exts E) (en_exts_o E))).
    { right. apply in_or_app. right. left. reflexivity. }
    assert (K2 : In (pn, en_pname E, nn) ((pn, en_pname E, nn) :: blocks_of (en_pub E) (en_pub_o E) ++ (ps, en_suites E, sn) :: blocks_of (en_encoded E) (en_encoded_o E) ++ blocks_EXTS (en_exts E) (en_exts_o E))).
    { left. reflexivity. }
    split; [right; exact K1|]. split; [exact (nodup_head_ne _ _ _ ND K1)|]. split; [right; exact K2| exact (nodup_head_ne _ _ _ ND K2)].
  Qed.

  (* [comment removed for export] *)
  Definition with_loadtime (E : entrep) (tv : Z) : entrep :=
    mkENT (en_version E) (en_pname E) (en_pname_o E) (en_publen E) (en_pub E) (en_pub_o E) (en_nsuites E) (en_suites E) (en_suites_o E)
          (en_maxname E) (en_cfgid E) (en_exts E) (en_exts_o E) tv (en_forretry E) (en_enclen E) (en_encoded E) (en_encoded_o E) (en_id E).
  Lemma blocks_with_loadtime : forall ee E tv, blocks_ENTRY ee (with_loadtime E tv) = blocks_ENTRY ee E.
  Proof. reflexivity. Qed.

  Lemma ENTRYobj_loadtime : forall Lx NB S' M' LE fr j3 m1 mo1 s1' ee E tv m2 pad1 pad2 pad3 pad4,
    DWKG Lx NB S' M' LE fr j3 m1 mo1 s1' -> ENTRYobj (DREST Lx NB LE) m1 ee E -> Permutation (blocks_ENTRY ee E) Lx ->
    munch [(ee + O_EN_LOADTIME, ee + 72)] m1 m2 -> wmono rsegs m1 m2 ->
    rw_cells rsegs m2 ee (entry_cells (with_loadtime E tv) pad1 pad2 pad3 pad4) ->
    length pad1 = 6%nat -> length pad2 = 4%nat -> length pad3 = 6%nat -> length pad4 = 4%nat ->
    ENTRYobj (DREST Lx NB LE) m2 ee (with_loadtime E tv) /\ xpres (DREST Lx NB LE) SPc [(ee + O_EN_LOADTIME, ee + 72)] m1 m2.
  Proof using HH SUBL.
    intros until pad4. intros DW EO PE MU WM EC L1 L2 L3 L4.
    destruct (ent_blocks _ _ _ _ _ _ _ _ _ _ ee E DW PE) as (EB1 & EB2 & NDE).
    assert (XP : xpres (DREST Lx NB LE) SPc [(ee + O_EN_LOADTIME, ee + 72)] m1 m2).
    { eapply xpres_of_munch_gen; [exact MU| exact WM|]. intros a Ha [_ HXa]. cbn [outside fst snd]. split; [| exact I].
      intros K. apply HXa. cbn [rin_ivs fst snd]. left. exact K. }
    split; [| exact XP].
    pose proof EO as (_ & HIN & O1 & O2 & O3 & O4 & XS). unfold ENTRYobj. cbn -[entry_cells ENTRY_SIZE EXTS ofield DREST].
    split; [exists pad1, pad2, pad3, pad4; split; [exact L1|]; split; [exact L2|]; split; [exact L3|]; split; [exact L4| exact EC]|].
    split; [exact HIN|]. split; [exact O1|]. split; [exact O2|]. split; [exact O3|]. split; [exact O4|].
    assert (AVX : forall b, In b (blocks_EXTS (en_exts E) (en_exts_o E)) -> avoids [(ee + O_EN_LOADTIME, ee + 72)] (blk_addr b) (blk_size b)).
    { intros b Hb. assert (HbE : In b (blocks_ENTRY ee E)) by (unfold blocks_ENTRY; right; do 4 (apply in_or_app; right); exact Hb).
      assert (NE : b <> (en_id E, ee, ENTRY_SIZE)).
      { eapply nodup_head_ne; [unfold blocks_ENTRY in NDE; exact NDE|]. do 4 (apply in_or_app; right). exact Hb. }
      pose proof (EB2 b HbE NE) as D. unfold avoids. apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. unfold O_EN_LOADTIME, ENTRY_SIZE in *. clear - D. lia. }
    revert XS AVX. unfold EXTS, blocks_EXTS. destruct (en_exts_o E) as [[K es]|]; intros XS AVX; [| exact XS].
    destruct XS as (PP & SKO & LEN & F2). split; [exact PP|]. split.
    - eapply SKobj_frameX; [exact SKO| intros b Hb; eapply SKobj_owned; [exact SKO| exact Hb]| exact XP|].
      intros b Hb. apply AVX. apply in_or_app. left. exact Hb.
    - split; [exact LEN|]. eapply EXTs_frameX; [exact F2| exact XP|]. intros b Hb. apply AVX. apply in_or_app. right. exact Hb.
  Qed.

    (* [comment removed for export] *)
    Lemma ENTRYs_mono : forall L L' m ps es, Forall2 (fun p E => ENTRYobj L m p E) ps es -> (forall b, In b L -> In b L') -> Forall2 (fun p E => ENTRYobj L' m p E) ps es.
    Proof. clear. intros L L' m ps es F2 SUB. induction F2; constructor; [eapply ENTRYobj_LB_mono; eassumption| assumption]. Qed.
    Lemma ENTRYs_rehome : forall L L' m ps es SP, Forall2 (fun p E => ENTRYobj L m p E) ps es ->
      (forall b, In b (concat (map (fun pe => blocks_ENTRY (fst pe) (snd pe)) (combine ps es))) -> In b L' /\ blk_addr b + blk_size b <= SP) ->
      Forall2 (fun p E => ENTRYobj L' m p E) ps es.
    Proof.
      clear. intros L L' m ps es SP F2. induction F2 as [|p E ps' es' HE F IH]; intros K; constructor.
      - eapply (ENTRYobj_frame_law L L' m m p E SP); [exact HE| intros b Hb; refine (proj1 (K b _)); cbn [concat map combine fst snd]; apply in_or_app; left; exact Hb| apply xpres_refl| intros b Hb; refine (proj2 (K b _)); cbn [concat map combine fst snd]; apply in_or_app; left; exact Hb].
      - apply IH. intros b Hb. apply K. cbn [concat map combine fst snd]. apply in_or_app. right. exact Hb.
    Qed.
    Lemma perm_pick {X : Type} : forall (x : X) l, In x l -> exists l', Permutation l (x :: l').
    Proof. clear. intros x l Hx. destruct (in_split x l Hx) as (l1 & l2 & ->). exists (l1 ++ l2). apply Permutation_sym. apply Permutation_middle. Qed.
    Lemma mid_eta : forall M0, mid_flag M0 = 1 -> mkMID 1 (mid_ctx M0) (mid_err M0) (mid_E M0) (mid_vdso M0) = M0.
    Proof. clear. intros [f c e E0 v] F1. cbn in *. subst f. reflexivity. Qed.

    Lemma perm_front : forall (l1 l2 l3 l4 l5 l6 l7 : list block) (a b x0 : block),
      Permutation (l1 ++ l2 ++ l3 ++ l4 ++ l5 ++ a :: b :: l6 ++ x0 :: l7) (x0 :: l1 ++ l2 ++ l3 ++ l4 ++ l5 ++ a :: b :: l6 ++ l7).
    Proof.
      clear. intros.
      assert (E1 : l1 ++ l2 ++ l3 ++ l4 ++ l5 ++ a :: b :: l6 ++ x0 :: l7 = (l1 ++ l2 ++ l3 ++ l4 ++ l5 ++ a :: b :: l6) ++ x0 :: l7) by (rewrite <- !app_assoc; reflexivity).
      assert (E2 : x0 :: l1 ++ l2 ++ l3 ++ l4 ++ l5 ++ a :: b :: l6 ++ l7 = x0 :: (l1 ++ l2 ++ l3 ++ l4 ++ l5 ++ a :: b :: l6) ++ l7) by (rewrite <- !app_assoc; reflexivity).
      rewrite E1, E2. apply Permutation_sym. apply Permutation_middle.
    Qed.

    (* [comment removed for export] *)
    Lemma rp_push : forall n cur rem c elen NBe NB S' M' LE w0 w1 w3 w5 w6 j3 m1 mo1 s1' ee E K es
        (u0 u1 u2 b2 b3 b4 b5 b6 b7 s4w s5w s6w s8w s9w s11w u3 u4 u5 u6 : word),
      LOOPAT n -> rem - 4 - elen <= Z.of_nat n -> dledger S' c -> cur = Bb + 2 + c -> c + rem = olen_of bs -> 19 <= elen -> 4 + elen <= rem ->
      DWK NBe NB S' M' LE w0 w1 w3 (Z_to_bv 64 (cur + 4)) w5 w6 (Z_to_bv 64 (rem - 4)) (Z_to_bv 64 elen) j3 m1 mo1 s1' ->
      es_entries_o S' = Some (K, es) ->
      ENTRYobj (DREST NBe NB LE) m1 ee E -> Permutation (blocks_ENTRY ee E) NBe -> 0 < ee ->
      5 * Z.of_nat (length NBe) <= 2 * (elen + 4) -> lb_bytes NBe <= ENTRY_KEPT elen -> lb_big NBe <= elen / 600 ->
      hs_SR H POSTc (mkCfg (MS (mkR (Z_to_bv 64 DF_R_PUSH) (Z_to_bv 64 SPc) gp (Z_to_bv 64 RATP) u0 u1 u2 sp (Z_to_bv 64 A) (Z_to_bv 64 (es_entries S')) (Z_to_bv 64 ee) b2 b3 b4 b5 b6 b7
                                  (Z_to_bv 64 bt) (Z_to_bv 64 Bb) s4w s5w s6w (Z_to_bv 64 ee) s8w s9w (Z_to_bv 64 cur) s11w u3 u4 u5 u6)
                             F (Z_to_bv 64 P_OPENSSL_sk_push) fc None m1 (seg_rom rsegs)) mo1).
    Proof using TR OLEN BUD0 CNT0 BIG0 A0 A1 SO SE SEO STL MBO MP0 MN0 MBB MBS DS DSL PAYL PAYS NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC BUDG AUX SPB BHI SPA ST CEIL LO ERR MI TP RAE HH HX NAR NBR MST POS BTR BT_frame PERM BTFREE RPE CERTO3 TIME.
      intros n cur rem c elen NBe NB S' M' LE w0 w1 w3 w5 w6 j3 m1 mo1 s1' ee E K es u0 u1 u2 b2 b3 b4 b5 b6 b7 s4w s5w s6w s8w s9w s11w u3 u4 u5 u6
             LP REM LED CUR CR EL19 ER DW ESO EO PE PEE ECNT EBYT EBIG.
      pose proof DW as (HP1 & KREL1 & MP1 & LM1 & STP1 & NEW1 & CTX1 & EC1 & EB1 & EG1 & LC1 & LBY1 & LG1 & SO1 & SID1 & SPM1 & SND1 & SKI1 & MBO1 & DSm1 & DSb1 & BT1
                        & FR0 & FR2 & FR3 & FR4 & [errv1 ERR1] & MI1 & ST1 & AUX1 & XA1 & DNB1).
      destruct RCFACTS as (SEQ & SIN & SBR & BEL0 & SUB0 & ND0 & STK0 & LO0 & MF0 & OBJ0 & DJA). hcb. pose proof (word_range sp) as SPR.
      destruct (DWKGF _ _ _ _ _ _ _ _ _ _ DW) as (HB & ND & DISJ & BRS & D2 & D1).
      pose proof (DRESTSUB NBe NB LE) as (SLB & S0 & SLE & SNB & STB & IB & IA & SLX & S3 & SLL).
      pose proof (DRESTSUB ([] : list block) NB LE) as (SLB0 & _ & SLE0 & SNB0 & STB0 & IB0 & IA0 & _ & S30 & SLL0).
      pose proof (dec_stack M M' STP1) as (_ & _ & _ & STKP & _).
      destruct (dwk_lib_facts _ _ _ _ _ _ _ _ _ _ DW) as (MFa & IMa & GMa & _).
      destruct (ent_blocks _ _ _ _ _ _ _ _ _ _ ee E DW PE) as (EBL & EBD & NDE).
      pose proof (EBL _ ltac:(left; reflexivity)) as (IEE & HEE & OEE & _). cbn [blk_addr blk_size fst snd] in HEE, OEE. unfold ENTRY_SIZE in HEE, OEE.
      destruct (nb_ledger _ _ _ _ _ _ _ _ _ _ c DW LED ltac:(clear - CR OLEN TR ER EL19; lia)) as (NB1 & NB2 & NB3 & C0 & N0 & N23).
      destruct (skb_facts _ _ _ _ _ _ _ _ _ _ DW) as (PNB & _). unfold SKB, EBS in PNB. rewrite ESO in PNB.
      pose proof LED as (L1 & L2 & L3 & L4 & L5). unfold nent, EBS in L1, L2, L3, L4, N0, N23. rewrite ESO in L1, L2, L3, L4, N0, N23.
      remember (concat (map (fun pe => blocks_ENTRY (fst pe) (snd pe)) (combine (sk_elems K) es))) as EB eqn:EBeq.
      pose proof SO1 as (SC1 & SIN1 & EN1). unfold ENTRIES in EN1. rewrite ESO in EN1. destruct EN1 as (PP & SKO & LEN & F2).
      destruct (SKI1 K es ESO) as [KC CAP].
      pose proof SKO as (_ & _ & KIN & KNC & KCAP2 & _ & _ & KDAT). unfold sk_num, zlength in KNC. rewrite <- LEN in KNC, CAP.
      assert (N64 : Z.of_nat (length es) <= 64) by (clear - N23 CR OLEN TR ER EL19 C0; lia).
      pose proof (blocks_SK_facts (es_entries S') K ltac:(clear - KNC; lia)) as (SKB1 & SKL1 & _ & SKG1 & _).
      pose proof (sk_grow_le (sk_cap K) ltac:(clear - KNC; lia)) as [GR GR5].
      pose proof (errph_nonneg (mid_err M')) as (EP0 & EC0 & EG0).
      destruct (dbud_raise NBe NB S' M' LE _ j3 m1 mo1 s1' (SKPUSH_COST K) 1 0 DW) as (_ & _ & _ & FB1 & FB2 & FB3 & _);
        [| unfold SKPUSH_COST; clear - GR; lia| clear; lia| clear; lia|].
      { eapply dbud_now; [exact DW| | |]; unfold SKPUSH_COST, DLOOP_BYTES, DLOOP_CNT, DLOOP_BIG, ENTRY_KEPT in *.
        - clear - NB1 EBYT ER CR OLEN TR C0 EL19 GR CAP N64. lia.
        - clear - NB2 ECNT ER CR OLEN TR C0 EL19. lia.
        - clear - NB3 EBIG ER CR OLEN TR C0 EL19. Z.div_mod_to_equations. lia. }
      (* [comment removed for export] *)
      pose proof (skpush_spec H HH HRE) as PS. unfold skpush_stmt in PS.
      eapply (sr_seq H HH).
      { eapply PS with (lo := lo) (B := B) (LB := mid_errblocks M' ++ DREST NBe NB LE) (s := s1') (a := es_entries S') (p := ee) (v := 1) (K := K) (errv := errv1); clear PS; try reflexivity.
        all: try first [exact HP1| exact KREL1| exact AUX1| exact MI1| exact CEIL].
        all: lazymatch goal with
             | |- 0 < _ < _ => clear - PEE HEE HCEILB; lia
             | |- SKobj _ _ _ _ => eapply SKobj_LB_mono; [exact SKO| intros b Hb; apply in_or_app; right; apply S0; apply S30; exact Hb]
             | |- sk_push_nocmp _ => left; exact KC
             | |- sk_cap _ <= SK_CAP_MAX => unfold SK_CAP_MAX; clear - CAP N64; lia
             | |- lb_bytes _ + _ <= _ => clear - FB1 EP0; lia
             | |- Z.of_nat _ + _ <= _ => clear - FB2 EC0; lia
             | |- lb_big _ + _ <= _ => rewrite (big1_small (8 * sk_grow (sk_cap K))) by (unfold BIGB; clear - GR5 CAP N64 KNC; lia); clear - FB3 EG0; lia
             | |- bv_unsigned _ <= B => unfold SP'; rewrite unsigned_lit by (clear - SPR LO STK0 LO0; lia); clear - SPB; lia
             | |- stk _ _ _ _ => unfold SP'; rewrite unsigned_lit by (clear - SPR LO STK0 LO0; lia); exact ST1
             | |- lo <= _ => unfold SP'; rewrite unsigned_lit by (clear - SPR LO STK0 LO0; lia); clear - LO STKP; lia
             | |- rw_cells _ _ (errno_addr _) _ => rewrite errno_RATP; exact ERR1
             | |- C1env _ _ => split; [exact MFa| split; [exact IMa| exact GMa]]
             | |- ?G => idtac "PUSHPRE" G
             end. }
      clear PS. intros [ms7 mo7] PO. unfold skpush_post in PO. cbn [cfg_ms cfg_model] in PO.
      destruct PO as (z0 & z1 & z2 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & z3 & z4 & z5 & z6 & m7 & errv7 & s7' & LB' & K' & data' & cap' & did' &
                      -> & KREL7 & MP7 & MI7 & ST7 & ERR7 & AUX7 & KEQ & PLB & HP7 & SO7 & XP7 & (v7 & (MF7 & IM7 & GM7) & VLE)).
      unfold SP' in ST7, XP7. rewrite (unsigned_lit (bv_unsigned sp + -2352)) in ST7, XP7 by (clear - SPR LO STK0 LO0; lia). rewrite errno_RATP in ERR7.
      change (bv_unsigned sp + -2352) with SPc in ST7, XP7.
      assert (V7 : v7 = 1) by (destruct MF7 as (fb & _ & _ & V01); clear - V01 VLE; lia). subst v7.
      (* [comment removed for export] *)
      unfold drest in PLB.
      pose proof (skpush_perm K K' (es_entries S') ee data' cap' did' (mid_errblocks M') NBe EB (TB ++ (pbin, Bb, nB) :: (p, A, nA) :: LE ++ LB) LB' NB KEQ PLB
                    (Permutation_sym PNB) ltac:(unfold sk_num, zlength; rewrite <- LEN; clear - KNC; lia)) as [PL' CAPS].
      set (LB0 := TB ++ (pbin, Bb, nB) :: (p, A, nA) :: LE ++ LB) in *.
      set (REST := mid_errblocks M' ++ NBe ++ EB ++ LB0) in *.
      set (SK' := blocks_SK (es_entries S') K') in *.
      assert (IDK : sk_id K' = sk_id K) by (rewrite KEQ; reflexivity).
      assert (ELK : sk_elems K' = sk_elems K ++ [ee]) by (rewrite KEQ; reflexivity).
      assert (CMK : sk_comp K' = sk_comp K) by (rewrite KEQ; reflexivity).
      assert (INR : forall b, In b REST -> In b LB') by (intros b Hb; eapply Permutation_in; [apply Permutation_sym; exact PL'| apply in_or_app; right; exact Hb]).
      assert (INK : forall b, In b SK' -> In b LB') by (intros b Hb; eapply Permutation_in; [apply Permutation_sym; exact PL'| apply in_or_app; left; exact Hb]).
      assert (R_LB : forall b, In b LB -> In b REST) by (intros b Hb; subst REST LB0; do 4 (apply in_or_app; right); right; right; apply in_or_app; right; exact Hb).
      assert (R_LE : forall b, In b LE -> In b REST) by (intros b Hb; subst REST LB0; do 4 (apply in_or_app; right); right; right; apply in_or_app; left; exact Hb).
      assert (R_LL : forall b, In b (LE ++ LIB) -> In b REST) by (intros b Hb; apply in_app_or in Hb; destruct Hb as [Hb|Hb]; [apply R_LE; exact Hb| apply R_LB; apply SUBL; exact Hb]).
      assert (R_TB : forall b, In b TB -> In b REST) by (intros b Hb; subst REST LB0; do 3 (apply in_or_app; right); apply in_or_app; left; exact Hb).
      assert (R_BIN : In (pbin, Bb, nB) REST) by (subst REST LB0; do 4 (apply in_or_app; right); left; reflexivity).
      assert (R_NBe : forall b, In b NBe -> In b REST) by (intros b Hb; subst REST; apply in_or_app; right; apply in_or_app; left; exact Hb).
      assert (R_EB : forall b, In b EB -> In b REST) by (intros b Hb; subst REST; do 2 (apply in_or_app; right); apply in_or_app; left; exact Hb).
      assert (R_ERR : forall b, In b (mid_errblocks M') -> In b REST) by (intros b Hb; subst REST; apply in_or_app; left; exact Hb).
      pose proof (HH_blocks_below H HH _ _ _ HP7) as HB7.
      assert (DJ : forall k1 k2, In k1 SK' -> In k2 REST -> blk_addr k1 + blk_size k1 <= blk_addr k2 \/ blk_addr k2 + blk_size k2 <= blk_addr k1)
        by (intros k1 k2 H1 H2; exact (perm_split_disjoint H HX _ _ _ _ _ _ _ HP7 PL' H1 H2)).
      assert (AV : forall b, In b REST -> avoids (memflag_foot ++ SK_foot (es_entries S') K') (blk_addr b) (blk_size b)).
      { intros b Hb. unfold avoids. apply Forall_app. split.
        - pose proof (HH_RHEAP_block_range H HH _ _ _ _ HP7 (INR _ Hb)) as (_ & _ & _ & _ & OFF). unfold memflag_foot, A_mem_inited. apply Forall_cons; [cbn [fst snd]; clear - OFF; lia| apply Forall_nil].
        - apply SK_foot_avoids. intros k1 H1. pose proof (DJ _ _ H1 Hb) as D0. clear - D0. lia. }
      assert (AVF : forall a n', SPc <= a -> avoids (memflag_foot ++ SK_foot (es_entries S') K') a n').
      { intros a n' Ha. unfold avoids. apply Forall_app. split.
        - unfold memflag_foot, A_mem_inited. apply Forall_cons; [cbn [fst snd]; unfold SP' in *; clear - Ha CEIL HCEILB LO STK0; lia| apply Forall_nil].
        - apply SK_foot_avoids. intros k1 H1. pose proof (HB7 _ (INK _ H1)) as E1. unfold SP' in *. clear - E1 Ha CEIL LO STK0. lia. }
      assert (XPR : xpres REST SPc (memflag_foot ++ SK_foot (es_entries S') K') m1 m7) by (eapply xpres_weaken; [exact XP7| clear; lia| exact INR| intros q Hq; exact Hq]).
      (* [comment removed for export] *)
      assert (SC7 : rw_cells rsegs m7 st [C8 (wz (es_entries S')); C8 (wz 0); C8 (wz 0)]).
      { eapply xpres_rw_cells'; [exact XPR| exact SC1| right; right; exists (es_id S, st, STORE_SIZE); split; [apply R_LB; exact (proj1 (proj2 SO))| cbn; unfold STORE_SIZE; clear; lia]|].
        eapply avoids_sub; [apply AV; apply R_LB; exact (proj1 (proj2 SO))| cbn; clear; lia| cbn; unfold STORE_SIZE; clear; lia]. }
      set (L7 := EB ++ NBe ++ LE ++ LB).
      assert (R_L7 : forall b, In b L7 -> In b REST).
      { intros b Hb. subst L7. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [apply R_EB; exact Hb|]. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [apply R_NBe; exact Hb|].
        apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [apply R_LE; exact Hb| apply R_LB; exact Hb]. }
      assert (EBE : concat (map (fun pe => blocks_ENTRY (fst pe) (snd pe)) (combine (sk_elems K ++ [ee]) (es ++ [E]))) = EB ++ blocks_ENTRY ee E).
      { rewrite (combine_app1 _ _ _ _ (eq_sym LEN)), map_app, concat_app. cbn [map concat fst snd]. rewrite app_nil_r, EBeq. reflexivity. }
      assert (F2all : Forall2 (fun q Eq => ENTRYobj L7 m1 q Eq) (sk_elems K ++ [ee]) (es ++ [E])).
      { apply Forall2_app.
        - eapply (ENTRYs_rehome (NB ++ LE ++ LB) L7 m1 _ _ hceil); [exact F2|]. intros b Hb. rewrite <- EBeq in Hb. split; [subst L7; apply in_or_app; left; exact Hb|].
          apply HB. apply in_or_app. right. apply S0. apply S30. apply in_or_app. left. eapply Permutation_in; [apply Permutation_sym; exact PNB|]. apply in_or_app. right. exact Hb.
        - constructor; [| constructor]. eapply (ENTRYobj_frame_law (DREST NBe NB LE) L7 m1 m1 ee E hceil); [exact EO| | apply xpres_refl|].
          + intros b Hb. subst L7. apply in_or_app. right. apply in_or_app. left. eapply Permutation_in; [exact PE| exact Hb].
          + intros b Hb. exact (proj1 (proj2 (EBL b Hb))). }
      assert (F27 : Forall2 (fun q Eq => ENTRYobj (SK' ++ L7) m7 q Eq) (sk_elems K ++ [ee]) (es ++ [E])).
      { eapply ENTRYs_mono; [| intros b Hb; apply in_or_app; right; exact Hb].
        eapply (ENTRYs_frameX L7 SPc); [exact F2all| eapply xpres_weaken; [exact XPR| clear; lia| exact R_L7| intros q Hq; exact Hq]|].
        intros b Hb. rewrite EBE in Hb. apply AV. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [apply R_EB; exact Hb| apply R_NBe; eapply Permutation_in; [exact PE| exact Hb]]. }
      assert (LM7 : LIBMID (LE ++ LIB) m7 M').
      { rewrite <- (mid_eta M' (proj1 STP1)). apply (LIBMID_mf_X (LE ++ LIB) LB' SPc (SK_foot (es_entries S') K') m1 m7 M'); [exact LM1| exact XP7| intros b Hb; apply INR; apply R_LL; exact Hb| exact MF7| |].
        - intros a Ha. destruct (SK_foot_rin _ _ _ Ha) as (k1 & H1 & R1). pose proof (HH_RHEAP_block_range H HH _ _ _ _ HP7 (INK _ H1)) as BR. exact (block_cell_off_image _ _ BR R1).
        - intros a b Ha Hb K0. destruct (SK_foot_rin _ _ _ Ha) as (k1 & H1 & R1). pose proof (DJ _ _ H1 (R_LL _ Hb)) as DJ1. clear - DJ1 R1 K0. lia. }
      assert (XA7 : xpres LB (bv_unsigned sp) XFc m m7).
      { eapply xpres_trans; [exact XA1|].
        apply (xpres_weaken LB LB (bv_unsigned sp) (bv_unsigned sp) [] XFc); [| clear; lia| auto| intros a Ha; destruct Ha].
        eapply (xpres_shrink LB' LB SPc (bv_unsigned sp) [] (SK_foot (es_entries S') K')); [| unfold SP'; clear - SPR; lia| intros b Hb; apply INR; apply R_LB; exact Hb|].
        - eapply (xpres_drop_memflag _ _ [] (SK_foot (es_entries S') K')); [exact MFa| exact MF7| cbn [app]; exact XP7].
        - intros a Ha XCa. destruct (SK_foot_rin _ _ _ Ha) as (k1 & H1 & R1).
          eapply (nb_not_client H HX lo CEIL s7' [] SK' REST (bv_unsigned sp) [] m7 k1 a); [cbn [app]; eapply PERM; [exact HP7| exact PL']| unfold SP' in *; clear - LO STK0; lia| exact H1| exact R1|].
          eapply xclient_mono; [exact R_LB| exact XCa]. }
      (* [comment removed for export] *)
      set (NB' := SK' ++ EB ++ NBe).
      set (S'' := mkSTORE (es_entries S') (Some (K', es ++ [E])) (es_id S')).
      assert (CAP' : 0 <= sk_cap K' <= 2 * (Z.of_nat (length es) + 1) + 4).
      { destruct CAPS as [C1|[[C0' C4]|(CG & NC & C4)]]; [rewrite C1; clear - CAP KNC; lia| rewrite C4; clear; lia|].
        rewrite CG. unfold sk_num, zlength in NC. rewrite <- LEN in NC. unfold sk_grow. clear - NC C4 CAP. Z.div_mod_to_equations. lia. }
      assert (SKF : Z.of_nat (length SK') <= 2 /\ 0 <= lb_bytes SK' <= SK_SIZE + 8 * sk_cap K' /\ lb_big SK' = 0).
      { subst SK'. unfold blocks_SK. destruct (Z.eqb_spec (sk_cap K') 0) as [C0'|CN]; rewrite ?lb_bytes_cons, ?lb_big_cons; cbn [length blk_size snd lb_bytes lb_big fold_right app Z.add];
          rewrite (big1_small SK_SIZE) by (unfold SK_SIZE, BIGB; clear; lia); unfold SK_SIZE; [clear - C0'; lia|].
        rewrite (big1_small (8 * sk_cap K')) by (unfold BIGB; clear - CAP' N64; lia). clear - CAP' CN. lia. }
      destruct SKF as (SKL' & SKB' & SKG').
      pose proof (Permutation_length PE) as NBeL. pose proof (lb_bytes_perm _ _ PE) as NBeB. pose proof (lb_big_perm _ _ PE) as NBeG.
      assert (DW7 : DWK [] NB' S'' M' LE w0 w1 w3 (Z_to_bv 64 (cur + 4)) w5 w6 (Z_to_bv 64 (rem - 4)) (Z_to_bv 64 elen) j3 m7 mo7 s7').
      { subst S''. unfold dwk. repeat match goal with |- _ /\ _ => split end.
        - eapply PERM; [exact HP7|]. etransitivity; [exact PL'|]. subst NB' REST LB0. unfold drest. rewrite app_nil_l, <- !app_assoc.
          etransitivity; [apply (Permutation_app_swap_app SK' (mid_errblocks M'))|]. rewrite <- ?app_assoc. apply Permutation_app_head. apply Permutation_app_head.
          rewrite !(app_assoc NBe EB), !(app_assoc EB NBe). apply Permutation_app_tail. apply Permutation_app_comm.
        - exact KREL7.
        - eapply (mpres_trans H HH); [exact MP1| exact MP7].
        - exact LM7.
        - exact STP1.
        - exact NEW1.
        - exact CTX1.
        - exact EC1.
        - exact EB1.
        - exact EG1.
        - exact LC1.
        - exact LBY1.
        - exact LG1.
        - unfold STOREobj. cbn [es_entries es_entries_o es_id]. split; [exact SC7|]. split; [apply in_or_app; right; apply in_or_app; right; rewrite SID1; exact (proj1 (proj2 SO))|].
          unfold ENTRIES. split; [exact PP|]. split; [eapply SKobj_relist; [exact SO7| intros b Hb; apply in_or_app; left; subst NB'; apply in_or_app; left; exact Hb]|].
          split; [rewrite ELK, !length_app; cbn [length]; rewrite LEN; reflexivity|].
          rewrite ELK. eapply ENTRYs_mono; [exact F27|]. intros b Hb. subst NB' L7. rewrite <- ?app_assoc. exact Hb.
        - cbn [es_id]. exact SID1.
        - unfold blocks_STORE. cbn [es_entries es_entries_o es_id]. rewrite ELK, EBE, SID1. apply perm_skip. subst NB' SK'. apply Permutation_app_head. apply Permutation_app_head. exact PE.
        - destruct (perm_pick _ _ (proj1 (proj2 SO))) as [lB PLB1].
          assert (PR : Permutation LB' (((es_id S, st, STORE_SIZE) :: SK' ++ EB ++ NBe) ++ (mid_errblocks M' ++ TB ++ (pbin, Bb, nB) :: (p, A, nA) :: LE ++ lB))).
          { etransitivity; [exact PL'|]. subst REST LB0.
            transitivity (SK' ++ mid_errblocks M' ++ NBe ++ EB ++ TB ++ (pbin, Bb, nB) :: (p, A, nA) :: LE ++ (es_id S, st, STORE_SIZE) :: lB).
            { do 5 (apply Permutation_app_head). do 2 (apply perm_skip). apply Permutation_app_head. exact PLB1. }
            cbn [app]. rewrite <- ?app_assoc.
            transitivity ((es_id S, st, STORE_SIZE) :: SK' ++ mid_errblocks M' ++ NBe ++ EB ++ TB ++ (pbin, Bb, nB) :: (p, A, nA) :: LE ++ lB); [apply perm_front|].
            apply perm_skip. apply Permutation_app_head.
            rewrite (app_assoc NBe EB). etransitivity; [apply Permutation_app_swap_app|]. rewrite (app_assoc EB NBe). apply Permutation_app; [apply Permutation_app_comm| apply Permutation_refl]. }
          eapply Permutation_NoDup; [apply Permutation_map; apply Permutation_sym|].
          { unfold blocks_STORE. cbn [es_entries es_entries_o es_id]. rewrite ELK, EBE, SID1. apply perm_skip. apply Permutation_app_head. apply Permutation_app_head. exact PE. }
          pose proof (Permutation_NoDup (Permutation_map blk_id PR) (HH_RHEAP_blocks_nodup H HH _ _ _ HP7)) as ND7. rewrite map_app in ND7.
          subst SK'. exact (NoDup_app_remove_r _ _ ND7).
        - intros K0 es0 EQ0. cbn [es_entries_o] in EQ0. injection EQ0 as <- <-. split; [rewrite CMK; exact KC| rewrite ELK, length_app, Nat2Z.inj_add, <- LEN; cbn [length Z.of_nat Pos.of_succ_nat]; clear - CAP'; lia].
        - eapply (MEMBIO_frameA LB LB SPc); [exact MBO1| exact MBLB| eapply xpres_weaken; [exact XPR| clear; lia| exact R_LB| intros q Hq; exact Hq]|].
          apply Forall_forall. intros iv Hiv. apply Forall_forall. intros bk Hbk. exact (proj1 (Forall_forall _ _) (AV bk (R_LB _ (MBLB _ Hbk))) iv Hiv).
        - destruct (PAYL ltac:(clear - NAR; lia)) as [pD [PIN _]]. pose proof DSL as DSL1. unfold zlength in DSL1.
          eapply xpres_bytes_at'; [exact XPR| exact DSm1| right; right; exists (pD, mb_buf R, mb_len R); split; [apply R_LB; exact PIN| cbn; rewrite DSL1; clear; lia]|].
          pose proof (AV _ (R_LB _ PIN)) as K0. cbn [blk_addr blk_size fst snd] in K0. rewrite DSL1. exact K0.
        - pose proof (AV _ R_BIN) as K0. cbn [blk_addr blk_size fst snd] in K0.
          eapply xpres_bytes_at'; [exact XPR| exact DSb1| right; right; exists (pbin, Bb, nB); split; [exact R_BIN| cbn; unfold zlength in NBR; clear - NBR; lia]|].
          eapply avoids_sub; [exact K0| clear; lia| unfold zlength in NBR; clear - NBR; lia].
        - eapply (BT_frame REST SPc); [exact BT1| exact XPR| exact R_TB| unfold SP'; clear - CEIL LO STK0; lia|].
          apply Forall_forall. intros iv Hiv. apply Forall_forall. intros bk Hbk. exact (proj1 (Forall_forall _ _) (AV bk (R_TB _ Hbk)) iv Hiv).
        - eapply xpres_rw_cells'; [exact XPR| exact FR0| left; clear; lia| apply AVF; clear; lia].
        - eapply xpres_rw_cells'; [exact XPR| exact FR2| left; unfold RBP, SP'; clear; lia| apply AVF; unfold RBP, SP'; clear; lia].
        - eapply xpres_rw_cells'; [exact XPR| exact FR3| left; unfold O_F3; clear; lia| apply AVF; unfold O_F3; clear; lia].
        - eapply xpres_rw_cells'; [exact XPR| exact FR4| left; unfold O_SAVES; clear; lia| apply AVF; unfold O_SAVES; clear; lia].
        - exists errv7; exact ERR7.
        - exact MI7.
        - exact ST7.
        - exact AUX7.
        - exact XA7.
        - unfold dnb. subst NB'. rewrite !length_app, !lb_bytes_app, !lb_big_app, !Nat2Z.inj_add.
          unfold DECODE_CNT, DECODE_BYTES, DECODE_BIG, ENTRY_KEPT, SK_SIZE in *. clear - SKL' SKB' SKG' L1 L2 L3 ECNT EBYT EBIG CAP' N64 CR OLEN TR ER EL19 C0 N0.
          split; [lia|]. split; [lia|]. Z.div_mod_to_equations. lia. }
      (* [comment removed for export] *)
      assert (LED7 : dledger S'' (c + 4 + elen)).
      { subst S''. unfold dledger, EBS, nent. cbn [es_entries_o es_entries]. rewrite ELK, EBE, !length_app, lb_bytes_app, lb_big_app, !Nat2Z.inj_add, NBeL, NBeB, NBeG. cbn [length Z.of_nat Pos.of_succ_nat].
        clear - L1 L2 L3 L4 L5 ECNT EBYT EBIG EL19. unfold ENTRY_KEPT in *. split; [lia|]. split; [lia|]. split; [Z.div_mod_to_equations; lia|]. lia. }
      (* [comment removed for export] *)
      pose proof DW7 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FR07 & _).
      eapply (sr_evt_krel H HH); [exact KREL7| unfold SP'; eapply fs_ok8 with (rv := sk_num K + 1) (st := st);
        [unfold sk_num, zlength; rewrite <- LEN; clear - N64; lia| clear - SPR LO STK0 LO0; lia| exact FR07| exact MI7]|].
      cbv beta. intros ms8 [a1' ->]. fold (SP' sp).
      eapply (rp_trip_adv n cur rem c elen NB' S'' M' LE); [exact LP| exact REM| exact DW7| exact LED7| exact CUR| exact CR| clear - EL19; lia| exact ER| exact C0].
    Qed.

    (* [comment removed for export] *)
    Lemma rp_setter : forall (entry which : Z) Lx NB S' M' LE fr j3 m1 mo1 s1' (a f ra0 : Z) K
        (u0 u1 u2 c2 c3 c4 c5 c6 c7 s2w s3w s4w s5w s6w s7w s8w s9w s10w s11w u3 u4 u5 u6 : word) (Q : config -> Prop),
      skset_stmt_at entry which ->
      DWKG Lx NB S' M' LE fr j3 m1 mo1 s1' -> In (sk_id K, a, SK_SIZE) Lx -> SKobj (mid_errblocks M' ++ DREST Lx NB LE) m1 a K -> sk_cap K = 0 ->
      0 <= f < 2^64 -> 0 <= ra0 < 2^64 ->
      (forall m2 (v0 v1 v2 d1 d2 d3 d4 d5 d6 d7 v3 v4 v5 v6 : word),
         DWKG Lx NB S' M' LE fr j3 m2 mo1 s1' -> SKobj (mid_errblocks M' ++ DREST Lx NB LE) m2 a (sk_with_thunk K which f) ->
         xpres (mid_errblocks M' ++ DREST Lx NB LE) SPc [(a, a + SK_SIZE)] m1 m2 ->
         hs_SR H Q (mkCfg (MS (mkR (Z_to_bv 64 ra0) (Z_to_bv 64 SPc) gp (Z_to_bv 64 RATP) v0 v1 v2 sp (Z_to_bv 64 A) (Z_to_bv 64 a) d1 d2 d3 d4 d5 d6 d7
                            s2w s3w s4w s5w s6w s7w s8w s9w s10w s11w v3 v4 v5 v6) F (ret_pc (Z_to_bv 64 ra0)) fc None m2 (seg_rom rsegs)) mo1)) ->
      hs_SR H Q (mkCfg (MS (mkR (Z_to_bv 64 ra0) (Z_to_bv 64 SPc) gp (Z_to_bv 64 RATP) u0 u1 u2 sp (Z_to_bv 64 A) (Z_to_bv 64 a) (Z_to_bv 64 f) c2 c3 c4 c5 c6 c7
                         s2w s3w s4w s5w s6w s7w s8w s9w s10w s11w u3 u4 u5 u6) F (Z_to_bv 64 entry) fc None m1 (seg_rom rsegs)) mo1).
    Proof using A0 A1 SO SE SEO STL MBO MP0 MN0 MBB MBS DS DSL PAYL NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC BUDG AUX SPB BHI SPA ST CEIL LO ERR MI TP RAE HH HX NAR NBR MST POS BTR BT_frame.
      intros until Q. intros SPEC DW KIN SKO C0 FR RAR KQ.
      pose proof DW as (HP1 & KREL1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FR0 & _ & FR3 & _ & _ & MI1 & ST1 & _).
      destruct RCFACTS as (SEQ & SIN & SBR & BEL0 & SUB0 & ND0 & STK0 & LO0 & MF0 & OBJ0 & DJA). hcb. pose proof (word_range sp) as SPR.
      destruct (DWKGF _ _ _ _ _ _ _ _ _ _ DW) as (HB & _).
      pose proof (DRESTSUB Lx NB LE) as (_ & _ & _ & _ & _ & _ & _ & SLX & _).
      pose proof (HB _ ltac:(apply in_or_app; right; apply SLX; exact KIN)) as KB. cbn [blk_addr blk_size fst snd] in KB.
      unfold skset_stmt_at in SPEC.
      eapply (sr_evt_krel H HH); [exact KREL1| eapply SPEC with (lo := lo) (a := a) (f := f) (K := K); [reflexivity| reflexivity| exact FR| exact SKO| | | | exact MI1]|].
      { split; [clear - KB CEIL; lia| left; exact C0]. }
      { unfold SP'. rewrite unsigned_lit by (clear - SPR LO STK0 LO0; lia). exact ST1. }
      { unfold SP'. rewrite unsigned_lit by (clear - SPR LO STK0 LO0; lia). clear - LO STK0. lia. }
      cbv beta. intros ms2 PO. unfold skset_post in PO.
      destruct PO as (v0 & v1 & v2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & m2 & -> & MU & WM & MI2 & ST2 & SKO2).
      unfold SP' in MU, ST2. rewrite (unsigned_lit (bv_unsigned sp + -2352)) in MU, ST2 by (clear - SPR LO STK0 LO0; lia). change (bv_unsigned sp + -2352) with SPc in MU, ST2.
      assert (DJF : forall q n', SPc <= q -> disjoint_from [(lo, SPc); (a, a + SK_SIZE)] q n').
      { intros q n' Hq. cbn. unfold SK_SIZE, SP' in *. clear - Hq KB CEIL LO STK0. split; [lia| split; [lia| exact I]]. }
      eapply KQ; [| exact SKO2|].
      2: { eapply xpres_of_munch_gen; [exact MU| exact WM|]. intros q Hq [HC HXq]. cbn [outside fst snd].
           split; [| split; [| exact I]]; [| intros K0; apply HXq; cbn [rin_ivs fst snd]; left; exact K0].
           destruct HC as [HC|[[HC _]|(b & Hb & Hr)]]; [unfold SP' in *; clear - HC; lia| unfold SP' in *; clear - HC CEIL HCEILB LO STK0; lia|].
           pose proof (HB b Hb) as E. clear - E Hr CEIL. lia. }
      eapply (DWKGW Lx NB S' M' LE fr j3 m1 mo1 s1' m2 _ fr j3); [exact DW| exact MU| exact WM| exact MI2| exact ST2| | |].
      - apply Forall_cons; [left; cbn; clear; lia|]. apply Forall_cons; [| apply Forall_nil]. right; right; right. exists (sk_id K, a, SK_SIZE). split; [exact KIN| cbn; clear; lia].
      - eapply rw_cells_transport; [exact FR0| exact MU| exact WM| apply DJF; clear; lia].
      - eapply rw_cells_transport; [exact FR3| exact MU| exact WM| apply DJF; unfold O_F3; clear; lia].
    Qed.

    (* [comment removed for export] *)
    Lemma rp_newsk : forall n cur rem c elen NBe NB S' M' LE w0 w1 w3 w5 w6 j3 m1 mo1 s1' ee E
        (u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 s4w s5w s6w s8w s9w s11w u3 u4 u5 u6 : word),
      LOOPAT n -> rem - 4 - elen <= Z.of_nat n -> dledger S' c -> cur = Bb + 2 + c -> c + rem = olen_of bs -> 19 <= elen -> 4 + elen <= rem ->
      DWK NBe NB S' M' LE w0 w1 w3 (Z_to_bv 64 (cur + 4)) w5 w6 (Z_to_bv 64 (rem - 4)) (Z_to_bv 64 elen) j3 m1 mo1 s1' ->
      es_entries S' = 0 ->
      ENTRYobj (DREST NBe NB LE) m1 ee E -> Permutation (blocks_ENTRY ee E) NBe -> 0 < ee ->
      5 * Z.of_nat (length NBe) <= 2 * (elen + 4) -> lb_bytes NBe <= ENTRY_KEPT elen -> lb_big NBe <= elen / 600 ->
      hs_SR H POSTc (mkCfg (MS (mkR (Z_to_bv 64 DF_R_SKNEW) (Z_to_bv 64 SPc) gp (Z_to_bv 64 RATP) u0 u1 u2 sp (Z_to_bv 64 A) (Z_to_bv 64 0) b1 b2 b3 b4 b5 b6 b7
                                  (Z_to_bv 64 bt) (Z_to_bv 64 Bb) s4w s5w s6w (Z_to_bv 64 ee) s8w s9w (Z_to_bv 64 cur) s11w u3 u4 u5 u6)
                             F (Z_to_bv 64 P_OPENSSL_sk_new_null) fc None m1 (seg_rom rsegs)) mo1).
    Proof using TR OLEN BUD0 CNT0 BIG0 A0 A1 SO SE SEO STL MBO MP0 MN0 MBB MBS DS DSL PAYL PAYS NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC BUDG AUX SPB BHI SPA ST CEIL LO ERR MI TP RAE HH HX NAR NBR MST POS BTR BT_frame PERM BTFREE RPE CERTO3 TIME.
      intros n cur rem c elen NBe NB S' M' LE w0 w1 w3 w5 w6 j3 m1 mo1 s1' ee E u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 s4w s5w s6w s8w s9w s11w u3 u4 u5 u6
             LP REM LED CUR CR EL19 ER DW ES0 EO PE PEE ECNT EBYT EBIG.
      pose proof DW as (HP1 & KREL1 & MP1 & LM1 & STP1 & NEW1 & CTX1 & EC1 & EB1 & EG1 & LC1 & LBY1 & LG1 & SO1 & SID1 & SPM1 & SND1 & SKI1 & MBO1 & DSm1 & DSb1 & BT1
                        & FR0 & FR2 & FR3 & FR4 & [errv1 ERR1] & MI1 & ST1 & AUX1 & XA1 & DNB1).
      destruct RCFACTS as (SEQ & SIN & SBR & BEL0 & SUB0 & ND0 & STK0 & LO0 & MF0 & OBJ0 & DJA). hcb. pose proof (word_range sp) as SPR.
      destruct (DWKGF _ _ _ _ _ _ _ _ _ _ DW) as (HB & ND & DISJ & BRS & D2 & D1).
      pose proof (DRESTSUB NBe NB LE) as (SLB & S0 & SLE & SNB & STB & IB & IA & SLX & S3 & SLL).
      pose proof (DRESTSUB ([] : list block) NB LE) as (SLB0 & _ & SLE0 & SNB0 & STB0 & IB0 & IA0 & _ & S30 & SLL0).
      pose proof (dec_stack M M' STP1) as (_ & _ & _ & STKP & _ & _ & _ & _ & _ & _ & STKN & _).
      destruct (dwk_lib_facts _ _ _ _ _ _ _ _ _ _ DW) as (MFa & IMa & GMa & _).
      destruct (ent_blocks _ _ _ _ _ _ _ _ _ _ ee E DW PE) as (EBL & EBD & NDE).
      pose proof (EBL _ ltac:(left; reflexivity)) as (IEE & HEE & OEE & _). cbn [blk_addr blk_size fst snd] in HEE, OEE. unfold ENTRY_SIZE in HEE, OEE.
      destruct (nb_ledger _ _ _ _ _ _ _ _ _ _ c DW LED ltac:(clear - CR OLEN TR ER EL19; lia)) as (NB1 & NB2 & NB3 & C0 & N0 & N23).
      (* [comment removed for export] *)
      pose proof SO1 as (SC1 & SIN1 & EN1).
      assert (ESO : es_entries_o S' = None).
      { unfold ENTRIES in EN1. destruct (es_entries_o S') as [[K es]|]; [| reflexivity]. destruct EN1 as (PP & _). rewrite ES0 in PP. exfalso. clear - PP. lia. }
      assert (NB0 : NB = []).
      { unfold blocks_STORE in SPM1. rewrite ESO in SPM1. apply Permutation_length in SPM1. cbn in SPM1. destruct NB; [reflexivity| cbn in SPM1; lia]. }
      subst NB. rewrite ES0 in SC1.
      pose proof (errph_nonneg (mid_err M')) as (EP0 & EC0 & EG0).
      destruct (dbud_raise NBe [] S' M' LE _ j3 m1 mo1 s1' SK_SIZE 1 0 DW) as (_ & _ & _ & FB1 & FB2 & FB3 & _); [| unfold SK_SIZE; clear; lia| clear; lia| clear; lia|].
      { eapply dbud_now; [exact DW| | |]; cbn [lb_bytes lb_big length fold_right Z.of_nat Z.add]; unfold SK_SIZE, DLOOP_BYTES, DLOOP_CNT, DLOOP_BIG, ENTRY_KEPT in *.
        - clear - EBYT ER CR OLEN TR C0 EL19. lia.
        - clear - ECNT ER CR OLEN TR C0 EL19. lia.
        - clear - EBIG ER CR OLEN TR C0 EL19. Z.div_mod_to_equations. lia. }
      (* [comment removed for export] *)
      pose proof (sknew_null_spec H HH) as NS. unfold sknew_null_stmt, sknew_stmt_gen in NS.
      eapply (sr_seq H HH).
      { eapply NS with (c := 0) (lo := lo) (B := B) (LB := mid_errblocks M' ++ DREST NBe [] LE) (s := s1') (v := 1) (errv := errv1); clear NS; try reflexivity.
        all: try first [exact HP1| exact KREL1| exact AUX1| exact MI1| exact CEIL].
        all: lazymatch goal with
             | |- lb_bytes _ + _ <= _ => clear - FB1 EP0; lia
             | |- Z.of_nat _ + _ <= _ => clear - FB2 EC0; lia
             | |- lb_big _ <= _ => clear - FB3 EG0; lia
             | |- bv_unsigned _ <= B => unfold SP'; rewrite unsigned_lit by (clear - SPR LO STK0 LO0; lia); clear - SPB; lia
             | |- stk _ _ _ _ => unfold SP'; rewrite unsigned_lit by (clear - SPR LO STK0 LO0; lia); exact ST1
             | |- lo <= _ => unfold SP'; rewrite unsigned_lit by (clear - SPR LO STK0 LO0; lia); unfold SKNEW_STACK, FR_sk_new, FR_sk_new_null in *; clear - LO STKN; lia
             | |- rw_cells _ _ (errno_addr _) _ => rewrite errno_RATP; exact ERR1
             | |- C1env _ _ => split; [exact MFa| split; [exact IMa| exact GMa]]
             | |- ?G => idtac "NEWPRE" G
             end. }
      clear NS. intros [ms2 mo2] PO. unfold sknew_post in PO. cbn [cfg_ms cfg_model] in PO.
      destruct PO as (z0 & z1 & z2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & z3 & z4 & z5 & z6 & m2 & errv2 & Ask & kid & did & s2' &
                      -> & KREL2 & MP2 & MI2 & ST2 & ERR2 & AUX2 & XP2 & APOS & HP2 & SKO2 & (MF2 & IM2 & GM2)).
      unfold SP' in ST2, XP2. rewrite (unsigned_lit (bv_unsigned sp + -2352)) in ST2, XP2 by (clear - SPR LO STK0 LO0; lia). rewrite errno_RATP in ERR2.
      change (bv_unsigned sp + -2352) with SPc in ST2, XP2.
      set (BK := (kid, Ask, SK_SIZE)) in *.
      assert (XP2' : xpres (mid_errblocks M' ++ DREST NBe [] LE) SPc [] m1 m2).
      { rewrite <- (app_nil_r memflag_foot) in XP2. pose proof (xpres_drop_memflag _ _ [] [] m1 m2 MFa MF2 XP2) as K0. exact K0. }
      assert (HP2' : hs_RHEAP H s2' (mid_errblocks M' ++ DREST (BK :: NBe) [] LE) m2) by (eapply PERM; [exact HP2|]; unfold drest; apply Permutation_middle).
      pose proof (DWKGX NBe (BK :: NBe) [] S' M' LE _ j3 m1 mo1 s1' m2 mo2 s2' DW
                    ltac:(eapply xpres_weaken; [exact XP2'| clear; lia| intros b Hb; apply in_or_app; right; apply S0; exact Hb| intros q Hq; exact Hq])
                    HP2' KREL2 ltac:(eapply (mpres_trans H HH); [exact MP1| exact MP2]) ltac:(exists errv2; exact ERR2) MI2 ST2 AUX2) as DW2.
      assert (EO2 : ENTRYobj (DREST (BK :: NBe) [] LE) m2 ee E).
      { eapply ENTRYobj_LB_mono; [| intros b Hb; right; exact Hb].
        eapply (ENTRYobj_frameX _ SPc); [exact EO| eapply xpres_weaken; [exact XP2'| clear; lia| intros b Hb; apply in_or_app; right; exact Hb| intros q Hq; exact Hq]| intros b Hb; apply Forall_nil]. }
      assert (SKO2' : SKobj (mid_errblocks M' ++ DREST (BK :: NBe) [] LE) m2 Ask (sk_fresh 0 kid did)).
      { eapply SKobj_LB_mono; [exact SKO2|]. intros b Hb. eapply Permutation_in; [| exact Hb]. unfold drest. apply Permutation_middle. }
      assert (KIN : In (sk_id (sk_fresh 0 kid did), Ask, SK_SIZE) (BK :: NBe)) by (left; reflexivity).
      pose proof (HH_blocks_below H HH _ _ _ HP2' BK ltac:(apply in_or_app; right; left; reflexivity)) as KB. cbv delta [BK] in KB. cbn [blk_addr blk_size fst snd] in KB. unfold SK_SIZE in KB.
      clear XP2 XP2' HP2 SKO2 EO DW HP1 KREL1 MI1 ST1 AUX1 ERR1 FR0 FR2 FR3 FR4.
      (* [comment removed for export] *)
      pose proof DW2 as (_ & KREL2' & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MI2' & _).
      eapply (sr_evt_krel H HH); [exact KREL2'| eapply fs_ok4; exact MI2'|]. cbv beta. intros ms3 [a0' [-> ->]].
      eapply (rp_setter P_OPENSSL_sk_set_cmp_thunks O_SK_CMPTH (BK :: NBe) [] S' M' LE _ j3 m2 mo2 s2' Ask A_THUNK1 DF_R_SET1 (sk_fresh 0 kid did));
        [exact skset_cmp_thunks_spec| exact DW2| exact KIN| exact SKO2'| reflexivity| unfold A_THUNK1; clear; lia| unfold DF_R_SET1; clear; lia|].
      intros m3 v0 v1 v2 d1 d2 d3 d4 d5 d6 d7 v3 v4 v5 v6 DW3 SKO3 XP23.
      pose proof DW3 as (_ & KREL3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MI3 & _).
      eapply (sr_evt_krel H HH); [exact KREL3| eapply fs_ok5; exact MI3|]. cbv beta. intros ms4 [a0'' [-> ->]].
      eapply (rp_setter P_OPENSSL_sk_set_copy_thunks O_SK_COPYTH (BK :: NBe) [] S' M' LE _ j3 m3 mo2 s2' Ask A_THUNK2 DF_R_SET2 (sk_with_thunk (sk_fresh 0 kid did) O_SK_CMPTH A_THUNK1));
        [exact skset_copy_thunks_spec| exact DW3| left; reflexivity| exact SKO3| reflexivity| unfold A_THUNK2; clear; lia| unfold DF_R_SET2; clear; lia|].
      clear DW3 SKO3 KREL3 MI3. intros m4 v0' v1' v2' e1 e2 e3 e4 e5 e6 e7 v3' v4' v5' v6' DW4 SKO4 XP34.
      pose proof DW4 as (_ & KREL4 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MI4 & _).
      eapply (sr_evt_krel H HH); [exact KREL4| eapply fs_ok6; exact MI4|]. cbv beta. intros ms5 [a0''' [-> ->]].
      eapply (rp_setter P_OPENSSL_sk_set_thunks O_SK_FREETH (BK :: NBe) [] S' M' LE _ j3 m4 mo2 s2' Ask A_THUNK3 DF_R_SET3 (sk_with_thunk (sk_with_thunk (sk_fresh 0 kid did) O_SK_CMPTH A_THUNK1) O_SK_COPYTH A_THUNK2));
        [exact skset_thunks_spec| exact DW4| left; reflexivity| exact SKO4| reflexivity| unfold A_THUNK3; clear; lia| unfold DF_R_SET3; clear; lia|].
      clear DW4 SKO4 KREL4 MI4. intros m5 v0'' v1'' v2'' g1 g2 g3 g4 g5 g6 g7 v3'' v4'' v5'' v6'' DW5 SKO5 XP45.
      set (Kth := sk_with_thunk (sk_with_thunk (sk_with_thunk (sk_fresh 0 kid did) O_SK_CMPTH A_THUNK1) O_SK_COPYTH A_THUNK2) O_SK_FREETH A_THUNK3) in SKO5.
      (* [comment removed for export] *)
      pose proof DW5 as (HP5 & KREL5 & MP5 & LM5 & STP5 & NEW5 & CTX5 & EC5 & EB5 & EG5 & LC5 & LBY5 & LG5 & SO5 & SID5 & SPM5 & SND5 & SKI5 & MBO5 & DSm5 & DSb5 & BT5
                        & FR05 & FR25 & FR35 & FR45 & [errv5 ERR5] & MI5 & ST5 & AUX5 & XA5 & DNB5).
      destruct (DWKGF _ _ _ _ _ _ _ _ _ _ DW5) as (HB5 & ND5 & DISJ5 & BRS5 & D25 & D15).
      pose proof (DRESTSUB (BK :: NBe) ([] : list block) LE) as (SLB5 & S05 & SLE5 & _ & STB5 & IB5 & IA5 & SLX5 & S35 & SLL5).
      pose proof SO5 as (SC5 & SIN5 & _). rewrite ES0 in SC5.
      assert (FLB : forall b, In b LB -> In b (mid_errblocks M' ++ DREST (BK :: NBe) [] LE)) by (intros b Hb; apply in_or_app; right; apply SLB5; exact Hb).
      assert (FTB : forall b, In b TB -> In b (mid_errblocks M' ++ DREST (BK :: NBe) [] LE)) by (intros b Hb; apply in_or_app; right; apply STB5; exact Hb).
      assert (FBIN : In (pbin, Bb, nB) (mid_errblocks M' ++ DREST (BK :: NBe) [] LE)) by (apply in_or_app; right; exact IB5).
      assert (STIN : In (es_id S, st, STORE_SIZE) (mid_errblocks M' ++ DREST (BK :: NBe) [] LE)) by (apply in_or_app; right; apply SLB5; exact (proj1 (proj2 SO))).
      eapply (sr_evt_krel H HH); [exact KREL5| unfold SP'; eapply fs_ok7 with (a := Ask) (st := st) (ee := ee);
        [clear - APOS KB HCEILB; lia| clear - SBR; destruct SBR as (P0 & _); exact P0| destruct SBR as (_ & _ & _ & K0 & _); clear - K0 HCEILB; unfold STORE_SIZE in *; lia
        | clear - SPR LO STK0 LO0; lia| exact FR05| exact SC5| exact MI5]|].
      cbv beta. intros ms6 (m6 & a1' & -> & -> & MU6 & WM6 & MI6 & SC6). fold (SP' sp).
      (* [comment removed for export] *)
      assert (XP56 : xpres (mid_errblocks M' ++ DREST (BK :: NBe) [] LE) SPc [(st, st + 8)] m5 m6).
      { eapply xpres_of_munch_gen; [exact MU6| exact WM6|]. intros q Hq [_ HXq]. cbn [outside fst snd]. split; [| exact I]. intros K0. apply HXq. cbn [rin_ivs fst snd]. left. exact K0. }
      assert (AV6 : forall b, In b (mid_errblocks M' ++ DREST (BK :: NBe) [] LE) -> blk_id b <> es_id S -> avoids [(st, st + 8)] (blk_addr b) (blk_size b)).
      { intros b Hb NE. pose proof (DISJ5 b (es_id S, st, STORE_SIZE) Hb STIN NE) as D0. cbn [blk_addr blk_size fst snd] in D0.
        unfold avoids. apply Forall_cons; [cbn [fst snd]; unfold STORE_SIZE in D0; clear - D0; lia| apply Forall_nil]. }
      assert (NEL : forall b, In b (LE ++ LIB) -> blk_id b <> es_id S).
      { intros b Hb. apply in_app_or in Hb. destruct Hb as [Hb|Hb].
        - destruct (drest_ids _ _ _ _ _ _ _ _ _ _ _ _ ND5) as (_ & _ & _ & _ & _ & _ & DLE). exact (DLE _ _ Hb (proj1 (proj2 SO))).
        - exact (DJ6 _ _ Hb (or_introl eq_refl)). }
      assert (DJF6 : forall q n', SPc <= q -> disjoint_from [(st, st + 8)] q n').
      { intros q n' Hq. cbn. destruct SBR as (_ & _ & _ & K0 & _). unfold SP', STORE_SIZE in *. clear - Hq K0 CEIL LO STK0. split; [lia| exact I]. }
      assert (ST6 : stk rsegs m6 lo SPc).
      { eapply stk_transport_disjoint; [exact ST5| exact MU6| exact WM6|]. cbn. destruct SBR as (_ & _ & _ & K0 & _). unfold STORE_SIZE in K0. clear - K0 CEIL. split; [lia| exact I]. }
      set (S2 := mkSTORE Ask (Some (Kth, [])) (es_id S')).
      assert (SKO6 : SKobj ([BK] ++ LE ++ LB) m6 Ask Kth).
      { cbv delta [Kth BK]. eapply SKobj_relist; [| intros b Hb; apply in_or_app; left; unfold blocks_SK in Hb; cbn [sk_cap sk_id sk_with_thunk sk_fresh Z.eqb app] in Hb; exact Hb].
        eapply SKobj_frameX; [exact SKO5| intros b Hb; eapply SKobj_owned; [exact SKO5| exact Hb]| exact XP56|].
        intros b Hb. apply AV6; [eapply SKobj_owned; [exact SKO5| exact Hb]|].
        unfold blocks_SK in Hb. cbn [sk_cap sk_id sk_with_thunk sk_fresh Z.eqb app] in Hb. destruct Hb as [<-|[]]. cbn [blk_id fst].
        intros EQ. exact (D25 BK (es_id S, st, STORE_SIZE) (or_introl eq_refl) (SLB0 _ (proj1 (proj2 SO))) EQ). }
      assert (DW6 : DWK NBe [BK] S2 M' LE w0 w1 w3 (Z_to_bv 64 (cur + 4)) w5 w6 (Z_to_bv 64 (rem - 4)) (Z_to_bv 64 elen) j3 m6 mo2 s2').
      { subst S2. cbv delta [Kth BK]. unfold dwk. repeat match goal with |- _ /\ _ => split end.
        - eapply PERM; [eapply (HH_RHEAP_frame H HH); [exact HP5| exact MU6| exact WM6| apply Forall_cons; [right; right; exists (es_id S, st, STORE_SIZE); split; [exact STIN| cbn; unfold STORE_SIZE; clear; lia]| apply Forall_nil]]|].
          unfold drest. apply Permutation_app_head. cbn [app]. apply Permutation_middle.
        - exact KREL5.
        - exact MP5.
        - eapply LIBMID_agree; [exact LM5|]. eapply magree_mono; [eapply magree_mid_of_xpres; [exact XP56| exact (fun b Hb => in_or_app _ _ _ (or_intror (S05 b (SLL5 b Hb))))]|].
          intros q Hq. split; [exact Hq|]. cbn [rin_ivs fst snd]. intros [K0|[]].
          destruct SBR as (_ & _ & _ & _ & OFF). unfold STORE_SIZE in OFF.
          destruct Hq as [[HL|(b & Hb & Hr)]|[HR _]]; [pose proof (libx_in_image q HL); unfold IMG_LO, IMG_HI in *; clear - K0 OFF H0; lia| | unfold RELRO_LO, RELRO_HI in HR; clear - K0 OFF HR; lia].
          pose proof (AV6 b (in_or_app _ _ _ (or_intror (S05 _ (SLL5 _ Hb)))) (NEL _ Hb)) as AB. unfold avoids in AB. pose proof (Forall_inv AB) as AB1. cbn [fst snd] in AB1. clear - AB1 Hr K0. lia.
        - exact STP5.
        - exact NEW5.
        - exact CTX5.
        - exact EC5.
        - exact EB5.
        - exact EG5.
        - exact LC5.
        - exact LBY5.
        - exact LG5.
        - unfold STOREobj. cbn [es_entries es_entries_o es_id]. split; [exact SC6|]. split; [apply in_or_app; right; apply in_or_app; right; rewrite SID5; exact (proj1 (proj2 SO))|].
          unfold ENTRIES. split; [exact APOS|]. split; [exact SKO6|]. split; [reflexivity| constructor].
        - cbn [es_id]. exact SID5.
        - unfold blocks_STORE. cbn [es_entries es_entries_o es_id]. unfold blocks_SK. cbn [sk_cap sk_id sk_with_thunk sk_fresh Z.eqb app combine map concat sk_elems]. rewrite SID5. apply Permutation_refl.
        - unfold blocks_STORE. cbn [es_entries es_entries_o es_id]. unfold blocks_SK. cbn [sk_cap sk_id sk_with_thunk sk_fresh Z.eqb app combine map concat sk_elems map blk_id fst].
          constructor; [| constructor; [intros []| constructor]]. cbn. intros [K0|[]]. rewrite SID5 in K0.
          exact (D25 BK (es_id S, st, STORE_SIZE) (or_introl eq_refl) (SLB0 _ (proj1 (proj2 SO))) K0).
        - intros K1 es1 EQ1. cbn [es_entries_o] in EQ1. injection EQ1 as <- <-. split; [reflexivity| cbn; clear; lia].
        - eapply (MEMBIO_frameA LB LB SPc); [exact MBO5| exact MBLB| eapply xpres_weaken; [exact XP56| clear; lia| exact FLB| intros q Hq; exact Hq]|].
          apply Forall_forall. intros iv Hiv. apply Forall_forall. intros bk Hbk.
          refine (proj1 (Forall_forall _ _) (AV6 bk (FLB _ (MBLB _ Hbk)) _) iv Hiv).
          rewrite (mb_static_blocks mb R R' MST) in Hbk. intros EQ. exact (nodup_ids_app_ne [(es_id S, st, STORE_SIZE)] _ _ _ NDsm (or_introl eq_refl) Hbk (eq_sym EQ)).
        - destruct (PAYL ltac:(clear - NAR; lia)) as [pD [PIN PNL]]. pose proof DSL as DSL1. unfold zlength in DSL1.
          eapply xpres_bytes_at'; [exact XP56| exact DSm5| right; right; exists (pD, mb_buf R, mb_len R); split; [apply FLB; exact PIN| cbn; rewrite DSL1; clear; lia]|].
          pose proof (AV6 _ (FLB _ PIN)) as K0. cbn [blk_addr blk_size blk_id fst snd] in K0. rewrite DSL1. apply K0.
          exact (PAYS ltac:(clear - NAR; lia) _ PIN).
        - pose proof (AV6 _ FBIN) as K0. cbn [blk_addr blk_size blk_id fst snd] in K0.
          eapply xpres_bytes_at'; [exact XP56| exact DSb5| right; right; exists (pbin, Bb, nB); split; [exact FBIN| cbn; unfold zlength in NBR; clear - NBR; lia]|].
          eapply avoids_sub; [apply K0| clear; lia| unfold zlength in NBR; clear - NBR; lia].
          destruct (drest_ids _ _ _ _ _ _ _ _ _ _ _ _ ND5) as (_ & _ & _ & _ & DBIN & _). intros EQ. exact (DBIN _ _ (or_introl eq_refl) ltac:(right; apply in_or_app; right; exact (proj1 (proj2 SO))) EQ).
        - eapply (BT_frame _ SPc); [exact BT5| exact XP56| exact FTB| unfold SP'; clear - CEIL LO STK0; lia|].
          apply Forall_forall. intros iv Hiv. apply Forall_forall. intros bk Hbk.
          refine (proj1 (Forall_forall _ _) (AV6 bk (FTB _ Hbk) _) iv Hiv).
          destruct (drest_ids _ _ _ _ _ _ _ _ _ _ _ _ ND5) as (_ & _ & _ & DTB & _). intros EQ. exact (DTB _ _ Hbk ltac:(right; right; apply in_or_app; right; exact (proj1 (proj2 SO))) EQ).
        - eapply rw_cells_transport; [exact FR05| exact MU6| exact WM6| apply DJF6; clear; lia].
        - eapply rw_cells_transport; [exact FR25| exact MU6| exact WM6| apply DJF6; unfold RBP, SP'; clear; lia].
        - eapply rw_cells_transport; [exact FR35| exact MU6| exact WM6| apply DJF6; unfold O_F3; clear; lia].
        - eapply rw_cells_transport; [exact FR45| exact MU6| exact WM6| apply DJF6; unfold O_SAVES; clear; lia].
        - exists errv5. eapply rw_cells_transport; [exact ERR5| exact MU6| exact WM6|]. cbn. destruct SBR as (_ & _ & _ & _ & OFF). unfold RERRNO, STORE_SIZE in *. clear - OFF. split; [lia| exact I].
        - exact MI6.
        - exact ST6.
        - eapply (HH_rauxv_frame H HH); [exact AUX5| exact MU6| exact WM6|]. apply Forall_cons; [| apply Forall_nil]. cbn [fst snd].
          destruct SBR as (_ & _ & _ & SH & OFF). unfold RAUXV_CELL, STORE_SIZE, SP' in *. clear - SH OFF CEIL LO STK0 SPB. split; lia.
        - eapply xpres_trans; [exact XA5|]. eapply xpres_weaken; [exact XP56| unfold SP'; clear; lia| exact FLB|].
          intros q Hq. unfold XF. apply rin_ivs_app. left. cbn [rin_ivs fst snd] in Hq |- *. destruct Hq as [Hq|[]]. left. unfold STORE_SIZE. clear - Hq. lia.
        - unfold dnb, blocks_SK. cbn. unfold SK_SIZE, DECODE_CNT, DECODE_BYTES, DECODE_BIG. rewrite ?(big1_small 56) by (unfold BIGB; clear; lia). clear. lia. }
      assert (LED6 : dledger S2 c) by (subst S2; cbv delta [Kth]; unfold dledger, EBS, nent; cbn; pose proof (Z.div_pos c 600 C0 ltac:(clear; lia)); clear - C0 H0; lia).
      eapply (rp_push n cur rem c elen NBe [BK] S2 M' LE w0 w1 w3 w5 w6 j3 m6 mo2 s2' ee E Kth []);
        [exact LP| exact REM| exact LED6| exact CUR| exact CR| exact EL19| exact ER| exact DW6| reflexivity| | exact PE| exact PEE| exact ECNT| exact EBYT| exact EBIG].
      (* [comment removed for export] *)
      assert (NBK : forall b, In b (blocks_ENTRY ee E) -> blk_id b <> blk_id BK).
      { intros b Hb EQ. destruct (nd_app _ _ ND5) as [_ NDR]. unfold drest in NDR. cbn [map app] in NDR. apply List.NoDup_cons_iff in NDR. destruct NDR as [NI _].
        apply NI. rewrite <- EQ. rewrite !map_app. apply in_or_app. left. apply in_map. eapply Permutation_in; [exact PE| exact Hb]. }
      assert (AVK : forall b, In b (blocks_ENTRY ee E) -> avoids [(Ask, Ask + SK_SIZE)] (blk_addr b) (blk_size b)).
      { intros b Hb. pose proof (DISJ5 b BK ltac:(apply in_or_app; right; apply SLX5; right; eapply Permutation_in; [exact PE| exact Hb]) ltac:(apply in_or_app; right; apply SLX5; left; reflexivity) (NBK b Hb)) as D0.
        cbv delta [BK] in D0. cbn [blk_addr blk_size fst snd] in D0. unfold avoids. apply Forall_cons; [cbn [fst snd]; clear - D0; lia| apply Forall_nil]. }
      assert (XP25 : xpres (mid_errblocks M' ++ DREST (BK :: NBe) [] LE) SPc [(Ask, Ask + SK_SIZE)] m2 m5).
      { eapply xpres_trans; [exact XP23|]. eapply xpres_trans; [exact XP34| exact XP45]. }
      assert (EO5 : ENTRYobj (mid_errblocks M' ++ DREST (BK :: NBe) [] LE) m5 ee E).
      { eapply (ENTRYobj_frameX _ SPc); [eapply ENTRYobj_LB_mono; [exact EO2| intros b Hb; apply in_or_app; right; exact Hb]| exact XP25| exact AVK]. }
      assert (EO6 : ENTRYobj (mid_errblocks M' ++ DREST (BK :: NBe) [] LE) m6 ee E).
      { eapply (ENTRYobj_frameX _ SPc); [exact EO5| exact XP56|]. intros b Hb. apply AV6; [apply in_or_app; right; apply SLX5; right; eapply Permutation_in; [exact PE| exact Hb]|].
        intros EQ. exact (D25 b (es_id S, st, STORE_SIZE) ltac:(right; eapply Permutation_in; [exact PE| exact Hb]) (SLB0 _ (proj1 (proj2 SO))) EQ). }
      eapply (ENTRYobj_frame_law _ (DREST NBe [BK] LE) m6 m6 ee E hceil); [exact EO6| | apply xpres_refl| intros b Hb; exact (proj1 (proj2 (EBL b Hb)))].
      intros b Hb. unfold drest. apply in_or_app. left. eapply Permutation_in; [exact PE| exact Hb].
    Qed.

    (* [comment removed for export] *)
    Lemma rp_trip_ok : forall n cur rem c NB S',
      LOOPAT n -> rem - 4 <= Z.of_nat n -> dledger S' c -> cur = Bb + 2 + c -> c + rem = olen_of bs -> 1 <= rem -> DK_OK cur rem NB S'.
    Proof using TR OLEN BUD0 CNT0 BIG0 A0 A1 SO SE SEO STL MBO MP0 MN0 MBB MBS DS DSL PAYL PAYS NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC BUDG AUX SPB BHI SPA ST CEIL LO ERR MI TP RAE HH HX NAR NBR MST POS BTR BT_frame PERM BTFREE RPE CERTO3 TIME.
      intros n cur rem c NB S' LP REM LED CUR CR R1. unfold dK_ok.
      intros NBe M' LE w0 w1 w3 w5 w6 j3 m1 mo1 s1' ee elen E rows ps sn pn ns rax u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 s4w s5w s6w s8w s9w s11w u3 u4 u5 u6
             DW EL19 ER EO PE LT0 FRY NSR SUO SUC ROWS SNR ROK PNO PNB NNUL NSL ECNT EBYT EBIG.
      pose proof DW as (HP1 & KREL1 & MP1 & LM1 & STP1 & NEW1 & CTX1 & EC1 & EB1 & EG1 & _ & _ & _ & SO1 & SID1 & SPM1 & SND1 & SKI1 & _ & _ & _ & _
                        & FR0 & FR2 & FR3 & FR4 & [errv1 ERR1] & MI1 & ST1 & AUX1 & _).
      destruct RCFACTS as (SEQ & SIN & SBR & BEL0 & SUB0 & ND0 & STK0 & LO0 & MF0 & OBJ0 & DJA). hcb. pose proof (word_range sp) as SPR.
      destruct (DWKGF _ _ _ _ _ _ _ _ _ _ DW) as (HB & ND & DISJ & BRS & D2 & D1).
      pose proof (DRESTSUB NBe NB LE) as (SLB & S0 & SLE & SNB & STB & IB & IA & SLX & S3 & SLL).
      pose proof (DRESTSUB ([] : list block) NB LE) as (SLB0 & _ & SLE0 & SNB0 & STB0 & IB0 & IA0 & _ & S30 & SLL0).
      pose proof (dec_stack M M' STP1) as (_ & STKF & STKR & STKP & STKE & _ & _ & _ & _ & _ & STKN & STKT & _ & _ & K11).
      destruct (ent_blocks _ _ _ _ _ _ _ _ _ _ ee E DW PE) as (EBL & EBD & NDE).
      destruct (ent_sub ee E ps sn pn (zlength ns + 1) SUO PNO NDE) as (INS & NES & INP & NEP).
      pose proof (EBL _ ltac:(left; reflexivity)) as (IEE & HEE & OEE & PEE). cbn [blk_addr blk_size fst snd] in HEE, OEE, PEE. unfold ENTRY_SIZE in HEE, OEE.
      destruct (nb_ledger _ _ _ _ _ _ _ _ _ _ c DW LED ltac:(clear - CR OLEN TR R1; lia)) as (NB1 & NB2 & NB3 & C0 & N0 & N23).
      (* [comment removed for export] *)
      eapply (sr_evt_krel H HH); [exact KREL1| eapply fs_ok1; exact MI1|]. intros ms2 ->.
      pose proof TIME as TM. unfold time_sr_stmt, time_sr_stmt_at in TM.
      pose proof LM1 as (_ & _ & _ & _ & _ & VD1 & _).
      eapply (sr_seq H HH).
      { eapply TM with (lo := lo) (B := B) (s := s1') (vf := if mid_vdso M' then 0 else P_cgt_init) (errv := errv1); clear TM; try reflexivity.
        all: try first [exact HP1| exact KREL1| exact AUX1| exact MI1| exact CEIL].
        all: lazymatch goal with
             | |- bv_unsigned _ <= B => unfold SP'; rewrite unsigned_lit by (clear - SPR LO STK0 LO0; lia); clear - SPB; lia
             | |- stk _ _ _ _ => unfold SP'; rewrite unsigned_lit by (clear - SPR LO STK0 LO0; lia); exact ST1
             | |- lo <= _ => unfold SP'; rewrite unsigned_lit by (clear - SPR LO STK0 LO0; lia); clear - LO STKT; lia
             | |- rw_cells _ _ (errno_addr _) _ => rewrite errno_RATP; exact ERR1
             | |- rw_cells _ _ _ [C8 _] => unfold wz in VD1; exact VD1
             | |- _ \/ _ => destruct (mid_vdso M'); [left| right]; reflexivity
             | |- ?G => idtac "TIMEPRE" G
             end. }
      clear TM. intros [ms3 mo3] PO. unfold time_sr_post in PO. cbn [cfg_ms cfg_model] in PO.
      destruct PO as (v0 & v1 & v2 & tv & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m3 & -> & KREL3 & MP3 & MI3 & ST3 & ERR3 & AUX3 & HP3 & MU3 & WM3 & VD3).
      unfold SP' in ST3, MU3. rewrite (unsigned_lit (bv_unsigned sp + -2352)) in ST3, MU3 by (clear - SPR LO STK0 LO0; lia). rewrite errno_RATP in ERR3, MU3.
      change (bv_unsigned sp + -2352) with SPc in ST3, MU3.
      pose proof (dwk_time NBe NB S' M' LE _ j3 m1 mo1 s1' m3 mo3 errv1 DW KREL3 MP3 MI3 ST3 AUX3 HP3 MU3 WM3 VD3 ERR3) as DW3.
      pose proof (xpres_time _ _ _ _ _ _ _ _ _ _ m3 DW MU3 WM3) as XP13. clear MU3 WM3 VD3.
      set (Mt := mkMID (mid_flag M') (mid_ctx M') (mid_err M') (mid_E M') true) in DW3.
      assert (AVv : forall b, In b (blocks_ENTRY ee E) -> avoids VDSO_X (blk_addr b) (blk_size b)).
      { intros b Hb. destruct (EBL b Hb) as (_ & _ & O & _). apply avoid_of_img; [| exact O].
        unfold VDSO_X. apply Forall_cons; [cbn [fst snd]; unfold ECH_Img.A_vdso_func, F_time.A_vdso_func, IMG_LO, IMG_HI; clear; lia| apply Forall_nil]. }
      assert (EO3 : ENTRYobj (DREST NBe NB LE) m3 ee E) by (eapply ENTRYobj_frameX; [exact EO| exact XP13| exact AVv]).
      pose proof EO3 as ((pad1 & pad2 & pad3 & pad4 & L1 & L2 & L3 & L4 & EC3) & _).
      pose proof DW3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FR03 & _ & FR33 & _ & _ & _ & ST3' & _).
      (* [comment removed for export] *)
      eapply (sr_evt_krel H HH); [exact KREL3| eapply (fs_ok2 _ _ _ _ _ _ _ _ tv) with (E := E); [exact PEE| clear - HEE HCEILB; unfold ENTRY_SIZE in *; lia| exact EC3| exact MI3]|].
      cbv beta. intros ms4 (m4 & -> & MU4 & WM4 & MI4 & EC4).
      change (mkENT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) with (with_loadtime E (bv_unsigned tv)) in EC4.
      destruct (ENTRYobj_loadtime NBe NB S' Mt LE _ j3 m3 mo3 s1' ee E (bv_unsigned tv) m4 pad1 pad2 pad3 pad4 DW3 EO3 PE MU4 WM4 EC4 L1 L2 L3 L4) as [EO4 XP34].
      assert (ST4 : stk rsegs m4 lo SPc).
      { eapply stk_transport_disjoint; [exact ST3'| exact MU4| exact WM4|]. cbn. unfold SP', O_EN_LOADTIME in *. clear - HEE CEIL LO STK0. split; [lia| exact I]. }
      assert (DJ4 : forall a n, SPc <= a -> disjoint_from [(ee + O_EN_LOADTIME, ee + 72)] a n).
      { intros a' n' Ha. cbn. unfold SP', O_EN_LOADTIME in *. clear - Ha HEE CEIL LO STK0. split; [lia| exact I]. }
      pose proof (DWKGW NBe NB S' Mt LE _ j3 m3 mo3 s1' m4 [(ee + O_EN_LOADTIME, ee + 72)] _ j3 DW3 MU4 WM4 MI4 ST4
                    ltac:(apply Forall_cons; [right; right; right; exists (en_id E, ee, ENTRY_SIZE); split; [eapply Permutation_in; [exact PE| left; reflexivity]| cbn; unfold O_EN_LOADTIME, ENTRY_SIZE; clear; lia]| apply Forall_nil])
                    ltac:(eapply rw_cells_transport; [exact FR03| exact MU4| exact WM4| apply DJ4; clear; lia])
                    ltac:(eapply rw_cells_transport; [exact FR33| exact MU4| exact WM4| apply DJ4; unfold O_F3; clear; lia])) as DW4.
      clear FR03 FR33 ST3' EC3 EC4.
      pose proof DW4 as (HP4 & KREL4 & MP4 & LM4 & STP4 & NEW4 & CTX4 & EC4 & EB4 & EG4 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & [errv4 ERR4] & _ & _ & AUX4 & _).
      (* [comment removed for export] *)
      assert (XP14 : xpres (DREST NBe NB LE) SPc (VDSO_X ++ [(ee + O_EN_LOADTIME, ee + 72)]) m1 m4).
      { eapply xpres_trans; [eapply xpres_weaken; [exact XP13| clear; lia| intros b Hb; exact Hb| intros q Hq; apply rin_ivs_app; left; exact Hq]|].
        eapply xpres_weaken; [exact XP34| clear; lia| intros b Hb; exact Hb| intros q Hq; apply rin_ivs_app; right; exact Hq]. }
      assert (AV14 : forall b, In b (blocks_ENTRY ee E) -> b <> (en_id E, ee, ENTRY_SIZE) -> avoids (VDSO_X ++ [(ee + O_EN_LOADTIME, ee + 72)]) (blk_addr b) (blk_size b)).
      { intros b Hb NE. unfold avoids. apply Forall_app. split; [exact (AVv b Hb)|]. apply Forall_cons; [| apply Forall_nil]. cbn [fst snd].
        pose proof (EBD b Hb NE). unfold O_EN_LOADTIME, ENTRY_SIZE in *. clear - H0. lia. }
      pose proof EO as (_ & _ & _ & _ & OSU & _). rewrite SUO in OSU. destruct OSU as (SUP & SN0 & _).
      pose proof EO as (_ & _ & OPN & _). rewrite PNO in OPN. destruct OPN as (PNP & _ & _).
      pose proof (suite_cells_size rows) as SCS. pose proof NSL as NSL'. pose proof ROWS as ROWS'. unfold zlength in NSL', ROWS'.
      assert (SUC4 : rw_cells rsegs m4 (en_suites E) (suite_cells rows)).
      { eapply xpres_rw_cells'; [exact XP14| exact SUC| right; right; exists (ps, en_suites E, sn); split; [exact (proj1 (EBL _ INS))| cbn [blk_addr blk_size fst snd]; rewrite SCS; unfold zlength; rewrite ROWS'; clear - SNR; lia]|].
        eapply avoids_sub; [exact (AV14 _ INS NES)| cbn; clear; lia| cbn [blk_addr blk_size fst snd]; rewrite SCS; unfold zlength; rewrite ROWS'; clear - SNR; lia]. }
      assert (PNB4 : bytes_at rsegs m4 (en_pname E) (ns ++ [Z_to_bv 8 0])).
      { eapply xpres_bytes_at'; [exact XP14| exact PNB| right; right; exists (pn, en_pname E, zlength ns + 1); split; [exact (proj1 (EBL _ INP))| cbn [blk_addr blk_size fst snd]; rewrite length_app; cbn [length]; unfold zlength; clear; lia]|].
        eapply avoids_sub; [exact (AV14 _ INP NEP)| cbn; clear; lia| cbn [blk_addr blk_size fst snd]; rewrite length_app; cbn [length]; unfold zlength; clear; lia]. }
      clear XP13 XP34 XP14 AV14 AVv SUC PNB EO EO3.
      (* [comment removed for export] *)
      destruct (dbud_raise NBe NB S' Mt LE _ j3 m4 mo3 s1' (FCC_BYTES + ERRSTR_BYTES) (FCC_CNT + ERRSTR_CNT) 0 DW4) as (RB1 & RB2 & RB3 & FB1 & FB2 & FB3 & _);
        [| unfold FCC_BYTES, ERRSTR_BYTES, VPM_SIZE, SK_SIZE; clear; lia| unfold FCC_CNT, ERRSTR_CNT; clear; lia| clear; lia|].
      { eapply dbud_now; [exact DW4| | |]; unfold FCC_BYTES, ERRSTR_BYTES, VPM_SIZE, SK_SIZE, FCC_CNT, ERRSTR_CNT, DLOOP_BYTES, DLOOP_CNT, DLOOP_BIG, ENTRY_KEPT in *.
        - clear - NB1 EBYT ER CR OLEN TR C0 EL19. lia.
        - clear - NB2 ECNT ER CR OLEN TR C0 EL19. lia.
        - clear - NB3 EBIG ER CR OLEN TR C0 EL19. Z.div_mod_to_equations. lia. }
      pose proof (fcc_spec H HX EGS) as FC. unfold fcc_stmt in FC.
      eapply (sr_seq H HH).
      { eapply FC with (LIB := LE ++ LIB) (LB := DREST NBe NB LE) (M := Mt) (x := x) (lo := lo) (B := B) (E := with_loadtime E (bv_unsigned tv)) (errv := errv4)
                       (rows := rows) (ps := ps) (sn := sn) (pn := pn) (ns := ns); clear FC; try reflexivity.
        all: try first [exact EO4| exact NSR| exact SUO| exact SUC4| exact ROWS| exact SNR| exact ROK| exact PNO| exact PNB4| exact NNUL| exact NSL| exact LM4| exact HP4| exact KREL4
                       | exact AUX4| exact BHI| exact CEIL| exact MI4| exact (fun b Hb => S0 b (SLL b Hb))].
        all: lazymatch goal with
             | |- bv_unsigned _ <= B => unfold SP'; rewrite unsigned_lit by (clear - SPR LO STK0 LO0; lia); clear - SPB; lia
             | |- bv_unsigned _ mod 16 = 0 => unfold SP'; rewrite unsigned_lit by (clear - SPR LO STK0 LO0; lia); clear - SPA; lia
             | |- stk _ _ _ _ => unfold SP'; rewrite unsigned_lit by (clear - SPR LO STK0 LO0; lia); exact ST4
             | |- lo <= _ => unfold SP'; rewrite unsigned_lit by (clear - SPR LO STK0 LO0; lia); subst Mt; unfold FCC_STACK in *; cbn [mid_err] in *; clear - LO STKF; lia
             | |- rw_cells _ _ (errno_addr _) _ => rewrite errno_RATP; exact ERR4
             | |- Forall _ (blocks_ENTRY _ _) => rewrite blocks_with_loadtime; apply Forall_forall; intros b Hb; destruct (EBL b Hb) as (_ & Kb & _); clear - Kb CEIL; lia
             | |- mid_ctx _ = _ => subst Mt; cbn [mid_ctx]; rewrite CTX1; exact CTX
             | |- mid_flag _ = _ => subst Mt; cbn [mid_flag]; exact (proj1 STP1)
             | |- forall b b', In b _ -> In b' _ -> _ => rewrite blocks_with_loadtime; intros b b' Hb Hb' EQ; refine (D2 b' b _ _ (eq_sym EQ)); [eapply Permutation_in; [exact PE| exact Hb']| exact (SLL0 _ Hb)]
             | |- lb_bytes _ + _ + _ + _ <= _ => clear - FB1; lia
             | |- Z.of_nat _ + _ + _ + _ <= _ => clear - FB2; lia
             | |- lb_big _ + _ <= _ => clear - FB3; lia
             | |- ?G => idtac "FCCPRE" G
             end. }
      clear FC. intros [ms5 mo5] PO. unfold fcc_post in PO. cbn [cfg_ms cfg_model] in PO.
      destruct PO as (z0 & z1 & z2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & z3 & z4 & z5 & z6 & m5 & errv5 & s5' & rv & M5 & LBN & -> & RV & KREL5 & MP5 & MI5 & ST5 & ERR5 & AUX5
                      & HP5 & LM5 & STP5 & NEW5 & CTX5 & VD5 & EC5 & EB5 & EG5 & EO5 & XP5).
      unfold SP' in ST5, XP5. rewrite (unsigned_lit (bv_unsigned sp + -2352)) in ST5, XP5 by (clear - SPR LO STK0 LO0; lia). rewrite errno_RATP in ERR5.
      change (bv_unsigned sp + -2352) with SPc in ST5, XP5.
      assert (F5 : mid_flag M5 = 1) by (destruct STP5 as (F5 & _); exact F5).
      assert (CX5 : mid_ctx M5 = CtxReady x) by (rewrite CTX5; subst Mt; cbn [mid_ctx]; rewrite CTX1; exact CTX).
      pose proof (dwk_after_raise NBe NB S' Mt LE _ j3 m4 mo3 s1' m5 mo5 s5' LBN M5 errv5 DW4 KREL5 MP5 MI5 ST5 AUX5 HP5 LM5 STP5 NEW5 F5 CX5 EC5 EB5 EG5 ERR5
                    ltac:(eapply xpres_weaken; [exact XP5| clear; lia| intros b Hb; exact Hb| intros q Hq; apply rin_ivs_app in Hq; apply rin_ivs_app; destruct Hq as [Hq|Hq]; [left; exact Hq| right; apply rin_ivs_app; right; exact Hq]])) as DW5.
      assert (EO5' : ENTRYobj (DREST NBe NB (LBN ++ LE)) m5 ee (with_loadtime E (bv_unsigned tv))).
      { eapply ENTRYobj_LB_mono; [exact EO5|]. intros b Hb. eapply Permutation_in; [apply drest_LEn_perm| exact Hb]. }
      clear EO5 XP5 HP5 LM5 NEW5 CTX5 EO4 SUC4 PNB4 DW4 HP4 KREL4 LM4 AUX4 ERR4 FB1 FB2 FB3 RB1 RB2 RB3 DW3 KREL3 MI3 MP3 ERR3 AUX3 HP3 MI4 ST4 DJ4 MU4 WM4.
      pose proof DW5 as (HP5 & _ & MP5' & LM5 & STP5' & NEW5 & CTX5 & _ & _ & _ & _ & _ & _ & SO5 & SID5 & SPM5 & SND5 & SKI5 & _ & _ & _ & _ & FR05 & _ & FR35 & _ & _ & _ & _ & _ & _).
      pose proof SO5 as (SC5 & SIN5 & EN5).
      (* [comment removed for export] *)
      eapply (sr_evt_krel H HH); [exact KREL5| unfold SP'; eapply (fs_ok3) with (rv := rv) (st := st) (ents := es_entries S');
        [exact RV| | clear - SBR; destruct SBR as (P & _); exact P| destruct SBR as (_ & _ & _ & K & _); clear - K HCEILB; unfold STORE_SIZE in *; lia
        | clear - SPR LO STK0 LO0; lia| exact FR05| exact SC5| exact MI5]|].
      { (* [comment removed for export] *)
        destruct (DWKGF _ _ _ _ _ _ _ _ _ _ DW5) as (HB5 & _). pose proof (DRESTSUB NBe NB (LBN ++ LE)) as (_ & S05 & _ & _ & _ & _ & _ & _ & S35 & _).
        revert EN5. unfold ENTRIES. destruct (es_entries_o S') as [[K es]|]; [| intros ->; clear; lia]. intros (PP & SK5 & _).
        pose proof SK5 as (_ & _ & KIN & _). pose proof (HB5 _ ltac:(apply in_or_app; right; apply S05; apply S35; exact KIN)) as KB. cbn [blk_addr blk_size fst snd] in KB.
        unfold SK_SIZE in KB. clear - PP KB HCEILB. lia. }
      cbv beta. intros ms6 K6.
      destruct K6 as [[R0 ->]|[(R1' & ENZ & ->)|(R1' & EZ & ->)]]; fold (SP' sp).
      - (* [comment removed for export] *)
        eapply (rp_tailX NBe NB S' M5 (LBN ++ LE) _ j3 m5 mo5 s5' ee (Some (with_loadtime E (bv_unsigned tv))));
          [exact DW5| reflexivity| split; [exact EO5'| rewrite blocks_with_loadtime; exact PE]|].
        eapply dbud_now; [exact DW5| | |]; unfold ERRDEBUG_BYTES, DLOOP_BYTES, DLOOP_CNT, DLOOP_BIG, ENTRY_KEPT in *.
        + clear - NB1 EBYT ER CR OLEN TR C0 EL19. lia.
        + clear - NB2 ECNT ER CR OLEN TR C0 EL19. lia.
        + clear - NB3 EBIG ER CR OLEN TR C0 EL19. Z.div_mod_to_equations. lia.
      - (* [comment removed for export] *)
        revert EN5. unfold ENTRIES. destruct (es_entries_o S') as [[K es]|] eqn:ESO; [| intros K0; exfalso; exact (ENZ K0)]. intros (PP & SK5 & LEN5 & F25).
        pose proof DW5 as (_ & KREL5' & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MI5' & _).
        eapply (sr_evt_krel H HH); [exact KREL5'| eapply fs_ok7b; exact MI5'|]. intros ms7 ->.
        eapply (rp_push n cur rem c elen NBe NB S' M5 (LBN ++ LE) w0 w1 w3 w5 w6 j3 m5 mo5 s5' ee (with_loadtime E (bv_unsigned tv)) K es);
          [exact LP| clear - REM EL19; lia| exact LED| exact CUR| exact CR| exact EL19| exact ER| exact DW5| exact ESO| exact EO5'| rewrite blocks_with_loadtime; exact PE| exact PEE| exact ECNT| exact EBYT| exact EBIG].
      - (* [comment removed for export] *)
        eapply (rp_newsk n cur rem c elen NBe NB S' M5 (LBN ++ LE) w0 w1 w3 w5 w6 j3 m5 mo5 s5' ee (with_loadtime E (bv_unsigned tv)));
          [exact LP| clear - REM EL19; lia| exact LED| exact CUR| exact CR| exact EL19| exact ER| exact DW5| exact EZ| exact EO5'| rewrite blocks_with_loadtime; exact PE| exact PEE| exact ECNT| exact EBYT| exact EBIG].
    Qed.

    (* [comment removed for export] *)
    Lemma rp_loop : forall n, LOOPAT n.
    Proof using TR OLEN BUD0 CNT0 BIG0 A0 A1 SO SE SEO STL MBO MP0 MN0 MBB MBS DS DSL PAYL PAYS NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC BUDG AUX SPB BHI SPA ST CEIL LO ERR MI TP RAE HH HX NAR NBR MST POS BTR BT_frame PERM BTFREE RPE CERTO3 TIME.
      induction n as [|n IH]; unfold LOOPAT;
        intros cur rem c NB S' M' LE w0 w1 w3 w4 w5 w6 w9 w10 j3 m' mo' s' rax u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 s5w s6w s7w s8w s9w s11w u3 u4 u5 u6 REM DW LED CUR CR R1.
      { exfalso. clear - REM R1. cbn in REM. lia. }
      destruct (nb_ledger _ _ _ _ _ _ _ _ _ _ c DW LED ltac:(clear - CR OLEN TR R1; lia)) as (NB1 & NB2 & NB3 & C0 & N0 & N23).
      pose proof RPE as RP. unfold rp_entry_stmt in RP.
      eapply RP; clear RP; [exact DW| clear - CUR C0; lia| exact R1| clear - CUR CR OLEN; lia| | | | exact rp_tailA| exact rp_tailZ].
      - eapply dbud_now; [exact DW| | |]; cbn [lb_bytes lb_big length fold_right Z.of_nat]; unfold ENTRY_BYTES, ENTRY_CNT, ENTRY_BIG, DLOOP_BYTES, DLOOP_CNT, DLOOP_BIG.
        + clear - NB1 CR OLEN TR R1 C0. lia.
        + clear - NB2 CR OLEN TR R1 C0. lia.
        + clear - NB3 CR OLEN TR R1 C0. lia.
      - eapply (rp_trip_ok n); [exact IH| clear - REM; lia| exact LED| exact CUR| exact CR| exact R1].
      - eapply (rp_trip_skip n); [exact IH| clear - REM; lia| exact LED| exact CUR| exact CR].
    Qed.
  End LOOP.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma rp_flat : forall M' LE j0 j3 m' mo' s' (rax u0 u1 u2 a0w b1 b2 b3 b4 b5 b6 b7 s4w s5w s6w s8w s9w s10w s11w u3 u4 u5 u6 : word),
    lb_bytes TB + nB + nA + lb_bytes LB + errph_bytes (mid_err M) + ERRSTR_BYTES + DLOOP_BYTES <= hs_LIVE_MAX H ->
    Z.of_nat (length TB) + 2 + Z.of_nat (length LB) + errph_cnt (mid_err M) + ERRSTR_CNT + DLOOP_CNT <= hs_LIVE_CNT_MAX H ->
    lb_big TB + big1 nB + big1 nA + lb_big LB + errph_big (mid_err M) + DLOOP_BIG <= hs_LIVE_BIG_MAX H ->
    DWKG [] [] S M' LE [CB 88 j0; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 st); C8 (Z_to_bv 64 0)] j3 m' mo' s' ->
    hs_SR H POSTc (mkCfg (MS (mkR rax (Z_to_bv 64 SPc) gp (Z_to_bv 64 RATP) u0 u1 u2 sp (Z_to_bv 64 A) a0w b1 b2 b3 b4 b5 b6 b7
                                (Z_to_bv 64 bt) (Z_to_bv 64 Bb) s4w s5w s6w (Z_to_bv 64 (zlength bs)) s8w s9w s10w s11w u3 u4 u5 u6)
                           F (Z_to_bv 64 DF_DEC) fc None m' (seg_rom rsegs)) mo').
  Proof using A0 A1 SO SE SEO STL MBO MP0 MN0 MBB MBS DS DSL PAYL PAYS NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC BUDG AUX SPB BHI SPA ST CEIL LO ERR MI TP RAE HH HX NAR NBR MST POS BTR BT_frame PERM BTFREE RPE CERTO3 TIME.
    intros until u6. intros BUD0 CNT0 BIG0 DW0.
    destruct RCFACTS as (SEQ & SIN & SBR & BEL0 & SUB0 & ND0 & STK0 & LO0 & MF0 & OBJ0 & DJA). hcb. pose proof (word_range sp) as SPR.
    (* [comment removed for export] *)
    pose proof DW0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FRc & _).
    destruct (CB_words 11 m' SPc j0 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 st); C8 (Z_to_bv 64 0)] FRc) as (ws & LW & FRw).
    destruct ws as [|v0 [|v1 [|v2 [|v3 [|v4 [|v5 [|v6 [|v7 [|v8 [|v9 [|v10 [|? ?]]]]]]]]]]]]; try (cbn in LW; discriminate LW). cbn [map app] in FRw. clear LW FRc.
    pose proof (dwkG_fr _ _ _ _ _ _ (eframe v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10) _ _ _ _ DW0 FRw) as DW. clear DW0 FRw.
    pose proof DW as (HP1 & KREL1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & DSb1 & _ & FR0 & _ & FR3 & _ & _ & MI1 & ST1 & _).
    destruct (DWKGF _ _ _ _ _ _ _ _ _ _ DW) as (HB & ND & DISJ & BRS & D2 & D1).
    pose proof (DRESTSUB ([] : list block) ([] : list block) LE) as (_ & _ & _ & _ & _ & IB0 & _).
    pose proof (BRS _ ltac:(apply in_or_app; right; exact IB0)) as (BP & _ & _ & BH & _). cbn [blk_addr blk_size fst snd] in BP, BH.
    pose proof NBR as NBR'. unfold zlength, OSSL_ECH_MAX_ECHCONFIG_LEN in NBR'.
    assert (LED0 : dledger S 0) by (unfold dledger, EBS, nent; rewrite SEO; cbn; clear; lia).
    assert (BDY : DBUD (DREST [] [] LE) M' ERRDEBUG_BYTES 2 0).
    { eapply (dbud_now BUD0 CNT0 BIG0); [exact DW| | |]; cbn; unfold ERRDEBUG_BYTES, DLOOP_BYTES, DLOOP_CNT, DLOOP_BIG; clear; lia. }
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL1| eapply fs_dec with (T := zlength bs); [unfold zlength; clear - NBR'; lia| exact MI1]|].
    cbv beta. intros ms2 (a1' & a2' & ->).
    destruct (andb (32 <=? zlength bs) (zlength bs <? 1500)) eqn:G.
    2: { (* [comment removed for export] *) eapply rp_tailY; [exact DW| reflexivity| clear; lia| unfold R_PASSED_NULL_PARAMETER; clear; lia| exact BDY]. }
    apply andb_prop in G. destruct G as [G1 G2]. apply Z.leb_le in G1. apply Z.ltb_lt in G2.
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL1| unfold SP'; eapply fs_hdr with (T := zlength bs) (st := st) (bs := bs);
      [clear - G1 G2; lia| reflexivity| exact DSb1| exact BP| unfold zlength in *; clear - BH HCEILB NBR'; lia| clear - SPR LO STK0 LO0; lia| exact FR0| exact MI1]|].
    cbv beta. intros ms3 (a0' & a1'' & a2'' & a3' & K3). fold (SP' sp) in K3.
    destruct K3 as [[LT ->]|[[Z0 ->]|([OL1 OL2] & m1 & -> & MU & WM & MI2 & FR1)]].
    - (* [comment removed for export] *) eapply rp_tailY; [exact DW| reflexivity| clear; lia| unfold R_INTERNAL_ERROR; clear; lia| exact BDY].
    - (* [comment removed for export] *) eapply rp_done. exact DW.
    - (* [comment removed for export] *)
      fold (SP' sp) in MU, FR1.
      assert (ST2 : stk rsegs m1 lo SPc) by (eapply stk_transport_disjoint; [exact ST1| exact MU| exact WM|]; cbn; unfold SP' in *; clear - LO STK0 CEIL; split; [lia| exact I]).
      pose proof (DWKGW [] [] S M' LE _ j3 m' mo' s' m1 [(SPc, bv_unsigned sp + -2264)] _ j3 DW MU WM MI2 ST2
                    ltac:(apply Forall_cons; [right; left; cbn; unfold SP'; clear; lia| apply Forall_nil]) FR1
                    ltac:(eapply rw_cells_transport; [exact FR3| exact MU| exact WM| cbn; unfold SP', O_F3; clear; split; [lia| exact I]])) as DW1.
      eapply (rp_loop (conj G1 G2) (conj OL1 OL2) BUD0 CNT0 BIG0 (Z.to_nat (olen_of bs)) (Bb + 2) (olen_of bs) 0); [rewrite Z2Nat.id by (clear - OL1; lia); clear; lia| exact DW1| exact LED0| clear; lia| clear; lia| exact OL1].
  Qed.
End RC.
