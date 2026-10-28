(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX Frame.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap AsCall AsCallX AsStack0 AsAuxv ECH_AImg ECH_Xpres ECH_ARep ECH_ALib
  ECH_ALibMF ECH_Iface ECH_AStmt_C1 ECH_AC1_zalloc ECH_AC1_free ECH_AC1_malloc ECH_AC1_dup ECH_AC1_marr ECH_AStmt_C3 ECH_AStmt_C4 ECH_AStmt_C5 ECH_AStmt_C7 ECH_AStmt_C10 ECH_AStmt_C13
  ECH_AStmt_C6 ECH_AStmt_C8 ECH_AStmt_C9 ECH_AKit ECH_AKitSeg ECH_AsKit ECH_AsKitK ECH_AC13_entry ECH_AC13_store ECH_AC7_kit ECH_AC7_rd ECH_AC7_rd2 ECH_AC7_bioread ECH_ARostr ECH_ALibMid ECH_AC11_fail
  ECH_AStmt_C12 ECH_AC12_addstr ECH_AC13 ECH_AC14_kit
  N6_memchr F_time ECH_AC10 ECH_AC13_small ECH_AC5_small ECH_AC5_new ECH_AC5_push ECH_AC14_decexts_seg ECH_AC14_fcc_seg ECH_AC14_decexts ECH_AC14_fcc
  ECH_AC14_bio2buf_seg ECH_AC14_ladder_seg ECH_AC14_ladloop ECH_AC14_fmt_seg ECH_AC14_flat_seg ECH_AC14_entry_seg ECH_AStmt_C14
  F_strspn N6_strspn ECH_AC14_b2b ECH_AC14_fmt ECH_AC14_dec ECH_AC14_pushK.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import ECH_B64.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim StrFun.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Section RC.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HX : asan_rt_hyps_x H.
  Hypothesis RAISE : araise_stmt H.
  Let HH : asan_rt_hyps H := proj1 HX.
  Let SM6 : stack_malloc_6_stmt H := proj1 (proj2 (proj2 (proj2 (proj2 HX)))).
  Let SF6 : stack_free_6_stmt H := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HX))))).
  Let SSF8 : set_shadow_f8_stmt := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HX))))))).
  Let PERM : rheap_perm H := HHx_rheap_perm H HX.

  (* [comment removed for export] *)
  Variables (PF9new : ctxphase -> list (Z * list Z)) (PF9free : list (Z * list Z)).
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model) (s : as_St H) (LIB LB : list block) (LF : list fframe)
            (M : libmid) (x : ctxinfo) (st mb lo B : Z) (S : storerep) (R : membio) (ds : list byte) (errv : word) (CH : list (Z * Z)).
  Hypotheses (VIS0 : as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                         F (Z_to_bv 64 P_OSSL_ECHSTORE_read_echconfiglist) fc None m (seg_rom asegs))
             (A0 : a0 = Z_to_bv 64 st) (A1 : a1 = Z_to_bv 64 mb)
             (SO : STOREobj LB m st S) (SE : es_entries S = 0) (SEO : es_entries_o S = None) (STL : st + STORE_SIZE <= lo) (SSH : STORE_shad m st S)
             (MBO : MEMBIO H LB m mb R) (MP0 : mb_pos R = 0) (MN0 : mb_nread R = 0) (MBB : MEMBIO_below mb R lo) (MBS : MEMBIO_sep mb R)
             (MSH : MEMBIO_shad m mb R) (PAY : PAYLOAD_shad m R)
             (DS : bytes_at asegs m (mb_buf R) ds) (DSL : zlength ds = mb_len R)
             (PAYL : 1 <= mb_len R -> exists pD, In (pD, mb_buf R, mb_len R) LB /\ forall b, In b LIB -> blk_id b <> pD)
             (PAYL2 : 1 <= mb_len R -> forall pD, In (pD, mb_buf R, mb_len R) LB -> pD <> es_id S)
             (NDsm : List.NoDup (map blk_id ((es_id S, st, STORE_SIZE) :: blocks_MEMBIO mb R)))
             (LM : LIBMID LIB m M) (SUBL : forall b, In b LIB -> In b LB) (CTX : mid_ctx M = CtxReady x) (MF1 : mid_flag M = 1)
             (DJ6 : forall b b', In b LIB -> In b' ((es_id S, st, STORE_SIZE) :: blocks_MEMBIO mb R) -> blk_id b <> blk_id b')
             (HP : as_RHEAP H s (mid_errblocks M ++ LB) m) (KREL : as_AKREL H s (mkCfg msF mo))
             (BUD : lb_bytes (mid_errblocks M ++ LB) + mid_bytes M + DECODE_BYTES + ERRSTR_BYTES <= as_LIVE_MAX H)
             (BUDC : Z.of_nat (length (mid_errblocks M ++ LB)) + mid_cnt M + DECODE_CNT + ERRSTR_CNT <= as_LIVE_CNT_MAX H)
             (AUX : as_rauxv_ok H m B) (SPB : bv_unsigned sp <= B) (BHI : B < 2^64) (SPA : bv_unsigned sp mod 16 = 0)
             (ST : stk asegs m lo (bv_unsigned sp)) (CEIL : aceil <= lo) (LO : lo <= bv_unsigned sp - READCFG_STACK M) (ST0 : stack0 m lo (bv_unsigned sp))
             (ERR : rw_cells asegs m (errno_addr tp) [C4 errv]) (MI : mem_inv asegs m) (TP : tp = Z_to_bv 64 ATP) (AC : ACONST m)
             (MCO : mid_closed_ok H M)
             (RFS : as_RFS H LF m) (LFB : (length LF + READCFG_LF <= READCFG_MAXLIVE)%nat) (ATH : athr_cells m)
             (CHN : as_chain H m (bv_unsigned s0) CH) (CHB : forall fp' ra', In (fp', ra') CH -> bv_unsigned sp + 16 <= fp')
             (PF : pf_ok (as_TR H) (PF_readcfg PF9new PF9free M) (bv_unsigned ra) CH) (ALW : READCFG_COST H M <= as_AL H s)
             (RAE : bv_unsigned ra mod 2 = 0).

  (* [comment removed for export] *)
  Local Notation L0c := (L0 LB M).
  Local Notation S1c := (S1 sp).
  Local Notation KGc := (KG sp).
  Local Notation POSTc := (POST H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo s LIB LB LF M st mb lo B S R ds).
  Local Notation XFc := (XF M st mb R).
  Local Notation SAVESc := (SAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
  Local Notation CH1c := (CH1 ra sp CH).
  Local Notation LF1c := (LF1 LF).
  Local Notation XSFc := (XSF H).
  Local Notation LEDGERc := (LEDGER H s).
  Local Notation pf_sitec := (pf_site H PF9new PF9free ra sp M CH PF).
  Local Notation rp_okKc := (rp_okK H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo s LIB LB LF M st mb lo B S R ds CH).
  (* [comment removed for export] *)
  Local Notation "'RCI' f" := (f H HX RAISE PF9new PF9free ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc msF m mo s LIB LB LF M x st mb lo B S R ds errv CH
                                 VIS0 A0 A1 SO SE SEO STL SSH MBO MP0 MN0 MBB MBS MSH PAY DS DSL PAYL PAYL2 NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC AUX SPB BHI SPA ST CEIL LO ST0 ERR MI TP AC MCO RFS LFB ATH CHN CHB PF ALW RAE)
    (at level 10, f at level 0).

  (* [comment removed for export] *)
  Local Notation AFWc := (AFW H ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m s LIB LB LF M st mb lo B R ds CH).

  (* [comment removed for export] *)
  Variables (p : bptr) (A nA : Z) (pbin : bptr) (Bb nB : Z) (bs : list byte) (R' : membio) (bt : Z) (TB : list block).
  Variable BT : mem -> Prop.
  Variables (ff fp n : Z) (fj24 tpb fj128 fj2 jz jg e5 : list byte) (w224 : word).
  Hypotheses (NAR : 1 <= mb_len R <= nA /\ nA <= 512 * 3)                 (* [comment removed for export] *)
             (NBR : 0 <= zlength bs <= nB /\ nB <= mb_len R /\ mb_len R < OSSL_ECH_MAX_ECHCONFIG_LEN)
             (MST : mb_static R R') (POS : mb_pos R' = mb_len R)
             (BTR : 0 <= bt < 2^64 /\ Z.of_nat (length TB) <= 7 /\ lb_bytes TB <= 3072)
             (BT_frame : forall (L : list block) (SP : Z) (X : list (Z * Z)) (m1 m2 : mem),
                 BT m1 -> xpres H L SP X m1 m2 -> (forall b, In b TB -> In b L) -> aceil <= SP ->
                 (forall b, In b TB -> avoids X (blk_addr b) (blk_size b) /\ shavoids X (blk_addr b) (blk_size b)) ->
                 mem_inv asegs m2 -> BT m2)
             (FRESH : fresh_frame H LF 6 ff fp).
  (* [comment removed for export] *)
  Hypothesis AUXV : aauxv_ok m B.
  Local Notation SH := (Z.shiftr ff 3 + ASHB).

  (* [comment removed for export] *)
  Local Notation adwkGc := (adwkG H ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m s LIB LB LF M st mb lo B S R ds CH p A nA pbin Bb nB bs R' TB BT ff fp n fj24 tpb fj128 fj2 jz jg e5).
  Local Notation adwkc := (adwk H ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m s LIB LB LF M st mb lo B S R ds CH p A nA pbin Bb nB bs R' bt TB BT ff fp n fj24 tpb fj128 fj2 jz jg e5).
  Local Notation drestc := (drest LB p A nA pbin Bb nB TB).
  Local Notation dffc := (dff sp fp n fj24 tpb fj128 fj2).
  Local Notation dfshc := (dfsh e5).
  Local Notation dsg2c := (dsg2 A ff).
  Local Notation dsg1c := (dsg1 st Bb bt ff).
  Local Notation "'DCT' f" := (f H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo s LIB LB LF M st mb lo B S R ds CH p A nA pbin Bb nB bs R' bt TB BT ff fp n fj24 tpb fj128 fj2 jz jg e5) (at level 10, f at level 0).
  Local Notation "'DCJ' f" := (f H HX RAISE PF9new PF9free ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc msF m mo s LIB LB LF M x st mb lo B S R ds errv CH
                                 VIS0 A0 A1 SO SE SEO STL SSH MBO MP0 MN0 MBB MBS MSH PAY DS DSL PAYL PAYL2 NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC AUX SPB BHI SPA ST CEIL LO ST0 ERR MI TP AC MCO RFS LFB ATH CHN CHB PF ALW RAE
                                 p A nA pbin Bb nB bs R' bt TB BT ff fp n fj24 tpb fj128 fj2 jz jg e5 NAR NBR MST POS BTR BT_frame FRESH)
    (at level 10, f at level 0).
  Local Notation adwkG_esc := (adwkG_es H ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m s LIB LB LF M x st mb lo B S R ds CH CTX p A nA pbin Bb nB bs R' TB BT ff fp n fj24 tpb fj128 fj2 jz jg e5).
  Local Notation adwkG_hfc := (adwkG_heap_facts H HX ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m s LIB LB LF M st mb lo B S R ds CH p A nA pbin Bb nB bs R' TB BT ff fp n fj24 tpb fj128 fj2 jz jg e5).

  Let SS00 : set_shadow_00_stmt := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HX)))))).

  (* [comment removed for export] *)
  Local Notation KADVc := (DCT dK_adv).
  Local Notation KTXc := (DCT dK_tailX).
  Local Notation KPUSHc := (DCT dK_push).
  Local Notation dbudc := (dbud H).
  (* [comment removed for export] *)
  Local Notation adwkG_wc := (DCJ adwkG_w).
  Local Notation adwkG_xc := (DCJ adwkG_x).
  Local Notation adwkG_libXc := (DCJ adwkG_libX).
  Local Notation adwk_raisec := (DCJ adwk_raise).
  Local Notation drest_subc := (drest_sub LIB LB SUBL p A nA pbin Bb nB TB).
  Local Notation drest_idsc := (drest_ids LB p A nA pbin Bb nB TB).


  (* [comment removed for export] *)
  Lemma rc_facts_c :
       S = store_empty (es_id S) /\ In (es_id S, st, STORE_SIZE) L0c /\ ablock_range H st STORE_SIZE
    /\ (forall b, In b L0c -> ablock_range H (blk_addr b) (blk_size b)) /\ (forall b, In b LB -> In b L0c)
    /\ List.NoDup (map blk_id L0c) /\ 9152 <= READCFG_STACK M /\ 0 <= lo /\ MEMFLAG m 1
    /\ (forall b', In b' ((es_id S, st, STORE_SIZE) :: blocks_MEMBIO mb R) -> In b' L0c)
    /\ (forall b b', In b LIB -> In b' ((es_id S, st, STORE_SIZE) :: blocks_MEMBIO mb R) ->
          blk_addr b + blk_size b + 16 <= blk_addr b' \/ blk_addr b' + blk_size b' + 16 <= blk_addr b)
    /\ afsb_ok H /\ 0x7fff7f800000 <= aceil <= 0x7fffff800000
    /\ rp_s1 (bv_unsigned sp) mod 32 = 0 /\ bv_unsigned sp - 464 <= rp_s1 (bv_unsigned sp) <= bv_unsigned sp - 448 /\ bv_unsigned sp < 2^64.
  Proof. exact (RCI rc_facts). Qed.


  (* [comment removed for export] *)
  Definition AENT0 (pe : bptr) : entrep := mkENT 0 0 None 0 0 None 0 0 None 0 0 0 None 0 0 0 0 None pe.
  Definition AENT1 (pe : bptr) : entrep := mkENT AECH_VERSION 0 None 0 0 None 0 0 None 0 0 0 None 0 0 0 0 None pe.

  (* [comment removed for export] *)
  Lemma ade_facts : forall Lx NB S' M' LE fr1 wee v192 v200 v208 v224 v232 fr3 tpl shb b2 shd um uf m' s',
    adwkGc Lx NB S' M' LE fr1 wee v192 v200 v208 v224 v232 fr3 tpl shb b2 shd um uf m' s' ->
       aceil <= S1c /\ bv_unsigned sp - 464 <= S1c <= bv_unsigned sp - 448 /\ S1c mod 32 = 0 /\ bv_unsigned sp < 2^64
    /\ 0 < Bb /\ Bb + zlength bs <= aceil /\ In (pbin, Bb, nB) (mid_errblocks M' ++ drestc Lx NB LE) /\ zlength bs <= nB /\ nB < 1500
    /\ (forall b, In b Lx -> Bb + nB <= blk_addr b \/ blk_addr b + blk_size b <= Bb)
    /\ (forall b, In b (mid_errblocks M' ++ drestc Lx NB LE) -> blk_addr b + blk_size b <= aceil)
    /\ (forall b, In b (mid_errblocks M' ++ drestc Lx NB LE) -> ablock_range H (blk_addr b) (blk_size b))
    /\ mid_flag M' = 1 /\ MEMFLAG m' 1 /\ IMPL_mem m' /\ GOT_mem m'
    /\ accessible m' Bb nB /\ aapp Bb nB /\ 0x7fff7f800000 <= aceil <= 0x7fffff800000
    /\ lo <= S1c - 9152 + 464 /\ 0 <= lo.
  Proof using VIS0 A0 A1 SO SE SEO STL SSH MBO MP0 MN0 MBB MBS MSH PAY DS DSL PAYL PAYL2 NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC AUX SPB BHI SPA ST CEIL LO ST0 ERR MI TP AC MCO RFS LFB ATH CHN CHB PF ALW RAE HH HX RAISE SM6 SF6 SSF8 PERM NAR NBR MST POS BTR BT_frame FRESH.
    intros until s'. intros DW.
    pose proof DW as (HP1 & LM1 & STP & NEW & CTX1 & EC & EB & LC & LBY & SO1 & SSH1 & SID & SPM & SND & SKI & MBO1 & MSH1 & DSm1 & DSb1 & [jb1 CBb1] & ADb1 & [ja1 CBa1] & ADa1 & BT1
                      & FR0 & FR1 & SZ1 & FR2 & FR3 & SZ3 & FRG & FRS & FF1 & FSH1 & LSH1 & RFS1 & [errv1 ERR1] & AUX1 & MI1 & AC1 & ST1 & STK1 & CHN1 & XA1 & LED1).
    destruct rc_facts_c as (SEQ & SIN & SBR & BLK0 & SUB0 & ND0 & STK0 & LO0 & MF0 & OBJ0 & DJA & AFSB & ACB & Q1 & Q2 & SPR). change (rp_s1 (bv_unsigned sp)) with S1c in Q1, Q2.
    destruct (adwkG_hfc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ DW) as (BRS & ND & DISJ & D2 & D1).
    pose proof (drest_subc Lx NB LE) as (SLB & SL0 & SLE & SNB & STB & IB & IA & SLX & S3 & SLL).
    assert (IB2 : In (pbin, Bb, nB) (mid_errblocks M' ++ drestc Lx NB LE)) by (apply in_or_app; right; exact IB).
    pose proof (BRS _ IB2) as (E1 & E2 & E3 & E4 & E5 & E6 & E7). cbn [blk_addr blk_size fst snd] in E1, E2, E3, E4, E5, E6, E7.
    pose proof LM1 as (IM & MF & _ & _ & _ & _ & _ & _ & GM & _). pose proof STP as (F1 & _). rewrite F1 in MF.
    pose proof NBR as NBRq. unfold zlength in NBRq |- *. unfold OSSL_ECH_MAX_ECHCONFIG_LEN in NBRq.
    repeat match goal with |- _ /\ _ => split end; try assumption.
    - clear - CEIL LO STK0 Q2; lia.
    - clear - Q2; lia.
    - clear - Q2; lia.
    - clear - E5 NBRq; lia.
    - clear - NBRq; lia.
    - clear - NBRq; lia.
    - intros b Hb. pose proof (DISJ b (pbin, Bb, nB) ltac:(apply in_or_app; right; apply SLX; exact Hb) IB2 ltac:(apply (D2 b (pbin, Bb, nB) Hb); exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (drest_subc [] NB LE))))))))) as K.
      cbn [blk_addr blk_size fst snd] in K. clear - K. lia.
    - intros b Hb. pose proof (BRS _ Hb) as (_ & _ & _ & _ & K5 & _). exact K5.
    - eapply (addressable_accessible _ _ _ _ _ ADb1); [apply Z.le_refl| apply Z.le_refl| unfold AAPP_HI; clear - E5 ACB; lia].
    - clear - ACB; lia.
    - clear - ACB; lia.
    - clear - LO STK0 Q2; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma alx_not_client : forall Lx NB LE M' s' m' b a,
    as_RHEAP H s' (mid_errblocks M' ++ drestc Lx NB LE) m' -> In b Lx -> blk_addr b <= a < blk_addr b + blk_size b -> aceil <= S1c ->
    aclient_addr H (mid_errblocks M' ++ drestc [] NB LE) S1c a -> False.
  Proof using HH HX.
    intros Lx NB LE M' s' m' b a HP' Hb Ha AS1 HC.
    assert (BIN' : In b (mid_errblocks M' ++ drestc Lx NB LE)) by (apply in_or_app; right; rewrite drest_app; apply in_or_app; left; exact Hb).
    pose proof (ah_nodup H HH _ _ _ HP') as ND. destruct (drest_idsc _ _ _ _ ND) as (D1 & D2 & _).
    refine (ECH_AC14_kit.blk_not_client H HX _ _ _ (mid_errblocks M' ++ drestc [] NB LE) S1c b a HP' BIN' _ _ AS1 Ha HC).
    - intros b' Hb'. apply in_app_or in Hb'. apply in_or_app. destruct Hb' as [Hb'|Hb']; [left; exact Hb'| right; rewrite drest_app; apply in_or_app; right; exact Hb'].
    - intros b' Hb'. apply in_app_or in Hb'. destruct Hb' as [Hb'|Hb'].
      + intros E. apply (D1 b' b Hb' ltac:(rewrite drest_app; apply in_or_app; left; exact Hb)). exact E.
      + intros E. apply (D2 b b' Hb Hb'). symmetry. exact E.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma de_setter : forall (entry which : Z) Lx NB S' M' LE fr1 wee v192 v200 v208 v224 v232 fr3 tpl shb b2 shd um uf m1 s1' msF1 mo1 (a f ra0 : Z) K
      (u0 u1 u2 c2 c3 c4 c5 c6 c7 s2w s4w s5w s6w s7w s8w s9w s10w s11w u3 u4 u5 u6 : word) (Q : config -> Prop),
    skset_stmt_at H entry which ->
    adwkGc Lx NB S' M' LE fr1 wee v192 v200 v208 v224 v232 fr3 tpl shb b2 shd um uf m1 s1' -> cells_size fr1 = 128%nat -> cells_size fr3 = 104%nat -> length shd = 256%nat ->
    In (sk_id K, a, SK_SIZE) Lx -> SKobj (mid_errblocks M' ++ drestc Lx NB LE) m1 a K -> SK_shad m1 a K -> sk_cap K = 0 ->
    0 <= f < 2^64 -> 0 <= ra0 < 2^64 -> ra0 mod 2 = 0 ->
    as_VIS H s1' msF1 = MS (mkR (Z_to_bv 64 ra0) (Z_to_bv 64 S1c) gp (Z_to_bv 64 ATP) u0 u1 u2 sp (Z_to_bv 64 S1c) (Z_to_bv 64 a) (Z_to_bv 64 f) c2 c3 c4 c5 c6 c7
                                s2w (Z_to_bv 64 SH) s4w s5w s6w s7w s8w s9w s10w s11w u3 u4 u5 u6) F (Z_to_bv 64 entry) fc None m1 (seg_rom asegs) ->
    as_AKREL H s1' (mkCfg msF1 mo1) ->
    (forall m2 msF2 mo2 (v0 v1 v2 d1 d2 d3 d4 d5 d6 d7 v3 v4 v5 v6 : word),
       adwkGc Lx NB S' M' LE fr1 wee v192 v200 v208 v224 v232 fr3 tpl shb b2 shd um uf m2 s1' ->
       SKobj (mid_errblocks M' ++ drestc Lx NB LE) m2 a (sk_with_thunk K which f) -> SK_shad m2 a (sk_with_thunk K which f) ->
       xpres H (mid_errblocks M' ++ drestc Lx NB LE) S1c [(a, a + SK_SIZE)] m1 m2 ->
       as_VIS H s1' msF2 = MS (mkR (Z_to_bv 64 ra0) (Z_to_bv 64 S1c) gp (Z_to_bv 64 ATP) v0 v1 v2 sp (Z_to_bv 64 S1c) (Z_to_bv 64 a) d1 d2 d3 d4 d5 d6 d7
                                   s2w (Z_to_bv 64 SH) s4w s5w s6w s7w s8w s9w s10w s11w v3 v4 v5 v6) F (ret_pc (Z_to_bv 64 ra0)) fc None m2 (seg_rom asegs) ->
       as_AKREL H s1' (mkCfg msF2 mo2) -> as_MPRES H mo1 mo2 -> as_SR H Q (mkCfg msF2 mo2)) ->
    as_SR H Q (mkCfg msF1 mo1).
  Proof using VIS0 A0 A1 SO SE SEO STL SSH MBO MP0 MN0 MBB MBS MSH PAY DS DSL PAYL PAYL2 NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC AUX SPB BHI SPA ST CEIL LO ST0 ERR MI TP AC MCO RFS LFB ATH CHN CHB PF ALW RAE HH HX RAISE SM6 SF6 SSF8 PERM NAR NBR MST POS BTR BT_frame FRESH.
    intros until Q. intros SPEC DW SZ1 SZ3 LSH KIN SKO SKSH C0 FR RAR RAE0 VIS1 KREL1 KQ.
    pose proof DW as (HP1 & LM1 & STP & NEW & CTX1 & EC & EB & LC & LBY & SO1 & SSH1 & SID & SPM & SND & SKI & MBO1 & MSH1 & DSm1 & DSb1 & [jb1 CBb1] & ADb1 & [ja1 CBa1] & ADa1 & BT1
                      & FR0 & FR1 & SZ1' & FR2 & FR3 & SZ3' & FRG & FRS & [lb1 FF1] & FSH1 & LSH1 & RFS1 & [errv1 ERR1] & AUX1 & MI1 & AC1 & ST1 & STK1 & CHN1 & XA1 & LED1).
    destruct (ade_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ DW) as (AS1 & Q2 & Q1 & SPR & BP & BH & IB2 & NBL & NB15 & BLX & BEL & BRS & F1 & MF & IM & GM & ACCB & APB & ACB & LOS & LO0).
    destruct rc_facts_c as (SEQ & SIN & SBR & BLK0 & SUB0 & ND0 & STK0 & LO0' & MF0 & OBJ0 & DJA & AFSB & ACB' & Q1' & Q2' & SPR'). change (rp_s1 (bv_unsigned sp)) with S1c in Q1', Q2'.
    pose proof AFSB as (AF1 & AF2 & AF3 & AF4). unfold AIMG_TOP in AF1. unfold AFS_SIZE in AF2.
    pose proof (fresh_frame_facts H _ _ _ _ FRESH) as (_ & FQ1 & FQ2 & FQ64 & FQ8 & FP1 & FP2 & FP3 & FP4 & FQ5 & FQ6 & FB1 & FB2 & FB3).
    change (fsz 6) with 4096 in FQ2, FQ6. unfold AFS_HDR, AFS_FLAGS, AFS_SIZE, AIMG_TOP in FQ1, FQ2, FP1, FP2, FP3, FP4, FQ5, FQ6, FB1, FB2.
    pose proof (drest_subc Lx NB LE) as (SLB & SL0 & SLE & SNB & STB & IB & IA & SLX & S3 & SLL).
    (* [comment removed for export] *)
    assert (KINL : In (sk_id K, a, SK_SIZE) (mid_errblocks M' ++ drestc Lx NB LE)) by (apply in_or_app; right; apply SLX; exact KIN).
    pose proof (BRS _ KINL) as (K1 & K2 & K3 & K4 & K5 & K6 & K7). cbn [blk_addr blk_size fst snd] in K1, K2, K3, K4, K5, K6, K7. unfold SK_SIZE in K3, K5, K6, K7.
    unfold AIMG_TOP, AFS_SIZE in K4, K6. pose proof (aapp_not_shadowland _ _ K7) as NSK.
    assert (SHF : SH = sh ff) by (unfold sh, ASHB; rewrite Z.shiftr_div_pow2 by (clear; lia); rewrite ASHADOW_BASE_val; change (2 ^ 3) with 8; clear; lia).
    pose proof (sh_aapp_range _ _ AF4 ltac:(unfold AFS_SIZE; clear; lia)) as (W1 & W2 & W3). unfold nsh, AFS_SIZE in W2. unfold AIMG_TOP in W1.
    pose proof (sh_mono (as_FSB H) ff ltac:(clear - FQ5; lia)) as SYL. pose proof (sh_mono (ff + 4096) _ FQ6) as SYU.
    pose proof (sh_add8 ff 512) as SY8. replace (ff + 8 * 512) with (ff + 4096) in SY8 by (clear; lia).
    (* [comment removed for export] *)
    unfold skset_stmt_at in SPEC.
    eapply (ahh_evt_then H HH); [exact KREL1| exact VIS1| |].
    { eapply SPEC with (lo := lo) (a := a) (f := f) (K := K) (LB := mid_errblocks M' ++ drestc Lx NB LE); clear SPEC;
        [reflexivity| reflexivity| exact FR| exact SKO| | exact SKSH| | exact AC1| | exact CEIL| | exact MI1].
      - split; [unfold SK_SIZE; clear - K5 CEIL; lia| left; exact C0].
      - split; [exact (BRS _ KINL)| intros NC; exfalso; exact (NC C0)].
      - rewrite unsigned_lit by (clear - Q2 SPR AS1 ACB; lia). exact ST1.
      - rewrite unsigned_lit by (clear - Q2 SPR AS1 ACB; lia). clear - LOS; lia. }
    intros msF2 mo2 KREL2 MP2 PO. cbn beta in PO. unfold skset_post in PO.
    destruct PO as (v0 & v1 & v2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & m2 & VIS2 & MU & WM & MI2 & AC2 & ST2 & SKO2).
    rewrite (unsigned_lit S1c) in MU, ST2 by (clear - Q2 SPR AS1 ACB; lia). unfold SK_SIZE in MU.
    (* [comment removed for export] *)
    assert (DJF : forall q n', S1c <= q -> disjoint_from [(lo, S1c); (a, a + 56)] q n').
    { intros q n' Hq. cbn. clear - Hq K5 AS1. split; [lia| split; [lia| exact I]]. }
    assert (DJff : disjoint_from [(lo, S1c); (a, a + 56)] ff 4096) by (cbn; clear - AS1 FQ5 FQ6 AF2 K6 CEIL; split; [lia| split; [lia| exact I]]).
    assert (DJsh : disjoint_from [(lo, S1c); (a, a + 56)] SH 512).
    { rewrite SHF. cbn. unfold ALOWSH_LO, AHI_LO in NSK. pose proof (sh_mono _ _ (Z.le_trans _ _ _ FQ6 AF2)) as SYC.
      assert (SHC : sh aceil < AHI_LO) by exact W3. unfold AHI_LO in SHC.
      clear - AS1 ACB CEIL SYL SYU SY8 W1 NSK SYC SHC. split; [lia| split; [| exact I]]. unfold sh in *. rewrite ?ASHADOW_BASE_val in *. lia. }
    assert (NSH : Forall (fun iv : Z * Z => snd iv <= ASHADOW_BASE \/ AHI_LO <= fst iv) [(lo, S1c); (a, a + 56)]).
    { apply Forall_cons; [cbn; right; clear - ACB CEIL; unfold AHI_LO; lia|]. apply Forall_cons; [cbn; clear - NSK; rewrite ASHADOW_BASE_val; unfold ALOWSH_LO in NSK; lia| apply Forall_nil]. }
    assert (SKSH2 : SK_shad m2 a (sk_with_thunk K which f)).
    { destruct SKSH as [SA _]. split; [| cbn [sk_cap sk_with_thunk]; intros NC; exfalso; exact (NC C0)].
      eapply addressable_across2; [exact SA| exact K7| exact MU| exact WM| exact NSH]. }
    assert (XP12 : xpres H (mid_errblocks M' ++ drestc Lx NB LE) S1c [(a, a + SK_SIZE)] m1 m2).
    { eapply (xpres_of_munch H); [exact HH| exact HP1| exact MU| exact WM|].
      apply Forall_cons; [left; cbn; clear - AS1 CEIL; lia|].
      apply Forall_cons; [right; cbn [fst snd]; intros q Hq; cbn [rin_ivs fst snd]; left; unfold SK_SIZE; exact Hq| apply Forall_nil]. }
    eapply (KQ m2 msF2 mo2); [| exact SKO2| exact SKSH2| exact XP12| exact VIS2| exact KREL2| exact MP2].
    eapply (adwkG_wc Lx NB S' M' LE fr1 wee v192 v200 v208 v224 v232 fr3 tpl shb b2 shd um uf m1 s1' m2 _ fr1 wee v192 v200 v208 v224 v232 fr3 tpl lb1 shb b2 shd);
      [exact DW| exact MU| exact WM| exact MI2| exact ST2| | | exact SZ1| | | exact SZ3| | | exact LSH].
    - apply Forall_cons; [left; cbn; clear; lia|]. apply Forall_cons; [| apply Forall_nil].
      repeat right. exists (sk_id K, a, SK_SIZE). split; [exact KIN| cbn; unfold SK_SIZE; clear; lia].
    - eapply rw_cells_transport; [exact FR1| exact MU| exact WM| apply DJF; clear; lia].
    - eapply rw_cells_transport; [exact FR2| exact MU| exact WM| apply DJF; clear; lia].
    - eapply rw_cells_transport; [exact FR3| exact MU| exact WM| apply DJF; clear; lia].
    - eapply rw_cells_transport; [exact FF1| exact MU| exact WM|]. unfold dff, arp_fframe2. cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul]. exact DJff.
    - eapply rw_cells_transport; [exact FSH1| exact MU| exact WM|]. unfold dfsh, arp_fshadow. cbn [cells_size csize Nat.add length poison_bytes repeat Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul].
      exact DJsh.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma M_eq1c : forall M', mid_step M M' -> mkMID 1 (mid_ctx M') (mid_err M') (mid_E M') (mid_vdso M') = M'.
  Proof. clear. intros [f c e E0 v] (F1 & _). cbn in *. subst. reflexivity. Qed.
  Lemma ENTRYs_mono : forall L L' mx ps es, Forall2 (fun q Eq => ENTRYobj L mx q Eq) ps es -> (forall b, In b L -> In b L') -> Forall2 (fun q Eq => ENTRYobj L' mx q Eq) ps es.
  Proof. clear. intros L L' mx ps es F2 SUB. induction F2; constructor; [eapply ENTRYobj_LB_mono; eauto| assumption]. Qed.
  (* [comment removed for export] *)
  Lemma ENTRYs_rehome : forall L L' mx ps es (SP : Z), Forall2 (fun q Eq => ENTRYobj L mx q Eq) ps es ->
    (forall b, In b (concat (map (fun pe => blocks_ENTRY (fst pe) (snd pe)) (combine ps es))) -> In b L' /\ blk_addr b + blk_size b <= SP) ->
    Forall2 (fun q Eq => ENTRYobj L' mx q Eq) ps es.
  Proof.
    clear - HX. intros L L' mx ps es SP F2. induction F2 as [|q Eq ps' es' EO F2 IH]; intros KEEP; constructor.
    - eapply (ENTRYobj_frame_law H L L' mx mx q Eq SP); [exact EO| intros b Hb; apply (proj1 (KEEP b ltac:(cbn [combine map concat fst snd]; apply in_or_app; left; exact Hb)))| apply xpres_refl| intros b Hb; apply (proj2 (KEEP b ltac:(cbn [combine map concat fst snd]; apply in_or_app; left; exact Hb)))].
    - apply IH. intros b Hb. apply KEEP. cbn [combine map concat fst snd]. apply in_or_app. right. exact Hb.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma de_pushcall : forall (cur rem : Z) (S0 : storerep) (um0 uf0 : Z) (ph0 : errphase)
      Lx NB S' M2 LE2 (w16 w32 w40 : word) (v192 v200 v208 v224 v232 : word) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : word) (tpl um uf elen hb hc : Z) m1 s1' msF1 mo1 (ee : Z) (E : entrep) K es
      (rax u0 u1 u2 a1w a2w a3w a4w a5w a6w a7w s2w s4w s5w s6w s8w s9w s11w u3 u4 u5 u6 : word),
    adwkc Lx NB S' M2 LE2 w16 w32 w40 (wz (cur + 4 + elen)) (wz ee) v192 v200 v208 v224 v232 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tpl um uf m1 s1' ->
    es_entries_o S' = Some (K, es) -> EBS S' = EBS S0 -> nent S' = nent S0 ->
    ENTRYobj (drestc Lx NB LE2) m1 ee E -> ENTRY_shad m1 ee E -> Permutation (blocks_ENTRY ee E) Lx -> 0 < ee ->
    5 * Z.of_nat (length (blocks_ENTRY ee E)) <= 2 * (elen + 4) -> lb_bytes (blocks_ENTRY ee E) <= ENTRY_KEPT elen ->
    19 <= elen -> 4 + elen <= rem -> Bb + 2 <= cur -> cur + rem <= Bb + zlength bs -> nent S' <= 65 ->
    dbudc (drestc Lx NB LE2) M2 hb hc -> SKPUSH_COST K <= hb -> 1 <= hc ->
    um + SKPUSH_COST K <= um0 + ENTRY_CM elen + (errph_bytes ph0 - errph_bytes (mid_err M2)) ->
    uf + 8 * sk_cap K <= uf0 + ENTRY_CF elen + (errph_bytes ph0 - errph_bytes (mid_err M2)) ->
    um + SKPUSH_COST K <= DECODE_CUM_BYTES -> uf + 8 * sk_cap K <= DECODE_CUM_BYTES ->
    KADVc cur rem NB S0 um0 uf0 ph0 ->
    as_VIS H s1' msF1 = MS (mkR rax (Z_to_bv 64 S1c) gp (Z_to_bv 64 ATP) u0 u1 u2 sp (Z_to_bv 64 S1c) (Z_to_bv 64 (es_entries S')) a1w a2w a3w a4w a5w a6w a7w
                                s2w (Z_to_bv 64 SH) s4w s5w s6w (Z_to_bv 64 (rem - 4)) s8w s9w (Z_to_bv 64 elen) s11w u3 u4 u5 u6)
                        F (Z_to_bv 64 ADE_PUSH) fc None m1 (seg_rom asegs) ->
    as_AKREL H s1' (mkCfg msF1 mo1) -> as_MPRES H mo mo1 ->
    as_SR H POSTc (mkCfg msF1 mo1).
  Proof using VIS0 A0 A1 SO SE SEO STL SSH MBO MP0 MN0 MBB MBS MSH PAY DS DSL PAYL PAYL2 NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC AUX SPB BHI SPA ST CEIL LO ST0 ERR MI TP AC MCO RFS LFB ATH CHN CHB PF ALW RAE HH HX RAISE SM6 SF6 SSF8 PERM NAR NBR MST POS BTR BT_frame FRESH AUXV.
    intros until u6. intros DW ESO EBS0 NEN0 EO ESH PE EEP ECNT EBYT EL19 ER CUR1 CUR2 N65 DB HB1 HC1 UM1 UF1 UMD UFD KADV VIS1 KREL1 MP1.
    pose proof DW as DWG. unfold adwk in DWG.
    pose proof DWG as (HP1 & LM1 & STP & NEW & CTX1 & EC & EB & LC & LBY & SO1 & SSH1 & SID & SPM & SND & SKI & MBO1 & MSH1 & DSm1 & DSb1 & [jb1 CBb1] & ADb1 & [ja1 CBa1] & ADa1 & BT1
                       & FR0 & FR1 & SZ1 & FR2 & FR3 & SZ3 & FRG & FRS & [lb1 FF1] & FSH1 & LSH1 & RFS1 & [errv1 ERR1] & AUX1 & MI1 & AC1 & ST1 & STK1 & CHN1 & XA1 & LED1).
    destruct (ade_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ DWG) as (AS1 & Q2 & Q1 & SPR & BP & BH & IB2 & NBL & NB15 & BLX & BEL & BRS & F1 & MF & IM & GM & ACCB & APB & ACB & LOS & LO0).
    destruct rc_facts_c as (SEQ & SIN & SBR & BLK0 & SUB0 & ND0 & STK0 & LO0' & MF0 & OBJ0 & DJA & AFSB & ACB' & Q1' & Q2' & SPR'). change (rp_s1 (bv_unsigned sp)) with S1c in Q1', Q2'.
    pose proof AFSB as (AF1 & AF2 & AF3 & AF4). unfold AIMG_TOP in AF1. unfold AFS_SIZE in AF2.
    pose proof (fresh_frame_facts H _ _ _ _ FRESH) as (_ & FQ1 & FQ2 & FQ64 & FQ8 & FP1 & FP2 & FP3 & FP4 & FQ5 & FQ6 & FB1 & FB2 & FB3).
    change (fsz 6) with 4096 in FQ2, FQ6. unfold AFS_HDR, AFS_FLAGS, AFS_SIZE, AIMG_TOP in FQ1, FQ2, FP1, FP2, FP3, FP4, FQ5, FQ6, FB1, FB2.
    destruct (adwkG_hfc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ DWG) as (_ & ND & DISJ & D2 & D1).
    pose proof (drest_subc Lx NB LE2) as (SLB & SL0 & SLE & SNB & STB & IB & IA & SLX & S3 & SLL).
    pose proof (dec_stack M M2 STP) as (_ & _ & _ & STKP & _).
    assert (CHBx : forall fp' ra', In (fp', ra') CH1c -> S1c + 16 <= fp').
    { intros fp' ra' [Ex|Hin]; [injection Ex as <- <-; clear - Q2; lia| pose proof (CHB _ _ Hin) as CB'; clear - CB' Q2; lia]. }
    assert (SHF : SH = sh ff) by (unfold sh, ASHB; rewrite Z.shiftr_div_pow2 by (clear; lia); rewrite ASHADOW_BASE_val; change (2 ^ 3) with 8; clear; lia).
    pose proof (sh_aapp_range _ _ AF4 ltac:(unfold AFS_SIZE; clear; lia)) as (W1 & W2 & W3). unfold nsh, AFS_SIZE in W2.
    assert (SHT : sh AIMG_TOP = 0x80178800) by reflexivity. rewrite SHT in W1.
    pose proof (sh_mono (as_FSB H) ff ltac:(clear - FQ5; lia)) as SYL. pose proof (sh_mono (ff + 4096) _ FQ6) as SYU.
    pose proof (sh_add8 ff 512) as SY8. replace (ff + 8 * 512) with (ff + 4096) in SY8 by (clear; lia).
    (* [comment removed for export] *)
    set (P := es_entries S') in *.
    pose proof SO1 as (SC1 & SIN1 & EN1). unfold ENTRIES in EN1. rewrite ESO in EN1. destruct EN1 as (PP & SKO & LEN & F2).
    pose proof SSH1 as (STOP & STAD & ENS). unfold ENTRIES_shad in ENS. rewrite ESO in ENS. destruct ENS as ((SKSH & PTOP & DTOP) & F2S).
    destruct (SKI K es ESO) as [KC KCAP].
    pose proof SKO as (_ & _ & KIN & KNC & KCAP2 & _ & _ & KDAT). unfold sk_num, zlength in KNC. rewrite <- LEN in KNC, KCAP.
    pose proof N65 as N65'. unfold nent in N65'. rewrite ESO in N65'.
    assert (N64 : Z.of_nat (length es) <= 65) by (clear - N65'; lia).
    remember (concat (map (fun pe => blocks_ENTRY (fst pe) (snd pe)) (combine (sk_elems K) es))) as EBl eqn:EBeq.
    assert (PNB : Permutation (blocks_SK P K ++ EBl) NB).
    { unfold blocks_STORE in SPM. rewrite ESO, SID, <- EBeq in SPM. exact (Permutation_cons_inv SPM). }
    pose proof (blocks_SK_facts P K ltac:(clear - KNC; lia)) as (SKB1 & SKL1 & SKL1' & _).
    pose proof (sk_grow_le (sk_cap K) ltac:(clear - KNC; lia)) as [GR GR5].
    pose proof (errph_nonneg (mid_err M2)) as [EP0 EC0].
    set (Lp := mid_errblocks M2 ++ drestc Lx NB LE2) in *.
    assert (SKsub : forall b, In b (blocks_SK P K) -> In b Lp).
    { intros b Hb. subst Lp. apply in_or_app. right. apply SNB. eapply Permutation_in; [exact PNB|]. apply in_or_app. left. exact Hb. }
    (* [comment removed for export] *)
    assert (LpB : lb_bytes Lp + SKPUSH_COST K <= as_LIVE_MAX H).
    { subst Lp. rewrite lb_bytes_app. destruct DB as [DB1 _]. clear - DB1 EB HB1 EP0. lia. }
    assert (LpC : Z.of_nat (length Lp) + 1 <= as_LIVE_CNT_MAX H).
    { subst Lp. rewrite length_app, Nat2Z.inj_add. destruct DB as [_ DB2]. clear - DB2 EC HC1 EC0. lia. }
    assert (CAPM : sk_cap K <= SK_CAP_MAX) by (unfold SK_CAP_MAX; clear - KCAP N64; lia).
    assert (PC0 : 0 <= SKPUSH_COST K) by (unfold SKPUSH_COST; clear - GR; lia).
    assert (HAL : as_Cm H (SKPUSH_COST K) + as_Cf H (8 * sk_cap K) <= as_AL H s1').
    { eapply (RCI LEDGER_pay); [exact LED1| exact PC0| clear - KNC; lia| exact UMD| exact UFD]. }
    (* [comment removed for export] *)
    assert (EIN' : In (en_id E, ee, ENTRY_SIZE) Lp) by (subst Lp; apply in_or_app; right; apply SLX; eapply Permutation_in; [exact PE| left; reflexivity]).
    pose proof (BEL _ EIN') as EEH. cbn [blk_addr blk_size fst snd] in EEH. unfold ENTRY_SIZE in EEH.
    eapply (ahh_evt_then H HH); [exact KREL1| exact VIS1| eapply ade_segP;
      [exact FR2| clear - PP PTOP ACB; unfold AAPP_HI, SK_SIZE in *; lia| clear - EEP EEH ACB; lia| clear - AS1 ACB; lia| clear - Q2 SPR; lia| exact MI1]|].
    intros msF2 mo2 KREL2 MP2 VIS2. cbn beta in VIS2.
    pose proof (askpush_spec H HX) as PS. unfold skpush_stmt in PS.
    eapply (ah_seq H HH).
    { eapply PS with (lo := lo) (B := B) (LB := Lp) (s := s1') (a := P) (p := ee) (v := 1) (K := K) (CH := CH1c); clear PS;
        [exact VIS2| reflexivity| reflexivity| ..]; rewrite ?unsigned_lit by (first [unfold ADE_R15; clear; lia| clear - AS1 ACB Q2 SPR; lia]).
      all: try first [exact HP1| exact KREL2| exact AUX1| exact ST1| exact CEIL| exact MI1| exact LpB| exact LpC| exact AC1| exact CHN1| exact SKSH| exact HAL| exact CHBx].
      all: lazymatch goal with
           | |- 0 < _ < _ => clear - EEP EEH ACB; lia
           | |- SKobj _ _ _ _ => eapply SKobj_LB_mono; [exact SKO| intros b Hb; subst Lp; apply in_or_app; right; apply SL0; apply S3; exact Hb]
           | |- sk_push_nocmp _ => left; exact KC
           | |- sk_cap _ <= SK_CAP_MAX => exact CAPM
           | |- _ <= B => clear - SPB Q2; lia
           | |- _ mod 16 = 0 => clear - Q1; Z.div_mod_to_equations; lia
           | |- _ <= _ - SKPUSH_STACK => clear - LO STKP Q2; lia
           | |- rw_cells _ _ (errno_addr _) _ => exact ERR1
           | |- @eq _ _ (Z_to_bv 64 ATP) => reflexivity
           | |- C1env _ _ => split; [exact MF| split; [exact IM| exact GM]]
           | |- pf_ok _ _ _ _ => apply pf_sitec; intros e He; unfold PF_readcfg, PF_read_priv; do 16 (apply in_or_app; right); apply in_or_app; left;
                                unfold PF_entry; do 9 (apply in_or_app; right); apply in_or_app; left; exact He
           | |- ?G => idtac "PUSHPRE" G
           end. }
    clear PS. intros [msF8 mo8] PO. unfold skpush_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (z0 & z1 & z2 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & z3 & z4 & z5 & z6 & m8 & errv8 & s8' & LB' & K' & data' & cap' & did' &
                    VIS8 & KREL8 & MP8 & MI8 & AC8 & ST8 & ERR8 & AUX8 & KEQ & PLB & HP8 & SO8 & SKSH8 & XP8 & (v8 & (MF8 & IM8 & GM8) & VLE) & AL8).
    rewrite (unsigned_lit S1c) in ST8, XP8 by (clear - AS1 ACB Q2 SPR; lia).
    assert (V8 : v8 = 1) by (destruct MF8 as (fb8 & _ & _ & V01); clear - VLE V01; lia). subst v8.
    (* [comment removed for export] *)
    assert (LED8 : LEDGERc s8' (um + SKPUSH_COST K) (uf + 8 * sk_cap K)).
    { eapply (RCI LEDGER_step); [exact LED1| exact PC0| clear - KNC; lia| exact AL8]. }
    (* [comment removed for export] *)
    assert (LPE : Lp = mid_errblocks M2 ++ Lx ++ NB ++ (TB ++ (pbin, Bb, nB) :: (p, A, nA) :: LE2 ++ LB)) by (subst Lp; unfold drest; reflexivity).
    rewrite LPE in PLB.
    pose proof (ECH_AC14_kit.skpush_perm _ _ P _ _ _ _ (mid_errblocks M2) Lx EBl (TB ++ (pbin, Bb, nB) :: (p, A, nA) :: LE2 ++ LB) LB' NB KEQ PLB PNB ltac:(unfold sk_num, zlength; clear - KNC; lia)) as [PL' CAPS].
    set (LB0 := TB ++ (pbin, Bb, nB) :: (p, A, nA) :: LE2 ++ LB) in *.
    set (REST := mid_errblocks M2 ++ Lx ++ EBl ++ LB0) in *.
    set (SK' := blocks_SK P K') in *.
    assert (IDK : sk_id K' = sk_id K) by (rewrite KEQ; reflexivity).
    assert (ELK : sk_elems K' = sk_elems K ++ [ee]) by (rewrite KEQ; reflexivity).
    assert (CMK : sk_comp K' = sk_comp K) by (rewrite KEQ; reflexivity).
    assert (C0' : 0 <= sk_cap K') by (clear - CAPS KNC GR; lia).
    assert (CAP' : sk_cap K' <= 2 * (Z.of_nat (length es) + 1) + 4).
    { destruct CAPS as [C1|[[C00 C4]|(CG & NC & C4)]]; [rewrite C1; clear - KCAP; lia| rewrite C4; clear; lia|].
      rewrite CG. unfold sk_num, zlength in NC. rewrite <- LEN in NC. unfold sk_grow. clear - NC C4 KCAP KNC. Z.div_mod_to_equations. lia. }
    assert (INR : forall b, In b REST -> In b LB') by (intros b Hb; eapply Permutation_in; [apply Permutation_sym; exact PL'| apply in_or_app; right; exact Hb]).
    assert (INK : forall b, In b SK' -> In b LB') by (intros b Hb; eapply Permutation_in; [apply Permutation_sym; exact PL'| apply in_or_app; left; exact Hb]).
    assert (R_LB : forall b, In b LB -> In b REST) by (intros b Hb; subst REST LB0; do 3 (apply in_or_app; right); apply in_or_app; right; right; right; apply in_or_app; right; exact Hb).
    assert (R_LE : forall b, In b LE2 -> In b REST) by (intros b Hb; subst REST LB0; do 3 (apply in_or_app; right); apply in_or_app; right; right; right; apply in_or_app; left; exact Hb).
    assert (R_TB : forall b, In b TB -> In b REST) by (intros b Hb; subst REST LB0; do 3 (apply in_or_app; right); apply in_or_app; left; exact Hb).
    assert (R_BIN : In (pbin, Bb, nB) REST) by (subst REST LB0; do 3 (apply in_or_app; right); apply in_or_app; right; left; reflexivity).
    assert (R_PA : In (p, A, nA) REST) by (subst REST LB0; do 3 (apply in_or_app; right); apply in_or_app; right; right; left; reflexivity).
    assert (R_LX : forall b, In b Lx -> In b REST) by (intros b Hb; subst REST; apply in_or_app; right; apply in_or_app; left; exact Hb).
    assert (R_EB : forall b, In b EBl -> In b REST) by (intros b Hb; subst REST; do 2 (apply in_or_app; right); apply in_or_app; left; exact Hb).
    assert (R_ERR : forall b, In b (mid_errblocks M2) -> In b REST) by (intros b Hb; subst REST; apply in_or_app; left; exact Hb).
    assert (R_LL : forall b, In b (LE2 ++ LIB) -> In b REST) by (intros b Hb; apply in_app_or in Hb; destruct Hb as [Hb|Hb]; [apply R_LE; exact Hb| apply R_LB; apply SUBL; exact Hb]).
    pose proof (Permutation_NoDup (Permutation_map blk_id PL') (ah_nodup H HH _ _ _ HP8)) as ND'.
    assert (IDSK : forall b1 b2, In b1 SK' -> In b2 REST -> blk_id b2 <> blk_id b1) by (intros b1 b2 H1 H2; apply not_eq_sym; exact (nodup_ids_app_ne _ _ _ _ ND' H1 H2)).
    assert (DJ : forall b1 b2, In b1 SK' -> In b2 REST -> blk_addr b1 + blk_size b1 + 16 <= blk_addr b2 \/ blk_addr b2 + blk_size b2 + 16 <= blk_addr b1)
      by (intros b1 b2 H1 H2; exact (ECH_AC14_kit.perm_split_disjoint H HX _ _ _ _ _ _ _ HP8 PL' H1 H2)).
    assert (HB8 : forall b, In b LB' -> 0 < blk_addr b /\ blk_addr b mod 16 = 0 /\ 0 <= blk_size b /\ AIMG_TOP <= blk_addr b /\ blk_addr b + blk_size b <= aceil /\ aapp (blk_addr b) (blk_size b)).
    { intros b Hb. pose proof (ah_blocks H HH _ _ _ _ HP8 Hb) as (B1 & B2 & B3 & B4 & B5 & B6 & B7). repeat split; assumption. }
    assert (SKF : forall b, In b SK' -> aapp (blk_addr b) (blk_size b) /\ blk_addr b mod 8 = 0 /\ 0 <= blk_size b).
    { intros b Hb. pose proof (HB8 _ (INK _ Hb)) as (_ & B2 & B3 & _ & _ & B7). split; [exact B7|]. split; [clear - B2; Z.div_mod_to_equations; lia| exact B3]. }
    (* [comment removed for export] *)
    assert (AV : forall b, In b REST -> avoids (memflag_foot ++ ASK_foot P K') (blk_addr b) (blk_size b) /\ shavoids (memflag_foot ++ ASK_foot P K') (blk_addr b) (blk_size b)).
    { intros b Hb. pose proof (HB8 _ (INR _ Hb)) as (B1 & B2 & B3 & B4 & B5 & B7).
      pose proof (ECH_AC14_kit.ASK_foot_app P K' (blk_addr b) (blk_size b) B7 B3 ltac:(clear - B2; Z.div_mod_to_equations; lia) C0'
                    ltac:(intros b1 H1; pose proof (SKF _ H1) as (Qa & Qb & Qc); split; [exact Qa|]; split; [exact Qb|]; pose proof (DJ _ _ H1 Hb); lia)) as [Aa Ab].
      split; [apply ECH_AC14_kit.avoids_app; [apply ECH_AC14_kit.avoids_memflag; exact B4| exact Aa]| apply ECH_AC14_kit.shavoids_app; [apply ECH_AC14_kit.shavoids_memflag; [exact B7| exact B3]| exact Ab]]. }
    assert (AVF : forall a n', aceil <= a -> avoids (memflag_foot ++ ASK_foot P K') a n').
    { intros a n' Ha. apply ECH_AC14_kit.avoids_app; [apply ECH_AC14_kit.avoids_memflag; unfold AIMG_TOP; clear - Ha ACB; lia|].
      apply ECH_AC14_kit.ASK_foot_stack; [exact Ha| exact C0'| intros b Hb; exact (proj1 (SKF _ Hb))]. }
    assert (SKF6 : forall b, In b SK' -> blk_addr b + blk_size b + 16 <= as_FSB H \/ as_FSB H + AFS_SIZE <= blk_addr b - 16).
    { intros b Hb. pose proof (ah_blocks H HH _ _ _ _ HP8 (INK _ Hb)) as (_ & _ & _ & _ & _ & B6 & _). exact B6. }
    pose proof (aapp_not_shadowland _ _ AF4) as NSF. unfold AFS_SIZE in NSF.
    assert (SHC : sh aceil < AHI_LO) by exact W3.
    assert (AVff : avoids (memflag_foot ++ ASK_foot P K') ff 4096).
    { unfold ECH_AC14_kit.avoids. apply Forall_app. split.
      - unfold memflag_foot, A_mem_inited. constructor; [cbn [fst snd]; right; clear - FQ1; lia| constructor].
      - unfold ASK_foot, SK_foot. apply Forall_app. split.
        + constructor; [cbn [fst snd]; pose proof (SKF6 _ ltac:(subst SK'; unfold blocks_SK; left; reflexivity)) as B6; cbn [blk_addr blk_size fst snd] in B6; unfold AFS_SIZE, SK_SIZE in *; clear - B6 FQ5 FQ6; lia|].
          destruct (Z.eqb_spec (sk_cap K') 0) as [E0|NE]; [constructor| constructor; [| constructor]].
          cbn [fst snd]. pose proof (SKF6 _ ltac:(subst SK'; unfold blocks_SK; rewrite (proj2 (Z.eqb_neq _ _) NE); right; left; reflexivity)) as B6; cbn [blk_addr blk_size fst snd] in B6.
          unfold AFS_SIZE in *; clear - B6 FQ5 FQ6; lia.
        + destruct (Z.eqb_spec (sk_cap K') 0) as [E0|NE]; [constructor| constructor; [| constructor]].
          cbn [fst snd]. pose proof (proj1 (SKF _ ltac:(subst SK'; unfold blocks_SK; rewrite (proj2 (Z.eqb_neq _ _) NE); right; left; reflexivity))) as AP2. cbn [blk_addr blk_size fst snd] in AP2.
          pose proof (HB8 _ (INK _ ltac:(subst SK'; unfold blocks_SK; rewrite (proj2 (Z.eqb_neq _ _) NE); right; left; reflexivity))) as (_ & _ & B3 & _ & B5 & _). cbn [blk_addr blk_size fst snd] in B3, B5.
          pose proof (sh_aapp_range _ _ AP2 B3) as (T1 & T2 & T3). rewrite SHT in T1. pose proof (sh_mono _ _ AF2) as T4.
          unfold ALOWSH_LO, AHI_LO in *. clear - NSF T1 T2 T3 T4 SHC FQ5 FQ6 AF2. unfold sh in T4. rewrite ?ASHADOW_BASE_val in *. lia. }
    assert (AVfsh : avoids (memflag_foot ++ ASK_foot P K') (sh ff) 512).
    { unfold ECH_AC14_kit.avoids. apply Forall_app. split.
      - unfold memflag_foot, A_mem_inited. constructor; [cbn [fst snd]; right; clear - SYL W1; rewrite ?ASHADOW_BASE_val in *; lia| constructor].
      - unfold ASK_foot, SK_foot. apply Forall_app. split.
        + constructor; [cbn [fst snd]; pose proof (aapp_not_shadowland _ _ (proj1 (SKF _ ltac:(subst SK'; unfold blocks_SK; left; reflexivity)))) as NS; cbn [blk_addr blk_size fst snd] in NS;
                        pose proof (sh_mono _ _ (Z.le_trans _ _ _ FQ6 AF2)) as SYC;
                        unfold ALOWSH_LO, AHI_LO, SK_SIZE in *; clear - NS SYL SYU SY8 SYC W1 SHC; rewrite ?ASHADOW_BASE_val in *; lia|].
          destruct (Z.eqb_spec (sk_cap K') 0) as [E0|NE]; [constructor| constructor; [| constructor]].
          cbn [fst snd]. pose proof (aapp_not_shadowland _ _ (proj1 (SKF _ ltac:(subst SK'; unfold blocks_SK; rewrite (proj2 (Z.eqb_neq _ _) NE); right; left; reflexivity)))) as NS; cbn [blk_addr blk_size fst snd] in NS.
          pose proof (sh_mono _ _ (Z.le_trans _ _ _ FQ6 AF2)) as SYC.
          unfold ALOWSH_LO, AHI_LO in *; clear - NS SYL SYU SY8 SYC W1 SHC; rewrite ?ASHADOW_BASE_val in *; lia.
        + destruct (Z.eqb_spec (sk_cap K') 0) as [E0|NE]; [constructor| constructor; [| constructor]].
          cbn [fst snd]. pose proof (SKF6 _ ltac:(subst SK'; unfold blocks_SK; rewrite (proj2 (Z.eqb_neq _ _) NE); right; left; reflexivity)) as B6; cbn [blk_addr blk_size fst snd] in B6.
          pose proof (HB8 _ (INK _ ltac:(subst SK'; unfold blocks_SK; rewrite (proj2 (Z.eqb_neq _ _) NE); right; left; reflexivity))) as (_ & B2 & B3 & _ & B5 & _). cbn [blk_addr blk_size fst snd] in B2, B3, B5.
          unfold AFS_SIZE in B6. unfold sh, nsh. clear - B6 B2 B3 FQ5 FQ6 FQ8 C0'. Z.div_mod_to_equations. lia. }
    (* [comment removed for export] *)
    set (NB' := SK' ++ EBl ++ Lx).
    assert (HP9 : as_RHEAP H s8' (mid_errblocks M2 ++ drestc [] NB' LE2) m8).
    { eapply PERM; [exact HP8|]. etransitivity; [exact PL'|]. subst NB' REST LB0. unfold drest. cbn [app].
      transitivity (mid_errblocks M2 ++ SK' ++ Lx ++ EBl ++ TB ++ (pbin, Bb, nB) :: (p, A, nA) :: LE2 ++ LB).
      { rewrite (app_assoc SK' (mid_errblocks M2)), (app_assoc (mid_errblocks M2) SK'). apply Permutation_app_tail. apply Permutation_app_comm. }
      apply Permutation_app_head. rewrite <- ?app_assoc. apply Permutation_app_head.
      rewrite (app_assoc Lx EBl), (app_assoc EBl Lx). apply Permutation_app_tail. apply Permutation_app_comm. }
    assert (SUBN : forall b, In b SK' \/ In b EBl \/ In b Lx -> In b NB') by (intros b Hb; subst NB'; destruct Hb as [Hb|[Hb|Hb]]; apply in_or_app; [left| right; apply in_or_app; left| right; apply in_or_app; right]; exact Hb).
    set (L7 := EBl ++ Lx ++ LE2 ++ LB).
    assert (R_L7 : forall b, In b L7 -> In b REST).
    { intros b Hb. subst L7. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [apply R_EB; exact Hb|]. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [apply R_LX; exact Hb|].
      apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [apply R_LE; exact Hb| apply R_LB; exact Hb]. }
    assert (N7 : forall b, In b (SK' ++ L7) -> In b (NB' ++ LE2 ++ LB)).
    { intros b Hb. subst NB' L7. clear - Hb. rewrite <- !app_assoc. apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left; exact Hb| right].
      apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left; exact Hb| right].
      apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left; exact Hb| right]. exact Hb. }
    (* [comment removed for export] *)
    assert (TF : forall Ax cs, rw_cells asegs m1 Ax cs -> S1c <= Ax -> rw_cells asegs m8 Ax cs).
    { intros Ax cs RC HA. eapply (xpres_rw_cells' H); [exact XP8| exact RC| left; exact HA| apply AVF; clear - HA AS1; lia]. }
    pose proof (TF _ _ FR0 ltac:(clear; lia)) as FR0'. pose proof (TF _ _ FR1 ltac:(clear; lia)) as FR1'. pose proof (TF _ _ FR2 ltac:(clear; lia)) as FR2'.
    pose proof (TF _ _ FR3 ltac:(clear; lia)) as FR3'. pose proof (TF _ _ FRG ltac:(clear; lia)) as FRG'. pose proof (TF _ _ FRS ltac:(clear - Q2; lia)) as FRS'.
    assert (FF8 : rw_cells asegs m8 ff (dffc tpl lb1)).
    { eapply (xpres_rw_cells' H); [exact XP8| exact FF1| |].
      - right; right; right; right; left. unfold dff, arp_fframe2. cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul]. unfold AFS_SIZE. clear - FQ5 FQ6; lia.
      - unfold dff, arp_fframe2. cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul]. exact AVff. }
    assert (FSH8 : rw_cells asegs m8 SH (dfshc (b8 0xf8) (b8 0xf8) (poison_bytes 256 0xf8))).
    { rewrite SHF in FSH1 |- *. eapply (xpres_rw_cells' H); [exact XP8| exact FSH1| |].
      - right; right; right; right; right; left. unfold dfsh, arp_fshadow. cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul]. unfold AFS_SIZE. clear - SYL SYU SY8; lia.
      - unfold dfsh, arp_fshadow. cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul]. exact AVfsh. }
    (* [comment removed for export] *)
    destruct (PAYL ltac:(clear - NAR; lia)) as [pD [PIN _]]. pose proof DSL as DSL1. unfold zlength in DSL1.
    assert (DSm8 : bytes_at asegs m8 (mb_buf R) ds).
    { eapply (xpres_bytes_at' H); [exact XP8| exact DSm1| right; right; left; exists (pD, mb_buf R, mb_len R); split; [apply INR, R_LB; exact PIN| cbn; rewrite DSL1; clear; lia]|].
      pose proof (proj1 (AV _ (R_LB _ PIN))) as K0. cbn [blk_addr blk_size fst snd] in K0. rewrite DSL1. exact K0. }
    pose proof NBR as NBRq. unfold zlength in NBRq.
    assert (DSb8 : bytes_at asegs m8 Bb bs).
    { eapply (xpres_bytes_at' H); [exact XP8| exact DSb1| right; right; left; exists (pbin, Bb, nB); split; [apply INR; exact R_BIN| cbn; clear - NBRq; lia]|].
      eapply ECH_AC14_kit.avoids_sub; [exact (proj1 (AV _ R_BIN))| cbn; clear; lia| cbn; clear - NBRq; lia]. }
    assert (CBb8 : rw_cells asegs m8 Bb [CB (length bs) bs; CB (Z.to_nat nB - length bs) jb1]).
    { eapply (xpres_rw_cells' H); [exact XP8| exact CBb1| right; right; left; exists (pbin, Bb, nB); split; [apply INR; exact R_BIN| cbn; clear - NBRq; lia]|].
      eapply ECH_AC14_kit.avoids_sub; [exact (proj1 (AV _ R_BIN))| cbn; clear; lia| cbn; clear - NBRq; lia]. }
    assert (CBa8 : rw_cells asegs m8 A [CB (Z.to_nat (mb_len R)) ds; CB (Z.to_nat (nA - mb_len R)) ja1]).
    { eapply (xpres_rw_cells' H); [exact XP8| exact CBa1| right; right; left; exists (p, A, nA); split; [apply INR; exact R_PA| cbn; clear - NAR; lia]|].
      eapply ECH_AC14_kit.avoids_sub; [exact (proj1 (AV _ R_PA))| cbn; clear; lia| cbn; clear - NAR; lia]. }
    pose proof (HB8 _ (INR _ R_BIN)) as (PB1 & PB2 & _ & _ & PB5 & _). cbn [blk_addr blk_size fst snd] in PB1, PB2, PB5.
    pose proof (HB8 _ (INR _ R_PA)) as (PA1 & PA2 & _ & _ & PA5 & _). cbn [blk_addr blk_size fst snd] in PA1, PA2, PA5.
    assert (ADb8 : addressable m8 Bb nB).
    { eapply (addressable_xpres_blkX H); [apply INR; exact R_BIN| unfold AAPP_HI; clear - PB5 ACB; lia| exact ADb1| exact XP8| exact (proj2 (AV _ R_BIN))]. }
    assert (ADa8 : addressable m8 A nA).
    { eapply (addressable_xpres_blkX H); [apply INR; exact R_PA| unfold AAPP_HI; clear - PA5 ACB; lia| exact ADa1| exact XP8| exact (proj2 (AV _ R_PA))]. }
    assert (MBLB : forall b, In b (blocks_MEMBIO mb R') -> In b LB).
    { intros b Hb. destruct MBO1 as (_ & _ & _ & _ & J1 & J2 & J3 & J4 & _). unfold blocks_MEMBIO in Hb. destruct Hb as [<-|[<-|[<-|[<-|[]]]]]; assumption. }
    assert (MBO8 : MEMBIO H LB m8 mb R').
    { eapply (AMEMBIO_xpres H); [exact MBO1| intros b Hb; apply INR, R_LB, MBLB; exact Hb| exact XP8|].
      apply Forall_forall. intros iv Hiv. apply Forall_forall. intros bk Hbk. exact (proj1 (Forall_forall _ _) (proj1 (AV bk (R_LB _ (MBLB _ Hbk)))) iv Hiv). }
    assert (MSH8 : MEMBIO_shad m8 mb R').
    { destruct MSH1 as (Y1 & Y2 & Y3 & Y4). pose proof MBO1 as (_ & _ & _ & _ & J1 & J2 & J3 & J4 & _).
      assert (T : forall i ax nx, In (i, ax, nx) LB -> addressable m1 ax nx -> addressable m8 ax nx).
      { intros i ax nx Hin ADx. pose proof (HB8 _ (INR _ (R_LB _ Hin))) as (_ & _ & _ & _ & Q5 & _). cbn [blk_addr blk_size fst snd] in Q5.
        eapply (addressable_xpres_blkX H); [apply INR, R_LB; exact Hin| unfold AAPP_HI; clear - Q5 ACB; lia| exact ADx| exact XP8| exact (proj2 (AV _ (R_LB _ Hin)))]. }
      split; [exact (T _ _ _ J1 Y1)|]. split; [exact (T _ _ _ J2 Y2)|]. split; [exact (T _ _ _ J3 Y3)| exact (T _ _ _ J4 Y4)]. }
    assert (BT8 : BT m8).
    { eapply (BT_frame LB' S1c); [exact BT1| exact XP8| intros b Hb; apply INR, R_TB; exact Hb| exact AS1| intros b Hb; exact (AV _ (R_TB _ Hb))| exact MI8]. }
    (* [comment removed for export] *)
    assert (RFS8 : as_RFS H (LF1c ff fp) m8).
    { eapply (ECH_AC14_kit.RFS_via_xpresX H HX s8' LB' m8); [exact RFS1| exact HP8| exact XP8| apply ECH_AC14_kit.ASK_foot_fs; [exact C0'| exact INK]]. }
    assert (LEA : AIMG_TOP <= aceil) by (unfold AIMG_TOP; clear - ACB; lia). pose proof (sh_mono _ _ LEA) as SHT2. rewrite SHT in SHT2.
    assert (STK8 : stack0 m8 lo (bv_unsigned sp)).
    { eapply (stack0_xpres H); [exact XP8| exact STK1|]. apply Forall_app. split.
      - unfold memflag_foot, A_mem_inited. constructor; [right; cbn [fst snd]; clear - SHT2; lia| constructor].
      - apply ECH_AC14_kit.ASK_foot_stack0; [exact C0'| intros b Hb; pose proof (SKF _ Hb) as (Z1 & _ & Z3); split; [exact Z1| exact Z3]]. }
    assert (CHN8 : as_chain H m8 (bv_unsigned sp) CH1c).
    { eapply (ECH_AC14_kit.chain_via_xpres_off H HH); [exact CHN1| exact XP8| exact CHBx|]. apply Forall_app. split.
      - unfold memflag_foot, A_mem_inited. constructor; [left; cbn [fst snd]; unfold AIMG_TOP in AF1; clear - AF1 AF2; lia| constructor].
      - unfold ASK_foot, SK_foot. apply Forall_app. split.
        + constructor; [left; cbn [fst snd]; pose proof (HB8 _ (INK _ ltac:(subst SK'; unfold blocks_SK; left; reflexivity))) as (_ & _ & _ & _ & B5 & _); cbn [blk_addr blk_size fst snd] in B5; exact B5|].
          destruct (Z.eqb_spec (sk_cap K') 0) as [E0|NE]; [constructor| constructor; [| constructor]].
          left. cbn [fst snd]. pose proof (HB8 _ (INK _ ltac:(subst SK'; unfold blocks_SK; rewrite (proj2 (Z.eqb_neq _ _) NE); right; left; reflexivity))) as (_ & _ & _ & _ & B5 & _). cbn [blk_addr blk_size fst snd] in B5. exact B5.
        + destruct (Z.eqb_spec (sk_cap K') 0) as [E0|NE]; [constructor| constructor; [| constructor]].
          left. cbn [fst snd]. pose proof (SKF _ ltac:(subst SK'; unfold blocks_SK; rewrite (proj2 (Z.eqb_neq _ _) NE); right; left; reflexivity)) as (AP2 & _ & N2). cbn [blk_addr blk_size fst snd] in AP2, N2.
          pose proof (sh_aapp_range _ _ AP2 N2) as (_ & T2 & _). pose proof aceil_facts as AF. unfold sh in T2 |- *. rewrite ASHADOW_BASE_val in *. clear - T2 AF ACB. Z.div_mod_to_equations. lia. }
    (* [comment removed for export] *)
    assert (NCL : forall L q, (forall b, In b L -> In b REST) -> rin_ivs (ASK_foot P K') q -> aclient_addr H L S1c q -> False).
    { intros L q SUBL0 Hq C. destruct (ECH_AC14_kit.ASK_foot_rin _ _ _ Hq) as [(b1 & H1 & R1)|[NE R1]].
      - eapply (ECH_AC14_kit.blk_not_client H HX s8' LB' m8 L S1c b1 q); [exact HP8| apply INK; exact H1| intros b Hb; apply INR, SUBL0; exact Hb| intros b Hb; apply (IDSK _ _ H1 (SUBL0 _ Hb))| exact AS1| exact R1| exact C].
      - eapply (ECH_AC14_kit.blksh_not_client H HX s8' LB' m8 L S1c (sk_did K', sk_data K', 8 * sk_cap K') q); [exact HP8| | intros b Hb; apply INR, SUBL0; exact Hb| | exact AS1| exact R1| exact C].
        + apply INK. subst SK'. unfold blocks_SK. rewrite (proj2 (Z.eqb_neq _ _) NE). right. left. reflexivity.
        + intros b Hb. apply (IDSK _ _ ltac:(subst SK'; unfold blocks_SK; rewrite (proj2 (Z.eqb_neq _ _) NE); right; left; reflexivity) (SUBL0 _ Hb)). }
    (* [comment removed for export] *)
    assert (CX2 : mid_ctx M2 = CtxReady x) by (rewrite CTX1; exact CTX).
    assert (LM8 : LIBMID (LE2 ++ LIB) m8 M2).
    { rewrite <- (M_eq1c M2 STP). eapply (LIBMID_mfX H HH s8' m8 (LE2 ++ LIB) LB' S1c (ASK_foot P K') m1 m8 M2 x);
        [exact HP8| exact LM1| exact CX2| exact XP8| intros b Hb; apply INR, R_LL; exact Hb| intros b Hb; apply INR, R_ERR; exact Hb| | | | | | exact MF8| ].
      - intros q Hq HXL. pose proof (LIBX_below q HXL) as QL. destruct (ECH_AC14_kit.ASK_foot_rin _ _ _ Hq) as [(b1 & H1 & R1)|[NE R1]].
        + pose proof (HB8 _ (INK _ H1)) as (_ & _ & _ & B4 & _). clear - QL R1 B4. lia.
        + pose proof (proj1 (SKF _ ltac:(subst SK'; unfold blocks_SK; rewrite (proj2 (Z.eqb_neq _ _) NE); right; left; reflexivity))) as AP2. cbn [blk_addr blk_size fst snd] in AP2.
          pose proof (sh_aapp_range _ _ AP2 ltac:(clear - C0'; lia)) as (T1 & _). rewrite SHT in T1. unfold AIMG_TOP in QL. clear - QL R1 T1. lia.
      - intros q Hq Rq. destruct (ECH_AC14_kit.ASK_foot_rin _ _ _ Hq) as [(b1 & H1 & R1)|[NE R1]].
        + pose proof (HB8 _ (INK _ H1)) as (_ & _ & _ & B4 & _). unfold AIMG_TOP in B4. clear - Rq R1 B4. lia.
        + pose proof (proj1 (SKF _ ltac:(subst SK'; unfold blocks_SK; rewrite (proj2 (Z.eqb_neq _ _) NE); right; left; reflexivity))) as AP2. cbn [blk_addr blk_size fst snd] in AP2.
          pose proof (sh_aapp_range _ _ AP2 ltac:(clear - C0'; lia)) as (T1 & _). rewrite SHT in T1. clear - Rq R1 T1. lia.
      - intros q Hq K0. eapply (NCL (LE2 ++ LIB) q); [exact R_LL| exact Hq| right; right; left; exact K0].
      - intros q Hq K0. eapply (NCL (LE2 ++ LIB) q); [exact R_LL| exact Hq| right; right; right; left; exact K0].
      - intros q Hq K0. eapply (NCL (mid_errblocks M2) q); [exact R_ERR| exact Hq| right; right; right; left; exact K0].
      - intros q Hq K0. eapply (NCL (mid_errblocks M2) q); [exact R_ERR| exact Hq| right; right; left; exact K0]. }
    (* [comment removed for export] *)
    assert (XP18 : xpres H LB S1c [] m1 m8).
    { eapply (xpres_drop_windows H LB LB' S1c [] (ASK_foot P K') m1 m8); [| intros b Hb; apply INR, R_LB; exact Hb| intros q Hq C; exact (NCL LB q R_LB Hq C)].
      cbn [app]. eapply (ECH_AC14_kit.axpres_drop_memflag H LB' _ [] (ASK_foot P K')); [exact MF| exact MF8| cbn [app]; exact XP8]. }
    destruct XA1 as (XSq & FXq & INq & XA1').
    assert (XA8 : xpres H LB (bv_unsigned sp) (XSq ++ XFc) m m8).
    { eapply xpres_trans; [exact XA1'|]. eapply xpres_weaken; [exact XP18| clear - Q2; lia| intros b Hb; exact Hb| intros q Hq; destruct Hq]. }
    (* [comment removed for export] *)
    set (S2 := mkSTORE P (Some (K', es ++ [E])) (es_id S')).
    assert (EBE : concat (map (fun pe => blocks_ENTRY (fst pe) (snd pe)) (combine (sk_elems K ++ [ee]) (es ++ [E]))) = EBl ++ blocks_ENTRY ee E).
    { rewrite (ECH_AC14_kit.combine_app1 _ _ _ _ (eq_sym LEN)), map_app, concat_app. cbn [map concat fst snd]. rewrite app_nil_r, EBeq. reflexivity. }
    assert (SC8 : rw_cells asegs m8 st [C8 (wz P); C8 (wz 0); C8 (wz 0)]).
    { eapply (xpres_rw_cells' H); [exact XP8| exact SC1| right; right; left; exists (es_id S, st, STORE_SIZE); split; [apply INR, R_LB; exact (proj1 (proj2 SO))| cbn; unfold STORE_SIZE; clear; lia]|].
      eapply ECH_AC14_kit.avoids_sub; [apply (proj1 (AV _ (R_LB _ (proj1 (proj2 SO)))))| cbn; clear; lia| cbn; unfold STORE_SIZE; clear; lia]. }
    assert (EBsub : forall b, In b EBl -> In b NB).
    { intros b Hb. eapply Permutation_in; [exact PNB|]. apply in_or_app. right. exact Hb. }
    assert (F2all : Forall2 (fun q Eq => ENTRYobj L7 m1 q Eq) (sk_elems K ++ [ee]) (es ++ [E])).
    { apply Forall2_app.
      - eapply (ENTRYs_rehome (NB ++ LE2 ++ LB) L7 m1 _ _ aceil); [exact F2|]. intros b Hb. rewrite <- EBeq in Hb.
        split; [subst L7; apply in_or_app; left; exact Hb| apply BEL; subst Lp; apply in_or_app; right; apply SNB; apply EBsub; exact Hb].
      - constructor; [| constructor]. eapply (ENTRYobj_frame_law H (drestc Lx NB LE2) L7 m1 m1 ee E aceil); [exact EO| | apply xpres_refl|].
        + intros b Hb. subst L7. apply in_or_app. right. apply in_or_app. left. eapply Permutation_in; [exact PE| exact Hb].
        + intros b Hb. apply BEL. subst Lp. apply in_or_app. right. apply SLX. eapply Permutation_in; [exact PE| exact Hb]. }
    assert (EB7 : forall b, In b (concat (map (fun pe => blocks_ENTRY (fst pe) (snd pe)) (combine (sk_elems K ++ [ee]) (es ++ [E])))) -> In b REST).
    { intros b Hb. rewrite EBE in Hb. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [apply R_EB; exact Hb| apply R_LX; eapply Permutation_in; [exact PE| exact Hb]]. }
    assert (F27 : Forall2 (fun q Eq => ENTRYobj (SK' ++ L7) m8 q Eq) (sk_elems K ++ [ee]) (es ++ [E])).
    { eapply ENTRYs_mono; [| intros b Hb; apply in_or_app; right; exact Hb].
      eapply (ENTRYs_frameX H L7 S1c); [exact F2all| eapply xpres_weaken; [exact XP8| clear; lia| exact (fun b Hb => INR b (R_L7 b Hb))| intros q Hq; exact Hq]|].
      intros b Hb. exact (proj1 (AV _ (EB7 _ Hb))). }
    assert (F2S8 : Forall2 (fun q Eq => ENTRY_shad m8 q Eq) (sk_elems K ++ [ee]) (es ++ [E])).
    { eapply (ENTRYs_shad_frameX H L7 LB' S1c); [| exact F2all| exact XP8| intros b Hb; split; [apply INR; exact (EB7 _ Hb)| exact (AV _ (EB7 _ Hb))]].
      apply Forall2_app; [exact F2S| constructor; [exact ESH| constructor]]. }
    assert (DTOP8 : sk_cap K' <> 0 -> sk_data K' + 8 * sk_cap K' <= AAPP_HI).
    { intros NE. pose proof (HB8 _ (INK _ ltac:(subst SK'; unfold blocks_SK; rewrite (proj2 (Z.eqb_neq _ _) NE); right; left; reflexivity))) as (_ & _ & _ & _ & Q5 & _). cbn [blk_addr blk_size fst snd] in Q5.
      unfold AAPP_HI. clear - Q5 ACB. lia. }
    assert (SO2 : STOREobj (NB' ++ LE2 ++ LB) m8 st S2).
    { subst S2. unfold STOREobj. cbn [es_entries es_entries_o es_id]. split; [exact SC8|].
      split; [apply in_or_app; right; apply in_or_app; right; rewrite SID; exact (proj1 (proj2 SO))|].
      unfold ENTRIES. split; [exact PP|]. split; [eapply ECH_AC14_kit.SKobj_relist; [exact SO8| intros b Hb; apply in_or_app; left; apply SUBN; left; exact Hb]|].
      split; [rewrite ELK, !length_app; cbn [length]; rewrite LEN; reflexivity|].
      rewrite ELK. eapply ENTRYs_mono; [exact F27|]. exact N7. }
    assert (SSH2 : STORE_shad m8 st S2).
    { subst S2. unfold STORE_shad. cbn [es_entries es_entries_o]. split; [exact STOP|].
      split; [eapply (addressable_xpres_blkX H); [apply INR, R_LB; exact (proj1 (proj2 SO))| exact STOP| exact STAD| exact XP8| exact (proj2 (AV _ (R_LB _ (proj1 (proj2 SO)))))]|].
      unfold ENTRIES_shad. split; [split; [exact SKSH8| split; [exact PTOP| exact DTOP8]]|]. rewrite ELK. exact F2S8. }
    (* [comment removed for export] *)
    assert (SKF2 : Z.of_nat (length SK') <= 2 /\ 0 <= lb_bytes SK' <= SK_SIZE + 8 * sk_cap K').
    { subst SK'. unfold blocks_SK. destruct (Z.eqb_spec (sk_cap K') 0) as [E0'|CN]; rewrite ?lb_bytes_cons; cbn [length blk_size snd lb_bytes fold_right app Z.add]; unfold SK_SIZE; [clear - E0'; lia| clear - C0' CN; lia]. }
    destruct SKF2 as [SKL' SKB'].
    pose proof (Permutation_length PE) as NBeL. pose proof (ECH_AC14_kit.lb_bytes_perm _ _ PE) as NBeB.
    (* [comment removed for export] *)
    assert (DW8 : adwkc [] NB' S2 M2 LE2 w16 w32 w40 (wz (cur + 4 + elen)) (wz ee) v192 v200 v208 v224 v232 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tpl (um + SKPUSH_COST K) (uf + 8 * sk_cap K) m8 s8').
    { unfold adwk, adwkG. repeat match goal with |- _ /\ _ => split end.
      all: try assumption.
      all: try (intros K0 es0 EQ0; subst S2; cbn [es_entries_o] in EQ0; injection EQ0 as <- <-; split; [rewrite CMK; exact KC| rewrite ELK, length_app, Nat2Z.inj_add, <- LEN; cbn [length Z.of_nat Pos.of_succ_nat]; clear - CAP'; lia]).
      all: lazymatch goal with
           | |- as_RHEAP _ _ _ _ => exact HP9
           | |- es_id _ = es_id S => subst S2; cbn [es_id]; exact SID
           | |- Permutation (blocks_STORE st _) _ => subst S2; unfold blocks_STORE; cbn [es_entries es_entries_o es_id]; rewrite ELK, EBE, SID; apply perm_skip; subst NB' SK'; apply Permutation_app_head; apply Permutation_app_head; exact PE
           | |- List.NoDup (map blk_id (blocks_STORE st _)) =>
               pose proof (ah_nodup H HH _ _ _ HP9) as ND9; unfold drest in ND9; cbn [app] in ND9; rewrite map_app in ND9; apply List.NoDup_app_remove_l in ND9;
               eapply Permutation_NoDup;
                 [ apply Permutation_map; subst S2; unfold blocks_STORE; cbn [es_entries es_entries_o es_id]; rewrite ELK, EBE, SID;
                   apply (@perm_skip block (es_id S, st, STORE_SIZE) NB'); subst NB' SK'; apply Permutation_app_head; apply Permutation_app_head; apply Permutation_sym; exact PE
                 | ];
               cbn [map]; constructor;
                 [ intros KIN'; apply in_map_iff in KIN'; destruct KIN' as (b1 & E1 & H1);
                   exact (nodup_ids_app_ne _ _ _ _ ND9 H1 ltac:(apply in_or_app; right; right; right; apply in_or_app; right; exact (proj1 (proj2 SO))) E1)
                 | rewrite map_app in ND9; exact (List.NoDup_app_remove_r _ _ ND9) ]
           | |- exists junk, rw_cells asegs _ Bb _ => exists jb1; exact CBb8
           | |- exists junk, rw_cells asegs _ A _ => exists ja1; exact CBa8
           | |- exists errv', rw_cells asegs _ (errno_addr _) _ => exists errv8; exact ERR8
           | |- exists lb, rw_cells asegs _ ff _ => exists lb1; exact FF8
           | |- exists XSq0, _ => exists XSq; split; [exact FXq| split; [exact INq| exact XA8]]
           | |- ?G => idtac "DW8LEFT" G
           end. }
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL8| exact VIS8| eapply ade_seg20 with (q := S1c) (prv := sk_num K + 1);
       [exact FR1'| exact FR2'| ..| exact MI8]|].
    all: lazymatch goal with
           | |- 0 <= sk_num _ + 1 < _ => unfold sk_num, zlength; rewrite <- LEN; clear - N64; lia
           | |- 0 <= AR_INTERNAL_ERROR < _ => unfold AR_INTERNAL_ERROR; clear; lia
           | |- 0 <= SH + 8 < _ => rewrite SHF; unfold sh; rewrite ASHADOW_BASE_val; clear - FQ1 FQ2 ACB; Z.div_mod_to_equations; lia
           | |- 0 <= S1c => clear - AS1 ACB; lia
           | |- S1c + 312 < _ => clear - Q2 SPR; lia
           | |- 0 <= A < _ => clear - PA1 PA5 ACB NAR; lia
           | |- 0 <= bt < _ => clear - BTR; lia
           | |- 0 <= Bb < _ => clear - PB1 PB5 ACB NBRq; lia
           | |- 0 <= ff < _ => clear - FQ1 FQ2 ACB; lia
           | |- 0 <= _ < _ => clear - EEP EEH ACB; lia
           | |- 0 <= _ => clear - CUR1 BP; lia
           | |- _ + 4 < _ => clear - CUR2 ER EL19 NBR PB5 ACB; lia
           | |- forall _, _ => idtac
           | |- ?G => idtac "SEG20LEFT" G
           end.
    intros msF9 mo9 KREL9 MP9 PO9. cbn beta in PO9. destruct PO9 as [[P0 _]|[_ VIS9]]; [exfalso; unfold sk_num, zlength in P0; clear - P0; lia|].
    (* [comment removed for export] *)
    eapply (KADV NB' (blocks_ENTRY ee E) S2 M2 LE2 w16 w32 w40 (wz (cur + 4 + elen)) (wz ee) v192 v200 v208 v224 v232 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tpl (um + SKPUSH_COST K) (uf + 8 * sk_cap K) elen m8 s8' msF9 mo9);
      [exact DW8| exact EL19| exact ER| exact UM1| exact UF1| | exact ECNT| exact EBYT| exact VIS9| exact KREL9
      | eapply (ah_mpres_trans H HH); [exact MP1|]; eapply (ah_mpres_trans H HH); [exact MP2|]; eapply (ah_mpres_trans H HH); [exact MP8| exact MP9]].
    rewrite <- EBS0, <- NEN0. subst S2. unfold EBS, nent, SKB. cbn [es_entries_o es_entries]. rewrite ESO, ELK, EBE.
    rewrite length_app, Nat2Z.inj_add. cbn [length Z.of_nat Pos.of_succ_nat].
    rewrite <- ?EBeq. split; [reflexivity|]. split; [clear; lia|]. split; [exact SKL'|]. subst SK'. clear - SKB' CAP' C0'. unfold SK_SIZE in *. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma de_push : forall cur rem NB S' um0 uf0 ph0, KPUSHc cur rem NB S' um0 uf0 ph0.
  Proof using VIS0 A0 A1 SO SE SEO STL SSH MBO MP0 MN0 MBB MBS MSH PAY DS DSL PAYL PAYL2 NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC AUX SPB BHI SPA ST CEIL LO ST0 ERR MI TP AC MCO RFS LFB ATH CHN CHB PF ALW RAE HH HX RAISE SM6 SF6 SSF8 PERM NAR NBR MST POS BTR BT_frame FRESH AUXV.
    intros cur rem NB S' um0 uf0 ph0. unfold dK_push.
    intros Lx M2 LE2 w16 w32 w40 v192 v200 v208 v224 v232 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tpl um uf elen m1 s1' msF1 mo1 ee frv E
           rax u0 u1 u2 a1w a2w a3w a4w a5w a6w a7w s2w s4w s5w s6w s8w s9w s11w u3 u4 u5 u6
           DW EO ESH PE ECNT EBYT EL19 ER CUR1 CUR2 N65 FRV STP' EPH1 EPH2 DB UM1 UF1 UM2 UF2 KADV KTX VIS1 KREL1 MP1.
    pose proof DW as DWG. unfold adwk in DWG.
    pose proof DWG as (HP1 & LM1 & STP & NEW & CTX1 & EC & EB & LC & LBY & SO1 & SSH1 & SID & SPM & SND & SKI & MBO1 & MSH1 & DSm1 & DSb1 & [jb1 CBb1] & ADb1 & [ja1 CBa1] & ADa1 & BT1
                       & FR0 & FR1 & SZ1 & FR2 & FR3 & SZ3 & FRG & FRS & FF1 & FSH1 & LSH1 & RFS1 & [errv1 ERR1] & AUX1 & MI1 & AC1 & ST1 & STK1 & CHN1 & XA1 & LED1).
    destruct (ade_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ DWG) as (AS1 & Q2 & Q1 & SPR & BP & BH & IB2 & NBL & NB15 & BLX & BEL & BRS & F1 & MF & IM & GM & ACCB & APB & ACB & LOS & LO0).
    destruct rc_facts_c as (SEQ & SIN & SBR & BLK0 & SUB0 & ND0 & STK0 & LO0' & MF0 & OBJ0 & DJA & AFSB & ACB' & Q1' & Q2' & SPR'). change (rp_s1 (bv_unsigned sp)) with S1c in Q1', Q2'.
    pose proof AFSB as (AF1 & AF2 & AF3 & AF4). unfold AIMG_TOP in AF1. unfold AFS_SIZE in AF2.
    pose proof (fresh_frame_facts H _ _ _ _ FRESH) as (_ & FQ1 & FQ2 & FQ64 & FQ8 & FP1 & FP2 & FP3 & FP4 & FQ5 & FQ6 & FB1 & FB2 & FB3).
    change (fsz 6) with 4096 in FQ2, FQ6. unfold AFS_HDR, AFS_FLAGS, AFS_SIZE, AIMG_TOP in FQ1, FQ2, FP1, FP2, FP3, FP4, FQ5, FQ6, FB1, FB2.
    destruct (adwkG_hfc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ DWG) as (_ & ND & DISJ & D2 & D1).
    pose proof (drest_subc Lx NB LE2) as (SLB & SL0 & SLE & SNB & STB & IB & IA & SLX & S3 & SLL).
    pose proof (dec_stack M M2 STP) as (_ & _ & _ & STKP & _ & _ & _ & _ & _ & _ & STKN & _).
    assert (CHBx : forall fp' ra', In (fp', ra') CH1c -> S1c + 16 <= fp').
    { intros fp' ra' [Ex|Hin]; [injection Ex as <- <-; clear - Q2; lia| pose proof (CHB _ _ Hin) as CB'; clear - CB' Q2; lia]. }
    set (Lp := mid_errblocks M2 ++ drestc Lx NB LE2) in *.
    (* [comment removed for export] *)
    pose proof SO1 as (SC1 & SIN1 & EN1). pose proof SSH1 as (STOP & STAD & ENS).
    pose proof SBR as (SB1 & SB2 & SB3 & SB4 & SB5 & SB6 & SB7). unfold STORE_SIZE in SB5, SB6. unfold AIMG_TOP in SB4.
    assert (STIN : In (es_id S, st, STORE_SIZE) Lp) by (subst Lp; apply in_or_app; right; apply SLB; exact (proj1 (proj2 SO))).
    assert (ACCS : accessible m1 st STORE_SIZE).
    { eapply (addressable_accessible _ _ _ _ _ STAD); [apply Z.le_refl| apply Z.le_refl| unfold AAPP_HI, STORE_SIZE; clear - SB5 ACB; lia]. }
    assert (HR : 0 <= es_entries S' < 2^64).
    { unfold ENTRIES in EN1. destruct (es_entries_o S') as [[K es]|]; [| rewrite EN1; clear; lia]. destruct EN1 as (PP & SKO & _). pose proof SKO as (_ & _ & KIN & _).
      pose proof (BEL _ ltac:(subst Lp; apply in_or_app; right; apply SL0; apply S3; exact KIN)) as KB. cbn [blk_addr blk_size fst snd] in KB. unfold SK_SIZE in KB. clear - PP KB ACB; lia. }
    (* [comment removed for export] *)
    assert (EIN' : In (en_id E, ee, ENTRY_SIZE) Lp) by (subst Lp; apply in_or_app; right; apply SLX; eapply Permutation_in; [exact PE| left; reflexivity]).
    pose proof (BRS _ EIN') as (EEP & _ & _ & _ & EEH' & _). cbn [blk_addr blk_size fst snd] in EEP, EEH'. unfold ENTRY_SIZE in EEH'.
    pose proof (BRS _ (in_or_app _ _ _ (or_intror IB))) as (PB1 & _ & _ & _ & PB5 & _). cbn [blk_addr blk_size fst snd] in PB1, PB5.
    pose proof (BRS _ (in_or_app _ _ _ (or_intror IA))) as (PA1 & _ & _ & _ & PA5 & _). cbn [blk_addr blk_size fst snd] in PA1, PA5.
    pose proof NBR as NBRq. unfold zlength in NBRq.
    assert (LX0 : 0 <= lb_bytes Lx).
    { apply lb_bytes_nonneg_s. apply Forall_forall. intros b Hb. pose proof (BRS _ ltac:(subst Lp; apply in_or_app; right; apply SLX; exact Hb)) as (_ & _ & E3 & _). exact E3. }
    (* [comment removed for export] *)
    assert (SKBC : Z.of_nat (length (SKB st S')) <= 2 /\ lb_bytes (SKB st S') <= 88 + 16 * nent S').
    { unfold SKB, nent. pose proof SKI as SKI'. destruct (es_entries_o S') as [[K es]|]; [| cbn; clear; lia].
      destruct (SKI' K es eq_refl) as [_ KCAP]. unfold ENTRIES in EN1. destruct EN1 as (_ & SKO & LEN & _). pose proof SKO as (_ & _ & _ & KNC & _).
      pose proof (ECH_AC14_kit.blocks_SK_facts (es_entries S') K ltac:(clear - KNC; lia)) as (SKB1 & SKL1 & _). rewrite <- LEN in KCAP. unfold SK_SIZE in SKB1. clear - SKB1 SKL1 KCAP. lia. }
    destruct DB as [DB1 DB2].
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL1| exact VIS1| eapply ade_seg14 with (q := S1c) (es := st) (h := es_entries S') (z1 := 0) (z2 := 0);
      [exact FR1| exact FR2| exact SC1| exact SB1| unfold STORE_SIZE; exact SB5| exact ACCS| clear - FRV; lia| exact HR| exact AS1| clear - Q2 SPR; lia| exact MI1]|].
    intros msF2 mo2 KREL2 MP2 PO. cbn beta in PO.
    destruct PO as [[F0 VIS2]|[[_ [HNZ VIS2]]|[_ [HZ VIS2]]]].
    { (* [comment removed for export] *)
      eapply (KTX Lx NB S' M2 LE2 w16 w32 w40 (wz (cur + 4 + elen)) v192 v200 v208 v224 v232 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tpl um uf m1 s1' msF2 mo2 ee E);
        [exact DW| | exact EO| exact ESH| exact PE| | | | exact VIS2| exact KREL2| eapply (ah_mpres_trans H HH); [exact MP1| exact MP2]].
      - split; [reflexivity|]. split; [reflexivity|]. exact SKBC.
      - split; [unfold PUSH_HB, ERRDEBUG_BYTES in *; clear - DB1; lia| unfold PUSH_HC in *; clear - DB2; lia].
      - unfold PUSH_CM, ERRDEBUG_BYTES in *. clear - UM2. lia.
      - unfold PUSH_CF, ERRDEBUG_BYTES in *. clear - UF2. lia. }
    { (* [comment removed for export] *)
      unfold ENTRIES in EN1. destruct (es_entries_o S') as [[K es]|] eqn:ESO; [| exfalso; exact (HNZ EN1)].
      destruct EN1 as (PP & SKO & LEN & F2). destruct (SKI K es eq_refl) as [KC KCAP]. pose proof SKO as (_ & _ & _ & KNC & _).
      unfold sk_num, zlength in KNC. rewrite <- LEN in KNC, KCAP. pose proof N65 as N65'. unfold nent in N65'. rewrite ESO in N65'.
      pose proof (sk_grow_le (sk_cap K) ltac:(clear - KNC; lia)) as [GR GR5].
      assert (PCB : SKPUSH_COST K <= 1744 /\ 8 * sk_cap K <= 1072).
      { unfold SKPUSH_COST, sk_grow in *. clear - KCAP N65' KNC. Z.div_mod_to_equations. lia. }
      eapply (de_pushcall cur rem S' um0 uf0 ph0 Lx NB S' M2 LE2 w16 w32 w40 v192 v200 v208 v224 v232 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tpl um uf elen PUSH_HB PUSH_HC m1 s1' msF2 mo2 ee E K es);
        [exact DW| exact ESO| reflexivity| reflexivity| exact EO| exact ESH| exact PE| exact EEP| exact ECNT| exact EBYT| exact EL19| exact ER| exact CUR1| exact CUR2| exact N65
        | split; [exact DB1| exact DB2]| unfold PUSH_HB; clear - PCB; lia| unfold PUSH_HC; clear; lia
        | unfold PUSH_CM in UM1; clear - UM1 PCB; lia| unfold PUSH_CF in UF1; clear - UF1 PCB KNC; lia
        | unfold PUSH_CM in UM2; pose proof (errph_nonneg (mid_err M2)) as [EP0 _]; clear - UM2 PCB EP0; lia
        | unfold PUSH_CF in UF2; pose proof (errph_nonneg (mid_err M2)) as [EP0 _]; clear - UF2 PCB KNC EP0 LX0; lia
        | exact KADV| exact VIS2| exact KREL2| eapply (ah_mpres_trans H HH); [exact MP1| exact MP2]]. }
    (* [comment removed for export] *)
    unfold ENTRIES in EN1. destruct (es_entries_o S') as [[K es]|] eqn:ESO; [destruct EN1 as (PP & _); exfalso; clear - PP HZ; lia|].
    assert (NB0 : NB = []).
    { unfold blocks_STORE in SPM. rewrite ESO in SPM. apply Permutation_length in SPM. cbn in SPM. destruct NB; [reflexivity| cbn in SPM; exfalso; clear - SPM; lia]. }
    subst NB.
    pose proof (errph_nonneg (mid_err M2)) as [EP0 EC0].
    (* [comment removed for export] *)
    assert (HAL0 : as_Cm H SK_SIZE <= as_AL H s1').
    { pose proof ((RCI LEDGER_pay) s1' um uf SK_SIZE 0 LED1 ltac:(unfold SK_SIZE; clear; lia) ltac:(clear; lia)
                    ltac:(unfold PUSH_CM, SK_SIZE in *; clear - UM2 EP0; lia) ltac:(unfold PUSH_CF in *; clear - UF2 EP0 LX0; lia)) as K0.
      pose proof (ECH_AC14_kit.aCf_pos H HH 0 ltac:(clear; lia)) as K1. clear - K0 K1. lia. }
    pose proof (asknew_null_spec H HH) as NS. unfold sknew_null_stmt, sknew_stmt_gen in NS.
    eapply (ah_seq H HH).
    { eapply NS with (c := 0) (lo := lo) (B := B) (LB := Lp) (s := s1') (v := 1) (errv := errv1) (CH := CH1c); clear NS;
        [exact VIS2| reflexivity| ..]; rewrite ?unsigned_lit by (first [unfold ADE_R11; clear; lia| clear - AS1 ACB Q2 SPR; lia]).
      all: try first [exact HP1| exact KREL2| exact AUX1| exact ST1| exact CEIL| exact MI1| exact AC1| exact CHN1| exact HAL0| exact CHBx].
      all: lazymatch goal with
           | |- lb_bytes _ + _ <= _ => subst Lp; rewrite lb_bytes_app; unfold PUSH_HB, SK_SIZE in *; clear - DB1 EB EP0; lia
           | |- Z.of_nat (length _) + _ <= _ => subst Lp; rewrite length_app, Nat2Z.inj_add; unfold PUSH_HC in *; clear - DB2 EC EC0; lia
           | |- _ <= B => clear - SPB Q2; lia
           | |- _ mod 16 = 0 => clear - Q1; Z.div_mod_to_equations; lia
           | |- lo <= _ - _ => unfold SKNEW_STACK, FR_sk_new, FR_sk_new_null in *; clear - LO STKN Q2; lia
           | |- rw_cells _ _ (errno_addr _) _ => exact ERR1
           | |- @eq _ _ (Z_to_bv 64 ATP) => reflexivity
           | |- C1env _ _ => split; [exact MF| split; [exact IM| exact GM]]
           | |- pf_ok _ _ _ _ => apply pf_sitec; intros e He; unfold PF_readcfg, PF_read_priv; do 16 (apply in_or_app; right); apply in_or_app; left;
                                unfold PF_entry; do 8 (apply in_or_app; right); apply in_or_app; left; exact He
           | |- ?G => idtac "NEWPRE" G
           end. }
    clear NS. intros [msF3 mo3] PO. unfold sknew_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (z0 & z1 & z2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & z3 & z4 & z5 & z6 & m3 & errv3 & Ask & kid & did & s3' &
                    VIS3 & KREL3 & MP3 & MI3 & AC3 & ST3 & ERR3 & AUX3 & XP3 & APOS & HP3 & SKO3 & SKSH3 & (MF3 & IM3 & GM3) & AL3).
    rewrite (unsigned_lit S1c) in ST3, XP3 by (clear - AS1 ACB Q2 SPR; lia).
    set (BK := (kid, Ask, SK_SIZE)) in *.
    assert (XP3' : xpres H Lp S1c [] m1 m3).
    { rewrite <- (app_nil_r memflag_foot) in XP3. eapply (ECH_AC14_kit.axpres_drop_memflag H Lp S1c [] [] m1 m3); [exact MF| exact MF3| cbn [app]; exact XP3]. }
    assert (HP3' : as_RHEAP H s3' (mid_errblocks M2 ++ drestc (BK :: Lx) [] LE2) m3) by (eapply PERM; [exact HP3|]; subst Lp; unfold drest; apply Permutation_middle).
    assert (LED3 : LEDGERc s3' (um + SK_SIZE) uf).
    { pose proof ((RCI LEDGER_step) s1' s3' um uf SK_SIZE 0 LED1 ltac:(unfold SK_SIZE; clear; lia) ltac:(clear; lia) ltac:(rewrite (ECH_AC14_kit.aCf0 H HH); clear - AL3; lia)) as K0.
      rewrite Z.add_0_r in K0. exact K0. }
    pose proof (adwkG_xc Lx (BK :: Lx) [] S' M2 LE2 _ _ _ _ _ _ _ _ _ _ _ _ um uf (um + SK_SIZE) uf m1 s1' m3 s3' errv3 DWG
                  ltac:(eapply xpres_weaken; [exact XP3'| clear; lia| intros b Hb; subst Lp; apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; exact Hb| right; apply SL0; exact Hb]| intros q Hq; exact Hq])
                  HP3' MI3 AC3 ST3 AUX3 ERR3 LED3) as DW3.
    assert (EO3 : ENTRYobj (drestc (BK :: Lx) [] LE2) m3 ee E).
    { eapply ENTRYobj_LB_mono; [| intros b Hb; unfold drest; cbn [app]; right; exact Hb].
      eapply (ENTRYobj_frameX H _ S1c []); [exact EO| eapply xpres_weaken; [exact XP3'| clear; lia| intros b Hb; subst Lp; apply in_or_app; right; exact Hb| intros q Hq; exact Hq]| intros b Hb; apply Forall_nil]. }
    assert (ESH3 : ENTRY_shad m3 ee E).
    { eapply (ENTRY_shad_frameX H (drestc Lx [] LE2) Lp S1c []); [exact ESH| exact EO| exact XP3'|].
      intros b Hb. split; [subst Lp; apply in_or_app; right; apply SLX; eapply Permutation_in; [exact PE| exact Hb]|]. split; apply Forall_nil. }
    assert (KIN : In BK (BK :: Lx)) by (left; reflexivity).
    assert (KB : Ask + SK_SIZE <= aceil).
    { pose proof (ah_blocks H HH _ _ _ _ HP3 (or_introl eq_refl)) as (_ & _ & _ & _ & K5 & _). exact K5. }
    unfold SK_SIZE in KB.
    clear XP3 HP3 VIS1 VIS2 KREL1 KREL2.
    (* [comment removed for export] *)
    assert (SZ1c : cells_size (dsg1c w16 w32 w40 (wz (cur + 4 + elen))) = 128%nat) by reflexivity.
    assert (SZ3c : cells_size (arp_sg3 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) = 104%nat) by reflexivity.
    assert (LSHc : length (poison_bytes 256 248) = 256%nat) by reflexivity.
    eapply (ahh_evt_then H HH); [exact KREL3| exact VIS3| eapply ade_seg15; [clear - APOS KB ACB; lia| clear - AS1 ACB; lia| clear - Q2 SPR; lia| exact MI3]|].
    intros msF4 mo4 KREL4 MP4 VIS4. cbn beta in VIS4.
    eapply (de_setter P_OPENSSL_sk_set_cmp_thunks O_SK_CMPTH (BK :: Lx) [] S' M2 LE2 _ _ _ _ _ _ _ _ _ _ _ _ (um + SK_SIZE) uf m3 s3' msF4 mo4 Ask ATH_CMP ADE_R12 (sk_fresh 0 kid did));
      [exact (askset_cmp_thunks_spec H)| exact DW3| exact SZ1c| exact SZ3c| exact LSHc| exact KIN| eapply ECH_AC14_kit.SKobj_relist; [exact SKO3| intros b Hb; unfold blocks_SK in Hb; cbn in Hb; destruct Hb as [<-|[]]; apply in_or_app; right; unfold drest; left; reflexivity]
      | exact SKSH3| reflexivity| unfold ATH_CMP; clear; lia| unfold ADE_R12; clear; lia| reflexivity| exact VIS4| exact KREL4|].
    clear DW3 SKO3 SKSH3 VIS3 VIS4 KREL3 KREL4. intros m5 msF5 mo5 v0 v1 v2 d1 d2 d3 d4 d5 d6 d7 v3 v4 v5 v6 DW5 SKO5 SKSH5 XP35 VIS5 KREL5 MP5.
    pose proof DW5 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MI5 & _).
    eapply (ahh_evt_then H HH); [exact KREL5| exact VIS5| eapply ade_seg16; [clear - APOS KB ACB; lia| clear - AS1 ACB; lia| clear - Q2 SPR; lia| exact MI5]|].
    intros msF6 mo6 KREL6 MP6 VIS6. cbn beta in VIS6.
    eapply (de_setter P_OPENSSL_sk_set_copy_thunks O_SK_COPYTH (BK :: Lx) [] S' M2 LE2 _ _ _ _ _ _ _ _ _ _ _ _ (um + SK_SIZE) uf m5 s3' msF6 mo6 Ask ATH_COPY ADE_R13 (sk_with_thunk (sk_fresh 0 kid did) O_SK_CMPTH ATH_CMP));
      [exact (askset_copy_thunks_spec H)| exact DW5| exact SZ1c| exact SZ3c| exact LSHc| exact KIN| exact SKO5| exact SKSH5| reflexivity| unfold ATH_COPY; clear; lia| unfold ADE_R13; clear; lia| reflexivity| exact VIS6| exact KREL6|].
    clear DW5 SKO5 SKSH5 VIS5 VIS6 KREL5 KREL6 MI5. intros m7 msF7 mo7 v0' v1' v2' e1 e2 e3 e4 e5' e6 e7 v3' v4' v5' v6' DW7 SKO7 SKSH7 XP57 VIS7 KREL7 MP7.
    pose proof DW7 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MI7 & _).
    eapply (ahh_evt_then H HH); [exact KREL7| exact VIS7| eapply ade_seg17; [clear - APOS KB ACB; lia| clear - AS1 ACB; lia| clear - Q2 SPR; lia| exact MI7]|].
    intros msF8 mo8 KREL8 MP8 VIS8. cbn beta in VIS8.
    eapply (de_setter P_OPENSSL_sk_set_thunks O_SK_FREETH (BK :: Lx) [] S' M2 LE2 _ _ _ _ _ _ _ _ _ _ _ _ (um + SK_SIZE) uf m7 s3' msF8 mo8 Ask ATH_FREE ADE_R14 (sk_with_thunk (sk_with_thunk (sk_fresh 0 kid did) O_SK_CMPTH ATH_CMP) O_SK_COPYTH ATH_COPY));
      [exact (askset_thunks_spec H)| exact DW7| exact SZ1c| exact SZ3c| exact LSHc| exact KIN| exact SKO7| exact SKSH7| reflexivity| unfold ATH_FREE; clear; lia| unfold ADE_R14; clear; lia| reflexivity| exact VIS8| exact KREL8|].
    clear DW7 SKO7 SKSH7 VIS7 VIS8 KREL7 KREL8 MI7. intros m9 msF9 mo9 v0'' v1'' v2'' g1 g2 g3 g4 g5 g6 g7 v3'' v4'' v5'' v6'' DW9 SKO9 SKSH9 XP79 VIS9 KREL9 MP9.
    set (Kth := sk_with_thunk (sk_with_thunk (sk_with_thunk (sk_fresh 0 kid did) O_SK_CMPTH ATH_CMP) O_SK_COPYTH ATH_COPY) O_SK_FREETH ATH_FREE) in *.
    (* [comment removed for export] *)
    assert (XP39 : xpres H (mid_errblocks M2 ++ drestc (BK :: Lx) [] LE2) S1c [(Ask, Ask + SK_SIZE)] m3 m9).
    { eapply xpres_trans; [exact XP35|]. eapply xpres_trans; [exact XP57| exact XP79]. }
    pose proof DW9 as (HP9 & LM9 & _ & _ & _ & _ & _ & _ & _ & SO9 & SSH9 & _ & SPM9 & SND9 & _ & MBO9 & MSH9 & DSm9 & DSb9 & [jb9 CBb9] & ADb9 & [ja9 CBa9] & ADa9 & BT9
                      & FR09 & FR19 & _ & FR29 & FR39 & _ & FRG9 & FRS9 & [lb9 FF9] & FSH9 & _ & RFS9 & [errv9 ERR9] & AUX9 & MI9 & AC9 & ST9 & STK9 & CHN9 & XA9 & LED9).
    destruct (adwkG_hfc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ DW9) as (BRS9 & ND9 & DISJ9 & D29 & D19).
    set (L9 := mid_errblocks M2 ++ drestc (BK :: Lx) [] LE2) in *.
    pose proof (drest_subc (BK :: Lx) [] LE2) as (SLB9 & SL09 & SLE9 & SNB9 & STB9 & IB9 & IA9 & SLX9 & S39 & SLL9).
    assert (STIN9 : In (es_id S, st, STORE_SIZE) L9) by (subst L9; apply in_or_app; right; apply SLB9; exact (proj1 (proj2 SO))).
    assert (BKIN9 : In BK L9) by (subst L9; apply in_or_app; right; apply SLX9; left; reflexivity).
    assert (BKAP : aapp Ask SK_SIZE) by (pose proof (BRS9 _ BKIN9) as (_ & _ & _ & _ & _ & _ & K7); exact K7).
    pose proof (aapp_not_shadowland _ _ BKAP) as BKNS. unfold SK_SIZE in BKNS. pose proof (aapp_not_shadowland _ _ SB7) as STNS. unfold STORE_SIZE in STNS.
    assert (SHT : sh AIMG_TOP = 0x80178800) by reflexivity.
    assert (SHC : sh aceil < AHI_LO) by (pose proof (sh_aapp_range _ _ AF4 ltac:(unfold AFS_SIZE; clear; lia)) as (_ & _ & W3); exact W3).
    (* [comment removed for export] *)
    assert (SHAV : forall a0' n0' b, aapp a0' n0' -> 0 <= n0' -> In b L9 -> shavoids [(a0', a0' + n0')] (blk_addr b) (blk_size b)).
    { intros a0' n0' b AP N0 Hb. pose proof (BRS9 _ Hb) as (_ & _ & B3 & _ & _ & _ & B7). pose proof (sh_aapp_range _ _ B7 B3) as (T1 & T2 & T3). rewrite SHT in T1.
      pose proof (aapp_not_shadowland _ _ AP) as NS. unfold ECH_AC14_kit.shavoids. constructor; [| constructor]. cbn [fst snd].
      unfold ALOWSH_LO, AHI_LO in *. clear - T1 T2 T3 NS SHC N0. lia. }
    (* [comment removed for export] *)
    assert (NEX : forall b, In b (blocks_ENTRY ee E) -> blk_id b <> blk_id BK).
    { intros b Hb EQ. pose proof (ah_nodup H HH _ _ _ HP3') as ND3. unfold drest in ND3. rewrite map_app in ND3. apply List.NoDup_app_remove_l in ND3.
      cbn [map app] in ND3. inversion ND3 as [|xq lq NI ND4]; subst. apply NI. rewrite <- EQ. apply in_map.
      apply in_or_app. left. eapply Permutation_in; [exact PE| exact Hb]. }
    assert (AVX : forall b, In b (blocks_ENTRY ee E) -> avoids [(Ask, Ask + SK_SIZE)] (blk_addr b) (blk_size b)).
    { intros b Hb. pose proof (DISJ9 b BK ltac:(subst L9; apply in_or_app; right; apply SLX9; right; eapply Permutation_in; [exact PE| exact Hb]) BKIN9 (NEX b Hb)) as D0.
      cbv delta [BK] in D0. cbn [blk_addr blk_size blk_id fst snd] in D0. unfold ECH_AC14_kit.avoids. constructor; [| constructor]. cbn [fst snd]. unfold SK_SIZE in *. clear - D0. lia. }
    assert (EO9 : ENTRYobj (drestc (BK :: Lx) [] LE2) m9 ee E).
    { eapply (ENTRYobj_frameX H _ S1c [(Ask, Ask + SK_SIZE)]); [exact EO3| eapply xpres_weaken; [exact XP39| clear; lia| intros b Hb; subst L9; apply in_or_app; right; exact Hb| intros q Hq; exact Hq]| exact AVX]. }
    assert (ESH9 : ENTRY_shad m9 ee E).
    { eapply (ENTRY_shad_frameX H (drestc (BK :: Lx) [] LE2) L9 S1c [(Ask, Ask + SK_SIZE)]); [exact ESH3| exact EO3| exact XP39|].
      intros b Hb. assert (HbL : In b L9) by (subst L9; apply in_or_app; right; apply SLX9; right; eapply Permutation_in; [exact PE| exact Hb]).
      split; [exact HbL|]. split; [exact (AVX b Hb)| apply SHAV; [exact BKAP| unfold SK_SIZE; clear; lia| exact HbL]]. }
    (* [comment removed for export] *)
    pose proof SO9 as (SC9 & SIN9 & _). rewrite HZ in SC9. pose proof SSH9 as (STOP9 & STAD9 & _).
    assert (ACCS9 : accessible m9 st STORE_SIZE).
    { eapply (addressable_accessible _ _ _ _ _ STAD9); [apply Z.le_refl| apply Z.le_refl| unfold AAPP_HI, STORE_SIZE; clear - SB5 ACB; lia]. }
    eapply (ahh_evt_then H HH); [exact KREL9| exact VIS9| eapply ade_seg18 with (q := S1c) (sk := Ask) (es := st) (z1 := 0) (z2 := 0) (h := 0);
      [exact FR19| exact FR29| exact SC9| exact SB1| unfold STORE_SIZE; exact SB5| exact ACCS9| clear - APOS KB ACB; lia| exact AS1| clear - Q2 SPR; lia| exact MI9]|].
    intros msF10 mo10 KREL10 MP10 PO. cbn beta in PO.
    destruct PO as (m10 & MU & WM & MI10 & SC10 & [[A00 _]|[_ VIS10]]); [exfalso; clear - A00 APOS; lia|].
    (* [comment removed for export] *)
    assert (XP910 : xpres H L9 S1c [(st, st + 8)] m9 m10).
    { eapply (xpres_of_munch H); [exact HH| exact HP9| exact MU| exact WM|]. apply Forall_cons; [right; cbn [fst snd]; intros q Hq; cbn [rin_ivs fst snd]; left; exact Hq| apply Forall_nil]. }
    assert (AV9 : forall b, In b L9 -> blk_id b <> es_id S -> disjoint_from [(st, st + 8)] (blk_addr b) (blk_size b) /\ avoids [(st, st + 8)] (blk_addr b) (blk_size b)).
    { intros b Hb NE. pose proof (DISJ9 b (es_id S, st, STORE_SIZE) Hb STIN9 NE) as D0. cbn [blk_addr blk_size fst snd] in D0. unfold STORE_SIZE in D0.
      split; [cbn; split; [clear - D0; lia| exact I]| unfold ECH_AC14_kit.avoids; constructor; [cbn [fst snd]; clear - D0; lia| constructor]]. }
    assert (NEL : forall b, In b (LE2 ++ LIB) -> blk_id b <> es_id S).
    { intros b Hb. apply in_app_or in Hb. destruct Hb as [Hb|Hb].
      - destruct (drest_idsc _ _ _ _ ND9) as (_ & _ & _ & _ & _ & _ & DLE). exact (DLE _ _ Hb (proj1 (proj2 SO))).
      - exact (DJ6 _ _ Hb (or_introl eq_refl)). }
    assert (DJF : forall q n', S1c <= q -> disjoint_from [(st, st + 8)] q n').
    { intros q n' Hq. cbn. clear - Hq SB5 AS1. split; [lia| exact I]. }
    assert (NSHst : Forall (fun iv : Z * Z => snd iv <= ASHADOW_BASE \/ AHI_LO <= fst iv) [(st, st + 8)]).
    { apply Forall_cons; [cbn; rewrite ASHADOW_BASE_val; unfold ALOWSH_LO in STNS; clear - STNS; lia| apply Forall_nil]. }
    assert (CWst : Forall (aclient_write_ok H L9) [(st, st + 8)]).
    { apply Forall_cons; [| apply Forall_nil]. right; right; left. exists (es_id S, st, STORE_SIZE). split; [exact STIN9| cbn; unfold STORE_SIZE; clear; lia]. }
    set (S1' := mkSTORE Ask (Some (Kth, [])) (es_id S')).
    assert (BKE : blocks_SK Ask Kth = [BK]) by (subst Kth BK; unfold blocks_SK; reflexivity).
    assert (MBLB : forall b, In b (blocks_MEMBIO mb R') -> In b LB /\ blk_id b <> es_id S).
    { intros b Hb. split; [destruct MBO9 as (_ & _ & _ & _ & J1 & J2 & J3 & J4 & _); unfold blocks_MEMBIO in Hb; destruct Hb as [<-|[<-|[<-|[<-|[]]]]]; assumption|].
      rewrite (mb_static_blocks mb R R' MST) in Hb. intros EQ. exact (nodup_ids_app_ne [(es_id S, st, STORE_SIZE)] (blocks_MEMBIO mb R) _ _ NDsm (or_introl eq_refl) Hb (eq_sym EQ)). }
    (* [comment removed for export] *)
    assert (TRb : forall b A0' cs, In b L9 -> blk_id b <> es_id S -> rw_cells asegs m9 A0' cs -> blk_addr b <= A0' -> A0' + Z.of_nat (cells_size cs) <= blk_addr b + blk_size b -> rw_cells asegs m10 A0' cs).
    { intros b A0' cs Hb NE RC H1 H2. eapply rw_cells_transport; [exact RC| exact MU| exact WM|]. pose proof (proj1 (AV9 b Hb NE)) as D0. cbn in D0 |- *. clear - D0 H1 H2. split; [lia| exact I]. }
    assert (MB1 : In (mb_id R', mb, BIO_SIZE) L9 /\ blk_id (mb_id R', mb, BIO_SIZE) <> es_id S).
    { destruct (MBLB _ ltac:(unfold blocks_MEMBIO; left; reflexivity)) as [J NE]. split; [subst L9; apply in_or_app; right; apply SLB9; exact J| exact NE]. }
    assert (MB2 : In (mb_bbid R', mb_bb R', BIOBUFMEM_SIZE) L9 /\ blk_id (mb_bbid R', mb_bb R', BIOBUFMEM_SIZE) <> es_id S).
    { destruct (MBLB _ ltac:(unfold blocks_MEMBIO; right; left; reflexivity)) as [J NE]. split; [subst L9; apply in_or_app; right; apply SLB9; exact J| exact NE]. }
    assert (MB3 : In (mb_bmid R', mb_bm R', BUFMEM_SIZE) L9 /\ blk_id (mb_bmid R', mb_bm R', BUFMEM_SIZE) <> es_id S).
    { destruct (MBLB _ ltac:(unfold blocks_MEMBIO; right; right; left; reflexivity)) as [J NE]. split; [subst L9; apply in_or_app; right; apply SLB9; exact J| exact NE]. }
    assert (MB4 : In (mb_rpid R', mb_rp R', BUFMEM_SIZE) L9 /\ blk_id (mb_rpid R', mb_rp R', BUFMEM_SIZE) <> es_id S).
    { destruct (MBLB _ ltac:(unfold blocks_MEMBIO; right; right; right; left; reflexivity)) as [J NE]. split; [subst L9; apply in_or_app; right; apply SLB9; exact J| exact NE]. }
    assert (MBO10 : MEMBIO H LB m10 mb R').
    { destruct MBO9 as (X1 & X2 & X3 & X4 & REST). split; [| split; [| split; [| split; [| exact REST]]]].
      - eapply (TRb _ _ _ (proj1 MB1) (proj2 MB1) X1); cbn [blk_addr blk_size fst snd cells_size csize buf_cells bio_cells length Nat.add Nat.mul Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul]; unfold BIO_SIZE; clear; lia.
      - eapply (TRb _ _ _ (proj1 MB2) (proj2 MB2) X2); cbn [blk_addr blk_size fst snd cells_size csize buf_cells bio_cells length Nat.add Nat.mul Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul]; unfold BIOBUFMEM_SIZE; clear; lia.
      - eapply (TRb _ _ _ (proj1 MB3) (proj2 MB3) X3); cbn [blk_addr blk_size fst snd cells_size csize buf_cells bio_cells length Nat.add Nat.mul Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul]; unfold BUFMEM_SIZE; clear; lia.
      - eapply (TRb _ _ _ (proj1 MB4) (proj2 MB4) X4); cbn [blk_addr blk_size fst snd cells_size csize buf_cells bio_cells length Nat.add Nat.mul Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul]; unfold BUFMEM_SIZE; clear; lia. }
    assert (MSH10 : MEMBIO_shad m10 mb R').
    { destruct MSH9 as (Y1 & Y2 & Y3 & Y4).
      pose proof (BRS9 _ (proj1 MB1)) as (_ & _ & _ & _ & _ & _ & P1). pose proof (BRS9 _ (proj1 MB2)) as (_ & _ & _ & _ & _ & _ & P2).
      pose proof (BRS9 _ (proj1 MB3)) as (_ & _ & _ & _ & _ & _ & P3). pose proof (BRS9 _ (proj1 MB4)) as (_ & _ & _ & _ & _ & _ & P4). cbn [blk_addr blk_size fst snd] in P1, P2, P3, P4.
      split; [| split; [| split]]; (eapply addressable_across2; [eassumption| eassumption| exact MU| exact WM| exact NSHst]). }
    destruct (PAYL ltac:(clear - NAR; lia)) as [pD [PIN PNL]]. pose proof DSL as DSL1. unfold zlength in DSL1.
    assert (PDIN : In (pD, mb_buf R, mb_len R) L9 /\ blk_id (pD, mb_buf R, mb_len R) <> es_id S).
    { split; [subst L9; apply in_or_app; right; apply SLB9; exact PIN| cbn [blk_id fst snd]; exact (PAYL2 ltac:(clear - NAR; lia) _ PIN)]. }
    assert (DSm10 : bytes_at asegs m10 (mb_buf R) ds).
    { eapply bytes_at_transport; [exact DSm9| exact MU|]. pose proof (proj1 (AV9 _ (proj1 PDIN) (proj2 PDIN))) as D0. cbn [blk_addr blk_size fst snd] in D0. rewrite DSL1. exact D0. }
    destruct (drest_idsc _ _ _ _ ND9) as (_ & _ & _ & DTB9 & DBIN9 & DPA9 & DLE9).
    assert (BIN9' : In (pbin, Bb, nB) L9 /\ blk_id (pbin, Bb, nB) <> es_id S).
    { split; [subst L9; apply in_or_app; right; exact IB9| cbn [blk_id fst snd]; exact (DBIN9 _ _ (or_introl eq_refl) ltac:(right; apply in_or_app; right; exact (proj1 (proj2 SO))))]. }
    assert (PAIN9 : In (p, A, nA) L9 /\ blk_id (p, A, nA) <> es_id S).
    { split; [subst L9; apply in_or_app; right; exact IA9| cbn [blk_id fst snd]; exact (DPA9 _ _ (or_introl eq_refl) ltac:(apply in_or_app; right; exact (proj1 (proj2 SO))))]. }
    assert (DSb10 : bytes_at asegs m10 Bb bs).
    { eapply bytes_at_transport; [exact DSb9| exact MU|]. pose proof (proj1 (AV9 _ (proj1 BIN9') (proj2 BIN9'))) as D0. cbn [blk_addr blk_size fst snd] in D0. cbn in D0 |- *. clear - D0 NBRq. split; [lia| exact I]. }
    assert (CBb10 : rw_cells asegs m10 Bb [CB (length bs) bs; CB (Z.to_nat nB - length bs) jb9]).
    { eapply (TRb _ _ _ (proj1 BIN9') (proj2 BIN9') CBb9); cbn [blk_addr blk_size fst snd cells_size csize Nat.add]; [clear; lia| clear - NBRq; lia]. }
    assert (CBa10 : rw_cells asegs m10 A [CB (Z.to_nat (mb_len R)) ds; CB (Z.to_nat (nA - mb_len R)) ja9]).
    { eapply (TRb _ _ _ (proj1 PAIN9) (proj2 PAIN9) CBa9); cbn [blk_addr blk_size fst snd cells_size csize Nat.add]; [clear; lia| clear - NAR; lia]. }
    assert (ADb10 : addressable m10 Bb nB).
    { pose proof (BRS9 _ (proj1 BIN9')) as (_ & _ & _ & _ & _ & _ & P1). eapply addressable_across2; [exact ADb9| exact P1| exact MU| exact WM| exact NSHst]. }
    assert (ADa10 : addressable m10 A nA).
    { pose proof (BRS9 _ (proj1 PAIN9)) as (_ & _ & _ & _ & _ & _ & P1). eapply addressable_across2; [exact ADa9| exact P1| exact MU| exact WM| exact NSHst]. }
    assert (BT10 : BT m10).
    { eapply (BT_frame L9 S1c); [exact BT9| exact XP910| intros b Hb; subst L9; apply in_or_app; right; apply STB9; exact Hb| exact AS1| | exact MI10].
      intros b Hb. assert (HbL : In b L9) by (subst L9; apply in_or_app; right; apply STB9; exact Hb).
      split; [apply (proj2 (AV9 _ HbL (DTB9 _ _ Hb ltac:(right; right; apply in_or_app; right; exact (proj1 (proj2 SO))))))| apply SHAV; [eapply aapp_sub; [exact SB7| clear; lia| unfold STORE_SIZE; clear; lia]| clear; lia| exact HbL]]. }
      (* [comment removed for export] *)
    assert (FR010 : rw_cells asegs m10 S1c [CB 16 jz]) by (eapply rw_cells_transport; [exact FR09| exact MU| exact WM| apply DJF; clear; lia]).
    assert (FR110 : rw_cells asegs m10 (S1c + 16) (dsg1c w16 w32 w40 (wz (cur + 4 + elen)))) by (eapply rw_cells_transport; [exact FR19| exact MU| exact WM| apply DJF; clear; lia]).
    assert (FR210 : rw_cells asegs m10 (S1c + 144) (dsg2c (wz ee) v192 v200 v208 v224 v232)) by (eapply rw_cells_transport; [exact FR29| exact MU| exact WM| apply DJF; clear; lia]).
    assert (FR310 : rw_cells asegs m10 (S1c + 240) (arp_sg3 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12)) by (eapply rw_cells_transport; [exact FR39| exact MU| exact WM| apply DJF; clear; lia]).
    assert (FRG10 : rw_cells asegs m10 (S1c + 344) [CB (Z.to_nat KGc) jg]) by (eapply rw_cells_transport; [exact FRG9| exact MU| exact WM| apply DJF; clear; lia]).
    assert (FRS10 : rw_cells asegs m10 (bv_unsigned sp + -104) SAVESc) by (eapply rw_cells_transport; [exact FRS9| exact MU| exact WM| apply DJF; clear - Q2; lia]).
    assert (FF10 : rw_cells asegs m10 ff (dffc tpl lb9)).
    { eapply rw_cells_transport; [exact FF9| exact MU| exact WM|]. cbn. unfold AFS_SIZE in SB6. clear - SB6 FQ5 FQ6. split; [lia| exact I]. }
    assert (SHF : SH = sh ff) by (unfold sh, ASHB; rewrite Z.shiftr_div_pow2 by (clear; lia); rewrite ASHADOW_BASE_val; change (2 ^ 3) with 8; clear; lia).
    assert (FSH10 : rw_cells asegs m10 SH (dfshc (b8 0xf8) (b8 0xf8) (poison_bytes 256 0xf8))).
    { eapply rw_cells_transport; [exact FSH9| exact MU| exact WM|]. rewrite SHF. cbn.
      pose proof (sh_aapp_range _ _ AF4 ltac:(unfold AFS_SIZE; clear; lia)) as (W1 & _ & _). rewrite SHT in W1.
      pose proof (sh_mono (as_FSB H) ff ltac:(clear - FQ5; lia)) as SYL. pose proof (sh_mono _ _ (Z.le_trans _ _ _ FQ6 AF2)) as SYC. pose proof (sh_add8 ff 512) as SY8. replace (ff + 8 * 512) with (ff + 4096) in SY8 by (clear; lia).
      unfold ALOWSH_LO, AHI_LO in STNS. clear - STNS W1 SYL SYC SY8 SHC. unfold AHI_LO in SHC. split; [lia| exact I]. }
    assert (RFS10 : as_RFS H (LF1c ff fp) m10).
    { eapply (ah_RFS_frame H HH); [exact RFS9| exact MU| exact WM|]. apply Forall_cons; [| apply Forall_nil].
      left. cbn. unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AFS_SIZE in *. clear - SB4 SB5 SB6 AF1 AF2 ACB. lia. }
    assert (ERR10 : rw_cells asegs m10 (errno_addr (Z_to_bv 64 ATP)) [C4 errv9]).
    { eapply rw_cells_transport; [exact ERR9| exact MU| exact WM|]. assert (ERNG : 0 <= errno_addr (Z_to_bv 64 ATP) <= 0xc04000 - 4) by (clear; vm_compute; split; discriminate).
      cbn -[errno_addr]. clear - ERNG SB4. split; [lia| exact I]. }
    assert (AUX10 : as_rauxv_ok H m10 B) by (eapply (ah_rauxv_frame H HH); [exact AUX9| exact MU| exact WM| exact CWst]).
    assert (AC10 : ACONST m10) by (eapply ACONST_frame; [exact AC9| exact MU| exact WM| apply Forall_cons; [eapply aconst_ok_aapp; [exact SB7| cbn; clear; lia| cbn; unfold STORE_SIZE; clear; lia]| apply Forall_nil]]).
    assert (ST10 : stk asegs m10 lo S1c) by (eapply stk_transport_disjoint; [exact ST9| exact MU| exact WM| cbn; clear - SB5 CEIL; split; [lia| exact I]]).
    assert (STK10 : stack0 m10 lo (bv_unsigned sp)).
    { eapply stack0_transport; [exact STK9| exact MU| exact WM|]. apply Forall_cons; [eapply stack0_ok_aapp; [exact SB7| cbn; clear; lia| cbn; unfold STORE_SIZE; clear; lia]| apply Forall_nil]. }
    assert (CHN10 : as_chain H m10 (bv_unsigned sp) CH1c).
    { eapply (achain_below H HH m9 m10 _ _ _ (S1c + 16)); [exact CHN9| exact CHBx| exact MU|]. apply Forall_cons; [left; cbn; clear - SB5 AS1; lia| apply Forall_nil]. }
    destruct XA9 as (XSq & FXq & INq & XA9').
    assert (XA10 : xpres H LB (bv_unsigned sp) (XSq ++ XFc) m m10).
    { eapply xpres_trans; [exact XA9'|]. eapply xpres_weaken; [exact XP910| clear - Q2; lia| intros b Hb; subst L9; apply in_or_app; right; apply SLB9; exact Hb|].
      intros q Hq. apply rin_ivs_app. right. unfold XF. cbn [rin_ivs fst snd app] in Hq |- *. left. unfold STORE_SIZE. clear - Hq. lia. }
    assert (SKO10 : SKobj ([BK] ++ LE2 ++ LB) m10 Ask Kth).
    { eapply ECH_AC14_kit.SKobj_relist; [| intros b Hb; rewrite BKE in Hb; apply in_or_app; left; exact Hb].
      eapply (ECH_AC14_kit.SKobj_frameX H _ S1c); [exact SKO9| exact XP910| | subst Kth; cbn; intros NC; exfalso; apply NC; reflexivity].
      assert (NEK : blk_id BK <> es_id S).
      { cbv delta [BK]. cbn [blk_id fst snd]. intros EQ. exact (D29 (kid, Ask, SK_SIZE) (es_id S, st, STORE_SIZE) (or_introl eq_refl) (proj1 (drest_subc [] [] LE2) _ (proj1 (proj2 SO))) EQ). }
      pose proof (proj2 (AV9 BK BKIN9 NEK)) as K0. cbv delta [BK] in K0. cbn [blk_addr blk_size fst snd] in K0. exact K0. }
    assert (SKSH10 : SK_shad m10 Ask Kth).
    { destruct SKSH9 as [SA _]. split; [eapply addressable_across2; [exact SA| exact BKAP| exact MU| exact WM| exact NSHst]| subst Kth; cbn; intros NC; exfalso; apply NC; reflexivity]. }
    assert (LM10 : LIBMID (LE2 ++ LIB) m10 M2).
    { eapply (LIBMID_xobj H HH s3' m9 (LE2 ++ LIB) L9 S1c [(st, st + 8)] [] [(es_id S, st, STORE_SIZE)] m9 m10 M2 x);
        [exact HP9| exact LM9| rewrite CTX1; exact CTX| exact XP910| intros b Hb; subst L9; apply in_or_app; right; apply SL09; apply SLL9; exact Hb
        | intros b Hb; subst L9; apply in_or_app; left; exact Hb| intros b [<-|[]]; exact STIN9| | apply Forall_nil
        | intros q Hq; left; exists (es_id S, st, STORE_SIZE); split; [left; reflexivity| cbn [blk_addr blk_size fst snd]; cbn [rin_ivs fst snd] in Hq; unfold STORE_SIZE; clear - Hq; lia]].
      intros b b' Hb [<-|[]]. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [exact (NEL _ Hb)|]. cbn [blk_id fst snd]. exact (D19 _ _ Hb ltac:(apply SLB9; exact (proj1 (proj2 SO)))). }
    assert (HP10 : as_RHEAP H s3' (mid_errblocks M2 ++ drestc Lx [BK] LE2) m10).
    { eapply PERM; [eapply (ah_RHEAP_frame H HH); [exact HP9| exact MU| exact WM| exact CWst]|].
      subst L9. unfold drest. cbn [app]. apply Permutation_app_head. apply Permutation_middle. }
    assert (DW10 : adwkc Lx [BK] S1' M2 LE2 w16 w32 w40 (wz (cur + 4 + elen)) (wz ee) v192 v200 v208 v224 v232 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tpl (um + SK_SIZE) uf m10 s3').
    { unfold adwk, adwkG. repeat match goal with |- _ /\ _ => split end.
      all: try assumption.
      all: try (intros K0 es0 EQ0; subst S1'; cbn [es_entries_o] in EQ0; injection EQ0 as <- <-; subst Kth; cbn; clear; lia).
      all: lazymatch goal with
           | |- STOREobj _ _ _ _ =>
               subst S1'; unfold STOREobj; cbn [es_entries es_entries_o es_id]; split; [exact SC10|];
               split; [apply in_or_app; right; apply in_or_app; right; rewrite SID; exact (proj1 (proj2 SO))|];
               unfold ENTRIES; split; [exact APOS|]; split; [exact SKO10| split; [subst Kth; reflexivity| subst Kth; cbn [sk_elems sk_with_thunk sk_fresh]; apply Forall2_nil]]
           | |- STORE_shad _ _ _ =>
               subst S1'; unfold STORE_shad; cbn [es_entries es_entries_o]; split; [exact STOP9|];
               split; [eapply addressable_across2; [exact STAD9| exact SB7| exact MU| exact WM| exact NSHst]|];
               unfold ENTRIES_shad, SKX_shad; split; [| subst Kth; cbn [sk_elems sk_with_thunk sk_fresh]; apply Forall2_nil]; split; [exact SKSH10| split; [unfold AAPP_HI, SK_SIZE; clear - KB ACB; lia| subst Kth; cbn; intros NC; exfalso; apply NC; reflexivity]]
           | |- es_id _ = es_id S => subst S1'; cbn [es_id]; exact SID
           | |- Permutation (blocks_STORE st _) _ => subst S1'; unfold blocks_STORE; cbn [es_entries es_entries_o es_id]; rewrite BKE, SID; subst Kth; cbn [sk_elems sk_with_thunk sk_fresh combine map concat app]; apply Permutation_refl
           | |- List.NoDup (map blk_id (blocks_STORE st _)) =>
               subst S1'; unfold blocks_STORE; cbn [es_entries es_entries_o es_id]; rewrite BKE, SID; subst Kth; cbn [sk_elems sk_with_thunk sk_fresh combine map concat app]; cbv delta [BK]; cbn [map blk_id fst snd];
               apply List.NoDup_cons; [| apply List.NoDup_cons; [intros K1; exact K1| apply List.NoDup_nil]]; cbn; intros [K0|[]];
               exact (D29 (kid, Ask, SK_SIZE) (es_id S, st, STORE_SIZE) (or_introl eq_refl) (proj1 (drest_subc [] [] LE2) _ (proj1 (proj2 SO))) K0)
           | |- exists junk, rw_cells asegs _ Bb _ => exists jb9; exact CBb10
           | |- exists junk, rw_cells asegs _ A _ => exists ja9; exact CBa10
           | |- exists errv', rw_cells asegs _ (errno_addr _) _ => exists errv9; exact ERR10
           | |- exists lb, rw_cells asegs _ ff _ => exists lb9; exact FF10
           | |- exists XSq0, _ => exists XSq; split; [exact FXq| split; [exact INq| exact XA10]]
           | |- length (poison_bytes 256 248) = 256%nat => exact LSHc
           | |- ?G => idtac "DW10LEFT" G
           end. }
    (* [comment removed for export] *)
    assert (NES : forall b, In b (blocks_ENTRY ee E) -> blk_id b <> es_id S).
    { intros b Hb. exact (D29 b (es_id S, st, STORE_SIZE) ltac:(right; eapply Permutation_in; [exact PE| exact Hb]) (proj1 (drest_subc [] [] LE2) _ (proj1 (proj2 SO)))). }
    assert (EBL9 : forall b, In b (blocks_ENTRY ee E) -> In b L9) by (intros b Hb; subst L9; apply in_or_app; right; apply SLX9; right; eapply Permutation_in; [exact PE| exact Hb]).
    assert (EO10' : ENTRYobj (drestc (BK :: Lx) [] LE2) m10 ee E).
    { eapply (ENTRYobj_frameX H _ S1c [(st, st + 8)]); [exact EO9| eapply xpres_weaken; [exact XP910| clear; lia| intros b Hb; subst L9; apply in_or_app; right; exact Hb| intros q Hq; exact Hq]|].
      intros b Hb. exact (proj2 (AV9 b (EBL9 b Hb) (NES b Hb))). }
    assert (EO10 : ENTRYobj (drestc Lx [BK] LE2) m10 ee E).
    { eapply ENTRYobj_LB_mono; [exact EO10'|]. intros b Hb. unfold drest in Hb |- *. clear - Hb. simpl in Hb.
      destruct Hb as [EQB|Hb]; [apply in_or_app; right; apply in_or_app; left; left; exact EQB|].
      apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left; exact Hb| right; apply in_or_app; right; exact Hb]. }
    assert (ESH10 : ENTRY_shad m10 ee E).
    { eapply (ENTRY_shad_frameX H (drestc (BK :: Lx) [] LE2) L9 S1c [(st, st + 8)]); [exact ESH9| exact EO9| exact XP910|].
      intros b Hb. split; [exact (EBL9 b Hb)|]. split; [exact (proj2 (AV9 b (EBL9 b Hb) (NES b Hb)))|].
      apply SHAV; [eapply aapp_sub; [exact SB7| clear; lia| unfold STORE_SIZE; clear; lia]| clear; lia| exact (EBL9 b Hb)]. }
    assert (PBK : Permutation (BK :: drestc Lx [] LE2) (drestc Lx [BK] LE2)) by (unfold drest; cbn [app]; apply Permutation_middle).
    assert (DB' : dbudc (drestc Lx [BK] LE2) M2 (PUSH_HB - SK_SIZE) (PUSH_HC - 1)).
    { unfold dbud in DB1, DB2 |- *. rewrite <- (ECH_AC14_kit.lb_bytes_perm _ _ PBK), <- (Permutation_length PBK). rewrite lb_bytes_cons. cbv delta [BK]. cbn [blk_size snd length].
      rewrite Nat2Z.inj_succ. unfold SK_SIZE. clear - DB1 DB2. set (XB := lb_bytes _) in *. set (XC := length _) in *. set (EBY := errph_bytes _) in *. set (ECN := errph_cnt _) in *. split; lia. }
    assert (SG0 : sk_grow 0 = 0) by reflexivity.
    assert (PC3 : SKPUSH_COST Kth = 32 /\ sk_cap Kth = 0) by (subst Kth; unfold SKPUSH_COST; cbn [sk_cap sk_with_thunk sk_fresh]; rewrite SG0; split; reflexivity).
    destruct PC3 as [PC3 CK3].
    eapply (de_pushcall cur rem S' um0 uf0 ph0 Lx [BK] S1' M2 LE2 w16 w32 w40 v192 v200 v208 v224 v232 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tpl (um + SK_SIZE) uf elen (PUSH_HB - SK_SIZE) (PUSH_HC - 1) m10 s3' msF10 mo10 ee E Kth []);
      [exact DW10| subst S1'; reflexivity| | | exact EO10| exact ESH10| exact PE| exact EEP| exact ECNT| exact EBYT| exact EL19| exact ER| exact CUR1| exact CUR2| | exact DB'
      | rewrite PC3; unfold PUSH_HB, SK_SIZE; clear; lia| unfold PUSH_HC; clear; lia
      | rewrite PC3; unfold PUSH_CM, SK_SIZE in *; clear - UM1; lia| rewrite CK3; unfold PUSH_CF in *; clear - UF1; lia
      | rewrite PC3; unfold PUSH_CM, SK_SIZE in *; clear - UM2 EP0; lia| rewrite CK3; unfold PUSH_CF in *; clear - UF2 EP0 LX0; lia
      | exact KADV| exact VIS10| exact KREL10
      | eapply (ah_mpres_trans H HH); [exact MP1|]; eapply (ah_mpres_trans H HH); [exact MP2|]; eapply (ah_mpres_trans H HH); [exact MP3|]; eapply (ah_mpres_trans H HH); [exact MP4|];
        eapply (ah_mpres_trans H HH); [exact MP5|]; eapply (ah_mpres_trans H HH); [exact MP6|]; eapply (ah_mpres_trans H HH); [exact MP7|]; eapply (ah_mpres_trans H HH); [exact MP8|];
        eapply (ah_mpres_trans H HH); [exact MP9| exact MP10]].
    - subst S1'. unfold EBS. cbn [es_entries_o]. rewrite ESO. subst Kth. cbn [sk_elems sk_with_thunk sk_fresh combine map concat]. reflexivity.
    - subst S1'. unfold nent. cbn [es_entries_o length Z.of_nat]. rewrite ESO. reflexivity.
    - subst S1'. unfold nent. cbn [es_entries_o length Z.of_nat]. clear; lia.
  Qed.
End RC.
