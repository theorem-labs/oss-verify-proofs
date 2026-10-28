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
  ECH_ALibMF ECH_Iface ECH_AStmt_C1 ECH_AC1_zalloc ECH_AC1_free ECH_AC1_malloc ECH_AC1_dup ECH_AStmt_C3 ECH_AStmt_C4 ECH_AStmt_C5 ECH_AStmt_C6 ECH_AC6_acc ECH_AStmt_C7 ECH_AStmt_C8 ECH_AStmt_C9
  ECH_AStmt_C10 ECH_AStmt_C13 ECH_AKit ECH_AKitSeg ECH_AsKit ECH_AC13_entry ECH_AC13_store ECH_AC7_kit ECH_AC7_rd ECH_AC7_rd2 ECH_AC7_bioread ECH_AC7_biofreeint ECH_ARostr ECH_ALibMid ECH_AC11_fail
  ECH_AKitS ECH_AC12_addstr ECH_AC13_small ECH_AC13 ECH_AC14_kit ECH_AC14_bio2buf_seg ECH_AC14_ladder_seg ECH_AC14_ladloop ECH_AC14_fmt_seg ECH_AC14_flat_seg ECH_AC14_b64arm_seg ECH_AC14_entry_seg
  ECH_AStmt_C14 F_strspn N6_strspn ECH_AC14_b2b ECH_AC14_fmt ECH_AC14_dec ECH_AC14_b64arm ECH_AC14_flatten.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import ECH_B64.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim StrFun.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section RC.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HX : asan_rt_hyps_x H.
  Hypothesis RAISE : araise_stmt H.
  Hypothesis SPN : strspn_icpt_stmt.                (* [comment removed for export] *)
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
  Local Notation SLOTSc := (SLOTS sp st).
  Local Notation rp_b64Kc := (rp_b64K H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo s LIB LB LF M st mb lo B S R ds CH).
  Local Notation "'DCW' f" := (f H ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m s LIB LB LF M st mb lo B S R ds CH) (at level 10, f at level 0).
  Local Notation "'DCS' f" := (f H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo s LIB LB LF M st mb lo B S R ds CH) (at level 10, f at level 0).
  Local Notation "'DCB' f" := (f H PF9free ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo s LIB LB LF M st mb lo B S R ds CH) (at level 10, f at level 0).
  Local Notation "'DCI' f" := (f H HX RAISE PF9new PF9free ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc msF m mo s LIB LB LF M x st mb lo B S R ds errv CH
                                 VIS0 A0 A1 SO SE SEO STL SSH MBO MP0 MN0 MBB MBS MSH PAY DS DSL PAYL PAYL2 NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC AUX SPB BHI SPA ST CEIL LO ST0 ERR MI TP AC MCO RFS LFB ATH CHN CHB PF ALW RAE)
    (at level 10, f at level 0).


  (* [comment removed for export] *)
  Hypothesis AUXV : aauxv_ok m B.
  (* [comment removed for export] *)
  Hypothesis NEWMB : newmembuf_stmt H.
  Hypothesis BNEW : bionew_b64_stmt H.
  Hypothesis BPUSH : biopush_stmt H.
  Hypothesis BREAD : bioread_b64_stmt H.
  Hypothesis BFALL : biofreeall_stmt H.
  Hypothesis PF9NEW : forall xq, PF9new (CtxReady xq) = PF_bionew_b64 xq.
  Hypothesis PF9FREE : PF9free = PF_biofreeall.
  (* [comment removed for export] *)
  Hypothesis RPE : rp_entry_shape H.

  Local Notation rp_decK0c := (rp_decK0 H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo s LIB LB LF M st mb lo B S R ds CH).
  (* [comment removed for export] *)
  Local Notation RPEc := (RPE PF9new PF9free ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc msF m mo s LIB LB LF M x st mb lo B S R ds errv CH
                          VIS0 A0 A1 SO SE SEO STL SSH MBO MP0 MN0 MBB MBS MSH PAY DS DSL PAYL PAYL2 NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC AUX SPB BHI SPA ST CEIL LO ST0 ERR MI TP AC MCO RFS LFB ATH CHN CHB PF ALW RAE).

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
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma rw_CB_bytes_at : forall m0 A0' k bs0, rw_cells asegs m0 A0' [CB k bs0] -> bytes_at asegs m0 A0' bs0.
  Proof. clear. intros m0 A0' k bs0 [[WF BA] _]. cbn [cells_bytes cbytes app] in BA. rewrite app_nil_r in BA. exact BA. Qed.

  (* [comment removed for export] *)
  Lemma rw_cells_CB0 : forall m0 a, 0 <= a -> a <= 2^64 -> rw_cells asegs m0 a [CB 0 []].
  Proof.
    clear. intros m0 a R1 R2. unfold rw_cells, cells_at, bytes_at, wr_at. cbn.
    repeat split; try (clear - R1 R2; lia); intros i Hi; exfalso; clear - Hi; lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma btfree_null : forall (p : bptr) (A nA : Z) (pbin : bptr) (Bb nB : Z) (bs : list byte) (R' : membio)
                             (ff fp n : Z) (fj24 tpb fj128 fj2 jz jg e5 : list byte),
    1 <= mb_len R <= nA /\ nA <= 512 * 3 -> 0 <= zlength bs <= nB /\ nB <= mb_len R /\ mb_len R < OSSL_ECH_MAX_ECHCONFIG_LEN ->
    mb_static R R' -> mb_pos R' = mb_len R -> fresh_frame H LF 6 ff fp ->
    (DCB btfree_stmt) p A nA pbin Bb nB bs R' 0 [] (fun _ => True) ff fp n fj24 tpb fj128 fj2 jz jg e5.
  Proof using VIS0 A0 A1 SO SE SEO STL SSH MBO MP0 MN0 MBB MBS MSH PAY DS DSL PAYL PAYL2 NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC AUX SPB BHI SPA ST CEIL LO ST0 ERR MI TP AC MCO RFS LFB ATH CHN CHB PF ALW RAE HH HX RAISE SM6 SF6 SSF8 PERM SPN AUXV NEWMB BNEW BPUSH BREAD BFALL PF9NEW PF9FREE RPE.
    intros until e5. intros NAR NBR MST POS FRESH.
    assert (BTR : 0 <= 0 < 2^64 /\ Z.of_nat (@length block []) <= 7 /\ lb_bytes [] <= 3072) by (cbn; clear; lia).
    assert (BTF : forall (L : list block) (SP : Z) (X : list (Z * Z)) (m1 m2 : mem),
               (fun _ : mem => True) m1 -> xpres H L SP X m1 m2 -> (forall b, In b [] -> In b L) -> aceil <= SP ->
               (forall b, In b [] -> avoids X (blk_addr b) (blk_size b) /\ shavoids X (blk_addr b) (blk_size b)) -> mem_inv asegs m2 -> (fun _ : mem => True) m2)
      by (intros; exact I).
    unfold btfree_stmt.
    intros NB S' M' LE fr1 fr3 wee v192 v200 v208 v224 v232 tpl um uf m1 s1' msF1 mo1 ra0 u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 s2w s3w s4w s5w s6w s7w s8w s9w s10w s11w u3 u4 u5 u6 Q.
    intros DW RAR RAE2 DNB PFF UFB UMB VIS1 KREL1 MP1 K.
    destruct rc_facts_c as (SEQ & SIN & SBR & BLK0 & SUB0 & ND0 & STK0 & LO0 & MF0 & OBJ0 & DJA & AFSB & ACB & Q1 & Q2 & SPR). change (rp_s1 (bv_unsigned sp)) with S1c in Q1, Q2.
    pose proof DW as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FR1 & SZ1 & FR2 & FR3 & SZ3 & _ & _ & [lb FF1] & FSH1 & LSH1 & _ & _ & _ & MI1 & AC1 & ST1 & _).
    destruct (ACONST_shbase m1 AC1) as [GSB SHB1].
    eapply (ahh_evt_then H HH); [exact KREL1| exact VIS1| eapply abio_free_all_null with (lo := lo);
      [exact GSB| exact SHB1| rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); exact ST1| exact CEIL
      | rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); clear - LO STK0 Q2; lia| exact MI1
      | rewrite unsigned_lit by (clear - RAR; lia); exact RAE2]|].
    intros msF2 mo2 KREL2 MP2 (m2 & VIS2 & MU2 & WM2 & MI2 & ST2).
    rewrite (unsigned_lit S1c) in MU2, ST2 by (clear - Q2 SPR CEIL LO STK0 LO0; lia).
    assert (T12 : forall A' cs, rw_cells asegs m1 A' cs -> (A' + Z.of_nat (cells_size cs) <= S1c + -48 \/ S1c <= A') -> rw_cells asegs m2 A' cs).
    { intros A' cs RC HA. eapply rw_cells_transport; [exact RC| exact MU2| exact WM2|]. cbn. split; [clear - HA; lia| exact I]. }
    pose proof (fresh_frame_facts H _ _ _ _ FRESH) as (_ & FQ1 & FQ2 & FQ64 & FQ8 & FP1 & FP2 & FP3 & FP4 & FQ5 & FQ6 & FB1 & FB2 & FB3).
    change (fsz 6) with 4096 in FQ2, FQ6. unfold AFS_HDR, AFS_FLAGS, AFS_SIZE, AIMG_TOP in FQ1, FQ2, FP1, FP2, FP3, FP4, FQ5, FQ6, FB1, FB2.
    pose proof AFSB as (AF1 & AF2 & AF3 & AF4). unfold AFS_SIZE in AF2.
    assert (SHC : sh aceil < aceil) by (unfold sh; rewrite ASHADOW_BASE_val; clear - ACB; lia).
    assert (DW2 : (DCW adwkG) p A nA pbin Bb nB bs R' [] (fun _ => True) ff fp n fj24 tpb fj128 fj2 jz jg e5 [] NB S' M' LE fr1 wee v192 v200 v208 v224 v232 fr3 tpl (b8 0xf8) (b8 0xf8) (poison_bytes 256 0xf8) um uf m2 s1').
    { eapply ((RCI adwkG_w) p A nA pbin Bb nB bs R' 0 [] (fun _ => True) ff fp n fj24 tpb fj128 fj2 jz jg e5 NAR NBR MST POS BTR BTF FRESH
                [] NB S' M' LE fr1 wee v192 v200 v208 v224 v232 fr3 tpl (b8 0xf8) (b8 0xf8) (poison_bytes 256 0xf8) um uf m1 s1' m2 [(S1c + -48, S1c)] fr1 wee v192 v200 v208 v224 v232 fr3 tpl lb (b8 0xf8) (b8 0xf8) (poison_bytes 256 0xf8));
        [exact DW| exact MU2| exact WM2| exact MI2| exact ST2| apply Forall_cons; [left; cbn [fst snd]; clear - LO STK0 Q2; lia| apply Forall_nil]
        | apply T12; [exact FR1| right; clear; lia]| exact SZ1| apply T12; [exact FR2| right; clear; lia]| apply T12; [exact FR3| right; clear; lia]| exact SZ3
        | apply T12; [exact FF1| left; unfold dff, arp_fframe2; cbn [cells_size csize Nat.add length]; clear - FQ6 AF2 CEIL LO STK0 Q2; lia]
        | apply T12; [exact FSH1| left; unfold dfsh, arp_fshadow; cbn [cells_size csize Nat.add length];
                      pose proof (sh_add8 ff 512) as SY8; replace (ff + 8 * 512) with (ff + 4096) in SY8 by (clear; lia); pose proof (sh_mono (ff + 4096) _ FQ6) as SYU; pose proof (sh_mono _ _ AF2) as SYA;
                      unfold sh, ASHB in *; rewrite ?Z.shiftr_div_pow2 by (clear; lia); change (2 ^ 3) with 8; clear - SY8 SYU SYA SHC CEIL LO STK0 Q2; rewrite ?ASHADOW_BASE_val in *; lia]
        | exact LSH1]. }
    pose proof DW2 as (HP2 & LM2 & _ & _ & _ & _ & _ & _ & _ & SO2 & SSH2 & _ & _ & _ & _ & MB2 & MSH2 & DS2 & BS2 & BC2 & ADB2 & AC2 & ADA2 & _
                       & FRJ2 & FR12 & _ & FR22 & FR32 & _ & FRG2 & SAV2 & FF2 & FSH2 & _ & RFS2 & [errv2 ERR2] & AUX2 & MI2' & ACO2 & STK2 & ST02 & CHN2 & XA2 & LED2).
    destruct XA2 as (XSq & FXq & XIq & XPq).
    unfold drest in HP2. cbn [app] in HP2.
    eapply (K m2 s1' msF2 mo2 errv2 uf XSq); [exact VIS2| exact KREL2| exact (ah_mpres_trans H HH _ _ _ MP1 MP2)| exact HP2| exact MI2'| exact ACO2| exact STK2| exact ST02
      | exact ERR2| exact AUX2| exact RFS2| exact LM2| exact SO2| exact SSH2| exact MB2| exact MSH2| exact DS2| exact BC2| exact ADB2| exact AC2| exact ADA2
      | exact FRJ2| exact FR12| exact FR22| exact FR32| exact FRG2| exact SAV2| exact FF2| exact FSH2| exact CHN2| exact FXq| exact XIq| exact XPq| exact LED2| clear; lia].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma ERRLc : forall (p : bptr) (A nA : Z) (pbin : bptr) (Bb nB : Z) (bs : list byte) (R' : membio) (bt : Z) (TB : list block) (BT : mem -> Prop)
                       (ff fp n : Z) (fj24 tpb fj128 fj2 jz jg e5 : list byte),
    1 <= mb_len R <= nA /\ nA <= 512 * 3 -> 0 <= zlength bs <= nB /\ nB <= mb_len R /\ mb_len R < OSSL_ECH_MAX_ECHCONFIG_LEN ->
    mb_static R R' -> mb_pos R' = mb_len R -> 0 <= bt < 2^64 /\ Z.of_nat (length TB) <= 7 /\ lb_bytes TB <= 3072 ->
    (forall (L : list block) (SP : Z) (X : list (Z * Z)) (m1 m2 : mem),
        BT m1 -> xpres H L SP X m1 m2 -> (forall b, In b TB -> In b L) -> aceil <= SP ->
        (forall b, In b TB -> avoids X (blk_addr b) (blk_size b) /\ shavoids X (blk_addr b) (blk_size b)) -> mem_inv asegs m2 -> BT m2) ->
    fresh_frame H LF 6 ff fp ->
    (DCB btfree_stmt) p A nA pbin Bb nB bs R' bt TB BT ff fp n fj24 tpb fj128 fj2 jz jg e5 ->
    (DCS rp_errl_stmt) p A nA pbin Bb nB bs R' bt TB BT ff fp n fj24 tpb fj128 fj2 jz jg e5.
  Proof using VIS0 A0 A1 SO SE SEO STL SSH MBO MP0 MN0 MBB MBS MSH PAY DS DSL PAYL PAYL2 NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC AUX SPB BHI SPA ST CEIL LO ST0 ERR MI TP AC MCO RFS LFB ATH CHN CHB PF ALW RAE HH HX RAISE SM6 SF6 SSF8 PERM SPN AUXV NEWMB BNEW BPUSH BREAD BFALL PF9NEW PF9FREE RPE.
    intros until e5. intros NAR NBR MST POS BTR BTF FRESH BTFq.
    exact ((RCI rp_errl) p A nA pbin Bb nB bs R' bt TB BT ff fp n fj24 tpb fj128 fj2 jz jg e5 NAR NBR MST POS BTR BTF FRESH
             (RPEc p A nA pbin Bb nB bs R' bt TB BT ff fp n fj24 tpb fj128 fj2 jz jg e5 (Z_to_bv 64 0) NAR NBR MST POS BTR BTF FRESH AUXV) BTFq).
  Qed.

  Lemma RPFLATc : forall (p : bptr) (A nA : Z) (pbin : bptr) (Bb nB : Z) (bs : list byte) (R' : membio) (bt : Z) (TB : list block) (BT : mem -> Prop)
                         (ff fp n : Z) (fj24 tpb fj128 fj2 jz jg e5 : list byte),
    1 <= mb_len R <= nA /\ nA <= 512 * 3 -> 0 <= zlength bs <= nB /\ nB <= mb_len R /\ mb_len R < OSSL_ECH_MAX_ECHCONFIG_LEN ->
    mb_static R R' -> mb_pos R' = mb_len R -> 0 <= bt < 2^64 /\ Z.of_nat (length TB) <= 7 /\ lb_bytes TB <= 3072 ->
    (forall (L : list block) (SP : Z) (X : list (Z * Z)) (m1 m2 : mem),
        BT m1 -> xpres H L SP X m1 m2 -> (forall b, In b TB -> In b L) -> aceil <= SP ->
        (forall b, In b TB -> avoids X (blk_addr b) (blk_size b) /\ shavoids X (blk_addr b) (blk_size b)) -> mem_inv asegs m2 -> BT m2) ->
    fresh_frame H LF 6 ff fp ->
    (DCB btfree_stmt) p A nA pbin Bb nB bs R' bt TB BT ff fp n fj24 tpb fj128 fj2 jz jg e5 ->
    (DCS rp_flat_stmt) p A nA pbin Bb nB bs R' bt TB BT ff fp n fj24 tpb fj128 fj2 jz jg e5.
  Proof using VIS0 A0 A1 SO SE SEO STL SSH MBO MP0 MN0 MBB MBS MSH PAY DS DSL PAYL PAYL2 NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC AUX SPB BHI SPA ST CEIL LO ST0 ERR MI TP AC MCO RFS LFB ATH CHN CHB PF ALW RAE HH HX RAISE SM6 SF6 SSF8 PERM SPN AUXV NEWMB BNEW BPUSH BREAD BFALL PF9NEW PF9FREE RPE.
    intros until e5. intros NAR NBR MST POS BTR BTF FRESH BTFq.
    exact ((RCI rp_flat) p A nA pbin Bb nB bs R' bt TB BT ff fp n fj24 tpb fj128 fj2 jz jg e5 NAR NBR MST POS BTR BTF FRESH
             (RPEc p A nA pbin Bb nB bs R' bt TB BT ff fp n fj24 tpb fj128 fj2 jz jg e5 (Z_to_bv 64 0) NAR NBR MST POS BTR BTF FRESH AUXV) BTFq).
  Qed.

  (* [comment removed for export] *)
  Lemma rp_b64 : rp_b64Kc.
  Proof using VIS0 A0 A1 SO SE SEO STL SSH MBO MP0 MN0 MBB MBS MSH PAY DS DSL PAYL PAYL2 NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC AUX SPB BHI SPA ST CEIL LO ST0 ERR MI TP AC MCO RFS LFB ATH CHN CHB PF ALW RAE HH HX RAISE SM6 SF6 SSF8 PERM SPN AUXV NEWMB BNEW BPUSH BREAD BFALL PF9NEW PF9FREE RPE. exact ((RCI rp_b64arm) NEWMB BNEW BPUSH BREAD BFALL PF9NEW PF9FREE ERRLc RPFLATc). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma rp_dec0 : rp_decK0c.
  Proof using VIS0 A0 A1 SO SE SEO STL SSH MBO MP0 MN0 MBB MBS MSH PAY DS DSL PAYL PAYL2 NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC AUX SPB BHI SPA ST CEIL LO ST0 ERR MI TP AC MCO RFS LFB ATH CHN CHB PF ALW RAE HH HX RAISE SM6 SF6 SSF8 PERM SPN AUXV NEWMB BNEW BPUSH BREAD BFALL PF9NEW PF9FREE RPE.
    unfold rp_decK0. intros p A nA R' ff fp fk1 fk2 jg e5 n um uf m1 s1' msF1 mo1 pbin Bb u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 s4w s5w u3 u4 u5 u6.
    intros L5 FW UMB UFB CELLS ADB VIS1 KREL1 MP1.
    destruct rc_facts_c as (SEQ & SIN & SBR & BLK0 & SUB0 & ND0 & STK0 & LO0 & MF0 & OBJ0 & DJA & AFSB & ACB & Q1 & Q2 & SPR). change (rp_s1 (bv_unsigned sp)) with S1c in Q1, Q2.
    pose proof (errph_bytes_range (mid_err M)) as [EBR ECR].
    pose proof FW as (HP1 & MBO1 & MST & POS & LR & NAR & LT & DSm1 & DSA1 & JK1 & ADA1 & SL1 & GP1 & SV1 & FRESH & FRM1 & FSH1 & RFS1 & ERR1 & AUX1 & LM1
                      & SC1 & SAD1 & MSH1 & PAYa1 & MI1 & AC1 & STK1 & ST01 & CHN1 & XA1 & LED1).
    cbn [app] in HP1.
    destruct SL1 as (jz & w16 & w24 & w32 & w40 & w48 & w56 & w64 & w72 & w80 & w88 & w192 & w200 & w208 & w224 & w232 & w240 & w248 & w256 & w264 & w272 & w280 & w288 & w296 & w304 & w312 & w320 & w328 & w336 & P0 & P1 & P2 & P3).
    destruct (fframe_to2 _ _ _ _ _ _ _ FRM1) as (tpl & fj24 & tpb & fj128 & FRM1' & TPLR).
    pose proof (errblocks_bounds _ _ _ LM1) as [EC1 EB1].
    pose proof SSH as SSHq. rewrite SEQ in SSHq. apply (proj1 (STORE_shad_empty _ _ _)) in SSHq. destruct SSHq as [SThi _].
    pose proof (rw_CB_bytes_at _ _ _ _ CELLS) as BS1.
    pose proof DSL as DSL1. unfold zlength in DSL1.
    pose proof (ah_blocks H HH _ _ _ _ HP1 ltac:(left; reflexivity)) as (Bb1 & Bb2 & Bb3 & Bb4 & Bb5 & Bb6 & Bb7). cbn [blk_addr blk_size fst snd] in Bb1, Bb2, Bb3, Bb4, Bb5, Bb6, Bb7.
    assert (NAR9 : 1 <= mb_len R <= nA /\ nA <= 512 * 3) by (clear - LR NAR; lia).
    assert (NBR9 : 0 <= zlength ds <= mb_len R /\ mb_len R <= mb_len R /\ mb_len R < OSSL_ECH_MAX_ECHCONFIG_LEN) by (rewrite DSL; clear - LR LT; lia).
    assert (BTR : 0 <= 0 < 2^64 /\ Z.of_nat (@length block []) <= 7 /\ lb_bytes [] <= 3072) by (cbn; clear; lia).
    assert (BTF : forall (L : list block) (SP : Z) (X : list (Z * Z)) (ma mb' : mem),
               (fun _ : mem => True) ma -> xpres H L SP X ma mb' -> (forall b, In b [] -> In b L) -> aceil <= SP ->
               (forall b, In b [] -> avoids X (blk_addr b) (blk_size b) /\ shavoids X (blk_addr b) (blk_size b)) -> mem_inv asegs mb' -> (fun _ : mem => True) mb')
      by (intros; exact I).
    (* [comment removed for export] *)
    assert (BC1 : exists junk, rw_cells asegs m1 Bb [CB (length ds) ds; CB (Z.to_nat (mb_len R) - length ds) junk]).
    { exists []. replace (Z.to_nat (mb_len R) - length ds)%nat with 0%nat by (clear - DSL1; lia).
      apply (proj2 (rw_cells_app asegs m1 Bb [CB (length ds) ds] [CB 0 []])). split.
      - replace (length ds) with (Z.to_nat (mb_len R)) by (clear - DSL1; lia). exact CELLS.
      - cbn [cells_size csize Nat.add]. apply rw_cells_CB0; clear - Bb1 Bb5 ACB DSL1 LR; lia. }
    (* [comment removed for export] *)
    assert (DW : (DCW adwkG) p A nA pbin Bb (mb_len R) ds R' [] (fun _ => True) ff fp n fj24 tpb fj128 fk2 jz jg e5 [] [] S M []
                   (arp_sg1 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 (wz 0) (wz (ff + 80)) (wz (ff + 64)) (wz 0) (wz st) (wz (ff + 32))) (wz ARP_FILE) w192 w200 w208 w224 w232 (arp_sg3 w240 w248 w256 w264 w272 w280 w288 w296 w304 w312 w320 w328 w336)
                   tpl (b8 0xf8) (b8 0xf8) (poison_bytes 256 0xf8) um uf m1 s1').
    { unfold adwkG.
      split. { eapply PERM; [exact HP1|]. unfold drest, L0. cbn [app].
               transitivity ((pbin, Bb, mb_len R) :: mid_errblocks M ++ (p, A, nA) :: LB); [apply perm_skip; apply Permutation_middle| apply Permutation_middle]. }
      split; [exact LM1|].
      split; [unfold mid_step; split; [exact MF1| split; [intros b Hb; exact Hb| split; [intros c Hc; exact Hc| intros Hv; exact Hv]]]|].
      split; [unfold mid_newlib_ok; exists [], []; split; [apply Permutation_refl| split; [rewrite CTX; reflexivity| destruct (mid_err M); reflexivity]]|].
      split; [reflexivity|].
      split; [exact EC1|]. split; [exact EB1|].
      split; [cbn [length Z.of_nat]; clear; lia|]. split; [change (lb_bytes []) with 0; clear; lia|].
      split; [rewrite SEQ; unfold STOREobj; cbn [es_entries es_entries_o es_id store_empty app]; split; [exact SC1| split; [exact (proj1 (proj2 SO))| reflexivity]]|].
      split; [rewrite SEQ; apply (proj2 (STORE_shad_empty _ _ _)); split; [exact SThi| exact SAD1]|].
      split; [reflexivity|].
      split; [rewrite SEQ; unfold blocks_STORE; cbn [es_entries_o es_id store_empty]; apply Permutation_refl|].
      split; [rewrite SEQ; unfold blocks_STORE; cbn [es_entries_o es_id store_empty map blk_id fst]; constructor; [intros []| constructor]|].
      split; [intros K es E; rewrite SEO in E; discriminate|].
      split; [exact MBO1|]. split; [exact MSH1|]. split; [exact DSm1|].
      split; [exact BS1|].
      split; [exact BC1|]. split; [exact ADB|].
      split; [exact JK1|]. split; [exact ADA1|].
      split; [exact I|].
      split; [exact P0|]. split; [exact P1|]. split; [reflexivity|]. split; [unfold dsg2; exact P2|]. split; [exact P3|]. split; [reflexivity|].
      split; [exact GP1|]. split; [exact SV1|].
      split; [unfold dff; exact FRM1'|]. split; [unfold dfsh; exact FSH1|]. split; [reflexivity|]. split; [exact RFS1|].
      split; [exact ERR1|]. split; [exact AUX1|]. split; [exact MI1|]. split; [exact AC1|]. split; [exact STK1|]. split; [exact ST01|].
      split; [exact CHN1|].
      split; [| exact LED1].
      exists (XSFc ff fp). split; [apply (fs_scratch_of_fresh H); exact FRESH|]. split; [intros q Hq; exact Hq|].
      eapply (xpres_weaken H); [exact XA1| apply Z.le_refl| intros b Hb; exact Hb|].
      intros q Hq. apply rin_ivs_app in Hq. apply rin_ivs_app. destruct Hq as [Hq|Hq]; [left; exact Hq| right]. unfold XF. apply rin_ivs_app; right. apply rin_ivs_app; left. exact Hq. }
    (* [comment removed for export] *)
    assert (LBE0 : 0 <= lb_bytes (mid_errblocks M)).
    { apply lb_bytes_nonneg_s. apply Forall_forall. intros b Hb. pose proof (ah_blocks H HH _ _ _ _ HP ltac:(apply in_or_app; left; exact Hb)) as (_ & _ & E3 & _). exact E3. }
    assert (BD : dbud H (drest LB p A nA pbin Bb (mb_len R) [] [] [] []) M DLOOP_BYTES DLOOP_CNT).
    { unfold dbud, drest. cbn [app]. rewrite !lb_bytes_cons. cbn [length blk_size snd]. rewrite ?Nat2Z.inj_succ.
      pose proof BUD as BUDq. pose proof BUDC as BUCq. unfold mid_bytes in BUDq. unfold mid_cnt in BUCq. rewrite CTX in BUDq, BUCq. cbn [ctxph_bytes ctxph_cnt] in BUDq, BUCq.
      rewrite lb_bytes_app in BUDq. rewrite length_app, Nat2Z.inj_add in BUCq.
      unfold DECODE_BYTES, DECODE_CNT, DLOOP_BYTES, DLOOP_CNT, OSSL_ECH_MAX_ECHCONFIG_LEN in *. clear - BUDq BUCq NAR9 LT LBE0. split; lia. }
    (* [comment removed for export] *)
    replace (Z_to_bv 64 (mb_len R) : word) with (Z_to_bv 64 (zlength ds) : word) in VIS1 by (rewrite DSL; reflexivity).
    replace (Z_to_bv 64 AFM_DEC : word) with (Z_to_bv 64 ADF_DEC : word) in VIS1 by reflexivity.
    eapply ((RCI rp_flat) p A nA pbin Bb (mb_len R) ds R' 0 [] (fun _ => True) ff fp n fj24 tpb fj128 fk2 jz jg e5 NAR9 NBR9 MST POS BTR BTF FRESH
              (RPEc p A nA pbin Bb (mb_len R) ds R' 0 [] (fun _ => True) ff fp n fj24 tpb fj128 fk2 jz jg e5 w224 NAR9 NBR9 MST POS BTR BTF FRESH AUXV)
              (btfree_null p A nA pbin Bb (mb_len R) ds R' ff fp n fj24 tpb fj128 fk2 jz jg e5 NAR9 NBR9 MST POS FRESH) M []);
      [exact DW
      | unfold FMT_UM, lad_cm, DECODE_CUM_BYTES, DLOOP_CM in *; clear - UMB EBR; lia
      | unfold FMT_UF, lad_cf, DECODE_CUM_BYTES, DLOOP_CF in *; clear - UFB EBR; lia
      | exact BD| exact VIS1| exact KREL1| exact MP1].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem readcfg_main : as_SR H POSTc (mkCfg msF mo).
  Proof using VIS0 A0 A1 SO SE SEO STL SSH MBO MP0 MN0 MBB MBS MSH PAY DS DSL PAYL PAYL2 NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC AUX SPB BHI SPA ST CEIL LO ST0 ERR MI TP AC MCO RFS LFB ATH CHN CHB PF ALW RAE HH HX RAISE SM6 SF6 SSF8 PERM SPN AUXV NEWMB BNEW BPUSH BREAD BFALL PF9NEW PF9FREE RPE.
    exact ((RCI rp_b2b) (rp_fmt H HX RAISE SPN PF9new PF9free ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc msF m mo s LIB LB LF M x st mb lo B S R ds errv CH
                            VIS0 A0 A1 SO SE SEO STL SSH MBO MP0 MN0 MBB MBS MSH PAY DS DSL PAYL PAYL2 NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC AUX SPB BHI SPA ST CEIL LO ST0 ERR MI TP AC MCO RFS LFB ATH CHN CHB PF ALW RAE
                            rp_dec0 rp_b64)).
  Qed.
End RC.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CLOSE.
  Context {HCEIL : HeapCeil}.
  Theorem readcfg_spec : forall (H : asr),
    asan_rt_hyps_x H -> araise_stmt H -> strspn_icpt_stmt ->
    newmembuf_stmt H -> bionew_b64_stmt H -> biopush_stmt H -> bioread_b64_stmt H -> biofreeall_stmt H ->
    rp_entry_shape H ->
    forall (PF9new : ctxphase -> list (Z * list Z)) (PF9free : list (Z * list Z)),
    (forall xq, PF9new (CtxReady xq) = PF_bionew_b64 xq) -> PF9free = PF_biofreeall ->
    readcfg_stmt H PF9new PF9free.
  Proof.
    intros H HX RAISE SPN NEWMB BNEW BPUSH BREAD BFALL RPE PF9new PF9free E1 E2. unfold readcfg_stmt. intros.
    eapply (readcfg_main H HX RAISE SPN PF9new PF9free); eassumption.
  Qed.
End CLOSE.
