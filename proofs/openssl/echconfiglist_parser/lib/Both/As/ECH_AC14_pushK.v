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
  F_strspn N6_strspn ECH_AC14_b2b ECH_AC14_fmt ECH_AC14_dec.
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

  (* [comment removed for export] *)

  Local Notation KADVc := (DCT dK_adv).
  Local Notation KTXc := (DCT dK_tailX).

  (* [comment removed for export] *)
  Definition PUSH_CM : Z := 2048.
  Definition PUSH_CF : Z := 2048.
  Definition PUSH_HB : Z := 1792.   (* [comment removed for export] *)
  Definition PUSH_HC : Z := 7.

  (* [comment removed for export] *)
  Definition dK_push (cur rem : Z) (NB : list block) (S' : storerep) (um0 uf0 : Z) (ph0 : errphase) : Prop :=
    forall (Lx : list block) (M2 : libmid) (LE2 : list block) (w16 w32 w40 : word) (v192 v200 v208 v224 v232 : word) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : word)
           (tpl um uf elen : Z) (m' : mem) (s' : as_St H) (msF' : machine_state) (mo' : Model) (ee frv : Z) (E : entrep)
           (rax u0 u1 u2 a1w a2w a3w a4w a5w a6w a7w s2w s4w s5w s6w s8w s9w s11w u3 u4 u5 u6 : word),
      adwkc Lx NB S' M2 LE2 w16 w32 w40 (wz (cur + 4 + elen)) (wz ee) v192 v200 v208 v224 v232 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tpl um uf m' s' ->
      ENTRYobj (drestc Lx NB LE2) m' ee E -> ENTRY_shad m' ee E -> Permutation (blocks_ENTRY ee E) Lx ->
      5 * Z.of_nat (length (blocks_ENTRY ee E)) <= 2 * (elen + 4) -> lb_bytes (blocks_ENTRY ee E) <= ENTRY_KEPT elen ->
      19 <= elen -> 4 + elen <= rem -> Bb + 2 <= cur -> cur + rem <= Bb + zlength bs -> nent S' <= 65 -> (frv = 0 \/ frv = 1) ->
      mid_step M M2 -> errph_bytes (mid_err M2) <= errph_bytes ph0 -> errph_bytes ph0 <= errph_bytes (mid_err M) ->
      dbud H (drestc Lx NB LE2) M2 PUSH_HB PUSH_HC ->
      um + PUSH_CM <= um0 + ENTRY_CM elen + (errph_bytes ph0 - errph_bytes (mid_err M2)) ->
      uf + PUSH_CF <= uf0 + ENTRY_CF elen + (errph_bytes ph0 - errph_bytes (mid_err M2)) ->
      um + errph_bytes (mid_err M2) + PUSH_CM <= DECODE_CUM_BYTES ->
      uf + errph_bytes (mid_err M2) + lb_bytes Lx + PUSH_CF + 8192 <= DECODE_CUM_BYTES ->
      KADVc cur rem NB S' um0 uf0 ph0 -> KTXc NB S' ->
      as_VIS H s' msF' = MS (mkR rax (Z_to_bv 64 S1c) gp (Z_to_bv 64 ATP) u0 u1 u2 sp (Z_to_bv 64 S1c) (Z_to_bv 64 frv) a1w a2w a3w a4w a5w a6w a7w
                                  s2w (Z_to_bv 64 SH) s4w s5w s6w (Z_to_bv 64 (rem - 4)) s8w s9w (Z_to_bv 64 elen) s11w u3 u4 u5 u6)
                          F (ret_pc (Z_to_bv 64 ADE_R10)) fc None m' (seg_rom asegs) ->
      as_AKREL H s' (mkCfg msF' mo') -> as_MPRES H mo mo' ->
      as_SR H POSTc (mkCfg msF' mo').
End RC.
