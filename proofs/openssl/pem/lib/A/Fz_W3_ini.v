(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA RzCPS NodesA SysStep Arr FarCall.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_tac Startup_glue Th_kit Fz_T_kit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg IcptSpec.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs PLayout I_lkit I_ut RT_iface_pem D_libiface_pem Fz_kit Fz_ckit Fz_chk Fz_fkit Fz_mkit Fz_env Fz_M_malloc Fz_M_free Fz_M_secure Fz_W1_defs Fz_W1_grow Fz_W1_pploc Fz_W3_iface Fz_W3_defs Fz_W3_lems Fz_W3_aux Fz_W3_aux2 Fz_W3_aux3 Fz_W3_aux4 Fz_W3_lits Fz_W4_defs Fz_W4_init Fz_W4_update Fz_W4_final Fz_W3_inik.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Fz_W4_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Notation wz := (Z_to_bv 64) (only parsing).

Section CIni.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AFP : art_facts_pem RT GOBJ.
(* [comment removed for export] *)
Hypothesis GO_b64 : GOBJ LIT_B64TAB LIT_B64TAB_SZ.
Variable libenv : mem -> list (Z * Z) -> Z -> Prop.
Variable libenv_fp : list (Z * Z) -> Z -> Prop.
Hypothesis libenv_agree : forall m m' LBL E, libenv m LBL E -> agree_on (libenv_fp LBL) m m' -> libenv m' LBL E.
Hypothesis libenv_fp_where : forall LBL a, libenv_fp LBL a -> (in_ranges LIB_W a /\ client_static a /\ ~ cl_cell a) \/ in_live LBL a.
Variable errst_at_rest : Z -> list (Z * Z) -> mem -> Prop.
Variable errst_live : Z -> Z -> Z -> list (Z * Z) -> mem -> Prop.
Variable errst_fp : Z -> list (Z * Z) -> Z -> Prop.
Hypothesis errst_rest_agree : forall m m' E strs, errst_at_rest E strs m -> agree_on (errst_fp E strs) m m' -> errst_at_rest E strs m'.
Hypothesis errst_fp_where : forall E strs a, errst_fp E strs a -> (E <= a < E + 904) \/ in_live strs a.
Variables FZ_SITES FZ_CALLS : list (Z * Z).
Hypothesis RZTP : RZT_stmt RT libenv errst_at_rest errst_live FZ_SITES FZ_CALLS.
Hypothesis DECP : DEC_stmt RT libenv errst_at_rest errst_live FZ_SITES FZ_CALLS.

Local Notation pem_entry := (pem_entry RT).
Local Notation pem_com := (pem_com RT libenv FZ_SITES FZ_CALLS).
Local Notation pem_frame := (pem_frame RT).
Local Notation pem_ms := (pem_ms RT).

Lemma mcost_nonneg : forall n, 0 <= mcost n.
Proof. intros n. unfold mcost. destruct (n <=? 64512) eqn:E; [lia| apply Z.leb_gt in E; lia]. Qed.

Lemma rw_CB_len : forall (m : word -> option byte) a n bs, rw_cells asegs m a [CB n bs] -> length bs = n.
Proof. intros m a n bs [[[W _] _] _]. exact W. Qed.

(* [comment removed for export] *)
Lemma ectx_blur : forall (m : word -> option byte) C num ed ln fl, length ed = 80%nat -> rw_cells asegs m C (ectx_cells num ed ln fl) ->
  exists cj, length cj = Z.to_nat ECTX /\ rw_cells asegs m C [CB (Z.to_nat ECTX) cj].
Proof.
  intros m C num ed ln fl L H. exists (cells_bytes (ectx_cells num ed ln fl)). split.
  - rewrite cells_bytes_length; [reflexivity|]. cbn. tauto.
  - rewrite <- (app_nil_r (ectx_cells num ed ln fl)) in H. exact (rw_cells_blur m C _ [] H).
Qed.

(* [comment removed for export] *)
Theorem INI_proof : INI_stmt RT libenv errst_at_rest errst_live FZ_SITES FZ_CALLS.
Proof.
  intros en Σ m off crem lrem j0 lH endv x1 x2 gap hj j1 tav j2 j3 F fc eH eD xra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s11 t3 t4 t5 t6
         ctxv namev nn hBv dBv BMY bn KX KY methX methY lenX maxX lenY maxY.
  cbv zeta. intros COM REST REM LRM PFR FFC ON CAL ZC NMA NN BNL NMC HIN MBX MBY LY1 LSUM. unfold pem_at, cps. intros T c HA Hk.
  pose proof COM as (ART0 & MI & ST & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & NTL & MB & OFF & BLT & KLV & PERM & CFR & ND & LPOS
     & FRS & FRN & SP0 & CG & LIV & LR0 & CR & CR0 & CRE & CGH & CGS & CTX & UWC & F0 & F64 & FTOP & FSEG & FSH & FFS & SAVED & PRES & FLR & NDO & OUTS & FDO & MST).
  destruct (com_lists RT libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ COM) as [ELV CLV].
  assert (HLO : e_lo RT en <= e_sp1 RT en) by (clear - LOR; unfold RT_STACK, PEM_CALLEE_STACK in *; lia).
  assert (SP0' : 0 <= e_sp1 RT en) by (clear - HLO HLOS; lia). assert (SPH : e_sp1 RT en + 368 <= 2 ^ 47) by (clear - TOP PD; unfold e_sp1, USTACK_TOP in *; lia).
  assert (EU : bv_unsigned (wz (e_sp1 RT en)) = e_sp1 RT en) by (apply unsigned_lit; clear - SP0' SPH; lia).
  assert (INF : In (e_f RT en, 1%nat) (rt_frames RT Σ)) by (rewrite FRS; left; reflexivity).
  pose proof (af_frames_range RT AF Σ m _ _ ART0 INF) as (_ & FLO & _ & FR4). change (fs_size 1) with 128 in FLO, FR4.
  assert (FH : e_f RT en + 128 <= e_lo RT en) by (clear - FLO LOW; lia).
  assert (HNM : In (namev, nn) (mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(namev, nn); (ctxv, ECTX)])) by (do 2 (apply in_or_app; right); left; reflexivity).
  assert (HCX : In (ctxv, ECTX) (mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(namev, nn); (ctxv, ECTX)])) by (do 2 (apply in_or_app; right); right; left; reflexivity).
  (* [comment removed for export] *)
  pose proof ND as ND'. rewrite map_app, map_app, <- app_assoc in ND'. pose proof (nd_split _ _ ND') as (_ & ND2 & DJX). pose proof (nd_split _ _ ND2) as (NDYN & _ & _).
  pose proof (nd_split _ _ NDYN) as (_ & _ & DJY). clear ND' ND2 NDYN. cbn [map fst] in DJX, DJY.
  (* [comment removed for export] *)
  pose proof (cur_live_facts RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ (ctxv, ECTX) COM HCX ltac:(cbn; unfold ECTX; clear; lia)) as (INC & C0 & CLO & CHI & _).
  cbn [fst snd] in C0, CLO, CHI. unfold ECTX in CLO, CHI. specialize (CHI ltac:(clear; lia)).
  assert (C8' : ctxv mod 8 = 0) by (clear - CAL; Z.div_mod_to_equations; lia).
  assert (CSEG : ctxv + 92 <= 0x10000 \/ 0xbc6000 <= ctxv) by (right; clear - CHI; lia). assert (CSH : ctxv + 92 <= 0x7fff8000 \/ 0x10007fff8000 <= ctxv) by (right; exact CHI).
  assert (CR6 : C_END + 6 <= crem) by (pose proof (mcost_nonneg (lenX + 1)) as M1; pose proof (mcost_nonneg lenY) as M2; clear - REM M1 M2; lia).
  assert (CXF : e_f RT en + 128 <= ctxv \/ ctxv + 92 <= e_f RT en) by (destruct (FR4 ctxv ECTX INC) as [Q|Q]; unfold ECTX in Q; clear - Q; lia).
  (* [comment removed for export] *)
  pose proof MBY as (fl & rrw & numw & padw & nr & nw & EBI & EBM & INBI & BI16 & NDK & METH & HEAD & W1C & FLOK & TAILC & (rmw & INBB & BB16 & BBC & INBM & BM16 & INRP & RP16 & Y1 & Y2 & Y3 & INNER)).
  destruct (k_d KY) as [d|] eqn:KD; [| destruct INNER as [MX0 _]; exfalso; clear - MX0 Y2 LY1; lia].
  destruct INNER as (junk & IND & MPOS & BMC & RPC & LJ & DC). rewrite <- EBM in INBM, BM16, BMC. clear HEAD W1C TAILC BBC RPC INBB INRP.
  pose proof (af_live_range RT AF Σ m d maxY ART0 IND) as (D0 & DHI & DSEG). pose proof (afp_live_mem RT GOBJ AFP Σ m d maxY ART0 IND ltac:(clear - MPOS; lia)) as (DSH & D47).
  assert (DLO : d + maxY <= e_lo RT en) by (clear - DHI LOW; lia).
  pose proof (af_live_range RT AF Σ m BMY 32 ART0 INBM) as (B0 & BHI & _). pose proof (afp_live_hi RT GOBJ AFP Σ m BMY 32 ART0 INBM ltac:(clear; lia)) as BHH.
  assert (BH : BMY + 32 <= e_sp1 RT en) by (clear - BHI LOW HLO; lia).
  assert (BM8 : BMY mod 8 = 0) by (clear - BM16; Z.div_mod_to_equations; lia).
  assert (IND' : In (d, maxY) (mbio_ent KY maxY)) by (unfold mbio_ent; rewrite KD; apply in_or_app; right; left; reflexivity).
  assert (INBM' : In (BMY, 32) (mbio_ent KY maxY)) by (rewrite EBM; unfold mbio_ent; right; right; left; reflexivity).
  assert (NE_CD : (ctxv, ECTX) <> (d, maxY)) by (intros E; injection E as X Y; exact (DJY d (in_map fst _ _ IND') (or_intror (or_introl X)))).
  pose proof (live_ne_apart RT AF Σ m ctxv ECTX d maxY ART0 INC IND NE_CD) as CXD. unfold ECTX in CXD.
  assert (DXF : e_f RT en + 128 <= d \/ d + maxY <= e_f RT en) by exact (FR4 d maxY IND).
  assert (BXF : e_f RT en + 128 <= BMY \/ BMY + 32 <= e_f RT en) by exact (FR4 BMY 32 INBM).
  pose proof ND as NDt. rewrite map_app, map_app, <- app_assoc in NDt. pose proof (proj1 (proj2 (nd_split _ _ NDt))) as NDt2.
  pose proof (proj1 (nd_split _ _ NDt2)) as NDt3. pose proof (proj1 (proj2 (nd_split _ _ NDt3))) as NDNC0. clear NDt NDt2 NDt3.
  assert (NNC : namev <> ctxv) by (intros E; cbn [map fst] in NDNC0; apply (proj1 (proj1 (List.NoDup_cons_iff _ _) NDNC0)); left; exact (eq_sym E)).
  clear NDNC0.
  assert (YC : forall e, In e (mbio_ent KY maxY) -> In e (mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(namev, nn); (ctxv, ECTX)])) by (intros e He; apply in_or_app; right; apply in_or_app; left; exact He).
  assert (XC : forall e, In e (mbio_ent KX maxX) -> In e (mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(namev, nn); (ctxv, ECTX)])) by (intros e He; apply in_or_app; left; exact He).
  (* [comment removed for export] *)
  assert (KEEP : forall (ma mb : mem) (W XL : list (Z * Z)),
    pem_com en Σ ma off crem lrem (mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(namev, nn); (ctxv, ECTX)]) -> rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (e_sp1 RT en) W ma mb ->
    (forall x, e_sp1 RT en <= x < USTACK_TOP -> outside W x) -> (forall f k x, In (f, k) (e_frames RT en) -> f <= x < f + fs_size k - 8 -> outside W x) ->
    w_live RT Σ XL W -> (forall e, In e XL -> In e [(ctxv, ECTX); (d, maxY); (BMY, 32)]) ->
    errst_at_rest (e_E RT en) [] ma -> pem_frame en ma j0 lH (loc_F RT en) endv eH eD x1 x2 gap -> out_null RT en ma -> rw_cells asegs ma namev [CB (Z.to_nat nn) bn] ->
    mbio_rep (rt_live RT Σ) ma KX hBv methX lenX maxX 0 ->
    errst_at_rest (e_E RT en) [] mb /\ pem_frame en mb j0 lH (loc_F RT en) endv eH eD x1 x2 gap /\ out_null RT en mb /\ rw_cells asegs mb namev [CB (Z.to_nat nn) bn]
    /\ mbio_rep (rt_live RT Σ) mb KX hBv methX lenX maxX 0).
  { intros ma mb W XL COMa PR WS WFR WL HXL RESTa PFRa ONa NMCa MBXa.
    assert (NIE : ~ In (e_E RT en, 904) XL).
    { intros X. pose proof (HXL _ X) as Y. apply (CFR (e_E RT en, 904)); [| cbn [fst]; exact (in_map fst _ _ INE)].
      destruct Y as [<-|[<-|[<-|[]]]]; [exact HCX| exact (YC _ IND')| exact (YC _ INBM')]. }
    split.
    { apply (errst_rest_agree ma mb _ _ RESTa). intros a Ha. destruct (errst_fp_where _ _ _ Ha) as [R | (p & n & [] & _)].
      apply PR; [apply (acl_live _ _ _ (e_E RT en) 904); [exact (ELV _ INE)| exact R]| exact (WL (e_E RT en) 904 _ (ELV _ INE) NIE R)]. }
    split; [exact (pem_frame_keep RT en ma mb _ _ _ j0 lH (loc_F RT en) endv eH eD x1 x2 gap PFRa PR PD TOP WS)|].
    split.
    { destruct ONa as (O1 & O2 & O3 & O4). pose proof (com_out_agree RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ ma mb off crem lrem _ _ _ COMa WS WFR PR) as AGP.
      assert (G8 : forall P vv, In P [e_PN RT en; e_PH RT en; e_PD RT en; e_PLN RT en] -> rw_cells asegs ma P [C8 vv] -> rw_cells asegs mb P [C8 vv]).
      { intros P vv HPP C. eapply rw_cells_agree_nw; [exact C|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. exact (AGP P HPP). }
      split; [apply G8; [left; reflexivity| exact O1]|]. split; [apply G8; [right; left; reflexivity| exact O2]|]. split; [apply G8; [do 2 right; left; reflexivity| exact O3]|]. apply G8; [do 3 right; left; reflexivity| exact O4]. }
    split.
    { eapply rw_cells_agree_nw; [exact NMCa|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. assert (Ha' : namev <= bv_unsigned a < namev + nn) by (clear - Ha NN; lia).
      apply PR; [apply (acl_live _ _ _ namev nn); [exact (CLV _ HNM)| exact Ha']|].
      refine (com_cur_outX RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ ma off crem lrem _ _ _ COMa WL (namev, nn) _ HNM _ Ha').
      intros X. pose proof (HXL _ X) as Y. destruct Y as [Y|[Y|[Y|[]]]].
      - apply NNC. injection Y as E1 E2. exact (eq_sym E1).
      - injection Y as E1 E2. exact (DJY d (in_map fst _ _ IND') (or_introl (eq_sym E1))).
      - injection Y as E1 E2. exact (DJY BMY (in_map fst _ _ INBM') (or_introl (eq_sym E1))). }
    eapply (mbio_rep_keep (rt_live RT Σ)); [exact MBXa| exact PR| intros e He; split; apply CLV; apply in_or_app; left; exact He|].
    intros e x He Hx. refine (com_cur_outX RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ ma off crem lrem _ _ _ COMa WL e x ltac:(apply in_or_app; left; exact He) _ Hx).
    intros X. pose proof (HXL _ X) as Y. pose proof (in_map fst _ _ He) as HeX.
    destruct Y as [<-|[<-|[<-|[]]]]; cbn [fst] in HeX.
    - exact (DJX ctxv HeX ltac:(apply in_or_app; left; apply in_or_app; right; right; left; reflexivity)).
    - exact (DJX d HeX ltac:(apply in_or_app; left; apply in_or_app; left; exact (in_map fst _ _ IND'))).
    - exact (DJX BMY HeX ltac:(apply in_or_app; left; apply in_or_app; left; exact (in_map fst _ _ INBM'))). }
  assert (NE_BD : (BMY, 32) <> (d, maxY)).
  { intros E. injection E as E1 E2. pose proof NDK as NDK'. unfold mbio_blocks in NDK'. rewrite KD, <- EBM in NDK'. cbn [app] in NDK'.
    pose proof (proj1 (List.NoDup_cons_iff _ _) (proj2 (proj1 (List.NoDup_cons_iff _ _) (proj2 (proj1 (List.NoDup_cons_iff _ _) NDK'))))) as N3. apply N3. right; left. exact (eq_sym E1). }
  assert (NE_CB : (ctxv, ECTX) <> (BMY, 32)) by (intros E; injection E as E1 E2; exact (DJY BMY (in_map fst _ _ INBM') (or_intror (or_introl E1)))).
  pose proof (live_ne_apart RT AF Σ m d maxY BMY 32 ART0 IND INBM (fun E => NE_BD (eq_sym E))) as DXB.
  assert (EN : Z.of_nat (Z.to_nat maxY) = maxY) by (clear - MPOS; lia).
  (* [comment removed for export] *)
  assert (FW : forall XL lo hi, (forall e, In e XL -> (In e (mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(namev, nn); (ctxv, ECTX)]) /\ 0 < snd e) \/ In e (mbio_ent (e_K RT en) (e_bmax RT en))) -> e_f RT en <= lo -> hi <= e_f RT en + 120 ->
            (forall x, e_sp1 RT en <= x < USTACK_TOP -> outside (map rng XL ++ [(lo, hi)]) x)
         /\ (forall f k x, In (f, k) (e_frames RT en) -> f <= x < f + fs_size k - 8 -> outside (map rng XL ++ [(lo, hi)]) x)
         /\ w_live RT Σ XL (map rng XL ++ [(lo, hi)]) /\ (forall x, e_f RT en <= x < e_f RT en + 120 -> ~ (lo <= x < hi) -> outside (map rng XL ++ [(lo, hi)]) x)).
  { intros XL lo hi HXL L1 L2. pose proof (com_WB_ok RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ XL COM HXL) as (KWS & KWFR & KWFF & KWSH & KWL & KWP).
    split. { intros x Hx. apply outside_app_intro; [exact (KWS x Hx)|]. cbn. split; [clear - Hx L1 L2 FH HLO; lia| exact I]. }
    split. { intros f' k x Hin Hx. apply outside_app_intro; [exact (KWFR f' k x Hin Hx)|]. cbn. split; [| exact I]. intros R.
             apply (proj1 (proj2 (seg_byte_facts RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ (lo, hi) x COM ltac:(right; right; cbn; clear - L1 L2; lia) ltac:(cbn; exact R)))).
             right; right; right; left. exists f', k. split; [exact Hin| exact Hx]. }
    split. { intros p n x Hin NIN Hx. apply outside_app_intro; [exact (KWL p n x Hin NIN Hx)|]. cbn. split; [| exact I]. destruct (FR4 p n Hin) as [Q|Q]; clear - Q Hx L1 L2; lia. }
    intros x Hx NX. apply outside_app_intro; [exact (KWFF x Hx)|]. cbn. split; [exact NX| exact I]. }
  assert (HXL1 : forall e, In e [(ctxv, ECTX)] -> (In e (mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(namev, nn); (ctxv, ECTX)]) /\ 0 < snd e) \/ In e (mbio_ent (e_K RT en) (e_bmax RT en))) by (intros e [<-|[]]; left; split; [exact HCX| cbn; unfold ECTX; clear; lia]).
  assert (HXL2 : forall e, In e [(ctxv, ECTX); (d, maxY)] -> (In e (mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(namev, nn); (ctxv, ECTX)]) /\ 0 < snd e) \/ In e (mbio_ent (e_K RT en) (e_bmax RT en))).
  { intros e [<-|[<-|[]]]; left; split; [exact HCX| cbn; unfold ECTX; clear; lia| exact (YC _ IND')| cbn; exact MPOS]. }
  assert (HXL4 : forall e, In e [(BMY, 32)] -> (In e (mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(namev, nn); (ctxv, ECTX)]) /\ 0 < snd e) \/ In e (mbio_ent (e_K RT en) (e_bmax RT en))) by (intros e [<-|[]]; left; split; [exact (YC _ INBM')| cbn; clear; lia]).
  (* [comment removed for export] *)
  assert (CTX0 : rw_cells asegs m ctxv (ectx_cells (wz 0) (repeat (Z_to_bv 8 0) 80) (wz 0) (wz 0))).
  { eapply rw_cells_recast; [exact ZC| cbn; repeat split; reflexivity| vm_compute; reflexivity]. }
  destruct (af_acc_live RT AF Σ m ctxv ECTX ART0 INC) as [_ ACCC].
  pose proof (af_client_consts RT AF Σ m ART0) as (_ & SHBC & _ & _ & UT).
  assert (STu : stk asegs m (e_lo RT en) (bv_unsigned (wz (e_sp1 RT en)))) by (rewrite EU; exact ST).
  assert (LO176 : e_lo RT en <= bv_unsigned (wz (e_sp1 RT en)) - 192) by (rewrite EU; clear - LOR; unfold RT_STACK, PEM_CALLEE_STACK in *; lia).
  assert (SPu : bv_unsigned (wz (e_sp1 RT en)) <= 2 ^ 47) by (rewrite EU; clear - SPH; lia).
  (* [comment removed for export] *)
  pose proof (in_c0_walk xra (e_sp1 RT en) (e_gp RT en) t0 t1 t2 (e_sp RT en) a1 a2 a3 a4 a5 a6 a7 s2 (wz dBv) s4 s5 s6 (wz hBv)
                (wz (shad (e_f RT en))) (wz SHB) (wz namev) s11 t3 t4 t5 t6 F fc m ctxv MI) as W.
  cl_lift W HA c1 Hc1. destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (-> & _) & Hc1'). clear Hc1 HA.
  pose proof (W4_decode_init_proof (wz SITE_in_dinit) (wz (e_sp1 RT en)) (e_gp RT en) (wz TP_A) t0 t1 t2 (e_sp RT en) (wz (e_sp1 RT en)) (wz ctxv) a1 a2 a3 a4 a5 a6 a7
                s2 (wz dBv) s4 s5 s6 (wz hBv) (wz (shad (e_f RT en))) (wz SHB) (wz namev) (wz ctxv) t3 t4 t5 t6 F fc m
                ctxv (e_lo RT en) (wz 0) (wz 0) (wz 0) (repeat (Z_to_bv 8 0) 80) eq_refl C0 C8' CLO ltac:(right; clear - CHI; lia) ltac:(right; exact CHI) CTX0 eq_refl ACCC UT SHBC
                STu HLOS ltac:(clear - LO176; lia) SPu MI) as W.
  cl_lift W Hc1' c2 Hc2. destruct (ASTA_unpack RT Σ _ _ c2 Hc2) as (ms2 & (g0 & g1 & g2 & g3 & g4 & m1 & -> & MU1 & WM1 & MI1 & ST1 & CTX1) & Hc2'). clear Hc2 Hc1'.
  rewrite EU in MU1, ST1. rewrite (ret_pc_even SITE_in_dinit ltac:(unfold SITE_in_dinit; clear; lia) eq_refl) in Hc2'.
  (* [comment removed for export] *)
  assert (COM1 : pem_com en Σ m1 off crem lrem (mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(namev, nn); (ctxv, ECTX)])).
  { eapply (com_leaf RT AF GOBJ AFP libenv libenv_fp libenv_agree libenv_fp_where FZ_SITES FZ_CALLS en Σ m m1); [exact COM| exact MU1| exact WM1| exact MI1| exact ST1|].
    intros iv [<-|[<-|[<-|[]]]]; cbn [fst snd].
    - right. unfold PEM_CALLEE_STACK. clear; lia.
    - left. right; left. exists (ctxv, ECTX). split; [exact HCX|]. cbn [fst snd]. unfold ECTX. clear; lia.
    - left. right; left. exists (ctxv, ECTX). split; [exact HCX|]. cbn [fst snd]. unfold ECTX. clear; lia. }
  assert (PR1 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (e_sp1 RT en) (map rng [(ctxv, ECTX)] ++ [(e_f RT en + 32, e_f RT en + 32)]) m m1).
  { intros a Ha Ho. apply MU1. cbn [map rng fst snd app outside] in Ho. destruct Ho as (Ho & _ & _). cbn [outside].
    destruct (cl_split RT AF Σ m (e_sp1 RT en) 16 (bv_unsigned a) ART0 ltac:(clear - LOW LOR; unfold RT_STACK, PEM_CALLEE_STACK in *; lia) ltac:(clear; lia) Ha) as [Q|Q];
      (refine (conj _ (conj _ (conj _ I))); [clear - Q; lia| unfold ECTX in Ho; clear - Ho; lia| unfold ECTX in Ho; clear - Ho; lia]). }
  destruct (FW [(ctxv, ECTX)] (e_f RT en + 32) (e_f RT en + 32) HXL1 ltac:(clear; lia) ltac:(clear; lia)) as (WS1 & WFR1 & WL1 & WFF1).
  destruct (KEEP m m1 _ _ COM PR1 WS1 WFR1 WL1 ltac:(intros e [<-|[]]; left; reflexivity) REST PFR ON NMC MBX) as (REST1 & PFR1 & ON1 & NMC1 & MBX1).
  pose proof (ff_keep m m1 (e_f RT en) _ _ _ _ hj (wz lenY) j1 tav j2 (wz BMY) j3 FFC PR1 INF ltac:(intros x Hx; apply (WFF1 x Hx); clear; lia)) as FFC1.
  assert (YOUT1 : forall p n (a : word), In (p, n) (mbio_ent KY maxY) -> p <= bv_unsigned a < p + n -> m1 a = m a).
  { intros p n a Hin Ha. apply PR1; [exact (acl_live _ _ _ p n _ (CLV _ (YC _ Hin)) Ha)|]. apply (WL1 p n _ (CLV _ (YC _ Hin))); [| exact Ha].
    intros [E|[]]. injection E as E1 E2. exact (DJY ctxv ltac:(rewrite E1; exact (in_map fst _ _ Hin)) (or_intror (or_introl eq_refl))). }
  assert (MBY1 : mbio_repx (rt_live RT Σ) m1 KY dBv BMY (wz lenY) methY lenY maxY 0).
  { eapply (mbio_repx_keep (rt_live RT Σ)); [exact MBY| exact PR1| intros e He; split; apply CLV; exact (YC _ He)|].
    intros [p n] x He Hx. apply (WL1 p n x (CLV _ (YC _ He))); [| exact Hx].
    intros [E|[]]. injection E as E1 E2. exact (DJY ctxv ltac:(rewrite E1; exact (in_map fst _ _ He)) (or_intror (or_introl eq_refl))). }
  assert (BMC1 : rw_cells asegs m1 BMY [C8 (wz lenY); C8 (wz d); C8 (wz maxY); C8 (wz (msec methY))]).
  { eapply rw_cells_agree_nw; [exact BMC|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. exact (YOUT1 BMY 32 a INBM' ltac:(clear - Ha; lia)). }
  assert (DC1 : rw_cells asegs m1 d [CB (Z.to_nat maxY) junk]).
  { eapply rw_cells_agree_nw; [exact DC|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. exact (YOUT1 d maxY a IND' ltac:(clear - Ha MPOS; lia)). }
  clear COM REST PFR ON NMC MBX MBY FFC BMC DC CTX0 ACCC SHBC UT STu MU1 WM1 MI PR1 WS1 WFR1 WL1 WFF1 YOUT1.
  (* [comment removed for export] *)
  pose proof COM1 as (ART1 & _ & ST1' & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FFS1 & _).
  pose proof PFR1 as (_ & _ & _ & FRF1 & _). unfold loc_F in FRF1.
  destruct (af_acc_live RT AF Σ m1 BMY 32 ART1 INBM) as [_ ACCB1]. destruct (af_acc_live RT AF Σ m1 ctxv ECTX ART1 INC) as [_ ACCC1].
  destruct (af_acc_live RT AF Σ m1 d maxY ART1 IND) as [_ DACC1]. rewrite <- EN in DACC1.
  pose proof (af_client_consts RT AF Σ m1 ART1) as (_ & SHBC1 & _ & _ & UT1).
  pose proof (afp_acc_global RT GOBJ AFP Σ m1 LIT_B64TAB LIT_B64TAB_SZ LIT_B64TAB LIT_B64TAB_SZ ART1 GO_b64 ltac:(clear; lia) ltac:(clear; lia)) as ACCT1.
  assert (ST1u : stk asegs m1 (e_lo RT en) (bv_unsigned (wz (e_sp1 RT en)))) by (rewrite EU; exact ST1').
  pose proof (in_c1_walk (e_sp1 RT en) (e_gp RT en) t0 t1 t2 (e_sp RT en) g0 g1 g2 g3 g4 a5 a6 a7 s2 (wz dBv) s4 s5 s6 (wz hBv)
                (wz (shad (e_f RT en))) (wz namev) t3 t4 t5 t6 F fc m1 (e_f RT en) BMY ctxv d lenY hj j1 tav j2 j3 (wz lenY) (wz maxY) (wz (msec methY)) (wz (e_f RT en + 48))
                SP0' SPH F0 ltac:(clear - FH HLO; lia) MI1 FRF1 FFC1 BMC1 ACCB1 BM8 B0 BH ltac:(clear - Y1 Y2 Y3; lia)) as W.
  cl_lift W Hc2' c3 Hc3. destruct (ASTA_unpack RT Σ _ _ c3 Hc3) as (ms3 & (-> & _) & Hc3'). clear Hc3 Hc2'.
  pose proof (W4_decode_update_proof (wz SITE_in_dupd) (wz (e_sp1 RT en)) (e_gp RT en) (wz TP_A) t0 t1 t2 (e_sp RT en) (wz (e_sp1 RT en))
                (wz ctxv) (wz d) (wz (e_f RT en + 32)) (wz d) (wz lenY) a5 a6 a7
                s2 (wz dBv) s4 s5 s6 (wz hBv) (wz (shad (e_f RT en))) (wz SHB) (wz namev) (wz ctxv) t3 t4 t5 t6 F fc m1
                ctxv d (e_f RT en + 32) (Z.to_nat maxY) lenY 0 (wz 0) (wz lenY) (repeat (Z_to_bv 8 0) 80) junk (e_lo RT en)
                eq_refl eq_refl eq_refl eq_refl eq_refl CTX1 eq_refl ltac:(clear; lia) C0 C8' CLO ACCC1 ltac:(right; clear - CHI; lia) ltac:(right; exact CHI)
                DC1 ltac:(rewrite EN; clear - Y1 Y2; lia) ltac:(clear - Y2 Y3; lia) ltac:(rewrite EN; clear - Y1 Y2; lia)
                D0 ltac:(rewrite EN; exact DLO) DACC1 ltac:(rewrite EN; clear - DSEG; unfold SEGTOP_A in *; lia) ltac:(rewrite EN; exact DSH)
                (ff_cell32 m1 _ hj (wz lenY) j1 tav j2 (wz BMY) j3 FFC1) ltac:(clear - F0; lia) ltac:(clear - F64; Z.div_mod_to_equations; lia) (proj1 (ff_acc4 m1 (e_f RT en) _ F64 F0 FFS1))
                ltac:(left; clear - FH; lia) ltac:(clear - FH HLO SPH; lia) ltac:(right; clear - FSEG; unfold SEGTOP_A in *; lia) ltac:(clear - FSH; lia)
                ltac:(rewrite EN; exact CXD) ltac:(clear - CXF; lia) ltac:(rewrite EN; clear - DXF; lia) ACCT1 UT1 SHBC1 ST1u HLOS LO176 SPu MI1) as W.
  cl_lift W Hc3' c4 Hc4.
  destruct (ASTA_unpack RT Σ _ _ c4 Hc4) as (ms4 & (rv & ret & num' & w0 & w1 & w2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & w3 & w4 & w5 & w6 & ed' & bs' & m2 & -> & MU2 & WM2 & MI2 & (RV & RET0 & NUM' & ROOM) & ST2 & CTX2 & LED' & DC2 & OLC2) & Hc4').
  clear Hc4 Hc3'. rewrite EU in MU2, ST2. rewrite (ret_pc_even SITE_in_dupd ltac:(unfold SITE_in_dupd; clear; lia) eq_refl) in Hc4'.
  (* [comment removed for export] *)
  assert (COM2 : pem_com en Σ m2 off crem lrem (mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(namev, nn); (ctxv, ECTX)])).
  { eapply (com_leaf RT AF GOBJ AFP libenv libenv_fp libenv_agree libenv_fp_where FZ_SITES FZ_CALLS en Σ m1 m2); [exact COM1| exact MU2| exact WM2| exact MI2| exact ST2|].
    intros iv [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd].
    - right. unfold PEM_CALLEE_STACK. clear; lia.
    - left. right; left. exists (ctxv, ECTX). split; [exact HCX|]. cbn [fst snd]. unfold ECTX. clear; lia.
    - left. right; left. exists (d, maxY). split; [exact (YC _ IND')|]. cbn [fst snd]. rewrite EN. clear - MPOS; lia.
    - left. right; right. cbn [fst snd]. clear; lia. }
  assert (PR2 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (e_sp1 RT en) (map rng [(ctxv, ECTX); (d, maxY)] ++ [(e_f RT en + 32, e_f RT en + 36)]) m1 m2).
  { intros a Ha Ho. apply MU2. cbn [map rng fst snd app outside] in Ho. destruct Ho as (Ho1 & Ho2 & Ho3 & _). cbn [outside]. rewrite EN.
    destruct (cl_split RT AF Σ m (e_sp1 RT en) 192 (bv_unsigned a) ART0 ltac:(clear - LOW LOR; unfold RT_STACK, PEM_CALLEE_STACK in *; lia) ltac:(clear; lia) Ha) as [Q|Q];
      (refine (conj _ (conj _ (conj _ (conj _ I)))); [clear - Q; lia| unfold ECTX in Ho1; clear - Ho1; lia| clear - Ho2; lia| clear - Ho3; lia]). }
  destruct (FW [(ctxv, ECTX); (d, maxY)] (e_f RT en + 32) (e_f RT en + 36) HXL2 ltac:(clear; lia) ltac:(clear; lia)) as (WS2 & WFR2 & WL2 & WFF2).
  destruct (KEEP m1 m2 _ _ COM1 PR2 WS2 WFR2 WL2 ltac:(intros e [<-|[<-|[]]]; [left| right; left]; reflexivity) REST1 PFR1 ON1 NMC1 MBX1) as (REST2 & PFR2 & ON2 & NMC2 & MBX2).
  assert (FFC2 : rw_cells asegs m2 (e_f RT en) (ff_cells hj (wz ret) j1 tav j2 (wz BMY) j3)).
  { apply (ff_upd32 m1 m2 (e_f RT en) hj (wz lenY) (wz ret) j1 tav j2 (wz BMY) j3 FFC1); [| exact OLC2]. intros a H1 H2.
    apply PR2; [apply (acl_frame _ _ _ (e_f RT en) 1%nat); [exact INF| change (fs_size 1) with 128; clear - H1; lia]| exact (WFF2 _ H1 H2)]. }
  assert (YOUT2 : forall p n (a : word), In (p, n) (mbio_ent KY maxY) -> (p, n) <> (d, maxY) -> p <= bv_unsigned a < p + n -> m2 a = m1 a).
  { intros p n a Hin NE Ha. apply PR2; [exact (acl_live _ _ _ p n _ (CLV _ (YC _ Hin)) Ha)|]. apply (WL2 p n _ (CLV _ (YC _ Hin))); [| exact Ha].
    intros [E|[E|[]]]; [| exact (NE (eq_sym E))]. injection E as E1 E2. exact (DJY ctxv ltac:(rewrite E1; exact (in_map fst _ _ Hin)) (or_intror (or_introl eq_refl))). }
  pose proof (rw_CB_len m2 _ _ _ DC2) as LBS2.
  assert (MBY2 : mbio_repx (rt_live RT Σ) m2 KY dBv BMY (wz lenY) methY lenY maxY 0).
  { apply (mbio_repx_upd RT AF Σ m1 m2 KY dBv BMY (wz lenY) (wz lenY) methY lenY maxY 0 d bs' ART1 MBY1 KD);
      [| | exact LBS2| exact DC2].
    - intros [p n] a He NE Hp _. exact (YOUT2 p n a He NE Hp).
    - eapply rw_cells_agree_nw; [exact (rw_cells_head m1 _ _ _ BMC1)|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. exact (YOUT2 BMY 32 a INBM' NE_BD ltac:(clear - Ha; lia)). }
  assert (BMC2 : rw_cells asegs m2 BMY [C8 (wz lenY); C8 (wz d); C8 (wz maxY); C8 (wz (msec methY))]).
  { eapply rw_cells_agree_nw; [exact BMC1|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. exact (YOUT2 BMY 32 a INBM' NE_BD ltac:(clear - Ha; lia)). }
  clear COM1 REST1 PFR1 ON1 NMC1 MBX1 MBY1 FFC1 BMC1 DC1 CTX1 ACCB1 ACCC1 DACC1 SHBC1 UT1 ACCT1 ST1u ST1' FFS1 FRF1 PR2 WS2 WFR2 WL2 WFF2 YOUT2 ART1.
  assert (RET : 0 <= ret /\ 4 * ret + 3 * num' <= 3 * lenY) by (clear - RET0 ROOM; lia).
  (* [comment removed for export] *)
  assert (RZ : forall (mq : mem) (ra0 q0 q1 q2 b1 b2 b3 b4 b5 b6 b7 q3 q4 q5 q6 lv tv bmw : word) (numq : Z) (edq : list byte) cq,
    pem_com en Σ mq off crem lrem (mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(namev, nn); (ctxv, ECTX)]) -> errst_at_rest (e_E RT en) [] mq -> pem_frame en mq j0 lH (loc_F RT en) endv eH eD x1 x2 gap ->
    rw_cells asegs mq (e_f RT en) (ff_cells hj lv j1 tv j2 bmw j3) -> out_null RT en mq -> length edq = 80%nat -> rw_cells asegs mq ctxv (ectx_cells (wz numq) edq (wz 0) (wz 0)) ->
    rw_cells asegs mq namev [CB (Z.to_nat nn) bn] -> mbio_rep (rt_live RT Σ) mq KX hBv methX lenX maxX 0 -> mbio_repx (rt_live RT Σ) mq KY dBv BMY (wz lenY) methY lenY maxY 0 ->
    ASTA RT Σ (e_PMc RT en) (eq (pem_ms en J_RZT mq F fc ra0 q0 q1 q2 (wz (-1)) b1 b2 b3 b4 b5 b6 b7 s2 (wz dBv) s4 s5 s6 (wz hBv) (wz namev) (wz ctxv) q3 q4 q5 q6)) cq ->
    realizes asegs cq T).
  { intros mq ra0 q0 q1 q2 b1 b2 b3 b4 b5 b6 b7 q3 q4 q5 q6 lv tv bmw numq edq cq COMq RESTq PFRq FFCq ONq LEDq CTXq NMCq MBXq MBYq Hcq.
    destruct MBXq as [BMX MBXq']. destruct (ectx_blur mq ctxv (wz numq) edq (wz 0) (wz 0) LEDq CTXq) as (cj & LCJ & CTXb).
    exact (RZTP en Σ mq off crem lrem j0 lH endv x1 x2 gap hj lv j1 tv j2 bmw j3 cj F fc eH eD ra0 q0 q1 q2 (wz (-1)) b1 b2 b3 b4 b5 b6 b7 s2 s4 s5 s6 q3 q4 q5 q6
             ctxv namev nn hBv dBv bn KX KY BMX BMY methX methY lenX maxX 0 lenY maxY 0 (wz lenX) (wz lenY) COMq RESTq CR6 ltac:(clear - LRM; lia) PFRq FFCq ONq CAL LCJ CTXb NMA NN BNL NMCq HIN MBXq' MBYq T cq Hcq Hk). }
  destruct (Z_lt_le_dec rv 0) as [RN | RP].
  - (* [comment removed for export] *)
    assert (ERV : rv = -1) by (clear - RN RV; lia). rewrite ERV in Hc4'.
    pose proof (in_c2r_walk (wz SITE_in_dupd) (e_sp1 RT en) (e_gp RT en) w0 w1 w2 (e_sp RT en) e1 e2 e3 e4 e5 e6 e7 s2 (wz dBv) s4 s5 s6 (wz hBv)
                  (wz (shad (e_f RT en))) (wz SHB) (wz namev) (wz ctxv) w3 w4 w5 w6 F fc m2 MI2) as W.
    cl_lift W Hc4' c5 Hc5. destruct (ASTA_unpack RT Σ _ _ c5 Hc5) as (ms5 & (-> & _) & Hc5'). clear Hc5 Hc4'.
    exact (RZ m2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ COM2 REST2 PFR2 FFC2 ON2 LED' CTX2 NMC2 MBX2 MBY2 Hc5').
  - (* [comment removed for export] *)
    pose proof COM2 as (ART2 & _ & ST2' & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FFS2 & _).
    pose proof PFR2 as (_ & _ & _ & FRF2 & _). unfold loc_F in FRF2.
    destruct (af_acc_live RT AF Σ m2 BMY 32 ART2 INBM) as [_ ACCB2]. destruct (af_acc_live RT AF Σ m2 ctxv ECTX ART2 INC) as [_ ACCC2].
    destruct (af_acc_live RT AF Σ m2 d maxY ART2 IND) as [_ DACC2].
    pose proof (af_client_consts RT AF Σ m2 ART2) as (_ & SHBC2 & _ & _ & UT2).
    pose proof (afp_acc_global RT GOBJ AFP Σ m2 LIT_B64TAB LIT_B64TAB_SZ LIT_B64TAB LIT_B64TAB_SZ ART2 GO_b64 ltac:(clear; lia) ltac:(clear; lia)) as ACCT2.
    assert (ST2u : stk asegs m2 (e_lo RT en) (bv_unsigned (wz (e_sp1 RT en)))) by (rewrite EU; exact ST2').
    assert (RETB : 0 <= ret <= lenY /\ ret < 2 ^ 31) by (clear - RET NUM' Y2 Y3; lia).
    pose proof (in_c2_walk (e_sp1 RT en) (e_gp RT en) w0 w1 w2 (e_sp RT en) e1 e2 e3 e4 e5 e6 e7 s2 (wz dBv) s4 s5 s6 (wz hBv)
                  (wz (shad (e_f RT en))) (wz namev) w3 w4 w5 w6 F fc m2 (e_f RT en) BMY ctxv d ret rv hj j1 tav j2 j3 (wz lenY) (wz maxY) (wz (msec methY))
                  SP0' SPH F0 ltac:(clear - FH HLO; lia) ltac:(clear - RP RV; lia) MI2 FRF2 FFC2 BMC2 ACCB2 BM8 B0 BH ltac:(clear - RETB; lia) D0 ltac:(clear - RETB DLO HLO SPH Y2; lia)) as W.
    cl_lift W Hc4' c5 Hc5. destruct (ASTA_unpack RT Σ _ _ c5 Hc5) as (ms5 & (-> & _) & Hc5'). clear Hc5 Hc4'.
    (* [comment removed for export] *)
    pose proof (rw_cells_split_CB asegs m2 d [] (Z.to_nat maxY) bs' [] [Z.to_nat ret; (Z.to_nat maxY - Z.to_nat ret)%nat] DC2 ltac:(cbn; clear - RETB Y2; lia)) as DS2.
    cbn [mk_CB_cells app] in DS2.
    pose proof (proj1 (rw_cells_app m2 _ [CB (Z.to_nat ret) (firstn (Z.to_nat ret) bs')] _) DS2) as [DCa2 TC2]. clear DS2.
    cbn [cells_size csize Nat.add] in TC2. rewrite Nat.add_0_r, Z2Nat.id in TC2 by (clear - RETB; lia).
    assert (EK : Z.of_nat (Z.to_nat maxY - Z.to_nat ret)%nat = maxY - ret) by (clear - RETB Y2; lia).
    assert (Q14 : 3 * (num' / 4) <= Z.of_nat (Z.to_nat maxY - Z.to_nat ret)%nat) by (rewrite EK; clear - RET NUM' Y2; Z.div_mod_to_equations; lia).
    assert (DACC2' : acc asegs m2 (d + ret) (Z.of_nat (Z.to_nat maxY - Z.to_nat ret)%nat)) by (rewrite EK; eapply acc_sub; [exact DACC2| clear - RETB; lia| clear - RETB; lia]).
    pose proof (W4_decode_final_proof (wz SITE_in_dfin) (wz (e_sp1 RT en)) (e_gp RT en) (wz TP_A) w0 w1 w2 (e_sp RT en) (wz (e_sp1 RT en))
                  (wz ctxv) (wz (d + ret)) (wz (e_f RT en + 48)) e3 e4 e5 e6 e7
                  s2 (wz dBv) s4 s5 s6 (wz hBv) (wz (shad (e_f RT en))) (wz SHB) (wz namev) (wz ctxv) w3 w4 w5 w6 F fc m2
                  ctxv (d + ret) (e_f RT en + 48) (e_lo RT en) num' (Z.to_nat maxY - Z.to_nat ret)%nat (wz 0) tav ed' (firstn (Z.to_nat maxY - Z.to_nat ret)%nat (skipn (Z.to_nat ret) bs'))
                  eq_refl eq_refl eq_refl CTX2 LED' NUM' C0 C8' CLO ACCC2 CSEG CSH TC2 ltac:(clear - D0 RETB; lia) Q14 ltac:(rewrite EK; clear - DLO RETB; lia) DACC2'
                  ltac:(rewrite EK; clear - DSEG RETB; unfold SEGTOP_A in *; lia) ltac:(rewrite EK; clear - DSH RETB; lia)
                  (ff_cell48 m2 _ hj (wz ret) j1 tav j2 (wz BMY) j3 FFC2) ltac:(clear - F0; lia) ltac:(clear - F64; Z.div_mod_to_equations; lia) (proj2 (ff_acc4 m2 (e_f RT en) _ F64 F0 FFS2))
                  ltac:(left; clear - FH; lia) ltac:(clear - FH HLO SPH; lia) ltac:(right; clear - FSEG; unfold SEGTOP_A in *; lia) ltac:(clear - FSH; lia)
                  ltac:(rewrite EK; clear - CXD RETB; lia) ltac:(clear - CXF; lia) ltac:(rewrite EK; clear - DXF RETB; lia)
                  ACCT2 UT2 SHBC2 ST2u HLOS ltac:(clear - LO176; lia) SPu MI2) as W.
    cl_lift W Hc5' c6 Hc6.
    destruct (ASTA_unpack RT Σ _ _ c6 Hc6) as (ms6 & (rv2 & dl & num2 & v0 & v1 & v2 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & v3 & v4 & v5 & v6 & bs2 & m3 & -> & MU3 & WM3 & MI3 & RVD & ST3 & CTX3 & TC3 & OLC3) & Hc6').
    clear Hc6 Hc5'. rewrite EU in MU3, ST3. rewrite (ret_pc_even SITE_in_dfin ltac:(unfold SITE_in_dfin; clear; lia) eq_refl) in Hc6'.
    (* [comment removed for export] *)
    assert (COM3 : pem_com en Σ m3 off crem lrem (mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(namev, nn); (ctxv, ECTX)])).
    { eapply (com_leaf RT AF GOBJ AFP libenv libenv_fp libenv_agree libenv_fp_where FZ_SITES FZ_CALLS en Σ m2 m3); [exact COM2| exact MU3| exact WM3| exact MI3| exact ST3|].
      intros iv [<-|[<-|[<-|[<-|[]]]]].
      - right. cbn [fst snd]. unfold PEM_CALLEE_STACK. clear; lia.
      - left. right; left. exists (ctxv, ECTX). split; [exact HCX|]. cbn [fst snd]. unfold ECTX. clear; lia.
      - left. right; left. exists (d, maxY). split; [exact (YC _ IND')|]. cbn [fst snd]. rewrite EK in Q14. clear - MPOS Q14 RETB; lia.
      - left. right; right. cbn [fst snd]. clear; lia. }
    assert (PR3 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (e_sp1 RT en) (map rng [(ctxv, ECTX); (d, maxY)] ++ [(e_f RT en + 48, e_f RT en + 52)]) m2 m3).
    { intros a Ha Ho. apply MU3. cbn [map rng fst snd app outside] in Ho. destruct Ho as (Ho1 & Ho2 & Ho3 & _). cbn [outside].
      destruct (cl_split RT AF Σ m (e_sp1 RT en) 128 (bv_unsigned a) ART0 ltac:(clear - LOW LOR; unfold RT_STACK, PEM_CALLEE_STACK in *; lia) ltac:(clear; lia) Ha) as [Q|Q];
        (refine (conj _ (conj _ (conj _ (conj _ I)))); [clear - Q; lia| unfold ECTX in Ho1; clear - Ho1; lia| rewrite EK in Q14; clear - Ho2 Q14 RETB; lia| clear - Ho3; lia]). }
    destruct (FW [(ctxv, ECTX); (d, maxY)] (e_f RT en + 48) (e_f RT en + 52) HXL2 ltac:(clear; lia) ltac:(clear; lia)) as (WS3 & WFR3 & WL3 & WFF3).
    destruct (KEEP m2 m3 _ _ COM2 PR3 WS3 WFR3 WL3 ltac:(intros e [<-|[<-|[]]]; [left| right; left]; reflexivity) REST2 PFR2 ON2 NMC2 MBX2) as (REST3 & PFR3 & ON3 & NMC3 & MBX3).
    assert (FFC3 : rw_cells asegs m3 (e_f RT en) (ff_cells hj (wz ret) j1 (wz dl) j2 (wz BMY) j3)).
    { apply (ff_upd48 m2 m3 (e_f RT en) hj (wz ret) j1 tav (wz dl) j2 (wz BMY) j3 FFC2); [| exact OLC3]. intros a H1 H2.
      apply PR3; [apply (acl_frame _ _ _ (e_f RT en) 1%nat); [exact INF| change (fs_size 1) with 128; clear - H1; lia]| exact (WFF3 _ H1 H2)]. }
    assert (YOUT3 : forall p n (a : word), In (p, n) (mbio_ent KY maxY) -> (p, n) <> (d, maxY) -> p <= bv_unsigned a < p + n -> m3 a = m2 a).
    { intros p n a Hin NE Ha. apply PR3; [exact (acl_live _ _ _ p n _ (CLV _ (YC _ Hin)) Ha)|]. apply (WL3 p n _ (CLV _ (YC _ Hin))); [| exact Ha].
      intros [E|[E|[]]]; [| exact (NE (eq_sym E))]. injection E as E1 E2. exact (DJY ctxv ltac:(rewrite E1; exact (in_map fst _ _ Hin)) (or_intror (or_introl eq_refl))). }
    pose proof COM3 as (ART3 & _).
    (* [comment removed for export] *)
    assert (DCa3 : rw_cells asegs m3 d [CB (Z.to_nat ret) (firstn (Z.to_nat ret) bs')]).
    { eapply rw_cells_agree_nw; [exact DCa2|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply MU3. cbn. rewrite EK in Q14.
      refine (conj _ (conj _ (conj _ (conj _ I)))); [clear - Ha DLO LOR RETB Y2; unfold RT_STACK, PEM_CALLEE_STACK in *; lia| clear - Ha CXD RETB Y2; lia| clear - Ha RETB; lia| clear - Ha DXF RETB Y2; lia]. }
    pose proof (rw_CB_len m3 _ _ _ TC3) as LK3.
    assert (LF : length (firstn (Z.to_nat ret) bs') = Z.to_nat ret) by (rewrite firstn_length_le; [reflexivity| rewrite LBS2; clear - RETB Y2; lia]).
    assert (LEN3 : length (firstn (Z.to_nat ret) bs' ++ bs2) = Z.to_nat maxY) by (rewrite length_app, LF, LK3; clear - RETB Y2; lia).
    assert (DC3 : rw_cells asegs m3 d [CB (Z.to_nat maxY) (firstn (Z.to_nat ret) bs' ++ bs2)]).
    { rewrite <- LEN3. apply rw_CB_of_bytes'.
      - apply (proj2 (bytes_at_app _ _ _ _ _)). split.
        + pose proof (rw_cells_bytes_at _ _ _ _ DCa3) as B. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
        + rewrite LF, Z2Nat.id by (clear - RETB; lia). pose proof (rw_cells_bytes_at _ _ _ _ TC3) as B. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
      - rewrite LEN3, Z2Nat.id by (clear - MPOS; lia). exact (proj1 (af_acc_live RT AF Σ m3 d maxY ART3 IND)). }
    assert (MBY3 : mbio_repx (rt_live RT Σ) m3 KY dBv BMY (wz lenY) methY lenY maxY 0).
    { apply (mbio_repx_upd RT AF Σ m2 m3 KY dBv BMY (wz lenY) (wz lenY) methY lenY maxY 0 d (firstn (Z.to_nat ret) bs' ++ bs2) ART2 MBY2 KD); [| | exact LEN3| exact DC3].
      - intros [p n] a He NE Hp _. exact (YOUT3 p n a He NE Hp).
      - eapply rw_cells_agree_nw; [exact (rw_cells_head m2 _ _ _ BMC2)|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. exact (YOUT3 BMY 32 a INBM' NE_BD ltac:(clear - Ha; lia)). }
    assert (BMC3 : rw_cells asegs m3 BMY [C8 (wz lenY); C8 (wz d); C8 (wz maxY); C8 (wz (msec methY))]).
    { eapply rw_cells_agree_nw; [exact BMC2|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. exact (YOUT3 BMY 32 a INBM' NE_BD ltac:(clear - Ha; lia)). }
    clear COM2 REST2 PFR2 ON2 NMC2 MBX2 MBY2 FFC2 BMC2 DC2 DCa2 TC2 CTX2 ACCB2 ACCC2 DACC2 DACC2' SHBC2 UT2 ACCT2 ST2u ST2' FFS2 FRF2 PR3 WS3 WFR3 WL3 WFF3 YOUT3 ART2 DCa3 LK3 LF TC3.
    destruct RVD as [(ERV2 & EN2 & DLB) | (ERV2 & EN2 & EDL)]; rewrite ERV2 in Hc6'.
    + (* [comment removed for export] *)
      pose proof COM3 as (_ & _ & ST3' & _). pose proof PFR3 as (_ & _ & _ & FRF3 & _). unfold loc_F in FRF3.
      destruct (af_acc_live RT AF Σ m3 BMY 32 ART3 INBM) as [_ ACCB3].
      assert (RD : 0 <= dl /\ ret + dl < 2 ^ 31 /\ ret + dl <= lenY) by (clear - RET DLB NUM' Y2 Y3; Z.div_mod_to_equations; lia).
      pose proof (in_c3_walk (e_sp1 RT en) (e_gp RT en) v0 v1 v2 (e_sp RT en) h1 h2 h3 h4 h5 h6 h7 s2 (wz dBv) s4 s5 s6 (wz hBv)
                    (wz (shad (e_f RT en))) (wz namev) v3 v4 v5 v6 F fc m3 (e_f RT en) BMY ctxv d ret dl 1 hj j1 j2 j3 (wz lenY) (wz maxY) (wz (msec methY))
                    SP0' SPH F0 ltac:(clear - FH HLO; lia) FSH ltac:(clear; lia) MI3 FRF3 FFC3 BMC3 ACCB3 BM8 BHH BH ltac:(clear - BXF; lia)
                    ltac:(clear - RET; lia) ltac:(clear - RD; lia) ltac:(clear - RD; lia)) as W.
      cl_lift W Hc6' c7 Hc7. destruct (ASTA_unpack RT Σ _ _ c7 Hc7) as (ms7 & (m4 & -> & MU4 & WM4 & MI4 & FFC4 & BMC4) & Hc7'). clear Hc7 Hc6'.
      assert (ST4 : stk asegs m4 (e_lo RT en) (e_sp1 RT en)).
      { eapply stk_munch; [exact ST3'| exact MU4| exact WM4|]. intros x Hx. cbn. refine (conj _ (conj _ I)); [clear - Hx FH; lia| clear - Hx BHI LOW; lia]. }
      assert (COM4 : pem_com en Σ m4 off crem lrem (mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(namev, nn); (ctxv, ECTX)])).
      { eapply (com_seg RT AF GOBJ AFP libenv libenv_fp libenv_agree libenv_fp_where FZ_SITES FZ_CALLS en Σ m3 m4); [exact COM3| exact MU4| exact WM4| exact MI4| exact ST4|].
        apply Forall_cons; [right; right; cbn [fst snd]; clear; lia|]. apply Forall_cons; [| apply Forall_nil].
        right; left. exists (BMY, 32). split; [exact (YC _ INBM')|]. cbn [fst snd]. clear; lia. }
      assert (PR4 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (e_sp1 RT en) (map rng [(BMY, 32)] ++ [(e_f RT en + 32, e_f RT en + 36)]) m3 m4).
      { intros a _ Ho. apply MU4. cbn [map rng fst snd app outside] in Ho. destruct Ho as (Ho1 & Ho2 & _). cbn. refine (conj _ (conj _ I)); [clear - Ho2; lia| clear - Ho1; lia]. }
      destruct (FW [(BMY, 32)] (e_f RT en + 32) (e_f RT en + 36) HXL4 ltac:(clear; lia) ltac:(clear; lia)) as (WS4 & WFR4 & WL4 & WFF4).
      destruct (KEEP m3 m4 _ _ COM3 PR4 WS4 WFR4 WL4 ltac:(intros e [<-|[]]; right; right; left; reflexivity) REST3 PFR3 ON3 NMC3 MBX3) as (REST4 & PFR4 & ON4 & NMC4 & MBX4).
      assert (DC4 : rw_cells asegs m4 d [CB (Z.to_nat maxY) (firstn (Z.to_nat ret) bs' ++ bs2)]).
      { eapply rw_cells_agree_nw; [exact DC3|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply MU4. cbn.
        refine (conj _ (conj _ I)); [clear - Ha DXF MPOS; lia| clear - Ha DXB MPOS; lia]. }
      pose proof (live_ne_apart RT AF Σ m ctxv ECTX BMY 32 ART0 INC INBM NE_CB) as CXB. unfold ECTX in CXB.
      assert (CTX4 : rw_cells asegs m4 ctxv (ectx_cells (wz num2) ed' (wz 0) (wz 0))).
      { eapply rw_cells_agree_nw; [exact CTX3|]. intros a Ha. unfold ectx_cells in Ha. cbn [cells_size csize Nat.add] in Ha. apply MU4. cbn.
        refine (conj _ (conj _ I)); [clear - Ha CXF; lia| clear - Ha CXB; lia]. }
      assert (MBY4 : mbio_repx (rt_live RT Σ) m4 KY dBv BMY (wz (ret + dl)) methY lenY maxY 0).
      { apply (mbio_repx_upd RT AF Σ m3 m4 KY dBv BMY (wz lenY) (wz (ret + dl)) methY lenY maxY 0 d (firstn (Z.to_nat ret) bs' ++ bs2) ART3 MBY3 KD); [| exact (rw_cells_head m4 _ _ _ BMC4)| exact LEN3| exact DC4].
        intros [p n] a He NE Hp NB. cbn [fst snd] in Hp. apply MU4. cbn. refine (conj _ (conj _ I)); [| clear - NB; lia].
        destruct (FR4 p n (CLV _ (YC _ He))) as [Q|Q]; clear - Q Hp; lia. }
      destruct (ectx_blur m4 ctxv (wz num2) ed' (wz 0) (wz 0) LED' CTX4) as (cj4 & LCJ4 & CTXb4).
      exact (DECP en Σ m4 off crem lrem j0 lH endv x1 x2 gap hj j1 (wz dl) j2 j3 cj4 F fc eH eD (wz SITE_in_dfin) v0 v1 v2 (wz BMY) (wz (ret + dl)) (wz 0) (wz (e_f RT en + 32)) h4 h5 h6 h7 s2 s4 s5 s6 v3 v4 v5 v6
               ctxv namev nn hBv dBv BMY (ret + dl) bn KX KY methX methY lenX maxX lenY maxY COM4 REST4 ltac:(clear - REM; lia) ltac:(clear - LRM; lia) PFR4 FFC4 ON4 CAL LCJ4 CTXb4
               NMA NN BNL NMC4 HIN MBX4 MBY4 ltac:(clear - RET RD; lia) LSUM T c7 Hc7' Hk).
    + (* [comment removed for export] *)
      pose proof (in_c3r_walk (wz SITE_in_dfin) (e_sp1 RT en) (e_gp RT en) v0 v1 v2 (e_sp RT en) h1 h2 h3 h4 h5 h6 h7 s2 (wz dBv) s4 s5 s6 (wz hBv)
                    (wz (shad (e_f RT en))) (wz SHB) (wz namev) (wz ctxv) v3 v4 v5 v6 F fc m3 MI3) as W.
      cl_lift W Hc6' c7 Hc7. destruct (ASTA_unpack RT Σ _ _ c7 Hc7) as (ms7 & (-> & _) & Hc7'). clear Hc7 Hc6'.
      exact (RZ m3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ COM3 REST3 PFR3 FFC3 ON3 LED' CTX3 NMC3 MBX3 MBY3 Hc7').
Qed.
End CIni.
