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
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs PLayout I_lkit I_ut RT_iface_pem D_libiface_pem Fz_kit Fz_ckit Fz_chk Fz_fkit Fz_mkit Fz_env Fz_M_malloc Fz_M_free Fz_M_secure Fz_W1_defs Fz_W1_grow Fz_W1_pploc Fz_W3_iface Fz_W3_defs Fz_W3_lems Fz_W3_aux Fz_W3_aux2 Fz_W3_aux3 Fz_W3_aux4 Fz_W3_lits Fz_W4_kit Fz_W3_inik Fz_W3_deck.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Notation wz := (Z_to_bv 64) (only parsing).

Lemma mcost_nonneg : forall n, 0 <= mcost n.
Proof. intros n. unfold mcost. destruct (n <=? 64512) eqn:E; [lia| apply Z.leb_gt in E; lia]. Qed.
Lemma mcost_mono : forall a b, 0 <= a <= b -> mcost a <= mcost b.
Proof. intros a b H. unfold mcost. destruct (a <=? 64512) eqn:E1; destruct (b <=? 64512) eqn:E2; apply Z.leb_le in E1 || apply Z.leb_gt in E1; apply Z.leb_le in E2 || apply Z.leb_gt in E2; lia. Qed.
Lemma rw_CB_len : forall (m : word -> option byte) a n bs, rw_cells asegs m a [CB n bs] -> length bs = n.
Proof. intros m a n bs [[[W _] _] _]. exact W. Qed.

Section CDec.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AFP : art_facts_pem RT GOBJ.
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
Hypothesis C_BI : bio_ctrl_info_stmt RT.
Hypothesis C_PM : pem_malloc_stmt RT libenv FZ_SITES FZ_CALLS.
Hypothesis C_PM0 : pem_malloc0_stmt RT libenv.
Hypothesis C_BR : bio_read_stmt RT.
Hypothesis RL : RELOAD_stmt RT libenv errst_at_rest errst_live FZ_SITES FZ_CALLS.
Hypothesis OUTP : OUTFREE_stmt RT libenv errst_at_rest errst_live FZ_SITES FZ_CALLS.

Local Notation pem_entry := (pem_entry RT).
Local Notation pem_com := (pem_com RT libenv FZ_SITES FZ_CALLS).
Local Notation pem_frame := (pem_frame RT).
Local Notation pem_ms := (pem_ms RT).

(* [comment removed for export] *)
Lemma out_facts : forall (en : pem_entry) Σ (m : mem) off crem lrem cur P f k,
  pem_com en Σ m off crem lrem cur -> In (f, k) (e_frames RT en) -> f <= P -> P + 8 <= f + fs_size k - 8 ->
  0 < P /\ P + 8 <= e_lo RT en /\ (P + 8 <= 2147450880 \/ 17594333495296 <= P) /\ 2147450880 <= shad P < 17594333495296
  /\ (P + 8 <= e_f RT en \/ e_f RT en + 128 <= P) /\ (forall p n, In (p, n) (rt_live RT Σ) -> P + 8 <= p \/ p + n <= P).
Proof using AF AFP.
  intros en Σ m off crem lrem cur P f k COM HF F1 F2.
  pose proof COM as (ART0 & MI & ST & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & NTL & MB & OFF & BLT & KLV & PERM & CFR & ND & LPOS & FRS & _).
  assert (HF' : In (f, k) (rt_frames RT Σ)) by (rewrite FRS; right; exact HF).
  pose proof (af_frames_range RT AF Σ m f k ART0 HF') as (X0 & X1 & X2 & X3). pose proof (afp_frame_mem RT GOBJ AFP Σ m f k ART0 HF') as (Y1 & Y2).
  pose proof (Z.shiftl_nonneg 64 (Z.of_nat k)) as KN.
  pose proof (af_frames_disj RT AF Σ m (e_f RT en) 1%nat f k [] _ ART0 FRS ltac:(exact HF)) as D. change (fs_size 1) with 128 in D.
  split; [clear - X0 F1; lia|]. split; [clear - X1 LOW F2 KN; unfold fs_size in *; lia|]. split; [clear - Y1 F1 F2 KN; unfold fs_size in *; lia|].
  split; [clear - X0 F1 F2 Y2 KN; unfold shad, SHB, fs_size in *; Z.div_mod_to_equations; lia|].
  split; [clear - D F1 F2 KN; unfold fs_size in *; lia|].
  intros p n Hin. destruct (X3 p n Hin) as [Q|Q]; clear - Q F1 F2 KN; unfold fs_size in *; lia.
Qed.

(* [comment removed for export] *)
Lemma rest_keepL : forall (en : pem_entry) Σ Σ' (m m' : mem) off crem lrem cur,
  pem_com en Σ m off crem lrem cur -> errst_at_rest (e_E RT en) [] m -> rt_pres_fp (rt_live RT Σ') (rt_frames RT Σ) (e_sp1 RT en) (lib_W (e_LBL RT en)) m m' ->
  In (e_E RT en, 904) (rt_live RT Σ') -> errst_at_rest (e_E RT en) [] m'.
Proof using AF AFP errst_rest_agree errst_fp_where.
  intros en Σ Σ' m m' off crem lrem cur COM REST PR INE'. apply (errst_rest_agree m m' _ _ REST). intros a Ha.
  destruct (errst_fp_where _ _ _ Ha) as [R | (p & n & [] & _)].
  apply PR; [apply (acl_live _ _ _ (e_E RT en) 904); [exact INE' | exact R] | exact (com_E_out RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem cur COM _ R)].
Qed.

(* [comment removed for export] *)
Theorem DEC_proof : DEC_stmt RT libenv errst_at_rest errst_live FZ_SITES FZ_CALLS.
Proof.
  intros en Σ m off crem lrem j0 lH endv x1 x2 gap hj j1 tav j2 j3 cj F fc eH eD xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 t3 t4 t5 t6
         ctxv namev nn hBv dBv BMY dlen bn KX KY methX methY lenX maxX lenY maxY.
  cbv zeta. intros COM REST REM LRM PFR FFC ON CAL LCJ CTX NMA NN BNL NMC HIN MBX MBY DLR LSUM. unfold pem_at, cps. intros T c HA Hk.
  pose proof COM as (ART0 & MI & ST & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & NTL & MB & OFF & BLT & KLV & PERM & CFR & ND & LPOS
     & FRS & FRN & SP0 & CG & LIV & LR0 & CR & CR0 & CRE & CGH & CGS & CTX0 & UWC & F0 & F64 & FTOP & FSEG & FSH & FFS & SAVED & PRES & FLR & NDO & OUTS & FDO & MST).
  destruct (com_lists RT libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ COM) as [ELV CLV].
  assert (HLO : e_lo RT en <= e_sp1 RT en) by (clear - LOR; unfold RT_STACK, PEM_CALLEE_STACK in *; lia).
  assert (SP0' : 0 <= e_sp1 RT en) by (clear - HLO HLOS; lia). assert (SPH : e_sp1 RT en + 368 <= 2 ^ 47) by (clear - TOP PD; unfold e_sp1, USTACK_TOP in *; lia).
  assert (INF : In (e_f RT en, 1%nat) (rt_frames RT Σ)) by (rewrite FRS; left; reflexivity).
  pose proof (af_frames_range RT AF Σ m _ _ ART0 INF) as (_ & FLO & _ & FR4). change (fs_size 1) with 128 in FLO, FR4.
  assert (FH : e_f RT en + 128 <= e_lo RT en) by (clear - FLO LOW; lia).
  assert (HNM : In (namev, nn) (mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(namev, nn); (ctxv, ECTX)])) by (do 2 (apply in_or_app; right); left; reflexivity).
  assert (HCX : In (ctxv, ECTX) (mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(namev, nn); (ctxv, ECTX)])) by (do 2 (apply in_or_app; right); right; left; reflexivity).
  assert (YC : forall e, In e (mbio_ent KY maxY) -> In e (mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(namev, nn); (ctxv, ECTX)])) by (intros e He; apply in_or_app; right; apply in_or_app; left; exact He).
  assert (XC : forall e, In e (mbio_ent KX maxX) -> In e (mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(namev, nn); (ctxv, ECTX)])) by (intros e He; apply in_or_app; left; exact He).
  (* [comment removed for export] *)
  assert (OUTF : forall P, In P [e_PN RT en; e_PH RT en; e_PD RT en; e_PLN RT en] ->
            exists f k, In (f, k) (e_frames RT en) /\ f <= P /\ P + 8 <= f + fs_size k - 8 /\ bytes_at asegs (e_m RT en) (shad P) [z8] /\ P mod 8 = 0).
  { intros P HP. pose proof (proj1 (Forall_forall _ _) OUTS P HP) as [M8 [[H1 H2] | (f & k & Hin & G1 & G2 & GB)]].
    - exfalso. clear - H1 H2 TOP. unfold USTACK_TOP in *. lia.
    - exists f, k. split; [exact Hin|]. split; [exact G1|]. split; [exact G2|]. split; [exact GB| exact M8]. }
  destruct (OUTF (e_PN RT en) ltac:(left; reflexivity)) as (fN & kN & HFN & N1 & N2 & NB & N8).
  destruct (OUTF (e_PH RT en) ltac:(right; left; reflexivity)) as (fH & kH & HFH & H1 & H2 & HB & H8).
  destruct (OUTF (e_PD RT en) ltac:(do 2 right; left; reflexivity)) as (fD & kD & HFD & D1 & D2 & DB & D8).
  destruct (OUTF (e_PLN RT en) ltac:(do 3 right; left; reflexivity)) as (fL & kL & HFL & L1 & L2 & LB & L8). clear OUTF.
  pose proof (out_facts en Σ m off crem lrem _ _ _ _ COM HFN N1 N2) as (PN0 & PNS & PSN & SRN & PNF & PNL).
  pose proof (out_facts en Σ m off crem lrem _ _ _ _ COM HFH H1 H2) as (PH0 & PHS & PSH & SRH & PHF & PHL).
  pose proof (out_facts en Σ m off crem lrem _ _ _ _ COM HFD D1 D2) as (PD0 & PDS & PSD & SRD & PDF & PDL).
  pose proof (out_facts en Σ m off crem lrem _ _ _ _ COM HFL L1 L2) as (PL0 & PLS & PSL & SRL & PLF & PLL).
  (* [comment removed for export] *)
  pose proof (proj1 (List.NoDup_cons_iff _ _) NDO) as [NDa NDO2]. pose proof (proj1 (List.NoDup_cons_iff _ _) NDO2) as [NDb NDO3]. pose proof (proj1 (List.NoDup_cons_iff _ _) NDO3) as [NDc _].
  cbn [In] in NDa, NDb, NDc.
  assert (AHD : e_PH RT en + 8 <= e_PD RT en \/ e_PD RT en + 8 <= e_PH RT en) by (clear - NDb H8 D8; Z.div_mod_to_equations; lia).
  assert (ALN : e_PLN RT en + 8 <= e_PN RT en \/ e_PN RT en + 8 <= e_PLN RT en) by (clear - NDa N8 L8; Z.div_mod_to_equations; lia).
  assert (AHL : e_PH RT en + 8 <= e_PLN RT en \/ e_PLN RT en + 8 <= e_PH RT en) by (clear - NDb H8 L8; Z.div_mod_to_equations; lia).
  assert (AHN : e_PH RT en + 8 <= e_PN RT en \/ e_PN RT en + 8 <= e_PH RT en) by (clear - NDa H8 N8; Z.div_mod_to_equations; lia).
  assert (ADL : e_PD RT en + 8 <= e_PLN RT en \/ e_PLN RT en + 8 <= e_PD RT en) by (clear - NDc D8 L8; Z.div_mod_to_equations; lia).
  assert (ADN : e_PD RT en + 8 <= e_PN RT en \/ e_PN RT en + 8 <= e_PD RT en) by (clear - NDa D8 N8; Z.div_mod_to_equations; lia).
  (* [comment removed for export] *)
  pose proof ND as NDt. rewrite map_app, map_app, <- app_assoc in NDt. pose proof (nd_split _ _ NDt) as (_ & NDt2 & DJX).
  pose proof (nd_split _ _ NDt2) as (NDt3 & _ & _). pose proof (nd_split _ _ NDt3) as (_ & NDNC & DJY). clear NDt NDt2 NDt3. cbn [map fst] in DJX, DJY, NDNC.
  assert (NNC : namev <> ctxv) by (intros E; apply (proj1 (proj1 (List.NoDup_cons_iff _ _) NDNC)); left; exact (eq_sym E)). clear NDNC.
  (* [comment removed for export] *)
  assert (KEEPL : forall Σa Σb (ma mb : mem) cra lra cura vN vH vD vL BMXa blx offx bly offy,
    pem_com en Σa ma off cra lra cura -> (forall e, In e (mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(namev, nn); (ctxv, ECTX)]) -> In e cura) -> rt_frames RT Σa = rt_frames RT Σ ->
    rt_pres_fp (rt_live RT Σa) (rt_frames RT Σa) (e_sp1 RT en) (lib_W (e_LBL RT en)) ma mb -> (forall e, In e (rt_live RT Σa) -> In e (rt_live RT Σb)) ->
    errst_at_rest (e_E RT en) [] ma -> pem_frame en ma j0 lH (loc_F RT en) endv eH eD x1 x2 gap -> rw_cells asegs ma (e_f RT en) (ff_cells hj (wz dlen) j1 tav j2 (wz BMY) j3) ->
    rw_cells asegs ma ctxv [CB (Z.to_nat ECTX) cj] -> rw_cells asegs ma namev [CB (Z.to_nat nn) bn] ->
    mbio_repx (rt_live RT Σa) ma KX hBv BMXa blx methX lenX maxX offx -> mbio_repx (rt_live RT Σa) ma KY dBv BMY bly methY lenY maxY offy ->
    rw_cells asegs ma (e_PN RT en) [C8 vN] -> rw_cells asegs ma (e_PH RT en) [C8 vH] -> rw_cells asegs ma (e_PD RT en) [C8 vD] -> rw_cells asegs ma (e_PLN RT en) [C8 vL] ->
       errst_at_rest (e_E RT en) [] mb /\ pem_frame en mb j0 lH (loc_F RT en) endv eH eD x1 x2 gap /\ rw_cells asegs mb (e_f RT en) (ff_cells hj (wz dlen) j1 tav j2 (wz BMY) j3)
    /\ rw_cells asegs mb ctxv [CB (Z.to_nat ECTX) cj] /\ rw_cells asegs mb namev [CB (Z.to_nat nn) bn]
    /\ mbio_repx (rt_live RT Σb) mb KX hBv BMXa blx methX lenX maxX offx /\ mbio_repx (rt_live RT Σb) mb KY dBv BMY bly methY lenY maxY offy
    /\ rw_cells asegs mb (e_PN RT en) [C8 vN] /\ rw_cells asegs mb (e_PH RT en) [C8 vH] /\ rw_cells asegs mb (e_PD RT en) [C8 vD] /\ rw_cells asegs mb (e_PLN RT en) [C8 vL]).
  { intros Σa Σb ma mb cra lra cura vN vH vD vL BMXa blx offx bly offy COMa SUB FRSa PR LIN RESTa PFRa FFCa CTXa NMCa MBXa MBYa CNa CHa CDa CLa.
    destruct (com_lists RT libenv FZ_SITES FZ_CALLS en Σa ma off cra lra _ COMa) as [ELVa CLVa].
    pose proof (com_W_ok RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σa ma off cra lra _ COMa) as (HWS & HWFR & HWFF & HWF & HWL & HWP).
    assert (INFa : In (e_f RT en, 1%nat) (rt_frames RT Σa)) by (rewrite FRSa; exact INF).
    split; [exact (rest_keepL en Σa Σa ma mb off cra lra _ COMa RESTa PR (ELVa _ INE))|].
    split; [exact (pem_frame_keep RT en ma mb _ _ _ j0 lH (loc_F RT en) endv eH eD x1 x2 gap PFRa PR PD TOP HWS)|].
    split; [exact (ff_keep ma mb (e_f RT en) _ _ _ _ hj (wz dlen) j1 tav j2 (wz BMY) j3 FFCa PR INFa HWFF)|].
    assert (CK : forall p n bs, In (p, n) (mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(namev, nn); (ctxv, ECTX)]) -> 0 < n -> rw_cells asegs ma p [CB (Z.to_nat n) bs] -> rw_cells asegs mb p [CB (Z.to_nat n) bs]).
    { intros p n bs Hin POS C. eapply rw_cells_agree_nw; [exact C|]. intros a Ha.
      apply (com_cur_agree RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σa ma mb off cra lra _ _ _ _ (p, n) COMa HWL (fun e H => or_intror H) PR (SUB _ Hin) (CLVa _ (SUB _ Hin))).
      cbn [fst snd]. cbn [cells_size csize Nat.add] in Ha. clear - Ha POS. lia. }
    split; [exact (CK ctxv ECTX cj HCX ltac:(unfold ECTX; clear; lia) CTXa)|]. split; [exact (CK namev nn bn HNM ltac:(clear - NN; lia) NMCa)|].
    split. { eapply (mbio_repx_keep (rt_live RT Σa)); [exact MBXa| exact PR| intros e He; split; [| apply LIN]; apply CLVa; apply SUB; exact (XC _ He)|].
             intros e x He Hx. exact (com_cur_out RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σa ma off cra lra _ _ _ COMa HWL (fun e0 H0 => or_intror H0) e x (SUB _ (XC _ He)) Hx). }
    split. { eapply (mbio_repx_keep (rt_live RT Σa)); [exact MBYa| exact PR| intros e He; split; [| apply LIN]; apply CLVa; apply SUB; exact (YC _ He)|].
             intros e x He Hx. exact (com_cur_out RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σa ma off cra lra _ _ _ COMa HWL (fun e0 H0 => or_intror H0) e x (SUB _ (YC _ He)) Hx). }
    pose proof (com_out_agree RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σa ma mb off cra lra _ _ _ COMa HWS HWFR PR) as AGP.
    assert (G8 : forall P vv, In P [e_PN RT en; e_PH RT en; e_PD RT en; e_PLN RT en] -> rw_cells asegs ma P [C8 vv] -> rw_cells asegs mb P [C8 vv]).
    { intros P vv HPP C. eapply rw_cells_agree_nw; [exact C|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. exact (AGP P HPP). }
    split; [apply G8; [left; reflexivity| exact CNa]|]. split; [apply G8; [right; left; reflexivity| exact CHa]|].
    split; [apply G8; [do 2 right; left; reflexivity| exact CDa]| apply G8; [do 3 right; left; reflexivity| exact CLa]]. }
  (* [comment removed for export] *)
  assert (KEEPW : forall Σa (ma mb : mem) cra lra cura lo hi Q1 Q2 Q3 v1 v2 v3 BMXa blx offx bly offy,
    pem_com en Σa ma off cra lra cura -> (forall e, In e (mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(namev, nn); (ctxv, ECTX)]) -> In e cura) -> munch [(lo, hi)] ma mb ->
    hi <= e_lo RT en -> (hi <= e_f RT en \/ e_f RT en + 128 <= lo) ->
    (forall p n, In (p, n) (rt_live RT Σa) -> (In (p, n) (mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(namev, nn); (ctxv, ECTX)]) \/ (p, n) = (e_E RT en, 904)) -> hi <= p \/ p + n <= lo) ->
    (hi <= Q1 \/ Q1 + 8 <= lo) -> (hi <= Q2 \/ Q2 + 8 <= lo) -> (hi <= Q3 \/ Q3 + 8 <= lo) ->
    errst_at_rest (e_E RT en) [] ma -> pem_frame en ma j0 lH (loc_F RT en) endv eH eD x1 x2 gap -> rw_cells asegs ma (e_f RT en) (ff_cells hj (wz dlen) j1 tav j2 (wz BMY) j3) ->
    rw_cells asegs ma ctxv [CB (Z.to_nat ECTX) cj] -> rw_cells asegs ma namev [CB (Z.to_nat nn) bn] ->
    mbio_repx (rt_live RT Σa) ma KX hBv BMXa blx methX lenX maxX offx -> mbio_repx (rt_live RT Σa) ma KY dBv BMY bly methY lenY maxY offy ->
    rw_cells asegs ma Q1 [C8 v1] -> rw_cells asegs ma Q2 [C8 v2] -> rw_cells asegs ma Q3 [C8 v3] ->
       errst_at_rest (e_E RT en) [] mb /\ pem_frame en mb j0 lH (loc_F RT en) endv eH eD x1 x2 gap /\ rw_cells asegs mb (e_f RT en) (ff_cells hj (wz dlen) j1 tav j2 (wz BMY) j3)
    /\ rw_cells asegs mb ctxv [CB (Z.to_nat ECTX) cj] /\ rw_cells asegs mb namev [CB (Z.to_nat nn) bn]
    /\ mbio_repx (rt_live RT Σa) mb KX hBv BMXa blx methX lenX maxX offx /\ mbio_repx (rt_live RT Σa) mb KY dBv BMY bly methY lenY maxY offy
    /\ rw_cells asegs mb Q1 [C8 v1] /\ rw_cells asegs mb Q2 [C8 v2] /\ rw_cells asegs mb Q3 [C8 v3]).
  { intros Σa ma mb cra lra cura lo hi Q1 Q2 Q3 v1 v2 v3 BMXa blx offx bly offy COMa SUB MU PxS PxF PxL A1 A2 A3 RESTa PFRa FFCa CTXa NMCa MBXa MBYa C1 C2 C3.
    destruct (com_lists RT libenv FZ_SITES FZ_CALLS en Σa ma off cra lra _ COMa) as [ELVa CLVa].
    assert (OUT1 : forall x, ~ (lo <= x < hi) -> outside [(lo, hi)] x) by (intros x Hx; cbn [outside]; split; [exact Hx| exact I]).
    assert (PR : rt_pres_fp (rt_live RT Σa) (rt_frames RT Σa) (e_sp1 RT en) [(lo, hi)] ma mb) by (intros a _ Ho; exact (MU a Ho)).
    assert (BK : forall p n cs, In (p, n) (rt_live RT Σa) -> In (p, n) (mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(namev, nn); (ctxv, ECTX)]) -> Z.of_nat (cells_size cs) <= n -> rw_cells asegs ma p cs -> rw_cells asegs mb p cs).
    { intros p n cs Hin Hc SZ C. eapply rw_cells_agree_nw; [exact C|]. intros a Ha. apply MU. apply OUT1. destruct (PxL p n Hin (or_introl Hc)) as [Q|Q]; clear - Q Ha SZ; lia. }
    split. { apply (errst_rest_agree ma mb _ _ RESTa). intros a Ha. destruct (errst_fp_where _ _ _ Ha) as [R | (p & n & [] & _)].
             apply MU. apply OUT1. destruct (PxL _ _ (ELVa _ INE) (or_intror eq_refl)) as [Q|Q]; clear - Q R; lia. }
    split; [exact (pem_frame_keep RT en ma mb _ _ _ j0 lH (loc_F RT en) endv eH eD x1 x2 gap PFRa PR PD TOP (fun x Hx => OUT1 x ltac:(clear - Hx PxS HLO; lia)))|].
    assert (SZF : Z.of_nat (cells_size (ff_cells hj (wz dlen) j1 tav j2 (wz BMY) j3)) = 120) by reflexivity.
    split. { eapply rw_cells_agree_nw; [exact FFCa|]. rewrite SZF. intros a Ha. apply MU. apply OUT1. clear - Ha PxF. lia. }
    assert (SZC : Z.of_nat (cells_size [CB (Z.to_nat ECTX) cj]) <= ECTX) by (cbn [cells_size csize Nat.add]; unfold ECTX; clear; lia).
    assert (SZN : Z.of_nat (cells_size [CB (Z.to_nat nn) bn]) <= nn) by (cbn [cells_size csize Nat.add]; clear - NN; lia).
    split; [exact (BK ctxv ECTX _ (CLVa _ (SUB _ HCX)) HCX SZC CTXa)|]. split; [exact (BK namev nn _ (CLVa _ (SUB _ HNM)) HNM SZN NMCa)|].
    split. { eapply (mbio_repx_keep (rt_live RT Σa)); [exact MBXa| exact PR| intros e He; split; apply CLVa; apply SUB; exact (XC _ He)|].
             intros [p n] x He Hx. cbn [fst snd] in Hx. apply OUT1. destruct (PxL p n (CLVa _ (SUB _ (XC _ He))) (or_introl (XC _ He))) as [Q|Q]; clear - Q Hx; lia. }
    split. { eapply (mbio_repx_keep (rt_live RT Σa)); [exact MBYa| exact PR| intros e He; split; apply CLVa; apply SUB; exact (YC _ He)|].
             intros [p n] x He Hx. cbn [fst snd] in Hx. apply OUT1. destruct (PxL p n (CLVa _ (SUB _ (YC _ He))) (or_introl (YC _ He))) as [Q|Q]; clear - Q Hx; lia. }
    assert (OK8 : forall Q vv, (hi <= Q \/ Q + 8 <= lo) -> rw_cells asegs ma Q [C8 vv] -> rw_cells asegs mb Q [C8 vv]).
    { intros Q vv AQ C. eapply rw_cells_agree_nw; [exact C|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. intros a Ha. apply MU. apply OUT1. clear - Ha AQ. lia. }
    split. { exact (OK8 _ _ A1 C1). } split. { exact (OK8 _ _ A2 C2). } exact (OK8 _ _ A3 C3). }
  (* [comment removed for export] *)
  destruct MBX as [BMX MBXx]. pose proof MBXx as (flx & rrwx & numwx & padwx & nrx & nwx & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (rmx & _ & _ & _ & _ & _ & _ & _ & X1 & X2 & X3 & _)).
  pose proof MBY as (fly & rrwy & numwy & padwy & nry & nwy & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (rmy & _ & _ & _ & _ & _ & _ & _ & Y1 & Y2 & Y3 & _)).
  assert (LXB : lenX + 1 < 2 ^ 27) by (clear - LSUM OFF BLT Y1 X1 MB; destruct MB as [BM0 (f0 & r0 & n0 & p0 & nr0 & nw0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (rm0 & _ & _ & _ & _ & _ & _ & _ & O1 & O2 & O3 & _))]; lia).
  destruct ON as (CN0 & CH0 & CD0 & CL0). pose proof (mcost_nonneg lenY) as MNY. pose proof (mcost_nonneg (lenX + 1)) as MNX. unfold C_END in REM.
  (* [comment removed for export] *)
  pose proof (dc0_walk xra (e_sp1 RT en) (e_gp RT en) t0 t1 t2 (e_sp RT en) a0 a1 a3 a4 a5 a6 a7 s2 (wz dBv) s4 s5 s6 (wz (shad (e_f RT en)))
                (wz SHB) (wz namev) (wz ctxv) t3 t4 t5 t6 F fc m hBv MI) as W.
  cl_lift W HA c1 Hc1. destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (-> & _) & Hc1'). clear Hc1 HA.
  eapply (pem_call_binfo RT AF GOBJ AFP libenv libenv_fp libenv_agree libenv_fp_where FZ_SITES FZ_CALLS C_BI T en Σ m off crem lrem _ KX hBv methX lenX maxX 0 SITE_dc_ctrl F fc
            t0 t1 t2 a4 a5 a6 a7 s2 (wz dBv) s4 s5 s6 (wz hBv) (wz namev) (wz ctxv) t3 t4 t5 t6 c1 COM (ex_intro _ BMX MBXx) ltac:(unfold SITE_dc_ctrl; clear; lia) eq_refl Hc1').
  clear Hc1'. intros m1 F1 fc1 y0 y1 y2 d1 d2 d3 d4 d5 d6 d7 y3 y4 y5 y6 c2 COM1 PR1 MI1 MBX1 Hc2. rewrite Z.sub_0_r in Hc2.
  destruct (KEEPL Σ Σ m m1 crem lrem _ _ _ _ _ _ _ _ _ _ COM (fun e He => He) eq_refl (fun a Ha _ => PR1 a Ha I) (fun e He => He) REST PFR FFC CTX NMC MBXx MBY CN0 CH0 CD0 CL0)
    as (REST1 & PFR1 & FFC1 & CTX1 & NMC1 & MBX1' & MBY1 & CN1 & CH1 & CD1 & CL1).
  clear COM REST PFR FFC CTX NMC MBXx MBY MBX1 CN0 CH0 CD0 CL0 PR1 MI. rename MBX1' into MBX1.
  (* [comment removed for export] *)
  pose proof PFR1 as (_ & _ & _ & _ & _ & _ & FRE1 & _). unfold loc_E in FRE1.
  pose proof (dc1_walk (e_sp1 RT en) (e_gp RT en) y0 y1 y2 (e_sp RT en) d1 d2 d3 d4 d5 d6 d7 s2 (wz dBv) s4 s5 s6 (wz hBv) (wz (shad (e_f RT en)))
                (wz SHB) (wz namev) (wz ctxv) y3 y4 y5 y6 F1 fc1 m1 lenX (e_PD RT en) (e_PH RT en) (e_PN RT en) (e_f RT en) eH eD (e_flags RT en) (e_PLN RT en) (e_BI RT en)
                SP0' SPH ltac:(clear - X1 X2 X3; lia) MI1 FRE1) as W.
  cl_lift W Hc2 c3 Hc3. destruct (ASTA_unpack RT Σ _ _ c3 Hc3) as (ms3 & (-> & _) & Hc3'). clear Hc3 Hc2.
  eapply (pem_call_pmal RT AF GOBJ AFP libenv libenv_fp libenv_agree libenv_fp_where FZ_SITES FZ_CALLS C_PM T en Σ m1 off crem lrem _ (lenX + 1) SITE_dc_pmal1 F1 fc1
            y0 y1 y2 (wz 1003) d3 d4 d5 d6 d7 s2 (wz dBv) (wz lenX) s5 s6 (wz hBv) (wz namev) (wz ctxv) y3 y4 y5 y6 c3 COM1
            ltac:(clear - X1 LXB; lia) ltac:(clear - REM MNY; lia) ltac:(clear - LRM; lia) ltac:(unfold PEM_RAS_pmal, SITE_dc_pmal1; do 3 right; left; reflexivity) Hc3').
  clear Hc3'. intros Σ2 m2 F2 fc2 z0 z1 z2 e1 e2 e3 e4 e5 e6 e7 z3 z4 z5 z6 c4 HD hjunk COM2 LV2 FRS2 PR2 LHJ HDC P0H H16 HTOP Hc4.
  assert (LIN2 : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σ2)) by (intros e He; rewrite LV2; right; exact He).
  destruct (KEEPL Σ Σ2 m1 m2 crem lrem _ _ _ _ _ _ _ _ _ _ COM1 (fun e He => He) eq_refl PR2 LIN2 REST1 PFR1 FFC1 CTX1 NMC1 MBX1 MBY1 CN1 CH1 CD1 CL1)
    as (REST2 & PFR2 & FFC2 & CTX2 & NMC2 & MBX2 & MBY2 & CN2 & CH2 & CD2 & CL2).
  clear COM1 REST1 PFR1 FFC1 CTX1 NMC1 MBX1 MBY1 CN1 CH1 CD1 CL1 PR2 MI1 FRE1.
  (* [comment removed for export] *)
  pose proof COM2 as (ART2 & MI2 & ST2 & _).
  pose proof (cur_live_facts RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ2 m2 off _ _ _ (HD, lenX + 1) COM2 ltac:(left; reflexivity) ltac:(cbn; clear - X1; lia)) as (INH & _ & HLO2 & _). cbn [fst snd] in HLO2.
  pose proof (afp_live_mem RT GOBJ AFP Σ2 m2 HD (lenX + 1) ART2 INH ltac:(clear - X1; lia)) as (HSH & H47).
  pose proof (af_frames_range RT AF Σ2 m2 _ _ ART2 ltac:(rewrite FRS2; exact INF)) as (_ & _ & _ & FR42). change (fs_size 1) with 128 in FR42.
  pose proof (FR42 HD (lenX + 1) INH) as HXF.
  pose proof (out_facts en Σ2 m2 off _ _ _ _ _ _ COM2 HFH H1 H2) as (_ & _ & _ & _ & _ & PHL2).
  pose proof (out_facts en Σ2 m2 off _ _ _ _ _ _ COM2 HFD D1 D2) as (_ & _ & _ & _ & _ & PDL2).
  pose proof (PHL2 HD (lenX + 1) INH) as APH. pose proof (PDL2 HD (lenX + 1) INH) as APD.
  assert (SUB2 : forall e, In e (mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(namev, nn); (ctxv, ECTX)]) -> In e ((HD, lenX + 1) :: (mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(namev, nn); (ctxv, ECTX)]))) by (intros e He; right; exact He).
  (* [comment removed for export] *)
  pose proof PFR2 as (_ & _ & _ & FRF2 & _ & _ & FRE2 & _). unfold loc_E in FRE2. unfold loc_F in FRF2.
  pose proof (out_sh0 RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ2 m2 off _ _ _ (e_PH RT en) fH kH COM2 ltac:(right; left; reflexivity) HFH H1 H2 HB) as SHP2.
  pose proof (dc2_walk (e_sp1 RT en) (e_gp RT en) z0 z1 z2 (e_sp RT en) e1 e2 e3 e4 e5 e6 e7 s2 (wz dBv) (wz lenX) s5 s6 (wz hBv) (wz (shad (e_f RT en))) (wz SHB)
                (wz namev) (wz ctxv) z3 z4 z5 z6 F2 fc2 m2 HD dlen (e_PD RT en) (e_PH RT en) (e_PN RT en) (e_f RT en) eH eD (e_flags RT en) (e_PLN RT en) (e_BI RT en) _ _ _
                SP0' SPH F0 ltac:(clear - FH HLO; lia) ltac:(clear - DLR Y2 Y3; lia) MI2 FRE2 FRF2 (ff_cell32 m2 _ hj (wz dlen) j1 tav j2 (wz BMY) j3 FFC2) SHP2 CH2 PH0 ltac:(clear - PHS HLO; lia) PHF SRH PSH) as W.
  cl_lift W Hc4 c5 Hc5. destruct (ASTA_unpack RT Σ2 _ _ c5 Hc5) as (ms5 & (m3 & -> & MU3 & WM3 & MI3 & CH3) & Hc5'). clear Hc5 Hc4.
  assert (ST3 : stk asegs m3 (e_lo RT en) (e_sp1 RT en)) by (eapply stk_munch; [exact ST2| exact MU3| exact WM3|]; intros x Hx; cbn [outside]; split; [clear - Hx PHS; lia| exact I]).
  pose proof (com_out_store RT AF GOBJ AFP libenv libenv_fp libenv_agree libenv_fp_where FZ_SITES FZ_CALLS en Σ2 m2 m3 off _ _ _ (e_PH RT en) fH kH COM2 ltac:(right; left; reflexivity) HFH H1 H2 MU3 WM3 MI3 ST3) as COM3.
  destruct (KEEPW Σ2 m2 m3 _ _ _ (e_PH RT en) (e_PH RT en + 8) (e_PN RT en) (e_PD RT en) (e_PLN RT en) _ _ _ _ _ _ _ _ COM2 SUB2 MU3 PHS PHF (fun p n Hin _ => PHL2 p n Hin) ltac:(clear - AHN; lia) AHD AHL
              REST2 PFR2 FFC2 CTX2 NMC2 MBX2 MBY2 CN2 CD2 CL2) as (REST3 & PFR3 & FFC3 & CTX3 & NMC3 & MBX3 & MBY3 & CN3 & CD3 & CL3).
  assert (HDC3 : rw_cells asegs m3 HD [CB (Z.to_nat (lenX + 1)) hjunk]).
  { eapply rw_cells_agree_nw; [exact HDC|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply MU3. cbn [outside]. split; [clear - Ha APH X1; lia| exact I]. }
  clear COM2 REST2 PFR2 FFC2 CTX2 NMC2 MBX2 MBY2 CN2 CH2 CD2 CL2 HDC MU3 WM3 MI2 ST2 ST3 FRE2 FRF2 SHP2 ART2.
  pose proof COM3 as (ART3 & MI3' & ST3 & _).
  destruct (Z.eq_dec dlen 0) as [DZ | DNZ].
  - (* [comment removed for export] *)
    subst dlen.
    eapply (pem_call_pmal0 RT AF GOBJ AFP libenv libenv_fp libenv_agree libenv_fp_where FZ_SITES FZ_CALLS C_PM0 T en Σ2 m3 off _ _ _ SITE_dc_pmal2 F2 fc2
              z0 z1 z2 (wz 1004) e3 e4 e5 e6 e7 s2 (wz dBv) (wz lenX) s5 s6 (wz hBv) (wz namev) (wz ctxv) z3 z4 z5 z6 c5 COM3
              ltac:(unfold PEM_RAS_pmal, SITE_dc_pmal2; do 4 right; left; reflexivity) Hc5').
    clear Hc5'. intros Σ4 m4 F4 fc4 w0 w1 w2 g1 g2 g3 g4 g5 g6 g7 w3 w4 w5 w6 c6 COM4 LV4 FRS4 PR4 Hc6.
    rewrite LV4 in PR4.
    destruct (KEEPL Σ2 Σ4 m3 m4 _ _ _ _ _ _ _ _ _ _ _ _ COM3 SUB2 FRS2 PR4 ltac:(intros e He; rewrite LV4; exact He) REST3 PFR3 FFC3 CTX3 NMC3 MBX3 MBY3 CN3 CH3 CD3 CL3)
      as (REST4 & PFR4 & FFC4 & CTX4 & NMC4 & MBX4 & MBY4 & CN4 & CH4 & CD4 & CL4).
    assert (HDC4 : rw_cells asegs m4 HD [CB (Z.to_nat (lenX + 1)) hjunk]).
    { destruct (com_lists RT libenv FZ_SITES FZ_CALLS en Σ2 m3 off _ _ _ COM3) as [_ CLV3].
      pose proof (com_W_ok RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ2 m3 off _ _ _ COM3) as (_ & _ & _ & _ & HWL3 & _).
      eapply rw_cells_agree_nw; [exact HDC3|]. intros a Ha.
      apply (com_cur_agree RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ2 m3 m4 off _ _ _ _ _ _ (HD, lenX + 1) COM3 HWL3 (fun e H => or_intror H) PR4 ltac:(left; reflexivity) (CLV3 _ ltac:(left; reflexivity))).
      cbn [fst snd]. cbn [cells_size csize Nat.add] in Ha. clear - Ha X1. lia. }
    clear COM3 REST3 PFR3 FFC3 CTX3 NMC3 MBX3 MBY3 CN3 CH3 CD3 CL3 HDC3 PR4 MI3 MI3' ST3 ART3.
    pose proof COM4 as (ART4 & MI4 & ST4 & _). pose proof PFR4 as (_ & _ & _ & _ & _ & _ & FRE4 & _). unfold loc_E in FRE4.
    pose proof (out_sh0 RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ4 m4 off _ _ _ (e_PH RT en) fH kH COM4 ltac:(right; left; reflexivity) HFH H1 H2 HB) as SHP4.
    pose proof (out_sh0 RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ4 m4 off _ _ _ (e_PD RT en) fD kD COM4 ltac:(do 2 right; left; reflexivity) HFD D1 D2 DB) as SHD4.
    pose proof (dc3z_walk (e_sp1 RT en) (e_gp RT en) w0 w1 w2 (e_sp RT en) g1 g2 g3 g4 g5 g6 g7 s2 (wz dBv) (wz lenX) s5 s6 (wz hBv) (wz (shad (e_f RT en))) (wz SHB)
                  (wz namev) (wz ctxv) w3 w4 w5 w6 F4 fc4 m4 HD (e_PD RT en) (e_PH RT en) (e_PN RT en) (e_f RT en) eH eD (e_flags RT en) (e_PLN RT en) (e_BI RT en) _
                  SP0' SPH MI4 FRE4 SHD4 CD4 PD0 ltac:(clear - PDS HLO; lia) SRD PSD SHP4 CH4 PH0 ltac:(clear - PHS HLO; lia) SRH AHD ltac:(clear - P0H H47 X1; lia)) as W.
    cl_lift W Hc6 c7 Hc7. destruct (ASTA_unpack RT Σ4 _ _ c7 Hc7) as (ms7 & (m5 & -> & MU5 & WM5 & MI5 & CD5 & CH5) & Hc7'). clear Hc7 Hc6.
    assert (ST5 : stk asegs m5 (e_lo RT en) (e_sp1 RT en)) by (eapply stk_munch; [exact ST4| exact MU5| exact WM5|]; intros x Hx; cbn [outside]; split; [clear - Hx PDS; lia| exact I]).
    pose proof (com_out_store RT AF GOBJ AFP libenv libenv_fp libenv_agree libenv_fp_where FZ_SITES FZ_CALLS en Σ4 m4 m5 off _ _ _ (e_PD RT en) fD kD COM4 ltac:(do 2 right; left; reflexivity) HFD D1 D2 MU5 WM5 MI5 ST5) as COM5.
    pose proof (out_facts en Σ4 m4 off _ _ _ _ _ _ COM4 HFD D1 D2) as (_ & _ & _ & _ & _ & PDL4).
    destruct (KEEPW Σ4 m4 m5 _ _ _ (e_PD RT en) (e_PD RT en + 8) (e_PN RT en) (e_PH RT en) (e_PLN RT en) _ _ _ _ _ _ _ _ COM4 SUB2 MU5 PDS PDF (fun p n Hin _ => PDL4 p n Hin) ltac:(clear - ADN; lia) ltac:(clear - AHD; lia) ADL
                REST4 PFR4 FFC4 CTX4 NMC4 MBX4 MBY4 CN4 CH4 CL4) as (REST5 & PFR5 & FFC5 & CTX5 & NMC5 & MBXx5 & MBY5 & CN5 & _ & CL5).
    assert (HDC5 : rw_cells asegs m5 HD [CB (Z.to_nat (lenX + 1)) hjunk]).
    { eapply rw_cells_agree_nw; [exact HDC4|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply MU5. cbn [outside]. split; [| exact I].
      destruct (PDL4 HD (lenX + 1) ltac:(rewrite LV4; exact INH)) as [Q|Q]; clear - Ha Q X1; lia. }
    assert (HP5 : Permutation ((HD, lenX + 1) :: (mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(namev, nn); (ctxv, ECTX)])) (mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(namev, nn); (ctxv, ECTX)] ++ opt_ent (Some (HD, lenX + 1)))).
    { cbn [opt_ent]. eapply Permutation_trans; [apply Permutation_cons_append|]. rewrite <- !app_assoc. apply Permutation_refl. }
    pose proof (com_perm RT libenv FZ_SITES FZ_CALLS en Σ4 m5 off _ _ _ _ COM5 HP5) as COM5'.
    eapply (OUTP en Σ4 m5 off (crem - mcost (lenX + 1)) (lrem - 1) j0 lH endv x1 x2 gap hj (wz 0) j1 tav j2 (wz BMY) j3 cj F4 fc4 eH eD (wz SITE_dc_pmal2) w0 w1 w2 (wz 0) (wz HD) g2 g3 g4 g5 g6 g7
             s2 (wz lenX) s5 s6 w3 w4 w5 w6 (Some (HD, lenX + 1)) ctxv namev nn hBv dBv HD (lenX + 1) bn hjunk KX KY BMX BMY methX methY lenX maxX 0 lenY maxY 0 (wz lenX) (wz 0)
             COM5' REST5);
      [ unfold C_END; clear - REM MNY MNX; lia | exact PFR5 | exact FFC5 | exact CAL | exact LCJ | exact CTX5 | exact NMA | exact NN | exact BNL | exact NMC5 | exact HIN
      | cbv iota beta; split; [reflexivity|]; split; [clear - X1; lia|]; split; [exact H16|]; split; [exact LHJ| exact HDC5]
      | exact MBXx5 | exact MBY5 | exact CN5 | exact CH5 | exact CD5 | exact CL5 | exact Hc7' | exact Hk ].
  - (* [comment removed for export] *)
    (* [comment removed for export] *)
    assert (DC5K : forall Σq (mq : mem) (Fq : bvmap 5 word) (fcq : bv 32) (raq q0 q1 q2 qa0 qa1 qa2 qa3 qa4 qa5 qa6 qa7 q3 q4 q5 q6 : word) (cremq lremq BMXq offX DT : Z) (hj' dj : list byte) cq,
      pem_com en Σq mq off cremq lremq ((DT, dlen) :: (HD, lenX + 1) :: (mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(namev, nn); (ctxv, ECTX)])) -> rt_frames RT Σq = rt_frames RT Σ -> C_END + 1 <= cremq ->
      errst_at_rest (e_E RT en) [] mq -> pem_frame en mq j0 lH (loc_F RT en) endv eH eD x1 x2 gap -> rw_cells asegs mq (e_f RT en) (ff_cells hj (wz dlen) j1 tav j2 (wz BMY) j3) ->
      rw_cells asegs mq ctxv [CB (Z.to_nat ECTX) cj] -> rw_cells asegs mq namev [CB (Z.to_nat nn) bn] ->
      mbio_repx (rt_live RT Σq) mq KX hBv BMXq (wz lenX) methX lenX maxX offX -> mbio_repx (rt_live RT Σq) mq KY dBv BMY (wz dlen) methY lenY maxY 0 ->
      rw_cells asegs mq (e_PN RT en) [C8 (wz 0)] -> rw_cells asegs mq (e_PH RT en) [C8 (wz HD)] -> rw_cells asegs mq (e_PD RT en) [C8 (wz DT)] -> rw_cells asegs mq (e_PLN RT en) [C8 (wz 0)] ->
      length hj' = Z.to_nat (lenX + 1) -> rw_cells asegs mq HD [CB (Z.to_nat (lenX + 1)) hj'] -> length dj = Z.to_nat dlen -> rw_cells asegs mq DT [CB (Z.to_nat dlen) dj] -> 0 < DT < 2 ^ 47 ->
      ASTA RT Σq (e_PMc RT en) (eq (pem_ms en J_DC5 mq Fq fcq raq q0 q1 q2 qa0 qa1 qa2 qa3 qa4 qa5 qa6 qa7 s2 (wz dBv) (wz lenX) s5 s6 (wz hBv) (wz namev) (wz ctxv) q3 q4 q5 q6)) cq ->
      realizes asegs cq T).
    { intros Σq mq Fq fcq raq q0 q1 q2 qa0 qa1 qa2 qa3 qa4 qa5 qa6 qa7 q3 q4 q5 q6 cremq lremq BMXq offX DT hj' dj cq COMq FRSq CRq RESTq PFRq FFCq CTXq NMCq MBXq MBYq CNq CHq CDq CLq LHJ' HDCq LDJ DTCq DTR Hcq.
      pose proof COMq as (ARTq & MIq & STq & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NTLq & _ & _ & _ & _ & _ & CFRq & NDq & _).
      destruct (com_lists RT libenv FZ_SITES FZ_CALLS en Σq mq off _ _ _ COMq) as [ELVq CLVq].
      assert (INHq : In (HD, lenX + 1) (rt_live RT Σq)) by (apply CLVq; right; left; reflexivity).
      assert (INDq : In (DT, dlen) (rt_live RT Σq)) by (apply CLVq; left; reflexivity).
      assert (INFq : In (e_f RT en, 1%nat) (rt_frames RT Σq)) by (rewrite FRSq; exact INF).
      assert (SUBq : forall e, In e (mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(namev, nn); (ctxv, ECTX)]) -> In e ((DT, dlen) :: (HD, lenX + 1) :: (mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(namev, nn); (ctxv, ECTX)]))) by (intros e He; right; right; exact He).
      pose proof (af_frames_range RT AF Σq mq _ _ ARTq INFq) as (_ & _ & _ & FR4q). change (fs_size 1) with 128 in FR4q.
      pose proof (cur_live_facts RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σq mq off _ _ _ (HD, lenX + 1) COMq ltac:(right; left; reflexivity) ltac:(cbn; clear - X1; lia)) as (_ & _ & HLOq & _). cbn [fst snd] in HLOq.
      pose proof (afp_live_mem RT GOBJ AFP Σq mq HD (lenX + 1) ARTq INHq ltac:(clear - X1; lia)) as (HSHq & H47q).
      change (map fst ((DT, dlen) :: (HD, lenX + 1) :: (mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(namev, nn); (ctxv, ECTX)])) ++ e_E RT en :: mbio_blocks (e_K RT en)) with (DT :: HD :: (map fst (mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(namev, nn); (ctxv, ECTX)]) ++ e_E RT en :: mbio_blocks (e_K RT en))) in NDq.
      pose proof (proj1 (List.NoDup_cons_iff _ _) NDq) as [NDT NDq']. pose proof (proj1 (List.NoDup_cons_iff _ _) NDq') as [NDH _]. clear NDq NDq'.
      pose proof (out_facts en Σq mq off _ _ _ _ _ _ COMq HFH H1 H2) as (_ & _ & _ & _ & _ & PHLq). pose proof (out_facts en Σq mq off _ _ _ _ _ _ COMq HFD D1 D2) as (_ & _ & _ & _ & _ & PDLq).
      pose proof (out_facts en Σq mq off _ _ _ _ _ _ COMq HFL L1 L2) as (_ & _ & _ & _ & _ & PLLq). pose proof (out_facts en Σq mq off _ _ _ _ _ _ COMq HFN N1 N2) as (_ & _ & _ & _ & _ & PNLq).
      (* [comment removed for export] *)
      pose proof (rw_cells_split_CB asegs mq HD [] (Z.to_nat (lenX + 1)) hj' [] [Z.to_nat lenX; 1%nat] HDCq ltac:(cbn; clear - X1; lia)) as HS. cbn [mk_CB_cells app] in HS.
      pose proof (proj1 (rw_cells_app mq _ [CB (Z.to_nat lenX) (firstn (Z.to_nat lenX) hj')] _) HS) as [HB0 HB1]. clear HS.
      cbn [cells_size csize Nat.add] in HB1. rewrite Nat.add_0_r, Z2Nat.id in HB1 by (clear - X1; lia).
      pose proof (rw_CB_len mq _ _ _ HB1) as LB1.
      destruct (firstn 1 (skipn (Z.to_nat lenX) hj')) as [|bl [|b2 tl2]] eqn:EB; [cbn in LB1; discriminate| | cbn in LB1; discriminate].
      assert (HB1' : rw_cells asegs mq (HD + lenX) [C1 bl]) by (eapply rw_cells_recast; [exact HB1| cbn; repeat split; exact I| reflexivity]). clear HB1 LB1.
      destruct (af_acc_live RT AF Σq mq HD (lenX + 1) ARTq INHq) as [_ ACCHq].
      pose proof PFRq as (_ & _ & _ & FRFq & _ & _ & FREq & _). unfold loc_E in FREq. unfold loc_F in FRFq.
      pose proof (out_sh0 RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σq mq off _ _ _ (e_PH RT en) fH kH COMq ltac:(right; left; reflexivity) HFH H1 H2 HB) as SHPq.
      pose proof (out_sh0 RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σq mq off _ _ _ (e_PD RT en) fD kD COMq ltac:(do 2 right; left; reflexivity) HFD D1 D2 DB) as SHDq.
      (* [comment removed for export] *)
      pose proof (dc5_walk raq (e_sp1 RT en) (e_gp RT en) q0 q1 q2 (e_sp RT en) qa0 qa1 qa2 qa3 qa4 qa5 qa6 qa7 s2 s5 s6 (wz (shad (e_f RT en))) (wz namev) (wz ctxv) q3 q4 q5 q6 Fq fcq mq
                    HD (HD + lenX) DT lenX dlen (e_PD RT en) (e_PH RT en) (e_PN RT en) (e_f RT en) eH eD hBv dBv (e_flags RT en) (e_PLN RT en) (e_BI RT en) _ _ bl
                    SP0' SPH F0 ltac:(clear - FH HLO; lia) ltac:(clear - DLR Y2 Y3; lia) ltac:(clear - X1 X2 X3; lia) eq_refl MIq FREq FRFq (ff_cell32 mq _ hj (wz dlen) j1 tav j2 (wz BMY) j3 FFCq)
                    SHPq CHq PH0 ltac:(clear - PHS HLO; lia) SRH SHDq CDq PD0 ltac:(clear - PDS HLO; lia) SRD HB1' ACCHq P0H ltac:(clear - HLOq HLO; lia)
                    ltac:(clear - HSHq; lia) ltac:(destruct (FR4q HD (lenX + 1) INHq); clear - H X1; lia) ltac:(destruct (PDLq HD (lenX + 1) INHq); clear - H X1; lia) ltac:(destruct (PHLq HD (lenX + 1) INHq); clear - H X1; lia) DTR) as W.
      cl_lift W Hcq c7 Hc7. destruct (ASTA_unpack RT Σq _ _ c7 Hc7) as (ms7 & (m7 & -> & MU7 & WM7 & MI7 & HB17) & Hc7'). clear Hc7 Hcq.
      assert (ST7 : stk asegs m7 (e_lo RT en) (e_sp1 RT en)) by (eapply stk_munch; [exact STq| exact MU7| exact WM7|]; intros x Hx; cbn [outside]; split; [clear - Hx HLOq; lia| exact I]).
      assert (COM7 : pem_com en Σq m7 off cremq lremq ((DT, dlen) :: (HD, lenX + 1) :: (mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(namev, nn); (ctxv, ECTX)]))).
      { eapply (com_seg RT AF GOBJ AFP libenv libenv_fp libenv_agree libenv_fp_where FZ_SITES FZ_CALLS en Σq mq m7); [exact COMq| exact MU7| exact WM7| exact MI7| exact ST7|].
        apply Forall_cons; [| apply Forall_nil]. right; left. exists (HD, lenX + 1). split; [right; left; reflexivity|]. cbn [fst snd]. clear - X1; lia. }
      assert (HXL : forall p n, In (p, n) (rt_live RT Σq) -> In (p, n) (mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(namev, nn); (ctxv, ECTX)]) \/ (p, n) = (e_E RT en, 904) -> HD + lenX + 1 <= p \/ p + n <= HD + lenX).
      { intros p n Hin Hc. destruct (live_ne_apart RT AF Σq mq p n HD (lenX + 1) ARTq Hin INHq) as [Q|Q]; [| clear - Q X1; lia| clear - Q; lia].
        intros E. injection E as E1 E2. apply NDH. apply in_or_app. destruct Hc as [Hc|Hc]; [left; rewrite <- E1; exact (in_map fst _ _ Hc)| right; left; injection Hc as E3 E4; rewrite <- E1, E3; reflexivity]. }
      destruct (KEEPW Σq mq m7 _ _ _ (HD + lenX) (HD + lenX + 1) (e_PN RT en) (e_PH RT en) (e_PD RT en) _ _ _ _ _ _ _ _ COMq SUBq MU7 ltac:(clear - HLOq; lia)
                  ltac:(destruct (FR4q HD (lenX + 1) INHq); clear - H X1; lia) HXL
                  ltac:(destruct (PNLq HD (lenX + 1) INHq); clear - H X1; lia) ltac:(destruct (PHLq HD (lenX + 1) INHq); clear - H X1; lia) ltac:(destruct (PDLq HD (lenX + 1) INHq); clear - H X1; lia)
                  RESTq PFRq FFCq CTXq NMCq MBXq MBYq CNq CHq CDq) as (REST7 & PFR7 & FFC7 & CTX7 & NMC7 & MBX7 & MBY7 & CN7 & CH7 & CD7).
      assert (CL7 : rw_cells asegs m7 (e_PLN RT en) [C8 (wz 0)]).
      { eapply rw_cells_agree_nw; [exact CLq|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. intros a Ha. apply MU7. cbn [outside]. split; [| exact I].
        destruct (PLLq HD (lenX + 1) INHq); clear - H Ha X1; lia. }
      assert (DTC7 : rw_cells asegs m7 DT [CB (Z.to_nat dlen) dj]).
      { eapply rw_cells_agree_nw; [exact DTCq|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply MU7. cbn [outside]. split; [| exact I].
        destruct (live_ne_apart RT AF Σq mq DT dlen HD (lenX + 1) ARTq INDq INHq ltac:(intros E; injection E as E1 E2; apply NDT; left; exact (eq_sym E1))); clear - H Ha X1 DLR DNZ; lia. }
      assert (HB07 : rw_cells asegs m7 HD [CB (Z.to_nat lenX) (firstn (Z.to_nat lenX) hj')]).
      { eapply rw_cells_agree_nw; [exact HB0|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply MU7. cbn [outside]. split; [clear - Ha X1; lia| exact I]. }
      clear COMq RESTq PFRq FFCq CTXq NMCq MBXq MBYq CNq CHq CDq CLq HDCq DTCq HB0 HB1' MU7 WM7 MIq STq ST7 FREq FRFq SHPq SHDq ACCHq.
      pose proof COM7 as (ART7 & MI7' & ST7 & _). destruct (com_lists RT libenv FZ_SITES FZ_CALLS en Σq m7 off _ _ _ COM7) as [ELV7 CLV7].
      (* [comment removed for export] *)
      assert (HPY : Permutation ((DT, dlen) :: (HD, lenX + 1) :: (mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(namev, nn); (ctxv, ECTX)])) (mbio_ent KY maxY ++ ((DT, dlen) :: (HD, lenX + 1) :: mbio_ent KX maxX ++ [(namev, nn); (ctxv, ECTX)]))).
      { change ((DT, dlen) :: (HD, lenX + 1) :: (mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(namev, nn); (ctxv, ECTX)])) with (([(DT, dlen); (HD, lenX + 1)] ++ mbio_ent KX maxX) ++ mbio_ent KY maxY ++ [(namev, nn); (ctxv, ECTX)]).
        exact (Permutation_app_swap_app ([(DT, dlen); (HD, lenX + 1)] ++ mbio_ent KX maxX) (mbio_ent KY maxY) [(namev, nn); (ctxv, ECTX)]). }
      pose proof (com_perm RT libenv FZ_SITES FZ_CALLS en Σq m7 off _ _ _ _ COM7 HPY) as COM7y.
      eapply (pem_call_bread RT AF GOBJ AFP libenv libenv_fp libenv_agree libenv_fp_where FZ_SITES FZ_CALLS C_BR T en Σq m7 off _ _ _ KY dBv BMY (wz dlen) methY lenY maxY 0 DT dlen dlen dj SITE_dc_dread Fq fcq
                q0 q1 q2 qa3 qa4 qa5 qa6 qa7 (wz (e_f RT en + 32)) (wz dBv) (wz lenX) s5 s6 (wz hBv) (wz namev) (wz ctxv) q3 q4 q5 q6 c7 COM7y MBY7
                ltac:(clear - DNZ DLR; lia) ltac:(left; reflexivity) ltac:(clear; lia) LDJ DTC7 ltac:(unfold C_END in CRq; clear - CRq; lia) ltac:(unfold SITE_dc_dread; clear; lia) eq_refl Hc7').
      clear Hc7'. intros Σ8 m8 F8 fc8 u0 u1 u2 k1 k2 k3 k4 k5 k6 k7 u3 u4 u5 u6 c8 dj8 COM8y LV8 FRS8 PR8 WOK8 MBY8 LDJ8 DTC8 Hc8.
      pose proof WOK8 as (KWS8 & KWFR8 & KWFF8 & KWSH8 & KWL8 & KWP8).
      assert (LIN8 : forall e, In e (rt_live RT Σq) -> In e (rt_live RT Σ8)) by (intros e He; rewrite LV8; exact He).
      assert (NIN8 : forall e, In e (mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(namev, nn); (ctxv, ECTX)]) -> ~ In e (mbio_ent KY maxY) -> ~ In e ((DT, dlen) :: mbio_ent KY maxY)).
      { intros e He NY [E|X]; [| exact (NY X)]. apply NDT. right. apply in_or_app; left. rewrite <- E in He. exact (in_map fst _ _ He). }
      assert (NXY : forall e, In e (mbio_ent KX maxX) -> ~ In e (mbio_ent KY maxY)).
      { intros e He X. exact (DJX (fst e) (in_map fst _ _ He) ltac:(apply in_or_app; left; apply in_or_app; left; exact (in_map fst _ _ X))). }
      assert (NNY : ~ In (namev, nn) (mbio_ent KY maxY)) by (intros X; exact (DJY namev (in_map fst _ _ X) (or_introl eq_refl))).
      assert (NCY : ~ In (ctxv, ECTX) (mbio_ent KY maxY)) by (intros X; exact (DJY ctxv (in_map fst _ _ X) (or_intror (or_introl eq_refl)))).
      assert (NHY : ~ In (HD, lenX + 1) ((DT, dlen) :: mbio_ent KY maxY)).
      { intros [E|X]; [apply NDT; left; injection E as E1 E2; exact (eq_sym E1)|]. apply NDH. apply in_or_app; left. exact (in_map fst _ _ (YC _ X)). }
      assert (NIE8 : ~ In (e_E RT en, 904) ((DT, dlen) :: mbio_ent KY maxY)).
      { intros [E|X].
        - apply (CFRq (DT, dlen) ltac:(left; reflexivity)). cbn [fst]. injection E as E1 E2. rewrite E1. exact (in_map fst _ _ INE).
        - apply (NTLq (e_E RT en, 904) (or_introl eq_refl)). apply in_or_app; right. exact (in_map fst _ _ (SUBq _ (YC _ X))). }
      assert (CK8 : forall p n cs, In (p, n) ((DT, dlen) :: (HD, lenX + 1) :: (mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(namev, nn); (ctxv, ECTX)])) -> ~ In (p, n) ((DT, dlen) :: mbio_ent KY maxY) -> Z.of_nat (cells_size cs) <= n ->
                rw_cells asegs m7 p cs -> rw_cells asegs m8 p cs).
      { intros p n cs Hin NY SZ C. eapply rw_cells_agree_nw; [exact C|]. intros a Ha.
        assert (Ha' : p <= bv_unsigned a < p + n) by (clear - Ha SZ; lia).
        apply PR8; [exact (acl_live _ _ _ p n _ (CLV7 _ Hin) Ha')|].
        exact (com_cur_outX RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σq m7 off _ _ _ _ _ COM7y KWL8 (p, n) _ (Permutation_in _ HPY Hin) NY Ha'). }
      assert (REST8 : errst_at_rest (e_E RT en) [] m8).
      { apply (errst_rest_agree m7 m8 _ _ REST7). intros a Ha. destruct (errst_fp_where _ _ _ Ha) as [R | (p & n & [] & _)].
        apply PR8; [apply (acl_live _ _ _ (e_E RT en) 904); [exact (ELV7 _ INE)| exact R]| exact (KWL8 (e_E RT en) 904 _ (ELV7 _ INE) NIE8 R)]. }
      assert (INF7 : In (e_f RT en, 1%nat) (rt_frames RT Σq)) by (rewrite FRSq; exact INF).
      pose proof (pem_frame_keep RT en m7 m8 _ _ _ j0 lH (loc_F RT en) endv eH eD x1 x2 gap PFR7 PR8 PD TOP KWS8) as PFR8.
      pose proof (ff_keep m7 m8 (e_f RT en) _ _ _ _ hj (wz dlen) j1 tav j2 (wz BMY) j3 FFC7 PR8 INF7 KWFF8) as FFC8.
      pose proof (CK8 ctxv ECTX [CB (Z.to_nat ECTX) cj] (SUBq _ HCX) (NIN8 _ HCX NCY) ltac:(cbn [cells_size csize Nat.add]; unfold ECTX; clear; lia) CTX7) as CTX8.
      pose proof (CK8 namev nn [CB (Z.to_nat nn) bn] (SUBq _ HNM) (NIN8 _ HNM NNY) ltac:(cbn [cells_size csize Nat.add]; clear - NN; lia) NMC7) as NMC8.
      pose proof (CK8 HD (lenX + 1) [CB (Z.to_nat lenX) (firstn (Z.to_nat lenX) hj')] ltac:(right; left; reflexivity) NHY ltac:(cbn [cells_size csize Nat.add]; clear - X1; lia) HB07) as HB08.
      assert (HBB7 : rw_cells asegs m7 HD [CB (Z.to_nat lenX) (firstn (Z.to_nat lenX) hj'); C1 (Z_to_bv 8 0)]).
      { apply (proj2 (rw_cells_app m7 HD [CB (Z.to_nat lenX) (firstn (Z.to_nat lenX) hj')] [C1 (Z_to_bv 8 0)])). split; [exact HB07|].
        cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by (clear - X1; lia). exact HB17. }
      pose proof (CK8 HD (lenX + 1) [CB (Z.to_nat lenX) (firstn (Z.to_nat lenX) hj'); C1 (Z_to_bv 8 0)] ltac:(right; left; reflexivity) NHY ltac:(cbn [cells_size csize Nat.add]; clear - X1; lia) HBB7) as HBB8.
      assert (MBX8 : mbio_repx (rt_live RT Σ8) m8 KX hBv BMXq (wz lenX) methX lenX maxX offX).
      { eapply (mbio_repx_keep (rt_live RT Σq)); [exact MBX7| exact PR8| intros e He; split; [| apply LIN8]; apply CLV7; exact (SUBq _ (XC _ He))|].
        intros e x He Hx. exact (com_cur_outX RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σq m7 off _ _ _ _ _ COM7y KWL8 e x (Permutation_in _ HPY (SUBq _ (XC _ He))) (NIN8 _ (XC _ He) (NXY _ He)) Hx). }
      pose proof (com_out_agree RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σq m7 m8 off _ _ _ _ _ COM7y KWS8 KWFR8 PR8) as AGP8.
      assert (G8 : forall P vv, In P [e_PN RT en; e_PH RT en; e_PD RT en; e_PLN RT en] -> rw_cells asegs m7 P [C8 vv] -> rw_cells asegs m8 P [C8 vv]).
      { intros P vv HPP C. eapply rw_cells_agree_nw; [exact C|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. exact (AGP8 P HPP). }
      pose proof (G8 _ _ ltac:(left; reflexivity) CN7) as CN8. pose proof (G8 _ _ ltac:(right; left; reflexivity) CH7) as CH8.
      pose proof (G8 _ _ ltac:(do 2 right; left; reflexivity) CD7) as CD8. pose proof (G8 _ _ ltac:(do 3 right; left; reflexivity) CL7) as CL8.
      pose proof (com_perm RT libenv FZ_SITES FZ_CALLS en Σ8 m8 off _ _ _ _ COM8y (Permutation_sym HPY)) as COM8.
      rewrite <- LV8 in MBY8.
      clear COM7 COM7y REST7 PFR7 FFC7 CTX7 NMC7 MBX7 MBY7 CN7 CH7 CD7 CL7 HB07 HBB7 HB17 DTC7 PR8 WOK8 KWS8 KWFR8 KWFF8 KWSH8 KWL8 KWP8 AGP8 G8 CK8 MI7 MI7' ST7 ART7 ELV7 CLV7.
      pose proof COM8 as (ART8 & MI8 & ST8 & _). assert (FRS8' : rt_frames RT Σ8 = rt_frames RT Σ) by (rewrite FRS8; exact FRSq).
      pose proof (out_facts en Σ8 m8 off _ _ _ _ _ _ COM8 HFL L1 L2) as (_ & _ & _ & _ & _ & PLL8). pose proof (out_facts en Σ8 m8 off _ _ _ _ _ _ COM8 HFN N1 N2) as (_ & _ & _ & _ & _ & PNL8).
      (* [comment removed for export] *)
      pose proof PFR8 as (_ & _ & _ & _ & _ & _ & FRE8 & _). unfold loc_E in FRE8.
      pose proof (out_sh0 RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ8 m8 off _ _ _ (e_PLN RT en) fL kL COM8 ltac:(do 3 right; left; reflexivity) HFL L1 L2 LB) as SHL8.
      pose proof (dc6a_walk (e_sp1 RT en) (e_gp RT en) u0 u1 u2 (e_sp RT en) k1 k2 k3 k4 k5 k6 k7 (wz dBv) (wz lenX) s5 s6 (wz hBv) (wz (shad (e_f RT en))) (wz SHB) (wz namev) (wz ctxv) u3 u4 u5 u6 F8 fc8 m8
                    dlen (e_PD RT en) (e_PH RT en) (e_PN RT en) (e_f RT en) eH eD (e_flags RT en) (e_PLN RT en) (e_BI RT en) _
                    SP0' SPH F0 ltac:(clear - FH HLO; lia) ltac:(clear - DLR Y2 Y3; lia) MI8 FRE8 (ff_cell32 m8 _ hj (wz dlen) j1 tav j2 (wz BMY) j3 FFC8)
                    SHL8 CL8 PL0 ltac:(clear - PLS HLO; lia) SRL PLF) as W.
      cl_lift W Hc8 c9 Hc9. destruct (ASTA_unpack RT Σ8 _ _ c9 Hc9) as (ms9 & (m9 & -> & MU9 & WM9 & MI9 & CL9) & Hc9'). clear Hc9 Hc8.
      assert (ST9 : stk asegs m9 (e_lo RT en) (e_sp1 RT en)) by (eapply stk_munch; [exact ST8| exact MU9| exact WM9|]; intros x Hx; cbn [outside]; split; [clear - Hx PLS; lia| exact I]).
      pose proof (com_out_store RT AF GOBJ AFP libenv libenv_fp libenv_agree libenv_fp_where FZ_SITES FZ_CALLS en Σ8 m8 m9 off _ _ _ (e_PLN RT en) fL kL COM8 ltac:(do 3 right; left; reflexivity) HFL L1 L2 MU9 WM9 MI9 ST9) as COM9.
      destruct (KEEPW Σ8 m8 m9 _ _ _ (e_PLN RT en) (e_PLN RT en + 8) (e_PN RT en) (e_PH RT en) (e_PD RT en) _ _ _ _ _ _ _ _ COM8 SUBq MU9 PLS PLF (fun p n Hin _ => PLL8 p n Hin)
                  ltac:(clear - ALN; lia) ltac:(clear - AHL; lia) ltac:(clear - ADL; lia)
                  REST8 PFR8 FFC8 CTX8 NMC8 MBX8 MBY8 CN8 CH8 CD8) as (REST9 & PFR9 & FFC9 & CTX9 & NMC9 & MBX9 & MBY9 & CN9 & CH9 & CD9).
      assert (BK9 : forall p n cs, In (p, n) (rt_live RT Σ8) -> Z.of_nat (cells_size cs) <= n -> rw_cells asegs m8 p cs -> rw_cells asegs m9 p cs).
      { intros p n cs Hin SZ C. eapply rw_cells_agree_nw; [exact C|]. intros a Ha. apply MU9. cbn [outside]. split; [| exact I]. destruct (PLL8 p n Hin) as [Q|Q]; clear - Ha Q SZ; lia. }
      pose proof (BK9 HD (lenX + 1) [CB (Z.to_nat lenX) (firstn (Z.to_nat lenX) hj'); C1 (Z_to_bv 8 0)] (LIN8 _ INHq) ltac:(cbn [cells_size csize Nat.add]; clear - X1; lia) HBB8) as HBB9.
      pose proof (BK9 DT dlen [CB (Z.to_nat dlen) dj8] (LIN8 _ INDq) ltac:(cbn [cells_size csize Nat.add]; clear - DLR; lia) DTC8) as DTC9.
      clear COM8 COM8y REST8 PFR8 FFC8 CTX8 NMC8 MBX8 MBY8 CN8 CH8 CD8 CL8 HBB8 HB08 DTC8 MU9 WM9 MI8 ST8 ST9 FRE8 SHL8 BK9.
      pose proof COM9 as (ART9 & MI9' & ST9 & _).
      (* [comment removed for export] *)
      pose proof PFR9 as (_ & _ & _ & _ & _ & _ & FRE9 & _). unfold loc_E in FRE9.
      pose proof (out_sh0 RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ8 m9 off _ _ _ (e_PN RT en) fN kN COM9 ltac:(left; reflexivity) HFN N1 N2 NB) as SHN9.
      pose proof (cur_live_facts RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ8 m9 off _ _ _ (namev, nn) COM9 (SUBq _ HNM) ltac:(cbn; clear - NN; lia)) as (_ & NM0 & NMLO & _). cbn [fst snd] in NM0, NMLO.
      pose proof (dc6b_walk (e_sp1 RT en) (e_gp RT en) u0 u1 u2 (e_sp RT en) (wz dlen) (wz (e_PLN RT en)) k2 k3 k4 k5 k6 k7 (wz (e_f RT en + 32)) (wz dBv) (wz lenX) s5 s6 (wz hBv) (wz (shad (e_f RT en))) (wz SHB) (wz ctxv) u3 u4 u5 u6 F8 fc8 m9
                    namev (e_PD RT en) (e_PH RT en) (e_PN RT en) (e_f RT en) eH eD (e_flags RT en) (e_PLN RT en) (e_BI RT en) _
                    SP0' SPH ltac:(clear - NM0 NMLO HLO SPH NN; lia) MI9 FRE9 SHN9 CN9 PN0 ltac:(clear - PNS HLO; lia) SRN) as W.
      cl_lift W Hc9' c10 Hc10. destruct (ASTA_unpack RT Σ8 _ _ c10 Hc10) as (ms10 & (m10 & -> & MU10 & WM10 & MI10 & CN10) & Hc10'). clear Hc10 Hc9'.
      assert (ST10 : stk asegs m10 (e_lo RT en) (e_sp1 RT en)) by (eapply stk_munch; [exact ST9| exact MU10| exact WM10|]; intros x Hx; cbn [outside]; split; [clear - Hx PNS; lia| exact I]).
      pose proof (com_out_store RT AF GOBJ AFP libenv libenv_fp libenv_agree libenv_fp_where FZ_SITES FZ_CALLS en Σ8 m9 m10 off _ _ _ (e_PN RT en) fN kN COM9 ltac:(left; reflexivity) HFN N1 N2 MU10 WM10 MI10 ST10) as COM10.
      pose proof (out_facts en Σ8 m9 off _ _ _ _ _ _ COM9 HFN N1 N2) as (_ & _ & _ & _ & _ & PNL9).
      destruct (KEEPW Σ8 m9 m10 _ _ _ (e_PN RT en) (e_PN RT en + 8) (e_PH RT en) (e_PD RT en) (e_PLN RT en) _ _ _ _ _ _ _ _ COM9 SUBq MU10 PNS PNF (fun p n Hin _ => PNL9 p n Hin)
                  ltac:(clear - AHN; lia) ltac:(clear - ADN; lia) ltac:(clear - ALN; lia)
                  REST9 PFR9 FFC9 CTX9 NMC9 MBX9 MBY9 CH9 CD9 CL9) as (REST10 & PFR10 & FFC10 & CTX10 & NMC10 & MBX10 & MBY10 & CH10 & CD10 & CL10).
      assert (BK10 : forall p n cs, In (p, n) (rt_live RT Σ8) -> Z.of_nat (cells_size cs) <= n -> rw_cells asegs m9 p cs -> rw_cells asegs m10 p cs).
      { intros p n cs Hin SZ C. eapply rw_cells_agree_nw; [exact C|]. intros a Ha. apply MU10. cbn [outside]. split; [| exact I]. destruct (PNL9 p n Hin) as [Q|Q]; clear - Ha Q SZ; lia. }
      pose proof (BK10 HD (lenX + 1) [CB (Z.to_nat lenX) (firstn (Z.to_nat lenX) hj'); C1 (Z_to_bv 8 0)] (LIN8 _ INHq) ltac:(cbn [cells_size csize Nat.add]; clear - X1; lia) HBB9) as HBB10.
      pose proof (BK10 DT dlen [CB (Z.to_nat dlen) dj8] (LIN8 _ INDq) ltac:(cbn [cells_size csize Nat.add]; clear - DLR; lia) DTC9) as DTC10.
      clear COM9 REST9 PFR9 FFC9 CTX9 NMC9 MBX9 MBY9 CN9 CH9 CD9 CL9 HBB9 DTC9 MU10 WM10 MI9 MI9' ST9 ST10 FRE9 SHN9 BK10.
      pose proof COM10 as (ART10 & _). destruct (com_lists RT libenv FZ_SITES FZ_CALLS en Σ8 m10 off _ _ _ COM10) as [ELV10 CLV10].
      (* [comment removed for export] *)
      assert (EQR : (mbio_ent KX maxX ++ mbio_ent KY maxY ++ opt_ent (Some (ctxv, ECTX)) ++ opt_ent None) ++ [] ++ [(DT, dlen); (HD, lenX + 1); (namev, nn)]
                    = (mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(ctxv, ECTX)]) ++ [(DT, dlen); (HD, lenX + 1); (namev, nn)]).
      { cbn [opt_ent]. rewrite (app_nil_r [(ctxv, ECTX)]). reflexivity. }
      assert (HPR : Permutation ((DT, dlen) :: (HD, lenX + 1) :: (mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(namev, nn); (ctxv, ECTX)])) ((mbio_ent KX maxX ++ mbio_ent KY maxY ++ opt_ent (Some (ctxv, ECTX)) ++ opt_ent None) ++ [] ++ [(DT, dlen); (HD, lenX + 1); (namev, nn)])).
      { rewrite EQR. apply Permutation_sym. apply (Permutation_trans (l' := [(DT, dlen); (HD, lenX + 1); (namev, nn)] ++ (mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(ctxv, ECTX)]))); [apply Permutation_app_comm|].
        change ([(DT, dlen); (HD, lenX + 1); (namev, nn)] ++ (mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(ctxv, ECTX)]))
          with ((DT, dlen) :: (HD, lenX + 1) :: (namev, nn) :: (mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(ctxv, ECTX)])).
        do 2 apply perm_skip. rewrite (app_assoc (mbio_ent KX maxX) (mbio_ent KY maxY) [(namev, nn); (ctxv, ECTX)]), (app_assoc (mbio_ent KX maxX) (mbio_ent KY maxY) [(ctxv, ECTX)]).
        apply Permutation_middle. }
      pose proof (com_perm RT libenv FZ_SITES FZ_CALLS en Σ8 m10 off _ _ _ _ COM10 HPR) as COM10'.
      assert (HJ : rw_cells asegs m10 HD [CB (Z.to_nat (lenX + 1)) (firstn (Z.to_nat lenX) hj' ++ [Z_to_bv 8 0])]).
      { assert (LF : length (firstn (Z.to_nat lenX) hj') = Z.to_nat lenX) by (rewrite firstn_length_le; [reflexivity| rewrite LHJ'; clear - X1; lia]).
        assert (LL : length (firstn (Z.to_nat lenX) hj' ++ [Z_to_bv 8 0]) = Z.to_nat (lenX + 1)) by (rewrite length_app, LF; cbn [length]; clear - X1; lia).
        rewrite <- LL. apply rw_CB_of_bytes'.
        - pose proof (rw_cells_bytes_at _ _ _ _ HBB10) as B. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
        - rewrite LL, Z2Nat.id by (clear - X1; lia). exact (proj1 (af_acc_live RT AF Σ8 m10 HD (lenX + 1) ART10 (LIN8 _ INHq))). }
      eapply (RL en Σ8 m10 off _ _ [] [(DT, dlen); (HD, lenX + 1); (namev, nn)] j0 lH (loc_F RT en) endv x1 x2 gap hj (wz dlen) j1 tav j2 (wz BMY) j3 F8 fc8 eH eD (wz SITE_dc_dread) u0 u1 u2
                (wz (e_PN RT en)) (wz (e_PLN RT en)) k2 k3 k4 k5 k6 k7 (wz (e_f RT en + 32)) (wz lenX) s6 u3 u4 u5 u6 (Some (ctxv, ECTX)) None ctxv 0 nn hBv dBv 1
                KX KY BMXq BMY methX methY lenX maxX offX lenY maxY dlen (wz lenX) (wz dlen) COM10');
        [| unfold C_END in CRq |- *; clear - CRq; lia| exact PFR10| exact FFC10| reflexivity| reflexivity| exact MBX10| exact MBY10| | cbn [news_sz fold_right snd]; clear - DLR LSUM NN; lia| exact Hc10'| exact Hk].
      - split; [left; split; [reflexivity| exact REST10]|]. split; [apply Forall_nil|]. split; intros e [].
      - right. split; [reflexivity|]. exists namev, HD, DT, nn, (lenX + 1), dlen, bn, (firstn (Z.to_nat lenX) hj' ++ [Z_to_bv 8 0]), dj8.
        split; [reflexivity|]. split; [clear - NN; lia|]. split; [clear - X1 X2 X3; lia|]. split; [clear - DNZ DLR Y2 Y3; lia|].
        split; [exact CN10|]. split; [exact CH10|]. split; [exact CD10|]. split; [exact CL10|].
        split; [exact BNL|]. split; [exact NMC10|]. split; [exact HIN|].
        split; [rewrite length_app, firstn_length_le by (rewrite LHJ'; clear - X1; lia); cbn [length]; clear - X1; lia|]. split; [exact HJ|].
        split; [rewrite nth_error_app2 by (rewrite firstn_length_le by (rewrite LHJ'; clear - X1; lia); clear - X1; lia); rewrite firstn_length_le by (rewrite LHJ'; clear - X1; lia);
               replace (Z.to_nat (lenX + 1 - 1) - Z.to_nat lenX)%nat with 0%nat by (clear - X1; lia); reflexivity|].
        split; [exact LDJ8| exact DTC10]. }
    assert (DLB : 0 < dlen < 2 ^ 27) by (clear - DNZ DLR LSUM OFF BLT Y1 X1 MB; destruct MB as [BM0 (f0 & r0 & n0 & p0 & nr0 & nw0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (rm0 & _ & _ & _ & _ & _ & _ & _ & O1 & O2 & O3 & _))]; lia).
    pose proof (mcost_mono dlen lenY ltac:(clear - DLR; lia)) as MDY.
    eapply (pem_call_pmal RT AF GOBJ AFP libenv libenv_fp libenv_agree libenv_fp_where FZ_SITES FZ_CALLS C_PM T en Σ2 m3 off _ _ _ dlen SITE_dc_pmal2 F2 fc2
              z0 z1 z2 (wz 1004) e3 e4 e5 e6 e7 s2 (wz dBv) (wz lenX) s5 s6 (wz hBv) (wz namev) (wz ctxv) z3 z4 z5 z6 c5 COM3
              DLB ltac:(clear - REM MNY MDY; lia) ltac:(clear - LRM; lia) ltac:(unfold PEM_RAS_pmal, SITE_dc_pmal2; do 4 right; left; reflexivity) Hc5').
    clear Hc5'. intros Σ4 m4 F4 fc4 w0 w1 w2 g1 g2 g3 g4 g5 g6 g7 w3 w4 w5 w6 c6 DT djunk COM4 LV4 FRS4 PR4 LDJ DTC D0T D16 DTOP Hc6.
    assert (LIN4 : forall e, In e (rt_live RT Σ2) -> In e (rt_live RT Σ4)) by (intros e He; rewrite LV4; right; exact He).
    assert (FRS4' : rt_frames RT Σ4 = rt_frames RT Σ) by (rewrite FRS4; exact FRS2).
    destruct (KEEPL Σ2 Σ4 m3 m4 _ _ _ _ _ _ _ _ _ _ _ _ COM3 SUB2 FRS2 PR4 LIN4 REST3 PFR3 FFC3 CTX3 NMC3 MBX3 MBY3 CN3 CH3 CD3 CL3)
      as (REST4 & PFR4 & FFC4 & CTX4 & NMC4 & MBX4 & MBY4 & CN4 & CH4 & CD4 & CL4).
    assert (HDC4 : rw_cells asegs m4 HD [CB (Z.to_nat (lenX + 1)) hjunk]).
    { destruct (com_lists RT libenv FZ_SITES FZ_CALLS en Σ2 m3 off _ _ _ COM3) as [_ CLV3].
      pose proof (com_W_ok RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ2 m3 off _ _ _ COM3) as (_ & _ & _ & _ & HWL3 & _).
      eapply rw_cells_agree_nw; [exact HDC3|]. intros a Ha.
      apply (com_cur_agree RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ2 m3 m4 off _ _ _ _ _ _ (HD, lenX + 1) COM3 HWL3 (fun e H => or_intror H) PR4 ltac:(left; reflexivity) (CLV3 _ ltac:(left; reflexivity))).
      cbn [fst snd]. cbn [cells_size csize Nat.add] in Ha. clear - Ha X1. lia. }
    clear COM3 REST3 PFR3 FFC3 CTX3 NMC3 MBX3 MBY3 CN3 CH3 CD3 CL3 HDC3 PR4 MI3 MI3' ST3 ART3.
    (* [comment removed for export] *)
    pose proof COM4 as (ART4 & MI4 & ST4 & _). destruct (com_lists RT libenv FZ_SITES FZ_CALLS en Σ4 m4 off _ _ _ COM4) as [ELV4 CLV4].
    pose proof (cur_live_facts RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ4 m4 off _ _ _ (DT, dlen) COM4 ltac:(left; reflexivity) ltac:(cbn; clear - DLB; lia)) as (IND & _ & DLO4 & _). cbn [fst snd] in DLO4.
    pose proof (afp_live_mem RT GOBJ AFP Σ4 m4 DT dlen ART4 IND ltac:(clear - DLB; lia)) as (DSH & D47).
    pose proof (out_facts en Σ4 m4 off _ _ _ _ _ _ COM4 HFH H1 H2) as (_ & _ & _ & _ & _ & PHL4). pose proof (out_facts en Σ4 m4 off _ _ _ _ _ _ COM4 HFD D1 D2) as (_ & _ & _ & _ & _ & PDL4).
    assert (SUB4 : forall e, In e (mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(namev, nn); (ctxv, ECTX)]) -> In e ((DT, dlen) :: (HD, lenX + 1) :: (mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(namev, nn); (ctxv, ECTX)]))) by (intros e He; right; right; exact He).
    (* [comment removed for export] *)
    pose proof PFR4 as (_ & _ & _ & _ & _ & _ & FRE4 & _). unfold loc_E in FRE4.
    pose proof (out_sh0 RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ4 m4 off _ _ _ (e_PH RT en) fH kH COM4 ltac:(right; left; reflexivity) HFH H1 H2 HB) as SHP4.
    pose proof (out_sh0 RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ4 m4 off _ _ _ (e_PD RT en) fD kD COM4 ltac:(do 2 right; left; reflexivity) HFD D1 D2 DB) as SHD4.
    pose proof (dc3_walk (e_sp1 RT en) (e_gp RT en) w0 w1 w2 (e_sp RT en) g1 g2 g3 g4 g5 g6 g7 s2 (wz dBv) s5 s6 (wz (shad (e_f RT en))) (wz SHB)
                  (wz namev) (wz ctxv) w3 w4 w5 w6 F4 fc4 m4 HD DT lenX (e_PD RT en) (e_PH RT en) (e_PN RT en) (e_f RT en) eH eD hBv dBv (e_flags RT en) (e_PLN RT en) (e_BI RT en) _
                  SP0' SPH MI4 FRE4 SHD4 CD4 PD0 ltac:(clear - PDS HLO; lia) SRD PSD SHP4 CH4 PH0 ltac:(clear - PHS HLO; lia) SRH AHD ltac:(clear - P0H H47 X1; lia)
                  ltac:(clear - D0T D47 DLB; lia) ltac:(clear - X1 X2 X3; lia)) as W.
    cl_lift W Hc6 c7 Hc7. destruct (ASTA_unpack RT Σ4 _ _ c7 Hc7) as (ms7 & (m5 & -> & MU5 & WM5 & MI5 & CD5 & CH5) & Hc7'). clear Hc7 Hc6.
    assert (ST5 : stk asegs m5 (e_lo RT en) (e_sp1 RT en)) by (eapply stk_munch; [exact ST4| exact MU5| exact WM5|]; intros x Hx; cbn [outside]; split; [clear - Hx PDS; lia| exact I]).
    pose proof (com_out_store RT AF GOBJ AFP libenv libenv_fp libenv_agree libenv_fp_where FZ_SITES FZ_CALLS en Σ4 m4 m5 off _ _ _ (e_PD RT en) fD kD COM4 ltac:(do 2 right; left; reflexivity) HFD D1 D2 MU5 WM5 MI5 ST5) as COM5.
    destruct (KEEPW Σ4 m4 m5 _ _ _ (e_PD RT en) (e_PD RT en + 8) (e_PN RT en) (e_PH RT en) (e_PLN RT en) _ _ _ _ _ _ _ _ COM4 SUB4 MU5 PDS PDF (fun p n Hin _ => PDL4 p n Hin) ltac:(clear - ADN; lia) ltac:(clear - AHD; lia) ADL
                REST4 PFR4 FFC4 CTX4 NMC4 MBX4 MBY4 CN4 CH4 CL4) as (REST5 & PFR5 & FFC5 & CTX5 & NMC5 & MBX5 & MBY5 & CN5 & _ & CL5).
    assert (BK5 : forall p n bs, In (p, n) (rt_live RT Σ4) -> 0 < n -> rw_cells asegs m4 p [CB (Z.to_nat n) bs] -> rw_cells asegs m5 p [CB (Z.to_nat n) bs]).
    { intros p n bs Hin POS C. eapply rw_cells_agree_nw; [exact C|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply MU5. cbn [outside]. split; [| exact I].
      destruct (PDL4 p n Hin) as [Q|Q]; clear - Ha Q POS; lia. }
    pose proof (BK5 HD (lenX + 1) hjunk (LIN4 _ INH) ltac:(clear - X1; lia) HDC4) as HDC5. pose proof (BK5 DT dlen djunk IND ltac:(clear - DLB; lia) DTC) as DTC5.
    clear COM4 REST4 PFR4 FFC4 CTX4 NMC4 MBX4 MBY4 CN4 CH4 CD4 CL4 HDC4 DTC BK5 MU5 WM5 MI4 ST4 FRE4 SHP4 SHD4.
    pose proof COM5 as (ART5 & MI5' & ST5' & _).
    destruct (Z.eq_dec lenX 0) as [LZ | LNZ].
    + (* [comment removed for export] *)
      rewrite LZ in Hc7'. cbn [Z.eqb] in Hc7'. rewrite <- LZ in Hc7'.
      exact (DC5K Σ4 m5 F4 fc4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ BMX 0 DT hjunk djunk c7 COM5 FRS4' ltac:(unfold C_END; clear - REM MNY MDY MNX; lia)
               REST5 PFR5 FFC5 CTX5 NMC5 MBX5 MBY5 CN5 CH5 CD5 CL5 LHJ HDC5 LDJ DTC5 ltac:(clear - D0T D47 DLB; lia) Hc7').
    + (* [comment removed for export] *)
      replace (lenX =? 0) with false in Hc7' by (symmetry; apply Z.eqb_neq; exact LNZ). cbn [negb] in Hc7'.
      (* [comment removed for export] *)
      pose proof COM5 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NTL5 & _ & _ & _ & _ & _ & CFR5 & ND5 & _).
      change (map fst ((DT, dlen) :: (HD, lenX + 1) :: (mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(namev, nn); (ctxv, ECTX)])) ++ e_E RT en :: mbio_blocks (e_K RT en))
        with (DT :: HD :: (map fst (mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(namev, nn); (ctxv, ECTX)]) ++ e_E RT en :: mbio_blocks (e_K RT en))) in ND5.
      pose proof (proj1 (List.NoDup_cons_iff _ _) ND5) as [NDT ND5']. pose proof (proj1 (List.NoDup_cons_iff _ _) ND5') as [NDH _]. clear ND5 ND5'.
      assert (HPX : Permutation ((DT, dlen) :: (HD, lenX + 1) :: (mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(namev, nn); (ctxv, ECTX)])) (mbio_ent KX maxX ++ ((DT, dlen) :: (HD, lenX + 1) :: mbio_ent KY maxY ++ [(namev, nn); (ctxv, ECTX)]))).
      { exact (Permutation_app_swap_app [(DT, dlen); (HD, lenX + 1)] (mbio_ent KX maxX) (mbio_ent KY maxY ++ [(namev, nn); (ctxv, ECTX)])). }
      pose proof (com_perm RT libenv FZ_SITES FZ_CALLS en Σ4 m5 off _ _ _ _ COM5 HPX) as COM5x.
      eapply (pem_call_bread RT AF GOBJ AFP libenv libenv_fp libenv_agree libenv_fp_where FZ_SITES FZ_CALLS C_BR T en Σ4 m5 off _ _ _ KX hBv BMX (wz lenX) methX lenX maxX 0 HD (lenX + 1) lenX hjunk SITE_dc_hread F4 fc4
                w0 w1 w2 g3 g4 g5 g6 g7 s2 (wz dBv) (wz lenX) s5 s6 (wz hBv) (wz namev) (wz ctxv) w3 w4 w5 w6 c7 COM5x MBX5
                ltac:(clear - LNZ X1; lia) ltac:(right; left; reflexivity) ltac:(clear; lia) LHJ HDC5 ltac:(unfold C_END; clear - REM MNY MDY MNX; lia) ltac:(unfold SITE_dc_hread; clear; lia) eq_refl Hc7').
      clear Hc7'. intros Σ6 m6 F6 fc6 v0 v1 v2 h1 h2 h3 h4 h5 h6 h7 v3 v4 v5 v6 c8 hj6 COM6x LV6 FRS6 PR6 WOK6 MBX6 LHJ6 HDC6 Hc8.
      pose proof WOK6 as (KWS6 & KWFR6 & KWFF6 & KWSH6 & KWL6 & KWP6).
      destruct (com_lists RT libenv FZ_SITES FZ_CALLS en Σ4 m5 off _ _ _ COM5x) as [ELV5 CLV5].
      assert (LIN6 : forall e, In e (rt_live RT Σ4) -> In e (rt_live RT Σ6)) by (intros e He; rewrite LV6; exact He).
      assert (INF4 : In (e_f RT en, 1%nat) (rt_frames RT Σ4)) by (rewrite FRS4'; exact INF).
      (* [comment removed for export] *)
      assert (NIN6 : forall e, In e (mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(namev, nn); (ctxv, ECTX)]) -> ~ In e (mbio_ent KX maxX) -> ~ In e ((HD, lenX + 1) :: mbio_ent KX maxX)).
      { intros e He NX [E|X]; [| exact (NX X)]. apply NDH. apply in_or_app; left. rewrite <- E in He. exact (in_map fst _ _ He). }
      assert (NYX : forall e, In e (mbio_ent KY maxY) -> ~ In e (mbio_ent KX maxX)).
      { intros e He X. exact (DJX (fst e) (in_map fst _ _ X) ltac:(apply in_or_app; left; apply in_or_app; left; exact (in_map fst _ _ He))). }
      assert (NNX : ~ In (namev, nn) (mbio_ent KX maxX)) by (intros X; exact (DJX namev (in_map fst _ _ X) ltac:(apply in_or_app; left; apply in_or_app; right; left; reflexivity))).
      assert (NCX : ~ In (ctxv, ECTX) (mbio_ent KX maxX)) by (intros X; exact (DJX ctxv (in_map fst _ _ X) ltac:(apply in_or_app; left; apply in_or_app; right; right; left; reflexivity))).
      assert (NDX : ~ In (DT, dlen) ((HD, lenX + 1) :: mbio_ent KX maxX)).
      { intros [E|X]; [apply NDT; left; injection E as E1 E2; exact E1|]. apply NDT. right. apply in_or_app; left. exact (in_map fst _ _ (XC _ X)). }
      assert (NIE6 : ~ In (e_E RT en, 904) ((HD, lenX + 1) :: mbio_ent KX maxX)).
      { intros [E|X].
        - apply (CFR5 (HD, lenX + 1) ltac:(right; left; reflexivity)). cbn [fst]. injection E as E1 E2. rewrite E1. exact (in_map fst _ _ INE).
        - apply (NTL5 (e_E RT en, 904) (or_introl eq_refl)). apply in_or_app; right. exact (in_map fst _ _ (SUB4 _ (XC _ X))). }
      assert (CK6 : forall p n bs, In (p, n) ((DT, dlen) :: (HD, lenX + 1) :: (mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(namev, nn); (ctxv, ECTX)])) -> ~ In (p, n) ((HD, lenX + 1) :: mbio_ent KX maxX) -> 0 < n ->
                rw_cells asegs m5 p [CB (Z.to_nat n) bs] -> rw_cells asegs m6 p [CB (Z.to_nat n) bs]).
      { intros p n bs Hin NX POS C. eapply rw_cells_agree_nw; [exact C|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha.
        assert (Ha' : p <= bv_unsigned a < p + n) by (clear - Ha POS; lia).
        apply PR6; [exact (acl_live _ _ _ p n _ (CLV5 _ (Permutation_in _ HPX Hin)) Ha')|].
        exact (com_cur_outX RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ4 m5 off _ _ _ _ _ COM5x KWL6 (p, n) _ (Permutation_in _ HPX Hin) NX Ha'). }
      assert (REST6 : errst_at_rest (e_E RT en) [] m6).
      { apply (errst_rest_agree m5 m6 _ _ REST5). intros a Ha. destruct (errst_fp_where _ _ _ Ha) as [R | (p & n & [] & _)].
        apply PR6; [apply (acl_live _ _ _ (e_E RT en) 904); [exact (ELV5 _ INE)| exact R]| exact (KWL6 (e_E RT en) 904 _ (ELV5 _ INE) NIE6 R)]. }
      pose proof (pem_frame_keep RT en m5 m6 _ _ _ j0 lH (loc_F RT en) endv eH eD x1 x2 gap PFR5 PR6 PD TOP KWS6) as PFR6.
      pose proof (ff_keep m5 m6 (e_f RT en) _ _ _ _ hj (wz dlen) j1 tav j2 (wz BMY) j3 FFC5 PR6 INF4 KWFF6) as FFC6.
      pose proof (CK6 ctxv ECTX cj (SUB4 _ HCX) (NIN6 _ HCX NCX) ltac:(unfold ECTX; clear; lia) CTX5) as CTX6.
      pose proof (CK6 namev nn bn (SUB4 _ HNM) (NIN6 _ HNM NNX) ltac:(clear - NN; lia) NMC5) as NMC6.
      pose proof (CK6 DT dlen djunk ltac:(left; reflexivity) NDX ltac:(clear - DLB; lia) DTC5) as DTC6.
      assert (MBY6 : mbio_repx (rt_live RT Σ6) m6 KY dBv BMY (wz dlen) methY lenY maxY 0).
      { eapply (mbio_repx_keep (rt_live RT Σ4)); [exact MBY5| exact PR6| intros e He; split; [| apply LIN6]; apply CLV5; apply (Permutation_in _ HPX); exact (SUB4 _ (YC _ He))|].
        intros e x He Hx. exact (com_cur_outX RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ4 m5 off _ _ _ _ _ COM5x KWL6 e x (Permutation_in _ HPX (SUB4 _ (YC _ He))) (NIN6 _ (YC _ He) (NYX _ He)) Hx). }
      pose proof (com_out_agree RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ4 m5 m6 off _ _ _ _ _ COM5x KWS6 KWFR6 PR6) as AGP6.
      assert (G8 : forall P vv, In P [e_PN RT en; e_PH RT en; e_PD RT en; e_PLN RT en] -> rw_cells asegs m5 P [C8 vv] -> rw_cells asegs m6 P [C8 vv]).
      { intros P vv HPP C. eapply rw_cells_agree_nw; [exact C|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. exact (AGP6 P HPP). }
      pose proof (G8 _ _ ltac:(left; reflexivity) CN5) as CN6. pose proof (G8 _ _ ltac:(right; left; reflexivity) CH5) as CH6.
      pose proof (G8 _ _ ltac:(do 2 right; left; reflexivity) CD5) as CD6. pose proof (G8 _ _ ltac:(do 3 right; left; reflexivity) CL5) as CL6.
      pose proof (com_perm RT libenv FZ_SITES FZ_CALLS en Σ6 m6 off _ _ _ _ COM6x (Permutation_sym HPX)) as COM6.
      clear COM5 COM5x REST5 PFR5 FFC5 CTX5 NMC5 MBX5 MBY5 CN5 CH5 CD5 CL5 HDC5 DTC5 PR6 WOK6 KWS6 KWFR6 KWFF6 KWSH6 KWL6 KWP6 AGP6 G8 CK6 MI5 MI5' ST5 ST5' ART5.
      pose proof COM6 as (_ & MI6 & _).
      (* [comment removed for export] *)
      pose proof (dc4_walk (e_sp1 RT en) (e_gp RT en) v0 v1 v2 (e_sp RT en) h1 h2 h3 h4 h5 h6 h7 s2 (wz dBv) s5 s6 (wz hBv) (wz (shad (e_f RT en))) (wz SHB)
                    (wz namev) (wz ctxv) v3 v4 v5 v6 F6 fc6 m6 lenX ltac:(clear - X1 X2 X3; lia) MI6) as W.
      cl_lift W Hc8 c9 Hc9. destruct (ASTA_unpack RT Σ6 _ _ c9 Hc9) as (ms9 & (-> & _) & Hc9'). clear Hc9 Hc8.
      assert (FRS6' : rt_frames RT Σ6 = rt_frames RT Σ) by (rewrite FRS6; exact FRS4').
      rewrite Z.add_0_l in MBX6. rewrite <- LV6 in MBX6.
      exact (DC5K Σ6 m6 F6 fc6 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ BMX lenX DT hj6 djunk c9 COM6 FRS6' ltac:(unfold C_END; clear - REM MNY MDY MNX; lia)
               REST6 PFR6 FFC6 CTX6 NMC6 MBX6 MBY6 CN6 CH6 CD6 CL6 LHJ6 HDC6 LDJ DTC6 ltac:(clear - D0T D47 DLB; lia) Hc9').
Qed.
End CDec.
