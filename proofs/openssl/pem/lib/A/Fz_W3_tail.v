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

Section CTail.
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
Hypothesis C_PF : pem_free_stmt RT libenv FZ_SITES FZ_CALLS.
Hypothesis C_PFN : pem_free_null_stmt RT libenv FZ_SITES FZ_CALLS.
Hypothesis RL : RELOAD_stmt RT libenv errst_at_rest errst_live FZ_SITES FZ_CALLS.

Local Notation pem_entry := (pem_entry RT).
Local Notation pem_com := (pem_com RT libenv FZ_SITES FZ_CALLS).
Local Notation pem_frame := (pem_frame RT).
Local Notation pem_ms := (pem_ms RT).

(* [comment removed for export] *)
Lemma out_factsT : forall (en : pem_entry) Σ (m : mem) off crem lrem cur P f k,
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
Lemma rest_keepT : forall (en : pem_entry) Σ Σ' (m m' : mem) off crem lrem cur,
  pem_com en Σ m off crem lrem cur -> errst_at_rest (e_E RT en) [] m -> rt_pres_fp (rt_live RT Σ') (rt_frames RT Σ) (e_sp1 RT en) (lib_W (e_LBL RT en)) m m' ->
  In (e_E RT en, 904) (rt_live RT Σ') -> errst_at_rest (e_E RT en) [] m'.
Proof using AF AFP errst_rest_agree errst_fp_where.
  intros en Σ Σ' m m' off crem lrem cur COM REST PR INE'. apply (errst_rest_agree m m' _ _ REST). intros a Ha.
  destruct (errst_fp_where _ _ _ Ha) as [R | (p & n & [] & _)].
  apply PR; [apply (acl_live _ _ _ (e_E RT en) 904); [exact INE' | exact R] | exact (com_E_out RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem cur COM _ R)].
Qed.

(* [comment removed for export] *)
Theorem OUTFREE_proof : OUTFREE_stmt RT libenv errst_at_rest errst_live FZ_SITES FZ_CALLS.
Proof.
  intros en Σ m off crem lrem j0 lH endv x1 x2 gap hj lenv j1 tav j2 bmv j3 cj F fc eH eD xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 t3 t4 t5 t6
         ohdr ctxv namev nn hBv dBv HD nh bn bh KX KY BMX BMY methX methY lenX maxX offX lenY maxY offY blwX blwY.
  cbv zeta. intros COM REST REM PFR FFC CAL LCJ CTX NMA NN BNL NMC HIN OH MBX MBY CN CH CD CL. unfold pem_at, cps. intros T c HA Hk.
  pose proof COM as (ART0 & MI & ST & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & NTL & MB & OFF & BLT & KLV & PERM & CFR & ND & LPOS
     & FRS & FRN & SP0 & CG & LIV & LR0 & CR & CR0 & CRE & CGH & CGS & CTX0 & UWC & F0 & F64 & FTOP & FSEG & FSH & FFS & SAVED & PRES & FLR & NDO & OUTS & FDO & MST).
  destruct (com_lists RT libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ COM) as [ELV CLV].
  assert (HLO : e_lo RT en <= e_sp1 RT en) by (clear - LOR; unfold RT_STACK, PEM_CALLEE_STACK in *; lia).
  assert (SP0' : 0 <= e_sp1 RT en) by (clear - HLO HLOS; lia). assert (SPH : e_sp1 RT en + 368 <= 2 ^ 47) by (clear - TOP PD; unfold e_sp1, USTACK_TOP in *; lia).
  assert (INF : In (e_f RT en, 1%nat) (rt_frames RT Σ)) by (rewrite FRS; left; reflexivity).
  pose proof (af_frames_range RT AF Σ m _ _ ART0 INF) as (_ & FLO & _ & _). change (fs_size 1) with 128 in FLO.
  assert (FH : e_f RT en + 128 <= e_lo RT en) by (clear - FLO LOW; lia).
  set (L3 := mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(namev, nn); (ctxv, ECTX)]) in *.
  assert (HNM : In (namev, nn) L3) by (unfold L3; do 2 (apply in_or_app; right); left; reflexivity).
  assert (HCX : In (ctxv, ECTX) L3) by (unfold L3; do 2 (apply in_or_app; right); right; left; reflexivity).
  assert (YC : forall e, In e (mbio_ent KY maxY) -> In e L3) by (intros e He; unfold L3; apply in_or_app; right; apply in_or_app; left; exact He).
  assert (XC : forall e, In e (mbio_ent KX maxX) -> In e L3) by (intros e He; unfold L3; apply in_or_app; left; exact He).
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
  pose proof (out_factsT en Σ m off crem lrem _ _ _ _ COM HFN N1 N2) as (PN0 & PNS & PSN & SRN & PNF & PNL).
  pose proof (out_factsT en Σ m off crem lrem _ _ _ _ COM HFH H1 H2) as (PH0 & PHS & PSH & SRH & PHF & PHL).
  pose proof (out_factsT en Σ m off crem lrem _ _ _ _ COM HFD D1 D2) as (PD0 & PDS & PSD & SRD & PDF & PDL).
  pose proof (out_factsT en Σ m off crem lrem _ _ _ _ COM HFL L1 L2) as (PL0 & PLS & PSL & SRL & PLF & PLL).
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
  assert (KEEPF : forall Σa Σb (ma mb : mem) cura vN vH vD vL,
    pem_com en Σa ma off crem lrem cura -> (forall e, In e L3 -> In e cura) -> rt_frames RT Σa = rt_frames RT Σ ->
    rt_pres_fp (rt_live RT Σb) (rt_frames RT Σa) (e_sp1 RT en) (lib_W (e_LBL RT en)) ma mb -> (forall e, In e (L3 ++ e_live RT en) -> In e (rt_live RT Σb)) ->
    errst_at_rest (e_E RT en) [] ma -> pem_frame en ma j0 lH (loc_F RT en) endv eH eD x1 x2 gap -> rw_cells asegs ma (e_f RT en) (ff_cells hj lenv j1 tav j2 bmv j3) ->
    rw_cells asegs ma ctxv [CB (Z.to_nat ECTX) cj] -> rw_cells asegs ma namev [CB (Z.to_nat nn) bn] ->
    mbio_repx (rt_live RT Σa) ma KX hBv BMX blwX methX lenX maxX offX -> mbio_repx (rt_live RT Σa) ma KY dBv BMY blwY methY lenY maxY offY ->
    rw_cells asegs ma (e_PN RT en) [C8 vN] -> rw_cells asegs ma (e_PH RT en) [C8 vH] -> rw_cells asegs ma (e_PD RT en) [C8 vD] -> rw_cells asegs ma (e_PLN RT en) [C8 vL] ->
       errst_at_rest (e_E RT en) [] mb /\ pem_frame en mb j0 lH (loc_F RT en) endv eH eD x1 x2 gap /\ rw_cells asegs mb (e_f RT en) (ff_cells hj lenv j1 tav j2 bmv j3)
    /\ rw_cells asegs mb ctxv [CB (Z.to_nat ECTX) cj] /\ rw_cells asegs mb namev [CB (Z.to_nat nn) bn]
    /\ mbio_repx (rt_live RT Σb) mb KX hBv BMX blwX methX lenX maxX offX /\ mbio_repx (rt_live RT Σb) mb KY dBv BMY blwY methY lenY maxY offY
    /\ rw_cells asegs mb (e_PN RT en) [C8 vN] /\ rw_cells asegs mb (e_PH RT en) [C8 vH] /\ rw_cells asegs mb (e_PD RT en) [C8 vD] /\ rw_cells asegs mb (e_PLN RT en) [C8 vL]).
  { intros Σa Σb ma mb cura vN vH vD vL COMa SUB FRSa PR LIN RESTa PFRa FFCa CTXa NMCa MBXa MBYa CNa CHa CDa CLa.
    destruct (com_lists RT libenv FZ_SITES FZ_CALLS en Σa ma off crem lrem _ COMa) as [ELVa CLVa].
    pose proof (com_W_ok RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σa ma off crem lrem _ COMa) as (HWS & HWFR & HWFF & HWF & HWL & HWP).
    assert (INFa : In (e_f RT en, 1%nat) (rt_frames RT Σa)) by (rewrite FRSa; exact INF).
    assert (LINc : forall e, In e L3 -> In e (rt_live RT Σb)) by (intros e He; apply LIN; apply in_or_app; left; exact He).
    split; [exact (rest_keepT en Σa Σb ma mb off crem lrem _ COMa RESTa PR (LIN _ ltac:(apply in_or_app; right; exact INE)))|].
    split; [exact (pem_frame_keep RT en ma mb _ _ _ j0 lH (loc_F RT en) endv eH eD x1 x2 gap PFRa PR PD TOP HWS)|].
    split; [exact (ff_keep ma mb (e_f RT en) _ _ _ _ hj lenv j1 tav j2 bmv j3 FFCa PR INFa HWFF)|].
    assert (CK : forall p n bs, In (p, n) L3 -> 0 < n -> rw_cells asegs ma p [CB (Z.to_nat n) bs] -> rw_cells asegs mb p [CB (Z.to_nat n) bs]).
    { intros p n bs Hin POS C. eapply rw_cells_agree_nw; [exact C|]. intros a Ha.
      apply (com_cur_agree RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σa ma mb off crem lrem _ _ _ _ (p, n) COMa HWL (fun e H => or_intror H) PR (SUB _ Hin) (LINc _ Hin)).
      cbn [fst snd]. cbn [cells_size csize Nat.add] in Ha. clear - Ha POS. lia. }
    split; [exact (CK ctxv ECTX cj HCX ltac:(unfold ECTX; clear; lia) CTXa)|]. split; [exact (CK namev nn bn HNM ltac:(clear - NN; lia) NMCa)|].
    split. { eapply (mbio_repx_keep (rt_live RT Σa)); [exact MBXa| exact PR| intros e He; split; [apply LINc| apply LINc]; exact (XC _ He)|].
             intros e x He Hx. exact (com_cur_out RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σa ma off crem lrem _ _ _ COMa HWL (fun e0 H0 => or_intror H0) e x (SUB _ (XC _ He)) Hx). }
    split. { eapply (mbio_repx_keep (rt_live RT Σa)); [exact MBYa| exact PR| intros e He; split; [apply LINc| apply LINc]; exact (YC _ He)|].
             intros e x He Hx. exact (com_cur_out RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σa ma off crem lrem _ _ _ COMa HWL (fun e0 H0 => or_intror H0) e x (SUB _ (YC _ He)) Hx). }
    pose proof (com_out_agree RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σa ma mb off crem lrem _ _ _ COMa HWS HWFR PR) as AGP.
    assert (G8 : forall P vv, In P [e_PN RT en; e_PH RT en; e_PD RT en; e_PLN RT en] -> rw_cells asegs ma P [C8 vv] -> rw_cells asegs mb P [C8 vv]).
    { intros P vv HPP C. eapply rw_cells_agree_nw; [exact C|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. exact (AGP P HPP). }
    split; [apply G8; [left; reflexivity| exact CNa]|]. split; [apply G8; [right; left; reflexivity| exact CHa]|].
    split; [apply G8; [do 2 right; left; reflexivity| exact CDa]| apply G8; [do 3 right; left; reflexivity| exact CLa]]. }
  (* [comment removed for export] *)
  assert (KEEPW : forall Σa (ma mb : mem) lo hi Q1 Q2 Q3 v1 v2 v3,
    pem_com en Σa ma off crem lrem L3 -> munch [(lo, hi)] ma mb ->
    hi <= e_lo RT en -> (hi <= e_f RT en \/ e_f RT en + 128 <= lo) ->
    (forall p n, In (p, n) (rt_live RT Σa) -> hi <= p \/ p + n <= lo) ->
    (hi <= Q1 \/ Q1 + 8 <= lo) -> (hi <= Q2 \/ Q2 + 8 <= lo) -> (hi <= Q3 \/ Q3 + 8 <= lo) ->
    errst_at_rest (e_E RT en) [] ma -> pem_frame en ma j0 lH (loc_F RT en) endv eH eD x1 x2 gap -> rw_cells asegs ma (e_f RT en) (ff_cells hj lenv j1 tav j2 bmv j3) ->
    rw_cells asegs ma ctxv [CB (Z.to_nat ECTX) cj] -> rw_cells asegs ma namev [CB (Z.to_nat nn) bn] ->
    mbio_repx (rt_live RT Σa) ma KX hBv BMX blwX methX lenX maxX offX -> mbio_repx (rt_live RT Σa) ma KY dBv BMY blwY methY lenY maxY offY ->
    rw_cells asegs ma Q1 [C8 v1] -> rw_cells asegs ma Q2 [C8 v2] -> rw_cells asegs ma Q3 [C8 v3] ->
       errst_at_rest (e_E RT en) [] mb /\ pem_frame en mb j0 lH (loc_F RT en) endv eH eD x1 x2 gap /\ rw_cells asegs mb (e_f RT en) (ff_cells hj lenv j1 tav j2 bmv j3)
    /\ rw_cells asegs mb ctxv [CB (Z.to_nat ECTX) cj] /\ rw_cells asegs mb namev [CB (Z.to_nat nn) bn]
    /\ mbio_repx (rt_live RT Σa) mb KX hBv BMX blwX methX lenX maxX offX /\ mbio_repx (rt_live RT Σa) mb KY dBv BMY blwY methY lenY maxY offY
    /\ rw_cells asegs mb Q1 [C8 v1] /\ rw_cells asegs mb Q2 [C8 v2] /\ rw_cells asegs mb Q3 [C8 v3]).
  { intros Σa ma mb lo hi Q1 Q2 Q3 v1 v2 v3 COMa MU PxS PxF PxL A1 A2 A3 RESTa PFRa FFCa CTXa NMCa MBXa MBYa C1 C2 C3.
    destruct (com_lists RT libenv FZ_SITES FZ_CALLS en Σa ma off crem lrem _ COMa) as [ELVa CLVa].
    assert (OUT1 : forall x, ~ (lo <= x < hi) -> outside [(lo, hi)] x) by (intros x Hx; cbn [outside]; split; [exact Hx| exact I]).
    assert (PR : rt_pres_fp (rt_live RT Σa) (rt_frames RT Σa) (e_sp1 RT en) [(lo, hi)] ma mb) by (intros a _ Ho; exact (MU a Ho)).
    assert (BK : forall p n cs, In (p, n) (rt_live RT Σa) -> Z.of_nat (cells_size cs) <= n -> rw_cells asegs ma p cs -> rw_cells asegs mb p cs).
    { intros p n cs Hin SZ C. eapply rw_cells_agree_nw; [exact C|]. intros a Ha. apply MU. apply OUT1. destruct (PxL p n Hin) as [Q|Q]; clear - Q Ha SZ; lia. }
    split. { apply (errst_rest_agree ma mb _ _ RESTa). intros a Ha. destruct (errst_fp_where _ _ _ Ha) as [R | (p & n & [] & _)].
             apply MU. apply OUT1. destruct (PxL _ _ (ELVa _ INE)) as [Q|Q]; clear - Q R; lia. }
    split; [exact (pem_frame_keep RT en ma mb _ _ _ j0 lH (loc_F RT en) endv eH eD x1 x2 gap PFRa PR PD TOP (fun x Hx => OUT1 x ltac:(clear - Hx PxS HLO; lia)))|].
    assert (SZF : Z.of_nat (cells_size (ff_cells hj lenv j1 tav j2 bmv j3)) = 120) by reflexivity.
    split. { eapply rw_cells_agree_nw; [exact FFCa|]. rewrite SZF. intros a Ha. apply MU. apply OUT1. clear - Ha PxF. lia. }
    assert (SZC : Z.of_nat (cells_size [CB (Z.to_nat ECTX) cj]) <= ECTX) by (cbn [cells_size csize Nat.add]; unfold ECTX; clear; lia).
    assert (SZN : Z.of_nat (cells_size [CB (Z.to_nat nn) bn]) <= nn) by (cbn [cells_size csize Nat.add]; clear - NN; lia).
    split; [exact (BK ctxv ECTX _ (CLVa _ HCX) SZC CTXa)|]. split; [exact (BK namev nn _ (CLVa _ HNM) SZN NMCa)|].
    split. { eapply (mbio_repx_keep (rt_live RT Σa)); [exact MBXa| exact PR| intros e He; split; apply CLVa; exact (XC _ He)|].
             intros [p n] x He Hx. cbn [fst snd] in Hx. apply OUT1. destruct (PxL p n (CLVa _ (XC _ He))) as [Q|Q]; clear - Q Hx; lia. }
    split. { eapply (mbio_repx_keep (rt_live RT Σa)); [exact MBYa| exact PR| intros e He; split; apply CLVa; exact (YC _ He)|].
             intros [p n] x He Hx. cbn [fst snd] in Hx. apply OUT1. destruct (PxL p n (CLVa _ (YC _ He))) as [Q|Q]; clear - Q Hx; lia. }
    assert (OK8 : forall Q vv, (hi <= Q \/ Q + 8 <= lo) -> rw_cells asegs ma Q [C8 vv] -> rw_cells asegs mb Q [C8 vv]).
    { intros Q vv AQ C. eapply rw_cells_agree_nw; [exact C|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. intros a Ha. apply MU. apply OUT1. clear - Ha AQ. lia. }
    split. { exact (OK8 _ _ A1 C1). } split. { exact (OK8 _ _ A2 C2). } exact (OK8 _ _ A3 C3). }
  (* [comment removed for export] *)
  assert (K1 : forall Σ1 (m1 : mem) (F1 : bvmap 5 word) (fc1 : bv 32) (v y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 : word) c2,
    pem_com en Σ1 m1 off crem lrem L3 -> rt_frames RT Σ1 = rt_frames RT Σ ->
    errst_at_rest (e_E RT en) [] m1 -> pem_frame en m1 j0 lH (loc_F RT en) endv eH eD x1 x2 gap -> rw_cells asegs m1 (e_f RT en) (ff_cells hj lenv j1 tav j2 bmv j3) ->
    rw_cells asegs m1 ctxv [CB (Z.to_nat ECTX) cj] -> rw_cells asegs m1 namev [CB (Z.to_nat nn) bn] ->
    mbio_repx (rt_live RT Σ1) m1 KX hBv BMX blwX methX lenX maxX offX -> mbio_repx (rt_live RT Σ1) m1 KY dBv BMY blwY methY lenY maxY offY ->
    rw_cells asegs m1 (e_PN RT en) [C8 (wz 0)] -> rw_cells asegs m1 (e_PH RT en) [C8 (wz HD)] -> rw_cells asegs m1 (e_PD RT en) [C8 (wz 0)] -> rw_cells asegs m1 (e_PLN RT en) [C8 (wz 0)] ->
    ASTA RT Σ1 (e_PMc RT en) (eq (pem_ms en SITE_of_pf1 m1 F1 fc1 (wz SITE_of_pf1) y0 y1 y2 v b1 b2 b3 b4 b5 b6 b7 s2 (wz dBv) s4 s5 s6 (wz hBv) (wz namev) (wz ctxv) y3 y4 y5 y6)) c2 ->
    realizes asegs c2 T).
  { intros Σ1 m1 F1 fc1 v y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 c2 COM1 FRS1 REST1 PFR1 FFC1 CTX1 NMC1 MBX1 MBY1 CN1 CH1 CD1 CL1 Hc2.
    pose proof COM1 as (ART1 & MI1 & ST1 & _). destruct (com_lists RT libenv FZ_SITES FZ_CALLS en Σ1 m1 off crem lrem _ COM1) as [ELV1 CLV1].
    pose proof (out_factsT en Σ1 m1 off crem lrem _ _ _ _ COM1 HFH H1 H2) as (_ & _ & _ & _ & _ & PHL1).
    (* [comment removed for export] *)
    pose proof PFR1 as (_ & _ & _ & _ & _ & _ & FRE1 & _). unfold loc_E in FRE1.
    pose proof (out_sh0 RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ1 m1 off crem lrem _ (e_PH RT en) fH kH COM1 ltac:(right; left; reflexivity) HFH H1 H2 HB) as SHP1.
    pose proof (out_sh0 RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ1 m1 off crem lrem _ (e_PD RT en) fD kD COM1 ltac:(do 2 right; left; reflexivity) HFD D1 D2 DB) as SHD1.
    pose proof (of1_walk (e_sp1 RT en) (e_gp RT en) y0 y1 y2 (e_sp RT en) v b1 b2 b3 b4 b5 b6 b7 s2 (wz dBv) s4 s5 s6 (wz hBv) (wz (shad (e_f RT en))) (wz SHB) (wz namev) (wz ctxv) y3 y4 y5 y6 F1 fc1 m1
                  (e_PD RT en) (e_PH RT en) (e_PN RT en) (e_f RT en) eH eD (e_flags RT en) (e_PLN RT en) (e_BI RT en) 0 (wz HD)
                  SP0' SPH MI1 FRE1 SHP1 CH1 PH0 ltac:(clear - PHS HLO; lia) SRH PSH SHD1 CD1 PD0 ltac:(clear - PDS HLO; lia) SRD AHD ltac:(clear; lia)) as W.
    cl_lift W Hc2 c3 Hc3. destruct (ASTA_unpack RT Σ1 _ _ c3 Hc3) as (ms3 & (m2 & -> & MU2 & WM2 & MI2 & CH2) & Hc3'). clear Hc3 Hc2.
    assert (ST2 : stk asegs m2 (e_lo RT en) (e_sp1 RT en)) by (eapply stk_munch; [exact ST1| exact MU2| exact WM2|]; intros x Hx; cbn [outside]; split; [clear - Hx PHS; lia| exact I]).
    pose proof (com_out_store RT AF GOBJ AFP libenv libenv_fp libenv_agree libenv_fp_where FZ_SITES FZ_CALLS en Σ1 m1 m2 off crem lrem _ (e_PH RT en) fH kH COM1 ltac:(right; left; reflexivity) HFH H1 H2 MU2 WM2 MI2 ST2) as COM2.
    destruct (KEEPW Σ1 m1 m2 (e_PH RT en) (e_PH RT en + 8) (e_PN RT en) (e_PD RT en) (e_PLN RT en) (wz 0) (wz 0) (wz 0) COM1 MU2 PHS PHF PHL1 ltac:(clear - AHN; lia) AHD AHL
                REST1 PFR1 FFC1 CTX1 NMC1 MBX1 MBY1 CN1 CD1 CL1) as (REST2 & PFR2 & FFC2 & CTX2 & NMC2 & MBX2 & MBY2 & CN2 & CD2 & CL2).
    clear COM1 REST1 PFR1 FFC1 CTX1 NMC1 MBX1 MBY1 CN1 CH1 CD1 CL1 MU2 WM2 MI1 ST1 ST2 FRE1 SHP1 SHD1 ART1 ELV1 CLV1 PHL1.
    (* [comment removed for export] *)
    eapply (pem_call_pfree_null RT AF GOBJ AFP libenv libenv_fp libenv_agree libenv_fp_where FZ_SITES FZ_CALLS C_PFN T en Σ1 m2 off crem lrem L3 0 SITE_of_pf2 F1 fc1
              y0 y1 y2 (wz 1021) b4 b5 b6 b7 s2 (wz dBv) s4 s5 s6 (wz hBv) (wz namev) (wz ctxv) y3 y4 y5 y6 c3 COM2 ltac:(clear; lia)
              ltac:(unfold PEM_RAS_pfree, SITE_of_pf2; do 6 right; left; reflexivity) Hc3').
    clear Hc3'. intros Σ3 m3 F3 fc3 v3 z0 z1 z2 d1 d2 d3 d4 d5 d6 d7 z3 z4 z5 z6 c4 COM3 LV3 FRS3 PR3 Hc4.
    assert (FRS3' : rt_frames RT Σ3 = rt_frames RT Σ) by (rewrite FRS3; exact FRS1).
    assert (LIN3 : forall e, In e (L3 ++ e_live RT en) -> In e (rt_live RT Σ3)).
    { intros e He. rewrite LV3. destruct (com_lists RT libenv FZ_SITES FZ_CALLS en Σ1 m2 off crem lrem _ COM2) as [ELV2 CLV2].
      apply in_app_iff in He. destruct He as [He|He]; [exact (CLV2 _ He)| exact (ELV2 _ He)]. }
    destruct (KEEPF Σ1 Σ3 m2 m3 L3 _ _ _ _ COM2 (fun e He => He) FRS1 PR3 LIN3 REST2 PFR2 FFC2 CTX2 NMC2 MBX2 MBY2 CN2 CH2 CD2 CL2)
      as (REST3 & PFR3 & FFC3 & CTX3 & NMC3 & MBX3 & MBY3 & CN3 & CH3 & CD3 & CL3).
    clear COM2 REST2 PFR2 FFC2 CTX2 NMC2 MBX2 MBY2 CN2 CH2 CD2 CL2 PR3 MI2.
    pose proof COM3 as (ART3 & MI3 & ST3 & _).
    pose proof (out_factsT en Σ3 m3 off crem lrem _ _ _ _ COM3 HFD D1 D2) as (_ & _ & _ & _ & _ & PDL3).
    (* [comment removed for export] *)
    pose proof PFR3 as (_ & _ & _ & _ & _ & _ & FRE3 & _). unfold loc_E in FRE3.
    pose proof (out_sh0 RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ3 m3 off crem lrem _ (e_PD RT en) fD kD COM3 ltac:(do 2 right; left; reflexivity) HFD D1 D2 DB) as SHD3.
    pose proof (of2_walk (e_sp1 RT en) (e_gp RT en) z0 z1 z2 (e_sp RT en) v3 d1 d2 d3 d4 d5 d6 d7 s2 (wz dBv) s4 s5 s6 (wz hBv) (wz (shad (e_f RT en))) (wz SHB) (wz namev) (wz ctxv) z3 z4 z5 z6 F3 fc3 m3
                  (e_PD RT en) (e_PH RT en) (e_PN RT en) (e_f RT en) eH eD (e_flags RT en) (e_PLN RT en) (e_BI RT en) (wz 0)
                  SP0' SPH MI3 FRE3 SHD3 CD3 PD0 ltac:(clear - PDS HLO; lia) SRD PSD) as W.
    cl_lift W Hc4 c5 Hc5. destruct (ASTA_unpack RT Σ3 _ _ c5 Hc5) as (ms5 & (m4 & -> & MU4 & WM4 & MI4 & CD4) & Hc5'). clear Hc5 Hc4.
    assert (ST4 : stk asegs m4 (e_lo RT en) (e_sp1 RT en)) by (eapply stk_munch; [exact ST3| exact MU4| exact WM4|]; intros x Hx; cbn [outside]; split; [clear - Hx PDS; lia| exact I]).
    pose proof (com_out_store RT AF GOBJ AFP libenv libenv_fp libenv_agree libenv_fp_where FZ_SITES FZ_CALLS en Σ3 m3 m4 off crem lrem _ (e_PD RT en) fD kD COM3 ltac:(do 2 right; left; reflexivity) HFD D1 D2 MU4 WM4 MI4 ST4) as COM4.
    destruct (KEEPW Σ3 m3 m4 (e_PD RT en) (e_PD RT en + 8) (e_PN RT en) (e_PH RT en) (e_PLN RT en) (wz 0) (wz 0) (wz 0) COM3 MU4 PDS PDF PDL3 ltac:(clear - ADN; lia) ltac:(clear - AHD; lia) ADL
                REST3 PFR3 FFC3 CTX3 NMC3 MBX3 MBY3 CN3 CH3 CL3) as (REST4 & PFR4 & FFC4 & CTX4 & NMC4 & MBX4 & MBY4 & CN4 & CH4 & CL4).
    clear COM3 REST3 PFR3 FFC3 CTX3 NMC3 MBX3 MBY3 CN3 CH3 CD3 CL3 MU4 WM4 MI3 ST3 ST4 FRE3 SHD3 ART3 PDL3.
    (* [comment removed for export] *)
    assert (HPR : Permutation L3 ((mbio_ent KX maxX ++ mbio_ent KY maxY ++ opt_ent (Some (ctxv, ECTX)) ++ opt_ent (Some (namev, nn))) ++ [] ++ [])).
    { unfold L3. cbn [opt_ent app]. rewrite !app_nil_r. do 2 apply Permutation_app_head. apply perm_swap. }
    pose proof (com_perm RT libenv FZ_SITES FZ_CALLS en Σ3 m4 off crem lrem _ _ COM4 HPR) as COM4'.
    pose proof (rw_cells_bound asegs m4 namev _ NMC4) as [NB1 NB2].
    eapply (RL en Σ3 m4 off crem lrem [] [] j0 lH (loc_F RT en) endv x1 x2 gap hj lenv j1 tav j2 bmv j3 F3 fc3 eH eD (wz SITE_of_pf2) z0 z1 z2
              (wz (e_PD RT en)) d1 d2 d3 d4 d5 d6 d7 s2 s4 s6 z3 z4 z5 z6 (Some (ctxv, ECTX)) (Some (namev, nn)) ctxv namev nn hBv dBv 0
              KX KY BMX BMY methX methY lenX maxX offX lenY maxY offY blwX blwY COM4');
      [| clear - REM; lia| exact PFR4| exact FFC4| reflexivity| | exact MBX4| exact MBY4| | cbn [news_sz fold_right]; clear - OFF; lia| exact Hc5'| exact Hk].
    - split; [left; split; [reflexivity| exact REST4]|]. split; [apply Forall_nil|]. split; intros e [].
    - cbv iota beta. split; [reflexivity|]. split; [clear - NN; lia|]. apply rw_cells_CB0; [exact NB1| cbn [cells_size csize Nat.add] in NB2; clear - NB2 NN; lia].
    - left. split; [reflexivity|]. split; [reflexivity|]. split; [exact CN4|]. split; [exact CH4|]. split; [exact CD4|]. exists (wz 0). exact CL4. }
  (* [comment removed for export] *)
  pose proof PFR as (_ & _ & _ & _ & _ & _ & FRE & _). unfold loc_E in FRE.
  pose proof (out_sh0 RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ (e_PH RT en) fH kH COM ltac:(right; left; reflexivity) HFH H1 H2 HB) as SHP.
  assert (HDR : 0 <= HD < 2 ^ 64).
  { destruct ohdr as [e|]; [| clear - OH; lia]. destruct OH as (-> & NH1 & _ & _ & _).
    pose proof (cur_live_facts RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ (HD, nh) COM ltac:(apply in_or_app; right; apply in_or_app; right; right; right; left; reflexivity) ltac:(cbn; clear - NH1; lia)) as (_ & HD0 & HDLO & _).
    cbn [fst snd] in HD0, HDLO. clear - HD0 HDLO HLO SPH NH1. lia. }
  pose proof (of0_walk xra (e_sp1 RT en) (e_gp RT en) t0 t1 t2 (e_sp RT en) a0 a1 a2 a3 a4 a5 a6 a7 s2 (wz dBv) s4 s5 s6 (wz hBv) (wz (shad (e_f RT en))) (wz SHB) (wz namev) (wz ctxv) t3 t4 t5 t6 F fc m
                HD (e_PD RT en) (e_PH RT en) (e_PN RT en) (e_f RT en) eH eD (e_flags RT en) (e_PLN RT en) (e_BI RT en) SP0' SPH MI FRE SHP CH PH0 ltac:(clear - PHS HLO; lia) SRH HDR) as W.
  cl_lift W HA c1 Hc1. destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (-> & _) & Hc1'). clear Hc1 HA.
  destruct ohdr as [e|].
  - (* [comment removed for export] *)
    destruct OH as (-> & NH1 & HAL & LBH & HC). cbn [opt_ent] in COM.
    assert (HP : Permutation (mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(namev, nn); (ctxv, ECTX)] ++ [(HD, nh)]) ((HD, nh) :: L3)).
    { apply Permutation_sym. eapply Permutation_trans; [apply Permutation_cons_append|]. unfold L3. rewrite <- !app_assoc. apply Permutation_refl. }
    assert (SUBs : forall e, In e L3 -> In e (mbio_ent KX maxX ++ mbio_ent KY maxY ++ [(namev, nn); (ctxv, ECTX)] ++ [(HD, nh)])) by (intros e He; exact (Permutation_in e (Permutation_sym HP) (or_intror He))).
    pose proof (com_perm RT libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ _ COM HP) as COMh.
    eapply (pem_call_pfree RT AF GOBJ AFP libenv libenv_fp libenv_agree libenv_fp_where FZ_SITES FZ_CALLS C_PF T en Σ m off crem lrem L3 HD nh 0 SITE_of_pf1 F fc
              t0 t1 t2 (wz 1019) a4 a5 a6 a7 s2 (wz dBv) s4 s5 s6 (wz hBv) (wz namev) (wz ctxv) t3 t4 t5 t6 c1 COMh ltac:(clear - NH1; lia)
              ltac:(unfold PEM_RAS_pfree, SITE_of_pf1; do 5 right; left; reflexivity) Hc1').
    clear Hc1'. intros Σ1 m1 F1 fc1 v y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 c2 COM1 LV1 FRS1 PR1 LIN1 Hc2.
    destruct (KEEPF Σ Σ1 m m1 _ _ _ _ _ COM SUBs eq_refl PR1 LIN1 REST PFR FFC CTX NMC MBX MBY CN CH CD CL)
      as (REST1 & PFR1 & FFC1 & CTX1 & NMC1 & MBX1 & MBY1 & CN1 & CH1 & CD1 & CL1).
    exact (K1 Σ1 m1 F1 fc1 v y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 c2 COM1 FRS1 REST1 PFR1 FFC1 CTX1 NMC1 MBX1 MBY1 CN1 CH1 CD1 CL1 Hc2).
  - (* [comment removed for export] *)
    cbn [opt_ent] in COM. rewrite app_nil_r in COM. subst HD. clear ELV CLV. destruct (com_lists RT libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ COM) as [ELV CLV].
    eapply (pem_call_pfree_null RT AF GOBJ AFP libenv libenv_fp libenv_agree libenv_fp_where FZ_SITES FZ_CALLS C_PFN T en Σ m off crem lrem L3 0 SITE_of_pf1 F fc
              t0 t1 t2 (wz 1019) a4 a5 a6 a7 s2 (wz dBv) s4 s5 s6 (wz hBv) (wz namev) (wz ctxv) t3 t4 t5 t6 c1 COM ltac:(clear; lia)
              ltac:(unfold PEM_RAS_pfree, SITE_of_pf1; do 5 right; left; reflexivity) Hc1').
    clear Hc1'. intros Σ1 m1 F1 fc1 v y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 c2 COM1 LV1 FRS1 PR1 Hc2.
    assert (LIN1 : forall e, In e (L3 ++ e_live RT en) -> In e (rt_live RT Σ1)).
    { intros e He. rewrite LV1. apply in_app_iff in He. destruct He as [He|He]; [exact (CLV _ He)| exact (ELV _ He)]. }
    destruct (KEEPF Σ Σ1 m m1 _ _ _ _ _ COM (fun e He => He) eq_refl PR1 LIN1 REST PFR FFC CTX NMC MBX MBY CN CH CD CL)
      as (REST1 & PFR1 & FFC1 & CTX1 & NMC1 & MBX1 & MBY1 & CN1 & CH1 & CD1 & CL1).
    exact (K1 Σ1 m1 F1 fc1 v y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 c2 COM1 FRS1 REST1 PFR1 FFC1 CTX1 NMC1 MBX1 MBY1 CN1 CH1 CD1 CL1 Hc2).
Qed.
End CTail.
