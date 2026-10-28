(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA RzCPS NodesA SysStep Arr FarCall.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_tac Startup_glue Th_kit Fz_T_kit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs PLayout I_lkit I_ut RT_iface_pem D_libiface_pem Fz_kit Fz_ckit Fz_chk Fz_fkit Fz_env Fz_M_malloc Fz_M_free Fz_M_secure Fz_W1_defs Fz_W1_pploc Fz_W3_iface Fz_W3_defs Fz_W3_lems Fz_W3_aux.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.

Section W3X2.
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
  Hypothesis errst_live_agree : forall m m' E top bot strs, errst_live E top bot strs m -> agree_on (errst_fp E strs) m m' -> errst_live E top bot strs m'.
  Hypothesis errst_fp_where : forall E strs a, errst_fp E strs a -> (E <= a < E + 904) \/ in_live strs a.
  Variables FZ_SITES FZ_CALLS : list (Z * Z).

  Local Notation pem_entry := (pem_entry RT).
  Local Notation pem_com := (pem_com RT libenv FZ_SITES FZ_CALLS).
  Local Notation pem_err := (pem_err RT errst_at_rest errst_live).
  Local Notation pem_frame := (pem_frame RT).
  Local Notation pem_ms := (pem_ms RT).

  (* [comment removed for export] *)
  Lemma com_cur_outX : forall (en : pem_entry) Σ (m : mem) off crem lrem cur XL W,
    pem_com en Σ m off crem lrem cur -> w_live RT Σ XL W -> forall e x, In e cur -> ~ In e XL -> fst e <= x < fst e + snd e -> outside W x.
  Proof using AF AFP.
    intros en Σ m off crem lrem cur XL W COM WL e x He NX Hx.
    destruct (com_lists RT libenv FZ_SITES FZ_CALLS en Σ m off crem lrem cur COM) as [ELV CLV]. destruct e as [p n]. cbn [fst snd] in Hx.
    exact (WL p n x (CLV _ He) NX Hx).
  Qed.
  Lemma com_klv_outX : forall (en : pem_entry) Σ (m : mem) off crem lrem cur XL W,
    pem_com en Σ m off crem lrem cur -> w_live RT Σ XL W -> (forall e, In e XL -> In e ((e_E RT en, 904) :: e_LBL RT en) \/ In e cur) ->
    forall e x, In e (mbio_ent (e_K RT en) (e_bmax RT en)) -> fst e <= x < fst e + snd e -> outside W x.
  Proof using AF AFP.
    intros en Σ m off crem lrem cur XL W COM WL HXL e x He Hx.
    pose proof COM as (ART0 & MI & ST & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & NTL & MB & OFF & BLT & KLV & PERM & CFR & ND & REST).
    destruct (com_lists RT libenv FZ_SITES FZ_CALLS en Σ m off crem lrem cur COM) as [ELV CLV]. destruct e as [p n]. cbn [fst snd] in Hx.
    assert (HB : In p (mbio_blocks (e_K RT en))) by (rewrite <- (mbio_ent_fst (e_K RT en) (e_bmax RT en)); apply (in_map fst _ _ He)).
    apply (WL p n x (ELV _ (KLV _ He))); [| exact Hx]. intros X. destruct (HXL _ X) as [X2|X2].
    - apply (NTL (p, n) X2). apply in_or_app; left. exact HB.
    - pose proof (nd_split _ _ ND) as (_ & _ & DJ). exact (DJ p (in_map fst _ _ X2) ltac:(right; exact HB)).
  Qed.
  (* [comment removed for export] *)
  Lemma pem_calls_enew : forall r, In r PEM_RAS_enew -> In (r, FZ_ERR_NEW) PEM_CALLS.
  Proof. intros r Hr. unfold PEM_CALLS. rewrite !in_app_iff. do 5 right. left. apply in_map_iff. exists r. split; [reflexivity| exact Hr]. Qed.
  Lemma pem_calls_edbg : forall r, In r PEM_RAS_edbg -> In (r, FZ_ERR_SET_DEBUG) PEM_CALLS.
  Proof. intros r Hr. unfold PEM_CALLS. rewrite !in_app_iff. do 6 right. left. apply in_map_iff. exists r. split; [reflexivity| exact Hr]. Qed.
  Lemma pem_calls_eerr : forall r, In r PEM_RAS_eerr -> In (r, FZ_ERR_SET_ERROR) PEM_CALLS.
  Proof. intros r Hr. unfold PEM_CALLS. rewrite !in_app_iff. do 7 right. left. apply in_map_iff. exists r. split; [reflexivity| exact Hr]. Qed.

  (* [comment removed for export] *)
  Lemma com_sec_out : forall (en : pem_entry) Σ (m : mem) off crem lrem cur, pem_com en Σ m off crem lrem cur -> outside (pem_W RT en) SEC_INIT.
  Proof using AF AFP.
    intros en Σ m off crem lrem cur COM.
    pose proof COM as (ART0 & MI & ST & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & NTL & MB & OFF & BLT & KLV & PERM & CFR & ND & LPOS
       & FRS & FRN & SP0 & CG & LIV & LR0 & CR & CR0 & CRE & CGH & CGS & CTX & UWC & F0 & F64 & FTOP & FSEG & FSH & FFS & SAVED & PRES & FLR & NDO & OUTS & FDO & MST).
    destruct (com_lists RT libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ COM) as [ELV CLV].
    assert (HLO : e_lo RT en <= e_sp1 RT en) by (clear - LOR; unfold RT_STACK, PEM_CALLEE_STACK in *; lia).
    assert (LIVE : forall p n, In (p, n) (rt_live RT Σ) -> ~ (p <= SEC_INIT < p + n)).
    { intros p n Hin R. pose proof (af_live_range RT AF Σ m p n ART0 Hin) as (_ & _ & Y). clear - R Y. unfold SEC_INIT, SEGTOP_A in *. lia. }
    assert (GP : forall P, In P [e_PN RT en; e_PH RT en; e_PD RT en; e_PLN RT en] -> ~ (P <= SEC_INIT < P + 8)).
    { intros P HP X. pose proof OUTS as OUTS'. rewrite Forall_forall in OUTS'. destruct (proj2 (OUTS' P HP)) as [[H1 H2]|(f & k & Hin & H1 & H2 & _)].
      - exfalso. clear - H1 H2. lia.
      - pose proof (af_frames_range RT AF Σ m f k ART0 ltac:(rewrite FRS; right; exact Hin)) as (_ & _ & FS & _). pose proof (Z.shiftl_nonneg 64 (Z.of_nat k)).
        clear - H1 H2 X FS H. unfold SEC_INIT, SEGTOP_A, fs_size in *. lia. }
    unfold pem_W. apply outside_app_intro; [| apply outside_app_intro].
    - cbn. split; [exact (GP (e_PN RT en) ltac:(cbn; tauto))|]. split; [exact (GP (e_PH RT en) ltac:(cbn; tauto))|]. split; [exact (GP (e_PD RT en) ltac:(cbn; tauto))|]. split; [exact (GP (e_PLN RT en) ltac:(cbn; tauto))|].
      split; [exact (LIVE _ _ (ELV _ INE))| exact I].
    - unfold mbio_W. apply outside_intro. intros iv Hiv. apply in_map_iff in Hiv. destruct Hiv as ([p n] & <- & Hpn). cbn [fst snd]. exact (LIVE p n (ELV _ (KLV _ Hpn))).
    - unfold lib_W. apply outside_app_intro; [unfold LIB_W, SEC_INIT; cbn; repeat split; try exact I; clear; lia|].
      apply outside_intro. intros iv Hiv. apply in_map_iff in Hiv. destruct Hiv as ([p n] & <- & Hpn). cbn [fst snd]. exact (LIVE p n (ELV _ (INCL _ Hpn))).
  Qed.

  (* [comment removed for export] *)
  Lemma pem_call_enew : err_new_rest_stmt RT libenv errst_at_rest errst_live FZ_SITES FZ_CALLS ->
    forall T (en : pem_entry) Σ (m : mem) off crem lrem cur site (F : bvmap 5 word) (fc : bv 32)
           (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6 : word) c,
    pem_com en Σ m off crem lrem cur -> errst_at_rest (e_E RT en) [] m -> 1 <= crem -> In site PEM_RAS_enew ->
    ASTA RT Σ (e_PMc RT en) (eq (pem_ms en FZ_ERR_NEW m F fc (wz site) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6)) c ->
    (forall Σ' (m' : mem) (F' : bvmap 5 word) (fc' : bv 32) (v y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 : word) c',
       pem_com en Σ' m' off (crem - 1) lrem cur ->
       rt_live RT Σ' = rt_live RT Σ -> rt_frames RT Σ' = rt_frames RT Σ ->
       rt_pres_fp (rt_live RT Σ') (rt_frames RT Σ) (e_sp1 RT en) ((e_E RT en, e_E RT en + 904) :: lib_W (e_LBL RT en)) m m' ->
       errst_live (e_E RT en) 1 0 [] m' ->
       ASTA RT Σ' (e_PMc RT en) (eq (pem_ms en site m' F' fc' (wz site) y0 y1 y2 v b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s10 s11 y3 y4 y5 y6)) c' ->
       realizes asegs c' T) ->
    realizes asegs c T.
  Proof using AF AFP libenv_agree libenv_fp_where.
    intros C_EN T en Σ m off crem lrem cur site F fc t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6 c COM REST0 CRM HSI HA Hk.
    pose proof COM as (ART0 & MI & ST & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & NTL & MB & OFF & BLT & KLV & PERM & CFR & ND & LPOS
       & FRS & FRN & SP0 & CG & LIV & LR0 & CR & CR0 & CRE & CGH & CGS & CTX & UWC & F0 & F64 & FTOP & FSEG & FSH & FFS & SAVED & PRES & FLR & NDO & OUTS & FDO & MST).
    destruct (com_lists RT libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ COM) as [ELV CLV].
    pose proof (com_WE_ok RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ COM) as WOK. pose proof WOK as (HWS & HWFR & HWFF & HWF & HWL & HWP).
    assert (HSR : In site PEM_RAS) by (unfold PEM_RAS; rewrite !in_app_iff; tauto).
    assert (SR : 0 <= site < 2 ^ 64) by (clear - HSI; unfold PEM_RAS_enew in HSI; cbn in HSI; lia).
    destruct (com_call_pre RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ site FZ_ERR_NEW COM (pem_site_in _ HSR) (pem_calls_enew _ HSI) SR)
      as (EU & COK & CTX1 & UWC1 & INCL1 & FRMAX & CRED & HLO & H352).
    apply (C_EN Σ (e_PMc RT en) (wz site) (wz (e_sp1 RT en)) (e_gp RT en) (wz TP_A) t0 t1 t2 (e_sp RT en) (wz (e_sp1 RT en)) a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 (wz (shad (e_f RT en))) (wz SHB) s10 s11 t3 t4 t5 t6 F fc m (e_lo RT en) (bv_unsigned (e_ra RT en) :: e_outer RT en) (e_canary RT en)
             (e_LBL RT en) (e_E RT en) FDO MST eq_refl LE INCL1 (ELV _ INE) REST0 ART0 MI COK
             ltac:(rewrite EU; clear - LOR; unfold PEM_CALLEE_STACK, ERRN_STACK in *; lia) CLE CTX1 UWC1 CGH FRMAX ltac:(clear - CRED CRM; lia) T c HA).
    intros c' (Σ' & AP & (LV' & FRS' & SP' & CR' & CG')). unfold apost in AP.
    destruct (ASTA_unpack RT Σ' _ _ c' AP) as (ms' & (v & m' & RS & (ART1 & MI1 & ST1) & PR & CLE1 & (WM1 & LE1 & EL1)) & Hc'). clear AP.
    destruct RS as (y0 & y1 & y2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & y3 & y4 & y5 & y6 & F' & fc' & ->).
    rewrite EU in ST1, PR. rewrite (ret_pc_even site SR) in Hc' by (clear - HSI; unfold PEM_RAS_enew in HSI; cbn in HSI; lia).
    assert (SEC1 : sec_off m').
    { eapply sec_off_agree; [exact SEC|]. intros a Ea. rewrite <- (Z_to_bv_bv_unsigned a), Ea.
      apply PR; rewrite (unsigned_lit SEC_INIT) by (unfold SEC_INIT; clear; lia); [apply acl_static; apply client_static_intro; unfold SEC_INIT; clear; lia|].
      apply HWP; [apply acl_static; apply client_static_intro; unfold SEC_INIT; clear; lia| exact (com_sec_out en Σ m off crem lrem _ COM)]. }
    eapply (Hk Σ' m' F' fc' v y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 c'); [| exact LV'| exact FRS'| rewrite LV'; exact PR| exact EL1| exact Hc'].
    eapply (com_call RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ Σ' m m' off off crem (crem - 1) lrem lrem _ cur _ _ 1 COM ART1 MI1 ST1 PR CLE1 SEC1 LE1);
      [| exact OFF| exact FRS'| exact SP'| exact CG'| exact CR'| clear - CRM; lia| clear; lia| exact LR0| rewrite LV'; clear; lia
       | exact ELV| exact HWP| exact HWS| exact HWF| rewrite LV'; exact PERM| exact CFR| exact ND| rewrite LV'; exact LPOS| exact NTL].
    eapply (mbio_rep_keep (rt_live RT Σ)); [exact MB| exact PR| intros e He; rewrite LV'; split; exact (ELV _ (KLV _ He))|].
    intros e x He Hx. exact (com_klv_out RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ _ _ COM HWL (fun e H => H) e x He Hx).
  Qed.
  (* [comment removed for export] *)
  Lemma pem_call_edbg : err_set_debug_stmt RT GOBJ libenv errst_live FZ_SITES FZ_CALLS ->
    forall T (en : pem_entry) Σ (m : mem) off crem lrem cur site SF nf SN nn line (fstr nstr : list byte) (F : bvmap 5 word) (fc : bv 32)
           (t0 t1 t2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6 : word) c,
    pem_com en Σ m off crem lrem cur -> errst_live (e_E RT en) 1 0 [] m -> 2 <= crem -> 2 <= lrem -> In site PEM_RAS_edbg -> 0 <= line < 2 ^ 31 ->
    pem_lit_ok GOBJ SF nf fstr -> pem_lit_ok GOBJ SN nn nstr ->
    ASTA RT Σ (e_PMc RT en) (eq (pem_ms en FZ_ERR_SET_DEBUG m F fc (wz site) t0 t1 t2 (wz SF) (wz line) (wz SN) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6)) c ->
    (forall Σ' (m' : mem) (F' : bvmap 5 word) (fc' : bv 32) (v y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 : word) c' (QF QN : Z),
       pem_com en Σ' m' off (crem - 2) (lrem - 2) ((QN, nn) :: (QF, nf) :: cur) ->
       rt_live RT Σ' = (QN, nn) :: (QF, nf) :: rt_live RT Σ -> rt_frames RT Σ' = rt_frames RT Σ ->
       rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (e_sp1 RT en) ((e_E RT en, e_E RT en + 904) :: lib_W (e_LBL RT en)) m m' ->
       errst_live (e_E RT en) 1 0 [(QN, nn); (QF, nf)] m' -> 0 < QF -> 0 < QN ->
       ASTA RT Σ' (e_PMc RT en) (eq (pem_ms en site m' F' fc' (wz site) y0 y1 y2 v b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s10 s11 y3 y4 y5 y6)) c' ->
       realizes asegs c' T) ->
    realizes asegs c T.
  Proof using AF AFP libenv_agree libenv_fp_where.
    intros C_ED T en Σ m off crem lrem cur site SF nf SN nn line fstr nstr F fc t0 t1 t2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6 c
           COM EL0 CRM LRM HSI HLINE LITF LITN HA Hk.
    assert (BF64 : 1 < nf <= 64) by (destruct LITF as (bf & szf & slf & X); clear - X; tauto). assert (BN64 : 1 < nn <= 64) by (destruct LITN as (bn & szn & sln & X); clear - X; tauto).
    pose proof COM as (ART0 & MI & ST & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & NTL & MB & OFF & BLT & KLV & PERM & CFR & ND & LPOS
       & FRS & FRN & SP0 & CG & LIV & LR0 & CR & CR0 & CRE & CGH & CGS & CTX & UWC & F0 & F64 & FTOP & FSEG & FSH & FFS & SAVED & PRES & FLR & NDO & OUTS & FDO & MST).
    destruct (com_lists RT libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ COM) as [ELV CLV].
    pose proof (com_WE_ok RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ COM) as WOK. pose proof WOK as (HWS & HWFR & HWFF & HWF & HWL & HWP).
    assert (HSR : In site PEM_RAS) by (unfold PEM_RAS; rewrite !in_app_iff; tauto).
    assert (SR : 0 <= site < 2 ^ 64) by (clear - HSI; unfold PEM_RAS_edbg in HSI; cbn in HSI; lia).
    destruct (com_call_pre RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ site FZ_ERR_SET_DEBUG COM (pem_site_in _ HSR) (pem_calls_edbg _ HSI) SR)
      as (EU & COK & CTX1 & UWC1 & INCL1 & FRMAX & CRED & HLO & H352).
    apply (C_ED Σ (e_PMc RT en) (wz site) (wz (e_sp1 RT en)) (e_gp RT en) (wz TP_A) t0 t1 t2 (e_sp RT en) (wz (e_sp1 RT en)) (wz SF) (wz line) (wz SN) a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 (wz (shad (e_f RT en))) (wz SHB) s10 s11 t3 t4 t5 t6 F fc m (e_lo RT en) (bv_unsigned (e_ra RT en) :: e_outer RT en) (e_canary RT en)
             (e_LBL RT en) (e_E RT en) SF nf SN nn line fstr nstr FDO MST eq_refl eq_refl eq_refl eq_refl HLINE LE INCL1 (ELV _ INE) EL0 LITF LITN
             ART0 MI COK ltac:(rewrite EU; clear - LOR; unfold PEM_CALLEE_STACK, ERRD_STACK in *; lia) CLE CTX1 UWC1 CGH FRMAX ltac:(clear - LIV LRM; lia) ltac:(clear - CRED CRM; lia) T c HA).
    intros c' (Σ' & QF & QN & AP & LV' & FRS' & SP' & CR' & CG' & QF0 & QN0). unfold apost in AP.
    destruct (ASTA_unpack RT Σ' _ _ c' AP) as (ms' & (v & m' & RS & (ART1 & MI1 & ST1) & PR & CLE1 & (WM1 & LE1 & EL1)) & Hc'). clear AP.
    destruct RS as (y0 & y1 & y2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & y3 & y4 & y5 & y6 & F' & fc' & ->).
    rewrite EU in ST1, PR. rewrite (ret_pc_even site SR) in Hc' by (clear - HSI; unfold PEM_RAS_edbg in HSI; cbn in HSI; lia).
    assert (SEC1 : sec_off m').
    { eapply sec_off_agree; [exact SEC|]. intros a Ea. rewrite <- (Z_to_bv_bv_unsigned a), Ea.
      apply PR; rewrite (unsigned_lit SEC_INIT) by (unfold SEC_INIT; clear; lia); [apply acl_static; apply client_static_intro; unfold SEC_INIT; clear; lia|].
      apply HWP; [apply acl_static; apply client_static_intro; unfold SEC_INIT; clear; lia| exact (com_sec_out en Σ m off crem lrem _ COM)]. }
    (* [comment removed for export] *)
    assert (FQN : forall e, In e ((QF, nf) :: rt_live RT Σ) -> fst e <> QN).
    { apply (live_fresh RT AF Σ' m' [] QN nn ((QF, nf) :: rt_live RT Σ) ART1); [rewrite LV'; reflexivity| clear - BN64; lia|].
      intros e [<-|He]; [cbn; clear - BF64; lia| exact (LPOS e He)]. }
    assert (FQF : forall e, In e ([(QN, nn)] ++ rt_live RT Σ) -> fst e <> QF).
    { apply (live_fresh RT AF Σ' m' [(QN, nn)] QF nf (rt_live RT Σ) ART1); [rewrite LV'; reflexivity| clear - BF64; lia|].
      intros e He. apply in_app_iff in He. destruct He as [[<-|[]]|He]; [cbn; clear - BN64; lia| exact (LPOS e He)]. }
    eapply (Hk Σ' m' F' fc' v y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 c' QF QN); [| exact LV'| exact FRS'| exact PR| exact EL1| exact QF0| exact QN0| exact Hc'].
    eapply (com_call RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ Σ' m m' off off crem (crem - 2) lrem (lrem - 2) _ _ _ _ 2 COM ART1 MI1 ST1 PR CLE1 SEC1 LE1);
      [| exact OFF| exact FRS'| exact SP'| exact CG'| exact CR'| clear - CRM; lia| clear; lia| clear - LRM; lia| rewrite LV'; cbn [length]; clear; lia
       | exact ELV| exact HWP| exact HWS| exact HWF| | | | | ].
    - eapply (mbio_rep_keep (rt_live RT Σ)); [exact MB| exact PR| intros e He; rewrite LV'; split; [| right; right]; exact (ELV _ (KLV _ He))|].
      intros e x He Hx. exact (com_klv_out RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ _ _ COM HWL (fun e H => H) e x He Hx).
    - rewrite LV'. cbn [app]. apply perm_skip, perm_skip. exact PERM.
    - intros e [<-|[<-|He]]; cbn [fst].
      + intros X. apply in_map_iff in X. destruct X as (e' & E' & He'). exact (FQN e' ltac:(right; exact (ELV _ He')) E').
      + intros X. apply in_map_iff in X. destruct X as (e' & E' & He'). exact (FQF e' ltac:(apply in_or_app; right; exact (ELV _ He')) E').
      + exact (CFR e He).
    - cbn [map fst app]. apply (nd_insert1 []); [apply (nd_insert1 [])|]; cbn [app].
      + exact ND.
      + intros X. apply in_app_iff in X. destruct X as [X|[X|X]].
        * apply in_map_iff in X. destruct X as (e' & E' & He'). exact (FQF e' ltac:(apply in_or_app; right; exact (CLV _ He')) E').
        * exact (FQF (e_E RT en, 904) ltac:(apply in_or_app; right; exact (ELV _ INE)) X).
        * rewrite <- (mbio_ent_fst (e_K RT en) (e_bmax RT en)) in X. apply in_map_iff in X. destruct X as (e' & E' & He'). exact (FQF e' ltac:(apply in_or_app; right; exact (ELV _ (KLV _ He'))) E').
      + intros [X|X].
        * exact (FQN (QF, nf) ltac:(left; reflexivity) X).
        * apply in_app_iff in X. destruct X as [X|[X|X]].
          -- apply in_map_iff in X. destruct X as (e' & E' & He'). exact (FQN e' ltac:(right; exact (CLV _ He')) E').
          -- exact (FQN (e_E RT en, 904) ltac:(right; exact (ELV _ INE)) X).
          -- rewrite <- (mbio_ent_fst (e_K RT en) (e_bmax RT en)) in X. apply in_map_iff in X. destruct X as (e' & E' & He'). exact (FQN e' ltac:(right; exact (ELV _ (KLV _ He'))) E').
    - intros e He. rewrite LV' in He. destruct He as [<-|[<-|He]]; [cbn; clear - BN64; lia| cbn; clear - BF64; lia| exact (LPOS e He)].
    - intros e He X. apply in_app_iff in X. destruct X as [X|X]; [exact (NTL e He ltac:(apply in_or_app; left; exact X))|].
      cbn [map fst] in X. destruct X as [X|[X|X]].
      + refine (FQN e _ (eq_sym X)). right. destruct He as [<-|He]; [exact (ELV _ INE)| exact (ELV _ (INCL _ He))].
      + refine (FQF e _ (eq_sym X)). apply in_or_app; right. destruct He as [<-|He]; [exact (ELV _ INE)| exact (ELV _ (INCL _ He))].
      + exact (NTL e He ltac:(apply in_or_app; right; exact X)).
  Qed.

  (* [comment removed for export] *)
  Lemma pem_call_eerr : err_set_error_stmt RT libenv errst_live FZ_SITES FZ_CALLS ->
    forall T (en : pem_entry) Σ (m : mem) off crem lrem cur strs site reason (F : bvmap 5 word) (fc : bv 32)
           (t0 t1 t2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6 : word) c,
    pem_com en Σ m off crem lrem cur -> errst_live (e_E RT en) 1 0 strs m -> (forall e, In e strs -> In e cur) -> 2 <= crem -> In site PEM_RAS_eerr -> 0 < reason < 2 ^ 31 ->
    ASTA RT Σ (e_PMc RT en) (eq (pem_ms en FZ_ERR_SET_ERROR m F fc (wz site) t0 t1 t2 (wz 9) (wz reason) (wz 0) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6)) c ->
    (forall Σ' (m' : mem) (F' : bvmap 5 word) (fc' : bv 32) (v y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 : word) c',
       pem_com en Σ' m' off (crem - 2) lrem cur ->
       rt_live RT Σ' = rt_live RT Σ -> rt_frames RT Σ' = rt_frames RT Σ ->
       rt_pres_fp (rt_live RT Σ') (rt_frames RT Σ) (e_sp1 RT en) ((e_E RT en, e_E RT en + 904) :: lib_W (e_LBL RT en)) m m' ->
       errst_live (e_E RT en) 1 0 strs m' ->
       ASTA RT Σ' (e_PMc RT en) (eq (pem_ms en site m' F' fc' (wz site) y0 y1 y2 v b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s10 s11 y3 y4 y5 y6)) c' ->
       realizes asegs c' T) ->
    realizes asegs c T.
  Proof using AF AFP libenv_agree libenv_fp_where.
    intros C_EE T en Σ m off crem lrem cur strs site reason F fc t0 t1 t2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6 c COM EL0 SC CRM HSI HR HA Hk.
    pose proof COM as (ART0 & MI & ST & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & NTL & MB & OFF & BLT & KLV & PERM & CFR & ND & LPOS
       & FRS & FRN & SP0 & CG & LIV & LR0 & CR & CR0 & CRE & CGH & CGS & CTX & UWC & F0 & F64 & FTOP & FSEG & FSH & FFS & SAVED & PRES & FLR & NDO & OUTS & FDO & MST).
    destruct (com_lists RT libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ COM) as [ELV CLV].
    pose proof (com_WE_ok RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ COM) as WOK. pose proof WOK as (HWS & HWFR & HWFF & HWF & HWL & HWP).
    assert (HSR : In site PEM_RAS) by (unfold PEM_RAS; rewrite !in_app_iff; tauto).
    assert (SR : 0 <= site < 2 ^ 64) by (clear - HSI; unfold PEM_RAS_eerr in HSI; cbn in HSI; lia).
    destruct (com_call_pre RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ site FZ_ERR_SET_ERROR COM (pem_site_in _ HSR) (pem_calls_eerr _ HSI) SR)
      as (EU & COK & CTX1 & UWC1 & INCL1 & FRMAX & CRED & HLO & H352).
    apply (C_EE Σ (e_PMc RT en) (wz site) (wz (e_sp1 RT en)) (e_gp RT en) (wz TP_A) t0 t1 t2 (e_sp RT en) (wz (e_sp1 RT en)) (wz 9) (wz reason) (wz 0) a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 (wz (shad (e_f RT en))) (wz SHB) s10 s11 t3 t4 t5 t6 F fc m (e_lo RT en) (bv_unsigned (e_ra RT en) :: e_outer RT en) (e_canary RT en)
             (e_LBL RT en) (e_E RT en) 9 reason strs FDO MST eq_refl eq_refl eq_refl eq_refl ltac:(clear; lia) ltac:(clear; lia) HR LE INCL1 (ELV _ INE)
             (fun e He => CLV _ (SC _ He)) EL0 ART0 MI COK ltac:(rewrite EU; clear - LOR; unfold PEM_CALLEE_STACK, ERRS_STACK in *; lia) CLE CTX1 UWC1 CGH
             ltac:(rewrite FRS; cbn [length]; clear - FRN; lia) ltac:(clear - CRED CRM; lia) T c HA).
    intros c' (Σ' & AP & (LV' & FRS' & SP' & CR' & CG')). unfold apost in AP.
    destruct (ASTA_unpack RT Σ' _ _ c' AP) as (ms' & (v & m' & RS & (ART1 & MI1 & ST1) & PR & CLE1 & (WM1 & LE1 & EL1)) & Hc'). clear AP.
    destruct RS as (y0 & y1 & y2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & y3 & y4 & y5 & y6 & F' & fc' & ->).
    rewrite EU in ST1, PR. rewrite (ret_pc_even site SR) in Hc' by (clear - HSI; unfold PEM_RAS_eerr in HSI; cbn in HSI; lia).
    assert (SEC1 : sec_off m').
    { eapply sec_off_agree; [exact SEC|]. intros a Ea. rewrite <- (Z_to_bv_bv_unsigned a), Ea.
      apply PR; rewrite (unsigned_lit SEC_INIT) by (unfold SEC_INIT; clear; lia); [apply acl_static; apply client_static_intro; unfold SEC_INIT; clear; lia|].
      apply HWP; [apply acl_static; apply client_static_intro; unfold SEC_INIT; clear; lia| exact (com_sec_out en Σ m off crem lrem _ COM)]. }
    eapply (Hk Σ' m' F' fc' v y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 c'); [| exact LV'| exact FRS'| rewrite LV'; exact PR| exact EL1| exact Hc'].
    eapply (com_call RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ Σ' m m' off off crem (crem - 2) lrem lrem _ cur _ _ 2 COM ART1 MI1 ST1 PR CLE1 SEC1 LE1);
      [| exact OFF| exact FRS'| exact SP'| exact CG'| exact CR'| clear - CRM; lia| clear; lia| exact LR0| rewrite LV'; clear; lia
       | exact ELV| exact HWP| exact HWS| exact HWF| rewrite LV'; exact PERM| exact CFR| exact ND| rewrite LV'; exact LPOS| exact NTL].
    eapply (mbio_rep_keep (rt_live RT Σ)); [exact MB| exact PR| intros e He; rewrite LV'; split; exact (ELV _ (KLV _ He))|].
    intros e x He Hx. exact (com_klv_out RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ _ _ COM HWL (fun e H => H) e x He Hx).
  Qed.
  (* [comment removed for export] *)
  Lemma com_call_pre0 : forall (en : pem_entry) Σ (m : mem) off crem lrem cur,
    pem_com en Σ m off crem lrem cur ->
       bv_unsigned (wz (e_sp1 RT en)) = e_sp1 RT en
    /\ call_ok RT Σ m (wz (e_sp1 RT en)) (e_lo RT en)
    /\ incl_live (e_LBL RT en) (rt_live RT Σ)
    /\ (length (rt_frames RT Σ) < FRAMES_MAX)%nat /\ crem <= rt_credit RT Σ
    /\ e_lo RT en <= e_sp1 RT en /\ e_sp1 RT en + 352 <= e_PL RT en.
  Proof using AF AFP.
    intros en Σ m off crem lrem cur COM.
    pose proof COM as (ART0 & MI & ST & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & NTL & MB & OFF & BLT & KLV & PERM & CFR & ND & LPOS
       & FRS & FRN & SP0 & CG & LIV & LR0 & CR & CR0 & CRE & CGH & CGS & CTX & UWC & F0 & F64 & FTOP & FSEG & FSH & FFS & SAVED & PRES & FLR & NDO & OUTS & FDO & MST).
    destruct (com_lists RT libenv FZ_SITES FZ_CALLS en Σ m off crem lrem cur COM) as [ELV CLV].
    assert (HLO : e_lo RT en <= e_sp1 RT en) by (clear - LOR; unfold RT_STACK, PEM_CALLEE_STACK in *; lia).
    assert (EU : bv_unsigned (wz (e_sp1 RT en)) = e_sp1 RT en) by (apply unsigned_lit; clear - HLO HLOS TOP PD; unfold e_sp1, USTACK_TOP in *; lia).
    split; [exact EU|].
    split. { unfold call_ok. rewrite EU. split; [exact ST|]. split; [exact LOW|]. split; [clear - LOR; unfold RT_STACK, PEM_CALLEE_STACK in *; lia|].
             split; [clear - TOP PD; unfold e_sp1, USTACK_TOP in *; lia|]. clear - PDM PD. unfold e_sp1 in *. Z.div_mod_to_equations. lia. }
    split; [intros e He; exact (ELV _ (INCL _ He))|].
    split; [rewrite FRS; cbn [length]; clear - FRN; lia|]. split; [clear - CR CRE; lia|].
    split; [exact HLO|]. unfold e_sp1. clear - PD; lia.
  Qed.

  Lemma pem_calls_pmal : forall r G, In r PEM_RAS_pmal -> In G [FZ_PEM_MALLOC; e_CRYPTO_malloc; e_CRYPTO_secure_malloc] -> In (r, G) PEM_CALLS.
  Proof.
    intros r G Hr HG. unfold PEM_CALLS. rewrite !in_app_iff. right; left. apply in_concat. exists [(r, FZ_PEM_MALLOC); (r, e_CRYPTO_malloc); (r, e_CRYPTO_secure_malloc)].
    split; [apply in_map_iff; exists r; split; [reflexivity| exact Hr]|]. cbn in HG |- *. destruct HG as [<-|[<-|[<-|[]]]]; tauto.
  Qed.

  (* [comment removed for export] *)
  Lemma pem_call_pmal : pem_malloc_stmt RT libenv FZ_SITES FZ_CALLS ->
    forall T (en : pem_entry) Σ (m : mem) off crem lrem cur n site (F : bvmap 5 word) (fc : bv 32)
           (t0 t1 t2 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6 : word) c,
    pem_com en Σ m off crem lrem cur -> 0 < n < 2 ^ 27 -> mcost n <= crem -> 1 <= lrem -> In site PEM_RAS_pmal ->
    ASTA RT Σ (e_PMc RT en) (eq (pem_ms en FZ_PEM_MALLOC m F fc (wz site) t0 t1 t2 (wz n) (wz (e_flags RT en)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6)) c ->
    (forall Σ' (m' : mem) (F' : bvmap 5 word) (fc' : bv 32) (y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 : word) c' (p : Z) (junk : list byte),
       pem_com en Σ' m' off (crem - mcost n) (lrem - 1) ((p, n) :: cur) ->
       rt_live RT Σ' = (p, n) :: rt_live RT Σ -> rt_frames RT Σ' = rt_frames RT Σ ->
       rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (e_sp1 RT en) (lib_W (e_LBL RT en)) m m' ->
       length junk = Z.to_nat n -> rw_cells asegs m' p [CB (Z.to_nat n) junk] -> 0 < p -> p mod 16 = 0 -> p + n < USTACK_TOP ->
       ASTA RT Σ' (e_PMc RT en) (eq (pem_ms en site m' F' fc' (wz site) y0 y1 y2 (wz p) b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s10 s11 y3 y4 y5 y6)) c' ->
       realizes asegs c' T) ->
    realizes asegs c T.
  Proof using AF AFP libenv_agree libenv_fp_where.
    intros C_PM T en Σ m off crem lrem cur n site F fc t0 t1 t2 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6 c COM HN CRM LRM HSI HA Hk.
    pose proof COM as (ART0 & MI & ST & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & NTL & MB & OFF & BLT & KLV & PERM & CFR & ND & LPOS
       & FRS & FRN & SP0 & CG & LIV & LR0 & CR & CR0 & CRE & CGH & CGS & CTX & UWC & F0 & F64 & FTOP & FSEG & FSH & FFS & SAVED & PRES & FLR & NDO & OUTS & FDO & MST).
    destruct (com_lists RT libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ COM) as [ELV CLV].
    pose proof (com_W_ok RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ COM) as WOK. pose proof WOK as (HWS & HWFR & HWFF & HWF & HWL & HWP).
    assert (HSR : In site PEM_RAS) by (unfold PEM_RAS; rewrite !in_app_iff; tauto).
    assert (SR : 0 <= site < 2 ^ 64) by (clear - HSI; unfold PEM_RAS_pmal in HSI; cbn in HSI; lia).
    destruct (com_call_pre RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ site FZ_PEM_MALLOC COM (pem_site_in _ HSR) (pem_calls_pmal _ FZ_PEM_MALLOC HSI ltac:(cbn; tauto)) SR)
      as (EU & COK & CTX1 & UWC1 & INCL1 & FRMAX & CRED & HLO & H352).
    assert (HCG : forall G, In G [FZ_PEM_MALLOC; e_CRYPTO_malloc; e_CRYPTO_secure_malloc] -> In (bv_unsigned (wz site), G) (cg_call (rt_cg RT Σ))).
    { intros G HG. rewrite (unsigned_lit site) by exact SR. exact (proj2 CGH _ (proj2 CGS _ (pem_calls_pmal _ G HSI HG))). }
    assert (MC0 : 0 <= mcost n) by (unfold mcost; destruct (n <=? 64512); clear - HN; lia).
    apply (C_PM Σ (e_PMc RT en) (wz site) (wz (e_sp1 RT en)) (e_gp RT en) (wz TP_A) t0 t1 t2 (e_sp RT en) (wz (e_sp1 RT en)) (wz n) (wz (e_flags RT en)) a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 (wz (shad (e_f RT en))) (wz SHB) s10 s11 t3 t4 t5 t6 F fc m (e_lo RT en) (bv_unsigned (e_ra RT en) :: e_outer RT en) (e_canary RT en)
             (e_LBL RT en) (e_E RT en) n (e_flags RT en) FDO MST eq_refl eq_refl eq_refl HN ltac:(clear - FLR; lia) LE INCL1 ART0 MI COK
             ltac:(rewrite EU; clear - LOR; unfold PEM_CALLEE_STACK, PMAL_STACK in *; lia) CLE SEC CTX1 UWC1 CGH
             (HCG e_CRYPTO_malloc ltac:(cbn; tauto)) (HCG e_CRYPTO_secure_malloc ltac:(cbn; tauto)) ltac:(clear - LIV LRM; lia) ltac:(clear - CRED CRM; lia) T c HA).
    intros c' (Σ' & p & junk & AP & LV' & FRS' & SP' & CR' & CG' & P0 & P16 & PTOP). unfold apost in AP.
    destruct (ASTA_unpack RT Σ' _ _ c' AP) as (ms' & (v & m' & RS & (ART1 & MI1 & ST1) & PR & CLE1 & (-> & WM1 & LE1 & SEC1 & LJ & PC)) & Hc'). clear AP.
    destruct RS as (y0 & y1 & y2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & y3 & y4 & y5 & y6 & F' & fc' & ->).
    rewrite EU in ST1, PR. rewrite (ret_pc_even site SR) in Hc' by (clear - HSI; unfold PEM_RAS_pmal in HSI; cbn in HSI; lia).
    assert (FP : forall e, In e ([] ++ rt_live RT Σ) -> fst e <> p).
    { apply (live_fresh RT AF Σ' m' [] p n (rt_live RT Σ) ART1); [rewrite LV'; reflexivity| clear - HN; lia| intros e He; exact (LPOS e He)]. }
    cbn [app] in FP.
    eapply (Hk Σ' m' F' fc' y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 c' p junk); [| exact LV'| exact FRS'| exact PR| exact LJ| exact PC| exact P0| exact P16| exact PTOP| exact Hc'].
    eapply (com_call RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ Σ' m m' off off crem (crem - mcost n) lrem (lrem - 1) _ _ _ _ (mcost n) COM ART1 MI1 ST1 PR CLE1 SEC1 LE1);
      [| exact OFF| exact FRS'| exact SP'| exact CG'| rewrite CR'; clear; lia| clear - CRM MC0; lia| clear; lia| clear - LRM; lia| rewrite LV'; cbn [length]; clear; lia
       | exact ELV| exact HWP| exact HWS| exact HWF| | | | | ].
    - eapply (mbio_rep_keep (rt_live RT Σ)); [exact MB| exact PR| intros e He; rewrite LV'; split; [| right]; exact (ELV _ (KLV _ He))|].
      intros e x He Hx. exact (com_klv_out RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ _ _ COM HWL (fun e H => or_intror H) e x He Hx).
    - rewrite LV'. cbn [app]. apply perm_skip. exact PERM.
    - intros e [<-|He]; [| exact (CFR e He)]. cbn [fst]. intros X. apply in_map_iff in X. destruct X as (e' & E' & He'). exact (FP e' (ELV _ He') E').
    - cbn [map fst app]. apply (nd_insert1 []); [exact ND|]. cbn [app]. intros X. apply in_app_iff in X. destruct X as [X|[X|X]].
      + apply in_map_iff in X. destruct X as (e' & E' & He'). exact (FP e' (CLV _ He') E').
      + exact (FP (e_E RT en, 904) (ELV _ INE) X).
      + rewrite <- (mbio_ent_fst (e_K RT en) (e_bmax RT en)) in X. apply in_map_iff in X. destruct X as (e' & E' & He'). exact (FP e' (ELV _ (KLV _ He')) E').
    - intros e He. rewrite LV' in He. destruct He as [<-|He]; [cbn; clear - HN; lia| exact (LPOS e He)].
    - intros e He X. apply in_app_iff in X. destruct X as [X|X]; [exact (NTL e He ltac:(apply in_or_app; left; exact X))|].
      cbn [map fst] in X. destruct X as [X|X]; [| exact (NTL e He ltac:(apply in_or_app; right; exact X))].
      refine (FP e _ (eq_sym X)). destruct He as [<-|He]; [exact (ELV _ INE)| exact (ELV _ (INCL _ He))].
  Qed.

  (* [comment removed for export] *)
  Lemma pem_call_pmal0 : pem_malloc0_stmt RT libenv ->
    forall T (en : pem_entry) Σ (m : mem) off crem lrem cur site (F : bvmap 5 word) (fc : bv 32)
           (t0 t1 t2 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6 : word) c,
    pem_com en Σ m off crem lrem cur -> In site PEM_RAS_pmal ->
    ASTA RT Σ (e_PMc RT en) (eq (pem_ms en FZ_PEM_MALLOC m F fc (wz site) t0 t1 t2 (wz 0) (wz (e_flags RT en)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6)) c ->
    (forall Σ' (m' : mem) (F' : bvmap 5 word) (fc' : bv 32) (y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 : word) c',
       pem_com en Σ' m' off crem lrem cur ->
       rt_live RT Σ' = rt_live RT Σ -> rt_frames RT Σ' = rt_frames RT Σ ->
       rt_pres_fp (rt_live RT Σ') (rt_frames RT Σ) (e_sp1 RT en) (lib_W (e_LBL RT en)) m m' ->
       ASTA RT Σ' (e_PMc RT en) (eq (pem_ms en site m' F' fc' (wz site) y0 y1 y2 (wz 0) b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s10 s11 y3 y4 y5 y6)) c' ->
       realizes asegs c' T) ->
    realizes asegs c T.
  Proof using AF AFP libenv_agree libenv_fp_where.
    intros C_PM0 T en Σ m off crem lrem cur site F fc t0 t1 t2 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6 c COM HSI HA Hk.
    pose proof COM as (ART0 & MI & ST & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & NTL & MB & OFF & BLT & KLV & PERM & CFR & ND & LPOS
       & FRS & FRN & SP0 & CG & LIV & LR0 & CR & CR0 & CRE & CGH & CGS & CTX & UWC & F0 & F64 & FTOP & FSEG & FSH & FFS & SAVED & PRES & FLR & NDO & OUTS & FDO & MST).
    destruct (com_lists RT libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ COM) as [ELV CLV].
    pose proof (com_W_ok RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ COM) as WOK. pose proof WOK as (HWS & HWFR & HWFF & HWF & HWL & HWP).
    assert (SR : 0 <= site < 2 ^ 64) by (clear - HSI; unfold PEM_RAS_pmal in HSI; cbn in HSI; lia).
    destruct (com_call_pre0 en Σ m off crem lrem _ COM) as (EU & COK & INCL1 & FRMAX & CRED & HLO & H352).
    apply (C_PM0 Σ (e_PMc RT en) (wz site) (wz (e_sp1 RT en)) (e_gp RT en) (wz TP_A) t0 t1 t2 (e_sp RT en) (wz (e_sp1 RT en)) (wz 0) (wz (e_flags RT en)) a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 (wz (shad (e_f RT en))) (wz SHB) s10 s11 t3 t4 t5 t6 F fc m (e_lo RT en) (bv_unsigned (e_ra RT en) :: e_outer RT en) (e_canary RT en)
             (e_LBL RT en) (e_E RT en) (e_flags RT en) FDO MST eq_refl eq_refl eq_refl ltac:(clear - FLR; lia) LE INCL1 ART0 MI COK
             ltac:(rewrite EU; clear - LOR; unfold PEM_CALLEE_STACK, PMAL_STACK in *; lia) CLE SEC T c HA).
    intros c' (Σ' & AP & (LV' & FRS' & SP' & CR' & CG')). unfold apost in AP.
    destruct (ASTA_unpack RT Σ' _ _ c' AP) as (ms' & (v & m' & RS & (ART1 & MI1 & ST1) & PR & CLE1 & (-> & WM1 & LE1 & SEC1)) & Hc'). clear AP.
    destruct RS as (y0 & y1 & y2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & y3 & y4 & y5 & y6 & F' & fc' & ->).
    rewrite EU in ST1, PR. rewrite (ret_pc_even site SR) in Hc' by (clear - HSI; unfold PEM_RAS_pmal in HSI; cbn in HSI; lia).
    eapply (Hk Σ' m' F' fc' y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 c'); [| exact LV'| exact FRS'| rewrite LV'; exact PR| exact Hc'].
    eapply (com_call RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ Σ' m m' off off crem crem lrem lrem _ cur _ _ 0 COM ART1 MI1 ST1 PR CLE1 SEC1 LE1);
      [| exact OFF| exact FRS'| exact SP'| exact CG'| exact CR'| exact CR0| clear; lia| exact LR0| rewrite LV'; clear; lia
       | exact ELV| exact HWP| exact HWS| exact HWF| rewrite LV'; exact PERM| exact CFR| exact ND| rewrite LV'; exact LPOS| exact NTL].
    eapply (mbio_rep_keep (rt_live RT Σ)); [exact MB| exact PR| intros e He; rewrite LV'; split; exact (ELV _ (KLV _ He))|].
    intros e x He Hx. exact (com_klv_out RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ _ _ COM HWL (fun e H => or_intror H) e x He Hx).
  Qed.
  (* [comment removed for export] *)
  Lemma com_WB_static : forall (en : pem_entry) Σ (m : mem) off crem lrem cur XL,
    pem_com en Σ m off crem lrem cur -> (forall e, In e XL -> In e (rt_live RT Σ)) -> forall x, client_static x -> outside (map rng XL) x.
  Proof using AF AFP.
    intros en Σ m off crem lrem cur XL COM HXL x CS. pose proof COM as (ART0 & _). pose proof (client_static_range _ CS) as R.
    apply outside_intro. intros iv Hiv. apply in_map_iff in Hiv. destruct Hiv as ([p n] & <- & Hpn). cbn [rng fst snd].
    pose proof (af_live_range RT AF Σ m p n ART0 (HXL _ Hpn)) as (_ & _ & Y). clear - R Y. unfold SEGTOP_A in *. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma pem_call_bgets : bio_gets_stmt RT ->
    forall T (en : pem_entry) Σ (m : mem) off crem lrem cur LB (bs : list byte) site (F : bvmap 5 word) (fc : bv 32)
           (t0 t1 t2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6 : word) c,
    pem_com en Σ m off crem lrem cur -> In (LB, 256) cur -> LB mod 16 = 0 -> length bs = 256%nat -> rw_cells asegs m LB [CB 256 bs] ->
    1 <= crem -> 0 <= site < 2 ^ 64 -> site mod 2 = 0 ->
    ASTA RT Σ (e_PMc RT en) (eq (pem_ms en FZ_BIO_GETS m F fc (wz site) t0 t1 t2 (wz (e_BI RT en)) (wz LB) (wz 255) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6)) c ->
    (forall Σ' (m' : mem) (F' : bvmap 5 word) (fc' : bv 32) (y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 : word) c' (k off' : Z) (bs' : list byte),
       pem_com en Σ' m' off' (crem - 1) lrem cur ->
       rt_live RT Σ' = rt_live RT Σ -> rt_frames RT Σ' = rt_frames RT Σ ->
       rt_pres_fp (rt_live RT Σ') (rt_frames RT Σ) (e_sp1 RT en) ((LB, LB + 256) :: mbio_W (e_K RT en) (e_bmax RT en)) m m' ->
       length bs' = 256%nat -> rw_cells asegs m' LB [CB 256 bs'] ->
       ((k = 0 /\ off' = off /\ off = e_blen RT en)
        \/ (1 <= k <= Z.min (e_blen RT en - off) 254 /\ nth_error bs' (Z.to_nat k) = Some (Z_to_bv 8 0) /\ (k < Z.min (e_blen RT en - off) 254 -> nth_error bs' (Z.to_nat (k - 1)) = Some (Z_to_bv 8 10)) /\ off' = off + k)) ->
       ASTA RT Σ' (e_PMc RT en) (eq (pem_ms en site m' F' fc' (wz site) y0 y1 y2 (wz k) b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s10 s11 y3 y4 y5 y6)) c' ->
       realizes asegs c' T) ->
    realizes asegs c T.
  Proof using AF AFP libenv_agree libenv_fp_where.
    intros C_BG T en Σ m off crem lrem cur LB bs site F fc t0 t1 t2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6 c COM HLB AL16 LBS LBC CRM SR SE HA Hk.
    pose proof COM as (ART0 & MI & ST & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & NTL & MB & OFF & BLT & KLV & PERM & CFR & ND & LPOS
       & FRS & FRN & SP0 & CG & LIV & LR0 & CR & CR0 & CRE & CGH & CGS & CTX & UWC & F0 & F64 & FTOP & FSEG & FSH & FFS & SAVED & PRES & FLR & NDO & OUTS & FDO & MST).
    destruct (com_lists RT libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ COM) as [ELV CLV].
    pose proof (com_WB_ok RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem cur ((LB, 256) :: mbio_ent (e_K RT en) (e_bmax RT en)) COM
                  ltac:(intros e [<-|He]; [left; split; [exact HLB| cbn; clear; lia]| right; exact He])) as WOK. pose proof WOK as (HWS & HWFR & HWFF & HWF & HWL & HWP).
    destruct (com_call_pre0 en Σ m off crem lrem _ COM) as (EU & COK & INCL1 & FRMAX & CRED & HLO & H352).
    assert (NT : ~ mbio_T (e_K RT en) LB).
    { unfold mbio_T. intros X. pose proof (nd_split _ _ ND) as (_ & _ & DJ). exact (DJ LB (in_map fst _ _ HLB) ltac:(right; exact X)). }
    apply (C_BG Σ (e_PMc RT en) (wz site) (wz (e_sp1 RT en)) (e_gp RT en) (wz TP_A) t0 t1 t2 (e_sp RT en) (wz (e_sp1 RT en)) (wz (e_BI RT en)) (wz LB) (wz 255) a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 (wz (shad (e_f RT en))) (wz SHB) s10 s11 t3 t4 t5 t6 F fc m (e_lo RT en) (e_canary RT en)
             (e_K RT en) (e_BI RT en) (e_meth RT en) (e_blen RT en) (e_bmax RT en) off LB bs FDO MST eq_refl eq_refl eq_refl eq_refl MB (CLV _ HLB) AL16 NT LBS LBC
             ART0 MI COK ltac:(rewrite EU; clear - LOR; unfold PEM_CALLEE_STACK, BGETS_STACK in *; lia) CLE FRMAX ltac:(clear - CRED CRM; lia) T c HA).
    intros c' (Σ' & AP & (LV' & FRS' & SP' & CR' & CG')). unfold apost in AP.
    destruct (ASTA_unpack RT Σ' _ _ c' AP) as (ms' & (v & m' & RS & (ART1 & MI1 & ST1) & PR & CLE1 & (WM1 & (k & bs' & -> & LBS' & LBC' & RES))) & Hc'). clear AP.
    destruct RS as (y0 & y1 & y2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & y3 & y4 & y5 & y6 & F' & fc' & ->).
    rewrite EU in ST1, PR. rewrite (ret_pc_even site SR SE) in Hc'.
    assert (XLV : forall e, In e ((LB, 256) :: mbio_ent (e_K RT en) (e_bmax RT en)) -> In e (rt_live RT Σ)).
    { intros e [<-|He]; [exact (CLV _ HLB)| exact (ELV _ (KLV _ He))]. }
    assert (LE1 : libenv m' (e_LBL RT en) (e_E RT en)).
    { eapply (libenv_keep libenv libenv_fp libenv_agree libenv_fp_where); [exact LE| exact PR| exact INCL1|].
      intros x Hx. destruct (libenv_fp_where _ _ Hx) as [(_ & CS & _)|(p & n & Hin & Hp)].
      - exact (com_WB_static en Σ m off crem lrem cur _ COM XLV x CS).
      - apply (HWL p n x (INCL1 _ Hin)); [| exact Hp]. intros [X|X].
        + apply (CFR _ HLB). cbn [fst]. injection X. intros _ Ep. rewrite Ep. exact (in_map fst _ _ (INCL _ Hin)).
        + apply (NTL (p, n) ltac:(right; exact Hin)). apply in_or_app; left. rewrite <- (mbio_ent_fst (e_K RT en) (e_bmax RT en)). exact (in_map fst _ _ X). }
    assert (SEC1 : sec_off m').
    { eapply sec_off_agree; [exact SEC|]. intros a Ea. rewrite <- (Z_to_bv_bv_unsigned a), Ea.
      apply PR; rewrite (unsigned_lit SEC_INIT) by (unfold SEC_INIT; clear; lia); [apply acl_static; apply client_static_intro; unfold SEC_INIT; clear; lia|].
      exact (com_WB_static en Σ m off crem lrem cur _ COM XLV SEC_INIT ltac:(apply client_static_intro; unfold SEC_INIT; clear; lia)). }
    assert (OFF' : exists off', mbio_rep (rt_live RT Σ) m' (e_K RT en) (e_BI RT en) (e_meth RT en) (e_blen RT en) (e_bmax RT en) off' /\ e_boff RT en <= off' <= e_blen RT en
              /\ ((k = 0 /\ off' = off /\ off = e_blen RT en) \/ (1 <= k <= Z.min (e_blen RT en - off) 254 /\ nth_error bs' (Z.to_nat k) = Some (Z_to_bv 8 0) /\ (k < Z.min (e_blen RT en - off) 254 -> nth_error bs' (Z.to_nat (k - 1)) = Some (Z_to_bv 8 10)) /\ off' = off + k))).
    { destruct RES as [(K0 & OE & MB1)|(KR & NTH & LFK & MB1)].
      - exists off. split; [exact MB1|]. split; [exact OFF|]. left. split; [exact K0|]. split; [reflexivity| exact OE].
      - exists (off + k). split; [exact MB1|]. split; [clear - OFF KR; lia|]. right. split; [exact KR|]. split; [exact NTH|]. split; [exact LFK| reflexivity]. }
    destruct OFF' as (off' & MB1 & OFF1 & RES').
    eapply (Hk Σ' m' F' fc' y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 c' k off' bs'); [| exact LV'| exact FRS'| rewrite LV'; exact PR| exact LBS'| exact LBC'| exact RES'| exact Hc'].
    eapply (com_call RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ Σ' m m' off off' crem (crem - 1) lrem lrem _ cur _ _ 1 COM ART1 MI1 ST1 PR CLE1 SEC1 LE1);
      [rewrite LV'; exact MB1| exact OFF1| exact FRS'| exact SP'| exact CG'| exact CR'| clear - CRM; lia| clear; lia| exact LR0| rewrite LV'; clear; lia
       | exact ELV| exact HWP| exact HWS| exact HWF| rewrite LV'; exact PERM| exact CFR| exact ND| rewrite LV'; exact LPOS| exact NTL].
  Qed.
  (* [comment removed for export] *)
  Lemma pem_call_san : sanitize_line_stmt RT ->
    forall T (en : pem_entry) Σ (m : mem) off crem lrem cur LB len flags fcall (bs : list byte) site (F : bvmap 5 word) (fc : bv 32)
           (t0 t1 t2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6 : word) c,
    pem_com en Σ m off crem lrem cur -> In (LB, 256) cur -> LB mod 16 = 0 -> length bs = 256%nat -> rw_cells asegs m LB [CB 256 bs] ->
    nth_error bs (Z.to_nat len) = Some (Z_to_bv 8 0) -> 1 <= len <= 254 -> 0 <= flags < 2 ^ 32 -> 0 <= fcall < 2 ^ 32 -> 0 <= site < 2 ^ 64 -> site mod 2 = 0 ->
    ASTA RT Σ (e_PMc RT en) (eq (pem_ms en FZ_SANITIZE m F fc (wz site) t0 t1 t2 (wz LB) (wz len) (wz flags) (wz fcall) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6)) c ->
    (forall (m' : mem) (F' : bvmap 5 word) (fc' : bv 32) (y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 : word) c' (len' : Z) (bs' : list byte),
       pem_com en Σ m' off crem lrem cur ->
       rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (e_sp1 RT en) [(LB, LB + 256)] m m' ->
       1 <= len' <= len + 1 -> (nth_error bs (Z.to_nat (len - 1)) = Some (Z_to_bv 8 10) -> len' <= len) -> length bs' = 256%nat -> rw_cells asegs m' LB [CB 256 bs'] ->
       nth_error bs' (Z.to_nat (len' - 1)) = Some (Z_to_bv 8 10) -> nth_error bs' (Z.to_nat len') = Some (Z_to_bv 8 0) ->
       ASTA RT Σ (e_PMc RT en) (eq (pem_ms en site m' F' fc' (wz site) y0 y1 y2 (wz len') b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s10 s11 y3 y4 y5 y6)) c' ->
       realizes asegs c' T) ->
    realizes asegs c T.
  Proof using AF AFP libenv_agree libenv_fp_where.
    intros C_SAN T en Σ m off crem lrem cur LB len flags fcall bs site F fc t0 t1 t2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6 c
           COM HLB AL16 LBS LBC NUL HLEN HFL HFC SR SE HA Hk.
    pose proof COM as (ART0 & MI & ST & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & NTL & MB & OFF & BLT & KLV & PERM & CFR & ND & LPOS
       & FRS & FRN & SP0 & CG & LIV & LR0 & CR & CR0 & CRE & CGH & CGS & CTX & UWC & F0 & F64 & FTOP & FSEG & FSH & FFS & SAVED & PRES & FLR & NDO & OUTS & FDO & MST).
    destruct (com_lists RT libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ COM) as [ELV CLV].
    pose proof (com_WB_ok RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem cur [(LB, 256)] COM
                  ltac:(intros e [<-|[]]; left; split; [exact HLB| cbn; clear; lia])) as WOK. pose proof WOK as (HWS & HWFR & HWFF & HWF & HWL & HWP).
    destruct (com_call_pre0 en Σ m off crem lrem _ COM) as (EU & COK & INCL1 & FRMAX & CRED & HLO & H352).
    assert (XLV : forall e, In e [(LB, 256)] -> In e (rt_live RT Σ)) by (intros e [<-|[]]; exact (CLV _ HLB)).
    apply (C_SAN Σ (e_PMc RT en) (wz site) (wz (e_sp1 RT en)) (e_gp RT en) (wz TP_A) t0 t1 t2 (e_sp RT en) (wz (e_sp1 RT en)) (wz LB) (wz len) (wz flags) (wz fcall) a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 (wz (shad (e_f RT en))) (wz SHB) s10 s11 t3 t4 t5 t6 F fc m (e_lo RT en) (e_canary RT en) LB len flags fcall bs
             FDO MST eq_refl eq_refl eq_refl eq_refl eq_refl HLEN HFL HFC (CLV _ HLB) AL16 LBS LBC NUL
             ART0 MI COK ltac:(rewrite EU; clear - LOR; unfold PEM_CALLEE_STACK, SAN_STACK in *; lia) CLE T c HA).
    intros c' AP. unfold apost in AP.
    destruct (ASTA_unpack RT Σ _ _ c' AP) as (ms' & (v & m' & RS & (ART1 & MI1 & ST1) & PR & CLE1 & (len' & bs' & -> & HL' & HL2 & WM1 & LBS' & LBC' & NL & NUL')) & Hc'). clear AP.
    destruct RS as (y0 & y1 & y2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & y3 & y4 & y5 & y6 & F' & fc' & ->).
    rewrite EU in ST1, PR. rewrite (ret_pc_even site SR SE) in Hc'.
    assert (LE1 : libenv m' (e_LBL RT en) (e_E RT en)).
    { eapply (libenv_keep libenv libenv_fp libenv_agree libenv_fp_where); [exact LE| exact PR| exact INCL1|].
      intros x Hx. destruct (libenv_fp_where _ _ Hx) as [(_ & CS & _)|(p & n & Hin & Hp)].
      - exact (com_WB_static en Σ m off crem lrem cur _ COM XLV x CS).
      - apply (HWL p n x (INCL1 _ Hin)); [| exact Hp]. intros [X|[]].
        apply (CFR _ HLB). cbn [fst]. injection X. intros _ Ep. rewrite Ep. exact (in_map fst _ _ (INCL _ Hin)). }
    assert (SEC1 : sec_off m').
    { eapply sec_off_agree; [exact SEC|]. intros a Ea. rewrite <- (Z_to_bv_bv_unsigned a), Ea.
      apply PR; rewrite (unsigned_lit SEC_INIT) by (unfold SEC_INIT; clear; lia); [apply acl_static; apply client_static_intro; unfold SEC_INIT; clear; lia|].
      exact (com_WB_static en Σ m off crem lrem cur _ COM XLV SEC_INIT ltac:(apply client_static_intro; unfold SEC_INIT; clear; lia)). }
    eapply (Hk m' F' fc' y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 c' len' bs'); [| exact PR| exact HL'| exact HL2| exact LBS'| exact LBC'| exact NL| exact NUL'| exact Hc'].
    eapply (com_call RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ Σ m m' off off crem crem lrem lrem _ cur _ _ 0 COM ART1 MI1 ST1 PR CLE1 SEC1 LE1);
      [| exact OFF| reflexivity| reflexivity| reflexivity| clear; lia| exact CR0| clear; lia| exact LR0| clear; lia
       | exact ELV| exact HWP| exact HWS| exact HWF| exact PERM| exact CFR| exact ND| exact LPOS| exact NTL].
    eapply (mbio_rep_keep (rt_live RT Σ)); [exact MB| exact PR| intros e He; split; exact (ELV _ (KLV _ He))|].
    intros e x He Hx. exact (com_klv_outX en Σ m off crem lrem _ _ _ COM HWL ltac:(intros e' [<-|[]]; right; exact HLB) e x He Hx).
  Qed.
End W3X2.
