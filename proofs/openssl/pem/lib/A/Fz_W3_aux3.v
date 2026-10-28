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
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg IcptSpec.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs PLayout I_lkit I_ut RT_iface_pem D_libiface_pem Fz_kit Fz_ckit Fz_chk Fz_fkit Fz_env Fz_M_malloc Fz_M_zalloc Fz_M_free Fz_M_secure Fz_W1_defs Fz_W1_grow Fz_W1_pploc Fz_W3_iface Fz_W3_defs Fz_W3_lems Fz_W3_aux Fz_W3_aux2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.

Section W3X3.
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
  Lemma com_icpt0 : forall (en : pem_entry) Σ (m m' : mem) off crem lrem cur,
    pem_com en Σ m off crem lrem cur -> ART RT Σ m' -> mem_inv asegs m' -> stk asegs m' (e_lo RT en) (e_sp1 RT en) ->
    rt_pres_ex (rt_live RT Σ) (rt_frames RT Σ) (e_sp1 RT en) 0 0 m m' ->
    pem_com en Σ m' off crem lrem cur /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (e_sp1 RT en) [] m m'.
  Proof using AF AFP libenv_agree libenv_fp_where.
    intros en Σ m m' off crem lrem cur COM ART1 MI1 ST1 PX.
    pose proof COM as (ART0 & MI & ST & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & NTL & MB & OFF & BLT & KLV & PERM & CFR & ND & LPOS
       & FRS & FRN & SP0 & CG & LIV & LR0 & CR & CR0 & CRE & CGH & CGS & CTX & UWC & F0 & F64 & FTOP & FSEG & FSH & FFS & SAVED & PRES & FLR & NDO & OUTS & FDO & MST).
    destruct (com_lists RT libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ COM) as [ELV CLV].
    assert (PR : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (e_sp1 RT en) [] m m') by (intros a Ha _; apply PX; [exact Ha| clear; lia]).
    split; [| exact PR].
    assert (CLE1 : cl_env m' (Z_to_bv 8 1) (e_canary RT en)) by (eapply cl_env_pres_ex; [exact CLE| exact PX| intros x _; clear; lia]).
    assert (LE1 : libenv m' (e_LBL RT en) (e_E RT en)).
    { eapply (libenv_keep libenv libenv_fp libenv_agree libenv_fp_where); [exact LE| exact PR| intros e He; exact (ELV _ (INCL _ He))| intros x _; exact I]. }
    assert (SEC1 : sec_off m').
    { eapply sec_off_agree; [exact SEC|]. intros a Ea. apply PR; [| exact I]. apply acl_static. rewrite Ea. apply client_static_intro. unfold SEC_INIT. clear; lia. }
    eapply (com_call RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ Σ m m' off off crem crem lrem lrem _ cur _ _ 0 COM ART1 MI1 ST1 PR CLE1 SEC1 LE1);
      [| exact OFF| reflexivity| reflexivity| reflexivity| clear; lia| exact CR0| clear; lia| exact LR0| clear; lia
       | exact ELV| intros a _ _; exact I| intros x _; exact I| intros x _; exact I| exact PERM| exact CFR| exact ND| exact LPOS| exact NTL].
    eapply (mbio_rep_keep (rt_live RT Σ)); [exact MB| exact PR| intros e He; split; exact (ELV _ (KLV _ He))| intros e x _ _; exact I].
  Qed.
  Lemma com_icpt_blk : forall (en : pem_entry) Σ (m m' : mem) off crem lrem cur d n p sz,
    pem_com en Σ m off crem lrem cur -> ART RT Σ m' -> mem_inv asegs m' -> stk asegs m' (e_lo RT en) (e_sp1 RT en) ->
    rt_pres_ex (rt_live RT Σ) (rt_frames RT Σ) (e_sp1 RT en) d n m m' -> In (p, sz) cur -> 0 < sz -> p <= d -> d + n <= p + sz ->
    pem_com en Σ m' off crem lrem cur /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (e_sp1 RT en) [(p, p + sz)] m m' /\ w_ok RT en Σ [(p, sz)] [(p, p + sz)].
  Proof using AF AFP libenv_agree libenv_fp_where.
    intros en Σ m m' off crem lrem cur d n p sz COM ART1 MI1 ST1 PX HP POS D1 D2.
    pose proof COM as (ART0 & MI & ST & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & NTL & MB & OFF & BLT & KLV & PERM & CFR & ND & LPOS
       & FRS & FRN & SP0 & CG & LIV & LR0 & CR & CR0 & CRE & CGH & CGS & CTX & UWC & F0 & F64 & FTOP & FSEG & FSH & FFS & SAVED & PRES & FLR & NDO & OUTS & FDO & MST).
    destruct (com_lists RT libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ COM) as [ELV CLV].
    assert (PR : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (e_sp1 RT en) [(p, p + sz)] m m') by (intros a Ha [Ho _]; apply PX; [exact Ha| clear - Ho D1 D2; lia]).
    pose proof (com_WB_ok RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem cur [(p, sz)] COM ltac:(intros e' [<-|[]]; left; split; [exact HP| exact POS])) as WOK.
    pose proof WOK as (HWS & HWFR & HWFF & HWF & HWL & HWP). cbn [map rng fst snd] in HWS, HWFF, HWF, HWL, HWP.
    split; [| split; [exact PR| exact WOK]].
    assert (XLV : forall e, In e [(p, sz)] -> In e (rt_live RT Σ)) by (intros e [<-|[]]; exact (CLV _ HP)).
    assert (CLE1 : cl_env m' (Z_to_bv 8 1) (e_canary RT en)).
    { eapply cl_env_pres_ex; [exact CLE| exact PX|]. intros x Hx R.
      pose proof (com_WB_static RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem cur _ COM XLV x (cl_cell_static _ Hx)) as [X _]. cbn [rng fst snd] in X. clear - X R D1 D2. lia. }
    assert (LE1 : libenv m' (e_LBL RT en) (e_E RT en)).
    { eapply (libenv_keep libenv libenv_fp libenv_agree libenv_fp_where); [exact LE| exact PR| intros e He; exact (ELV _ (INCL _ He))|].
      intros x Hx. destruct (libenv_fp_where _ _ Hx) as [(_ & CS & _)|(p' & n' & Hin & Hp)].
      - exact (com_WB_static RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem cur _ COM XLV x CS).
      - apply (HWL p' n' x (ELV _ (INCL _ Hin))); [| exact Hp]. intros [X|[]].
        apply (CFR _ HP). cbn [fst]. injection X. intros _ Ep. rewrite Ep. exact (in_map fst _ _ (INCL _ Hin)). }
    assert (SEC1 : sec_off m').
    { eapply sec_off_agree; [exact SEC|]. intros a Ea. rewrite <- (Z_to_bv_bv_unsigned a), Ea.
      apply PR; rewrite (unsigned_lit SEC_INIT) by (unfold SEC_INIT; clear; lia); [apply acl_static; apply client_static_intro; unfold SEC_INIT; clear; lia|].
      exact (com_WB_static RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem cur _ COM XLV SEC_INIT ltac:(apply client_static_intro; unfold SEC_INIT; clear; lia)). }
    eapply (com_call RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ Σ m m' off off crem crem lrem lrem _ cur _ _ 0 COM ART1 MI1 ST1 PR CLE1 SEC1 LE1);
      [| exact OFF| reflexivity| reflexivity| reflexivity| clear; lia| exact CR0| clear; lia| exact LR0| clear; lia
       | exact ELV| exact HWP| exact HWS| exact HWF| exact PERM| exact CFR| exact ND| exact LPOS| exact NTL].
    eapply (mbio_rep_keep (rt_live RT Σ)); [exact MB| exact PR| intros e He; split; exact (ELV _ (KLV _ He))|].
    intros e x He Hx. exact (com_klv_outX RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ _ _ COM HWL ltac:(intros e' [<-|[]]; right; exact HP) e x He Hx).
  Qed.
  (* [comment removed for export] *)
  Lemma com_chk_cur : forall (en : pem_entry) Σ (m : mem) off crem lrem cur p sz s k,
    pem_com en Σ m off crem lrem cur -> In (p, sz) cur -> 0 < sz -> p <= s -> s + k <= p + sz -> 0 <= k ->
    checked_src RT Σ m (wz (e_sp1 RT en)) (e_lo RT en) s k.
  Proof using AF AFP.
    intros en Σ m off crem lrem cur p sz s k COM HP POS H1 H2 K0.
    pose proof COM as (ART0 & _). destruct (com_lists RT libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ COM) as [ELV CLV].
    pose proof (cur_live_facts RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem cur (p, sz) COM HP POS) as (INP & _ & PLO & _). cbn [fst snd] in PLO.
    split; [| left; clear - PLO H2; lia]. intros _. split.
    - destruct (af_acc_live RT AF Σ m p sz ART0 INP) as [_ ACC]. eapply acc_sub; [exact ACC| lia| lia].
    - left. exists p, sz. split; [exact INP| clear - H1 H2; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma pem_icpt_strncmp : strncmp_icontract RT ->
    forall T (en : pem_entry) Σ (m : mem) off crem lrem cur p1 p2 n (b1 b2 : list byte) site (F : bvmap 5 word) (fc : bv 32)
           (t0 t1 t2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6 : word) c,
    pem_com en Σ m off crem lrem cur -> 0 < n < 2 ^ 31 -> bytes_at asegs m p1 b1 -> bytes_at asegs m p2 b2 -> strncmp_ok n b1 b2 ->
    checked_src RT Σ m (wz (e_sp1 RT en)) (e_lo RT en) p1 (strncmp_sz n b1 b2) -> checked_src RT Σ m (wz (e_sp1 RT en)) (e_lo RT en) p2 (strncmp_sz n b1 b2) ->
    0 <= site < 2 ^ 64 -> site mod 2 = 0 ->
    ASTA RT Σ (e_PMc RT en) (eq (pem_ms en e_strncmp m F fc (wz site) t0 t1 t2 (wz p1) (wz p2) (wz n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6)) c ->
    (forall (m' : mem) (F' : bvmap 5 word) (fc' : bv 32) (y0 y1 y2 b1' b2' b3 b4 b5 b6 b7 y3 y4 y5 y6 : word) c',
       pem_com en Σ m' off crem lrem cur -> rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (e_sp1 RT en) [] m m' -> mem_inv asegs m' ->
       ASTA RT Σ (e_PMc RT en) (eq (pem_ms en site m' F' fc' (wz site) y0 y1 y2 (wz (strncmp_res n b1 b2)) b1' b2' b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s10 s11 y3 y4 y5 y6)) c' ->
       realizes asegs c' T) ->
    realizes asegs c T.
  Proof using AF AFP libenv_agree libenv_fp_where.
    intros SNC T en Σ m off crem lrem cur p1 p2 n b1 b2 site F fc t0 t1 t2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6 c COM HN B1 B2 OK CK1 CK2 SR SE HA Hk.
    pose proof COM as (ART0 & MI & ST & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & NTL & MB & OFF & BLT & KLV & PERM & CFR & ND & LPOS
       & FRS & FRN & SP0 & CG & LIV & LR0 & CR & CR0 & CRE & CGH & CGS & CTX & UWC & F0 & F64 & FTOP & FSEG & FSH & FFS & SAVED & PRES & FLR & NDO & OUTS & FDO & MST).
    destruct (com_call_pre0 RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ COM) as (EU & COK & INCL1 & FRMAX & CRED & HLO & H352).
    apply (SNC Σ (e_PMc RT en) (wz site) (wz (e_sp1 RT en)) (e_gp RT en) (wz TP_A) t0 t1 t2 (e_sp RT en) (wz (e_sp1 RT en)) (wz p1) (wz p2) (wz n) a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 (wz (shad (e_f RT en))) (wz SHB) s10 s11 t3 t4 t5 t6 F fc m p1 p2 n b1 b2 (e_lo RT en)
             FDO MST eq_refl eq_refl eq_refl HN B1 B2 OK CK1 CK2 ART0 MI COK T c HA).
    intros c' AP. unfold icpt_post in AP.
    destruct (ASTA_unpack RT Σ _ _ c' AP) as (ms' & (m' & RS & (ART1 & MI1 & WM1 & ST1) & PX & _) & Hc'). clear AP.
    destruct RS as (y0 & y1 & y2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y3 & y4 & y5 & y6 & F' & fc' & ->).
    rewrite EU in ST1, PX. rewrite (ret_pc_even site SR SE) in Hc'.
    destruct (com_icpt0 en Σ m m' off crem lrem cur COM ART1 MI1 ST1 PX) as [COM1 PR].
    exact (Hk m' F' fc' y0 y1 y2 d1 d2 d3 d4 d5 d6 d7 y3 y4 y5 y6 c' COM1 PR MI1 Hc').
  Qed.

  (* [comment removed for export] *)
  Lemma pem_icpt_memchr : memchr_icontract RT ->
    forall T (en : pem_entry) Σ (m : mem) off crem lrem cur s cz n (buf : list byte) site (F : bvmap 5 word) (fc : bv 32)
           (t0 t1 t2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6 : word) c,
    pem_com en Σ m off crem lrem cur -> 0 < s <= 2 ^ 47 -> 0 <= cz < 256 -> 0 <= n < 2 ^ 40 -> bytes_at asegs m s buf -> memchr_ok s cz n buf ->
    (s + Z.of_nat (length buf) <= e_lo RT en) -> checked_src RT Σ m (wz (e_sp1 RT en)) (e_lo RT en) s (memchr_chk cz n buf) ->
    0 <= site < 2 ^ 64 -> site mod 2 = 0 ->
    ASTA RT Σ (e_PMc RT en) (eq (pem_ms en e_memchr m F fc (wz site) t0 t1 t2 (wz s) (wz cz) (wz n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6)) c ->
    (forall (m' : mem) (F' : bvmap 5 word) (fc' : bv 32) (y0 y1 y2 b1' b2' b3 b4 b5 b6 b7 y3 y4 y5 y6 : word) c',
       pem_com en Σ m' off crem lrem cur -> rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (e_sp1 RT en) [] m m' -> mem_inv asegs m' ->
       ASTA RT Σ (e_PMc RT en) (eq (pem_ms en site m' F' fc' (wz site) y0 y1 y2 (wz (memchr_res s cz n buf)) b1' b2' b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s10 s11 y3 y4 y5 y6)) c' ->
       realizes asegs c' T) ->
    realizes asegs c T.
  Proof using AF AFP libenv_agree libenv_fp_where.
    intros MCHR T en Σ m off crem lrem cur s cz n buf site F fc t0 t1 t2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6 c COM HS HC HN BB OK LO CK SR SE HA Hk.
    pose proof COM as (ART0 & MI & ST & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & NTL & MB & OFF & BLT & KLV & PERM & CFR & ND & LPOS
       & FRS & FRN & SP0 & CG & LIV & LR0 & CR & CR0 & CRE & CGH & CGS & CTX & UWC & F0 & F64 & FTOP & FSEG & FSH & FFS & SAVED & PRES & FLR & NDO & OUTS & FDO & MST).
    destruct (com_call_pre0 RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ COM) as (EU & COK & INCL1 & FRMAX & CRED & HLO & H352).
    apply (MCHR Σ (e_PMc RT en) (wz site) (wz (e_sp1 RT en)) (e_gp RT en) (wz TP_A) t0 t1 t2 (e_sp RT en) (wz (e_sp1 RT en)) (wz s) (wz cz) (wz n) a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 (wz (shad (e_f RT en))) (wz SHB) s10 s11 t3 t4 t5 t6 F fc m s cz n buf (e_lo RT en)
             FDO MST eq_refl eq_refl eq_refl HS HC HN BB OK (or_introl LO) CK ART0 MI COK T c HA).
    intros c' AP. unfold icpt_post in AP.
    destruct (ASTA_unpack RT Σ _ _ c' AP) as (ms' & (m' & RS & (ART1 & MI1 & WM1 & ST1) & PX & _) & Hc'). clear AP.
    destruct RS as (y0 & y1 & y2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y3 & y4 & y5 & y6 & F' & fc' & ->).
    rewrite EU in ST1, PX. rewrite (ret_pc_even site SR SE) in Hc'.
    destruct (com_icpt0 en Σ m m' off crem lrem cur COM ART1 MI1 ST1 PX) as [COM1 PR].
    exact (Hk m' F' fc' y0 y1 y2 d1 d2 d3 d4 d5 d6 d7 y3 y4 y5 y6 c' COM1 PR MI1 Hc').
  Qed.

  (* [comment removed for export] *)
  Lemma pem_icpt_strlen : strlen_icontract RT ->
    forall T (en : pem_entry) Σ (m : mem) off crem lrem cur s (str slack : list byte) site (F : bvmap 5 word) (fc : bv 32)
           (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6 : word) c,
    pem_com en Σ m off crem lrem cur -> bytes_at asegs m s (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str -> Z.of_nat (length str) < 2 ^ 40 ->
    (- (s + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) -> 0 < s <= 2 ^ 47 ->
    s + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= e_lo RT en -> checked_src RT Σ m (wz (e_sp1 RT en)) (e_lo RT en) s (Z.of_nat (length str) + 1) ->
    0 <= site < 2 ^ 64 -> site mod 2 = 0 ->
    ASTA RT Σ (e_PMc RT en) (eq (pem_ms en e_strlen m F fc (wz site) t0 t1 t2 (wz s) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6)) c ->
    (forall (m' : mem) (F' : bvmap 5 word) (fc' : bv 32) (y0 y1 y2 b1' b2' b3 b4 b5 b6 b7 y3 y4 y5 y6 : word) c',
       pem_com en Σ m' off crem lrem cur -> rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (e_sp1 RT en) [] m m' -> mem_inv asegs m' ->
       ASTA RT Σ (e_PMc RT en) (eq (pem_ms en site m' F' fc' (wz site) y0 y1 y2 (wz (Z.of_nat (length str))) b1' b2' b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s10 s11 y3 y4 y5 y6)) c' ->
       realizes asegs c' T) ->
    realizes asegs c T.
  Proof using AF AFP libenv_agree libenv_fp_where.
    intros SLC T en Σ m off crem lrem cur s str slack site F fc t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6 c COM BB NZ LS SLK HS LO CK SR SE HA Hk.
    pose proof COM as (ART0 & MI & ST & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & NTL & MB & OFF & BLT & KLV & PERM & CFR & ND & LPOS
       & FRS & FRN & SP0 & CG & LIV & LR0 & CR & CR0 & CRE & CGH & CGS & CTX & UWC & F0 & F64 & FTOP & FSEG & FSH & FFS & SAVED & PRES & FLR & NDO & OUTS & FDO & MST).
    destruct (com_call_pre0 RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ COM) as (EU & COK & INCL1 & FRMAX & CRED & HLO & H352).
    apply (SLC Σ (e_PMc RT en) (wz site) (wz (e_sp1 RT en)) (e_gp RT en) (wz TP_A) t0 t1 t2 (e_sp RT en) (wz (e_sp1 RT en)) (wz s) a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 (wz (shad (e_f RT en))) (wz SHB) s10 s11 t3 t4 t5 t6 F fc m s str slack (e_lo RT en)
             FDO MST eq_refl BB NZ LS SLK HS (or_introl LO) CK ART0 MI COK T c HA).
    intros c' AP. unfold icpt_post in AP.
    destruct (ASTA_unpack RT Σ _ _ c' AP) as (ms' & (m' & RS & (ART1 & MI1 & WM1 & ST1) & PX & _) & Hc'). clear AP.
    destruct RS as (y0 & y1 & y2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y3 & y4 & y5 & y6 & F' & fc' & ->).
    rewrite EU in ST1, PX. rewrite (ret_pc_even site SR SE) in Hc'.
    destruct (com_icpt0 en Σ m m' off crem lrem cur COM ART1 MI1 ST1 PX) as [COM1 PR].
    exact (Hk m' F' fc' y0 y1 y2 d1 d2 d3 d4 d5 d6 d7 y3 y4 y5 y6 c' COM1 PR MI1 Hc').
  Qed.

  (* [comment removed for export] *)
  Lemma pem_icpt_memcpy : memcpy_icontract RT e_asan_memcpy ->
    forall T (en : pem_entry) Σ (m : mem) off crem lrem cur d s p sz (bs : list byte) site (F : bvmap 5 word) (fc : bv 32)
           (t0 t1 t2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6 : word) c,
    pem_com en Σ m off crem lrem cur -> In (p, sz) cur -> 0 < sz -> p <= d -> d + Z.of_nat (length bs) <= p + sz ->
    0 <= s <= 2 ^ 47 -> Z.of_nat (length bs) < 2 ^ 40 -> bytes_at asegs m s bs -> checked_src RT Σ m (wz (e_sp1 RT en)) (e_lo RT en) s (Z.of_nat (length bs)) ->
    (d + Z.of_nat (length bs) <= s \/ s + Z.of_nat (length bs) <= d) ->
    0 <= site < 2 ^ 64 -> site mod 2 = 0 ->
    ASTA RT Σ (e_PMc RT en) (eq (pem_ms en e_asan_memcpy m F fc (wz site) t0 t1 t2 (wz d) (wz s) (wz (Z.of_nat (length bs))) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6)) c ->
    (forall (m' : mem) (F' : bvmap 5 word) (fc' : bv 32) (y0 y1 y2 b1' b2' b3 b4 b5 b6 b7 y3 y4 y5 y6 : word) c',
       pem_com en Σ m' off crem lrem cur -> rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (e_sp1 RT en) [(p, p + sz)] m m' -> w_ok RT en Σ [(p, sz)] [(p, p + sz)] ->
       rt_pres_ex (rt_live RT Σ) (rt_frames RT Σ) (e_sp1 RT en) d (Z.of_nat (length bs)) m m' -> mem_inv asegs m' -> bytes_at asegs m' d bs ->
       ASTA RT Σ (e_PMc RT en) (eq (pem_ms en site m' F' fc' (wz site) y0 y1 y2 (wz d) b1' b2' b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s10 s11 y3 y4 y5 y6)) c' ->
       realizes asegs c' T) ->
    realizes asegs c T.
  Proof using AF AFP libenv_agree libenv_fp_where.
    intros MCP T en Σ m off crem lrem cur d s p sz bs site F fc t0 t1 t2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6 c COM HP POS D1 D2 HS LS BB CKS AP0 SR SE HA Hk.
    pose proof COM as (ART0 & MI & ST & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & NTL & MB & OFF & BLT & KLV & PERM & CFR & ND & LPOS
       & FRS & FRN & SP0 & CG & LIV & LR0 & CR & CR0 & CRE & CGH & CGS & CTX & UWC & F0 & F64 & FTOP & FSEG & FSH & FFS & SAVED & PRES & FLR & NDO & OUTS & FDO & MST).
    destruct (com_lists RT libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ COM) as [ELV CLV].
    destruct (com_call_pre0 RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ COM) as (EU & COK & INCL1 & FRMAX & CRED & HLO & H352).
    pose proof (cur_live_facts RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem cur (p, sz) COM HP POS) as (INP & P0 & PLO & PHI & NAC). cbn [fst snd] in P0, PLO, PHI, NAC.
    pose proof (af_sp0_range RT AF Σ m ART0) as SPR.
    assert (CKD : checked_dst RT Σ m (wz (e_sp1 RT en)) d (Z.of_nat (length bs))).
    { split; [| split].
      - intros _. split; [destruct (af_acc_live RT AF Σ m p sz ART0 INP) as [_ ACC]; eapply acc_sub; [exact ACC| lia| lia]| left; exists p, sz; split; [exact INP| lia]].
      - intros i Hi. rewrite EU. apply (acl_live _ _ _ p sz); [exact INP| lia].
      - destruct (af_acc_live RT AF Σ m p sz ART0 INP) as [WR _]. eapply wr_at_sub; [exact WR| lia| lia| lia]. }
    apply (MCP Σ (e_PMc RT en) (wz site) (wz (e_sp1 RT en)) (e_gp RT en) (wz TP_A) t0 t1 t2 (e_sp RT en) (wz (e_sp1 RT en)) (wz d) (wz s) (wz (Z.of_nat (length bs))) a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 (wz (shad (e_f RT en))) (wz SHB) s10 s11 t3 t4 t5 t6 F fc m d s bs (e_lo RT en)
             FDO MST eq_refl eq_refl eq_refl ltac:(clear - P0 PLO D1 D2 HLO TOP PD; unfold e_sp1, USTACK_TOP in *; lia) HS LS BB CKS CKD AP0 ART0 MI COK T c HA).
    intros c' AP. unfold icpt_post in AP.
    destruct (ASTA_unpack RT Σ _ _ c' AP) as (ms' & (m' & RS & (ART1 & MI1 & WM1 & ST1) & PX & BB1) & Hc'). clear AP.
    destruct RS as (y0 & y1 & y2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & y3 & y4 & y5 & y6 & F' & fc' & ->).
    rewrite EU in ST1, PX. rewrite (ret_pc_even site SR SE) in Hc'.
    destruct (com_icpt_blk en Σ m m' off crem lrem cur d (Z.of_nat (length bs)) p sz COM ART1 MI1 ST1 PX HP POS D1 D2) as (COM1 & PR & WOK).
    exact (Hk m' F' fc' y0 y1 y2 e1 e2 e3 e4 e5 e6 e7 y3 y4 y5 y6 c' COM1 PR WOK PX MI1 BB1 Hc').
  Qed.
  (* [comment removed for export] *)
  Lemma w_ok_sub : forall (en : pem_entry) Σ XL W W',
    w_ok RT en Σ XL W' -> (forall x, outside W' x -> outside W x) -> w_ok RT en Σ XL W.
  Proof.
    intros en Σ XL W W' (WS & WFR & WFF & WSH & WL & WP) SUB.
    split; [intros x Hx; exact (SUB _ (WS x Hx))|]. split; [intros f k x H1 H2; exact (SUB _ (WFR f k x H1 H2))|]. split; [intros x Hx; exact (SUB _ (WFF x Hx))|].
    split; [intros x Hx; exact (SUB _ (WSH x Hx))|]. split; [intros p n x H1 H2 H3; exact (SUB _ (WL p n x H1 H2 H3))| intros a H1 H2; exact (SUB _ (WP a H1 H2))].
  Qed.
  Lemma w_ok_app : forall (en : pem_entry) Σ XL1 XL2 W1 W2,
    w_ok RT en Σ XL1 W1 -> w_ok RT en Σ XL2 W2 -> w_ok RT en Σ (XL1 ++ XL2) (W1 ++ W2).
  Proof.
    intros en Σ XL1 XL2 W1 W2 (WS & WFR & WFF & WSH & WL & WP) (WS' & WFR' & WFF' & WSH' & WL' & WP').
    split; [intros x Hx; apply outside_app_intro; [exact (WS x Hx)| exact (WS' x Hx)]|].
    split; [intros f k x H1 H2; apply outside_app_intro; [exact (WFR f k x H1 H2)| exact (WFR' f k x H1 H2)]|].
    split; [intros x Hx; apply outside_app_intro; [exact (WFF x Hx)| exact (WFF' x Hx)]|].
    split; [intros x Hx; apply outside_app_intro; [exact (WSH x Hx)| exact (WSH' x Hx)]|].
    split; [intros p n x H1 H2 H3; apply outside_app_intro; [apply (WL p n x H1); [| exact H3]| apply (WL' p n x H1); [| exact H3]]; intros X; apply H2; apply in_or_app; tauto|].
    intros a H1 H2. apply outside_app_intro; [exact (WP a H1 H2)| exact (WP' a H1 H2)].
  Qed.
  Lemma ids_live : forall (en : pem_entry) Σ (m : mem) off crem lrem cur,
    pem_com en Σ m off crem lrem cur -> forall q, In q (map fst cur ++ e_E RT en :: mbio_blocks (e_K RT en)) -> exists e, In e (rt_live RT Σ) /\ fst e = q.
  Proof using AF AFP.
    intros en Σ m off crem lrem cur COM q Hq.
    pose proof COM as (ART0 & MI & ST & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & NTL & MB & OFF & BLT & KLV & REST).
    destruct (com_lists RT libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ COM) as [ELV CLV].
    apply in_app_iff in Hq. destruct Hq as [Hq|[<-|Hq]].
    - apply in_map_iff in Hq. destruct Hq as (e & <- & He). exists e. split; [exact (CLV _ He)| reflexivity].
    - exists (e_E RT en, 904). split; [exact (ELV _ INE)| reflexivity].
    - rewrite <- (mbio_ent_fst (e_K RT en) (e_bmax RT en)) in Hq. apply in_map_iff in Hq. destruct Hq as (e & <- & He). exists e. split; [exact (ELV _ (KLV _ He))| reflexivity].
  Qed.
  Lemma mbio_ent_pos : forall live (m : mem) K BI BM blw meth len max off, mbio_repx live m K BI BM blw meth len max off -> forall e, In e (mbio_ent K max) -> 0 < snd e.
  Proof.
    intros live m K BI BM blw meth len max off MBX e He.
    destruct MBX as (fl & rrw & numw & padw & nr & nw & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & INNER). destruct INNER as (rmaxw & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & DK).
    unfold mbio_ent in He. apply in_app_iff in He. destruct He as [He|He].
    - destruct He as [<-|[<-|[<-|[<-|[]]]]]; cbn; lia.
    - destruct (k_d K) as [d|]; [| destruct He]. destruct He as [<-|[]]. cbn. destruct DK as (junk & _ & POS & _). exact POS.
  Qed.

  Lemma pem_calls_cnew : forall r G, In r PEM_RAS_cnew -> In G [FZ_EVP_CTX_NEW; e_CRYPTO_zalloc] -> In (r, G) PEM_CALLS.
  Proof.
    intros r G Hr HG. unfold PEM_CALLS. rewrite !in_app_iff. do 8 right. left. apply in_concat. exists [(r, FZ_EVP_CTX_NEW); (r, e_CRYPTO_zalloc)].
    split; [apply in_map_iff; exists r; split; [reflexivity| exact Hr]|]. cbn in HG |- *. destruct HG as [<-|[<-|[]]]; tauto.
  Qed.
  Lemma pem_calls_bnew : forall r, In r PEM_RAS_new -> In (r, FZ_BIO_NEW) PEM_CALLS.
  Proof. intros r Hr. unfold PEM_CALLS. rewrite !in_app_iff. left. apply in_map_iff. exists r. split; [reflexivity| exact Hr]. Qed.

  (* [comment removed for export] *)
  Lemma pem_call_binfo : bio_ctrl_info_stmt RT ->
    forall T (en : pem_entry) Σ (m : mem) off crem lrem cur K BIv meth len max offK site (F : bvmap 5 word) (fc : bv 32)
           (t0 t1 t2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6 : word) c,
    pem_com en Σ m off crem lrem cur -> mbio_rep (rt_live RT Σ) m K BIv meth len max offK -> 0 <= site < 2 ^ 64 -> site mod 2 = 0 ->
    ASTA RT Σ (e_PMc RT en) (eq (pem_ms en FZ_BIO_CTRL m F fc (wz site) t0 t1 t2 (wz BIv) (wz 3) (wz 0) (wz 0) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6)) c ->
    (forall (m' : mem) (F' : bvmap 5 word) (fc' : bv 32) (y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 : word) c',
       pem_com en Σ m' off crem lrem cur -> rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (e_sp1 RT en) [] m m' -> mem_inv asegs m' ->
       mbio_rep (rt_live RT Σ) m' K BIv meth len max offK ->
       ASTA RT Σ (e_PMc RT en) (eq (pem_ms en site m' F' fc' (wz site) y0 y1 y2 (wz (len - offK)) b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s10 s11 y3 y4 y5 y6)) c' ->
       realizes asegs c' T) ->
    realizes asegs c T.
  Proof using AF AFP libenv_agree libenv_fp_where.
    intros C_BI T en Σ m off crem lrem cur K BIv meth len max offK site F fc t0 t1 t2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6 c COM MBK SR SE HA Hk.
    pose proof COM as (ART0 & MI & ST & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & NTL & MB & OFF & BLT & KLV & PERM & CFR & ND & LPOS
       & FRS & FRN & SP0 & CG & LIV & LR0 & CR & CR0 & CRE & CGH & CGS & CTX & UWC & F0 & F64 & FTOP & FSEG & FSH & FFS & SAVED & PRES & FLR & NDO & OUTS & FDO & MST).
    destruct (com_call_pre0 RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ COM) as (EU & COK & INCL1 & FRMAX & CRED & HLO & H352).
    apply (C_BI Σ (e_PMc RT en) (wz site) (wz (e_sp1 RT en)) (e_gp RT en) (wz TP_A) t0 t1 t2 (e_sp RT en) (wz (e_sp1 RT en)) (wz BIv) (wz 3) (wz 0) (wz 0) a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 (wz (shad (e_f RT en))) (wz SHB) s10 s11 t3 t4 t5 t6 F fc m (e_lo RT en) (e_canary RT en) K BIv meth len max offK
             FDO MST eq_refl eq_refl eq_refl eq_refl eq_refl MBK ART0 MI COK ltac:(rewrite EU; clear - LOR; unfold PEM_CALLEE_STACK, BCTRL_STACK in *; lia) CLE T c HA).
    intros c' AP. unfold apost in AP.
    destruct (ASTA_unpack RT Σ _ _ c' AP) as (ms' & (v & m' & RS & (ART1 & MI1 & ST1) & PR & CLE1 & (-> & WM1 & MBK1)) & Hc'). clear AP.
    destruct RS as (y0 & y1 & y2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & y3 & y4 & y5 & y6 & F' & fc' & ->).
    rewrite EU in ST1, PR. rewrite (ret_pc_even site SR SE) in Hc'.
    assert (PX : rt_pres_ex (rt_live RT Σ) (rt_frames RT Σ) (e_sp1 RT en) 0 0 m m') by (intros a Ha _; exact (PR a Ha I)).
    destruct (com_icpt0 en Σ m m' off crem lrem cur COM ART1 MI1 ST1 PX) as [COM1 _].
    exact (Hk m' F' fc' y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 c' COM1 PR MI1 MBK1 Hc').
  Qed.

  (* [comment removed for export] *)
  Lemma pem_call_cnew : evp_ctx_new_stmt RT FZ_SITES FZ_CALLS ->
    forall T (en : pem_entry) Σ (m : mem) off crem lrem cur site (F : bvmap 5 word) (fc : bv 32)
           (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6 : word) c,
    pem_com en Σ m off crem lrem cur -> 1 <= lrem -> In site PEM_RAS_cnew ->
    ASTA RT Σ (e_PMc RT en) (eq (pem_ms en FZ_EVP_CTX_NEW m F fc (wz site) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6)) c ->
    (forall Σ' (m' : mem) (F' : bvmap 5 word) (fc' : bv 32) (y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 : word) c' (p : Z),
       pem_com en Σ' m' off crem (lrem - 1) ((p, ECTX) :: cur) ->
       rt_live RT Σ' = (p, ECTX) :: rt_live RT Σ -> rt_frames RT Σ' = rt_frames RT Σ ->
       rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (e_sp1 RT en) [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] m m' ->
       rw_cells asegs m' p [CB (Z.to_nat ECTX) (repeat (Z_to_bv 8 0) (Z.to_nat ECTX))] -> 0 < p -> p mod 16 = 0 -> p + ECTX < USTACK_TOP ->
       ASTA RT Σ' (e_PMc RT en) (eq (pem_ms en site m' F' fc' (wz site) y0 y1 y2 (wz p) b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s10 s11 y3 y4 y5 y6)) c' ->
       realizes asegs c' T) ->
    realizes asegs c T.
  Proof using AF AFP libenv_agree libenv_fp_where.
    intros C_CN T en Σ m off crem lrem cur site F fc t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6 c COM LRM HSI HA Hk.
    pose proof COM as (ART0 & MI & ST & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & NTL & MB & OFF & BLT & KLV & PERM & CFR & ND & LPOS
       & FRS & FRN & SP0 & CG & LIV & LR0 & CR & CR0 & CRE & CGH & CGS & CTX & UWC & F0 & F64 & FTOP & FSEG & FSH & FFS & SAVED & PRES & FLR & NDO & OUTS & FDO & MST).
    destruct (com_lists RT libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ COM) as [ELV CLV].
    pose proof (w_ok_sub en Σ (e_LBL RT en) [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] _ (com_W_ok RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ COM)
                  ltac:(intros x Hx; cbn; split; [| exact I]; unfold lib_W, LIB_W in Hx; apply outside_app_l in Hx; cbn in Hx; unfold G_ALLOW_CUST; clear - Hx; lia)) as WOK.
    pose proof WOK as (HWS & HWFR & HWFF & HWF & HWL & HWP).
    assert (HSR : In site PEM_RAS) by (unfold PEM_RAS; rewrite !in_app_iff; tauto).
    assert (SR : 0 <= site < 2 ^ 64) by (clear - HSI; unfold PEM_RAS_cnew in HSI; cbn in HSI; lia).
    destruct (com_call_pre RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ site FZ_EVP_CTX_NEW COM (pem_site_in _ HSR) (pem_calls_cnew _ FZ_EVP_CTX_NEW HSI ltac:(cbn; tauto)) SR)
      as (EU & COK & CTX1 & UWC1 & INCL1 & FRMAX & CRED & HLO & H352).
    assert (HCG : In (bv_unsigned (wz site), e_CRYPTO_zalloc) (cg_call (rt_cg RT Σ))).
    { rewrite (unsigned_lit site) by exact SR. exact (proj2 CGH _ (proj2 CGS _ (pem_calls_cnew _ e_CRYPTO_zalloc HSI ltac:(cbn; tauto)))). }
    apply (C_CN Σ (e_PMc RT en) (wz site) (wz (e_sp1 RT en)) (e_gp RT en) (wz TP_A) t0 t1 t2 (e_sp RT en) (wz (e_sp1 RT en)) a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 (wz (shad (e_f RT en))) (wz SHB) s10 s11 t3 t4 t5 t6 F fc m (e_lo RT en) (bv_unsigned (e_ra RT en) :: e_outer RT en) (e_canary RT en)
             FDO MST eq_refl ART0 MI COK ltac:(rewrite EU; clear - LOR; unfold PEM_CALLEE_STACK in *; lia) CLE CTX1 UWC1 CGH HCG
             ltac:(clear - LIV LRM; lia) ltac:(clear - CRED CR0; lia) T c HA).
    intros c' (Σ' & p & AP & LV' & FRS' & SP' & CR' & CG' & P0 & P16 & PTOP). unfold apost in AP.
    destruct (ASTA_unpack RT Σ' _ _ c' AP) as (ms' & (v & m' & RS & (ART1 & MI1 & ST1) & PR & CLE1 & (-> & WM1 & PC)) & Hc'). clear AP.
    destruct RS as (y0 & y1 & y2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & y3 & y4 & y5 & y6 & F' & fc' & ->).
    rewrite EU in ST1, PR. rewrite (ret_pc_even site SR) in Hc' by (clear - HSI; unfold PEM_RAS_cnew in HSI; cbn in HSI; lia).
    assert (FP : forall e, In e ([] ++ rt_live RT Σ) -> fst e <> p).
    { apply (live_fresh RT AF Σ' m' [] p ECTX (rt_live RT Σ) ART1); [rewrite LV'; reflexivity| unfold ECTX; clear; lia| intros e He; exact (LPOS e He)]. }
    cbn [app] in FP.
    assert (LE1 : libenv m' (e_LBL RT en) (e_E RT en)).
    { eapply (libenv_keep libenv libenv_fp libenv_agree libenv_fp_where); [exact LE| exact PR| exact INCL1|].
      intros x Hx. cbn. split; [| exact I]. destruct (libenv_fp_where _ _ Hx) as [(_ & CS & NC)|(p' & n' & Hin & Hp)].
      - intros R. apply NC. exists G_ALLOW_CUST, (G_ALLOW_CUST + 1). split; [unfold CL_CELLS; cbn; tauto| exact R].
      - pose proof (af_live_range RT AF Σ m p' n' ART0 (INCL1 _ Hin)) as (_ & _ & Y). clear - Y Hp. unfold G_ALLOW_CUST, SEGTOP_A in *. lia. }
    assert (SEC1 : sec_off m').
    { eapply sec_off_agree; [exact SEC|]. intros a Ea. apply PR; [apply acl_static; rewrite Ea; apply client_static_intro; unfold SEC_INIT; clear; lia|].
      rewrite Ea. cbn. split; [unfold SEC_INIT, G_ALLOW_CUST; clear; lia| exact I]. }
    eapply (Hk Σ' m' F' fc' y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 c' p); [| exact LV'| exact FRS'| exact PR| exact PC| exact P0| exact P16| exact PTOP| exact Hc'].
    eapply (com_call RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ Σ' m m' off off crem crem lrem (lrem - 1) _ _ _ _ 0 COM ART1 MI1 ST1 PR CLE1 SEC1 LE1);
      [| exact OFF| exact FRS'| exact SP'| exact CG'| rewrite CR'; clear; lia| exact CR0| clear; lia| clear - LRM; lia| rewrite LV'; cbn [length]; clear; lia
       | exact ELV| exact HWP| exact HWS| exact HWF| | | | | ].
    - eapply (mbio_rep_keep (rt_live RT Σ)); [exact MB| exact PR| intros e He; rewrite LV'; split; [| right]; exact (ELV _ (KLV _ He))|].
      intros e x He Hx. exact (com_klv_out RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ _ _ COM HWL (fun e H => or_intror H) e x He Hx).
    - rewrite LV'. cbn [app]. apply perm_skip. exact PERM.
    - intros e [<-|He]; [| exact (CFR e He)]. cbn [fst]. intros X. apply in_map_iff in X. destruct X as (e' & E' & He'). exact (FP e' (ELV _ He') E').
    - cbn [map fst app]. apply (nd_insert1 []); [exact ND|]. cbn [app]. intros X. destruct (ids_live en Σ m off crem lrem cur COM p X) as (e' & He' & E'). exact (FP e' He' E').
    - intros e He. rewrite LV' in He. destruct He as [<-|He]; [cbn; unfold ECTX; clear; lia| exact (LPOS e He)].
    - intros e He X. apply in_app_iff in X. destruct X as [X|X]; [exact (NTL e He ltac:(apply in_or_app; left; exact X))|].
      cbn [map fst] in X. destruct X as [X|X]; [| exact (NTL e He ltac:(apply in_or_app; right; exact X))].
      refine (FP e _ (eq_sym X)). destruct He as [<-|He]; [exact (ELV _ INE)| exact (ELV _ (INCL _ He))].
  Qed.
  (* [comment removed for export] *)
  Lemma pem_call_bread : bio_read_stmt RT ->
    forall T (en : pem_entry) Σ (m : mem) off crem lrem rest K BIv BM blw meth len max offK OUT no n (ojunk : list byte) site (F : bvmap 5 word) (fc : bv 32)
           (t0 t1 t2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6 : word) c,
    pem_com en Σ m off crem lrem (mbio_ent K max ++ rest) -> mbio_repx (rt_live RT Σ) m K BIv BM blw meth len max offK -> 1 <= n <= len - offK ->
    In (OUT, no) rest -> n <= no -> length ojunk = Z.to_nat no -> rw_cells asegs m OUT [CB (Z.to_nat no) ojunk] -> 1 <= crem -> 0 <= site < 2 ^ 64 -> site mod 2 = 0 ->
    ASTA RT Σ (e_PMc RT en) (eq (pem_ms en FZ_BIO_READ m F fc (wz site) t0 t1 t2 (wz BIv) (wz OUT) (wz n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6)) c ->
    (forall Σ' (m' : mem) (F' : bvmap 5 word) (fc' : bv 32) (y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 : word) c' (ojunk' : list byte),
       pem_com en Σ' m' off (crem - 1) lrem (mbio_ent K max ++ rest) ->
       rt_live RT Σ' = rt_live RT Σ -> rt_frames RT Σ' = rt_frames RT Σ ->
       rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (e_sp1 RT en) (map rng ((OUT, no) :: mbio_ent K max)) m m' ->
       w_ok RT en Σ ((OUT, no) :: mbio_ent K max) (map rng ((OUT, no) :: mbio_ent K max)) ->
       mbio_repx (rt_live RT Σ) m' K BIv BM blw meth len max (offK + n) -> length ojunk' = Z.to_nat no -> rw_cells asegs m' OUT [CB (Z.to_nat no) ojunk'] ->
       ASTA RT Σ' (e_PMc RT en) (eq (pem_ms en site m' F' fc' (wz site) y0 y1 y2 (wz n) b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s10 s11 y3 y4 y5 y6)) c' ->
       realizes asegs c' T) ->
    realizes asegs c T.
  Proof using AF AFP libenv_agree libenv_fp_where.
    intros C_BR T en Σ m off crem lrem rest K BIv BM blw meth len max offK OUT no n ojunk site F fc t0 t1 t2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6 c
           COM MBX HN HOUT NNO LOJ OJC CRM SR SE HA Hk.
    pose proof COM as (ART0 & MI & ST & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & NTL & MB & OFF & BLT & KLV & PERM & CFR & ND & LPOS
       & FRS & FRN & SP0 & CG & LIV & LR0 & CR & CR0 & CRE & CGH & CGS & CTX & UWC & F0 & F64 & FTOP & FSEG & FSH & FFS & SAVED & PRES & FLR & NDO & OUTS & FDO & MST).
    destruct (com_lists RT libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ COM) as [ELV CLV].
    assert (XLC : forall e, In e ((OUT, no) :: mbio_ent K max) -> In e (mbio_ent K max ++ rest) /\ 0 < snd e).
    { intros e [<-|He]; [split; [apply in_or_app; right; exact HOUT| cbn; clear - HN NNO; lia]| split; [apply in_or_app; left; exact He| exact (mbio_ent_pos _ _ _ _ _ _ _ _ _ _ MBX e He)]]. }
    pose proof (com_WB_ok RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ ((OUT, no) :: mbio_ent K max) COM ltac:(intros e He; left; exact (XLC e He))) as WOK.
    pose proof WOK as (HWS & HWFR & HWFF & HWF & HWL & HWP).
    destruct (com_call_pre0 RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ COM) as (EU & COK & INCL1 & FRMAX & CRED & HLO & H352).
    assert (NT : ~ mbio_T K OUT).
    { unfold mbio_T. intros X. rewrite map_app, mbio_ent_fst, <- app_assoc in ND. pose proof (nd_split _ _ ND) as (_ & _ & DJ). exact (DJ OUT X ltac:(apply in_or_app; left; exact (in_map fst _ _ HOUT))). }
    apply (C_BR Σ (e_PMc RT en) (wz site) (wz (e_sp1 RT en)) (e_gp RT en) (wz TP_A) t0 t1 t2 (e_sp RT en) (wz (e_sp1 RT en)) (wz BIv) (wz OUT) (wz n) a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 (wz (shad (e_f RT en))) (wz SHB) s10 s11 t3 t4 t5 t6 F fc m (e_lo RT en) (e_canary RT en) K BIv BM meth len max offK OUT no n blw ojunk
             FDO MST eq_refl eq_refl eq_refl eq_refl MBX HN (CLV _ ltac:(apply in_or_app; right; exact HOUT)) NT NNO LOJ OJC
             ART0 MI COK ltac:(rewrite EU; clear - LOR; unfold PEM_CALLEE_STACK, BREAD_STACK in *; lia) CLE FRMAX ltac:(clear - CRED CRM; lia) T c HA).
    intros c' (Σ' & AP & (LV' & FRS' & SP' & CR' & CG')). unfold apost in AP.
    destruct (ASTA_unpack RT Σ' _ _ c' AP) as (ms' & (v & m' & RS & (ART1 & MI1 & ST1) & PR0 & CLE1 & (ojunk' & -> & WM1 & MBX1 & LOJ' & OJC')) & Hc'). clear AP.
    destruct RS as (y0 & y1 & y2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & y3 & y4 & y5 & y6 & F' & fc' & ->).
    rewrite EU in ST1, PR0. rewrite (ret_pc_even site SR SE) in Hc'.
    assert (PR : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (e_sp1 RT en) (map rng ((OUT, no) :: mbio_ent K max)) m m').
    { intros a Ha Ho. apply PR0; [exact Ha|]. change (outside ((OUT, OUT + no) :: map rng (mbio_ent K max)) (bv_unsigned a)) in Ho. destruct Ho as [Ho1 Ho2].
      cbn [outside]. split; [clear - Ho1 NNO; lia| exact Ho2]. }
    assert (XLV : forall e, In e ((OUT, no) :: mbio_ent K max) -> In e (rt_live RT Σ)) by (intros e He; exact (CLV _ (proj1 (XLC e He)))).
    assert (LE1 : libenv m' (e_LBL RT en) (e_E RT en)).
    { eapply (libenv_keep libenv libenv_fp libenv_agree libenv_fp_where); [exact LE| exact PR| exact INCL1|].
      intros x Hx. destruct (libenv_fp_where _ _ Hx) as [(_ & CS & _)|(p' & n' & Hin & Hp)].
      - exact (com_WB_static RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ _ COM XLV x CS).
      - apply (HWL p' n' x (INCL1 _ Hin)); [| exact Hp]. intros X. apply (CFR _ (proj1 (XLC _ X))). cbn [fst]. exact (in_map fst _ _ (INCL _ Hin)). }
    assert (SEC1 : sec_off m').
    { eapply sec_off_agree; [exact SEC|]. intros a Ea. rewrite <- (Z_to_bv_bv_unsigned a), Ea.
      apply PR; rewrite (unsigned_lit SEC_INIT) by (unfold SEC_INIT; clear; lia); [apply acl_static; apply client_static_intro; unfold SEC_INIT; clear; lia|].
      exact (com_WB_static RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ _ COM XLV SEC_INIT ltac:(apply client_static_intro; unfold SEC_INIT; clear; lia)). }
    eapply (Hk Σ' m' F' fc' y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 c' ojunk'); [| exact LV'| exact FRS'| exact PR| exact WOK| exact MBX1| exact LOJ'| exact OJC'| exact Hc'].
    eapply (com_call RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ Σ' m m' off off crem (crem - 1) lrem lrem _ _ _ _ 1 COM ART1 MI1 ST1 PR CLE1 SEC1 LE1);
      [| exact OFF| exact FRS'| exact SP'| exact CG'| exact CR'| clear - CRM; lia| clear; lia| exact LR0| rewrite LV'; clear; lia
       | exact ELV| exact HWP| exact HWS| exact HWF| rewrite LV'; exact PERM| exact CFR| exact ND| rewrite LV'; exact LPOS| exact NTL].
    eapply (mbio_rep_keep (rt_live RT Σ)); [exact MB| exact PR| intros e He; rewrite LV'; split; exact (ELV _ (KLV _ He))|].
    intros e x He Hx. exact (com_klv_outX RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ _ _ COM HWL ltac:(intros e' He'; right; exact (proj1 (XLC e' He'))) e x He Hx).
  Qed.

  (* [comment removed for export] *)
  Lemma pem_call_bnew : bio_new_mem_stmt RT libenv FZ_SITES FZ_CALLS ->
    forall T (en : pem_entry) Σ (m : mem) off crem lrem cur meth site (F : bvmap 5 word) (fc : bv 32)
           (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6 : word) c,
    pem_com en Σ m off crem lrem cur -> (meth = M_MEM \/ meth = M_SECMEM) -> 1 <= crem -> 4 <= lrem -> In site PEM_RAS_new ->
    ASTA RT Σ (e_PMc RT en) (eq (pem_ms en FZ_BIO_NEW m F fc (wz site) t0 t1 t2 (wz meth) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6)) c ->
    (forall Σ' (m' : mem) (F' : bvmap 5 word) (fc' : bv 32) (y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 : word) c' (K : mbk) (BI BB BM RP : Z),
       pem_com en Σ' m' off (crem - 1) (lrem - 4) (mbio_ent K 0 ++ cur) -> K = MBK BI BB BM RP None ->
       rt_live RT Σ' = (RP, 32) :: (BM, 32) :: (BB, 16) :: (BI, 128) :: rt_live RT Σ -> rt_frames RT Σ' = rt_frames RT Σ ->
       rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (e_sp1 RT en) (lib_W (e_LBL RT en)) m m' ->
       mbio_rep (rt_live RT Σ') m' K BI meth 0 0 0 ->
       ASTA RT Σ' (e_PMc RT en) (eq (pem_ms en site m' F' fc' (wz site) y0 y1 y2 (wz BI) b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s10 s11 y3 y4 y5 y6)) c' ->
       realizes asegs c' T) ->
    realizes asegs c T.
  Proof using AF AFP libenv_agree libenv_fp_where.
    intros C_BN T en Σ m off crem lrem cur meth site F fc t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6 c COM HM CRM LRM HSI HA Hk.
    pose proof COM as (ART0 & MI & ST & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & NTL & MB & OFF & BLT & KLV & PERM & CFR & ND & LPOS
       & FRS & FRN & SP0 & CG & LIV & LR0 & CR & CR0 & CRE & CGH & CGS & CTX & UWC & F0 & F64 & FTOP & FSEG & FSH & FFS & SAVED & PRES & FLR & NDO & OUTS & FDO & MST).
    destruct (com_lists RT libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ COM) as [ELV CLV].
    pose proof (com_W_ok RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ COM) as WOK. pose proof WOK as (HWS & HWFR & HWFF & HWF & HWL & HWP).
    assert (HSR : In site PEM_RAS) by (unfold PEM_RAS; rewrite !in_app_iff; tauto).
    assert (SR : 0 <= site < 2 ^ 64) by (clear - HSI; unfold PEM_RAS_new in HSI; cbn in HSI; lia).
    destruct (com_call_pre RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ site FZ_BIO_NEW COM (pem_site_in _ HSR) (pem_calls_bnew _ HSI) SR)
      as (EU & COK & CTX1 & UWC1 & INCL1 & FRMAX & CRED & HLO & H352).
    apply (C_BN Σ (e_PMc RT en) (wz site) (wz (e_sp1 RT en)) (e_gp RT en) (wz TP_A) t0 t1 t2 (e_sp RT en) (wz (e_sp1 RT en)) (wz meth) a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 (wz (shad (e_f RT en))) (wz SHB) s10 s11 t3 t4 t5 t6 F fc m (e_lo RT en) (bv_unsigned (e_ra RT en) :: e_outer RT en) (e_canary RT en)
             (e_LBL RT en) (e_E RT en) meth FDO MST eq_refl eq_refl HM LE INCL1 ART0 MI COK ltac:(rewrite EU; clear - LOR; unfold PEM_CALLEE_STACK, BNEW_STACK in *; lia) CLE CTX1 UWC1 CGH
             FRMAX ltac:(clear - LIV LRM; lia) ltac:(clear - CRED CRM; lia) T c HA).
    intros c' (Σ' & AP & FRS' & SP' & CR' & CG'). unfold apost in AP.
    destruct (ASTA_unpack RT Σ' _ _ c' AP) as (ms' & (v & m' & RS & (ART1 & MI1 & ST1) & PR & CLE1 & (WM1 & LE1 & (K & BI & BB & BM & RP & -> & HK & LV' & MBN))) & Hc'). clear AP.
    destruct RS as (y0 & y1 & y2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & y3 & y4 & y5 & y6 & F' & fc' & ->).
    rewrite EU in ST1, PR. rewrite (ret_pc_even site SR) in Hc' by (clear - HSI; unfold PEM_RAS_new in HSI; cbn in HSI; lia).
    assert (SEC1 : sec_off m').
    { eapply sec_off_agree; [exact SEC|]. intros a Ea. rewrite <- (Z_to_bv_bv_unsigned a), Ea.
      apply PR; rewrite (unsigned_lit SEC_INIT) by (unfold SEC_INIT; clear; lia); [apply acl_static; apply client_static_intro; unfold SEC_INIT; clear; lia|].
      apply HWP; [apply acl_static; apply client_static_intro; unfold SEC_INIT; clear; lia| exact (com_sec_out RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ COM)]. }
    (* [comment removed for export] *)
    assert (F1 : forall e, In e ([] ++ (BM, 32) :: (BB, 16) :: (BI, 128) :: rt_live RT Σ) -> fst e <> RP).
    { apply (live_fresh RT AF Σ' m' [] RP 32 _ ART1); [rewrite LV'; reflexivity| clear; lia| intros e He; destruct He as [<-|[<-|[<-|He]]]; [cbn; clear; lia| cbn; clear; lia| cbn; clear; lia| exact (LPOS e He)]]. }
    assert (F2 : forall e, In e ([(RP, 32)] ++ (BB, 16) :: (BI, 128) :: rt_live RT Σ) -> fst e <> BM).
    { apply (live_fresh RT AF Σ' m' [(RP, 32)] BM 32 _ ART1); [rewrite LV'; reflexivity| clear; lia| intros e He; apply in_app_iff in He; destruct He as [[<-|[]]|[<-|[<-|He]]]; [cbn; clear; lia| cbn; clear; lia| cbn; clear; lia| exact (LPOS e He)]]. }
    assert (F3 : forall e, In e ([(RP, 32); (BM, 32)] ++ (BI, 128) :: rt_live RT Σ) -> fst e <> BB).
    { apply (live_fresh RT AF Σ' m' [(RP, 32); (BM, 32)] BB 16 _ ART1); [rewrite LV'; reflexivity| clear; lia| intros e He; apply in_app_iff in He; destruct He as [[<-|[<-|[]]]|[<-|He]]; [cbn; clear; lia| cbn; clear; lia| cbn; clear; lia| exact (LPOS e He)]]. }
    assert (F4 : forall e, In e ([(RP, 32); (BM, 32); (BB, 16)] ++ rt_live RT Σ) -> fst e <> BI).
    { apply (live_fresh RT AF Σ' m' [(RP, 32); (BM, 32); (BB, 16)] BI 128 _ ART1); [rewrite LV'; reflexivity| clear; lia| intros e He; apply in_app_iff in He; destruct He as [[<-|[<-|[<-|[]]]]|He]; [cbn; clear; lia| cbn; clear; lia| cbn; clear; lia| exact (LPOS e He)]]. }
    cbn [app] in F1, F2, F3, F4.
    assert (FL : forall q e, In q [BI; BB; BM; RP] -> In e (rt_live RT Σ) -> fst e <> q).
    { intros q e Hq He. destruct Hq as [<-|[<-|[<-|[<-|[]]]]]; [apply F4| apply F3| apply F2| apply F1]; do 3 right; exact He. }
    assert (ND4 : List.NoDup [BI; BB; BM; RP]).
    { apply (nd_insert1 []); [apply (nd_insert1 []); [apply (nd_insert1 []); [apply (nd_insert1 []); [constructor| intros []]|]|]|]; cbn; intros X.
      - destruct X as [X|[]]. exact (F1 (BM, 32) ltac:(left; reflexivity) (eq_sym X)).
      - destruct X as [X|[X|[]]]; [exact (F2 (BB, 16) ltac:(right; left; reflexivity) (eq_sym X))| exact (F1 (BB, 16) ltac:(right; left; reflexivity) (eq_sym X))].
      - destruct X as [X|[X|[X|[]]]]; [exact (F3 (BI, 128) ltac:(right; right; left; reflexivity) (eq_sym X))| exact (F2 (BI, 128) ltac:(right; right; left; reflexivity) (eq_sym X))| exact (F1 (BI, 128) ltac:(right; right; left; reflexivity) (eq_sym X))]. }
    subst K.
    eapply (Hk Σ' m' F' fc' y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 c' (MBK BI BB BM RP None) BI BB BM RP); [| reflexivity| exact LV'| exact FRS'| exact PR| exact MBN| exact Hc'].
    eapply (com_call RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ Σ' m m' off off crem (crem - 1) lrem (lrem - 4) _ _ _ _ 1 COM ART1 MI1 ST1 PR CLE1 SEC1 LE1);
      [| exact OFF| exact FRS'| exact SP'| exact CG'| exact CR'| clear - CRM; lia| clear; lia| clear - LRM; lia| rewrite LV'; cbn [length]; clear; lia
       | exact ELV| exact HWP| exact HWS| exact HWF| | | | | ].
    - eapply (mbio_rep_keep (rt_live RT Σ)); [exact MB| exact PR| intros e He; rewrite LV'; split; [| do 4 right]; exact (ELV _ (KLV _ He))|].
      intros e x He Hx. exact (com_klv_out RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ _ _ COM HWL (fun e H => or_intror H) e x He Hx).
    - rewrite LV'. cbn [mbio_ent k_bi k_bb k_bm k_rp k_d app].
      apply (Permutation_trans (l' := [(RP, 32); (BM, 32); (BB, 16); (BI, 128)] ++ (cur ++ e_live RT en))); [exact (Permutation_app_head [(RP, 32); (BM, 32); (BB, 16); (BI, 128)] PERM)|].
      change ((BI, 128) :: (BB, 16) :: (BM, 32) :: (RP, 32) :: cur ++ e_live RT en) with ([(BI, 128); (BB, 16); (BM, 32); (RP, 32)] ++ (cur ++ e_live RT en)).
      apply Permutation_app_tail. apply (Permutation_rev [(RP, 32); (BM, 32); (BB, 16); (BI, 128)]).
    - intros e He. cbn [mbio_ent k_bi k_bb k_bm k_rp k_d app] in He. destruct He as [<-|[<-|[<-|[<-|He]]]]; [| | | | exact (CFR e He)]; cbn [fst]; intros X; apply in_map_iff in X; destruct X as (e' & E' & He');
        first [exact (FL BI e' ltac:(left; reflexivity) (ELV _ He') E')| exact (FL BB e' ltac:(right; left; reflexivity) (ELV _ He') E')
              | exact (FL BM e' ltac:(right; right; left; reflexivity) (ELV _ He') E')| exact (FL RP e' ltac:(right; right; right; left; reflexivity) (ELV _ He') E')].
    - cbn [mbio_ent k_bi k_bb k_bm k_rp k_d app map fst]. 
      assert (GEN : forall pre, List.NoDup pre -> (forall q, In q pre -> In q [BI; BB; BM; RP]) -> List.NoDup (pre ++ map fst cur ++ e_E RT en :: mbio_blocks (e_K RT en))).
      { intros pre NDP SUB. induction pre as [|q pre IH]; [exact ND|]. cbn [app]. apply (nd_insert1 []). 
        - apply IH; [inversion NDP; assumption| intros q' Hq'; apply SUB; right; exact Hq'].
        - cbn [app]. intros X. apply in_app_iff in X. destruct X as [X|X].
          + inversion NDP; subst. exact (H1 X).
          + destruct (ids_live en Σ m off crem lrem cur COM q X) as (e' & He' & E'). exact (FL q e' (SUB q (or_introl eq_refl)) He' E'). }
      exact (GEN [BI; BB; BM; RP] ND4 (fun q H => H)).
    - intros e He. rewrite LV' in He. destruct He as [<-|[<-|[<-|[<-|He]]]]; [cbn; clear; lia| cbn; clear; lia| cbn; clear; lia| cbn; clear; lia| exact (LPOS e He)].
    - intros e He X. apply in_app_iff in X. destruct X as [X|X]; [exact (NTL e He ltac:(apply in_or_app; left; exact X))|].
      cbn [mbio_ent k_bi k_bb k_bm k_rp k_d app map fst] in X.
      assert (HeL : In e (rt_live RT Σ)) by (destruct He as [<-|He]; [exact (ELV _ INE)| exact (ELV _ (INCL _ He))]).
      destruct X as [X|[X|[X|[X|X]]]]; [exact (FL BI e ltac:(left; reflexivity) HeL (eq_sym X))| exact (FL BB e ltac:(right; left; reflexivity) HeL (eq_sym X))
        | exact (FL BM e ltac:(right; right; left; reflexivity) HeL (eq_sym X))| exact (FL RP e ltac:(right; right; right; left; reflexivity) HeL (eq_sym X))|].
      exact (NTL e He ltac:(apply in_or_app; right; exact X)).
  Qed.
End W3X3.
