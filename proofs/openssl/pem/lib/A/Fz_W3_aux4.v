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
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs PLayout I_lkit I_ut RT_iface_pem D_libiface_pem Fz_kit Fz_ckit Fz_chk Fz_fkit Fz_mkit Fz_env Fz_M_malloc Fz_M_zalloc Fz_M_free Fz_M_secure Fz_W1_defs Fz_W1_grow Fz_W1_pploc Fz_W3_iface Fz_W3_defs Fz_W3_lems Fz_W3_aux Fz_W3_aux2 Fz_W3_aux3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.

Section W3X4.
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

  Lemma pem_calls_puts : forall r, In r PEM_RAS_puts -> In (r, FZ_BIO_PUTS) PEM_CALLS.
  Proof. intros r Hr. unfold PEM_CALLS. rewrite !in_app_iff. do 4 right. left. apply in_map_iff. exists r. split; [reflexivity| exact Hr]. Qed.

  (* [comment removed for export] *)
  Lemma com_Wstat_ok : forall (en : pem_entry) Σ (m : mem) off crem lrem cur W,
    pem_com en Σ m off crem lrem cur -> (forall x, outside LIB_W x -> outside W x) -> w_ok RT en Σ [] W.
  Proof using AF AFP.
    intros en Σ m off crem lrem cur W COM SUB.
    pose proof COM as (ART0 & MI & ST & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & NTL & MB & OFF & BLT & KLV & PERM & CFR & ND & LPOS
       & FRS & FRN & SP0 & CG & LIV & LR0 & CR & CR0 & CRE & CGH & CGS & CTX & UWC & F0 & F64 & FTOP & FSEG & FSH & FFS & SAVED & PRES & FLR & NDO & OUTS & FDO & MST).
    assert (HLO : e_lo RT en <= e_sp1 RT en) by (clear - LOR; unfold RT_STACK, PEM_CALLEE_STACK in *; lia).
    assert (G : forall x, (x < 0x5a9f20 \/ 0xbc5698 <= x) -> outside W x) by (intros x Hx; exact (SUB x (outside_LIB_W x Hx))).
    split; [intros x Hx; apply G; clear - Hx HLO HLOS; lia|].
    assert (FRG : forall f k x, In (f, k) (rt_frames RT Σ) -> f <= x < f + fs_size k - 8 -> outside W x).
    { intros f k x Hin Hx. pose proof (af_frames_range RT AF Σ m f k ART0 Hin) as (_ & _ & FS & _). pose proof (Z.shiftl_nonneg 64 (Z.of_nat k)). apply G. clear - Hx FS H. unfold fs_size, SEGTOP_A in *. lia. }
    split; [intros f k x Hin Hx; exact (FRG f k x ltac:(rewrite FRS; right; exact Hin) Hx)|].
    split; [intros x Hx; exact (FRG (e_f RT en) 1%nat x ltac:(rewrite FRS; left; reflexivity) ltac:(change (fs_size 1) with 128; clear - Hx; lia))|].
    split; [intros x Hx; apply G; clear - Hx F0; unfold shad, SHB in *; Z.div_mod_to_equations; lia|].
    split; [intros p n x Hin _ Hx; pose proof (af_live_range RT AF Σ m p n ART0 Hin) as (_ & _ & Y); apply G; clear - Y Hx; unfold SEGTOP_A in *; lia|].
    intros a _ Ho. apply SUB. unfold pem_W, lib_W in Ho. exact (outside_app_l _ _ _ (outside_app_r _ _ _ (outside_app_r _ _ _ Ho))).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma mbio_rep_dpos : forall live (m : mem) K BI meth len max off d, mbio_rep live m K BI meth len max off -> k_d K = Some d -> 0 < max.
  Proof.
    intros live m K BI meth len max off d (BM & fl & rrw & numw & padw & nr & nw & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (rmx & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MT)) EK.
    rewrite EK in MT. destruct MT as (junk & _ & POS & _). exact POS.
  Qed.
  Lemma pem_call_bputs : bio_puts_stmt RT FZ_SITES FZ_CALLS ->
    forall T (en : pem_entry) Σ (m : mem) off crem lrem rest K BIv meth len max LB n (bs : list byte) site (F : bvmap 5 word) (fc : bv 32)
           (t0 t1 t2 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6 : word) c,
    pem_com en Σ m off crem lrem (mbio_ent K max ++ rest) -> mbio_rep (rt_live RT Σ) m K BIv meth len max 0 -> gr_n (len + n) <= 2 ^ 27 ->
    In (LB, 256) rest -> LB mod 16 = 0 -> length bs = 256%nat -> rw_cells asegs m LB [CB 256 bs] ->
    0 <= n <= 255 -> nth_error bs (Z.to_nat n) = Some (Z_to_bv 8 0) -> (forall i, (i < Z.to_nat n)%nat -> nth_error bs i <> Some (Z_to_bv 8 0)) ->
    puts_cost len n max <= crem -> 1 <= lrem -> In site PEM_RAS_puts ->
    ASTA RT Σ (e_PMc RT en) (eq (pem_ms en FZ_BIO_PUTS m F fc (wz site) t0 t1 t2 (wz BIv) (wz LB) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6)) c ->
    (forall Σ' (m' : mem) (F' : bvmap 5 word) (fc' : bv 32) (y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 : word) c' (pd' : option Z) (max' : Z),
       pem_com en Σ' m' off (crem - puts_cost len n max) (lrem + Z.of_nat (length (mbio_ent K max)) - Z.of_nat (length (mbio_ent (mbk_data K pd') max'))) (mbio_ent (mbk_data K pd') max' ++ rest) ->
       rt_frames RT Σ' = rt_frames RT Σ ->
       rt_pres_fp (match k_d K with Some d => live_remove d (rt_live RT Σ) | None => rt_live RT Σ end) (rt_frames RT Σ) (e_sp1 RT en)
                  ((G_ALLOW_CUST, G_ALLOW_CUST + 1) :: mbio_W K max) m m' ->
       w_ok RT en Σ (mbio_ent K max) ((G_ALLOW_CUST, G_ALLOW_CUST + 1) :: mbio_W K max) ->
       (forall e, In e (rest ++ e_live RT en) -> In e (match k_d K with Some d => live_remove d (rt_live RT Σ) | None => rt_live RT Σ end) /\ In e (rt_live RT Σ')) ->
       mbio_rep (rt_live RT Σ') m' (mbk_data K pd') BIv meth (len + n) max' 0 -> (max' = max \/ (max < len + n /\ max' = gr_n (len + n))) -> len + n <= max' ->
       ASTA RT Σ' (e_PMc RT en) (eq (pem_ms en site m' F' fc' (wz site) y0 y1 y2 (wz n) b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s10 s11 y3 y4 y5 y6)) c' ->
       realizes asegs c' T) ->
    realizes asegs c T.
  Proof using AF AFP libenv_agree libenv_fp_where.
    intros C_BP T en Σ m off crem lrem rest K BIv meth len max LB n bs site F fc t0 t1 t2 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6 c
           COM MBK GRN HLB AL16 LBS LBC HN NUL NNUL CRM LRM HSI HA Hk.
    pose proof COM as (ART0 & MI & ST & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & NTL & MB & OFF & BLT & KLV & PERM & CFR & ND & LPOS
       & FRS & FRN & SP0 & CG & LIV & LR0 & CR & CR0 & CRE & CGH & CGS & CTX & UWC & F0 & F64 & FTOP & FSEG & FSH & FFS & SAVED & PRES & FLR & NDO & OUTS & FDO & MST).
    destruct (com_lists RT libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ COM) as [ELV CLV].
    destruct MBK as [BM0 MBX].
    assert (XLC : forall e, In e (mbio_ent K max) -> In e (mbio_ent K max ++ rest) /\ 0 < snd e).
    { intros e He. split; [apply in_or_app; left; exact He| exact (mbio_ent_pos _ _ _ _ _ _ _ _ _ _ MBX e He)]. }
    pose proof (w_ok_app RT en Σ [] (mbio_ent K max) [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] (mbio_W K max)
                 (com_Wstat_ok en Σ m off crem lrem _ [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] COM ltac:(intros x Hx; cbn; split; [| exact I]; unfold LIB_W in Hx; cbn in Hx; unfold G_ALLOW_CUST; clear - Hx; lia))
                 (com_WB_ok RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ (mbio_ent K max) COM ltac:(intros e He; left; exact (XLC e He)))) as WOK.
    cbn [app] in WOK. pose proof WOK as (HWS & HWFR & HWFF & HWF & HWL & HWP).
    assert (HSR : In site PEM_RAS) by (unfold PEM_RAS; rewrite !in_app_iff; tauto).
    assert (SR : 0 <= site < 2 ^ 64) by (clear - HSI; unfold PEM_RAS_puts in HSI; cbn in HSI; lia).
    destruct (com_call_pre RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ site FZ_BIO_PUTS COM (pem_site_in _ HSR) (pem_calls_puts _ HSI) SR)
      as (EU & COK & CTX1 & UWC1 & INCL1 & FRMAX & CRED & HLO & H352).
    assert (NT : ~ mbio_T K LB).
    { unfold mbio_T. intros X. rewrite map_app, mbio_ent_fst, <- app_assoc in ND. pose proof (nd_split _ _ ND) as (_ & _ & DJ). exact (DJ LB X ltac:(apply in_or_app; left; exact (in_map fst _ _ HLB))). }
    assert (PC1 : 1 <= puts_cost len n max).
    { unfold puts_cost, mcost. destruct (max <? len + n); [| clear; lia]. destruct (gr_n (len + n) <=? 64512) eqn:E; [clear; lia| apply Z.leb_gt in E; clear - E; lia]. }
    apply (C_BP Σ (e_PMc RT en) (wz site) (wz (e_sp1 RT en)) (e_gp RT en) (wz TP_A) t0 t1 t2 (e_sp RT en) (wz (e_sp1 RT en)) (wz BIv) (wz LB) a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 (wz (shad (e_f RT en))) (wz SHB) s10 s11 t3 t4 t5 t6 F fc m (e_lo RT en) (bv_unsigned (e_ra RT en) :: e_outer RT en) (e_canary RT en)
             K BIv meth len max LB n bs FDO MST eq_refl eq_refl eq_refl (ex_intro _ BM0 MBX) GRN (CLV _ ltac:(apply in_or_app; right; exact HLB)) AL16 NT LBS LBC HN NUL NNUL
             ART0 MI COK ltac:(rewrite EU; clear - LOR; unfold PEM_CALLEE_STACK, BPUTS_STACK in *; lia) CLE SEC CTX1 UWC1 CGH FRMAX ltac:(clear - LIV LRM; lia) ltac:(clear - CRED CRM; lia) T c HA).
    intros c' (Σ' & AP & FRS' & SP' & CR' & CG'). unfold apost in AP.
    destruct (ASTA_unpack RT Σ' _ _ c' AP) as (ms' & (v & m' & RS & (ART1 & MI1 & ST1) & PR & CLE1 & (SEC1 & (pd' & max' & -> & HMAX & HLEN & MB1 & PL))) & Hc'). clear AP.
    destruct RS as (y0 & y1 & y2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & y3 & y4 & y5 & y6 & F' & fc' & ->).
    rewrite EU in ST1, PR. rewrite (ret_pc_even site SR) in Hc' by (clear - HSI; unfold PEM_RAS_puts in HSI; cbn in HSI; lia).
    set (KEEP := match k_d K with Some d => live_remove d (rt_live RT Σ) | None => rt_live RT Σ end) in *.
    assert (DJK : forall q, In q (mbio_blocks K) -> ~ In q (map fst rest) /\ ~ In q (map fst (e_live RT en)) /\ ~ In q (e_E RT en :: mbio_blocks (e_K RT en))).
    { intros q Hq. rewrite map_app, mbio_ent_fst, <- app_assoc in ND. pose proof (nd_split _ _ ND) as (_ & _ & DJ).
      split; [intros X; exact (DJ q Hq ltac:(apply in_or_app; left; exact X))|].
      split; [| intros X; exact (DJ q Hq ltac:(apply in_or_app; right; exact X))].
      rewrite <- (mbio_ent_fst K max) in Hq. apply in_map_iff in Hq. destruct Hq as (e & <- & He). exact (CFR e ltac:(apply in_or_app; left; exact He)). }
    assert (KSUB : forall e, In e KEEP -> In e (rt_live RT Σ)) by (intros e He; subst KEEP; destruct (k_d K); [exact (live_remove_sub _ _ _ He)| exact He]).
    assert (KIN : forall e, In e (rt_live RT Σ) -> (forall d, k_d K = Some d -> fst e <> d) -> In e KEEP).
    { intros e He Hd. subst KEEP. destruct (k_d K) as [d|]; [| exact He]. apply live_remove_keep; [exact He| exact (Hd d eq_refl)]. }
    assert (KPR : forall e, In e (rest ++ e_live RT en) -> In e KEEP).
    { intros e He. apply KIN.
      - apply (Permutation_in _ (Permutation_sym PERM)). apply in_or_app. apply in_app_iff in He. destruct He as [He|He]; [left; apply in_or_app; right; exact He| right; exact He].
      - intros d EKD X. assert (HD : In d (mbio_blocks K)) by (unfold mbio_blocks; rewrite EKD; apply in_or_app; right; left; reflexivity).
        apply in_app_iff in He. destruct He as [He|He]; [exact (proj1 (DJK _ HD) ltac:(rewrite <- X; exact (in_map fst _ _ He)))| exact (proj1 (proj2 (DJK _ HD)) ltac:(rewrite <- X; exact (in_map fst _ _ He)))]. }
    assert (LE1 : libenv m' (e_LBL RT en) (e_E RT en)).
    { eapply (libenv_keep libenv libenv_fp libenv_agree libenv_fp_where); [exact LE| exact PR| intros e He; apply KPR; apply in_or_app; right; exact (INCL _ He)|].
      intros x Hx. destruct (libenv_fp_where _ _ Hx) as [(_ & CS & NC)|(p' & n' & Hin & Hp)].
      - cbn. split; [intros R; apply NC; exists G_ALLOW_CUST, (G_ALLOW_CUST + 1); split; [unfold CL_CELLS; cbn; tauto| exact R]|].
        exact (com_WB_static RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ _ COM (fun e He => CLV _ (proj1 (XLC e He))) x CS).
      - apply (HWL p' n' x (ELV _ (INCL _ Hin))); [| exact Hp]. intros X. apply (CFR _ (proj1 (XLC _ X))). cbn [fst]. exact (in_map fst _ _ (INCL _ Hin)). }
    (* [comment removed for export] *)
    assert (FIN : forall cur', cur' = mbio_ent (mbk_data K pd') max' ++ rest ->
      Permutation (rt_live RT Σ') (cur' ++ e_live RT en) -> (forall e, In e cur' -> ~ In (fst e) (map fst (e_live RT en))) ->
      List.NoDup (map fst cur' ++ e_E RT en :: mbio_blocks (e_K RT en)) -> (forall e, In e (rt_live RT Σ') -> 0 < snd e) ->
      (forall e, In e ((e_E RT en, 904) :: e_LBL RT en) -> ~ In (fst e) (mbio_blocks (e_K RT en) ++ map fst cur')) ->
      (forall e, In e KEEP -> In e (rt_live RT Σ')) -> realizes asegs c' T).
    { intros cur' -> PERM1 CFR1 ND1 LPOS1 NTL1 KL.
      eapply (Hk Σ' m' F' fc' y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 c' pd' max'); [| exact FRS'| exact PR| exact WOK| intros e He; split; [exact (KPR e He)| exact (KL _ (KPR e He))]| exact MB1| exact HMAX| exact HLEN| exact Hc'].
      eapply (com_call RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ Σ' m m' off off crem (crem - puts_cost len n max) lrem (lrem + Z.of_nat (length (mbio_ent K max)) - Z.of_nat (length (mbio_ent (mbk_data K pd') max'))) _ _ KEEP _ (puts_cost len n max) COM ART1 MI1 ST1 PR CLE1 SEC1 LE1);
        [| exact OFF| exact FRS'| exact SP'| exact CG'| exact CR'| clear - CRM; lia| clear; lia| unfold mbio_ent; rewrite !length_app; cbn [mbk_data k_bi k_bb k_bm k_rp k_d]; destruct pd'; destruct (k_d K); cbn [length Nat.add]; clear - LRM; lia| | intros e He; apply KPR; apply in_or_app; right; exact He| exact HWP| exact HWS| exact HWF| exact PERM1| exact CFR1| exact ND1| exact LPOS1| exact NTL1].
      - eapply (mbio_rep_keep (rt_live RT Σ)); [exact MB| exact PR| intros e He; split; [| apply KL]; apply KPR; apply in_or_app; right; exact (KLV _ He)|].
        intros e x He Hx. exact (com_klv_outX RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ _ _ COM HWL ltac:(intros e' He'; right; exact (proj1 (XLC e' He'))) e x He Hx).
      - pose proof (Permutation_length PERM1) as L1. pose proof (Permutation_length PERM) as L0. unfold mbio_ent in L1, L0. cbn [mbk_data k_bi k_bb k_bm k_rp k_d] in L1.
        rewrite !length_app in L1, L0. rewrite ?length_app in L1, L0. cbn [length] in L1, L0. unfold mbio_ent. rewrite !length_app. cbn [mbk_data k_bi k_bb k_bm k_rp k_d].
        destruct pd'; destruct (k_d K); cbn [length Nat.add] in L1, L0 |- *; clear - L1 L0; lia. }
    assert (LEN0 : 0 <= len) by (destruct MBX as (fl & rrw & numw & padw & nr & nw & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (rmaxw & _ & _ & _ & _ & _ & _ & _ & OL & _)); clear - OL; lia).
    pose proof MBX as (fl0 & rrw0 & numw0 & padw0 & nr0 & nw0 & _ & _ & _ & _ & NDK & _).
    assert (B4 : forall e, In e [(k_bi K, 128); (k_bb K, 16); (k_bm K, 32); (k_rp K, 32)] -> In e (mbio_ent K max)) by (intros e He; unfold mbio_ent; apply in_or_app; left; exact He).
    assert (NTL4 : forall e, In e ((e_E RT en, 904) :: e_LBL RT en) -> forall x, In x [k_bi K; k_bb K; k_bm K; k_rp K] -> x <> fst e).
    { intros e He x Hx E. apply (NTL e He). apply in_or_app; right. rewrite map_app, mbio_ent_fst. apply in_or_app; left. unfold mbio_blocks. apply in_or_app; left. rewrite <- E. exact Hx. }
    assert (NTLR : forall e, In e ((e_E RT en, 904) :: e_LBL RT en) -> ~ In (fst e) (map fst rest)).
    { intros e He X. apply (NTL e He). apply in_or_app; right. rewrite map_app. apply in_or_app; right. exact X. }
    destruct PL as [(EPD & EMAX & LV')|[(q & EPD & EKD & LV')|(q & d & EPD & EKD & LV')]].
    - (* [comment removed for export] *)
      subst pd' max'. apply (FIN (mbio_ent K max ++ rest)); [destruct K; reflexivity| rewrite LV'; exact PERM| exact CFR| exact ND| rewrite LV'; exact LPOS| exact NTL| intros e He; rewrite LV'; exact (KSUB e He)].
    - (* [comment removed for export] *)
      subst pd'. unfold KEEP in *. rewrite EKD in *. clear KEEP.
      pose proof (mbio_rep_dpos _ _ _ _ _ _ _ _ q MB1 ltac:(destruct K; reflexivity)) as MQ.
      assert (FQ : forall e, In e ([] ++ rt_live RT Σ) -> fst e <> q).
      { apply (live_fresh RT AF Σ' m' [] q max' (rt_live RT Σ) ART1); [rewrite LV'; reflexivity| clear - MQ; lia| intros e He; exact (LPOS e He)]. }
      cbn [app] in FQ.
      assert (PERM0 : Permutation (rt_live RT Σ) ([(k_bi K, 128); (k_bb K, 16); (k_bm K, 32); (k_rp K, 32)] ++ (rest ++ e_live RT en))).
      { unfold mbio_ent in PERM. rewrite EKD, app_nil_r, <- app_assoc in PERM. exact PERM. }
      apply (FIN (([(k_bi K, 128); (k_bb K, 16); (k_bm K, 32); (k_rp K, 32)] ++ [(q, max')]) ++ rest)); [cbn [mbio_ent mbk_data k_bi k_bb k_bm k_rp k_d]; reflexivity| | | | | |].
      + rewrite LV', <- !app_assoc. cbn [app]. 
        change (Permutation ((q, max') :: rt_live RT Σ) ([(k_bi K, 128); (k_bb K, 16); (k_bm K, 32); (k_rp K, 32)] ++ (q, max') :: (rest ++ e_live RT en))).
        apply Permutation_cons_app. exact PERM0.
      + intros e He. rewrite <- app_assoc in He. apply in_app_iff in He. destruct He as [He|He]; [exact (CFR e ltac:(apply in_or_app; left; exact (B4 e He)))|].
        destruct He as [<-|He]; [| exact (CFR e ltac:(apply in_or_app; right; exact He))].
        cbn [fst]. intros X. apply in_map_iff in X. destruct X as (e' & E' & He'). exact (FQ e' (ELV _ He') E').
      + rewrite !map_app, <- !app_assoc. cbn [map fst app]. apply (nd_insert1 [k_bi K; k_bb K; k_bm K; k_rp K]).
        * unfold mbio_ent in ND. rewrite EKD, app_nil_r, map_app, <- app_assoc in ND. exact ND.
        * intros X. assert (X' : In q (map fst (mbio_ent K max ++ rest) ++ e_E RT en :: mbio_blocks (e_K RT en))).
          { unfold mbio_ent. rewrite EKD, app_nil_r, map_app, <- app_assoc. exact X. }
          destruct (ids_live RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ COM q X') as (e' & He' & E'). exact (FQ e' He' E').
      + intros e He. rewrite LV' in He. destruct He as [<-|He]; [cbn; clear - MQ; lia| exact (LPOS e He)].
      + intros e He X. rewrite !map_app, <- !app_assoc in X. cbn [map fst app] in X.
        assert (HeL : In e (rt_live RT Σ)) by (destruct He as [<-|He]; [exact (ELV _ INE)| exact (ELV _ (INCL _ He))]).
        apply in_app_iff in X. destruct X as [X|X]; [exact (NTL e He ltac:(apply in_or_app; left; exact X))|].
        destruct X as [X|[X|[X|[X|[X|X]]]]]; [exact (NTL4 e He _ ltac:(left; reflexivity) X)| exact (NTL4 e He _ ltac:(right; left; reflexivity) X)
          | exact (NTL4 e He _ ltac:(right; right; left; reflexivity) X)| exact (NTL4 e He _ ltac:(right; right; right; left; reflexivity) X)| exact (FQ e HeL (eq_sym X))| exact (NTLR e He X)].
      + intros e He. rewrite LV'. right. exact He.
    - (* [comment removed for export] *)
      subst pd'. unfold KEEP in *. rewrite EKD in *. clear KEEP.
      pose proof (mbio_rep_dpos _ _ _ _ _ _ _ _ q MB1 ltac:(destruct K; reflexivity)) as MQ.
      assert (FQ : forall e, In e ([] ++ live_remove d (rt_live RT Σ)) -> fst e <> q).
      { apply (live_fresh RT AF Σ' m' [] q max' (live_remove d (rt_live RT Σ)) ART1); [rewrite LV'; reflexivity| clear - MQ; lia| intros e He; exact (LPOS e (live_remove_sub _ _ _ He))]. }
      cbn [app] in FQ.
      assert (HD : In d (mbio_blocks K)) by (unfold mbio_blocks; rewrite EKD; apply in_or_app; right; left; reflexivity).
      assert (ND4 : forall e, In e [(k_bi K, 128); (k_bb K, 16); (k_bm K, 32); (k_rp K, 32)] -> fst e <> d).
      { intros e He E. unfold mbio_blocks in NDK. rewrite EKD in NDK. pose proof (nd_split _ _ NDK) as (_ & _ & DJ). apply (DJ (fst e)); [| left; exact (eq_sym E)].
        destruct He as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst]; [left| right; left| right; right; left| right; right; right; left]; reflexivity. }
      assert (PERM0 : Permutation (live_remove d (rt_live RT Σ)) ([(k_bi K, 128); (k_bb K, 16); (k_bm K, 32); (k_rp K, 32)] ++ (rest ++ e_live RT en))).
      { apply (live_remove_split d max).
        - unfold mbio_ent in PERM. rewrite EKD, <- !app_assoc in PERM. cbn [app] in PERM.
          eapply Permutation_trans; [exact PERM|]. apply Permutation_sym.
          change (Permutation ((d, max) :: [(k_bi K, 128); (k_bb K, 16); (k_bm K, 32); (k_rp K, 32)] ++ (rest ++ e_live RT en)) ([(k_bi K, 128); (k_bb K, 16); (k_bm K, 32); (k_rp K, 32)] ++ (d, max) :: (rest ++ e_live RT en))).
          apply Permutation_middle.
        - intros e He. apply in_app_iff in He. destruct He as [He|He]; [exact (ND4 e He)|]. intros E.
          apply in_app_iff in He. destruct He as [He|He]; [exact (proj1 (DJK _ HD) ltac:(rewrite <- E; exact (in_map fst _ _ He)))| exact (proj1 (proj2 (DJK _ HD)) ltac:(rewrite <- E; exact (in_map fst _ _ He)))]. }
      apply (FIN (([(k_bi K, 128); (k_bb K, 16); (k_bm K, 32); (k_rp K, 32)] ++ [(q, max')]) ++ rest)); [cbn [mbio_ent mbk_data k_bi k_bb k_bm k_rp k_d]; reflexivity| | | | | |].
      + rewrite LV', <- !app_assoc. cbn [app].
        change (Permutation ((q, max') :: live_remove d (rt_live RT Σ)) ([(k_bi K, 128); (k_bb K, 16); (k_bm K, 32); (k_rp K, 32)] ++ (q, max') :: (rest ++ e_live RT en))).
        apply Permutation_cons_app. exact PERM0.
      + intros e He. rewrite <- app_assoc in He. apply in_app_iff in He. destruct He as [He|He]; [exact (CFR e ltac:(apply in_or_app; left; exact (B4 e He)))|].
        destruct He as [<-|He]; [| exact (CFR e ltac:(apply in_or_app; right; exact He))].
        cbn [fst]. intros X. apply in_map_iff in X. destruct X as (e' & E' & He'). exact (FQ e' (KPR e' ltac:(apply in_or_app; right; exact He')) E').
      + rewrite !map_app, <- !app_assoc. cbn [map fst app]. apply (nd_insert1 [k_bi K; k_bb K; k_bm K; k_rp K]).
        * unfold mbio_ent in ND. rewrite EKD, !map_app, <- !app_assoc in ND. cbn [map fst app] in ND. exact (nd_drop [k_bi K; k_bb K; k_bm K; k_rp K] _ d ND).
        * intros X. assert (X' : In q (map fst (mbio_ent K max ++ rest) ++ e_E RT en :: mbio_blocks (e_K RT en)) /\ q <> d).
          { apply in_app_iff in X. split.
            - unfold mbio_ent. rewrite EKD, !map_app, <- !app_assoc. cbn [map fst]. apply in_or_app. destruct X as [X|X]; [left; exact X| right; apply in_or_app; right; exact X].
            - intros ->. unfold mbio_ent in ND. rewrite EKD, !map_app, <- !app_assoc in ND. cbn [map fst] in ND.
              pose proof (nd_split [k_bi K; k_bb K; k_bm K; k_rp K] _ ND) as (_ & NDR & DJ). destruct X as [X|X]; [exact (DJ d X ltac:(apply in_or_app; left; left; reflexivity))|].
              cbn [app] in NDR. inversion NDR; subst. exact (H1 X). }
          destruct X' as [X' NQD]. destruct (ids_live RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ COM q X') as (e' & He' & E'). apply (FQ e'); [| exact E'].
          apply live_remove_keep; [exact He'| rewrite E'; exact NQD].
      + intros e He. rewrite LV' in He. destruct He as [<-|He]; [cbn; clear - MQ; lia| exact (LPOS e (live_remove_sub _ _ _ He))].
      + intros e He X. rewrite !map_app, <- !app_assoc in X. cbn [map fst app] in X.
        assert (HeK : In e (live_remove d (rt_live RT Σ))) by (apply KPR; apply in_or_app; right; destruct He as [<-|He]; [exact INE| exact (INCL _ He)]).
        apply in_app_iff in X. destruct X as [X|X]; [exact (NTL e He ltac:(apply in_or_app; left; exact X))|].
        destruct X as [X|[X|[X|[X|[X|X]]]]]; [exact (NTL4 e He _ ltac:(left; reflexivity) X)| exact (NTL4 e He _ ltac:(right; left; reflexivity) X)
          | exact (NTL4 e He _ ltac:(right; right; left; reflexivity) X)| exact (NTL4 e He _ ltac:(right; right; right; left; reflexivity) X)| exact (FQ e HeK (eq_sym X))| exact (NTLR e He X)].
      + intros e He. rewrite LV'. right. exact He.
  Qed.
  (* [comment removed for export] *)
  Lemma pem_call_bptr : bio_ctrl_ptr_stmt RT ->
    forall T (en : pem_entry) Σ (m : mem) off crem lrem rest K BIv meth len max offK hj lenv j1 tav j2 bmv j3 site (F : bvmap 5 word) (fc : bv 32)
           (t0 t1 t2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6 : word) c,
    pem_com en Σ m off crem lrem (mbio_ent K max ++ rest) -> mbio_rep (rt_live RT Σ) m K BIv meth len max offK ->
    rw_cells asegs m (e_f RT en) (ff_cells hj lenv j1 tav j2 bmv j3) -> 0 <= site < 2 ^ 64 -> site mod 2 = 0 ->
    ASTA RT Σ (e_PMc RT en) (eq (pem_ms en FZ_BIO_CTRL m F fc (wz site) t0 t1 t2 (wz BIv) (wz 115) (wz 0) (wz (e_f RT en + 64)) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6)) c ->
    (forall (m' : mem) (F' : bvmap 5 word) (fc' : bv 32) (y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 : word) c' (BM : Z),
       pem_com en Σ m' off crem lrem (mbio_ent K max ++ rest) ->
       rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (e_sp1 RT en) ((e_f RT en + 64, e_f RT en + 72) :: mbio_W K max) m m' ->
       (forall x, e_sp1 RT en <= x < USTACK_TOP -> outside ((e_f RT en + 64, e_f RT en + 72) :: mbio_W K max) x) ->
       (forall f k x, In (f, k) (e_frames RT en) -> f <= x < f + fs_size k - 8 -> outside ((e_f RT en + 64, e_f RT en + 72) :: mbio_W K max) x) ->
       w_live RT Σ (mbio_ent K max) ((e_f RT en + 64, e_f RT en + 72) :: mbio_W K max) ->
       rw_cells asegs m' (e_f RT en) (ff_cells hj lenv j1 tav j2 (wz BM) j3) ->
       mbio_repx (rt_live RT Σ) m' K BIv BM (wz (len - offK)) meth (len - offK) max 0 -> mem_inv asegs m' ->
       ASTA RT Σ (e_PMc RT en) (eq (pem_ms en site m' F' fc' (wz site) y0 y1 y2 (wz 1) b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s10 s11 y3 y4 y5 y6)) c' ->
       realizes asegs c' T) ->
    realizes asegs c T.
  Proof using AF AFP libenv_agree libenv_fp_where.
    intros C_BT T en Σ m off crem lrem rest K BIv meth len max offK hj lenv j1 tav j2 bmv j3 site F fc t0 t1 t2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6 c
           COM MBK FFC SR SE HA Hk.
    pose proof COM as (ART0 & MI & ST & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & NTL & MB & OFF & BLT & KLV & PERM & CFR & ND & LPOS
       & FRS & FRN & SP0 & CG & LIV & LR0 & CR & CR0 & CRE & CGH & CGS & CTX & UWC & F0 & F64 & FTOP & FSEG & FSH & FFS & SAVED & PRES & FLR & NDO & OUTS & FDO & MST).
    destruct (com_lists RT libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ COM) as [ELV CLV].
    destruct MBK as [BM0 MBX].
    assert (XLC : forall e, In e (mbio_ent K max) -> In e (mbio_ent K max ++ rest) /\ 0 < snd e).
    { intros e He. split; [apply in_or_app; left; exact He| exact (mbio_ent_pos _ _ _ _ _ _ _ _ _ _ MBX e He)]. }
    pose proof (com_WB_ok RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ (mbio_ent K max) COM ltac:(intros e He; left; exact (XLC e He))) as (KWS & KWFR & KWFF & KWSH & KWL & KWP).
    assert (XLV : forall e, In e (mbio_ent K max) -> In e (rt_live RT Σ)) by (intros e He; exact (CLV _ (proj1 (XLC e He)))).
    destruct (com_call_pre0 RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ COM) as (EU & COK & INCL1 & FRMAX & CRED & HLO & H352).
    assert (INF : In (e_f RT en, 1%nat) (rt_frames RT Σ)) by (rewrite FRS; left; reflexivity).
    pose proof (af_frames_range RT AF Σ m _ _ ART0 INF) as (_ & FLO & _ & FR4). change (fs_size 1) with 128 in FLO, FR4.
    set (PP := e_f RT en + 64) in *.
    (* [comment removed for export] *)
    assert (PPF : forall a, PP <= a < PP + 8 ->
               aclient (rt_live RT Σ) (rt_frames RT Σ) (e_sp1 RT en) a /\ ~ aclient (e_live RT en) (e_frames RT en) (e_PL RT en) a /\ ~ client_static a
            /\ ~ (0x7fff8000 <= a < 0x10007fff8000) /\ a < e_PL RT en - 104 /\ (forall p n, In (p, n) (e_live RT en) -> ~ (p <= a < p + n))).
    { intros a Ha. exact (seg_byte_facts RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ (PP, PP + 8) a COM ltac:(right; right; unfold PP; cbn; lia) ltac:(cbn; exact Ha)). }
    assert (WS : forall x, e_sp1 RT en <= x < USTACK_TOP -> outside ((PP, PP + 8) :: mbio_W K max) x).
    { intros x Hx. split; [clear - Hx FLO LOW HLO; unfold PP; lia| exact (KWS x Hx)]. }
    assert (WFR : forall f k x, In (f, k) (e_frames RT en) -> f <= x < f + fs_size k - 8 -> outside ((PP, PP + 8) :: mbio_W K max) x).
    { intros f k x Hin Hx. split; [| exact (KWFR f k x Hin Hx)]. intros R. apply (proj1 (proj2 (PPF x R))). right; right; right; left. exists f, k. split; [exact Hin| exact Hx]. }
    assert (WSH : forall x, shad (e_f RT en) <= x < shad (e_f RT en) + 16 -> outside ((PP, PP + 8) :: mbio_W K max) x).
    { intros x Hx. split; [| exact (KWSH x Hx)]. intros R. apply (proj1 (proj2 (proj2 (proj2 (PPF x R))))). clear - Hx F0 FTOP. unfold shad, SHB, USTACK_TOP in *. Z.div_mod_to_equations. lia. }
    assert (WL : w_live RT Σ (mbio_ent K max) ((PP, PP + 8) :: mbio_W K max)).
    { intros p n x Hin NIN Hx. split; [| exact (KWL p n x Hin NIN Hx)]. destruct (FR4 p n Hin) as [Q|Q]; clear - Q Hx; unfold PP; lia. }
    assert (WP : forall a, aclient (e_live RT en) (e_frames RT en) (e_PL RT en) a -> outside (pem_W RT en) a -> outside ((PP, PP + 8) :: mbio_W K max) a).
    { intros a Ha Ho. split; [intros R; exact (proj1 (proj2 (PPF a R)) Ha)| exact (KWP a Ha Ho)]. }
    (* [comment removed for export] *)
    assert (PP8 : PP mod 8 = 0) by (unfold PP; clear - F64; Z.div_mod_to_equations; lia).
    pose proof FFC as FFC0. unfold ff_cells in FFC0.
    change ([C8 (wz FF_MAGIC); C8 (wz FF_DESCR); CB 16 hj; C4 lenv; CB 12 j1; C4 tav; CB 12 j2; C8 bmv; CB 48 j3])
      with ([C8 (wz FF_MAGIC); C8 (wz FF_DESCR); CB 16 hj; C4 lenv; CB 12 j1; C4 tav; CB 12 j2] ++ [C8 bmv] ++ [CB 48 j3]) in FFC0.
    pose proof (proj1 (rw_cells_app m _ _ _) FFC0) as [FA FBC]. pose proof (proj1 (rw_cells_app m _ _ _) FBC) as [FB FC].
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add] in FB, FC. fold PP in FB. replace (e_f RT en + 64 + 8) with (PP + 8) in FC by (unfold PP; lia).
    assert (SH8 : bytes_at asegs m (shad PP) [z8]).
    { unfold PP. change (e_f RT en + 64) with (e_f RT en + 64 * 1). rewrite (shad_add64 _ 1 F64). unfold ff_shadow in FFS.
      exact (rw_C1_bytes m _ _ (rw_cells_head m _ _ _ (rw_cells_skip m (shad (e_f RT en))
               [C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 4); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 4); C1 (Z_to_bv 8 (-14))] _ FFS))). }
    assert (PPLOC : pp_loc (rt_frames RT Σ) m (bv_unsigned (wz (e_sp1 RT en))) PP).
    { right. exists (e_f RT en), 1%nat. split; [exact INF|]. split; [unfold PP; lia|]. split; [change (fs_size 1) with 128; unfold PP; lia| exact SH8]. }
    assert (APART : forall e, In e (mbio_ent K max) -> PP + 8 <= fst e \/ fst e + snd e <= PP).
    { intros [p n] He. cbn [fst snd]. destruct (FR4 p n (XLV _ He)) as [Q|Q]; clear - Q; unfold PP; lia. }
    apply (C_BT Σ (e_PMc RT en) (wz site) (wz (e_sp1 RT en)) (e_gp RT en) (wz TP_A) t0 t1 t2 (e_sp RT en) (wz (e_sp1 RT en)) (wz BIv) (wz 115) (wz 0) (wz PP) a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 (wz (shad (e_f RT en))) (wz SHB) s10 s11 t3 t4 t5 t6 F fc m (e_lo RT en) (e_canary RT en) K BIv meth len max offK PP bmv
             FDO MST eq_refl eq_refl eq_refl eq_refl eq_refl (ex_intro _ BM0 MBX) PP8 FB PPLOC APART
             ART0 MI COK ltac:(rewrite EU; clear - LOR; unfold PEM_CALLEE_STACK, BCTRL_STACK in *; lia) CLE T c HA).
    intros c' AP. unfold apost in AP.
    destruct (ASTA_unpack RT Σ _ _ c' AP) as (ms' & (v & m' & RS & (ART1 & MI1 & ST1) & PR & CLE1 & (BM & -> & WM1 & PPC & MBX1)) & Hc'). clear AP.
    destruct RS as (y0 & y1 & y2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & y3 & y4 & y5 & y6 & F' & fc' & ->).
    rewrite EU in ST1, PR. rewrite (ret_pc_even site SR SE) in Hc'.
    assert (LE1 : libenv m' (e_LBL RT en) (e_E RT en)).
    { eapply (libenv_keep libenv libenv_fp libenv_agree libenv_fp_where); [exact LE| exact PR| exact INCL1|].
      intros x Hx. destruct (libenv_fp_where _ _ Hx) as [(_ & CS & _)|(p' & n' & Hin & Hp)].
      - split; [intros R; exact (proj1 (proj2 (proj2 (PPF x R))) CS)| exact (com_WB_static RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ _ COM XLV x CS)].
      - apply (WL p' n' x (ELV _ (INCL _ Hin))); [| exact Hp]. intros X. apply (CFR _ (proj1 (XLC _ X))). cbn [fst]. exact (in_map fst _ _ (INCL _ Hin)). }
    assert (SEC1 : sec_off m').
    { eapply sec_off_agree; [exact SEC|]. intros a Ea. rewrite <- (Z_to_bv_bv_unsigned a), Ea.
      apply PR; rewrite (unsigned_lit SEC_INIT) by (unfold SEC_INIT; clear; lia); [apply acl_static; apply client_static_intro; unfold SEC_INIT; clear; lia|].
      split; [intros R; exact (proj1 (proj2 (proj2 (PPF _ R))) ltac:(apply client_static_intro; unfold SEC_INIT; clear; lia))|].
      exact (com_WB_static RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ _ COM XLV SEC_INIT ltac:(apply client_static_intro; unfold SEC_INIT; clear; lia)). }
    (* [comment removed for export] *)
    assert (FFC1 : rw_cells asegs m' (e_f RT en) (ff_cells hj lenv j1 tav j2 (wz BM) j3)).
    { unfold ff_cells. change ([C8 (wz FF_MAGIC); C8 (wz FF_DESCR); CB 16 hj; C4 lenv; CB 12 j1; C4 tav; CB 12 j2; C8 (wz BM); CB 48 j3])
        with ([C8 (wz FF_MAGIC); C8 (wz FF_DESCR); CB 16 hj; C4 lenv; CB 12 j1; C4 tav; CB 12 j2] ++ [C8 (wz BM)] ++ [CB 48 j3]).
      apply (proj2 (rw_cells_app m' _ _ _)). split.
      - eapply rw_cells_agree_nw; [exact FA|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add]. intros a Ha. cbv beta in Ha.
        apply PR; [apply (acl_frame _ _ _ (e_f RT en) 1%nat); [exact INF| change (fs_size 1) with 128; lia]|].
        split; [unfold PP; clear - Ha; lia| apply KWFF; lia].
      - apply (proj2 (rw_cells_app m' _ _ _)). cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add]. fold PP. split; [exact PPC|].
        replace (e_f RT en + 64 + 8) with (PP + 8) by (unfold PP; lia).
        eapply rw_cells_agree_nw; [exact FC|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add]. intros a Ha. cbv beta in Ha.
        apply PR; [apply (acl_frame _ _ _ (e_f RT en) 1%nat); [exact INF| change (fs_size 1) with 128; unfold PP in Ha; lia]|].
        split; [clear - Ha; lia| apply KWFF; unfold PP in Ha; lia]. }
    unfold PP in *. replace (e_f RT en + 64 + 8) with (e_f RT en + 72) in * by lia.
    eapply (Hk m' F' fc' y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 c' BM); [| exact PR| exact WS| exact WFR| exact WL| exact FFC1| exact MBX1| exact MI1| exact Hc'].
    eapply (com_call RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ Σ m m' off off crem crem lrem lrem _ _ _ _ 0 COM ART1 MI1 ST1 PR CLE1 SEC1 LE1);
      [| exact OFF| reflexivity| reflexivity| reflexivity| clear; lia| exact CR0| clear; lia| exact LR0| clear; lia
       | exact ELV| exact WP| exact WS| exact WSH| exact PERM| exact CFR| exact ND| exact LPOS| exact NTL].
    eapply (mbio_rep_keep (rt_live RT Σ)); [exact MB| exact PR| intros e He; split; exact (ELV _ (KLV _ He))|].
    intros e x He Hx. exact (com_klv_outX RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem _ _ _ COM WL ltac:(intros e' He'; right; exact (proj1 (XLC e' He'))) e x He Hx).
  Qed.
End W3X4.
