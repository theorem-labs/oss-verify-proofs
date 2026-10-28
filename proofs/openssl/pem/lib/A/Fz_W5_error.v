(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA RzCPS Arr.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface RT_iface_pem D_libiface_pem D_defs D_agree D_clx PLayout Fz_kit Fz_ckit Fz_M_malloc Fz_env Th_mutex Fz_W5_glx Fz_W5_icb Fz_W5_gsi Fz_W5_rep Fz_W5_vset Fz_W5_seterr Fz_W5_clear Fz_W2_exdc Fz_W2_bnew Fz_W3_iface Fz_W5_env.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma outside_libW_errno : forall LBL E a, outside ((E, E + 904) :: lib_W LBL) a -> ~ (ERRNO_A <= a < ERRNO_A + 4) /\ ~ (E <= a < E + 904).
Proof.
  intros LBL E a H. cbn [outside] in H. destruct H as [HE H]. unfold lib_W in H. destruct (outside_appD _ _ _ H) as [HL _].
  unfold LIB_W, ERRNO_A in *. cbn [outside] in HL. split; [lia | exact HE].
Qed.

Section CErrA.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis C_SE : Fz_W5_seterr.err_set_error_stmt RT.
Variables FZ_SITES FZ_CALLS : list (Z * Z).

Theorem err_set_error_proof : Fz_W3_iface.err_set_error_stmt RT libenv errst_live FZ_SITES FZ_CALLS.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo outer canary LBL E lib reason strs
         FDO MST Htp -> -> -> HLIB HLIB2 HRE LE INCL INE INS EL ART0 MI0 CALL HSTK CLE CTX UWC CGH HFR HCR.
  intros T c HA Hk.
  destruct LE as (od & e & k & MK & SA & NODES & LV & pad & tw & ne & kd & LK & ELBL & ENV & AL1 & AL2 & AL3 & AL4 & XS & LKC & APT).
  destruct EL as (bot' & fl & mk & buf & fs & ls & fn & ks & ES & SL & HB).
  assert (BLK : err_blocks (rt_live RT Σ) MK SA NODES E).
  { split; [apply INCL; rewrite ELBL; cbn; tauto|]. split; [apply INCL; rewrite ELBL; cbn; tauto|]. split; [apply INCL; rewrite ELBL; cbn; tauto|].
    split; [exact INE|]. exact (conj AL1 (conj AL2 (conj AL3 AL4))). }
  pose proof (afp_live_hi RT GOBJ AFP Σ m E 904 ART0 INE ltac:(lia)) as EHI.
  assert (INLK : In (LK, 40) (rt_live RT Σ)) by (apply INCL; rewrite ELBL; cbn; tauto).
  pose proof (live_in_disj RT AF Σ m LK 40 E 904 ART0 INLK INE ltac:(intros X; injection X; lia)) as APLE.
  apply (C_SE Σ PMc ra sp gp tp t0 t1 t2 s0 s1 (wz lib) (wz reason) (wz 0) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo od e k MK SA NODES E LV pad tw ne 1 bot' fl mk buf fs ls fn
           FDO MST Htp eq_refl ART0 MI0 CALL ltac:(clear - HSTK; unfold ERRS_STACK in *; lia) ltac:(clear - HFR; lia) HCR ENV BLK ES T c HA).
  intros c' (Σ' & e' & v & buf' & AST & LV' & FRS' & SP' & CR' & CG'). apply Hk. exists Σ'.
  split; [| split; [exact LV'|]; split; [exact FRS'|]; split; [exact SP'|]; split; [clear - CR'; lia| exact CG']].
  unfold apost. eapply ASTA_conseq; [exact AST|]. cbv beta. intros ms (m' & RS & (ART1 & MI1 & WM1 & ST1) & PRES & ENV' & ES'). exists v, m'.
  split; [exact RS|]. split; [exact (conj ART1 (conj MI1 ST1))|].
  assert (PR : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (bv_unsigned a) -> outside ((E, E + 904) :: lib_W LBL) (bv_unsigned a) -> m' a = m a).
  { intros a Ha Ho. apply PRES; [exact Ha|]. destruct (outside_libW_errno LBL E _ Ho) as [H1 H2]. unfold VSE_W. cbn [outside]. clear - H1 H2. lia. }
  split; [exact PR|].
  assert (PRS : forall a : word, client_static (bv_unsigned a) -> ~ (ERRNO_A <= bv_unsigned a < ERRNO_A + 4) -> m' a = m a).
  { intros a Hs Hn. apply PRES; [right; left; exact Hs|]. unfold VSE_W. cbn [outside]. pose proof Hs as [(l & h & Hin & Hx) _].
    unfold CLIENT_STATIC in Hin. cbn [In] in Hin. clear - Hn Hin Hx EHI. repeat (destruct Hin as [EQ|Hin]; [injection EQ as <- <-; lia|]). destruct Hin. }
  split.
  { apply (cl_env_agree m m' _ _ CLE). intros a Ha. apply PRS; [exact (cl_cell_static _ Ha)|].
    destruct Ha as (l & h & Hin & Hx). unfold CL_CELLS, G_MALLOC_IMPL, CL_REALLOC_IMPL, CL_FREE_IMPL, CL_MEMSET_FUNC, G_ALLOW_CUST, PLayout.ssp_guard, ERRNO_A in *.
    cbn [In] in Hin. clear - Hin Hx. repeat (destruct Hin as [EQ|Hin]; [injection EQ as <- <-; lia|]). destruct Hin. }
  split; [exact WM1|]. split.
  - exists od, e', k, MK, SA, NODES, LV, pad, tw, ne, kd, LK. split; [exact ELBL|]. split; [exact ENV'|]. split; [exact AL1|]. split; [exact AL2|]. split; [exact AL3|]. split; [exact AL4|].
    pose proof XS as (_ & _ & KD & _).
    split; [apply (exd_stat_agree m m' kd LK XS); intros a Ha; apply PRS; [exact (exd_fp_static kd _ KD Ha)| unfold exd_fp, ERRNO_A in Ha; unfold ERRNO_A; clear - Ha KD; lia]|].
    split; [| exact APT].
    apply (rw_cells_agree_nw asegs m m' _ _ LKC). intros a Ha. cbv beta in Ha. unfold mutex_cells in Ha. cbn [cells_size csize Nat.add] in Ha.
    apply PRES; [apply (acl_live _ _ _ LK 40); [exact INLK| clear - Ha; lia]|]. unfold VSE_W, ERRNO_A. cbn [outside].
    pose proof (afp_live_hi RT GOBJ AFP Σ m LK 40 ART0 INLK ltac:(lia)) as LKHI. clear - Ha APLE LKHI. lia.
  - exists bot', fl, mk, buf', fs, ls, fn, ks. exact (conj ES' (conj SL HB)).
Qed.
End CErrA.
