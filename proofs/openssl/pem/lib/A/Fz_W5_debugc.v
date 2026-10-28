(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA RzCPS Arr.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface RT_iface_pem D_libiface_pem D_defs D_agree D_clx PLayout Fz_kit Fz_ckit Fz_M_malloc Fz_M_free Fz_env Th_mutex Fz_W5_glx Fz_W5_icb Fz_W5_gsi Fz_W5_rep Fz_W5_debug Fz_W5_clear Fz_W2_exdc Fz_W2_bnew Fz_W3_iface Fz_W5_env Fz_W5_error.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma outside_libW_dbg : forall LBL E a, outside ((E, E + 904) :: lib_W LBL) a -> outside (DBG_W E) a.
Proof.
  intros LBL E a H. cbn [outside] in H. destruct H as [HE H]. unfold lib_W in H. destruct (outside_appD _ _ _ H) as [HL _].
  unfold LIB_W, DBG_W, ERRNO_A, G_ALLOW_CUST in *. cbn [outside] in HL. cbn [outside]. lia.
Qed.

(* [comment removed for export] *)
Lemma slots_ok_none : forall fs fn ks j, slots_ok fs fn ks [] -> length fs = 16%nat -> length fn = 16%nat -> 0 <= j < 16 ->
  nth_error fs (Z.to_nat j) = Some (Z_to_bv 64 0) /\ nth_error fn (Z.to_nat j) = Some (Z_to_bv 64 0).
Proof.
  intros fs fn ks j (ND & LEN & RNG & SL & NUL) LF LN Hj. destruct ks as [|k0 ks']; [| cbn in LEN; discriminate].
  destruct (nth_error fs (Z.to_nat j)) as [wf|] eqn:EF; [| exfalso; apply nth_error_None in EF; rewrite LF in EF; lia].
  destruct (nth_error fn (Z.to_nat j)) as [wn|] eqn:EN; [| exfalso; apply nth_error_None in EN; rewrite LN in EN; lia].
  rewrite (NUL (j, false) wf ltac:(cbn; lia) ltac:(unfold slot_word; cbn [fst snd]; exact EF) ltac:(intros [])).
  rewrite (NUL (j, true) wn ltac:(cbn; lia) ltac:(unfold slot_word; cbn [fst snd]; exact EN) ltac:(intros [])). split; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma slots_ok_two : forall fs fn ks QF nf QN nn, slots_ok fs fn ks [] -> length fs = 16%nat -> length fn = 16%nat -> 0 < QF -> 0 < QN -> 0 < nf -> 0 < nn ->
  slots_ok (upd fs 1 (Z_to_bv 64 QF)) (upd fn 1 (Z_to_bv 64 QN)) [(1, true); (1, false)] [(QN, nn); (QF, nf)].
Proof.
  intros fs fn ks QF nf QN nn SL LF LN QF0 QN0 NF NN. pose proof SL as (ND & LEN & RNG & SL4 & NUL). destruct ks as [|k0 ks']; [| cbn in LEN; discriminate].
  split; [apply NoDup_ListNoDup; apply List.NoDup_cons; [cbn; intros [X|[]]; discriminate|]; apply List.NoDup_cons; [intros []|]; apply List.NoDup_nil|]. split; [reflexivity|].
  split; [intros ik [<-|[<-|[]]]; cbn; lia|]. split.
  - intros j ik pn Hk Hp. destruct j as [|[|j]]; cbn in Hk, Hp; [injection Hk as <-; injection Hp as <- | injection Hk as <-; injection Hp as <- | destruct j; discriminate];
      unfold slot_word; cbn [fst snd]; (split; [apply nth_error_upd_same; lia | cbn; lia]).
  - intros ik w Hi Hw Hn. unfold slot_word in Hw. destruct ik as (i, b). cbn [fst snd] in *.
    assert (Hi1 : i <> 1) by (intros ->; apply Hn; destruct b; cbn; tauto).
    destruct b; rewrite nth_error_upd_other in Hw by lia; [exact (NUL (i, true) w Hi Hw ltac:(intros [])) | exact (NUL (i, false) w Hi Hw ltac:(intros []))].
Qed.

Section CDbgA.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis C_DBG : Fz_W5_debug.err_set_debug_stmt RT GOBJ.
Variables FZ_SITES FZ_CALLS : list (Z * Z).
Hypothesis HCG_D : cg_sub DBG_SITES DBG_CALLS FZ_SITES FZ_CALLS.

Lemma lit_of_pem : forall L n str, pem_lit_ok GOBJ L n str -> exists b sz slack, lit_ok GOBJ L b sz str slack /\ n = Z.of_nat (length str) + 1 /\ 1 < n <= 64.
Proof.
  intros L n str (b & sz & slack & RO & NN & NE & HN & HR & SLK & GO & B1 & B2 & L1 & L2). exists b, sz, slack. split; [| exact (conj HN HR)].
  unfold lit_ok. repeat (split; [first [assumption | lia]|]). exact L2.
Qed.

Theorem err_set_debug_proof : Fz_W3_iface.err_set_debug_stmt RT GOBJ libenv errst_live FZ_SITES FZ_CALLS.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo outer canary LBL E SF nf SN nn line fstr nstr
         FDO MST Htp HA0 HA1 HA2 HLINE LE INCL INE EL LITF LITN ART0 MI0 CALL HSTK CLE CTX UWC CGH HFR HLIVE HCR.
  intros T c HA Hk.
  destruct LE as (od & e & k & MK & SA & NODES & LV & pad & tw & ne & kd & LK & ELBL & ENV & AL1 & AL2 & AL3 & AL4 & XS & LKC & APT).
  destruct EL as (bot' & fl & mk & buf & fs & ls & fn & ks & ES & SL & HB).
  pose proof ES as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LFS & _ & _ & _ & LFN & _).
  destruct (slots_ok_none fs fn ks 1 SL LFS LFN ltac:(lia)) as [FS1 FN1].
  destruct (lit_of_pem SF nf fstr LITF) as (bf & szf & slf & LOKF & NF & RF). destruct (lit_of_pem SN nn nstr LITN) as (bn & szn & sln & LOKN & NN & RN).
  assert (BLK : err_blocks (rt_live RT Σ) MK SA NODES E).
  { split; [apply INCL; rewrite ELBL; cbn; tauto|]. split; [apply INCL; rewrite ELBL; cbn; tauto|]. split; [apply INCL; rewrite ELBL; cbn; tauto|].
    split; [exact INE|]. exact (conj AL1 (conj AL2 (conj AL3 AL4))). }
  pose proof (afp_live_hi RT GOBJ AFP Σ m E 904 ART0 INE ltac:(lia)) as EHI.
  assert (INLK : In (LK, 40) (rt_live RT Σ)) by (apply INCL; rewrite ELBL; cbn; tauto).
  pose proof (live_in_disj RT AF Σ m LK 40 E 904 ART0 INLK INE ltac:(intros X; injection X; lia)) as APLE.
  apply (C_DBG Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo outer od e k MK SA NODES E LV pad tw ne 1 bot'
           fl mk buf fs ls fn (Z_to_bv 8 1) canary SF bf szf fstr slf SN bn szn nstr sln
           FDO MST Htp HA0 HA2 LOKF LOKN ART0 MI0 CALL ltac:(clear - HSTK; unfold ERRD_STACK in *; lia) CTX UWC (cg_has_of_sub _ _ _ _ _ CGH HCG_D) HFR
           ltac:(clear - HLIVE; lia) ltac:(clear - HCR; lia) ENV BLK ES FS1 FN1 CLE T c HA).
  intros c' (Σ' & e' & v & qf & qn & ls' & AST & LV' & FRS' & SP' & CR' & QF0 & QN0 & CG'). apply Hk. exists Σ', qf, qn.
  rewrite <- NF, <- NN in LV'.
  split; [| split; [exact LV'|]; split; [exact FRS'|]; split; [exact SP'|]; split; [clear - CR'; lia|]; split; [exact CG'|]; exact (conj QF0 QN0)].
  unfold apost. eapply ASTA_conseq; [exact AST|]. cbv beta. intros ms (m' & RS & (ART1 & MI1 & WM1 & ST1) & PRES & ENV' & ES' & CLE' & _ & _). exists v, m'.
  split; [exact RS|]. split; [exact (conj ART1 (conj MI1 ST1))|].
  assert (PR : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (bv_unsigned a) -> outside ((E, E + 904) :: lib_W LBL) (bv_unsigned a) -> m' a = m a).
  { intros a Ha Ho. apply PRES; [exact Ha| exact (outside_libW_dbg LBL E _ Ho)]. }
  split; [exact PR|].
  assert (PRS : forall a : word, client_static (bv_unsigned a) -> ~ (ERRNO_A <= bv_unsigned a < ERRNO_A + 4) -> bv_unsigned a <> G_ALLOW_CUST -> m' a = m a).
  { intros a Hs Hn Hl. apply PRES; [right; left; exact Hs|]. unfold DBG_W. cbn [outside]. pose proof Hs as [(l & h & Hin & Hx) _].
    unfold CLIENT_STATIC in Hin. cbn [In] in Hin. clear - Hn Hl Hin Hx EHI. repeat (destruct Hin as [EQ|Hin]; [injection EQ as <- <-; lia|]). destruct Hin. }
  split; [exact CLE'|]. split; [exact WM1|]. split.
  - exists od, e', k, MK, SA, NODES, LV, pad, tw, ne, kd, LK. split; [exact ELBL|]. split; [exact ENV'|]. split; [exact AL1|]. split; [exact AL2|]. split; [exact AL3|]. split; [exact AL4|].
    pose proof XS as (_ & _ & KD & _).
    split; [apply (exd_stat_agree m m' kd LK XS); intros a Ha; apply PRS;
            [exact (exd_fp_static kd _ KD Ha)| unfold exd_fp, ERRNO_A in Ha; unfold ERRNO_A; clear - Ha KD; lia| unfold exd_fp in Ha; unfold G_ALLOW_CUST; clear - Ha KD; lia]|].
    split; [| exact APT].
    apply (rw_cells_agree_nw asegs m m' _ _ LKC). intros a Ha. cbv beta in Ha. unfold mutex_cells in Ha. cbn [cells_size csize Nat.add] in Ha.
    apply PRES; [apply (acl_live _ _ _ LK 40); [exact INLK| clear - Ha; lia]|]. unfold DBG_W, ERRNO_A, G_ALLOW_CUST. cbn [outside].
    pose proof (afp_live_hi RT GOBJ AFP Σ m LK 40 ART0 INLK ltac:(lia)) as LKHI. clear - Ha APLE LKHI. lia.
  - exists bot', fl, mk, buf, (upd fs 1 (Z_to_bv 64 qf)), ls', (upd fn 1 (Z_to_bv 64 qn)), [(1, true); (1, false)].
    split; [exact ES'|]. split; [| exact HB]. apply (slots_ok_two fs fn ks qf nf qn nn SL LFS LFN QF0 QN0); clear - RF RN; lia.
Qed.
End CDbgA.
