(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import ShapeAlg.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import ImageA RzCPS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Layout RT_iface D_defs D_kit I_read RT_liveprim L_libA.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.L2 Require Import L2Kit L2Act L2Stmt.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzCStream BzCState BzCBlock BzCDriver BzArrD CmpMem CmpCut CmpSess CmpSess2 CmpSessB CmpFsKit0 AsanKit AsanCut A0_cmp_cbV A0_b2c_bzc.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpCut6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.
#[local] Notation mem := (word -> option byte).

Section BZC.
Context {BZP : BzParams} {ACEIL__ : ACeil}.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis AF_PRIM : af_live_primary RT.
Variables (HCXB : cctx -> Z -> eg -> est -> zstrm -> Prop) (CBFACTS : est -> Prop).
Hypothesis HC : handle_compress_contract RT HCXB CBFACTS.

(* [comment removed for export] *)
Lemma lib_of_munch : forall W (m m' : mem), L_libA.LIB_A m -> munch W m m' -> (forall x, 802816 <= x < 806144 -> outside W x) -> L_libA.LIB_A m'.
Proof.
  intros W m m' H MU HO. apply (L_libA.LIB_locA m m' H). intros a (l0 & h0 & IN & R). apply MU. apply HO.
  cbn [D_libiface.LIB_FP In] in IN. destruct IN as [E|[E|[]]]; injection E as <- <-; lia.
Qed.
(* [comment removed for export] *)
Lemma bzc_tail_shape : forall e z pr ret e2 z2, bzc_finish_tail e z pr = (ret, e2, z2) ->
  z2 = z /\ (e2 = e \/ e2 = est_set_modes e BZ_M_IDLE (e_state e) (e_avail_in_expect e)).
Proof.
  intros e z pr ret e2 z2 H. unfold bzc_finish_tail in H.
  destruct (negb pr); [injection H as _ <- <-; auto|].
  destruct ((0 <? e_avail_in_expect e) || negb (isempty_RL_e e) || (e_state_out_pos e <? bw_numZ (e_bw e)))%bool; injection H as _ <- <-; auto.
Qed.

Theorem bzCompress_cps : bzCompress_contract RT HCXB CBFACTS.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m cx ob on dbza dbzfr g e z nin pl OB p1 p2 lo usp STRM W
         FDO MST A0E A1E TP CEQ MRUN SINP AIN OUTR AOUT EM AM LIB SM SOKA OBM LOB OOK OLIV PLM ZIN PAY PAYL ELIV A1LIV A2LIV FTLIV FRMAX CRED ART0 MI0 ST0 LOW LOR SPT SPA
         CX SEP IMG LAWS HX.
  intros T c Hc Hk. subst a0 a1.
  set (P := usp - 80).
  (* [comment removed for export] *)
  assert (WCL : forall x, ~ outside W x -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp x).
  { intros x Hx. unfold W in Hx. cbn [outside] in Hx.
    destruct SOKA as ((f & k & FIN & FLO & FHI) & _ & _).
    assert (C : (c_E cx <= x < c_E cx + ESTATE_SIZE) \/ (c_A1 cx <= x < c_A1 cx + ARR1_SIZE) \/ (c_A2 cx <= x < c_A2 cx + ARR2_SIZE) \/
                (c_FT cx <= x < c_FT cx + 4 * FTAB_WORDS) \/ (ob <= x < ob + on) \/ (STRM <= x < STRM + 80)) by (clear - Hx; lia).
    destruct C as [C|[C|[C|[C|[C|C]]]]].
    - right; right; left. exists (c_E cx), ESTATE_SIZE. split; [exact ELIV| lia].
    - right; right; left. exists (c_A1 cx), ARR1_SIZE. split; [exact A1LIV| lia].
    - right; right; left. exists (c_A2 cx), ARR2_SIZE. split; [exact A2LIV| lia].
    - right; right; left. exists (c_FT cx), (4 * FTAB_WORDS). split; [exact FTLIV| lia].
    - right; right; left. exists ob, on. split; [exact OLIV| lia].
    - right; right; right; left. exists f, k. split; [exact FIN| lia]. }
  destruct (act_setup_nf RT AF Σ m lo P usp W ART0 LOW ltac:(unfold P, RT_STACK in *; lia) ltac:(unfold P; lia) SPT
              ltac:(unfold P; clear - SPA; Z.div_mod_to_equations; lia) WCL) as (G & SOK).

  (* [comment removed for export] *)
  pose proof CX as CX'. unfold cctx_ok in CX'. cbv zeta in CX'.
  destruct CX' as (RE & RE' & RA1 & RA1' & RA2 & RA2' & RFT & RFT' & _ & _ & _ & _ & ME16 & MA1 & MA2 & MFT & _).
  pose proof IMG as IMG'. unfold cctx_img, img_apart, IMG_LO3 in IMG'. cbn [ci_hi aci_c A0C] in IMG'. destruct IMG' as (_ & IA1 & IA2 & IFT & _).
  pose proof alloc_ceiling_range as ACR. bz_params.
  unfold FTAB_WORDS, ESTATE_SIZE, CEIL in *. change (4 * 65537) with 262148 in *.
  destruct IA1 as [IA1|IA1]; [exfalso; clear - IA1 RA1 BZbsL__; lia|]. destruct IA2 as [IA2|IA2]; [exfalso; clear - IA2 RA2 BZbsL__; lia|].
  destruct IFT as [IFT|IFT]; [exfalso; clear - IFT RFT; lia|].
  pose proof (AF_PRIM Σ m _ _ ART0 ELIV ltac:(clear; lia)) as IE. unfold SEGTOP_A in IE.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR. fold usp in SPR.
  pose proof LOR as LOR'. unfold RT_STACK in LOR'.
  set (X := CBE ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc cx lo false).
  assert (XOK : cbenv_ok X).
  { unfold cbenv_ok, CEILv. cbn [X ce_sp ce_cx ce_lo]. fold usp.
    repeat (split; [first [assumption| clear - RE RE' RA1 RA1' RA2 RA2' RFT RFT' CEQ LOW LOR' SPR IE IA1 IA2 IFT; lia]|]). exact SPA. }
  (* [comment removed for export] *)
  destruct SOKA as ((fS & kS & FIN & FLO & FHI) & S8 & ZSH).
  pose proof (af_frames_range RT AF Σ m fS kS ART0 FIN) as (FS0 & FS1 & _ & FSL).
  pose proof (af_frames_align RT AF Σ m fS kS ART0 FIN) as (_ & FSEG). unfold SEGTOP_A in FSEG.
  pose proof (af_frames_hi RT AF Σ m fS kS ART0 FIN) as FSHI.
  assert (SLO : 0x61e000 <= STRM) by (clear - FSEG FLO; lia).
  assert (SHI : STRM + 80 <= CEILv) by (unfold CEILv; clear - FS1 FHI CEQ; lia).
  assert (SES : apartv (c_E cx) ESTATE_SIZE STRM 80) by (unfold apartv, ESTATE_SIZE; destruct (FSL _ _ ELIV) as [D|D]; clear - D FLO FHI; lia).
  set (SHE := c_E cx / 8 + 2147450880). set (SHS := STRM / 8 + 2147450880).
  assert (AE : sanchor (c_E cx) SHE) by (apply sanchor_intro; clear - ME16; Z.div_mod_to_equations; lia).
  assert (AS : sanchor STRM SHS) by (apply sanchor_intro; exact S8).
  clearbody SHE SHS.
  (* [comment removed for export] *)
  pose proof (hlB_hci _ _ LAWS _ _ _ _ _ HX) as HCI0.
  destruct (HCIB_avail_in _ _ _ _ _ HCI0) as (_ & AVR).
  (* [comment removed for export] *)
  destruct EM as (EH1 & INU & UNS & EH2 & MTF & SEL & SLM & LEN & COD & RFQ & LNP).
  destruct AM as (AR1 & AR2 & FTB). unfold FTAB_WORDS in FTB.
  destruct (af_acc_live RT AF Σ m _ _ ART0 ELIV) as [_ ACCE].
  pose proof (af_live_range RT AF Σ m _ _ ART0 ELIV) as (_ & EL1 & _).
  pose proof (af_live_offshadow RT AF Σ m _ _ ART0 ELIV) as EOFF.
  assert (ACCS : acc asegs m STRM 80).
  { pose proof (acc_of_zero_shadow asegs m STRM (STRM / 8 + 2147450880) 0 10 S8 eq_refl ltac:(clear - SLO; lia) ltac:(clear; lia)) as A.
    replace (STRM + 8 * 0) with STRM in A by (clear; lia). change (8 * Z.of_nat 10) with 80 in A. apply A.
    replace (STRM / 8 + 2147450880 + 0) with (shad STRM) by (unfold shad, SHB; clear; lia). exact ZSH. }
  assert (AFW : app_fp (bzcA_W X)).
  { unfold bzcA_W. cbn [app_fp X ce_cx ce_sp]. fold usp. unfold SH_LO, SH_HI. split; [clear - EOFF; lia|]. split; [right; clear - LOW LOR' CEQ ACR; lia| exact I]. }
  assert (SHe : shzW a0segs (bzcA_W X) m (c_E cx) (c_E cx + ESTATE_SIZE)).
  { unfold ESTATE_SIZE. apply (shzW_of_acc a0segs (bzcA_W X) m (c_E cx) 55768 _ _ ACCE AFW); [clear - RE; lia| clear - RE' ACR; lia| clear; lia| clear - ME16; Z.div_mod_to_equations; lia]. }
  assert (SHs : shzW a0segs (bzcA_W X) m STRM (STRM + 80)).
  { apply (shzW_of_acc a0segs (bzcA_W X) m STRM 80 _ _ ACCS AFW); [clear - SLO; lia| clear - SHI ACR; unfold CEILv in SHI; lia| clear; lia| clear - S8; Z.div_mod_to_equations; lia]. }
  destruct (af_client_consts RT AF Σ m ART0) as (G1 & G2 & _ & _).
  assert (AC : aconsts A0C m) by (split; [exact (ro_C8_KN m _ _ G1)| exact (ro_C8_KN m _ _ G2)]). clear G1 G2.
  eapply (l1_realizes RT AF Σ PMc _ T c MST Hc).
  eapply (A0_bzc_A X _ SHE SHS ob on dbza dbzfr nin p1 p2 XOK AE AS SLO SHI SES g e z m);
    [exact MRUN| clear - AIN AVR; lia| exact EH1| exact SM| exact (kmem_inv_N _ _ MI0)| exact ST0| exact AC| exact SHe| exact SHs|].
  clear Hc EH1 SM SHe SHs.
  intros m1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y22 y23 y28 y29 y30 y31 EH1 SM SAV ST1n NMI1 MU1 WM1. apply evt_done. intros c1 Hc1.
  cbn [X ce_cx ce_sp ce_lo ce_gp ce_tp ce_F ce_fc ce_s9 ce_s10 ce_s11] in EH1, SM, SAV, ST1n, MU1, Hc1. fold usp in SAV, ST1n, MU1, Hc1.
  assert (PE : P = usp - 80) by reflexivity.
  destruct (stk_split a0segs m lo P usp ST0 ltac:(clear - PE LOR'; lia)) as [ST0P _].
  unfold bzcA_W in MU1. cbn [X ce_cx ce_sp] in MU1. fold usp in MU1.
  destruct (after_l1 AF G Σ _ m m1 SOK ART0 MI0 ST0P (presi_refl _ _ _ _ m) NMI1 MU1 WM1 ltac:(per_interval; unfold W, P; cbn [outside]; lia)) as (ART1 & MI1 & ST1 & PR1 & STEP1).
  (* [comment removed for export] *)
  pose proof SEP as SEP'. unfold cctx_sep, apart in SEP'. cbv zeta in SEP'. destruct SEP' as (SE1 & SE2 & SEF & _).
  unfold ESTATE_SIZE, FTAB_WORDS in SE1, SE2, SEF. change (4 * 65537) with 262148 in SEF.
  pose proof OOK as OOK'. unfold out_okB, apart, img_apart, IMG_LO3, CEIL in OOK'. cbn [ci_hi aci_c A0C] in OOK'.
  destruct OOK' as (OB0 & ON0 & OBC & ONR & SOE & _ & _ & _ & OIMG). unfold ESTATE_SIZE in SOE.
  pose proof (af_fshadow_apart RT AF Σ m fS kS ART0 FIN) as (FSHL & _).
  assert (SHSR : shad fS <= SHS /\ SHS + 10 <= shad (fS + fs_size kS)).
  { destruct AS as [_ ->]. unfold shad, SHB. clear - FLO FHI. Z.div_mod_to_equations. lia. }
  assert (SSE : c_E cx + 55768 <= SHS \/ SHS + 10 <= c_E cx) by (destruct (FSHL _ _ ELIV) as [D|D]; clear - D SHSR; lia).
  assert (SHSH : SHS + 10 <= 17594333495296) by (destruct AS as [_ ->]; unfold CEILv in SHI; clear - SHI ACR; Z.div_mod_to_equations; lia).
  assert (ZSHn : bytes_at a0segs m SHS (repeat z8 10)) by (destruct AS as [_ ->]; exact ZSH).
  unfold apartv, ESTATE_SIZE in SES.
  change (id (c_E cx + 55768 <= c_A1 cx \/ c_A1 cx + ARR1_SIZE <= c_E cx)) in SE1. change (id (c_E cx + 55768 <= c_A2 cx \/ c_A2 cx + ARR2_SIZE <= c_E cx)) in SE2.
  change (id (c_E cx + 55768 <= c_FT cx \/ c_FT cx + 262148 <= c_E cx)) in SEF. change (id (ob + on <= c_E cx \/ c_E cx + 55768 <= ob)) in SOE.
  change (id (c_E cx + 55768 <= SHS \/ SHS + 10 <= c_E cx)) in SSE. change (id (c_E cx + 55768 <= c_bz cx + BZF_STRM \/ c_bz cx + BZF_STRM + 80 <= c_E cx)) in SES.
  clear FSHL FSL FSHI EOFF IE.
  pose proof (ck_intro P CStack) as KP. pose proof (ck_intro usp CStack) as KU.
  (* [comment removed for export] *)
  assert (PLM1 : u8ro a0segs m1 nin pl).
  { apply (u8ro_keep a0segs _ m m1 nin pl PLM MU1). intros NE. pose proof (PAY NE) as PK. unfold pay_okB, apart, CEIL, ESTATE_SIZE in PK.
    destruct PK as (_ & _ & PC & PE0 & _). cbn [disjoint_from]. clear - PC PE0 LOW LOR' CEQ. lia. }
  assert (LIB1 : L_libA.LIB_A m1) by (apply (lib_of_munch _ m m1 LIB MU1); intros x Hx; cbn [outside]; clear - Hx RE LOW LOR' CEQ ACR XOK; cbenv_open XOK; cbn [X ce_cx] in *; lia).
  clear ST0 ST0P ZSH PLM LIB.
  xfer_l1 m m1 MU1 WM1.
  clear NMI1 MU1 WM1 ST1n.
  (* [comment removed for export] *)
  assert (EM1 : emem cx a0segs (eg_set_aie g) (e_finish e z) m1).
  { unfold emem. exact (conj EH1 (conj INU (conj UNS (conj EH2 (conj MTF (conj SEL (conj SLM (conj LEN (conj COD (conj RFQ LNP)))))))))). }
  assert (AM1 : CmpCut.amem cx a0segs (e_finish e z) m1) by (unfold CmpCut.amem, FTAB_WORDS; exact (conj AR1 (conj AR2 FTB))).
  assert (SOKA1 : strm_okA RT Σ m1 STRM).
  { split; [exists fS, kS; split; [exact FIN| split; [exact FLO| exact FHI]]|]. split; [exact S8|]. destruct AS as [_ SHSE]. rewrite SHSE in ZSHn. exact ZSHn. }
  pose proof (HC Σ PMc (Z_to_bv 64 0x82614) (Z_to_bv 64 P) gp tp y5 y6 y7 (Z_to_bv 64 (-1)) (Z_to_bv 64 (c_E cx + 8)) (Z_to_bv 64 STRM) y11 y12 y13 y14 y15 y16 y17
                 (Z_to_bv 64 (c_E cx)) (Z_to_bv 64 (c_E cx + 16)) (Z_to_bv 64 (SHE + 1)) (Z_to_bv 64 2147450880) y22 y23 (Z_to_bv 64 (SHE + 2)) s9 s10 s11 y28 y29 y30 y31
                 F fc m1 cx ob on dbza dbzfr (eg_set_aie g) (e_finish e z) z nin pl OB p1 p2 lo) as HCc.
  cbv zeta in HCc. rewrite (P_unsigned G) in HCc.
  refine (cps_realizes asegs _ _ T c1 (HCc FDO MST eq_refl TP CEQ EM1 AM1 LIB1 SM SOKA1 OBM LOB OOK OLIV PLM1 ZIN PAY PAYL OUTR AOUT ELIV A1LIV A2LIV FTLIV FRMAX CRED ART1 MI1 ST1 LOW
            ltac:(clear - PE LOR; lia) ltac:(clear - PE SPT; lia) (ag_spa G) CX SEP IMG LAWS HX) Hc1 _).
  clear Hc1 HCc. intros c2 (Σ' & Hq & LV' & FR' & SP' & CR').
  destruct (ASTA_unpack RT Σ' _ _ c2 Hq) as (ms2 & (m2 & q0 & q1 & q2 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & q3 & q4 & q5 & q6 & F' & fc' & g' & POST) & Hc2). clear Hq.
  destruct (handle_compress znew (e_finish e z) z) as [[e' z'] pr] eqn:HCE.
  destruct POST as (-> & ART2 & MI2 & ST2 & EM2 & AM2 & LIB2 & SM2 & OBM2 & ZIN2 & HX2 & STEP2).
  rewrite (ret_pc_even 0x82614 ltac:(lia) eq_refl) in Hc2.
  destruct (after_call G Σ Σ' _ m1 m2 SOK LV' FR' SP' PR1 STEP2
              ltac:(per_interval; right; match goal with H : _ <= _ < _ |- _ => unfold ESTATE_SIZE, FTAB_WORDS in H; unfold W, STRM; cbn [outside]; clear - H; lia end)) as (SOK' & PR2).
  clear EH1 INU UNS EH2 MTF SEL SLM LEN COD RFQ LNP AR1 AR2 FTB SM OBM ZSHn EM1 AM1 SOKA1 PLM1 LIB1 ST1.
  unfold ESTATE_SIZE, FTAB_WORDS in STEP2. change (4 * 65537) with 262148 in STEP2.
  assert (STRMH : c_bz cx + BZF_STRM + 80 <= alloc_ceiling) by exact SHI.
  xfer_rtf G SOK STEP2 m1 m2.
  (* [comment removed for export] *)
  rewrite (bzCompress_finish_runningB znew e z MRUN), HCE in Hk.
  destruct (bzc_finish_tail e' z' pr) as [[ret e''] z''] eqn:TAIL.
  destruct (bzc_tail_shape _ _ _ _ _ _ TAIL) as (-> & E2S).
  pose proof (hlB_hci _ _ LAWS _ _ _ _ _ HX2) as HCI2.
  pose proof (HCIB_est_ok _ _ _ _ _ HCI2) as EOK2. destruct (HCIB_mode _ _ _ _ _ HCI2) as (_ & GA2 & AIE2).
  destruct (HCIB_avail_in _ _ _ _ _ HCI2) as (AVL2 & AVR2). pose proof (HCIB_numZ _ _ _ _ _ HCI2) as NZ2.
  destruct (HCIB_avail_out _ _ _ _ _ HCI2) as (AVO2 & OUTL2).
  destruct EM2 as (EH1 & INU & UNS & EH2 & MTF & SEL & SLM & LEN & COD & RFQ & LNP).
  destruct AM2 as (AR1 & AR2 & FTB). unfold FTAB_WORDS in FTB.
  assert (ELIV' : In (c_E cx, 55768) (rt_live RT Σ')) by (rewrite LV'; exact ELIV).
  destruct (af_acc_live RT AF Σ' m2 _ _ ART2 ELIV') as [_ ACCE2].
  pose proof (af_live_offshadow RT AF Σ' m2 _ _ ART2 ELIV') as EOFF2.
  assert (SHe2 : shzW a0segs (bzcB_W X) m2 (c_E cx) (c_E cx + ESTATE_SIZE)).
  { unfold ESTATE_SIZE. apply (shzW_of_acc a0segs (bzcB_W X) m2 (c_E cx) 55768 _ _ ACCE2); [| clear - RE; lia| clear - RE' ACR; lia| clear; lia| clear - ME16; Z.div_mod_to_equations; lia].
    unfold bzcB_W. cbn [app_fp X ce_cx]. unfold SH_LO, SH_HI. split; [clear - EOFF2; lia| exact I]. }
  pose proof EOK2 as EOK2'. unfold est_ok in EOK2'. destruct EOK2' as (_ & _ & _ & NB2 & NZ20 & _).
  eapply (l1_realizes RT AF Σ' PMc _ T c2 MST Hc2).
  eapply (A0_bzc_B (xFc X F' fc') _ SHE XOK AE g' e' e'' z' z' pr ret m2); [exact TAIL| exact EOK2| exact GA2| clear - AIE2 AVL2 AVR2; lia| clear - NZ2 NB2 BZbsH__; lia
                                                               | exact EH1| exact SAV| exact ST2| exact (kmem_inv_N _ _ MI2)| exact SHe2|].
  clear Hc2 EH1 SAV SHe2.
  intros m3 w5 w6 w7 w11 w12 w13 w14 w15 w16 w17 w28 w29 w30 w31 EH1 ST3n NMI3 MU3 WM3. apply evt_done. intros c3 Hc3.
  unfold bzcB_W in MU3.
  cbn [xFc X ce_cx ce_sp ce_lo ce_gp ce_tp ce_F ce_fc ce_ra ce_s0 ce_s1 ce_s2 ce_s3 ce_s4 ce_s5 ce_s6 ce_s7 ce_s8 ce_s9 ce_s10 ce_s11] in EH1, ST3n, MU3, Hc3. fold usp in ST3n.
  destruct (after_l1 AF G Σ' _ m2 m3 SOK' ART2 MI2 ST2 PR2 NMI3 MU3 WM3 ltac:(per_interval; right; right; right; unfold W; cbn [outside]; lia)) as (ART3 & MI3 & _ & PR3 & _).
  assert (LIB3 : L_libA.LIB_A m3) by (apply (lib_of_munch _ m2 m3 LIB2 MU3); intros x Hx; cbn [outside]; clear - Hx RE XOK; cbenv_open XOK; cbn [X ce_cx] in *; lia).
  pose proof (outb_length (z_outr z') OB on LOB ltac:(clear - OUTL2 AVO2; lia)) as LOBz.
  clear ST2 LIB2.
  xfer_l1 m2 m3 MU3 WM3.
  (* [comment removed for export] *)
  apply Hk. exists Σ'.
  split; [| split; [exact LV'| split; [exact FR'| split; [exact SP'| exact CR']]]].
  eapply ASTA_conseq; [exact Hc3|]. intros ms <-.
  exists m3, w5, w6, w7, w11, w12, w13, w14, w15, w16, w17, w28, w29, w30, w31, F', fc', g'.
  cbv beta iota zeta.
  split; [reflexivity|]. split; [exact ART3|]. split; [exact MI3|]. split; [exact ST3n|].
  split. { destruct E2S as [->| ->]; unfold emem; exact (conj EH1 (conj INU (conj UNS (conj EH2 (conj MTF (conj SEL (conj SLM (conj LEN (conj COD (conj RFQ LNP)))))))))). }
  split. { destruct E2S as [->| ->]; unfold CmpCut.amem, FTAB_WORDS; exact (conj AR1 (conj AR2 FTB)). }
  split; [exact LIB3|]. split; [exact SM2|]. split; [exact OBM2|]. split; [exact (conj AVO2 OUTL2)|].
  split. { destruct E2S as [->| ->]; [exact EOK2|]. destruct EOK2 as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
           exact (conj A1 (conj A2 (conj A3 (conj A4 (conj A5 (conj A6 (conj (or_introl eq_refl) (conj A8 A9)))))))). }
  exact (pres_final_nf RT AF Σ lo P usp W m m m3 ART0 LOW ltac:(clear - PE LOR'; lia) ltac:(clear - PE; lia) (munch_refl _ m) PR3).
Qed.
End BZC.
