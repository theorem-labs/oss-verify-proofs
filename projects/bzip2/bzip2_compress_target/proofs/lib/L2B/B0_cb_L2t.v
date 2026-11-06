(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import ShapeAlg.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import ImageA RzCPS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Layout RT_iface D_defs D_kit I_read RT_liveprim. Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.Layout.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_iface.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_kit.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.I_read.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_liveprim.TwinB__.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require L_libA.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.L2B Require Import L2Kit L2Act L2Stmt B0_fs_L2f B0_cb_L2a B0_cb_L2b B0_cb_L2c.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.L2B Require B0_sessK.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0 SegsB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzArr BzCMem BzCStream BzCState BzCMtf BzCBlock BzCHuff BzArrD BzCLemmas1 CmpMem CmpCut CmpCutMS CmpCutMtf CmpCutSM CmpCutSmA BzCFactsSmA CmpCutSmB BzCFactsGm BzCSmF1 BzCFactsSmB BzCFactsSd CmpHmKit CmpSmKit CmpSmKit2 AsanKit AsanKit2 AsanCut AsanCutB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCNumZ CmpLaws CmpCutCB BzCFactsSmA2 BzCFactsSmB3 BzCFactsSd2 BzCLemmasMs6 BzCFactsBs6 BzCFactsCb BzCSortPost.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCHuffF1.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuffF1.BzCFactsHm.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpCut6.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import B0_cmp_fsV B0_cmp_msV B0_cmp_cbV B0_cmp_fsP B0_cmp_cbP B0_cmp_cbWc B0_cmp_cbH2.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.
#[local] Notation mem := (word -> option byte).


Lemma mod16_linqC : forall x, x mod 16 = 0 -> exists q, x = 16 * q.
Proof. intros x H. exists (x / 16). Z.div_mod_to_equations. lia. Qed.

Section CBT.
Context {BZP : BzParams} {ACEIL__ : ACeil}.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis SMAL : stack_malloc_contract RT 3.
Hypothesis SSH : forall v, In v set_shadow_vals -> set_shadow_contract RT v.
Hypothesis BSC : blockSort_contract RT bsX.
Hypothesis SMC : sendMTFValues_contract RT smA_facts smB_facts sd_facts.
Hypothesis AF_PRIM : af_live_primary RT.   (* [comment removed for export] *)

Theorem compressBlock_cps : compressBlock_contract RT cb_facts.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m cx g e is_last lo usp W
    FDO MST Ha0 Ha1 TP CEQ EM AM LIB0 LIVE LIV1 LIV2 LIVF FRMAX CRED ART0 MI0 ST0 LOW LOR SPT AL CX SEP IMG PRE CBF.
  subst a0 a1. intros T c Hc Hk.
  pose proof CX as CX'. unfold cctx_ok in CX'. cbv zeta in CX'.
  destruct CX' as (RE & RE' & RA1 & RA1' & RA2 & RA2' & RFT & RFT' & _ & _ & _ & _ & ME16 & MA1 & MA2 & MFT & _).
  pose proof IMG as IMG'. unfold cctx_img, img_apart, IMG_LO3 in IMG'. cbn [ci_hi aci_c B0C] in IMG'. destruct IMG' as (_ & IA1 & IA2 & IFT & _).
  pose proof alloc_ceiling_range as ACR. bz_params. unfold FTAB_WORDS, ESTATE_SIZE, CEIL in *.
  change (4 * 65537) with 262148 in *.
  destruct IA1 as [IA1|IA1]; [exfalso; clear - IA1 RA1 BZbsL__; lia|]. destruct IA2 as [IA2|IA2]; [exfalso; clear - IA2 RA2 BZbsL__; lia|].
  destruct IFT as [IFT|IFT]; [exfalso; clear - IFT RFT; lia|].
  pose proof (AF_PRIM Σ m _ _ ART0 LIVE ltac:(clear; lia)) as IE. unfold SEGTOP_A in IE.
  destruct (mod16_linqC _ AL) as [qsp ALQ].
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR. fold usp in SPR.
  unfold RT_STACK in LOR.
  set (X := CBE ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc cx lo is_last).
  assert (XOK : cbenv_ok X).
  { unfold cbenv_ok, CmpFsKit0.CEILv. cbn [ce_cx ce_lo ce_sp X]. fold usp.
    split; [exact CX|]. split; [exact SEP|]. repeat (split; [first [assumption| clear - IE IA1 IA2 IFT CEQ LOW LOR SPR; lia]|]). exact AL. }
  set (P := 32 * ((usp - 288) / 32)).
  assert (PF : lo + 65536 + 2064 <= P /\ P + 288 <= usp /\ usp <= P + 304 /\ P mod 16 = 0 /\ exists q, P = 32 * q).
  { subst P. split; [clear - ALQ LOR; Z.div_mod_to_equations; lia|]. split; [clear - ALQ; Z.div_mod_to_equations; lia|]. split; [clear - ALQ; Z.div_mod_to_equations; lia|].
    split; [clear; Z.div_mod_to_equations; lia|]. exists ((usp - 288) / 32). reflexivity. }
  destruct PF as (YPl4 & YPh & YPa & SPA & qP & PQ).
  assert (YPl : lo <= P) by (clear - YPl4; lia).
  clearbody P.
  destruct (fs_aconsts_of_art RT AF Σ m ART0) as [AC AU].
  (* [comment removed for export] *)
  eapply (l1_realizes RT AF Σ PMc _ T c MST Hc).
  eapply (B0_cb_P1 X P _ XOK YPl YPh YPa qP m); [exact PQ| exact ST0| exact (kmem_inv_N _ _ MI0)| exact AC| exact AU|].
  intros m1 sl x11 x12 SL GAP SAV ST1 NMI1 MU1 WM1. apply evt_done. clear Hc. intros c1 Hc1.
  cbn [X ce_sp ce_lo ce_cx ce_gp ce_tp ce_il ce_F ce_fc ce_s5 ce_s6 ce_s7 ce_s8 ce_s9 ce_s10 ce_s11] in GAP, SAV, ST1, MU1, Hc1. fold usp in GAP, SAV, MU1.
  assert (MU1k : KFrame.munch [(P, usp)] m m1) by exact MU1.
  assert (ART1 : ART RT Σ m1).
  { apply (art_of_munch RT AF Σ m m1 [(P, usp)] P ART0 ltac:(clear - LOW YPl; lia) MU1k WM1). per_interval. left. unfold USTACK_TOP in *. match goal with HX : _ <= _ < _ |- _ => clear - SPT HX YPl; lia end. }
  assert (MI1 : KMem.mem_inv bsegs m1).
  { apply (kmem_inv_munch' bsegs [(P, usp)] m m1 MI0 MU1k NMI1). intros x Hx. revert Hx. refine (not_outside_cons _ _ _ _ _ _ _); [intro| refine (not_outside_nil _ _)].
    unfold KMem.UTOP, USTACK_TOP in *. match goal with HX : _ <= _ < _ |- _ => clear - SPT HX; lia end. }
  pose proof (ck_intro P CStack) as KP. pose proof (ck_intro usp CStack) as KU.
  pose proof (ck_intro (c_E cx) (CLive (c_E cx) 55768)) as KE.
  pose proof (ck_intro (c_A1 cx) (CLive (c_A1 cx) ARR1_SIZE)) as KA1. pose proof (ck_intro (c_A2 cx) (CLive (c_A2 cx) ARR2_SIZE)) as KA2.
  pose proof (ck_intro (c_FT cx) (CLive (c_FT cx) 262148)) as KFT.
  assert (BLW : c_E cx + 55768 <= P /\ c_A1 cx + ARR1_SIZE <= P /\ c_A2 cx + ARR2_SIZE <= P /\ c_FT cx + 262148 <= P) by (clear - RE' RA1' RA2' RFT' CEQ LOW YPl; lia).
  destruct BLW as (BLE & BL1 & BL2 & BLF).
  destruct EM as (EH1 & INU & UNS & EH2 & MTF & SEL & SELM & LEN & CODE & RFQ & LPK). destruct AM as (AR1 & AR2 & FTB). unfold FTAB_WORDS in FTB.
  assert (LIB1 : OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_libA.TwinB__.LIB_A m1).
  { apply (B0_sessK.lib_of_munch [(P, usp)] m m1 LIB0 MU1k). intros x Hx. cbn. split; [| exact I]. clear - Hx YPl LOW CEQ ACR. lia. }
  xfer_l1 m m1 MU1 WM1.
  (* [comment removed for export] *)
  refine (cps_realizes bsegs _ _ T c1 _ Hc1 _).
  { eapply (SMAL Σ PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 352 lo FDO MST
              ltac:(right; right; left; reflexivity) TP).
    - reflexivity.
    - change (fs_size 3) with 512. clear; lia.
    - reflexivity.
    - clear - FRMAX. lia.
    - clear - CRED. lia.
    - exact ART1.
    - exact MI1.
    - unfold call_ok. rewrite unsigned_lit by (clear - YPl YPh SPR LOW ACR CEQ; lia). unfold STACK_WIN, USTACK_TOP, RT_STACK in *.
      split; [exact ST1|]. split; [exact LOW|]. split; [clear - YPl4; lia|]. split; [clear - SPT YPh; lia| exact SPA]. }
  intros c2 (Σ1 & f & Hq2 & FRS1 & LV1 & SP1 & CR1 & FPOS & F64 & FTOP). change (fs_size 3) with 512 in *.
  destruct (ASTA_unpack RT Σ1 _ _ c2 Hq2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & WRF & WRS & ZSH) & Hc2). clear Hq2.
  destruct RS2 as (u0 & u1 & u2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->).
  rewrite unsigned_lit in ST2, PRES2 by (clear - YPl YPh SPR LOW ACR CEQ; lia). change (512 - 8) with 504 in WRF. change (512 / 8) with 64 in WRS.
  rewrite (KMState.ret_pc_even 0x899e4 ltac:(lia) eq_refl) in Hc2.
  (* [comment removed for export] *)
  set (Wcb := [(c_E cx, c_E cx + 55768); (c_A1 cx, c_A1 cx + ARR1_SIZE); (c_A2 cx, c_A2 cx + ARR2_SIZE); (c_FT cx, c_FT cx + 262148)]).
  assert (WCL : forall x, ~ outside Wcb x -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp x).
  { intros x Hx. unfold Wcb in Hx. cbn [outside] in Hx.
    assert (C : (c_E cx <= x < c_E cx + 55768) \/ (c_A1 cx <= x < c_A1 cx + ARR1_SIZE) \/ (c_A2 cx <= x < c_A2 cx + ARR2_SIZE) \/ (c_FT cx <= x < c_FT cx + 262148)) by (clear - Hx; lia).
    destruct C as [C|[C|[C|C]]]; right; right; left.
    - exists (c_E cx), 55768. split; [exact LIVE| exact C].
    - exists (c_A1 cx), ARR1_SIZE. split; [exact LIV1| exact C].
    - exists (c_A2 cx), ARR2_SIZE. split; [exact LIV2| exact C].
    - exists (c_FT cx), 262148. split; [exact LIVF| exact C]. }
  set (SHF := f / 8 + 2147450880). change (shad f) with SHF in WRS, ZSH.
  destruct (act_setup RT AF Σ Σ1 m m2 3 f SHF 512 64 lo P usp Wcb eq_refl eq_refl eq_refl eq_refl ART0 ART2 FRS1 LV1 SP1 LOW
              ltac:(unfold RT_STACK; clear - YPl4; lia) ltac:(clear - YPh; lia) SPT SPA WCL) as (G & SOK & _ & FSEG & FHI & SHR0 & SHR1 & GSELF & GLV).
  destruct (GLV _ _ LIVE) as (GFE & GSE & _ & _ & OFE & _). destruct (GLV _ _ LIV1) as (GF1 & GS1 & _ & _ & OF1 & _).
  destruct (GLV _ _ LIV2) as (GF2 & GS2 & _ & _ & OF2 & _). destruct (GLV _ _ LIVF) as (GFF & GSF & _ & _ & OFF & _).
  clearbody SHF. unfold SEGTOP_A in FSEG.
  pose proof (ag_gfr G) as (_ & FR1). unfold STACK_WIN in FR1.
  set (SHE := c_E cx / 8 + 2147450880).
  assert (AE : sanchor (c_E cx) SHE) by (split; [clear - ME16; Z.div_mod_to_equations; lia| reflexivity]).
  clearbody SHE.
  set (Y := ACE P f SHF SHE).
  assert (YOK : acenv_ok X Y).
  { unfold acenv_ok, CmpFsKit0.CEILv, SH_LO, SH_HI. cbn [ac_P ac_FB ac_SHF ce_lo ce_sp X Y]. fold usp.
    repeat split; clear - YPl4 YPh YPa FSEG FR1 CEQ SHR0 SHR1; unfold STACK_WIN in *; lia. }
  assert (YSEP : acenv_sep X Y).
  { unfold acenv_sep, CmpFsKit0.apartv, ESTATE_SIZE. cbn [ac_FB ce_cx X Y]. split; [clear - GFE; lia| split; [clear - GF1; lia| clear - GF2; lia]]. }
  assert (YOFF : acenv_offsh X Y).
  { unfold acenv_offsh, ESTATE_SIZE, SH_LO, SH_HI. cbn [ac_FB ce_cx X Y]. split; [clear - OFE; lia| split; [clear - OF1; lia| split; [clear - OF2; lia| clear - FHI; lia]]]. }
  (* [comment removed for export] *)
  assert (STEP2 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) P [] m1 m2) by exact (pfp_of_pres _ _ _ [] m1 m2 PRES2).
  assert (LIB2 : OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_libA.TwinB__.LIB_A m2).
  { apply (B0_sessK.lib_of_pfp _ _ _ [] m1 m2 LIB1 STEP2). intros x _. exact I. }
  clear ST1.
  xfer_rt G I STEP2 WM2 m1 m2.
  assert (GFE' : c_E cx + 55768 <= f \/ f + 512 <= c_E cx) by (clear - GFE; lia).
  assert (GF1' : c_A1 cx + ARR1_SIZE <= f \/ f + 512 <= c_A1 cx) by (clear - GF1; lia).
  assert (GF2' : c_A2 cx + ARR2_SIZE <= f \/ f + 512 <= c_A2 cx) by (clear - GF2; lia).
  assert (GFF' : c_FT cx + 262148 <= f \/ f + 512 <= c_FT cx) by (clear - GFF; lia).
  assert (EM2 : emem cx b0segs g e m2).
  { unfold emem. split; [exact EH1|]. split; [exact INU|]. split; [exact UNS|]. split; [exact EH2|]. split; [exact MTF|]. split; [exact SEL|]. split; [exact SELM|].
    split; [exact LEN|]. split; [exact CODE|]. split; [exact RFQ| exact LPK]. }
  assert (AM2 : CmpCut.amem cx b0segs e m2) by (unfold CmpCut.amem, FTAB_WORDS; split; [exact AR1| split; [exact AR2| exact FTB]]).
  (* [comment removed for export] *)
  eapply (cb_act RT AF SSH BSC SMC X Y g e XOK YOK YSEP YOFF AE IMG PRE CBF TP PMc (rt_frames RT Σ) (rt_live RT Σ) (rt_sp0 RT Σ) FDO MST G CEQ
            ltac:(unfold RT_STACK; cbn [ac_P ce_lo X Y]; clear - YPl4; lia) ltac:(clear - FRMAX; lia) LIVE LIV1 LIV2 LIVF GFE' GF1' GF2' GFF' GSE GS1 GS2 GSF GSELF OFF m2 LIB2
            Σ1 sl _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F2 fc2 T c2 SOK ltac:(rewrite CR1; clear - CRED; lia) EM2 AM2 SL GAP SAV WRF WRS ART2 MI2 ST2 Hc2).
  intros c' Σ2 m' z0 z1 z2 g0 g1 g2 g3 g4 g5 g6 g7 z3 z4 z5 z6 F' fc' Hc' FRS2 LV2 SP2 CR2 ART' MI' ST' POST PR'.
  apply Hk. exists Σ2.
  split; [| split; [rewrite LV2, LV1; reflexivity| split; [exact FRS2| split; [exact SP2| rewrite CR1 in CR2; clear - CR2; lia]]]].
  eapply ASTA_conseq; [exact Hc'|]. intros ms <-. exists m', z0, z1, z2, g0, g1, g2, g3, g4, g5, g6, g7, z3, z4, z5, z6, F', fc'.
  split; [reflexivity|]. split; [exact ART'|]. split; [exact MI'|]. split; [exact ST'|].
  split; [exact POST|].
  exact (pres_final RT AF Σ lo P usp Wcb m m1 m2 m' ART0 LOW ltac:(clear - YPl; lia) ltac:(clear - YPh; lia) MU1 PRES2 PR').
Qed.
End CBT.
