(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import ShapeAlg.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import ImageA RzCPS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Layout RT_iface D_defs D_kit I_read RT_liveprim.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.L2 Require Import L2Kit L2Act L2Stmt A0_fs_L2f A0_bs_L2f.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzArr BzCMem BzCState BzCSortF BzCSortM BzCBlock BzArrD CmpMem CmpCut CmpCutMS BzCLemmasFs BzCFactsFs CmpFsKit0 CmpMsKit AsanKit AsanKit2 AsanCut.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpCut6.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCFactsBs BzCLemmasMs6.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_fsV A0_cmp_msV A0_cmp_msW A0_cmp_bsV A0_cmp_bsP.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.
#[local] Notation mem := (word -> option byte).
Strategy 1000 [ms_ftab_zero ms_radix1 ms_overshoot ms_accum ms_radix2 ms_ro_init ms_sh_shift ms_sh_pass ms_shell ms_step1 ms_copy_init ms_copy_fwd ms_copy_bwd
               ms_mark ms_shifts ms_quad ms_big ms_bigs mainSort blockSort mainQSort3 mqs_loop mainSimpleSort find_orig fallbackSort].

Lemma mod16_linqB : forall x, x mod 16 = 0 -> exists q, x = 16 * q.
Proof. intros x H. exists (x / 16). Z.div_mod_to_equations. lia. Qed.

Section BST.
Context {BZP : BzParams} {ACEIL__ : ACeil}.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis SMAL : stack_malloc_contract RT 7.
Hypothesis SSH : forall v, In v set_shadow_vals -> set_shadow_contract RT v.
Hypothesis MSET : memset_icontract RT e_asan_memset.
Hypothesis SFREE : stack_free_contract RT 7.
Hypothesis FSC : fallbackSort_contract RT fs_facts.
Hypothesis AF_PRIM : af_live_primary RT.   (* [comment removed for export] *)

Theorem blockSort_cps : blockSort_contract RT bsX.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m cx g e lo usp W
    FDO MST Ha0 TP CEQ EH1 EH2 AM LIVE LIV1 LIV2 LIVF FRMAX CRED ART0 MI0 ST0 LOW LOR SPT AL CX SEP IMG EOK NB FACTS.
  subst a0. intros T c Hc Hk.
  pose proof CX as CX'. unfold cctx_ok in CX'. cbv zeta in CX'.
  destruct CX' as (RE & RE' & RA1 & RA1' & RA2 & RA2' & RFT & RFT' & _ & _ & _ & _ & ME16 & MA1 & MA2 & MFT & _).
  pose proof SEP as SEP'. unfold cctx_sep, apart in SEP'. cbv zeta in SEP'.
  destruct SEP' as (SE1 & SE2 & SEF & _ & _ & AP12 & AP1F & _ & _ & AP2F & _).
  pose proof IMG as IMG'. unfold cctx_img, img_apart, IMG_LO3 in IMG'. cbn [ci_hi aci_c A0C] in IMG'. destruct IMG' as (_ & IA1 & IA2 & IFT & _).
  pose proof alloc_ceiling_range as ACR. bz_params. unfold FTAB_WORDS, ESTATE_SIZE, CEIL in *.
  change (4 * 65537) with 262148 in *.
  destruct IA1 as [IA1|IA1]; [exfalso; clear - IA1 RA1 BZbsL__; lia|]. destruct IA2 as [IA2|IA2]; [exfalso; clear - IA2 RA2 BZbsL__; lia|].
  destruct IFT as [IFT|IFT]; [exfalso; clear - IFT RFT; lia|].
  pose proof (AF_PRIM Σ m _ _ ART0 LIVE ltac:(clear; lia)) as IE. unfold SEGTOP_A in IE.
  destruct (mod16_linqB _ AL) as [qsp ALQ]. destruct (mod16_linqB _ MA1) as [q1 AQ1]. destruct (mod16_linqB _ MA2) as [q2 AQ2]. destruct (mod16_linqB _ MFT) as [qF AQF].
  destruct (mod16_linqB _ ME16) as [qE AQE].
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR. fold usp in SPR.
  unfold RT_STACK in LOR.
  pose proof EOK as EOK0. destruct EOK as (A1OK & A2OK & FTW & NBe & EOKr).
  destruct AM as (AR1 & AR2 & FTB). unfold FTAB_WORDS in FTB.
  (* [comment removed for export] *)
  set (qo := e_nblock e + Z.land (e_nblock e) 1 + 34).
  assert (QOR : e_nblock e + 34 <= qo <= e_nblock e + 35) by (subst qo; rewrite land1_mod2; clear; Z.div_mod_to_equations; lia).
  assert (QOQ' : exists qq, qo = 2 * qq) by (exists (qo / 2); subst qo; rewrite land1_mod2; clear; Z.div_mod_to_equations; lia).
  destruct QOQ' as [qq QOQ].
  assert (EQOF : bp_qoff e = qo).
  { unfold bp_qoff, bp_n, BZ_N_OVERSHOOT. subst qo. rewrite !land1_mod2.
    destruct (Z.eqb_spec ((e_nblock e + 34) mod 2) 0); clear - e0 || clear - n; Z.div_mod_to_equations; lia. }
  assert (QOD : qo = e_nblock e + Z.land (e_nblock e) 1 + 34) by reflexivity.
  clearbody qo.
  set (X := ME ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (c_E cx) (c_A1 cx) (c_A2 cx) (c_FT cx) (e_nblock e) qo lo qE q1 q2 qF qsp qq
               (e_arr1 e) (e_arr2 e) (e_ftab e) (Z_to_bv 64 0) m).
  assert (XOK1 : msenv_ok1 X).
  { unfold msenv_ok1, CEILm. cbn [me_E me_A1 me_A2 me_FT me_lo me_sp me_n me_qE me_q1 me_q2 me_qF me_qsp me_a1 me_a2 me_ft X]. fold usp.
    repeat (split; [first [assumption| clear - RE RE' RA1 RA1' RA2 RA2' RFT RFT' CEQ LOW LOR SPR NB; lia]|]). exact FTW. }
  assert (XSEP : msenv_sep X) by (unfold msenv_sep, apartm; cbn [me_E me_A1 me_A2 me_FT X]; repeat (split; [assumption|]); assumption).
  set (P := 32 * ((usp - 544) / 32)).
  assert (PF : lo + 4096 <= P /\ P + 544 <= usp /\ usp <= P + 560 /\ P mod 16 = 0).
  { subst P. clear - ALQ LOR. Z.div_mod_to_equations. lia. }
  destruct PF as (YPl4 & YPh & YPa & SPA).
  assert (YPl : lo <= P) by (clear - YPl4; lia).
  destruct (fs_aconsts_of_art RT AF Σ m ART0) as [AC AU].
  (* [comment removed for export] *)
  eapply (l1_realizes RT AF Σ PMc _ T c MST Hc).
  eapply (A0_bs_P1 X P _ XOK1 YPl YPh YPa ((usp - 544) / 32) m); [reflexivity| exact ST0| exact (kmem_inv_N _ _ MI0)| exact AC| exact AU|].
  intros m1 v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144 v152 v160 v168 v176 v184 v192 v200 v208
    v216 v224 v232 v240 v248 v256 v264 v272 v280 v288 v296 v304 v312 v320 v328 v336 v344 v352 v360 v368 v376 v384 v392 v400 v408 v416 v424 j432 jbud x11 x12
    C0 C16 C104 C152 C200 C216 C384 C416 C424 C432 BUD GAP SAV ST1 NMI1 MU1 WM1. apply evt_done. intros c1 Hc1.
  cbn [X me_sp me_lo] in C0, C16, C104, C152, C200, C216, C384, C416, C424, C432, BUD, GAP, SAV, ST1, MU1. fold usp in GAP, SAV, ST1, MU1.
  unfold MSAVED in SAV. cbn [X me_ra me_s0 me_s1 me_s2 me_s3 me_s4 me_s5 me_s6 me_s7 me_s8 me_s9 me_s10 me_s11] in SAV.
  assert (MU1k : KFrame.munch [(P, usp)] m m1) by exact MU1.
  assert (ART1 : ART RT Σ m1).
  { apply (art_of_munch RT AF Σ m m1 [(P, usp)] P ART0 ltac:(clear - LOW YPl; lia) MU1k WM1). per_interval. left. unfold USTACK_TOP in *. match goal with HX : _ <= _ < _ |- _ => clear - SPT HX YPl; lia end. }
  assert (MI1 : KMem.mem_inv asegs m1).
  { apply (kmem_inv_munch' asegs [(P, usp)] m m1 MI0 MU1k NMI1). intros x Hx. revert Hx. refine (not_outside_cons _ _ _ _ _ _ _); [intro| refine (not_outside_nil _ _)].
    unfold KMem.UTOP, USTACK_TOP in *. match goal with HX : _ <= _ < _ |- _ => clear - SPT HX; lia end. }
  pose proof (ck_intro P CStack) as KP. pose proof (ck_intro usp CStack) as KU.
  pose proof (ck_intro (c_E cx) (CLive (c_E cx) 55768)) as KE.
  pose proof (ck_intro (c_A1 cx) (CLive (c_A1 cx) ARR1_SIZE)) as KA1. pose proof (ck_intro (c_A2 cx) (CLive (c_A2 cx) ARR2_SIZE)) as KA2.
  pose proof (ck_intro (c_FT cx) (CLive (c_FT cx) 262148)) as KFT.
  assert (BLW : c_E cx + 55768 <= P /\ c_A1 cx + ARR1_SIZE <= P /\ c_A2 cx + ARR2_SIZE <= P /\ c_FT cx + 262148 <= P) by (clear - RE' RA1' RA2' RFT' CEQ LOW YPl; lia).
  destruct BLW as (BLE & BL1 & BL2 & BLF).
  xfer_l1 m m1 MU1 WM1.
  (* [comment removed for export] *)
  refine (cps_realizes asegs _ _ T c1 _ Hc1 _).
  { eapply (SMAL Σ PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 5216 lo FDO MST
              ltac:(right; right; right; right; reflexivity) TP).
    - reflexivity.
    - change (fs_size 7) with 8192. clear; lia.
    - reflexivity.
    - clear - FRMAX. lia.
    - clear - CRED. lia.
    - exact ART1.
    - exact MI1.
    - unfold call_ok. rewrite unsigned_lit by (clear - YPl YPh SPR LOW ACR CEQ; lia). unfold STACK_WIN, USTACK_TOP, RT_STACK in *.
      split; [exact ST1|]. split; [exact LOW|]. split; [clear - YPl4 LOR YPh YPa; lia|]. split; [clear - SPT YPh; lia| exact SPA]. }
  intros c2 (Σ1 & f & Hq2 & FRS1 & LV1 & SP1 & CR1 & FPOS & F64 & FTOP). change (fs_size 7) with 8192 in *.
  destruct (ASTA_unpack RT Σ1 _ _ c2 Hq2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & WRF & WRS & ZSH) & Hc2). clear Hq2.
  destruct RS2 as (u0 & u1 & u2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->).
  rewrite unsigned_lit in ST2, PRES2 by (clear - YPl YPh SPR LOW ACR CEQ; lia). change (8192 - 8) with 8184 in WRF. change (8192 / 8) with 1024 in WRS.
  rewrite (KMState.ret_pc_even 0x975fc ltac:(lia) eq_refl) in Hc2.
  (* [comment removed for export] *)
  set (Wbs := [(c_E cx + 48, c_E cx + 52); (c_A1 cx, c_A1 cx + ARR1_SIZE); (c_A2 cx, c_A2 cx + ARR2_SIZE); (c_FT cx, c_FT cx + 262148)]).
  assert (WCL : forall x, ~ outside Wbs x -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp x).
  { intros x Hx. unfold Wbs in Hx. cbn [outside] in Hx.
    assert (C : (c_E cx + 48 <= x < c_E cx + 52) \/ (c_A1 cx <= x < c_A1 cx + ARR1_SIZE) \/ (c_A2 cx <= x < c_A2 cx + ARR2_SIZE) \/ (c_FT cx <= x < c_FT cx + 262148)) by (clear - Hx; lia).
    destruct C as [C|[C|[C|C]]]; right; right; left.
    - exists (c_E cx), 55768. split; [exact LIVE| clear - C; lia].
    - exists (c_A1 cx), ARR1_SIZE. split; [exact LIV1| exact C].
    - exists (c_A2 cx), ARR2_SIZE. split; [exact LIV2| exact C].
    - exists (c_FT cx), 262148. split; [exact LIVF| exact C]. }
  set (SHF := f / 8 + 2147450880). change (shad f) with SHF in WRS, ZSH.
  destruct (act_setup RT AF Σ Σ1 m m2 7 f SHF 8192 1024 lo P usp Wbs eq_refl eq_refl eq_refl eq_refl ART0 ART2 FRS1 LV1 SP1 LOW
              ltac:(unfold RT_STACK; clear - YPl4 LOR YPh YPa; lia) ltac:(clear - YPh; lia) SPT SPA WCL) as (G & SOK & _ & FSEG & FHI & SHR0 & SHR1 & GSELF & GLV).
  destruct (GLV _ _ LIVE) as (GFE & GSE & _). destruct (GLV _ _ LIV1) as (GF1 & GS1 & _). destruct (GLV _ _ LIV2) as (GF2 & GS2 & _). destruct (GLV _ _ LIVF) as (GFF & GSF & _).
  pose proof (GLV _ _ LIV1) as (_ & _ & _ & _ & OF1 & _). pose proof (GLV _ _ LIV2) as (_ & _ & _ & _ & OF2 & _). pose proof (GLV _ _ LIVF) as (_ & _ & _ & _ & OFF & _).
  pose proof (ag_ax G) as AXf.
  clearbody SHF.
  set (Y := AME P ((usp - 544) / 32) f (f + 32) (f + 496) (f + 960) (f + 1424) (f + 2576) (f + 2896) (f + 4048)).
  pose proof (ag_gfr G) as (_ & FR1). unfold SEGTOP_A in FSEG. unfold STACK_WIN in FR1.
  assert (YOK : amenv_ok X Y).
  { unfold amenv_ok, Y, CEILm. cbn [am_P am_qP am_FB am_SLO am_SHI am_SD am_RO am_BD am_CS am_CE me_lo me_sp me_E me_A1 me_A2 me_FT X]. fold usp. fold P.
    repeat split; try reflexivity; clear - YPl4 YPh YPa FSEG FR1 CEQ IE IA1 IA2 IFT; unfold STACK_WIN in *; lia. }
  assert (YSEP : amenv_sep X Y).
  { unfold amenv_sep, apartm, Y. cbn [am_FB me_E me_A1 me_A2 me_FT X]. split; [clear - GFE; lia| split; [clear - GF1; lia| split; [clear - GF2; lia| clear - GFF; lia]]]. }
  assert (YOFF : amenv_offsh X Y).
  { unfold amenv_offsh, Y, SH_LO, SH_HI. cbn [am_FB me_A1 me_A2 me_FT X]. split; [clear - OF1; lia| split; [clear - OF2; lia| split; [clear - OFF; lia| clear - FHI; lia]]]. }
  assert (YSF : amenv_shf Y SHF) by (unfold amenv_shf, Y, SH_LO, SH_HI; cbn [am_FB]; split; [exact AXf| clear - SHR0 SHR1; lia]).
  (* [comment removed for export] *)
  assert (STEP2 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) P [] m1 m2) by exact (pfp_of_pres _ _ _ [] m1 m2 PRES2).
  clear ST1.
  xfer_rt G I STEP2 WM2 m1 m2.
  assert (GFE' : c_E cx + 55768 <= f \/ f + 8192 <= c_E cx) by (clear - GFE; lia).
  assert (GF1' : c_A1 cx + ARR1_SIZE <= f \/ f + 8192 <= c_A1 cx) by (clear - GF1; lia).
  assert (GF2' : c_A2 cx + ARR2_SIZE <= f \/ f + 8192 <= c_A2 cx) by (clear - GF2; lia).
  assert (GFF' : c_FT cx + 262148 <= f \/ f + 8192 <= c_FT cx) by (clear - GFF; lia).
  (* [comment removed for export] *)
  eapply (bs_act RT AF SSH MSET SFREE FSC ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 cx g e lo qE q1 q2 qF qsp qo qq m F fc XOK1 XSEP CX SEP IMG TP QOD QOR QOQ EQOF
            PMc Y SHF (rt_frames RT Σ) (rt_live RT Σ) (rt_sp0 RT Σ) FDO MST YOK YSEP YOFF YSF G CEQ
            ltac:(unfold RT_STACK; cbn [am_P Y]; clear - LOR YPh YPa; lia) ltac:(clear - FRMAX; lia) LIVE LIV1 LIV2 LIVF GFE' GF1' GF2' GFF' GSE GS1 GS2 GSF GSELF m2 Σ1);
    try eassumption.
  - rewrite CR1. clear - CRED. lia.
  - intros c' Σ2 m' z0 z1 z2 g0 g1 g2 g3 g4 g5 g6 g7 z3 z4 z5 z6 F' fc' Hc' FRS2 LV2 SP2 CR2 ART' MI' ST' POST PR'.
    apply Hk. exists Σ2.
    split; [| split; [rewrite LV2, LV1; reflexivity| split; [exact FRS2| split; [exact SP2| rewrite CR1 in CR2; clear - CR2; lia]]]].
    eapply ASTA_conseq; [exact Hc'|]. intros ms <-. exists m', z0, z1, z2, g0, g1, g2, g3, g4, g5, g6, g7, z3, z4, z5, z6, F', fc'.
    split; [reflexivity|]. split; [exact ART'|]. split; [exact MI'|]. split; [exact ST'|].
    split; [exact POST|].
    exact (pres_final RT AF Σ lo P usp Wbs m m1 m2 m' ART0 LOW ltac:(clear - YPl; lia) ltac:(clear - YPh; lia) MU1 PRES2 PR').
Qed.
End BST.
