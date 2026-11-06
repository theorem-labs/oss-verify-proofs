(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import ShapeAlg.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import ImageA RzCPS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Layout RT_iface D_defs D_kit I_read.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.L2 Require Import L2Kit L2Act L2Stmt A0_fs_L2f.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzArr BzCMem BzCState BzCSortF BzArrD CmpMem CmpCut BzCLemmasFs BzCFactsFs BzCFactsFs2 CmpFsKit0 AsanKit AsanKit2 AsanCut.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpCut6.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_fsV A0_cmp_fsS A0_cmp_fsP A0_cmp_fsQ A0_cmp_fsZ.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.
#[local] Notation mem := (word -> option byte).
Strategy 1000 [fs_ftab_zero fs_count fs_copy fs_accum fs_distrib fs_bh_zero fs_bh_init fs_sentinel fs_eclass fs_H_loop fs_H_iter
               fs_bucket_loop fs_bucket_iter fs_headers fs_skip0 fs_rebuild fqs_loop fallbackQSort3 fallbackSort].

Lemma mod16_linq : forall x, x mod 16 = 0 -> exists q, x = 16 * q.
Proof. intros x H. exists (x / 16). Z.div_mod_to_equations. lia. Qed.

Section FST.
Context {BZP : BzParams} {ACEIL__ : ACeil}.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis SMAL : stack_malloc_contract RT 6.
Hypothesis SSH : forall v, In v set_shadow_vals -> set_shadow_contract RT v.
Hypothesis MSET : memset_icontract RT e_asan_memset.
Hypothesis MCPY : memcpy_icontract RT e_asan_memcpy.
Hypothesis SFREE : stack_free_contract RT 6.
Hypothesis AF_DRV : forall Σ m, ART RT Σ m -> drv_consts m.

Theorem fallbackSort_cps : fallbackSort_contract RT fs_facts.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m cx e nblock lo usp W
    FDO MST Ha0 Ha1 Ha2 Ha3 Ha4 TP CEQ AR1 AR2 FTB LIV1 LIV2 LIVF FRMAX CRED ART0 MI0 ST0 LOW LOR SPT AL CX SEP IMG FMOK ECOK FTW NB FACTS.
  subst a0 a1 a2 a3 a4.
  intros T c Hc Hk.
  pose proof CX as CX'. unfold cctx_ok in CX'. cbv zeta in CX'.
  destruct CX' as (_ & _ & RA1 & RA1' & RA2 & RA2' & RFT & RFT' & _ & _ & _ & _ & _ & MA1 & MA2 & MFT & _).
  pose proof SEP as SEP'. unfold cctx_sep, apart in SEP'. cbv zeta in SEP'.
  destruct SEP' as (_ & _ & _ & _ & _ & AP12 & AP1F & _ & _ & AP2F & _).
  pose proof IMG as IMG'. unfold cctx_img, img_apart, IMG_LO3 in IMG'. cbn [ci_hi aci_c A0C] in IMG'. destruct IMG' as (_ & IA1 & IA2 & IFT & _).
  pose proof alloc_ceiling_range as ACR. bz_params. unfold FTAB_WORDS, CEIL in *.
  change (4 * 65537) with 262148 in *.
  destruct IA1 as [IA1|IA1]; [exfalso; clear - IA1 RA1 BZbsL__; lia|]. destruct IA2 as [IA2|IA2]; [exfalso; clear - IA2 RA2 BZbsL__; lia|].
  destruct IFT as [IFT|IFT]; [exfalso; clear - IFT RFT; lia|].
  destruct (mod16_linq _ AL) as [qsp ALQ]. destruct (mod16_linq _ MA1) as [q1 AQ1]. destruct (mod16_linq _ MA2) as [q2 AQ2]. destruct (mod16_linq _ MFT) as [qF AQF].
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR. fold usp in SPR.
  unfold RT_STACK in LOR.
  set (X := FE ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (c_A1 cx) (c_A2 cx) (c_FT cx) nblock lo q1 q2 qF qsp
               (e_arr1 e) (e_arr2 e) (e_ftab e) (Z_to_bv 64 0) m).
  assert (BW0 : bh_w32 (e_ftab e)) by (intros i; apply FTW).
  assert (XOK : fsenv_ok X).
  { unfold fsenv_ok, CEILv. cbn [fe_A1 fe_A2 fe_FT fe_lo fe_sp fe_nb fe_q1 fe_q2 fe_qF fe_qsp fe_fm fe_ec fe_bh X]. fold usp.
    repeat (split; [first [assumption| clear - IA1 IA2 IFT RA1' RA2' RFT' CEQ LOW LOR SPR NB; lia]|]). exact BW0. }
  assert (XSEP : fsenv_sep X) by (unfold fsenv_sep, apartv; cbn [fe_A1 fe_A2 fe_FT X]; split; [exact AP12| split; [exact AP1F| exact AP2F]]).
  set (P := 32 * ((usp - 1376) / 32)).
  assert (PF : lo <= P /\ P + 1376 <= usp /\ usp <= P + 1392 /\ P mod 16 = 0).
  { subst P. clear - ALQ LOR. Z.div_mod_to_equations. lia. }
  destruct PF as (YPl & YPh & YPa & SPA).
  destruct (fs_aconsts_of_art RT AF Σ m ART0) as [AC AU].
  (* [comment removed for export] *)
  eapply (l1_realizes RT AF Σ PMc _ T c MST Hc).
  eapply (A0_fs_P1 X P _ XOK YPl YPh YPa ((usp - 1376) / 32) m); [reflexivity| exact ST0| exact (kmem_inv_N _ _ MI0)| exact AC| exact AU|].
  intros m1 v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v104 v112 v120 v128 v136 v144 v152 v160 v168 v176 v184 v192 v200 v208 v216 v224 v232 j4 jft x11 x12
    SLa SLb SLc FTJ GAP SAV ST1 NMI1 MU1 WM1. apply evt_done. intros c1 Hc1.
  cbn [X fe_sp fe_lo] in SLa, SLb, SLc, FTJ, GAP, SAV, ST1, MU1. fold usp in GAP, SAV, ST1, MU1.
  assert (MU1k : KFrame.munch [(P, usp)] m m1) by exact MU1.
  assert (ART1 : ART RT Σ m1).
  { apply (art_of_munch RT AF Σ m m1 [(P, usp)] P ART0 ltac:(clear - LOW YPl; lia) MU1k WM1). per_interval. left. unfold USTACK_TOP in *. match goal with HX : _ <= _ < _ |- _ => clear - SPT HX YPl; lia end. }
  assert (MI1 : KMem.mem_inv asegs m1).
  { apply (kmem_inv_munch' asegs [(P, usp)] m m1 MI0 MU1k NMI1). intros x Hx. revert Hx. refine (not_outside_cons _ _ _ _ _ _ _); [intro| refine (not_outside_nil _ _)].
    unfold KMem.UTOP, USTACK_TOP in *. match goal with HX : _ <= _ < _ |- _ => clear - SPT HX; lia end. }
  pose proof (ck_intro P CStack) as KP. pose proof (ck_intro usp CStack) as KU.
  pose proof (ck_intro (c_A1 cx) (CLive (c_A1 cx) ARR1_SIZE)) as KA1. pose proof (ck_intro (c_A2 cx) (CLive (c_A2 cx) ARR2_SIZE)) as KA2.
  pose proof (ck_intro (c_FT cx) (CLive (c_FT cx) 262148)) as KFT.
  assert (BLW : c_A1 cx + ARR1_SIZE <= P /\ c_A2 cx + ARR2_SIZE <= P /\ c_FT cx + 262148 <= P) by (clear - RA1' RA2' RFT' CEQ LOW YPl; lia).
  destruct BLW as (BL1 & BL2 & BLF).
  xfer_l1 m m1 MU1 WM1.
  (* [comment removed for export] *)
  refine (cps_realizes asegs _ _ T c1 _ Hc1 _).
  { eapply (SMAL Σ PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 2112 lo FDO MST
              ltac:(right; right; right; left; reflexivity) TP).
    - reflexivity.
    - change (fs_size 6) with 4096. lia.
    - reflexivity.
    - exact FRMAX.
    - exact CRED.
    - exact ART1.
    - exact MI1.
    - unfold call_ok. rewrite unsigned_lit by (clear - YPl YPh SPR LOW ACR CEQ; lia). unfold STACK_WIN, USTACK_TOP, RT_STACK in *.
      split; [exact ST1|]. split; [exact LOW|]. split; [clear - YPl LOR YPh YPa; lia|]. split; [clear - SPT YPh; lia| exact SPA]. }
  intros c2 (Σ1 & f & Hq2 & FRS1 & LV1 & SP1 & CR1 & FPOS & F64 & FTOP). change (fs_size 6) with 4096 in *.
  destruct (ASTA_unpack RT Σ1 _ _ c2 Hq2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & WRF & WRS & ZSH) & Hc2). clear Hq2.
  destruct RS2 as (u0 & u1 & u2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->).
  rewrite unsigned_lit in ST2, PRES2 by (clear - YPl YPh SPR LOW ACR CEQ; lia). change (4096 - 8) with 4088 in WRF. change (4096 / 8) with 512 in WRS.
  rewrite (KMState.ret_pc_even 0x9aab4 ltac:(lia) eq_refl) in Hc2.
  (* [comment removed for export] *)
  set (Wfs := [(c_A1 cx, c_A1 cx + ARR1_SIZE); (c_A2 cx, c_A2 cx + ARR2_SIZE); (c_FT cx, c_FT cx + 262148)]).
  assert (WCL : forall x, ~ outside Wfs x -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp x).
  { intros x Hx. unfold Wfs in Hx. cbn [outside] in Hx.
    assert (C : (c_A1 cx <= x < c_A1 cx + ARR1_SIZE) \/ (c_A2 cx <= x < c_A2 cx + ARR2_SIZE) \/ (c_FT cx <= x < c_FT cx + 262148)) by (clear - Hx; lia).
    destruct C as [C|[C|C]]; right; right; left.
    - exists (c_A1 cx), ARR1_SIZE. split; [exact LIV1| exact C].
    - exists (c_A2 cx), ARR2_SIZE. split; [exact LIV2| exact C].
    - exists (c_FT cx), 262148. split; [exact LIVF| exact C]. }
  set (SHF := f / 8 + 2147450880). change (shad f) with SHF in WRS, ZSH.
  destruct (act_setup RT AF Σ Σ1 m m2 6 f SHF 4096 512 lo P usp Wfs eq_refl eq_refl eq_refl eq_refl ART0 ART2 FRS1 LV1 SP1 LOW
              ltac:(unfold RT_STACK; clear - YPl LOR YPh YPa; lia) ltac:(clear - YPh; lia) SPT SPA WCL) as (G & SOK & _ & FSEG & FHI & SHR0 & SHR1 & GSELF & GLV).
  destruct (GLV _ _ LIV1) as (GF1 & GS1 & _). destruct (GLV _ _ LIV2) as (GF2 & GS2 & _). destruct (GLV _ _ LIVF) as (GFF & GSF & _).
  pose proof (GLV _ _ LIV1) as (_ & _ & _ & _ & OF1 & _). pose proof (GLV _ _ LIV2) as (_ & _ & _ & _ & OF2 & _). pose proof (GLV _ _ LIVF) as (_ & _ & _ & _ & OFF & _).
  pose proof (ag_ax G) as AXf.
  clearbody SHF.
  set (Y := AFE P f SHF (f + 32) (f + 496) (f + 960)).
  pose proof (ag_gfr G) as (_ & FR1). unfold SEGTOP_A in FSEG. unfold STACK_WIN in FR1.
  assert (YOK : afenv_ok X Y).
  { unfold afenv_ok, Y, CEILv, SH_LO, SH_HI. cbn [ae_P ae_FB ae_SHF ae_SLO ae_SHI ae_FCP fe_lo fe_sp X]. fold usp.
    repeat split; try reflexivity; clear - YPl YPh FSEG FR1 CEQ SHR0 SHR1; unfold STACK_WIN in *; lia. }
  assert (YSEP : afenv_sep X Y).
  { unfold afenv_sep, apartv, Y. cbn [ae_FB fe_A1 fe_A2 fe_FT X]. split; [clear - GF1; lia| split; [clear - GF2; lia| clear - GFF; lia]]. }
  assert (YOFF : afenv_offsh X Y).
  { unfold afenv_offsh, Y, SH_LO, SH_HI. cbn [ae_FB fe_A1 fe_A2 fe_FT X]. split; [clear - OF1; lia| split; [clear - OF2; lia| split; [clear - OFF; lia| clear - FHI; lia]]]. }
  (* [comment removed for export] *)
  assert (STEP2 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) P [] m1 m2) by exact (pfp_of_pres _ _ _ [] m1 m2 PRES2).
  clear ST1.
  xfer_rt G I STEP2 WM2 m1 m2.
  (* [comment removed for export] *)
  eapply (fs_act RT AF SSH MSET MCPY SFREE AF_DRV X XOK XSEP Σ1 PMc Y (rt_frames RT Σ) (rt_live RT Σ) (rt_sp0 RT Σ) FDO MST YOK YSEP YOFF AXf G SOK LIV1 LIV2 LIVF IFT
            GS1 GS2 GSF GSELF m2); try eassumption.
  intros c' Σ2 m' z0 z1 z2 g0 g1 g2 g3 g4 g5 g6 g7 z3 z4 z5 z6 F' fc' Hc' FRS2 LV2 SP2 CR2 ART' MI' ST' AR1' AR2' FTB' PR'.
  apply Hk. exists Σ2.
  split; [| split; [rewrite LV2, LV1; reflexivity| split; [exact FRS2| split; [exact SP2| rewrite CR2, CR1; reflexivity]]]].
  eapply ASTA_conseq; [exact Hc'|]. intros ms <-. exists m', z0, z1, z2, g0, g1, g2, g3, g4, g5, g6, g7, z3, z4, z5, z6, F', fc'.
  split; [reflexivity|]. split; [exact ART'|]. split; [exact MI'|]. split; [exact ST'|].
  split.
  { cbv zeta. rewrite fallbackSort_eq. cbv zeta. cbn [fr_fm fr_ec fr_bh]. split; [exact AR1'| split; [exact AR2'| exact FTB']]. }
  exact (pres_final RT AF Σ lo P usp Wfs m m1 m2 m' ART0 LOW ltac:(clear - YPl; lia) ltac:(clear - YPh; lia) MU1 PRES2 PR').
Qed.
End FST.
