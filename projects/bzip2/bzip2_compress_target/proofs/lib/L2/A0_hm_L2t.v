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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.L2 Require Import L2Kit L2Act L2Stmt A0_hm_L2 A0_hm_L2f.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzCHuff BzArrD CmpMem CmpHmKit AsanKit AsanCut A0_cmp_hmV A0_cmp_hmP.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCHuffF1.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuffF1.BzCFactsHm.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.
#[local] Notation mem := (word -> option byte).


Section HMT.
Context {BZP : BzParams} {ACEIL__ : ACeil}.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis SMAL : stack_malloc_contract RT 7.
Hypothesis SSH : forall v, In v set_shadow_vals -> set_shadow_contract RT v.
Hypothesis MSET : memset_icontract RT e_asan_memset.
Hypothesis SFREE : stack_free_contract RT 7.

(* [comment removed for export] *)
Theorem hbMakeCodeLengths_cps : hbMakeCodeLengths_contract RT.
Proof.
  intros Σ PMc X m pl nl t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 usp FDO MST XOK TP CEQ LEN FREQ LIV L1 L2 L3 L4 FRMAX CRED ART0 MI0 ST0 LOW LOR SPT HMF.
  intros T c Hc Hk.
  hmenv_open XOK. fold usp in XLOF, XSP, XAL.
  set (P := 32 * ((usp - 224) / 32)).
  assert (PF : he_lo X <= P /\ P + 224 <= usp /\ usp <= P + 240 /\ P mod 16 = 0).
  { subst P. clear - XAL LOR. unfold RT_STACK in LOR. Z.div_mod_to_equations. lia. }
  destruct PF as (YPl & YPh & YPa & SPA).
  destruct (aconsts_of_art RT AF Σ m ART0) as [AC AU].
  (* [comment removed for export] *)
  eapply (l1_realizes RT AF Σ PMc _ T c MST Hc).
  eapply (A0_hm_P1 X P _ XOK YPl YPh YPa ((usp - 224) / 32) m); [reflexivity| exact ST0| exact (kmem_inv_N _ _ MI0)| exact AC| exact AU|].
  intros m1 v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v96 v104 v112 x11 x12 SL GAP SAV ST1 NMI1 MU1 WM1. apply evt_done. intros c1 Hc1.
  assert (MU1k : KFrame.munch [(P, usp)] m m1) by exact MU1.
  assert (ART1 : ART RT Σ m1).
  { apply (art_of_munch RT AF Σ m m1 [(P, usp)] P ART0 ltac:(unfold STACK_WIN, RT_STACK in *; lia) MU1k WM1). per_interval. left. unfold USTACK_TOP in *. lia. }
  assert (MI1 : KMem.mem_inv asegs m1).
  { apply (kmem_inv_munch' asegs [(P, usp)] m m1 MI0 MU1k NMI1). intros x Hx. revert Hx. refine (not_outside_cons _ _ _ _ _ _ _); [intro| refine (not_outside_nil _ _)].
    unfold KMem.UTOP, USTACK_TOP in *. lia. }
  xfer_l1 m m1 MU1 WM1.
  (* [comment removed for export] *)
  refine (cps_realizes asegs _ _ T c1 _ Hc1 _).
  { eapply (SMAL Σ PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (he_F X) (he_fc X) m1 5600 (he_lo X) FDO MST
              ltac:(right; right; right; right; reflexivity) TP).
    - reflexivity.
    - change (fs_size 7) with 8192. lia.
    - reflexivity.
    - exact FRMAX.
    - exact CRED.
    - exact ART1.
    - exact MI1.
    - unfold call_ok. rewrite unsigned_lit by lia. unfold STACK_WIN, USTACK_TOP, RT_STACK in *. split; [exact ST1|]. split; [lia|]. split; [lia|]. split; [lia| exact SPA]. }
  intros c2 (Σ1 & f & Hq2 & FRS1 & LV1 & SP1 & CR1 & FPOS & F64 & FTOP). change (fs_size 7) with 8192 in *.
  destruct (ASTA_unpack RT Σ1 _ _ c2 Hq2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & WRF & WRS & ZSH) & Hc2). clear Hq2.
  destruct RS2 as (u0 & u1 & u2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->).
  rewrite unsigned_lit in ST2, PRES2 by lia. change (8192 - 8) with 8184 in WRF. change (8192 / 8) with 1024 in WRS.
  rewrite (KMState.ret_pc_even 0x9d148 ltac:(lia) eq_refl) in Hc2.
  (* [comment removed for export] *)
  set (Wlen := [(he_El X + he_lb X, he_El X + he_lb X + he_A X)]).
  assert (WCL : forall x, ~ outside Wlen x -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp x).
  { intros x Hx. right; right; left. exists pl, nl. split; [exact LIV|]. unfold Wlen in Hx. cbn [outside] in Hx. lia. }
  set (SHF := f / 8 + 2147450880). change (shad f) with SHF in WRS, ZSH.
  destruct (act_setup RT AF Σ Σ1 m m2 7 f SHF 8192 1024 (he_lo X) P usp Wlen eq_refl eq_refl eq_refl eq_refl ART0 ART2 FRS1 LV1 SP1 LOW
              ltac:(unfold RT_STACK in *; lia) ltac:(lia) SPT SPA WCL) as (G & SOK & _ & FSEG & FHI & SHR0 & SHR1 & GSELF & GLV).
  destruct (GLV pl nl LIV) as (GLIVF & GLIVS & PL0 & PL1 & LHI & _).
  pose proof (ag_ax G) as AXf.
  clearbody SHF.
  set (Y := AHE P f SHF (f + 32) (f + 1200) (f + 3392)).
  pose proof (ag_gfr G) as (_ & FR1).
  pose proof alloc_ceiling_range as ACR. unfold SEGTOP_A in FSEG.
  assert (YOK : ahenv_ok X Y).
  { unfold ahenv_ok, Y, CEILh, SH_LO, SH_HI. cbn [ah_P ah_FB ah_SHF ah_HP ah_WT ah_PR]. fold usp. repeat split; try reflexivity; lia. }
  assert (YSEP : ahenv_sep X Y).
  { unfold ahenv_sep, Y. cbn [ah_FB]. destruct GLIVF; split; lia. }
  assert (YOFF : ahenv_offsh X Y).
  { unfold ahenv_offsh, Y, SH_LO, SH_HI. cbn [ah_FB]. repeat split; lia. }
  pose proof (ahenv_sepx_of X Y XOK YOK YSEP) as YSX.
  (* [comment removed for export] *)
  assert (STEP2 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) P [] m1 m2) by exact (pfp_of_pres _ _ _ [] m1 m2 PRES2).
  pose proof (ck_intro P CStack) as KP. pose proof (ck_intro (bv_unsigned (he_sp X)) CStack) as KU.
  pose proof (ck_intro (he_El X) (CLive pl nl)) as KEl. pose proof (ck_intro (he_Ef X) (CLive pl nl)) as KEf.
  clear ST1.
  (* [comment removed for export] *)
  xfer_rt G I STEP2 WM2 m1 m2.
  (* [comment removed for export] *)
  eapply (hm_act_pro RT AF SSH X XOK Σ1 PMc Y (rt_frames RT Σ) (rt_live RT Σ) (rt_sp0 RT Σ) pl nl FDO MST YOK YSX AXf YOFF G SOK LIV L1 L2 L3 L4 GSELF GLIVF GLIVS m2);
    try eassumption.
  intros c11 m11 w0 w1 w2 r0 d1 d2 d3 d4 d5 d6 d7 w3 w4 w5 w6 F11 fc11 Hc11 ART11 MI11 ST11 WRF11 WRS11 PR11 SL11 HD11 GAP11 SAV11 LEN11 FREQ11 SHH SHW SHP.
  eapply (hm_act_body RT AF SSH MSET SFREE X XOK Σ1 PMc Y (rt_frames RT Σ) (rt_live RT Σ) (rt_sp0 RT Σ) pl nl FDO MST YOK YSX AXf YOFF G SOK LIV L1 L2 L3 L4 GSELF GLIVF GLIVS m2);
    try eassumption.
  intros c' Σ2 m' q0 q1 q2 g0 g1 g2 g3 g4 g5 g6 g7 q3 q4 q5 q6 F' fc' Hc' FRS2 LV2 SP2 CR2 ART' MI' ST' LEN' PR'.
  apply Hk. exists Σ2.
  split; [| split; [rewrite LV2, LV1; reflexivity| split; [exact FRS2| split; [exact SP2| rewrite CR2, CR1; reflexivity]]]].
  eapply ASTA_conseq; [exact Hc'|]. intros ms <-. exists m', q0, q1, q2, g0, g1, g2, g3, g4, g5, g6, g7, q3, q4, q5, q6, F', fc'.
  split; [reflexivity|]. split; [exact ART'|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact LEN'|].
  exact (pres_final RT AF Σ (he_lo X) P usp Wlen m m1 m2 m' ART0 LOW ltac:(lia) ltac:(lia) MU1 PRES2 PR').
Qed.
End HMT.
