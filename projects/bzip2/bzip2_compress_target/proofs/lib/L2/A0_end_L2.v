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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.L2 Require Import L2Kit L2Act L2Stmt L2StmtS A0_sessK.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzCStream BzCState BzCBlock BzCDriver BzArrD CmpMem CmpCut CmpSess CmpSess2 CmpSessB CmpFsKit0 AsanKit AsanCut A0_cmp_cbV A0_b2c_hcV A0_b2c_wrV A0_b2c_wrE A0_b2c_wrI.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpCut6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.
#[local] Notation mem := (word -> option byte).


Section ENDL2.
Context {BZP : BzParams} {ACEIL__ : ACeil}.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis FRE : free_contract RT.

Theorem bzCompressEnd_cps : bzCompressEnd_contract RT.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m cx ob on dbza g e z nin p1 p2 lo usp STRM W
         FDO MST A0E TP CEQ EH1 SM SOKA ELIV A1LIV A2LIV FTLIV ART0 MI0 ST0 LOW LOR SPT SPA CX SEP.
  intros T c Hc Hk. subst a0.
  set (P := usp - 64). assert (PE : P = usp - 64) by reflexivity.
  (* [comment removed for export] *)
  pose proof CX as CX'. unfold cctx_ok in CX'. cbv zeta in CX'.
  destruct CX' as (RE & RE' & RA1 & RA1' & RA2 & RA2' & RFT & RFT' & _ & _ & _ & _ & ME16 & MA1 & MA2 & MFT & _).
  pose proof SEP as SEP'. unfold cctx_sep, apart in SEP'. cbv zeta in SEP'. destruct SEP' as (SE1 & SE2 & SEF & _ & _ & S12 & S1F & _ & _ & S2F & _).
  pose proof alloc_ceiling_range as ACR. bz_params.
  unfold FTAB_WORDS, ESTATE_SIZE, CEIL in *. change (4 * 65537) with 262148 in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR. fold usp in SPR.
  pose proof LOR as LOR'. unfold RT_STACK in LOR'.
  assert (NE12 : c_A2 cx <> c_A1 cx) by (clear - S12 BZbsL__; lia). assert (NE1F : c_FT cx <> c_A1 cx) by (clear - S1F BZbsL__; lia).
  assert (NE1E : c_E cx <> c_A1 cx) by (clear - SE1 BZbsL__; lia). assert (NE2F : c_FT cx <> c_A2 cx) by (clear - S2F BZbsL__; lia).
  assert (NE2E : c_E cx <> c_A2 cx) by (clear - SE2 BZbsL__; lia). assert (NEFE : c_E cx <> c_FT cx) by (clear - SEF; lia).
  (* [comment removed for export] *)
  destruct SOKA as ((fS & kS & FIN & FLO & FHI) & S8 & ZSH).
  pose proof (af_frames_range RT AF Σ m fS kS ART0 FIN) as (FS0 & FS1 & _ & FSL).
  pose proof (af_frames_align RT AF Σ m fS kS ART0 FIN) as (_ & FSEG). unfold SEGTOP_A in FSEG.
  pose proof (af_frames_hi RT AF Σ m fS kS ART0 FIN) as FSHI.
  assert (SLO : 0x61e000 <= STRM) by (clear - FSEG FLO; lia).
  assert (SHI : STRM + 80 <= CEILv) by (unfold CEILv; clear - FS1 FHI CEQ; lia).
  assert (SES : apartv (c_E cx) ESTATE_SIZE STRM 80) by (unfold apartv, ESTATE_SIZE; destruct (FSL _ _ ELIV) as [D|D]; clear - D FLO FHI; lia).
  assert (LLO : CEILv <= lo) by (unfold CEILv; clear - CEQ LOW; lia).
  set (SHE := c_E cx / 8 + 2147450880). set (SHS := STRM / 8 + 2147450880).
  assert (AE : sanchor (c_E cx) SHE) by (apply sanchor_intro; clear - ME16; Z.div_mod_to_equations; lia).
  assert (AS : sanchor STRM SHS) by (apply sanchor_intro; exact S8).
  clearbody SHE SHS.
  (* [comment removed for export] *)
  set (L0 := live_remove (c_E cx) (live_remove (c_FT cx) (live_remove (c_A2 cx) (live_remove (c_A1 cx) (rt_live RT Σ))))).
  assert (L0SUB : forall e0, In e0 L0 -> In e0 (rt_live RT Σ)).
  { intros e0 H. apply live_remove_in in H as [H _]. apply live_remove_in in H as [H _]. apply live_remove_in in H as [H _]. apply live_remove_in in H as [H _]. exact H. }
  assert (L0NE : forall e0, In e0 L0 -> fst e0 <> c_E cx).
  { intros e0 H. apply live_remove_in in H as [_ H]. exact H. }
  assert (L0NF : forall e0, In e0 L0 -> fst e0 <> c_FT cx).
  { intros e0 H. apply live_remove_in in H as [H _]. apply live_remove_in in H as [_ H]. exact H. }
  assert (L0N2 : forall e0, In e0 L0 -> fst e0 <> c_A2 cx).
  { intros e0 H. apply live_remove_in in H as [H _]. apply live_remove_in in H as [H _]. apply live_remove_in in H as [_ H]. exact H. }
  assert (L0N1 : forall e0, In e0 L0 -> fst e0 <> c_A1 cx).
  { intros e0 H. apply live_remove_in in H as [H _]. apply live_remove_in in H as [H _]. apply live_remove_in in H as [H _]. apply live_remove_in in H as [_ H]. exact H. }
  assert (L0IN : forall e0, In e0 (rt_live RT Σ) -> fst e0 <> c_A1 cx -> fst e0 <> c_A2 cx -> fst e0 <> c_FT cx -> fst e0 <> c_E cx -> In e0 L0).
  { intros e0 H N1 N2 NF NE. unfold L0. apply live_remove_keep; [| exact NE]. apply live_remove_keep; [| exact NF]. apply live_remove_keep; [| exact N2]. apply live_remove_keep; [exact H| exact N1]. }
  clearbody L0.
  set (Wc := [(STRM + 48, STRM + 56)]).
  assert (SCL : forall x, STRM <= x < STRM + 80 -> aclient L0 (rt_frames RT Σ) usp x).
  { intros x Hx. right; right; right; left. exists fS, kS. split; [exact FIN| clear - Hx FLO FHI; lia]. }
  assert (WCL0 : forall x, ~ outside Wc x -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp x).
  { intros x Hx. unfold Wc in Hx. cbn [outside] in Hx. right; right; right; left. exists fS, kS. split; [exact FIN| clear - Hx FLO FHI; lia]. }
  destruct (act_setup_nf RT AF Σ m lo P usp Wc ART0 LOW ltac:(clear - PE LOR'; unfold RT_STACK; lia) ltac:(clear - PE; lia) SPT
              ltac:(clear - PE SPA; Z.div_mod_to_equations; lia) WCL0) as (G0 & SOK0).
  assert (G : act_geom RT lo P usp (rt_sp0 RT Σ) false 0 8 2147450881 0 0 (rt_frames RT Σ) L0 Wc).
  { apply (act_geom_sub _ _ _ _ _ _ _ _ _ _ _ _ _ L0 _ Wc G0 L0SUB). intros x Hx. apply SCL. unfold Wc in Hx. cbn [outside] in Hx. clear - Hx. lia. }
  pose proof (sig_ok_sub _ _ _ _ _ _ _ L0 _ SOK0 L0SUB) as SOK. clear G0 SOK0 WCL0.
  (* [comment removed for export] *)
  destruct (af_acc_live RT AF Σ m _ _ ART0 ELIV) as [_ ACCE].
  pose proof (af_live_offshadow RT AF Σ m _ _ ART0 ELIV) as EOFF.
  assert (ZSHn : bytes_at a0segs m SHS (repeat z8 10)) by (destruct AS as [_ ->]; exact ZSH).
  assert (ACCS : acc asegs m STRM 80).
  { pose proof (acc_of_zero_shadow asegs m STRM SHS 0 10 S8 (proj2 AS) ltac:(clear - SLO; lia) ltac:(clear; lia)) as A.
    replace (STRM + 8 * 0) with STRM in A by (clear; lia). change (8 * Z.of_nat 10) with 80 in A. apply A.
    replace (SHS + 0) with SHS by (clear; lia). exact ZSHn. }
  assert (AFW : app_fp [(P, P + 64)]).
  { cbn [app_fp]. unfold SH_LO, SH_HI. split; [right; clear - PE LOW LOR' CEQ ACR; lia| exact I]. }
  assert (SHe : shzW a0segs [(P, P + 64)] m (c_E cx) (c_E cx + ESTATE_SIZE)).
  { unfold ESTATE_SIZE. apply (shzW_of_acc a0segs _ m (c_E cx) 55768 _ _ ACCE AFW); [clear - RE; lia| clear - RE' ACR; lia| clear; lia| clear - ME16; Z.div_mod_to_equations; lia]. }
  assert (SHs : shzW a0segs [(P, P + 64)] m STRM (STRM + 80)).
  { apply (shzW_of_acc a0segs _ m STRM 80 _ _ ACCS AFW); [clear - SLO; lia| clear - SHI ACR; unfold CEILv in SHI; lia| clear; lia| clear - S8; Z.div_mod_to_equations; lia]. }
  destruct (af_client_consts RT AF Σ m ART0) as (G1 & G2 & _ & _).
  assert (AC : aconsts A0C m) by (split; [exact (ro_C8_KN m _ _ G1)| exact (ro_C8_KN m _ _ G2)]). clear G1 G2.
  eapply (l1_realizes RT AF Σ PMc _ T c MST Hc).
  eapply (A0_end_X1 cx _ SHE SHS ob on dbza p1 p2 P STRM lo gp tp F fc eq_refl CX AE AS SLO SHI LLO ltac:(clear - PE LOR'; lia) g e z nin m ra sp);
    [reflexivity| exact ST0| exact EH1| exact SM| exact (kmem_inv_N _ _ MI0)| exact AC| exact SHe| exact SHs|].
  clear Hc EH1 SM SHe SHs AC.
  intros m1 a3' SAV ST1n EH1 SM NMI1 MU1 WM1. apply evt_done. intros c1 Hc1.
  unfold end_W in MU1.
  destruct (stk_split a0segs m lo P usp ST0 ltac:(clear - PE LOR'; lia)) as [ST0P _].
  destruct (after_l1 AF G Σ _ m m1 SOK ART0 MI0 ST0P (presi_refl _ _ _ _ m) NMI1 MU1 WM1 ltac:(per_interval; unfold P; lia)) as (ART1 & MI1 & ST1 & PR1 & _).
  (* [comment removed for export] *)
  assert (SHSR : shad fS <= SHS /\ SHS + 10 <= shad (fS + fs_size kS)).
  { destruct AS as [_ ->]. unfold shad, SHB. clear - FLO FHI. Z.div_mod_to_equations. lia. }
  assert (SHCL : forall x, SHS <= x < SHS + 10 -> aclient L0 (rt_frames RT Σ) usp x).
  { intros x Hx. right; right; right; right. exists fS, kS. split; [exact FIN| clear - Hx SHSR; lia]. }
  assert (SHSH : SHS + 10 <= 17594333495296) by (destruct AS as [_ ->]; unfold CEILv in SHI; clear - SHI ACR; Z.div_mod_to_equations; lia).
  unfold CEILv in SHI, LLO.
  pose proof (ck_intro P CStack) as KP. pose proof (ck_intro usp CStack) as KU. pose proof (ck_intro (c_E cx) (CLive (c_E cx) 55768)) as KE.
  pose proof (ck_intro STRM CCaller) as KS. pose proof (ck_intro SHS CCaller) as KSH.
  clear ST0 ST0P ZSH ACCE ACCS EOFF AFW FSL.
  xfer_l1 m m1 MU1 WM1. clear NMI1 MU1 WM1 ST1n.
  assert (S0R : 0 <= STRM + 48 < P /\ P < 2^64) by (clear - SLO SHI LLO PE LOR' SPR; lia).
  (* [comment removed for export] *)
  eapply (free_call G PMc FDO MST Σ (c_A1 cx) ARR1_SIZE m1); [exact FRE| exact SOK| exact A1LIV| exact L0N1| exact TP| exact ART1| exact MI1| exact ST1| exact PR1| | exact Hc1|];
    [apply unwind_site1; [apply in_alloc_ras; reflexivity| exact (proj1 S0R)| exact (proj2 S0R)]|].
  clear Hc1. intros c2 Σ2 m2 u0 u1 u2 v0 e1 e2 e3 e4 e5 e6 e7 u3 u4 u5 u6 F2 fc2 Hc2 SOK2 LV2 FR2 CR2 ART2 MI2 ST2 PR2 STEP2.
  rewrite (KMState.ret_pc_even 0x83d4c ltac:(lia) eq_refl) in Hc2.
  assert (ELIV2 : In (c_E cx, 55768) (rt_live RT Σ2)) by (rewrite LV2; apply live_remove_keep; [exact ELIV| exact NE1E]).
  assert (A2LIV2 : In (c_A2 cx, ARR2_SIZE) (rt_live RT Σ2)) by (rewrite LV2; apply live_remove_keep; [exact A2LIV| exact NE12]).
  assert (FTLIV2 : In (c_FT cx, 262148) (rt_live RT Σ2)) by (rewrite LV2; apply live_remove_keep; [exact FTLIV| exact NE1F]).
  clear ST1. xfer_rtf G SOK2 STEP2 m1 m2.
  (* [comment removed for export] *)
  assert (S47 : 0 <= STRM /\ STRM + 80 <= 2^47) by (clear - SLO SHI ACR; lia).
  eapply (l1_realizes RT AF Σ2 PMc _ T c2 MST Hc2).
  eapply (A0_end_X2 cx _ SHS ob on dbza p1 p2 P STRM gp tp F2 fc2 eq_refl CX SLO SHI g e z nin m2);
    [exact EH1| exact SM| exact (live_reader RT AF Σ2 m2 _ _ [] ART2 ELIV2 ltac:(clear - ME16; Z.div_mod_to_equations; lia) eq_refl I)
     | exact (strm_reader m2 STRM SHS [] AS (proj1 S47) (proj2 S47) ZSHn I)|].
  apply evt_done. clear Hc2. intros c3 Hc3.
  eapply (free_call G PMc FDO MST Σ2 (c_A2 cx) ARR2_SIZE m2); [exact FRE| exact SOK2| exact A2LIV2| exact L0N2| exact TP| exact ART2| exact MI2| exact ST2| exact PR2| | exact Hc3|];
    [apply unwind_site1; [apply in_alloc_ras; reflexivity| exact (proj1 S0R)| exact (proj2 S0R)]|].
  clear Hc3. intros c4 Σ3 m3 x0 x1 x2 y0 f1 f2 f3 f4 f5 f6 f7 x3 x4 x5 x6 F3 fc3 Hc4 SOK3 LV3 FR3 CR3 ART3 MI3 ST3 PR3 STEP3.
  rewrite (KMState.ret_pc_even 0x83d94 ltac:(lia) eq_refl) in Hc4.
  assert (ELIV3 : In (c_E cx, 55768) (rt_live RT Σ3)) by (rewrite LV3; apply live_remove_keep; [exact ELIV2| exact NE2E]).
  assert (FTLIV3 : In (c_FT cx, 262148) (rt_live RT Σ3)) by (rewrite LV3; apply live_remove_keep; [exact FTLIV2| exact NE2F]).
  clear ST2. xfer_rtf G SOK3 STEP3 m2 m3.
  (* [comment removed for export] *)
  eapply (l1_realizes RT AF Σ3 PMc _ T c4 MST Hc4).
  eapply (A0_end_X3 cx _ SHS ob on dbza p1 p2 P STRM gp tp F3 fc3 eq_refl CX SLO SHI g e z nin m3);
    [exact EH1| exact SM| exact (live_reader RT AF Σ3 m3 _ _ [] ART3 ELIV3 ltac:(clear - ME16; Z.div_mod_to_equations; lia) eq_refl I)
     | exact (strm_reader m3 STRM SHS [] AS (proj1 S47) (proj2 S47) ZSHn I)|].
  apply evt_done. clear Hc4. intros c5 Hc5.
  eapply (free_call G PMc FDO MST Σ3 (c_FT cx) 262148 m3); [exact FRE| exact SOK3| exact FTLIV3| exact L0NF| exact TP| exact ART3| exact MI3| exact ST3| exact PR3| | exact Hc5|];
    [apply unwind_site1; [apply in_alloc_ras; reflexivity| exact (proj1 S0R)| exact (proj2 S0R)]|].
  clear Hc5. intros c6 Σ4 m4 z0 z1 z2 yy0 h1 h2 h3 h4 h5 h6 h7 z3 z4 z5 z6 F4 fc4 Hc6 SOK4 LV4 FR4 CR4 ART4 MI4 ST4 PR4 STEP4.
  rewrite (KMState.ret_pc_even 0x83ddc ltac:(lia) eq_refl) in Hc6.
  assert (ELIV4 : In (c_E cx, 55768) (rt_live RT Σ4)) by (rewrite LV4; apply live_remove_keep; [exact ELIV3| exact NEFE]).
  clear ST3. xfer_rtf G SOK4 STEP4 m3 m4.
  (* [comment removed for export] *)
  eapply (l1_realizes RT AF Σ4 PMc _ T c6 MST Hc6).
  eapply (A0_end_X4 cx _ SHS ob on dbza p1 p2 P STRM gp tp F4 fc4 CX AS SLO SHI z nin m4); [exact SM| exact (strm_reader m4 STRM SHS [] AS (proj1 S47) (proj2 S47) ZSHn I)|].
  apply evt_done. clear Hc6. intros c7 Hc7.
  eapply (free_call G PMc FDO MST Σ4 (c_E cx) 55768 m4); [exact FRE| exact SOK4| exact ELIV4| exact L0NE| exact TP| exact ART4| exact MI4| exact ST4| exact PR4| | exact Hc7|];
    [apply unwind_site1; [apply in_alloc_ras; reflexivity| exact (proj1 S0R)| exact (proj2 S0R)]|].
  clear Hc7. intros c8 Σ5 m5 k0 k1 k2 kk0 j1 j2 j3 j4 j5 j6 j7 k3 k4 k5 k6 F5 fc5 Hc8 SOK5 LV5 FR5 CR5 ART5 MI5 ST5 PR5 STEP5.
  rewrite (KMState.ret_pc_even 0x83e14 ltac:(lia) eq_refl) in Hc8.
  clear ST4 EH1. xfer_rtf G SOK5 STEP5 m4 m5.
  (* [comment removed for export] *)
  assert (AFW5 : app_fp [(STRM + 48, STRM + 56)]) by (cbn [app_fp]; unfold SH_LO, SH_HI; split; [clear - FSHI FLO FHI; lia| exact I]).
  eapply (l1_realizes RT AF Σ5 PMc _ T c8 MST Hc8).
  eapply (A0_end_X5 cx _ SHS ob on dbza p1 p2 P STRM lo gp tp F5 fc5 CX AS SHI LLO ltac:(clear - PE LOR'; lia) z nin m5 sp);
    [reflexivity| exact SM| exact SAV| exact ST5| exact (kmem_inv_N _ _ MI5)| exact (strm_reader m5 STRM SHS _ AS (proj1 S47) (proj2 S47) ZSHn AFW5)|].
  clear Hc8 SM SAV. intros m6 SM ST6 NMI6 MU6 WM6. apply evt_done. intros c9 Hc9.
  unfold end5_W in MU6.
  destruct (after_l1 AF G Σ5 _ m5 m6 SOK5 ART5 MI5 ST5 PR5 NMI6 MU6 WM6 ltac:(per_interval; right; right; right; unfold Wc; cbn [outside]; lia)) as (ART6 & MI6 & _ & PR6 & _).
  (* [comment removed for export] *)
  apply Hk. exists Σ5.
  split; [| split; [rewrite LV5, LV4, LV3, LV2; reflexivity| split; [rewrite FR5, FR4, FR3, FR2; reflexivity| split; [exact (proj1 (proj2 SOK5))| rewrite CR5, CR4, CR3, CR2; reflexivity]]]].
  eapply ASTA_conseq; [exact Hc9|]. intros ms <-.
  exists m6, k0, k1, k2, j1, j2, j3, j4, j5, j6, j7, k3, k4, k5, k6, F5, fc5.
  split; [reflexivity|]. split; [exact ART6|]. split; [exact MI6|]. split; [exact ST6|]. split; [exact SM|].
  intros a Ha Ho. apply PR6. unfold W in Ho. cbn [outside] in Ho. destruct Ho as (O1 & O2 & O3 & O4 & O5 & _).
  split; [| unfold Wc; cbn [outside]; exact (conj O5 I)].
  destruct Ha as [H|[H|[H|H]]]; [left; exact H| right; left; exact H| | right; right; right; exact H].
  destruct H as (p & n & IN & R). right; right; left. exists p, n. split; [| exact R].
  apply L0IN; [exact IN| | | |]; cbn [fst].
  - apply (live_other_base RT AF Σ m (c_A1 cx) ARR1_SIZE p n _ ART0 A1LIV IN ltac:(clear - BZbsL__; lia) R). clear - O2. lia.
  - apply (live_other_base RT AF Σ m (c_A2 cx) ARR2_SIZE p n _ ART0 A2LIV IN ltac:(clear - BZbsL__; lia) R). clear - O3. lia.
  - apply (live_other_base RT AF Σ m (c_FT cx) 262148 p n _ ART0 FTLIV IN ltac:(clear; lia) R). clear - O4. lia.
  - apply (live_other_base RT AF Σ m (c_E cx) 55768 p n _ ART0 ELIV IN ltac:(clear; lia) R). clear - O1. lia.
Qed.
End ENDL2.
