(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import ShapeAlg.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import ImageA RzCPS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Layout RT_iface D_defs D_kit I_read RT_liveprim L_libA. Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.Layout.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_iface.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_kit.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.I_read.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_liveprim.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_libA.TwinB__.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.L2B Require Import L2Kit L2Act L2Stmt L2StmtS B0_sessK B0_sessK2 B0_initK.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzCStream BzCState BzCBlock BzCDriver BzArrD CmpMem CmpCut CmpSess CmpSess2 CmpSessB CmpFsKit0 AsanKit AsanCut AsanCutB0 B0_b2c_cbV B0_b2c_hcV B0_b2c_wrV B0_b2c_wrE B0_b2c_wrI.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpCut6.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpCarve BzCLemmasFs.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require S0_cmp_bs CmpCutCB DecTac2.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require ZBridge.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.
#[local] Notation mem := (word -> option byte).



Section INITL2.
Context {BZP : BzParams} {ACEIL__ : ACeil}.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis AF_PRIM : af_live_primary RT.
Hypothesis MAL : malloc_contract RT.

(* [comment removed for export] *)
Ltac fp_new ELIV NEW :=
  per_interval;
  first [ left; lia
        | right; right; right; left; cbn [outside]; lia
        | right; right; right; right; split; [eexists _, _; split; [exact ELIV| lia]| apply NEW; lia] ].

(* [comment removed for export] *)
Ltac afw EOFF FSHI :=
  cbn [app_fp]; unfold SH_LO, SH_HI;
  repeat (split; [first [ right; lia
                        | let D := fresh "D" in pose proof EOFF as D; unfold id in D; lia
                        | let D := fresh "D" in pose proof FSHI as D; unfold id in D; lia ]|]); exact I.

Ltac in_list := cbn [app In]; repeat (first [left; reflexivity | right]).

Theorem bzCompressInit_cps : bzCompressInit_contract RT.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m STRM w0 w8 w12 w16 w20 w24 w32 w36 w40 w44 w48 lo usp
         FDO MST A0E A1E A2E A3E TP CEQ SM SOKA UWC LVM CRED ART0 MI0 ST0 LOW LOR SPT SPA.
  intros T c Hc Hk. subst a0 a1 a2 a3.
  set (P := usp - 176). assert (PE : P = usp - 176) by reflexivity.      (* [comment removed for export] *)
  (* [comment removed for export] *)
  pose proof alloc_ceiling_range as ACR. bz_params.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR. fold usp in SPR.
  pose proof LOR as LOR'. unfold RT_STACK in LOR'.
  assert (MC0 : mcost 55768 = 0) by reflexivity.
  assert (MC1 : mcost ARR1_SIZE = 2 * ARR1_SIZE + 16384) by (unfold mcost; destruct (Z.leb_spec ARR1_SIZE 64512); [exfalso; clear - H BZbsL__; lia| reflexivity]).
  assert (MC2 : mcost ARR2_SIZE = 2 * ARR2_SIZE + 16384) by (unfold mcost; destruct (Z.leb_spec ARR2_SIZE 64512); [exfalso; clear - H BZbsL__; lia| reflexivity]).
  assert (MC3 : mcost 262148 = 540680) by reflexivity.
  unfold INIT_COST, ESTATE_SIZE, FTAB_WORDS in CRED. change (4 * 65537) with 262148 in CRED. rewrite MC0, MC1, MC2, MC3 in CRED.
  (* [comment removed for export] *)
  destruct SOKA as ((fS & kS & FIN & FLO & FHI) & S8 & ZSH).
  pose proof (af_frames_range RT AF Σ m fS kS ART0 FIN) as (FS0 & FS1 & _ & _).
  pose proof (af_frames_align RT AF Σ m fS kS ART0 FIN) as (_ & FSEG). unfold SEGTOP_A in FSEG.
  pose proof (af_frames_hi RT AF Σ m fS kS ART0 FIN) as FSHI.
  pose proof (af_fshadow_apart RT AF Σ m fS kS ART0 FIN) as (_ & FSHF).
  assert (SLO : 0x62b000 <= STRM) by (clear - FSEG FLO; lia).
  assert (SHI : STRM + 80 <= CEILv) by (unfold CEILv; clear - FS1 FHI CEQ; lia).
  assert (LLO : CEILv <= lo) by (unfold CEILv; clear - CEQ LOW; lia).
  assert (S47 : 0 <= STRM /\ STRM + 80 <= 2^47) by (unfold CEILv in SHI; clear - SLO SHI ACR; lia).
  set (SHS := STRM / 8 + 2147450880).
  assert (AS : sanchor STRM SHS) by (apply sanchor_intro; exact S8).
  assert (ZSHn : bytes_at b0segs m SHS (repeat z8 10)) by exact ZSH.
  assert (SHSR : shad fS <= SHS /\ SHS + 10 <= shad (fS + fs_size kS)) by (unfold SHS, shad, SHB; clear - FLO FHI; Z.div_mod_to_equations; lia).
  assert (SHSH : SHS + 10 <= 17594333495296) by (unfold SHS; unfold CEILv in SHI; clear - SHI ACR; Z.div_mod_to_equations; lia).
  assert (SSA : STRM + 80 <= SHS \/ SHS + 10 <= STRM) by (destruct (FSHF _ _ FIN) as [D|D]; clear - D SHSR FLO FHI; lia).
  clearbody SHS. clear ZSH FSHF.
  (* [comment removed for export] *)
  assert (SCL : forall x, STRM <= x < STRM + 80 -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp x).
  { intros x Hx. right; right; right; left. exists fS, kS. split; [exact FIN| clear - Hx FLO FHI; lia]. }
  assert (SHCL : forall x, SHS <= x < SHS + 10 -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp x).
  { intros x Hx. right; right; right; right. exists fS, kS. split; [exact FIN| clear - Hx SHSR; lia]. }
  assert (WCL : forall x, ~ outside [(STRM, STRM + 80)] x -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp x).
  { intros x Hx. apply SCL. cbn [outside] in Hx. clear - Hx. lia. }
  destruct (act_setup_nf RT AF Σ m lo P usp [(STRM, STRM + 80)] ART0 LOW ltac:(clear - PE LOR'; unfold RT_STACK; lia) ltac:(clear - PE; lia) SPT
              ltac:(clear - PE SPA; Z.div_mod_to_equations; lia) WCL) as (G & SOK).
  pose proof (ck_intro P CStack) as KP. pose proof (ck_intro usp CStack) as KU. pose proof (ck_intro STRM CCaller) as KS. pose proof (ck_intro SHS CCaller) as KSH.
  unfold CEILv in SHI, LLO.
  (* [comment removed for export] *)
  assert (AFW1 : app_fp [(P, P + 176); (STRM + 56, STRM + 72)]).
  { cbn [app_fp]. unfold SH_LO, SH_HI. split; [right; clear - PE LLO LOR' ACR; lia|]. split; [clear - FSHI FLO FHI; lia| exact I]. }
  destruct (af_client_consts RT AF Σ m ART0) as (G1 & G2 & _ & _).
  assert (AC : aconsts B0C m) by (split; [exact (ro_C8_KN m _ _ G1)| exact (ro_C8_KN m _ _ G2)]). clear G1 G2.
  eapply (l1_realizes RT AF Σ PMc _ T c MST Hc).
  eapply (B0_init_I1 _ SHS P STRM lo gp tp F fc AS SLO SHI LLO ltac:(clear - PE LOR'; lia) m w0 w8 w12 w16 w20 w24 w32 w36 w40 w44 w48 ra sp);
    [reflexivity| exact ST0| exact SM| exact (kmem_inv_N _ _ MI0)| exact AC| exact (strm_reader m STRM SHS _ AS (proj1 S47) (proj2 S47) ZSHn AFW1)|].
  clear Hc SM AC. intros m1 v0 v8 v16 v24 v32 v40 v48 v64 SL SAV ST1n SM NMI1 MU1 WM1. apply evt_done. intros c1 Hc1.
  unfold init1_W in MU1.
  destruct (stk_split b0segs m lo P usp ST0 ltac:(clear - PE LOR'; lia)) as [ST0P _].
  destruct (after_l1 AF G Σ _ m m1 SOK ART0 MI0 ST0P (presi_refl _ _ _ _ m) NMI1 MU1 WM1 ltac:(per_interval; unfold P; cbn [outside]; lia)) as (ART1 & MI1 & ST1 & PR1 & _).
  clear ST0 ST0P AFW1.
  xfer_l1 m m1 MU1 WM1. clear NMI1 MU1 WM1 ST1n.
  (* [comment removed for export] *)
  assert (UW1 : unwind_ch m1 (Z_to_bv 64 0x81818) s0 (Z_to_bv 64 P)).
  { exists [0x814a4; 0x81200]. split.
    - rewrite unsigned_lit by (clear; lia). unfold SITE_TRACES. apply in_or_app. right. cbn [In]. right; right; right; right; left; reflexivity.
    - rewrite (P_unsigned G). apply (uw_chain_lower _ _ usp P); [| clear - PE; lia]. apply (uw_chain_agree _ m m1 _ _ _ UWC). intros a Ha. apply PR1.
      split; [left; exact Ha|]. cbn [outside]. split; [clear - Ha SHI LLO LOR'; lia| exact I]. }
  eapply (malloc_call AF G PMc FDO MST Σ 55768 m1); [exact MAL| exact SOK| clear; lia| exact TP| clear - LVM; lia| rewrite MC0; clear - CRED BZbsL__; lia| exact ART1| exact MI1| exact ST1| exact PR1
                                                    | exact UW1| exact Hc1|].
  clear Hc1 UW1. intros c2 Σ1 m2 E u0 u1 u2 e1 e2 e3 e4 e5 e6 e7 u3 u4 u5 u6 F2 fc2 Hc2 SOK1 LV1 FR1 CR1 EP0 E16 ETOP ART2 MI2 ST2 WM2 PR2 WRE ACCE STEP2 NEWE.
  rewrite (KMState.ret_pc_even 0x81818 ltac:(lia) eq_refl) in Hc2.
  clear ST1. xfer_rt G SOK STEP2 WM2 m1 m2.
  assert (ELIV1 : In (E, 55768) (rt_live RT Σ1)) by (rewrite LV1; left; reflexivity).
  pose proof (AF_PRIM Σ1 m2 _ _ ART2 ELIV1 ltac:(clear; lia)) as ELO. unfold SEGTOP_A in ELO.
  pose proof (af_live_range RT AF Σ1 m2 _ _ ART2 ELIV1) as (_ & EHI & _). rewrite (proj1 (proj2 SOK1)), <- CEQ in EHI.
  pose proof (af_live_offshadow RT AF Σ1 m2 _ _ ART2 ELIV1) as EOFF.
  assert (FIN1 : In (fS, kS) (rt_frames RT Σ1)) by (rewrite FR1; exact FIN).
  pose proof (af_frames_range RT AF Σ1 m2 fS kS ART2 FIN1) as (_ & _ & _ & FSL1).
  pose proof (af_fshadow_apart RT AF Σ1 m2 fS kS ART2 FIN1) as (FSHL1 & _).
  assert (SES : apartv E 55768 STRM 80) by (unfold apartv; destruct (FSL1 _ _ ELIV1) as [D|D]; clear - D FLO FHI; lia).
  assert (SSE : E + 55768 <= SHS \/ SHS + 10 <= E) by (destruct (FSHL1 _ _ ELIV1) as [D|D]; clear - D SHSR; lia).
  clear FSL1 FSHL1.
  set (SHE := E / 8 + 2147450880).
  assert (AE : sanchor E SHE) by (apply sanchor_intro; clear - E16; Z.div_mod_to_equations; lia).
  clearbody SHE.
  (* [comment removed for export] *)
  assert (NEWE' : forall x, E <= x < E + 55768 -> ~ aclient (rt_live RT Σ) (rt_frames RT Σ) usp x).
  { intros x Hx HA. exact (NEWE x (acl_caller G Σ x SOK HA) Hx). }
  (* [comment removed for export] *)
  destruct (n_wr_at_rw_CB m2 E 55768 WRE ltac:(clear; lia)) as (J & EJ).
  assert (LJ : Z.of_nat (length J) = 55768) by (destruct EJ as [[Hwf _] _]; cbn in Hwf; destruct Hwf as [HL _]; rewrite HL; reflexivity).
  destruct (estate_carveA b0segs m2 E J EJ LJ) as (EH & INJ & UNJ & EH2 & REST). clear EJ WRE ACCE.
  pose proof (ck_intro E (CLive E 55768)) as KE.
  (* [comment removed for export] *)
  assert (E8 : E mod 8 = 0) by (clear - E16; Z.div_mod_to_equations; lia).
  assert (AFW2 : app_fp [(E, E + 8); (E + 24, E + 48); (P + 8, P + 72)]).
  { cbn [app_fp]. unfold SH_LO, SH_HI. split; [clear - EOFF; lia|]. split; [clear - EOFF; lia|]. split; [right; clear - PE LLO LOR' ACR; lia| exact I]. }
  eapply (l1_realizes RT AF Σ1 PMc _ T c2 MST Hc2).
  eapply (B0_init_I2 _ SHS P STRM lo gp tp F2 fc2 AS SHI LLO ltac:(clear - PE LOR'; lia) E SHE J AE ELO EHI SES m2 _ _ _ _ v0 v8 v16 v24 v32 v40 v48 (Z_to_bv 64 (SHS + 8)) v64
            w0 w8 w12 w16 w20 w24 w32 w36 w40 w44 w48);
    [exact EH| exact SL| exact SM| exact (kmem_inv_N _ _ MI2)| exact (live_reader RT AF Σ1 m2 E 55768 _ ART2 ELIV1 E8 eq_refl AFW2)
     | exact (strm_reader m2 STRM SHS _ AS (proj1 S47) (proj2 S47) ZSHn AFW2)|].
  clear Hc2 EH SL SM AFW2. intros m5 a4' EH SL SM NMI5 MU5 WM5. apply evt_done. intros c5 Hc5.
  unfold init2_W in MU5.
  destruct (after_l1_new AF G Σ1 _ m2 m5 SOK1 ART2 MI2 ST2 PR2 NMI5 MU5 WM5 ltac:(fp_new ELIV1 NEWE')) as (ART5 & MI5 & ST5 & PR5 & _).
  unfold apartv in SES.
  change (id (E + 55768 <= STRM \/ STRM + 80 <= E)) in SES. change (id (E + 55768 <= SHS \/ SHS + 10 <= E)) in SSE. change (id (STRM + 80 <= SHS \/ SHS + 10 <= STRM)) in SSA.
  change (id (E + 55768 <= 2147446784 \/ 17594333495296 <= E)) in EOFF.
  change (id (fS + fs_size kS <= 2147446784 \/ 17594333495296 <= fS)) in FSHI.
  clear ST2. xfer_l1 m2 m5 MU5 WM5. clear NMI5 MU5 WM5.
  assert (PR64 : 0 <= E < P /\ P < 2^64) by (clear - ELO EHI LLO PE LOR' SPR; lia).
  eapply (malloc_call AF G PMc FDO MST Σ1 ARR1_SIZE m5); [exact MAL| exact SOK1| clear - BZbsL__ BZbsH__; lia| exact TP| rewrite LV1; cbn [length]; rewrite Nat2Z.inj_succ; clear - LVM; lia
                                                        | rewrite CR1, MC0, MC1; clear - CRED BZbsL__; lia| exact ART5| exact MI5| exact ST5| exact PR5| | exact Hc5|];
    [apply unwind_site1; [apply in_alloc_ras; reflexivity| exact (proj1 PR64)| exact (proj2 PR64)]|].
  clear Hc5. intros c6 Σ2 m6 r1 y0 y1 y2 g1 g2 g3 g4 g5 g6 g7 y3 y4 y5 y6 F6 fc6 Hc6 SOK2 LV2 FR2 CR2 R1P R116 R1TOP ART6 MI6 ST6 WM6 PR6 WR1 ACC1 STEP6 NEW1.
  rewrite (KMState.ret_pc_even 0x818d8 ltac:(lia) eq_refl) in Hc6.
  clear ST5. xfer_rt G SOK1 STEP6 WM6 m5 m6. clear ACC1 STEP6 WM6 NEW1.
  assert (ELIV2 : In (E, 55768) (rt_live RT Σ2)) by (rewrite LV2; right; exact ELIV1).
  (* [comment removed for export] *)
  assert (AFW4 : app_fp [(E + 24, E + 32)]) by (afw EOFF FSHI).
  eapply (l1_realizes RT AF Σ2 PMc _ T c6 MST Hc6).
  eapply (B0_init_I4 _ SHS P STRM gp tp F6 fc6 AS E SHE J AE SES m6 r1 w0 w8 w12 w16 w20 w24 w32 w36 w40 w44 w48);
    [unfold USTACK_TOP in R1TOP; clear - R1P R1TOP BZbsL__; lia| exact EH| exact SM| exact (kmem_inv_N _ _ MI6)
     | exact (live_reader RT AF Σ2 m6 E 55768 _ ART6 ELIV2 E8 eq_refl AFW4)| exact (strm_reader m6 STRM SHS _ AS (proj1 S47) (proj2 S47) ZSHn AFW4)|].
  clear Hc6 EH SM AFW4. intros m7 EH SM NMI7 MU7 WM7. apply evt_done. intros c7 Hc7.
  unfold init4_W in MU7.
  destruct (after_l1_new AF G Σ2 _ m6 m7 SOK2 ART6 MI6 ST6 PR6 NMI7 MU7 WM7 ltac:(fp_new ELIV2 NEWE')) as (ART7 & MI7 & ST7 & PR7 & _).
  clear ST6. xfer_l1 m6 m7 MU7 WM7. clear NMI7 MU7 WM7.
  eapply (malloc_call AF G PMc FDO MST Σ2 ARR2_SIZE m7); [exact MAL| exact SOK2| clear - BZbsL__ BZbsH__; lia| exact TP| rewrite LV2, LV1; cbn [length]; rewrite !Nat2Z.inj_succ; clear - LVM; lia
                                                        | rewrite CR2, CR1, MC0, MC1, MC2; clear - CRED BZbsL__; lia| exact ART7| exact MI7| exact ST7| exact PR7| | exact Hc7|];
    [apply unwind_site1; [apply in_alloc_ras; reflexivity| exact (proj1 PR64)| exact (proj2 PR64)]|].
  clear Hc7. intros c8 Σ3 m8 r2 z0 z1 z2 h1 h2 h3 h4 h5 h6 h7 z3 z4 z5 z6 F8 fc8 Hc8 SOK3 LV3 FR3 CR3 R2P R216 R2TOP ART8 MI8 ST8 WM8 PR8 WR2 ACC2 STEP8 NEW2.
  rewrite (KMState.ret_pc_even 0x81908 ltac:(lia) eq_refl) in Hc8.
  clear ST7. xfer_rt G SOK2 STEP8 WM8 m7 m8. clear ACC2 STEP8 WM8 NEW2.
  assert (ELIV3 : In (E, 55768) (rt_live RT Σ3)) by (rewrite LV3; right; exact ELIV2).
  (* [comment removed for export] *)
  assert (AFW5 : app_fp [(E + 32, E + 40)]) by (afw EOFF FSHI).
  eapply (l1_realizes RT AF Σ3 PMc _ T c8 MST Hc8).
  eapply (B0_init_I5 _ SHS P STRM lo gp tp F8 fc8 AS LLO ltac:(clear - PE LOR'; lia) E SHE J AE EHI SES m8 r1 r2 w0 w8 w12 w16 w20 w24 w32 w36 w40 w44 w48);
    [unfold USTACK_TOP in R2TOP; clear - R2P R2TOP BZbsL__; lia| exact EH| exact SM| exact SL| exact (kmem_inv_N _ _ MI8)
     | exact (live_reader RT AF Σ3 m8 E 55768 _ ART8 ELIV3 E8 eq_refl AFW5)| exact (strm_reader m8 STRM SHS _ AS (proj1 S47) (proj2 S47) ZSHn AFW5)|].
  clear Hc8 EH SM SL AFW5. intros m9 EH SM SL NMI9 MU9 WM9. apply evt_done. intros c9 Hc9.
  unfold init5_W in MU9.
  destruct (after_l1_new AF G Σ3 _ m8 m9 SOK3 ART8 MI8 ST8 PR8 NMI9 MU9 WM9 ltac:(fp_new ELIV3 NEWE')) as (ART9 & MI9 & ST9 & PR9 & _).
  clear ST8. xfer_l1 m8 m9 MU9 WM9. clear NMI9 MU9 WM9.
  eapply (malloc_call AF G PMc FDO MST Σ3 262148 m9); [exact MAL| exact SOK3| clear; lia| exact TP| rewrite LV3, LV2, LV1; cbn [length]; rewrite !Nat2Z.inj_succ; clear - LVM; lia
                                                     | rewrite CR3, CR2, CR1, MC0, MC1, MC2, MC3; clear - CRED BZbsL__; lia| exact ART9| exact MI9| exact ST9| exact PR9| | exact Hc9|];
    [apply unwind_site1; [apply in_alloc_ras; reflexivity| exact (proj1 PR64)| exact (proj2 PR64)]|].
  clear Hc9. intros c10 Σ4 m10 r3 k0 k1 k2 j1 j2 j3 j4 j5 j6 j7 k3 k4 k5 k6 F10 fc10 Hc10 SOK4 LV4 FR4 CR4 R3P R316 R3TOP ART10 MI10 ST10 WM10 PR10 WR3 ACC3 STEP10 NEW3.
  rewrite (KMState.ret_pc_even 0x81940 ltac:(lia) eq_refl) in Hc10.
  clear ST9. xfer_rt G SOK3 STEP10 WM10 m9 m10. clear ACC3 STEP10 WM10 NEW3.
  assert (ELIV4 : In (E, 55768) (rt_live RT Σ4)) by (rewrite LV4; right; exact ELIV3).
  (* [comment removed for export] *)
  assert (AFW6 : app_fp [(E, E + 128); (E + 128, E + 384); (E + 640, E + 672); (STRM + 12, STRM + 56); (P - 16, P + 176)]) by (afw EOFF FSHI).
  destruct (af_client_consts RT AF Σ4 m10 ART10) as (G1 & G2 & _ & _).
  assert (AC10 : aconsts B0C m10) by (split; [exact (ro_C8_KN m10 _ _ G1)| exact (ro_C8_KN m10 _ _ G2)]). clear G1 G2.
  eapply (l1_realizes RT AF Σ4 PMc _ T c10 MST Hc10).
  eapply (B0_init_I6 _ SHS P STRM lo gp tp F10 fc10 SLO SHI LLO ltac:(clear - PE LOR'; lia) ltac:(clear - PE SPR; lia) E SHE J AE ELO EHI SES m10 sp r1 r2 r3 (jseg J 128 256)
            w0 w8 w12 w16 w20 w24 w32 w36 w40 w44 w48);
    [reflexivity| clear - PE LOR'; lia
     | unfold USTACK_TOP in R1TOP; clear - R1P R1TOP BZbsL__; lia| unfold USTACK_TOP in R2TOP; clear - R2P R2TOP BZbsL__; lia| unfold USTACK_TOP in R3TOP; clear - R3P R3TOP; lia
     | exact EH| exact INJ| exact EH2| exact SM| exact SL| exact SAV| exact ST10| exact (kmem_inv_N _ _ MI10)| exact AC10
     | exact (live_reader RT AF Σ4 m10 E 55768 _ ART10 ELIV4 E8 eq_refl AFW6)| exact (strm_reader m10 STRM SHS _ AS (proj1 S47) (proj2 S47) ZSHn AFW6)|].
  clear Hc10 EH INJ EH2 SM SL SAV AC10 AFW6. intros m13 t0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' EH INZ EH2 SM ST13 NMI13 MU13 WM13. apply evt_done. intros c13 Hc13.
  unfold init6_W in MU13.
  destruct (after_l1_new_leaf RT AF _ _ _ _ _ _ _ _ _ _ _ _ _ G _ Σ4 _ 16 m10 m13 SOK4 ART10 MI10 PR10 NMI13 MU13 WM13 ltac:(clear; lia) ltac:(clear - PE LOR'; unfold RT_STACK; lia)
              ltac:(per_interval; first [ left; unfold P; lia
                                        | right; right; right; left; cbn [outside]; lia
                                        | right; right; right; right; split; [eexists _, _; split; [exact ELIV4| lia]| apply NEWE'; lia] ])) as (ART13 & MI13 & PR13 & _).
  clear ST10. xfer_l1 m10 m13 MU13 WM13. clear NMI13 MU13 WM13.
  (* [comment removed for export] *)
  assert (LVall : rt_live RT Σ4 = (r3, 262148) :: (r2, ARR2_SIZE) :: (r1, ARR1_SIZE) :: (E, 55768) :: rt_live RT Σ) by (rewrite LV4, LV3, LV2, LV1; reflexivity).
  assert (SP4 : rt_sp0 RT Σ4 - STACK_WIN = alloc_ceiling) by (rewrite (proj1 (proj2 SOK4)); symmetry; exact CEQ).
  assert (R1LIV : In (r1, ARR1_SIZE) (rt_live RT Σ4)) by (rewrite LVall; in_list).
  assert (R2LIV : In (r2, ARR2_SIZE) (rt_live RT Σ4)) by (rewrite LVall; in_list).
  assert (R3LIV : In (r3, 262148) (rt_live RT Σ4)) by (rewrite LVall; in_list).
  pose proof (af_live_range RT AF Σ4 m13 _ _ ART13 R1LIV) as (_ & R1H & R1I). pose proof (af_live_range RT AF Σ4 m13 _ _ ART13 R2LIV) as (_ & R2H & R2I).
  pose proof (af_live_range RT AF Σ4 m13 _ _ ART13 R3LIV) as (_ & R3H & R3I). pose proof (af_live_range RT AF Σ4 m13 _ _ ART13 ELIV4) as (_ & _ & EI).
  rewrite SP4 in R1H, R2H, R3H. unfold SEGTOP_A in R1I, R2I, R3I, EI.
  pose proof (af_live_disj RT AF Σ4 m13 r3 262148 r2 ARR2_SIZE [] _ ART13 LVall ltac:(in_list)) as D32.
  pose proof (af_live_disj RT AF Σ4 m13 r3 262148 r1 ARR1_SIZE [] _ ART13 LVall ltac:(in_list)) as D31.
  pose proof (af_live_disj RT AF Σ4 m13 r3 262148 E 55768 [] _ ART13 LVall ltac:(in_list)) as D3E.
  pose proof (af_live_disj RT AF Σ4 m13 r2 ARR2_SIZE r1 ARR1_SIZE [(r3, 262148)] _ ART13 LVall ltac:(in_list)) as D21.
  pose proof (af_live_disj RT AF Σ4 m13 r2 ARR2_SIZE E 55768 [(r3, 262148)] _ ART13 LVall ltac:(in_list)) as D2E.
  pose proof (af_live_disj RT AF Σ4 m13 r1 ARR1_SIZE E 55768 [(r3, 262148); (r2, ARR2_SIZE)] _ ART13 LVall ltac:(in_list)) as D1E.
  destruct (n_wr_at_rw_CB m13 r1 ARR1_SIZE WR1 ltac:(clear - BZbsL__; lia)) as (J1 & R1J).
  destruct (n_wr_at_rw_CB m13 r2 ARR2_SIZE WR2 ltac:(clear - BZbsL__; lia)) as (J2 & R2J).
  destruct (n_wr_at_rw_CB m13 r3 262148 WR3 ltac:(clear; lia)) as (J3 & R3J).
  destruct (erest_carve b0segs m13 E J REST LJ) as (MTF & SEL & SLM & LEN & COD & RFQ & LNP).
  apply Hk. exists Σ4, E, r1, r2, r3.
  split; [| split; [rewrite LVall; unfold FTAB_WORDS, ESTATE_SIZE; reflexivity| split; [rewrite FR4, FR3, FR2, FR1; reflexivity| split; [exact (proj1 (proj2 SOK4))|]]]].
  2:{ rewrite CR4, CR3, CR2, CR1. unfold INIT_COST, ESTATE_SIZE, FTAB_WORDS. change (4 * 65537) with 262148. clear. lia. }
  eapply ASTA_conseq; [exact Hc13|]. intros ms <-.
  exists m13, t0'', k1, k2, a1'', a2'', a3'', a4'', a5'', a6'', a7'', k3, k4, k5, k6, F10, fc10, J,
         (zarr_of_junkb J1), (zarr_of_junkb J2), (S0_cmp_bs.zarr_of_junkw J3 65537), znew, znew, znew, znew, znew, znew, znew, znew, znew, 0, 0, 0, 0, 0.
  cbv zeta.
  split; [reflexivity|]. split; [exact ART13|]. split; [exact MI13|]. split; [exact ST13|].
  split. { unfold cctx_ok. cbn [c_E c_A1 c_A2 c_FT c_J]. unfold ESTATE_SIZE, FTAB_WORDS, CEIL. change (4 * 65537) with 262148.
           repeat (split; [first [exact I| assumption| clear - ELO EHI R1P R1H R2P R2H R3P R3H; lia]|]). exact I. }
  split. { unfold cctx_sep, apart. cbn [c_E c_A1 c_A2 c_FT]. unfold ESTATE_SIZE, FTAB_WORDS. change (4 * 65537) with 262148.
           repeat (split; [first [exact I| clear - D32 D31 D3E D21 D2E D1E; lia]|]). exact I. }
  split. { unfold cctx_img, img_apart, IMG_LO3. cbn [ci_hi aci_c B0C c_E c_A1 c_A2 c_FT]. unfold ESTATE_SIZE, FTAB_WORDS. change (4 * 65537) with 262148.
           repeat (split; [first [exact I| clear - EI R1I R2I R3I; lia]|]). exact I. }
  split.
  { unfold emem. cbn [c_E c_J]. unfold est_init. cbn [e_inUse e_unseqToSeq e_mtfFreq e_selector e_selectorMtf e_len e_code e_rfreq e_len_pack].
    split. { replace (EFINA J STRM r1 r2 r3) with (EFINA J (STRM - BZF_STRM + BZF_STRM) r1 r2 r3) in EH by (f_equal; clear; lia). exact EH. }
    split. { rewrite ovb_inUse_clear. exact INZ. }
    split. { exact (ovb_init b0segs m13 _ 256 _ UNJ ltac:(clear; lia)). }
    split. { exact EH2. }
    exact (conj MTF (conj SEL (conj SLM (conj LEN (conj COD (conj RFQ LNP)))))). }
  split.
  { unfold CmpCut.amem, FTAB_WORDS. cbn [c_A1 c_A2 c_FT]. unfold est_init. cbn [e_arr1 e_arr2 e_ftab].
    split; [exact (zb8_of_junk b0segs m13 r1 ARR1_SIZE J1 R1J ltac:(clear - BZbsL__; lia))|].
    split; [exact (zb8_of_junk b0segs m13 r2 ARR2_SIZE J2 R2J ltac:(clear - BZbsL__; lia))|].
    exact (S0_cmp_bs.zw32_of_junk b0segs m13 r3 65537 J3 R3J ltac:(clear; lia)). }
  split; [exact (zarr_of_junkb_ok J1)|]. split; [exact (zarr_of_junkb_ok J2)|]. split; [exact (zarr_of_junkw_w32 J3 65537 ltac:(clear; lia))|].
  split; [exact SM|].
  exact (pres_final_nf RT AF Σ lo P usp _ m m m13 ART0 LOW ltac:(clear - PE LOR'; lia) ltac:(clear - PE; lia) (munch_refl _ m) PR13).
Qed.
End INITL2.
