(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import ShapeAlg.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import ImageA RzCPS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Layout RT_iface D_defs D_kit I_read RT_liveprim L_libA. Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.Layout.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_iface.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_kit.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.I_read.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_liveprim.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_libA.TwinB__.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.L2B Require Import L2Kit L2Act L2Stmt L2StmtS L2StmtD B0_sessK.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0 SegsB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzInv BzContracts CmpMem CmpCut CmpCarve CmpFsKit0 AsanKit AsanCut AsanCutB0 B0_b2c_cbV B0_b2c_hcV B0_b2c_wrV B0F_b2d_wrV B0F_b2d_wrI.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require GlueCarve.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.
#[local] Notation mem := (word -> option byte).

Section DINITL2.
Context {ACEIL__ : ACeil}.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis AF_PRIM : af_live_primary RT.
Hypothesis MAL : malloc_contract RT.

(* [comment removed for export] *)
Ltac fp_new SLIV NEW :=
  per_interval;
  first [ left; lia
        | right; right; right; left; cbn [outside]; lia
        | right; right; right; right; split; [eexists _, _; split; [exact SLIV| lia]| apply NEW; lia] ].

Theorem bzDecompressInit_cps : bzDecompressInit_contract RT.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m STRM small w0 w8 w12 w16 q1 w24 w32 w36 w40 q2 w48 lo usp
         FDO MST A0E A1E A2E SMALL TP CEQ SM Q1L Q2L SOKA LVM ART0 MI0 ST0 LOW LOR SPT SPA.
  intros T c Hc Hk. subst a0 a1 a2.
  set (P := usp - 48). assert (PE : P = usp - 48) by reflexivity.
  (* [comment removed for export] *)
  pose proof alloc_ceiling_range as ACR.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR. fold usp in SPR.
  pose proof LOR as LOR'. unfold RT_STACK in LOR'.
  assert (MC0 : mcost 64144 = 0) by reflexivity.
  pose proof (af_credit_nonneg RT AF Σ m ART0) as CRN.
  assert (SMR : 0 <= small <= 1) by (clear - SMALL; lia).
  (* [comment removed for export] *)
  destruct SOKA as ((fS & kS & FIN & FLO & FHI) & S8 & ZSH).
  pose proof (af_frames_range RT AF Σ m fS kS ART0 FIN) as (FS0 & FS1 & _ & _).
  pose proof (af_frames_align RT AF Σ m fS kS ART0 FIN) as (_ & FSEG). unfold SEGTOP_A in FSEG.
  pose proof (af_frames_hi RT AF Σ m fS kS ART0 FIN) as FSHI.
  pose proof (af_fshadow_apart RT AF Σ m fS kS ART0 FIN) as (_ & FSHF).
  assert (SLO : 0x62b000 <= STRM) by (clear - FSEG FLO; lia).
  assert (SHI : STRM + 80 <= alloc_ceiling) by (clear - FS1 FHI CEQ; lia).
  assert (LLO : alloc_ceiling <= lo) by (clear - CEQ LOW; lia).
  assert (PLO : lo <= P) by (clear - PE LOR'; lia).
  assert (S47 : 0 <= STRM /\ STRM + 80 <= 2^47) by (clear - SLO SHI ACR; lia).
  set (SHS := STRM / 8 + 2147450880).
  assert (AS : sanchor STRM SHS) by (apply sanchor_intro; exact S8).
  assert (ZSHn : bytes_at b0segs m SHS (repeat z8 10)) by exact ZSH.
  assert (SHSR : shad fS <= SHS /\ SHS + 10 <= shad (fS + fs_size kS)) by (unfold SHS, shad, SHB; clear - FLO FHI; Z.div_mod_to_equations; lia).
  assert (SHSH : SHS + 10 <= 17594333495296) by (unfold SHS; clear - SHI ACR; Z.div_mod_to_equations; lia).
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
  (* [comment removed for export] *)
  assert (AFW1 : app_fp [(P, P + 48); (STRM + 56, STRM + 72)]).
  { cbn [app_fp]. unfold SH_LO, SH_HI. split; [right; clear - PE LLO LOR' ACR; lia|]. split; [clear - FSHI FLO FHI; lia| exact I]. }
  destruct (af_client_consts RT AF Σ m ART0) as (G1 & G2 & _ & _).
  assert (AC : aconsts B0C m) by (split; [exact (ro_C8_KN m _ _ G1)| exact (ro_C8_KN m _ _ G2)]). clear G1 G2.
  eapply (l1_realizes RT AF Σ PMc _ T c MST Hc).
  eapply (B0_dinit_I1 _ P STRM lo 0 small gp tp F fc SLO SHI S8 LLO PLO ltac:(clear; lia) SMR m w0 w8 w12 w16 q1 w24 w32 w36 w40 q2 w48 ra sp);
    [reflexivity| exact ST0| exact SM| exact (kmem_inv_N _ _ MI0)| exact AC| exact (strm_reader m STRM SHS _ AS (proj1 S47) (proj2 S47) ZSHn AFW1)|].
  clear Hc SM AC. intros m1 v0 SAV ST1n SM NMI1 MU1 WM1. apply evt_done. intros c1 Hc1.
  unfold dinit1_W in MU1.
  destruct (stk_split b0segs m lo P usp ST0 ltac:(clear - PE LOR'; lia)) as [ST0P _].
  destruct (after_l1 AF G Σ _ m m1 SOK ART0 MI0 ST0P (presi_refl _ _ _ _ m) NMI1 MU1 WM1 ltac:(per_interval; unfold P; cbn [outside]; lia)) as (ART1 & MI1 & ST1 & PR1 & _).
  clear ST0 ST0P AFW1.
  xfer_l1 m m1 MU1 WM1. clear NMI1 MU1 WM1 ST1n.
  (* [comment removed for export] *)
  assert (P0R : 0 <= 0 < P /\ P < 2^64) by (clear - PE LLO LOR' ACR SPR; lia).
  eapply (malloc_call AF G PMc FDO MST Σ 64144 m1); [exact MAL| exact SOK| clear; lia| exact TP| clear - LVM; lia| rewrite MC0; exact CRN| exact ART1| exact MI1| exact ST1| exact PR1
                                                    | | exact Hc1|];
    [apply unwind_site1; [apply in_alloc_ras; reflexivity| exact (proj1 P0R)| exact (proj2 P0R)]|].
  clear Hc1. intros c2 Σ1 m2 S u0 u1 u2 e1 e2 e3 e4 e5 e6 e7 u3 u4 u5 u6 F2 fc2 Hc2 SOK1 LV1 FR1 CR1 SP0 S16 STOP ART2 MI2 ST2 WM2 PR2 WRS ACCS STEP2 NEWS.
  rewrite (KMState.ret_pc_even 0x83b04 ltac:(lia) eq_refl) in Hc2.
  clear ST1. xfer_rt G SOK STEP2 WM2 m1 m2.
  assert (SLIV1 : In (S, 64144) (rt_live RT Σ1)) by (rewrite LV1; left; reflexivity).
  pose proof (AF_PRIM Σ1 m2 _ _ ART2 SLIV1 ltac:(clear; lia)) as SSLO. unfold SEGTOP_A in SSLO.
  pose proof (af_live_range RT AF Σ1 m2 _ _ ART2 SLIV1) as (_ & SSHI & _). rewrite (proj1 (proj2 SOK1)), <- CEQ in SSHI.
  pose proof (af_live_offshadow RT AF Σ1 m2 _ _ ART2 SLIV1) as SOFF.
  assert (FIN1 : In (fS, kS) (rt_frames RT Σ1)) by (rewrite FR1; exact FIN).
  pose proof (af_frames_range RT AF Σ1 m2 fS kS ART2 FIN1) as (_ & _ & _ & FSL1).
  pose proof (af_fshadow_apart RT AF Σ1 m2 fS kS ART2 FIN1) as (FSHL1 & _).
  assert (SES : apartv S 64144 STRM 80) by (unfold apartv; destruct (FSL1 _ _ SLIV1) as [D|D]; clear - D FLO FHI; lia).
  assert (SSE : S + 64144 <= SHS \/ SHS + 10 <= S) by (destruct (FSHL1 _ _ SLIV1) as [D|D]; clear - D SHSR; lia).
  clear FSL1 FSHL1.
  (* [comment removed for export] *)
  assert (NEWS' : forall x, S <= x < S + 64144 -> ~ aclient (rt_live RT Σ) (rt_frames RT Σ) usp x).
  { intros x Hx HA. exact (NEWS x (acl_caller G Σ x SOK HA) Hx). }
  (* [comment removed for export] *)
  destruct (n_wr_at_rw_CB m2 S 64144 WRS ltac:(clear; lia)) as (J & SJ).
  destruct (GlueCarve.split_block b0segs m2 S J SJ) as (HDJ & (BA & WA & LA) & MDJ & (bsB & BB & WB & LB)). clear SJ WRS ACCS.
  pose proof (ck_intro S (CLive S 64144)) as KSS.
  (* [comment removed for export] *)
  assert (S8' : S mod 8 = 0) by (clear - S16; Z.div_mod_to_equations; lia).
  assert (AFW2 : app_fp [(S, S + 68); (S + 3152, S + 3176); (S + 3188, S + 3192); (STRM + 12, STRM + 20); (STRM + 36, STRM + 44); (STRM + 48, STRM + 56)]).
  { cbn [app_fp]. unfold SH_LO, SH_HI. split; [clear - SOFF; lia|]. split; [clear - SOFF; lia|]. split; [clear - SOFF; lia|].
    split; [clear - FSHI FLO FHI; lia|]. split; [clear - FSHI FLO FHI; lia|]. split; [clear - FSHI FLO FHI; lia| exact I]. }
  eapply (l1_realizes RT AF Σ1 PMc _ T c2 MST Hc2).
  eapply (B0_dinit_I2 _ P STRM lo 0 small gp tp F2 fc2 SLO SHI LLO PLO S SSLO SSHI S8' SES m2 sp);
    [exact PE| exact HDJ| exact MDJ| exact SM| exact SAV| exact ST2| exact (kmem_inv_N _ _ MI2)| exact (live_reader RT AF Σ1 m2 S 64144 _ ART2 SLIV1 S8' eq_refl AFW2)
     | exact (strm_reader m2 STRM SHS _ AS (proj1 S47) (proj2 S47) ZSHn AFW2)|].
  clear Hc2 HDJ MDJ SM SAV AFW2. intros m5 p20 p4 p3 p12 q12 q4 a1' a2' a3' HD MD SM ST5 NMI5 MU5 WM5. apply evt_done. intros c5 Hc5.
  unfold dinit2_W in MU5.
  destruct (after_l1_new AF G Σ1 _ m2 m5 SOK1 ART2 MI2 ST2 PR2 NMI5 MU5 WM5 ltac:(fp_new SLIV1 NEWS')) as (ART5 & MI5 & _ & PR5 & _).
  unfold apartv in SES.
  change (id (S + 64144 <= STRM \/ STRM + 80 <= S)) in SES. change (id (S + 64144 <= SHS \/ SHS + 10 <= S)) in SSE. change (id (STRM + 80 <= SHS \/ SHS + 10 <= STRM)) in SSA.
  change (id (S + 64144 <= 2147446784 \/ 17594333495296 <= S)) in SOFF.
  change (id (fS + fs_size kS <= 2147446784 \/ 17594333495296 <= fS)) in FSHI.
  clear ST2. xfer_l1 m2 m5 MU5 WM5. clear NMI5 MU5 WM5.
  (* [comment removed for export] *)
  pose proof (DHEAD3_init b0segs m5 S STRM small p20 p4 p3 p12 HD) as HDI.
  destruct (GlueCarve.carve_head b0segs m5 S STRM small p20 p4 p3 p12 HDI ltac:(clear - SMR; lia)) as (HC & L1' & L2' & L3' & R1' & R2' & R3' & R4' & R5' & SMV).
  pose proof (DMID3_init' b0segs m5 (S + 3152) q12 q4 MD) as MDI.
  destruct (GlueCarve.carve_mid b0segs m5 (S + 3152) q12 q4 MDI) as (MC & MT & M16 & M4 & MNI).
  destruct (GlueCarve.carve_rest b0segs m5 S _ bsB BA WA LA BB WB LB) as (nbu & cf & r & js & NBU & NBR & CF & CFL & DR & SV & SVL).
  apply Hk. exists Σ1, S.
  split; [| split; [exact LV1| split; [exact FR1| split; [exact (proj1 (proj2 SOK1))| rewrite CR1, MC0; clear; lia]]]].
  eapply ASTA_conseq; [exact Hc5|]. intros ms <-.
  eexists m5, _, _, _, _, _, _, _, _, _, _, _, _, _, _, F2, fc2, _, nbu, cf, _, r, js.
  split; [reflexivity|]. split; [exact ART5|]. split; [exact MI5|]. split; [exact ST5|].
  split.
  { unfold dstate10A. split; [exact HC|]. split.
    { unfold hwf10A. repeat split; first [reflexivity| assumption| lia]. }
    split; [exact NBU|]. split; [exact NBR|]. split; [exact CF|]. split; [exact CFL|]. split; [exact MC|].
    split; [exact MT|]. split; [exact M16|]. split; [exact M4|]. split; [exact MNI|]. split; [reflexivity|]. split; [exact DR| exact SV]. }
  split; [exact SM|]. split; [exact S16|].
  split. { intros a Ha Hx. exact (NEWS' a Hx Ha). }
  exact (pres_final_nf RT AF Σ lo P usp _ m m m5 ART0 LOW PLO ltac:(clear - PE; lia) (munch_refl _ m) PR5).
Qed.
End DINITL2.
