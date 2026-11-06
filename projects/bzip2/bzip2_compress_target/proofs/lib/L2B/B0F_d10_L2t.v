(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import ShapeAlg.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import ImageA RzCPS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Layout RT_iface D_defs D_kit I_read RT_liveprim RT_globals R_unwind_chain. Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.Layout.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_iface.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_kit.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.I_read.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_liveprim.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_globals.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_unwind_chain.TwinB__.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require L_libA D_libiface RT_frame.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.L2B Require Import L2Kit L2Act L2StmtD B0_fs_L2f B0_sessK B0F_decK B0F_decX B0F_dec_L2a B0F_dec_L2b B0F_dec_L2t B0F_bzd_L2t B0F_d10_L2k.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0 SegsB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel BzTac BzTables CmpMem AsanKit AsanKit2 AsanCut.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzDefs BzInv BzContracts.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState BzDBlock BzDK BzDU5 BzDU10M BzDOKp DecCut DecCutF10 DecCutFB B0F_decV B0F_decRet B0F_decCutsA B0F_dec_pro1 B0F_dec_U0 B0F_dec_epi B0F_g10A B0F_g10C B0F_g10Main B0F_g10H B0F_g10K.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU10M OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOKp OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutFB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decV OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decRet OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decCutsA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_g10A OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_g10C OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_g10Main.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.
#[local] Notation mem := (word -> option byte).

(* [comment removed for export] *)
Ltac agx_side AG tac := eapply agree_sub; [exact AG|]; let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; cbv beta in Hx |- *; cbn [cells_size csize Nat.add length] in Hx; tac Hx.
Ltac agx AG H tac :=
  lazymatch type of AG with agree_on _ _ ?m' =>
  lazymatch type of H with
  | rw_cells _ ?m ?a ?cs => apply (n_rw_cells_agree b0segs m m' a cs) in H; [| agx_side AG tac]
  | ro_cells _ ?m ?a ?cs => apply (n_ro_cells_agree b0segs m m' a cs) in H; [| agx_side AG tac]
  | u8arr _ ?m ?a ?bs => apply (n_u8arr_agree b0segs m m' a bs) in H; [| agx_side AG tac]
  | u32arr _ ?m ?a ?ws => apply (n_u32arr_agree b0segs m m' a ws) in H; [| agx_side AG tac]
  | bytes_at _ ?m ?a ?bs => apply (bytes_at_agree b0segs m m' a bs) in H; [| agx_side AG tac]
  | KMem.bytes_at _ ?m ?a ?bs => apply (bytes_at_agree b0segs m m' a bs) in H; [| agx_side AG tac]
  | NMem.bytes_at _ ?m ?a ?bs => apply (bytes_at_agree b0segs m m' a bs) in H; [| agx_side AG tac]
  | ?T => fail 1 "agx: unknown chunk shape" T
  end end.

Section D10T.
Context {ACEIL__ : ACeil}.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis AF_DRV : forall Σ m, ART RT Σ m -> drv_consts m.
Hypothesis AF_PRIM : af_live_primary RT.
Hypothesis SMAL : stack_malloc_contract RT 0.
Hypothesis MAL : malloc_contract RT.

Theorem decompress10_cps : decompress10_contract RT.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m cx payload
         h0 nbu0 cf0 d0 r0 js b0 zp zn op on lo usp W
         FDO MST Ha0 TP CEQ RAE S0C DS10 STRM0 S10 PAY PLEN LIB0 DLIVE DPURE N0 TT0 L160 L40 FRMAX LIVEMAX CRED ART0 MI0 ST0 LOW LOR SPT AL.
  subst a0. intros T c Hc Hk.
  destruct DLIVE as (SLIV & ZLIV & ZLO & ZHI & OLIV & OLO & OHI & _ & _ & _ & (fS & kS & FSIN & FSLO & FSHI) & T8 & ZSH).
  pose proof DPURE as (LEN0 & DLEN0 & SM01 & NR & S16 & _ & _ & _ & SEP).
  pose proof SEP as (D1 & D2 & D3 & D4 & D5 & D6 & _). cbv zeta in D1, D2, D3, D4, D5, D6. unfold disj in D1, D2, D3, D4, D5, D6.
  destruct S10 as (BWF & BS & BSRC & BLEN & BDST & BDLEN & BZA & BZF & BOP & BAI & BAV & BTIL).
  pose proof DS10 as (HD0 & HW0 & NBU0 & NBR0 & CF0 & CFL0 & MID0 & MT0 & M160 & M40 & NIU0 & CCC0 & DR0 & SAVE0).
  destruct HW0 as (HSTRM & HST10 & HBB & HBL & HSM & HCBN & HVERB & HP1 & HP2 & HP3 & HSOL & HRN & HRT & HN & HOP).
  pose proof alloc_ceiling_range as ACR.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR. fold usp in SPR.
  unfold RT_STACK, DEC_STACK in LOR.
  destruct (dk_mod16_q _ AL) as [qsp ALQ].
  set (P := 32 * ((usp - 864) / 32)).
  assert (PF : lo + 65536 + 256 <= P /\ P + 864 <= usp /\ usp <= P + 880 /\ P mod 16 = 0 /\ P mod 32 = 0 /\ exists q, P = 32 * q).
  { subst P. split; [clear - ALQ LOR; Z.div_mod_to_equations; lia|]. split; [clear - ALQ; Z.div_mod_to_equations; lia|]. split; [clear - ALQ; Z.div_mod_to_equations; lia|].
    split; [clear; Z.div_mod_to_equations; lia|]. split; [clear; Z.div_mod_to_equations; lia|]. exists ((usp - 864) / 32). reflexivity. }
  destruct PF as (YPl4 & YPh & YPa & SPA & SP32 & qP & PQ).
  assert (YPl : lo <= P) by (clear - YPl4; lia).
  clearbody P.
  pose proof (AF_PRIM Σ m _ _ ART0 SLIV ltac:(clear; lia)) as IE. unfold SEGTOP_A in IE.
  destruct (fs_aconsts_of_art RT AF Σ m ART0) as [AC AU].
  pose proof (af_live_range RT AF Σ m _ _ ART0 SLIV) as (SL0 & SL1 & _). pose proof (af_live_offshadow RT AF Σ m _ _ ART0 SLIV) as SOFF.
  pose proof (af_live_range RT AF Σ m _ _ ART0 ZLIV) as (ZL0 & ZL1 & _).
  pose proof (af_frames_range RT AF Σ m _ _ ART0 FSIN) as (FS0 & FS1 & _). pose proof (af_frames_align RT AF Σ m _ _ ART0 FSIN) as (FS64 & FSSEG).
  pose proof (af_frames_hi RT AF Σ m _ _ ART0 FSIN) as FSOFF. unfold SEGTOP_A in FSSEG.
  pose proof (af_sp0_range RT AF Σ m ART0) as (_ & SP0T).
  set (S := b_s cx) in *. set (STRM := b_strm cx) in *. set (SRC := b_src cx) in *. set (len := b_len cx) in *.
  (* [comment removed for export] *)
  set (A1 := ACT ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m cx h0 b0 lo B0F_decK.DG1 B0F_decK.DSV payload P 0 0 0 0).
  eapply (l1_realizes RT AF Σ PMc _ T c MST Hc).
  eapply (B0F_dec_pro1.B0F_pro1 A1 P _ YPl YPh YPa AL ltac:(cbn [A1 a_lo]; clear - LOW CEQ ACR; lia) qP m); [exact PQ| exact ST0| exact (kmem_inv_N _ _ MI0)| exact AC| exact AU|].
  intros m1 jb ng jg b1 b2 FR FRT GEO NG ST1 NMI1 MU1 WM1. apply evt_done. clear Hc. intros c1 Hc1.
  cbn [A1 a_lo a_sp a_s2 a_s3 a_s4 a_s5 a_s7 a_s8 a_s9 a_s11] in FRT, GEO, ST1, MU1, Hc1. fold usp in GEO, MU1.
  assert (MU1k : KFrame.munch [(P, usp)] m m1) by exact MU1.
  assert (ART1 : ART RT Σ m1).
  { apply (art_of_munch RT AF Σ m m1 [(P, usp)] P ART0 ltac:(clear - LOW YPl; lia) MU1k WM1). per_interval. left. unfold USTACK_TOP in *. match goal with HX : _ <= _ < _ |- _ => clear - SPT HX YPl; lia end. }
  assert (MI1 : KMem.mem_inv bsegs m1).
  { apply (kmem_inv_munch' bsegs [(P, usp)] m m1 MI0 MU1k NMI1). intros x Hx. revert Hx. refine (not_outside_cons _ _ _ _ _ _ _); [intro| refine (not_outside_nil _ _)].
    unfold KMem.UTOP, USTACK_TOP in *. match goal with HX : _ <= _ < _ |- _ => clear - SPT HX; lia end. }
  pose proof (ck_intro P CStack) as KP. pose proof (ck_intro usp CStack) as KU. pose proof (ck_intro lo CStack) as KLO.
  (* [comment removed for export] *)
  refine (cps_realizes bsegs _ _ T c1 _ Hc1 _).
  { eapply (SMAL Σ PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 64 lo FDO MST ltac:(left; reflexivity) TP).
    - reflexivity.
    - change (fs_size 0) with 64. clear; lia.
    - reflexivity.
    - exact FRMAX.
    - unfold DEC10_COST in CRED. change (mcost 3600000) with 7216384 in CRED. clear - CRED. lia.
    - exact ART1.
    - exact MI1.
    - unfold call_ok. rewrite unsigned_lit by (clear - YPl YPh SPR LOW ACR CEQ; lia). unfold STACK_WIN, USTACK_TOP, RT_STACK in *.
      split; [exact ST1|]. split; [exact LOW|]. split; [clear - YPl4; lia|]. split; [clear - SPT YPh; lia| exact SPA]. }
  intros c2 (Σ1 & f & Hq2 & FRS1 & LV1 & SP1 & CR1 & FPOS & F64 & FTOP). change (fs_size 0) with 64 in *.
  destruct (ASTA_unpack RT Σ1 _ _ c2 Hq2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & WRF & WRS & ZSHF) & Hc2). clear Hq2.
  destruct RS2 as (u0 & u1 & u2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->).
  rewrite unsigned_lit in ST2, PRES2 by (clear - YPl YPh SPR LOW ACR CEQ; lia). change (64 - 8) with 56 in WRF. change (64 / 8) with 8 in WRS.
  rewrite (KMState.ret_pc_even 0xa9500 ltac:(lia) eq_refl) in Hc2.
  (* [comment removed for export] *)
  set (Wc := [(S, S + 64144); (STRM, STRM + 20)]).
  assert (WCL : forall x, ~ outside Wc x -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp x).
  { intros x Hx. unfold Wc in Hx. cbn [outside] in Hx. assert (C : (S <= x < S + 64144) \/ (STRM <= x < STRM + 20)) by (clear - Hx; lia). destruct C as [C|C].
    - right; right; left. exists S, 64144. split; [exact SLIV| exact C].
    - right; right; right; left. exists fS, kS. split; [exact FSIN| clear - C FSLO FSHI; lia]. }
  set (SHF := f / 8 + 2147450880). change (shad f) with SHF in WRS, ZSHF.
  destruct (act_setup RT AF Σ Σ1 m m2 0 f SHF 64 8 lo P usp Wc eq_refl eq_refl eq_refl eq_refl ART0 ART2 FRS1 LV1 SP1 LOW
              ltac:(unfold RT_STACK; clear - YPl4; lia) ltac:(clear - YPh; lia) SPT SPA WCL) as (G & SOK & _ & FSEG & FHI & SHR0 & SHR1 & GSELF & GLV).
  assert (ANF : sanchor f SHF) by (split; [clear - F64; Z.div_mod_to_equations; lia| reflexivity]).
  assert (INk : In (f, 0%nat) (rt_frames RT Σ1)) by (rewrite FRS1; left; reflexivity).
  pose proof (af_frames_disj RT AF Σ1 m2 f 0%nat fS kS [] (rt_frames RT Σ) ART2 FRS1 FSIN) as FFD. change (fs_size 0) with 64 in FFD.
  destruct (af_fshadow_apart RT AF Σ1 m2 f 0%nat ART2 INk) as (_ & FSF).
  pose proof (FSF fS kS ltac:(rewrite FRS1; right; exact FSIN)) as FSD. change (shad f) with SHF in FSD.
  replace (shad (f + fs_size 0)) with (SHF + 8) in FSD by (unfold shad, SHB, SHF; change (fs_size 0) with 64; clear - F64; Z.div_mod_to_equations; lia).
  clearbody SHF. unfold SEGTOP_A in FSEG.
  set (SHS := S / 8 + 2147450880). assert (ANS : sanchor S SHS) by (split; [clear - S16; Z.div_mod_to_equations; lia| reflexivity]). clearbody SHS.
  set (SHT := STRM / 8 + 2147450880). assert (ANT : sanchor STRM SHT) by (split; [exact T8| reflexivity]).
  assert (ZSH' : bytes_at b0segs m SHT (repeat z8 10)) by exact ZSH.
  assert (SHTR : 0x7fff8000 <= SHT /\ SHT + 10 <= 0x10007fff8000).
  { unfold USTACK_TOP, STACK_WIN in *. subst SHT. clear - FS0 FS1 FSLO FSHI SP0T. Z.div_mod_to_equations. lia. }
  destruct (GLV _ _ SLIV) as (GS1 & GS2 & _). destruct (GLV _ _ ZLIV) as (GZ1 & GZ2 & _).
  set (A := ACT ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F2 fc2 m2 cx h0 b0 lo B0F_decK.DG1 B0F_decK.DSV payload P f SHS SHT SHF).
  (* [comment removed for export] *)
  set (SES := fun x => (S <= x < S + 64144) \/ (STRM <= x < STRM + 80) \/ (SRC <= x < SRC + len) \/ (SHT <= x < SHT + 10)).
  assert (SESLO : forall x, SES x -> 0 < x < lo).
  { intros x [C|[C|[C|C]]]; [clear - C SL0 SL1 LOW; lia| clear - C FS0 FS1 FSLO FSHI LOW; lia| clear - C ZL0 ZL1 ZLO ZHI LOW; lia| clear - C SHTR LOW CEQ ACR; lia]. }
  assert (SHTC : forall x, SHT <= x < SHT + 10 -> in_fframe_shadow (rt_frames RT Σ) x).
  { intros x Hx. exists fS, kS. split; [exact FSIN|]. unfold shad, SHB. subst SHT.
    pose proof FSHI as FSHI'. revert FSHI'. generalize (fs_size kS). intros fsz FSHI'. clear - Hx FSLO FSHI' FS64 T8. Z.div_mod_to_equations. lia. }
  assert (SESCL : forall spx x, SES x -> aclient (rt_live RT Σ) (rt_frames RT Σ) spx x).
  { intros spx x [C|[C|[C|C]]].
    - right; right; left. exists S, 64144. split; [exact SLIV| exact C].
    - right; right; right; left. exists fS, kS. split; [exact FSIN| clear - C FSLO FSHI; lia].
    - right; right; left. exists zp, zn. split; [exact ZLIV| clear - C ZLO ZHI; lia].
    - right; right; right; right. exact (SHTC x C). }
  assert (AG02 : agree_on SES m m2).
  { apply (agree_trans _ m m1 m2).
    - apply (agree_of_nmunch [(P, usp)] m m1 _ MU1). intros x Hx. cbn [KFrame.outside NFrame.outside outside]. pose proof (SESLO x Hx) as B. split; [clear - B YPl; lia| exact I].
    - exact (agree_of_pres _ _ _ m1 m2 _ PRES2 (SESCL P)). }
  assert (DS2 : dstate10A m2 S STRM (b_small cx) h0 nbu0 cf0 d0 r0 js).
  { apply (dstate10A_agree m m2 _ _ _ _ _ _ _ _ _ DS10). eapply agree_sub; [exact AG02|]. intros x Hx. left. exact Hx. }
  assert (STRM2 : rw_cells b0segs m2 STRM (STRM_CELLS b0)) by (pose proof STRM0 as X; agx AG02 X ltac:(fun H => right; left; clear - H; lia); exact X).
  assert (PAY2 : bytes_at b0segs m2 SRC payload) by (pose proof PAY as X; agx AG02 X ltac:(fun H => right; right; left; clear - H PLEN; lia); exact X).
  assert (ZSH2 : bytes_at b0segs m2 SHT (repeat z8 10)) by (pose proof ZSH' as X; agx AG02 X ltac:(fun H => right; right; right; rewrite repeat_length in H; clear - H; lia); exact X).
  assert (LIB1 : OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_libA.TwinB__.LIB_A m1) by (apply (B0_sessK.lib_of_munch [(P, usp)] m m1 LIB0 MU1); intros x Hx; cbn [outside]; split; [clear - Hx YPl LOW CEQ ACR; lia| exact I]).
  assert (LIB2 : OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_libA.TwinB__.LIB_A m2) by (apply (lib_of_pfp _ _ _ [] m1 m2 LIB1 (pfp_of_pres _ _ _ [] m1 m2 PRES2)); intros x _; exact I).
  (* [comment removed for export] *)
  assert (STEP2 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) P [] m1 m2) by exact (pfp_of_pres _ _ _ [] m1 m2 PRES2).
  clear ST1. unfold FT_REGS in FRT. cbn [A1 a_s11 a_s10 a_s9 a_s8 a_s7 a_s6 a_s5 a_s4 a_s3 a_s2 a_s1 a_s0 a_ra] in FRT.
  xfer_rt G I STEP2 WM2 m1 m2.
  destruct (n_wr_at_rw_CB m2 f 56 WRF ltac:(clear; lia)) as (jf & FFJ). destruct (n_wr_at_rw_CB m2 SHF 8 WRS ltac:(clear; lia)) as (jsh & FSJ).
  destruct (release_inline2 AF G (mi := m2) Σ1 m2 eq_refl SOK ART2) as (_ & fl & _ & FLP & _). replace (f + 64 - 8) with (f + 56) in FLP by (clear; lia).
  (* [comment removed for export] *)
  pose proof (ag_gfr G) as (FB0 & FB1). rewrite <- CEQ in FB1.
  assert (GL : g10_lin A).
  { unfold g10_lin. cbn [A a_cx a_fb a_shf a_lo a_P a_sp]. fold S STRM usp. rewrite <- CEQ in SL1, FS1.
    clear - SL0 SL1 FS0 FS1 FSLO FSHI FB0 FB1 SHR0 SHR1 LOW CEQ YPl4 SPR YPh YPa. repeat split; lia. }
  assert (DFT : f + 64 <= STRM \/ STRM + 80 <= f) by (clear - FFD FSLO FSHI; lia).
  assert (OFFT : STRM + 80 <= 0x7fff7000 \/ 0x10007fff8000 <= STRM) by (clear - FSOFF FSLO FSHI; lia).
  assert (OFFP : 0x10007fff8000 <= P) by (clear - YPl4 LOW CEQ ACR; lia).
  assert (SEPshs : SHF + 8 <= S \/ S + 64144 <= SHF) by (clear - GS2; lia).
  assert (SEPsht : SHF + 8 <= STRM \/ STRM + 80 <= SHF) by (clear - FSD FSLO FSHI; lia).
  assert (SLIV1 : In (S, 64144) (rt_live RT Σ1)) by (rewrite LV1; exact SLIV). assert (ZLIV1 : In (zp, zn) (rt_live RT Σ1)) by (rewrite LV1; exact ZLIV).
  destruct (d10_readers RT AF Σ1 m2 A zp zn ART2 SLIV1 ZLIV1 ZLO ZHI ltac:(cbn [A a_cx]; fold S; clear - S16; Z.div_mod_to_equations; lia) ANT ANF ltac:(cbn [A a_cx]; fold STRM; clear - FS0 FSLO; lia)
              ltac:(cbn [A a_cx]; fold STRM; clear - FS1 FSHI CEQ ACR; lia) ZSH2 OFFT FHI OFFP GS1 DFT GZ1) as (SHs2 & SHt2 & SHp2).
  pose proof DS2 as (HD2 & _ & NBU3 & _ & CF3 & _ & MID3 & _ & _ & _ & _ & _ & DR2 & SAVE2).
  eapply (l1_realizes RT AF Σ1 PMc _ T c2 MST Hc2).
  eapply (B0F_g10_P2 A _ GL ANS ANF GS1 GSELF SEPshs m2 h0 jb jf jsh js fl ng jg F2 fc2);
    [exact SHs2| exact HD2| exact HST10| exact HP1| exact SAVE2| exact FR| exact FRT| exact GEO| exact NG| exact FFJ| exact (ro_C8_KN m2 _ _ FLP)| exact FSJ| exact ST2| exact (kmem_inv_N _ _ MI2)|].
  clear Hc2 SHs2 SHt2 SHp2 HD2 FR FFJ FSJ SAVE2.
  intros m4 w0 w8 w16 w24 w32 w40 w48 w56 w736 w744 y11 y12 y13 y14 y15 y16 HD3 SV4 FL4 FH4 AFR4 ST4n NMI4 MU4 WM4 MU4p. apply evt_done. intros c4 Hc4.
  cbn [A a_cx a_P a_fb a_shf a_shs a_lo a_sp] in HD3, SV4, FL4, FH4, ST4n, Hc4. fold S STRM in HD3, SV4, FL4, FH4, Hc4.
  unfold W10p2 in MU4p. cbn [A a_cx a_P a_fb a_shf] in MU4p. fold S in MU4p.
  destruct (after_l1 AF G Σ1 _ m2 m4 SOK ART2 MI2 ST2 (presi_refl _ _ _ _ m2) NMI4 MU4p WM4
              ltac:(per_interval; [right; right; right| left| right; left| right; right; left];
                    match goal with HX : _ <= _ < _ |- _ => first [clear - HX YPh; lia| unfold Wc; cbn [outside]; clear - HX; lia] end)) as (ART4 & MI4 & ST4 & PR4 & STEP4).
  (* [comment removed for export] *)
  assert (SESOUT : forall x, SES x -> outside [(P, P + 760); (f, f + 56); (SHF, SHF + 8)] x).
  { intros x Hx. pose proof (SESLO x Hx) as B. cbn [outside]. split; [clear - B YPl; lia|]. destruct Hx as [C|[C|[C|C]]].
    - split; [clear - C GS1; lia|]. split; [clear - C GS2; lia| exact I].
    - split; [clear - C DFT; lia|]. split; [clear - C SEPsht; lia| exact I].
    - split; [clear - C GZ1 ZLO ZHI; lia|]. split; [clear - C GZ2 ZLO ZHI; lia| exact I].
    - split; [clear - C FHI SHTR; lia|]. split; [| exact I]. destruct ANF as [F8 EF]. subst SHT. rewrite EF. clear - C DFT F8 T8. Z.div_mod_to_equations. lia. }
  assert (AG24 : agree_on (fun x => SES x /\ ~ (S + 64036 <= x < S + 64144)) m2 m4).
  { apply (agree_of_nmunch _ m2 m4 _ MU4p). intros x Hx. cbv beta in Hx. destruct Hx as [Hx N]. pose proof (SESOUT x Hx) as O. cbn [outside] in O |- *. split; [clear - N; lia| exact O]. }
  agx AG24 NBU3 ltac:(fun H => split; [left; clear - H; lia| clear - H; lia]).
  agx AG24 CF3 ltac:(fun H => rewrite CFL0 in H; split; [left; clear - H; lia| clear - H; lia]).
  agx AG24 MID3 ltac:(fun H => split; [left; clear - H; lia| clear - H; lia]).
  assert (DR4 : drest_at b0segs m4 S r0).
  { apply (drest_agree m2 m4 S r0 _ DR2 AG24). intros x Hx. split; [left; clear - Hx; lia| clear - Hx; lia]. }
  pose proof STRM2 as STRM3. agx AG24 STRM3 ltac:(fun H => split; [right; left; clear - H; lia| clear - H D1; lia]).
  pose proof PAY2 as PAY3. agx AG24 PAY3 ltac:(fun H => split; [right; right; left; clear - H PLEN; lia| clear - H D2 PLEN; lia]).
  pose proof ZSH2 as ZSH3. agx AG24 ZSH3 ltac:(fun H => rewrite repeat_length in H; split; [right; right; right; clear - H; lia| clear - H SHTR SOFF; lia]).
  assert (LIB4 : OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_libA.TwinB__.LIB_A m4) by (apply (B0_sessK.lib_of_munch _ m2 m4 LIB2 MU4p); intros x Hx; cbn [outside]; clear - Hx IE OFFP FSEG SHR0; lia).
  unfold USTACK_TOP, STACK_WIN in SP0T.
  (* [comment removed for export] *)
  assert (CLS : forall (Σx : rts RT) x, sig_ok RT (rt_sp0 RT Σ) true 0 f (rt_frames RT Σ) (rt_live RT Σ) Σx ->
            SES x \/ (P <= x < usp) \/ (f <= x < f + 56) \/ (SHF <= x < SHF + 8) -> aclient (rt_live RT Σx) (rt_frames RT Σx) P x).
  { intros Σx x SKx [C|[C|[C|C]]].
    - exact (acl_caller G Σx x SKx (SESCL usp x C)).
    - apply (acl_stack RT P Σx x). unfold USTACK_TOP. clear - C SPT. unfold USTACK_TOP in SPT. lia.
    - apply (acl_frame G Σx x SKx). clear - C. lia.
    - apply (acl_shadow G Σx x SKx). exact C. }
  (* [comment removed for export] *)
  assert (GSrc : 0 < SRC /\ SRC + len <= alloc_ceiling /\ 0 <= len < 2 ^ 27 /\ Z.of_nat (length payload) = len).
  { rewrite <- CEQ in ZL1. change (2 ^ 27) with 134217728. clear - ZL0 ZL1 ZLO ZHI LEN0 PLEN. repeat split; lia. }
  destruct (d10_readers RT AF Σ1 m4 A zp zn ART4 SLIV1 ZLIV1 ZLO ZHI ltac:(cbn [A a_cx]; fold S; clear - S16; Z.div_mod_to_equations; lia) ANT ANF ltac:(cbn [A a_cx]; fold STRM; clear - FS0 FSLO; lia)
              ltac:(cbn [A a_cx]; fold STRM; clear - FS1 FSHI CEQ ACR; lia) ZSH3 OFFT FHI OFFP GS1 DFT GZ1) as (SHs4 & SHt4 & SHp4).
  assert (BAI' : bs_ai b0 = len) by (rewrite BAI; exact BLEN).
  assert (W10C : forall x, ~ KFrame.outside (W10 A) x -> (P <= x < usp) \/ (f <= x < f + 64 - 8) \/ (SHF <= x < SHF + 8) \/ ~ outside Wc x).
  { unfold W10. cbn [A a_cx a_P a_fb a_shf]. fold S STRM. per_interval; [right; right; right| right; right; right| right; right; right| left| right; left| right; right; left];
      match goal with HX : _ <= _ < _ |- _ => first [clear - HX YPh; lia| unfold Wc; cbn [outside]; clear - HX; lia] end. }
  (* [comment removed for export] *)
  set (SESP := fun x => (S + 68 <= x < S + 64036) \/ (STRM + 20 <= x < STRM + 80) \/ (SRC <= x < SRC + len) \/ (SHT <= x < SHT + 10)).
  assert (SESPOUT : forall x, SESP x -> outside (W10 A) x).
  { intros x Hx. assert (SX : SES x) by (destruct Hx as [C|[C|[C|C]]]; [left; clear - C; lia| right; left; clear - C; lia| right; right; left; exact C| right; right; right; exact C]).
    pose proof (SESOUT x SX) as (O1 & O2 & O3 & _). unfold W10. cbn [A a_cx a_P a_fb a_shf outside]. fold S STRM.
    split; [destruct Hx as [C|[C|[C|C]]]; [clear - C; lia| clear - C D1; lia| clear - C D2; lia| clear - C SHTR SOFF; lia]|].
    split; [destruct Hx as [C|[C|[C|C]]]; [clear - C; lia| clear - C D1; lia| clear - C D2; lia| clear - C SHTR SOFF; lia]|].
    split; [destruct Hx as [C|[C|[C|C]]]; [clear - C D1; lia| clear - C; lia| clear - C D4; lia| clear - C SHTR OFFT; lia]|].
    split; [exact O1|]. split; [exact O2|]. split; [exact O3| exact I]. }
  (* [comment removed for export] *)
  assert (HOV : forall (Σk : rts RT) (mk : mem) (Fk : bvmap 5 word) (fck : bv 32) (uc tt l16 l4 : Z) (rest : list Z) (k : blk) (dH : dsm) ck
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x23 x24 x25 x28 x29 x30 x31 v0 v8 v16 v24 v32 v40 v48 v56 v736 v744 : word),
    sig_ok RT (rt_sp0 RT Σ) true 0 f (rt_frames RT Σ) (rt_live RT Σ) Σk -> rt_live RT Σk = dblocks (uc - 48) tt l16 l4 ++ rt_live RT Σ ->
    rt_credit RT Σ - DEC10_COST <= rt_credit RT Σk <= rt_credit RT Σ - 1 ->
    ART RT Σk mk -> KMem.mem_inv bsegs mk -> PRESI usp (rt_frames RT Σ) (rt_live RT Σ) Wc m2 mk ->
    map bv_unsigned payload = 66 :: 90 :: 104 :: uc :: rest -> 49 <= uc <= 57 ->
    dpureA (cx_blocks cx (uc - 48) tt l16 l4) -> dblocks_ok (b_small cx) (uc - 48) tt l16 l4 -> blk_at b0segs mk (cx_blocks cx (uc - 48) tt l16 l4) k ->
    rw_cells b0segs mk S (HEAD_CELLS (g10_hd h0 13 (((66 * 256 + 90) * 256 + 104) * 256 + uc) 0 (uc - 48))) ->
    rw_cells b0segs mk (S + 1092) [C4 (Z_to_bv 64 nbu0)] -> u32arr b0segs mk (S + 1096) cf0 ->
    rw_cells b0segs mk (S + 3152) (MID_CELLS dH) -> sm_tt dH = tt -> sm_ll16 dH = l16 -> sm_ll4 dH = l4 -> sm_cccrc dH = Z_to_bv 64 0 ->
    rw_cells b0segs mk (S + 64036) SAVE0_CELLS -> drest_at b0segs mk S r0 ->
    rw_cells b0segs mk STRM (STRM_CELLS (bupd b0 (len - 4) (Z_to_bv 64 4) (bs_tih b0))) ->
    bytes_at b0segs mk SRC payload -> OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_libA.TwinB__.LIB_A mk -> bytes_at b0segs mk SHT (repeat z8 10) ->
    B0FL A mk v0 v8 v16 v24 v32 v40 v48 v56 (Z_to_bv 64 (S + 7884)) (Z_to_bv 64 (S + 3160)) (Z_to_bv 64 (S + 3192)) (Z_to_bv 64 (S + 3176)) (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (S + 8)) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (S + 2047)) ->
    B0FH A mk (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 SHS) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 f) (Z_to_bv 64 (S + 7820)) (Z_to_bv 64 0) (Z_to_bv 64 (SHS + 1)) (Z_to_bv 64 0) (Z_to_bv 64 0) v736 v744 (Z_to_bv 64 f) ->
    aframe A mk -> stk bsegs mk lo P ->
    ASTA RT Σk PMc (eq (MS (mkR x1 (Z_to_bv 64 P) gp tp x5 x6 x7 sp (Z_to_bv 64 P) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 (S + 64036)) x21 (Z_to_bv 64 2147450880)
                               x23 x24 x25 (Z_to_bv 64 S) (Z_to_bv 64 SHF) x28 x29 x30 x31) Fk (Z_to_bv 64 0xaa7cc) fck None mk (seg_rom b0segs))) ck ->
    realizes bsegs ck T).
  { intros Σk mk Fk fck uc tt l16 l4 rest k dH ck x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x23 x24 x25 x28 x29 x30 x31 v0 v8 v16 v24 v32 v40 v48 v56 v736 v744.
    intros SOKk LVk CRk ARTk MIk PRk PAYEQ UC DPk DBk BLKk HDk NBUk CFk MIDk ET E16 E4 ECC SVk DRk STRMk PAYk LIBk ZSHk FLk FHk AFRk STk Hck.
    set (n := uc - 48) in *. set (cx1 := cx_blocks cx n tt l16 l4) in *.
    assert (N19 : 1 <= n <= 9) by (unfold n; clear - UC; lia).
    assert (NB : (b_small cx = 0 /\ tt <> 0 /\ l16 = 0 /\ l4 = 0) \/ (b_small cx = 1 /\ tt = 0 /\ l16 <> 0 /\ l4 <> 0)) by (destruct DBk as [(E & _)|(_ & D)]; [exfalso; clear - E N19; lia| exact D]).
    set (bH := bupd b0 (len - 4) (Z_to_bv 64 4) (bs_tih b0)).
    set (A2 := ACT ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Fk fck mk cx1 (dk_ph_h0 cx1) bH lo B0F_decK.DG1 B0F_decK.DSV payload P f SHS SHT SHF).
    set (LIVEK := dblocks n tt l16 l4 ++ rt_live RT Σ) in *.
    assert (INK : forall e, In e (rt_live RT Σ) -> In e LIVEK) by (intros e He; apply in_or_app; right; exact He).
    assert (TLK : b_small cx = 0 -> In (tt, 400000 * n) LIVEK).
    { intros E. destruct NB as [(_ & TN & -> & ->)|(E1 & _)]; [| exfalso; clear - E E1; lia]. apply in_or_app. left. unfold dblocks. rewrite (proj2 (Z.eqb_neq tt 0) TN). cbn. left. reflexivity. }
    assert (LLK : b_small cx = 1 -> In (l16, 200000 * n) LIVEK /\ In (l4, 50000 * n) LIVEK).
    { intros E. destruct NB as [(E0 & _)|(_ & -> & N16 & N4)]; [exfalso; clear - E E0; lia|]. unfold LIVEK, dblocks. rewrite (proj2 (Z.eqb_neq l16 0) N16), (proj2 (Z.eqb_neq l4 0) N4). cbn.
      split; [right; left; reflexivity| left; reflexivity]. }
    assert (NZF : b_small cx1 = 0 -> b_tt cx1 <> 0) by (cbn [cx1 cx_blocks b_small b_tt]; intros E; destruct NB as [(_ & TN & _)|(E1 & _)]; [exact TN| exfalso; clear - E E1; lia]).
    assert (NZS : b_small cx1 = 1 -> b_ll16 cx1 <> 0 /\ b_ll4 cx1 <> 0) by (cbn [cx1 cx_blocks b_small b_ll16 b_ll4]; intros E; destruct NB as [(E0 & _)|(_ & _ & N16 & N4)]; [exfalso; clear - E E0; lia| exact (conj N16 N4)]).
    assert (FRSk : rt_frames RT Σk = (f, 0%nat) :: rt_frames RT Σ) by exact (proj1 SOKk).
    assert (AOK2 : act_ok BIHI0 A2).
    { apply (dec_act_ok RT AF Σk mk A2 zp zn op on (rt_frames RT Σ) fS kS ARTk ltac:(rewrite (proj1 (proj2 SOKk)); exact CEQ) FRSk FSIN FSLO FSHI T8);
        cbn [A2 a_cx a_lo a_P a_sp a_h0 a_b0 a_payload a_shs a_sht a_shf a_fb cx1 cx_blocks b_s b_strm b_src b_len b_dst b_dlen b_small b_n b_tt b_ll16 b_ll4]; fold S STRM SRC len; rewrite ?LVk; fold LIVEK.
      - exact (INK _ SLIV). - exact (INK _ ZLIV). - exact ZLO. - exact ZHI. - exact (INK _ OLIV). - exact OLO. - exact OHI.
      - intros TN. apply TLK. destruct NB as [(E & _)|(_ & E & _)]; [exact E| exfalso; exact (TN E)].
      - intros N16. destruct NB as [(_ & _ & E & _)|(E & _)]; [exfalso; exact (N16 E)| exact (proj1 (LLK E))].
      - intros N4. destruct NB as [(_ & _ & _ & E)|(E & _)]; [exfalso; exact (N4 E)| exact (proj2 (LLK E))].
      - exact DPk. - exact (proj1 N19). - exact NZF. - exact NZS. - exact ANS. - exact ANT. - exact ANF.
      - clear - LOW CEQ; lia. - clear - YPl4; lia. - fold usp. clear - YPh YPa; lia. - exact SP32.
      - unfold dsh_wf, dk_ph_h0. cbn. repeat split; try reflexivity; clear - N19; lia.
      - unfold bzs_wf, bH, bupd in *. cbn [bs_q1 bs_q2 bs_ai bs_len bs_av bs_dlen]. pose proof (f_equal (@length Z) PAYEQ) as LP. rewrite length_map in LP. cbn [length] in LP.
        fold len in BLEN. clear - BWF BLEN PLEN LP. lia.
      - exact PLEN. - reflexivity. - reflexivity. - unfold dk_ph_h0. cbn [sh_small]. apply unsigned_lit8. clear - SM01; lia.
      - exact BS. - exact BSRC. - exact BLEN. - exact BDST. - exact BDLEN. }
    (* [comment removed for export] *)
    set (Wc2 := Wc ++ blk_ivls cx1).
    assert (BLKC : forall x, ~ outside (blk_ivls cx1) x -> exists p nn, In (p, nn) (dblocks n tt l16 l4) /\ p <= x < p + nn).
    { intros x Hx. unfold blk_ivls in Hx. cbn [cx1 cx_blocks b_small b_tt b_ll16 b_ll4 b_n] in Hx.
      destruct NB as [(E & TN & -> & ->)|(E & -> & N16 & N4)]; rewrite E in Hx; cbn [Z.eqb outside] in Hx; unfold dblocks.
      - rewrite (proj2 (Z.eqb_neq tt 0) TN). cbn. exists tt, (400000 * n). split; [left; reflexivity| clear - Hx; lia].
      - rewrite (proj2 (Z.eqb_neq l16 0) N16), (proj2 (Z.eqb_neq l4 0) N4). cbn.
        assert (C : (l16 <= x < l16 + 200000 * n) \/ (l4 <= x < l4 + 50000 * n)) by (clear - Hx; lia).
        destruct C as [C|C]; [exists l16, (200000 * n); split; [right; left; reflexivity| exact C]| exists l4, (50000 * n); split; [left; reflexivity| exact C]]. }
    assert (WCL2 : forall x, ~ outside Wc2 x -> aclient LIVEK (rt_frames RT Σ) usp x).
    { intros x Hx. destruct (outside_dec (blk_ivls cx1) x) as [O|O].
      - assert (HW : ~ outside Wc x).
        { intros OW. apply Hx. unfold Wc2, Wc. cbn [app outside]. unfold Wc in OW. cbn [outside] in OW. destruct OW as (O1 & O2 & _). split; [exact O1| split; [exact O2| exact O]]. }
        apply (aclient_mono _ _ usp _ _ usp x (WCL x HW)); [exact INK| intros e He; exact He| apply Z.le_refl].
      - destruct (BLKC x O) as (p & nn & IN & R). right; right; left. exists p, nn. split; [apply in_or_app; left; exact IN| exact R]. }
    destruct (act_geom_ext RT AF _ _ _ _ _ _ _ _ _ _ _ _ _ Σk mk (dblocks n tt l16 l4) Wc2 G SOKk ARTk LVk WCL2) as (G2 & SOK2).
    fold LIVEK in G2, SOK2.
    (* [comment removed for export] *)
    assert (BLKR : forall x, ~ outside (blk_ivls cx1) x -> 0 < x < lo /\ (x < 0x10000 \/ 0x62b000 <= x) /\ (x < 0x7fff7000 \/ 0x10007fff8000 <= x)).
    { intros x Hx. destruct (BLKC x Hx) as (p & nn & IN & R). assert (INL : In (p, nn) (rt_live RT Σk)) by (rewrite LVk; apply in_or_app; left; exact IN).
      pose proof (af_live_range RT AF Σk mk _ _ ARTk INL) as (B0 & B1 & B2). pose proof (af_live_offshadow RT AF Σk mk _ _ ARTk INL) as B3.
      rewrite (proj1 (proj2 SOKk)) in B1. unfold SEGTOP_A in B2. clear - R B0 B1 B2 B3 LOW. lia. }
    assert (WCOUT2 : forall x, (0x10000 <= x < 0x62b000) \/ (0x7fff7000 <= x < 0x10007fff8000) -> outside Wc2 x).
    { intros x Hx. unfold Wc2, Wc. cbn [app outside]. split; [clear - Hx IE SOFF; lia|]. split; [clear - Hx FSSEG FSOFF FSLO FSHI; lia|].
      destruct (outside_dec (blk_ivls cx1) x) as [O|O]; [exact O| exfalso]. pose proof (BLKR x O) as B. clear - Hx B. lia. }
    assert (KZSH2 : forall m', PRESI usp (rt_frames RT Σ) LIVEK Wc2 mk m' -> bytes_at b0segs m' SHT (repeat z8 10)).
    { intros m' PR. apply (bytes_at_agree b0segs mk m' SHT _ ZSHk). intros a Ha. cbv beta in Ha. rewrite repeat_length in Ha. change (Z.of_nat 10) with 10 in Ha.
      apply PR. split; [right; right; right; right; exact (SHTC _ Ha)| apply WCOUT2; right; clear - Ha SHTR; lia]. }
    assert (KLIB2 : forall m', PRESI usp (rt_frames RT Σ) LIVEK Wc2 mk m' -> OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_libA.TwinB__.LIB_A m').
    { intros m' PR. apply (OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_libA.TwinB__.LIB_locA mk m' LIBk). intros a (lo' & hi' & HIn & Hx). refine (PR a _).
      assert (R : 857056 <= bv_unsigned a < 858080 \/ 858336 <= bv_unsigned a < 858392 \/ 858432 <= bv_unsigned a < 860480).
      { unfold OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_libiface.TwinB__.LIB_FP in HIn. cbn [In] in HIn. destruct HIn as [HI|[HI|[HI|[]]]]; injection HI as <- <-; [left| right; left| right; right]; exact Hx. }
      clear HIn Hx. split; [right; left; exact (lib_static _ R)| apply WCOUT2; left; clear - R; lia]. }
    (* [comment removed for export] *)
    set (hH := g10_hd h0 13 (((66 * 256 + 90) * 256 + 104) * 256 + uc) 0 (uc - 48)) in *.
    pose proof (BzDU10M.dec10_ok' (DecCutF10.jd_of hH nbu0 cf0 dH r0 k) (b_small cx) (b_dlen cx) uc rest UC) as E10. unfold BzDU10M.s10 in E10. rewrite <- PAYEQ in E10.
    pose proof (BzDU5.BzDRv.decompress_rv (dst_init (DecCutF10.jd_of hH nbu0 cf0 dH r0 k) 0 (b_small cx)) (dstrm_init (map bv_unsigned payload) (b_dlen cx))) as RV. rewrite E10 in RV.
    set (Fh := (9 * length rest + 92)%nat) in *.
    set (R0 := drun Fh 14 dsv_zero (d14 (DecCutF10.jd_of hH nbu0 cf0 dH r0 k) (b_small cx) uc) (s14 rest (b_dlen cx))) in *.
    assert (HK2 : forall c' (Σ2 : rts RT) (m' : mem) (rv : Z) (L : dsv) (d' : dst) (s' : dstrm) (J' : jk)
        (z0 z1 z2 h1 h2 h3 h4 h5 h6 h7 z3 z4 z5 z6 : word) F' fc',
      DRet rv L d' s' = R0 ->
      ASTA RT Σ2 PMc (eq (MS (mkR ra sp gp tp z0 z1 z2 s0 s1 (Z_to_bv 64 rv) h1 h2 h3 h4 h5 h6 h7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 z3 z4 z5 z6)
                             F' (ret_pc ra) fc' None m' (seg_rom b0segs))) c' ->
      rt_frames RT Σ2 = rt_frames RT Σ -> rt_live RT Σ2 = LIVEK -> rt_sp0 RT Σ2 = rt_sp0 RT Σ -> rt_credit RT Σ2 = rt_credit RT Σk ->
      ART RT Σ2 m' -> KMem.mem_inv bsegs m' -> stk bsegs m' lo usp -> PRESI usp (rt_frames RT Σ) LIVEK Wc2 mk m' ->
      dmem DI_B0 cx1 B0F_decK.DG1 B0F_decK.DSV payload m' (dvF cx1 J' (d_set_sv d' L) s') ->
      dpureF cx1 bH payload J' (d_set_sv d' L) s' -> dpost14 (d_set_sv d' L) ->
      realizes bsegs c' T).
    { intros c' Σ2 m' rv L d' s' J' z0 z1 z2 h1 h2 h3 h4 h5 h6 h7 z3 z4 z5 z6 F' fc' ER Hc' FRS2 LV2 SP2 CR2 ART' MI' ST' PR' DM' DP' DPO'.
      apply Hk. exists Σ2, n, tt, l16, l4. split; [| split; [exact LV2| split; [exact FRS2| split; [exact SP2| rewrite CR2; exact CRk]]]].
      eapply ASTA_conseq; [exact Hc'|]. intros ms <-. exists m', z0, z1, z2, h1, h2, h3, h4, h5, h6, h7, z3, z4, z5, z6, F', fc', (DecCutF10.jd_of hH nbu0 cf0 dH r0 k).
      cbv zeta. rewrite E10. rewrite <- ER in RV |- *. cbn [dfin] in RV |- *. fold cx1.
      split; [reflexivity|]. split; [exact ART'|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact (KLIB2 m' PR')|].
      split. { unfold dliveA. rewrite LV2. cbn [cx1 cx_blocks b_s b_strm b_src b_len b_dst b_dlen b_small b_n b_tt b_ll16 b_ll4]. fold S STRM SRC len.
               split; [exact (INK _ SLIV)|]. split; [exact (INK _ ZLIV)|]. split; [exact ZLO|]. split; [exact ZHI|]. split; [exact (INK _ OLIV)|]. split; [exact OLO|]. split; [exact OHI|].
               split; [intros TN; apply TLK; destruct NB as [(E & _)|(_ & E & _)]; [exact E| exfalso; exact (TN E)]|].
               split; [intros N16; destruct NB as [(_ & _ & E & _)|(E & _)]; [exfalso; exact (N16 E)| exact (proj1 (LLK E))]|].
               split; [intros N4; destruct NB as [(_ & _ & _ & E)|(E & _)]; [exfalso; exact (N4 E)| exact (proj2 (LLK E))]|].
               split; [exists fS, kS; split; [rewrite FRS2; exact FSIN| split; [exact FSLO| exact FSHI]]| split; [exact T8| exact (KZSH2 m' PR')]]. }
      split; [exact DPk|]. split; [exact DBk|].
      split.
      - left. exists J'. split; [exact (dmemL_of m' cx1 _ _ _ _ DM')|].
        split; [apply (B0F_g10K.g10_dpureF_bupd cx1 b0 (len - 4) (Z_to_bv 64 4) (bs_tih b0) payload J' _ s' DP'); fold len in BAI'; clear - BAI'; lia|].
        split; [| exact (proj1 N19)].
        unfold dpost14W. split; [intros E2; exact (DPO' E2)|]. split; [| exact RV].
        intros _. pose proof (dpureF_rep _ _ _ _ _ _ DP') as RP. unfold drep in RP. change (2^32) with 4294967296 in RP. exact (proj1 (proj2 (proj2 (proj2 (proj2 RP))))).
      - assert (PRF : PRESI usp (rt_frames RT Σ) (rt_live RT Σ) Wc m2 m').
        { apply (presi_compose usp (rt_frames RT Σ) (rt_live RT Σ) Wc (dblocks n tt l16 l4) Wc2 m2 mk m' PRk PR'). intros x CA OW. unfold Wc2, Wc. cbn [app outside].
          unfold Wc in OW. cbn [outside] in OW. destruct OW as (O1 & O2 & _). split; [exact O1|]. split; [exact O2|].
          destruct (outside_dec (blk_ivls cx1) x) as [O|O]; [exact O| exfalso]. destruct (BLKC x O) as (p & nn & IN & R).
          exact (newlive_not_caller RT AF Σk mk _ _ usp _ p nn ARTk LVk IN ltac:(intros e He; rewrite FRSk; right; exact He) ltac:(rewrite (proj1 (proj2 SOKk)); clear - LOW LOR; lia) x R CA). }
        exact (pres_final RT AF Σ lo P usp Wc m m1 m2 m' ART0 LOW YPl ltac:(clear - YPh; lia) MU1 PRES2 PRF). }
    (* [comment removed for export] *)
    assert (IV2 : INV RT A2 (rt_sp0 RT Σ) (rt_frames RT Σ) LIVEK Wc2 mk (rt_credit RT Σk) Σk mk).
    { unfold INV. cbn [A2 a_sp a_fb]. split; [exact SOK2|]. split; [exact LVk|]. split; [reflexivity|]. split; [exact ARTk|]. split; [exact MIk| apply presi_refl]. }
    assert (H14 : B0F_cut_H14 A2 (QL RT PMc T Σk R0) Fh).
    { refine (dec_H14 RT AF AF_DRV A2 (rt_sp0 RT Σ) (rt_frames RT Σ) LIVEK Wc2 G2 mk PMc MST T AOK2 eq_refl eq_refl _ _ zp zn fS kS
                (INK _ SLIV) (INK _ ZLIV) ZLO ZHI TLK LLK FSIN FSLO FSHI (rt_credit RT Σk) R0 HK2 KLIB2 KZSH2 OFFT FHI _ _ IE Σk mk Fk fck IV2 Fh).
      - cbn [A2 a_lo a_P]. unfold RT_STACK. clear - YPl4. lia.
      - intros x Hx. unfold W14, DSTATE_SIZE, blk_ivls in Hx. unfold Wc2, Wc, blk_ivls.
        cbn [A2 a_cx a_P a_sp a_fb a_shf cx1 cx_blocks b_s b_strm b_small b_tt b_ll16 b_ll4 b_n] in Hx |- *. fold S STRM usp in Hx |- *.
        destruct SM01 as [E|E]; rewrite E in Hx |- *; cbn [Z.eqb app outside KFrame.outside] in Hx |- *; clear - Hx; lia.
      - cbn [A2 a_P]. clear - YPl4 LOW CEQ ACR. lia.
      - cbn [A2 a_sp]. fold usp. unfold USTACK_TOP in SPT. clear - SPT. lia. }
    destruct (dec_img RT AF AF_DRV Σk mk ARTk LIBk) as (GOTk & SVRk & RNk & _).
    eapply (l1_realizes RT AF Σk PMc _ T ck MST Hck).
    eapply evt_mono; [| intros ms' HQ; exact (HQ (eq_refl R0))].
    eapply (B0F_g10H.B0F_g10_H14 A2 AOK2 (QL RT PMc T Σk R0) hH nbu0 cf0 dH r0 k b0 (Z_to_bv 64 4) (bs_tih b0) uc rest mk);
      cbn [A2 a_cx a_lo a_P a_sp a_b0 a_payload a_shs a_sht a_shf a_fb a_g1 a_sv a_m0 cx1 cx_blocks b_s b_strm b_src b_len b_dst b_dlen b_small b_n b_tt b_ll16 b_ll4]; fold S STRM SRC len;
      [ exact H14| exact UC| reflexivity| exact PAYEQ| reflexivity| exact BS| exact BSRC| exact BLEN| exact BDST| exact BDLEN| rewrite BAV; exact BDLEN
      | exact HDk| exact HSTRM| reflexivity| reflexivity| reflexivity| reflexivity| exact HSM| exact HCBN| exact HVERB
      | exact NBUk| exact (proj1 NBR0)| exact CFk| exact CFL0| exact MIDk| exact ET| exact E16| exact E4| exact ECC
      | exact (B0F_g10K.g10_save0_save_cells b0segs mk _ SVk)| exact DRk| exact STRMk| exact BLKk| exact PAYk| exact GOTk| exact SVRk| exact RNk
      | exact FLk| exact FHk| exact AFRk| exact STk| apply munch_refl| apply wmono_refl| exact (kmem_inv_N _ _ MIk)]. }
  eapply (l1_realizes RT AF Σ1 PMc _ T c4 MST Hc4).
  eapply (B0F_g10_B A _ GL GSrc ANS ANT GS1 GSELF SEPshs D1 D2 D4 DFT SEPsht m4 h0 b0 F2 fc2 gp tp SHs4 SHt4 SHp4 HSTRM HN HP1 HP2 HP3 BSRC BLEN BAI' BZA);
    [ | | | exact HD3| exact HST10| exact HBB| exact HBL| exact SV4| exact STRM3| exact BTIL| exact PAY3| exact FL4| exact FH4| exact AFR4| exact ST4| exact (kmem_inv_N _ _ MI4)].
  - (* [comment removed for export] *)
    clear Hc4. intros rc m5 st bb n5 ai' til' tih' fl5 zt ng5 jg5 j24 pos j38 ku0 ku8 ku16 ku24 kyw32 kyw40 kyw48 kyw56 ku736 ku744.
    intros ke1 ke5 ke6 ke7 ke12 ke13 ke14 ke15 ke16 ke17 ke18 ke19 ke20 ke21 ke22 ke23 ke24 ke25 ke26 ke27 ke28 ke29 ke30 ke31.
    intros EARLY RC STR BBR NNR HD5 STRM5 AI5 SV5 LO5 HI5 GEO5 NG5 FLP5 FM5 FRT5 FF5 FS5 ST5n MU5 WM5 NMI5. apply evt_done. intros c5 Hc5.
    cbn [A a_cx a_P a_fb a_shf a_shs a_lo a_sp] in HD5, STRM5, SV5, LO5, HI5, GEO5, FLP5, FM5, FRT5, FF5, FS5, ST5n, Hc5. fold S STRM in HD5, STRM5, SV5, LO5, HI5, FM5, Hc5.
    destruct (after_l1 AF G Σ1 _ m4 m5 SOK ART4 MI4 ST4 PR4 NMI5 MU5 WM5 W10C) as (ART5 & MI5 & ST5 & PR5 & STEP5).
    assert (AG45 : agree_on SESP m4 m5) by (apply (agree_of_nmunch _ m4 m5 _ MU5); exact SESPOUT).
    agx AG45 NBU3 ltac:(fun H => left; clear - H; lia). agx AG45 CF3 ltac:(fun H => rewrite CFL0 in H; left; clear - H; lia). agx AG45 MID3 ltac:(fun H => left; clear - H; lia).
    agx AG45 ZSH3 ltac:(fun H => rewrite repeat_length in H; right; right; right; clear - H; lia).
    assert (LIB5 : OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_libA.TwinB__.LIB_A m5).
    { apply (B0_sessK.lib_of_munch _ m4 m5 LIB4 MU5). intros x Hx. unfold W10. cbn [A a_cx a_P a_fb a_shf outside]. fold S STRM. clear - Hx IE FSSEG FSLO OFFP FSEG SHR0. lia. }
    (* [comment removed for export] *)
    destruct (release_inline2 AF G (mi := m2) Σ1 m5 eq_refl SOK ART5) as (Σ2 & fl' & FLC & FLP' & FL0 & FLW & FLD & REL).
    replace (f + 64 - 8) with (f + 56) in FLP' by (clear; lia).
    pose proof (dk_ro_C8_inj m5 _ _ _ FLP5 (ro_C8_KN m5 _ _ FLP')) as EFL. rewrite EFL in Hc5. clear FLP5 FLP' EFL.
    eapply (l1_realizes RT AF Σ1 PMc _ T c5 MST Hc5).
    eapply (B0F_dec_epi.B0F_rel_flag _ m5 fl' (Z_to_bv 8 1)); [exact FLC| exact (kmem_inv_N _ _ MI5)|].
    clear Hc5. intros m6 FLC6 NMI6 MU6 WM6. apply evt_done. intros c6 Hc6.
    destruct (REL m6 MU6 WM6 FLC6 MI5 NMI6 ST5 PR5) as (ART6 & FRS6 & LV6 & SP6 & CR6 & AL6 & AM6 & MI6 & ST6 & PR6).
    assert (AG56 : agree_on (fun x => SES x \/ (P <= x < usp) \/ (f <= x < f + 56) \/ (SHF <= x < SHF + 8) \/ client_static x) m5 m6).
    { apply (agree_of_nmunch [(fl', fl' + 1)] m5 m6 _ MU6). intros x Hx. cbn [outside]. split; [| exact I].
      assert (C : cls RT P Σ1 x 1).
      { intros y Hy. replace y with x by (clear - Hy; lia). destruct Hx as [C|[C|[C|[C|C]]]]; [apply (CLS Σ1 x SOK); left; exact C| apply (CLS Σ1 x SOK); right; left; exact C
          | apply (CLS Σ1 x SOK); right; right; left; exact C| apply (CLS Σ1 x SOK); right; right; right; exact C| apply (acl_static RT P Σ1 x C)]. }
      pose proof (FLD x 1 C) as D. clear - D. lia. }
    agx AG56 HD5 ltac:(fun H => left; left; clear - H; lia). agx AG56 STRM5 ltac:(fun H => left; right; left; clear - H; lia).
    agx AG56 MID3 ltac:(fun H => left; left; clear - H; lia). agx AG56 ZSH3 ltac:(fun H => rewrite repeat_length in H; left; right; right; right; clear - H; lia).
    agx AG56 LO5 ltac:(fun H => right; left; clear - H YPh; lia). agx AG56 HI5 ltac:(fun H => right; left; clear - H YPh; lia).
    agx AG56 FM5 ltac:(fun H => right; left; unfold FM_CELLS in H; cbn [cells_size csize Nat.add length] in H; clear - H YPh; lia).
    agx AG56 FRT5 ltac:(fun H => right; left; unfold FT_REGS in H; cbn [cells_size csize Nat.add] in H; clear - H NG5 GEO5; lia).
    assert (LIB6 : OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_libA.TwinB__.LIB_A m6).
    { apply (OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_libA.TwinB__.LIB_locA m5 m6 LIB5). intros a (lo' & hi' & HIn & Hx). apply AG56. right; right; right; right.
      assert (R : 857056 <= bv_unsigned a < 858080 \/ 858336 <= bv_unsigned a < 858392 \/ 858432 <= bv_unsigned a < 860480).
      { unfold OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_libiface.TwinB__.LIB_FP in HIn. cbn [In] in HIn. destruct HIn as [HI|[HI|[HI|[]]]]; injection HI as <- <-; [left| right; left| right; right]; exact Hx. }
      exact (lib_static _ R). }
    pose proof (ASTA_switch RT Σ1 Σ2 PMc _ c6 Hc6 AL6 AM6) as Hc6'. clear Hc6.
    (* [comment removed for export] *)
    eapply (l1_realizes RT AF Σ2 PMc _ T c6 MST Hc6').
    eapply (B0F_dec_epi.B0F_epi A _ m6 _ _ zt ng5 jg5); cbn [A a_cx a_P a_fb a_shf a_shs a_lo a_sp]; [exact GEO5| exact NG5| exact YPl| exact LO5| exact FM5| exact HI5| exact FRT5| exact ST6|].
    clear Hc6'. intros STu. apply evt_done. intros c7 Hc7.
    cbn [A a_ra a_sp a_s0 a_s1 a_s2 a_s3 a_s4 a_s5 a_s6 a_s7 a_s8 a_s9 a_s10 a_s11] in Hc7. fold usp in STu.
    (* [comment removed for export] *)
    assert (CXE : cx_blocks cx 0 0 0 0 = cx) by (clear - N0 TT0 L160 L40; destruct cx; cbn in *; subst; reflexivity).
    pose proof (EARLY BzDU10M.dst_zero (b_small cx) (b_dlen cx)) as EM. unfold BzDU10M.s10 in EM. cbn [A a_payload] in EM.
    apply Hk. exists Σ2, 0, 0, 0, 0.
    split; [| split; [rewrite LV6, LV1; reflexivity| split; [exact FRS6| split; [exact SP6| rewrite CR6, CR1; unfold DEC10_COST; change (mcost 3600000) with 7216384; clear; lia]]]].
    eapply ASTA_conseq; [exact Hc7|]. intros ms <-.
    eexists m6, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, BzDU10M.dst_zero. cbv zeta. rewrite CXE.
    destruct (decompress (dst_init BzDU10M.dst_zero 0 (b_small cx)) (dstrm_init (map bv_unsigned payload) (b_dlen cx))) as [[rv dF] sF].
    unfold early10 in EM. destruct EM as (-> & RVC & ST13 & SOUT & SAVO).
    split; [reflexivity|]. split; [exact ART6|]. split; [exact MI6|]. split; [exact STu|]. split; [exact LIB6|].
    split. { unfold dliveA. rewrite LV6, LV1. repeat (split; [first [assumption| intros X; exfalso; apply X; assumption]|]).
             split; [exists fS, kS; split; [rewrite FRS6; exact FSIN| split; [exact FSLO| exact FSHI]]| split; [exact T8| exact ZSH3]]. }
    split; [exact DPURE|]. split; [left; repeat split; reflexivity|].
    split.
    + right. split; [exact RVC|]. split; [exact ST13|]. split; [exact SOUT|]. split; [exact SAVO|]. split; [reflexivity|].
      exists (g10_hd h0 st bb 0 n5), d0, ai', til', tih'.
      split; [exact HD5|]. split; [exact HSTRM|]. split; [cbn [g10_hd sh_state]; change (2 ^ 31) with 2147483648; clear - STR; lia|].
      split; [cbn [g10_hd sh_state]; unfold BZ_X_OUTPUT; clear - STR; lia|]. split; [exact MID3|]. split; [exact MT0|]. split; [exact M160|]. split; [exact M40|].
      split; [exact STRM5| exact AI5].
    + exact (pres_final RT AF Σ lo P usp Wc m m1 m2 m6 ART0 LOW YPl ltac:(clear - YPh; lia) MU1 PRES2 PR6).
  - (* [comment removed for export] *)
    clear Hc4. intros m5 uc rest ku0 ku8 ku16 ku24 kyw32 kyw40 kyw48 kyw56 ku736 ku744 kf5 kf6 kf7 kf11 kf12 kf13 kf14 kf15 kf16 kf18 kf21 kf23 kf25 kf28 kf29 kf30 kf31.
    intros PAYEQ UC SMALL0 HD5 STRM5 SV5 PAY5 LO5 HI5 AFR5 ST5n MU5 WM5 NMI5. apply evt_done. intros c5 Hc5.
    cbn [A a_cx a_P a_fb a_shf a_shs a_sht a_lo a_sp a_payload] in PAYEQ, HD5, STRM5, SV5, PAY5, LO5, HI5, ST5n, Hc5. fold S STRM SRC len in HD5, STRM5, SV5, PAY5, LO5, HI5, Hc5.
    destruct (after_l1 AF G Σ1 _ m4 m5 SOK ART4 MI4 ST4 PR4 NMI5 MU5 WM5 W10C) as (ART5 & MI5 & ST5 & PR5 & STEP5).
    assert (AG45 : agree_on SESP m4 m5) by (apply (agree_of_nmunch _ m4 m5 _ MU5); exact SESPOUT).
    agx AG45 NBU3 ltac:(fun H => left; clear - H; lia). agx AG45 CF3 ltac:(fun H => rewrite CFL0 in H; left; clear - H; lia). agx AG45 MID3 ltac:(fun H => left; clear - H; lia).
    agx AG45 ZSH3 ltac:(fun H => rewrite repeat_length in H; right; right; right; clear - H; lia).
    assert (DR5 : drest_at b0segs m5 S r0) by (apply (drest_agree m4 m5 S r0 _ DR4 AG45); intros x Hx; left; exact Hx).
    assert (LIB5 : OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_libA.TwinB__.LIB_A m5).
    { apply (B0_sessK.lib_of_munch _ m4 m5 LIB4 MU5). intros x Hx. unfold W10. cbn [A a_cx a_P a_fb a_shf outside]. fold S STRM. clear - Hx IE FSSEG FSLO OFFP FSEG SHR0. lia. }
    (* [comment removed for export] *)
    set (nb := (uc - 48) * 400000) in *.
    assert (UNW : unwind_ch m5 (Z_to_bv 64 0xaa7a8) sp (Z_to_bv 64 P)).
    { apply (d10_unwind m5 A 0xaa7a8 AFR5); cbn [A a_ra a_s0 a_sp a_P]; fold usp.
      - rewrite RAE. unfold SITE_TRACES. apply in_or_app. right. cbn. do 7 right. left. reflexivity.
      - clear; lia. - clear - AL; Z.div_mod_to_equations; lia. - clear - SPT; lia. - clear - YPl4 LOW CEQ ACR; lia. - exact S0C. }
    eapply (malloc_call AF G PMc FDO MST Σ1 nb m5); [exact MAL| exact SOK| unfold nb; clear - UC; lia| exact TP| rewrite LV1; clear - LIVEMAX; lia
      | rewrite CR1; unfold DEC10_COST in CRED; change (mcost 3600000) with 7216384 in CRED; unfold mcost, nb; destruct (_ <=? _); clear - CRED UC; lia
      | exact ART5| exact MI5| exact ST5| exact PR5| exact UNW| exact Hc5|].
    clear Hc5. intros c6 Σ2 m6 p r0' r1' r2' j1 j2 j3 j4 j5 j6 j7 r3' r4' r5' r6' F6 fc6 Hc6 SOK2 LV2 FRS2 CR2 P0 P16 PTOP ART6 MI6 ST6 WM6 PR6 WRP ACCP STEP6 APART.
    rewrite (KMState.ret_pc_even 0xaa7a8 ltac:(lia) eq_refl) in Hc6.
    assert (AG56 : agree_on (fun x => SES x \/ (P <= x < usp) \/ (f <= x < f + 56) \/ (SHF <= x < SHF + 8)) m5 m6).
    { apply (agree_of_pres_fp _ _ _ _ m5 m6 _ STEP6). intros x C. split; [exact (CLS Σ1 x SOK C)| cbn [KFrame.outside]; exact I]. }
    agx AG56 HD5 ltac:(fun H => left; left; clear - H; lia). agx AG56 STRM5 ltac:(fun H => left; right; left; clear - H; lia).
    agx AG56 SV5 ltac:(fun H => left; left; unfold SAVE0_CELLS in H; cbn [cells_size csize Nat.add] in H; clear - H; lia).
    agx AG56 PAY5 ltac:(fun H => left; right; right; left; clear - H PLEN; lia).
    agx AG56 NBU3 ltac:(fun H => left; left; clear - H; lia). agx AG56 CF3 ltac:(fun H => rewrite CFL0 in H; left; left; clear - H; lia). agx AG56 MID3 ltac:(fun H => left; left; clear - H; lia).
    agx AG56 ZSH3 ltac:(fun H => rewrite repeat_length in H; left; right; right; right; clear - H; lia).
    agx AG56 LO5 ltac:(fun H => right; left; clear - H YPh; lia). agx AG56 HI5 ltac:(fun H => right; left; clear - H YPh; lia).
    assert (DR6 : drest_at b0segs m6 S r0) by (apply (drest_agree m5 m6 S r0 _ DR5 AG56); intros x Hx; left; left; clear - Hx; lia).
    pose proof (dec_aframe_xfer2 RT AF _ _ _ _ _ _ _ _ _ G A eq_refl eq_refl eq_refl eq_refl Σ1 Σ2 [] m5 m6 m2 SOK SOK2 ART6 STEP6 I I I AFR5) as AFR6.
    assert (LIB6 : OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_libA.TwinB__.LIB_A m6) by (apply (lib_of_pfp _ _ _ [] m5 m6 LIB5 STEP6); intros x _; exact I).
    destruct (n_wr_at_rw_CB m6 p nb WRP ltac:(unfold nb; clear - UC; lia)) as (Jt & BJ).
    (* [comment removed for export] *)
    assert (SLIV2 : In (S, 64144) (rt_live RT Σ2)) by (rewrite LV2; right; exact SLIV1).
    assert (APPc : app_fp (W10c A)) by (unfold W10c; cbn [A a_cx app_fp]; fold S; unfold SH_LO, SH_HI; split; [clear - SOFF; lia| exact I]).
    pose proof (live_reader RT AF Σ2 m6 S 64144 (W10c A) ART6 SLIV2 ltac:(clear - S16; Z.div_mod_to_equations; lia) eq_refl APPc) as SHSc.
    eapply (l1_realizes RT AF Σ2 PMc _ T c6 MST Hc6).
    eapply (B0F_g10_C2f A _ m6 GL ANS SHSc); [apply munch_refl| apply wmono_refl| exact MID3| unfold USTACK_TOP in PTOP; clear - P0 PTOP UC; unfold nb in PTOP; lia| exact LO5| exact ST6| exact (kmem_inv_N _ _ MI6)|].
    clear Hc6. intros m7 c11 c12 MID7 LO7 ST7n MU7 WM7 NMI7. apply evt_done. intros c7 Hc7.
    cbn [A a_cx a_P a_lo a_sp] in MID7, LO7, ST7n, Hc7. fold S in MID7, LO7, Hc7. unfold W10c in MU7. cbn [A a_cx] in MU7. fold S in MU7.
    destruct (after_l1 AF G Σ2 _ m6 m7 SOK2 ART6 MI6 ST6 PR6 NMI7 MU7 WM7
                ltac:(per_interval; right; right; right; unfold Wc; cbn [outside]; match goal with HX : _ <= _ < _ |- _ => clear - HX; lia end)) as (ART7 & MI7 & ST7 & PR7 & STEP7).
    destruct (d10_new_apart RT AF Σ2 m6 p nb (rt_live RT Σ1) ART6 LV2) as (LD & FD).
    pose proof (LD _ _ SLIV1) as DSP. unfold disj in DSP.
    assert (AG67 : agree_on (fun x => ~ (S + 3152 <= x < S + 3176)) m6 m7) by (apply (agree_of_nmunch _ m6 m7 _ MU7); intros x Hx; cbn [outside]; split; [exact Hx| exact I]).
    agx AG67 HD5 ltac:(fun H => clear - H; lia). agx AG67 STRM5 ltac:(fun H => clear - H D1; lia). agx AG67 SV5 ltac:(fun H => unfold SAVE0_CELLS in H; cbn [cells_size csize Nat.add] in H; clear - H; lia).
    agx AG67 PAY5 ltac:(fun H => clear - H PLEN D2; lia). agx AG67 NBU3 ltac:(fun H => clear - H; lia). agx AG67 CF3 ltac:(fun H => rewrite CFL0 in H; clear - H; lia).
    agx AG67 ZSH3 ltac:(fun H => rewrite repeat_length in H; clear - H SHTR SOFF; lia). agx AG67 HI5 ltac:(fun H => clear - H SL1 LOW YPl; lia).
    agx AG67 BJ ltac:(fun H => clear - H DSP; lia).
    assert (DR7 : drest_at b0segs m7 S r0).
    { apply (BzContracts.drest_transport b0segs _ m6 m7 S r0 DR6 MU7 WM7); cbn [disjoint_from]; (split; [clear; lia| exact I]). }
    assert (AFR7 : aframe A m7).
    { apply (aframe_tr A _ m6 m7 AFR6 MU7 WM7); cbn [A a_P a_fb a_shf disjoint_from]; (split; [| exact I]); [clear - SL1 LOW YPl; lia| clear - SL1 LOW YPl; lia| clear - GS1; lia| clear - GS2; lia]. }
    assert (LIB7 : OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_libA.TwinB__.LIB_A m7) by (apply (B0_sessK.lib_of_munch _ m6 m7 LIB6 MU7); intros x Hx; cbn [outside]; split; [clear - Hx IE; lia| exact I]).
    (* [comment removed for export] *)
    assert (SM0 : b_small cx = 0) by (rewrite <- HSM; exact SMALL0).
    assert (NBE : nb = 400000 * (uc - 48)) by (unfold nb; clear; lia).
    assert (PNZ : p <> 0) by (clear - P0; lia).
    eapply (HOV Σ2 m7 F6 fc6 uc p 0 0 rest (BlkF (zw32 (S0_cmp_bs.zarr_of_junkw Jt (100000 * (uc - 48))) (100000 * (uc - 48))))
             (DSM p (sm_ll16 d0) (sm_ll4 d0) (sm_sbcrc d0) (sm_sccrc d0) (sm_cbcrc d0) (sm_cccrc d0) (sm_nInUse d0)) c7
             _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SOK2).
    + rewrite LV2, LV1, NBE. unfold dblocks. rewrite (proj2 (Z.eqb_neq p 0) PNZ). reflexivity.
    + rewrite CR2, CR1. unfold DEC10_COST. change (mcost 3600000) with 7216384. unfold mcost, nb. destruct (_ <=? _); clear - UC; lia.
    + exact ART7. + exact MI7. + exact PR7. + exact PAYEQ. + exact UC.
    + unfold dpureA. cbn [cx_blocks b_len b_dlen b_small b_n b_s b_tt b_ll16 b_ll4]. repeat (split; [first [assumption| clear - UC; lia| reflexivity]|]).
      unfold dsepA. cbn [cx_blocks b_s b_strm b_src b_len b_dst b_dlen b_n b_tt b_ll16 b_ll4]. fold S STRM SRC len. unfold disj.
      split. { intros _. rewrite <- NBE. pose proof (LD _ _ ZLIV1) as DZ. pose proof (LD _ _ ltac:(rewrite LV1; exact OLIV)) as DO. pose proof (FD fS kS ltac:(rewrite FRS2, FRS1; right; exact FSIN)) as DFR.
               unfold disj in DZ, DO. split; [exact DSP|]. split; [clear - DFR FSLO FSHI; lia|]. split; [clear - DZ ZLO ZHI; lia| clear - DO OLO OHI; lia]. }
      split; [intros X; exfalso; apply X; reflexivity|]. split; [intros X; exfalso; apply X; reflexivity| intros X; exfalso; apply X; reflexivity].
    + right. split; [clear - UC; lia|]. left. repeat split; [exact SM0| exact PNZ].
    + apply d10_blkF; cbn [cx_blocks b_small b_n b_tt]; [exact SM0| clear - UC; lia|]. replace (4 * (100000 * (uc - 48))) with nb by (unfold nb; clear; lia). exact BJ.
    + exact HD5. + exact NBU3. + exact CF3. + exact MID7. + reflexivity. + exact M160. + exact M40. + exact CCC0. + exact SV5. + exact DR7. + exact STRM5. + exact PAY5. + exact LIB7. + exact ZSH3.
    + exact LO7. + exact HI5. + exact AFR7. + exact ST7. + exact Hc7.
  - (* [comment removed for export] *)
    clear Hc4. intros m5 uc rest ku0 ku8 ku16 ku24 kyw32 kyw40 kyw48 ku736 ku744 kf5 kf6 kf7 kf11 kf12 kf13 kf14 kf15 kf16 kf21 kf28 kf29 kf30 kf31.
    intros PAYEQ UC SMALLNZ HD5 STRM5 SV5 PAY5 LO5 HI5 AFR5 ST5n MU5 WM5 NMI5. apply evt_done. intros c5 Hc5.
    cbn [A a_cx a_P a_fb a_shf a_shs a_sht a_lo a_sp a_payload] in PAYEQ, HD5, STRM5, SV5, PAY5, LO5, HI5, ST5n, Hc5. fold S STRM SRC len in HD5, STRM5, SV5, PAY5, LO5, HI5, Hc5.
    destruct (after_l1 AF G Σ1 _ m4 m5 SOK ART4 MI4 ST4 PR4 NMI5 MU5 WM5 W10C) as (ART5 & MI5 & ST5 & PR5 & STEP5).
    assert (AG45 : agree_on SESP m4 m5) by (apply (agree_of_nmunch _ m4 m5 _ MU5); exact SESPOUT).
    agx AG45 NBU3 ltac:(fun H => left; clear - H; lia). agx AG45 CF3 ltac:(fun H => rewrite CFL0 in H; left; clear - H; lia). agx AG45 MID3 ltac:(fun H => left; clear - H; lia).
    agx AG45 ZSH3 ltac:(fun H => rewrite repeat_length in H; right; right; right; clear - H; lia).
    assert (DR5 : drest_at b0segs m5 S r0) by (apply (drest_agree m4 m5 S r0 _ DR4 AG45); intros x Hx; left; exact Hx).
    assert (LIB5 : OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_libA.TwinB__.LIB_A m5).
    { apply (B0_sessK.lib_of_munch _ m4 m5 LIB4 MU5). intros x Hx. unfold W10. cbn [A a_cx a_P a_fb a_shf outside]. fold S STRM. clear - Hx IE FSSEG FSLO OFFP FSEG SHR0. lia. }
    (* [comment removed for export] *)
    set (nb := (uc - 48) * 200000) in *.
    assert (UNW : unwind_ch m5 (Z_to_bv 64 0xaa4f4) sp (Z_to_bv 64 P)).
    { apply (d10_unwind m5 A 0xaa4f4 AFR5); cbn [A a_ra a_s0 a_sp a_P]; fold usp.
      - rewrite RAE. unfold SITE_TRACES. apply in_or_app. right. cbn. do 5 right. left. reflexivity.
      - clear; lia. - clear - AL; Z.div_mod_to_equations; lia. - clear - SPT; lia. - clear - YPl4 LOW CEQ ACR; lia. - exact S0C. }
    eapply (malloc_call AF G PMc FDO MST Σ1 nb m5); [exact MAL| exact SOK| unfold nb; clear - UC; lia| exact TP| rewrite LV1; clear - LIVEMAX; lia
      | rewrite CR1; unfold DEC10_COST in CRED; change (mcost 3600000) with 7216384 in CRED; unfold mcost, nb; destruct (_ <=? _); clear - CRED UC; lia
      | exact ART5| exact MI5| exact ST5| exact PR5| exact UNW| exact Hc5|].
    clear Hc5 UNW. intros c6 Σ2 m6 p r0' r1' r2' j1 j2 j3 j4 j5 j6 j7 r3' r4' r5' r6' F6 fc6 Hc6 SOK2 LV2 FRS2 CR2 P0 P16 PTOP ART6 MI6 ST6 WM6 PR6 WRP ACCP STEP6 APART.
    rewrite (KMState.ret_pc_even 0xaa4f4 ltac:(lia) eq_refl) in Hc6.
    assert (AG56 : agree_on (fun x => SES x \/ (P <= x < usp) \/ (f <= x < f + 56) \/ (SHF <= x < SHF + 8)) m5 m6).
    { apply (agree_of_pres_fp _ _ _ _ m5 m6 _ STEP6). intros x C. split; [exact (CLS Σ1 x SOK C)| cbn [KFrame.outside]; exact I]. }
    agx AG56 HD5 ltac:(fun H => left; left; clear - H; lia). agx AG56 STRM5 ltac:(fun H => left; right; left; clear - H; lia).
    agx AG56 SV5 ltac:(fun H => left; left; unfold SAVE0_CELLS in H; cbn [cells_size csize Nat.add] in H; clear - H; lia).
    agx AG56 PAY5 ltac:(fun H => left; right; right; left; clear - H PLEN; lia).
    agx AG56 NBU3 ltac:(fun H => left; left; clear - H; lia). agx AG56 CF3 ltac:(fun H => rewrite CFL0 in H; left; left; clear - H; lia). agx AG56 MID3 ltac:(fun H => left; left; clear - H; lia).
    agx AG56 ZSH3 ltac:(fun H => rewrite repeat_length in H; left; right; right; right; clear - H; lia).
    agx AG56 LO5 ltac:(fun H => right; left; clear - H YPh; lia). agx AG56 HI5 ltac:(fun H => right; left; clear - H YPh; lia).
    assert (DR6 : drest_at b0segs m6 S r0) by (apply (drest_agree m5 m6 S r0 _ DR5 AG56); intros x Hx; left; left; clear - Hx; lia).
    pose proof (dec_aframe_xfer2 RT AF _ _ _ _ _ _ _ _ _ G A eq_refl eq_refl eq_refl eq_refl Σ1 Σ2 [] m5 m6 m2 SOK SOK2 ART6 STEP6 I I I AFR5) as AFR6.
    assert (LIB6 : OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_libA.TwinB__.LIB_A m6) by (apply (lib_of_pfp _ _ _ [] m5 m6 LIB5 STEP6); intros x _; exact I).
    destruct (n_wr_at_rw_CB m6 p nb WRP ltac:(unfold nb; clear - UC; lia)) as (J16 & BJ).
    destruct (d10_new_apart RT AF Σ2 m6 p nb (rt_live RT Σ1) ART6 LV2) as (LD & FD).
    pose proof (LD _ _ SLIV1) as DSP. unfold disj in DSP.
    (* [comment removed for export] *)
    assert (SLIV2 : In (S, 64144) (rt_live RT Σ2)) by (rewrite LV2; right; exact SLIV1).
    assert (APPc : app_fp (W10c A)) by (unfold W10c; cbn [A a_cx app_fp]; fold S; unfold SH_LO, SH_HI; split; [clear - SOFF; lia| exact I]).
    pose proof (live_reader RT AF Σ2 m6 S 64144 (W10c A) ART6 SLIV2 ltac:(clear - S16; Z.div_mod_to_equations; lia) eq_refl APPc) as SHSc.
    assert (SHTc : shzW b0segs (W10c A) m6 STRM (STRM + 80)).
    { apply (strm_reader m6 STRM SHT _ ANT); [clear - FS0 FSLO; lia| clear - FS1 FSHI CEQ ACR; lia| exact ZSH3| exact APPc]. }
    eapply (l1_realizes RT AF Σ2 PMc _ T c6 MST Hc6).
    eapply (B0F_g10_C2s A _ m6 GL ANS ANT D1 SHSc SHTc); [apply munch_refl| apply wmono_refl| exact HD5| cbn [g10_hd sh_n]; clear - UC; lia| exact HP1| exact HP2| exact HP3| exact STRM5| exact BZA
      | exact MID3| exact LO5| exact ST6| exact (kmem_inv_N _ _ MI6)|].
    clear Hc6. intros m7 c11 c12 c13 HD7 STRM7 MID7 LO7 ST7n MU7 WM7 NMI7. apply evt_done. intros c7 Hc7.
    cbn [A a_cx a_P a_lo a_sp g10_hd sh_n] in HD7, STRM7, MID7, LO7, ST7n, Hc7. fold S STRM in HD7, STRM7, MID7, LO7, Hc7. unfold W10c in MU7. cbn [A a_cx] in MU7. fold S in MU7.
    destruct (after_l1 AF G Σ2 _ m6 m7 SOK2 ART6 MI6 ST6 PR6 NMI7 MU7 WM7
                ltac:(per_interval; right; right; right; unfold Wc; cbn [outside]; match goal with HX : _ <= _ < _ |- _ => clear - HX; lia end)) as (ART7 & MI7 & ST7 & PR7 & STEP7).
    assert (AG67 : agree_on (fun x => ~ (S + 3152 <= x < S + 3176)) m6 m7) by (apply (agree_of_nmunch _ m6 m7 _ MU7); intros x Hx; cbn [outside]; split; [exact Hx| exact I]).
    agx AG67 SV5 ltac:(fun H => unfold SAVE0_CELLS in H; cbn [cells_size csize Nat.add] in H; clear - H; lia).
    agx AG67 PAY5 ltac:(fun H => clear - H PLEN D2; lia). agx AG67 NBU3 ltac:(fun H => clear - H; lia). agx AG67 CF3 ltac:(fun H => rewrite CFL0 in H; clear - H; lia).
    agx AG67 ZSH3 ltac:(fun H => rewrite repeat_length in H; clear - H SHTR SOFF; lia). agx AG67 HI5 ltac:(fun H => clear - H SL1 LOW YPl; lia).
    agx AG67 BJ ltac:(fun H => clear - H DSP; lia).
    assert (DR7 : drest_at b0segs m7 S r0).
    { apply (BzContracts.drest_transport b0segs _ m6 m7 S r0 DR6 MU7 WM7); cbn [disjoint_from]; (split; [clear; lia| exact I]). }
    assert (AFR7 : aframe A m7).
    { apply (aframe_tr A _ m6 m7 AFR6 MU7 WM7); cbn [A a_P a_fb a_shf disjoint_from]; (split; [| exact I]); [clear - SL1 LOW YPl; lia| clear - SL1 LOW YPl; lia| clear - GS1; lia| clear - GS2; lia]. }
    assert (LIB7 : OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_libA.TwinB__.LIB_A m7) by (apply (B0_sessK.lib_of_munch _ m6 m7 LIB6 MU7); intros x Hx; cbn [outside]; split; [clear - Hx IE; lia| exact I]).
    (* [comment removed for export] *)
    set (nb4 := 50000 * (uc - 48)) in *.
    assert (UNW : unwind_ch m7 (Z_to_bv 64 0xaa570) sp (Z_to_bv 64 P)).
    { apply (d10_unwind m7 A 0xaa570 AFR7); cbn [A a_ra a_s0 a_sp a_P]; fold usp.
      - rewrite RAE. unfold SITE_TRACES. apply in_or_app. right. cbn. do 6 right. left. reflexivity.
      - clear; lia. - clear - AL; Z.div_mod_to_equations; lia. - clear - SPT; lia. - clear - YPl4 LOW CEQ ACR; lia. - exact S0C. }
    eapply (malloc_call AF G PMc FDO MST Σ2 nb4 m7); [exact MAL| exact SOK2| unfold nb4; clear - UC; lia| exact TP| rewrite LV2, LV1; cbn [length]; clear - LIVEMAX; lia
      | rewrite CR2, CR1; unfold DEC10_COST in CRED; change (mcost 3600000) with 7216384 in CRED; unfold mcost, nb, nb4; destruct (_ <=? _); destruct (_ <=? _); clear - CRED UC; lia
      | exact ART7| exact MI7| exact ST7| exact PR7| exact UNW| exact Hc7|].
    clear Hc7 UNW. intros c8 Σ3 m8 p4 o0 o1 o2 i1 i2 i3 i4 i5 i6 i7 o3 o4 o5 o6 F8 fc8 Hc8 SOK3 LV3 FRS3 CR3 P40 P416 P4TOP ART8 MI8 ST8 WM8 PR8 WRP4 ACCP4 STEP8 APART4.
    rewrite (KMState.ret_pc_even 0xaa570 ltac:(lia) eq_refl) in Hc8.
    assert (PLIV2 : In (p, nb) (rt_live RT Σ2)) by (rewrite LV2; left; reflexivity).
    assert (AG78 : agree_on (fun x => SES x \/ (P <= x < usp) \/ (f <= x < f + 56) \/ (SHF <= x < SHF + 8) \/ (p <= x < p + nb)) m7 m8).
    { apply (agree_of_pres_fp _ _ _ _ m7 m8 _ STEP8). intros x C. split; [| cbn [KFrame.outside]; exact I].
      destruct C as [C|[C|[C|[C|C]]]]; [apply (CLS Σ2 x SOK2); left; exact C| apply (CLS Σ2 x SOK2); right; left; exact C| apply (CLS Σ2 x SOK2); right; right; left; exact C
        | apply (CLS Σ2 x SOK2); right; right; right; exact C| exact (acl_live RT P Σ2 p nb x PLIV2 C)]. }
    agx AG78 HD7 ltac:(fun H => left; left; clear - H; lia). agx AG78 STRM7 ltac:(fun H => left; right; left; clear - H; lia).
    agx AG78 SV5 ltac:(fun H => left; left; unfold SAVE0_CELLS in H; cbn [cells_size csize Nat.add] in H; clear - H; lia).
    agx AG78 PAY5 ltac:(fun H => left; right; right; left; clear - H PLEN; lia).
    agx AG78 NBU3 ltac:(fun H => left; left; clear - H; lia). agx AG78 CF3 ltac:(fun H => rewrite CFL0 in H; left; left; clear - H; lia). agx AG78 MID7 ltac:(fun H => left; left; clear - H; lia).
    agx AG78 ZSH3 ltac:(fun H => rewrite repeat_length in H; left; right; right; right; clear - H; lia).
    agx AG78 LO7 ltac:(fun H => right; left; clear - H YPh; lia). agx AG78 HI5 ltac:(fun H => right; left; clear - H YPh; lia).
    agx AG78 BJ ltac:(fun H => right; right; right; right; clear - H UC; unfold nb in H |- *; lia).
    assert (DR8 : drest_at b0segs m8 S r0) by (apply (drest_agree m7 m8 S r0 _ DR7 AG78); intros x Hx; left; left; clear - Hx; lia).
    pose proof (dec_aframe_xfer2 RT AF _ _ _ _ _ _ _ _ _ G A eq_refl eq_refl eq_refl eq_refl Σ2 Σ3 [] m7 m8 m2 SOK2 SOK3 ART8 STEP8 I I I AFR7) as AFR8.
    assert (LIB8 : OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_libA.TwinB__.LIB_A m8) by (apply (lib_of_pfp _ _ _ [] m7 m8 LIB7 STEP8); intros x _; exact I).
    destruct (n_wr_at_rw_CB m8 p4 nb4 WRP4 ltac:(unfold nb4; clear - UC; lia)) as (J4 & BJ4).
    destruct (d10_new_apart RT AF Σ3 m8 p4 nb4 (rt_live RT Σ2) ART8 LV3) as (LD4 & FD4).
    pose proof (LD4 _ _ SLIV2) as DSP4. unfold disj in DSP4.
    (* [comment removed for export] *)
    assert (SLIV3 : In (S, 64144) (rt_live RT Σ3)) by (rewrite LV3; right; exact SLIV2).
    pose proof (live_reader RT AF Σ3 m8 S 64144 (W10c A) ART8 SLIV3 ltac:(clear - S16; Z.div_mod_to_equations; lia) eq_refl APPc) as SHSc3.
    eapply (l1_realizes RT AF Σ3 PMc _ T c8 MST Hc8).
    eapply (B0F_g10_C3s A _ m8 GL ANS SHSc3); [apply munch_refl| apply wmono_refl| exact MID7| cbn [sm_ll16]; unfold USTACK_TOP in PTOP; unfold nb in PTOP; clear - P0 PTOP UC; lia
      | unfold USTACK_TOP in P4TOP; unfold nb4 in P4TOP; clear - P40 P4TOP UC; lia| exact LO7| exact ST8| exact (kmem_inv_N _ _ MI8)|].
    clear Hc8. intros m9 d10' d11 d12 d13 MID9 LO9 ST9n MU9 WM9 NMI9. apply evt_done. intros c9 Hc9.
    cbn [A a_cx a_P a_lo a_sp sm_tt sm_ll16 sm_ll4 sm_sbcrc sm_sccrc sm_cbcrc sm_cccrc sm_nInUse] in MID9, LO9, ST9n, Hc9. fold S in MID9, LO9, Hc9. unfold W10c in MU9. cbn [A a_cx] in MU9. fold S in MU9.
    destruct (after_l1 AF G Σ3 _ m8 m9 SOK3 ART8 MI8 ST8 PR8 NMI9 MU9 WM9
                ltac:(per_interval; right; right; right; unfold Wc; cbn [outside]; match goal with HX : _ <= _ < _ |- _ => clear - HX; lia end)) as (ART9 & MI9 & ST9 & PR9 & STEP9).
    assert (AG89 : agree_on (fun x => ~ (S + 3152 <= x < S + 3176)) m8 m9) by (apply (agree_of_nmunch _ m8 m9 _ MU9); intros x Hx; cbn [outside]; split; [exact Hx| exact I]).
    agx AG89 HD7 ltac:(fun H => clear - H; lia). agx AG89 STRM7 ltac:(fun H => clear - H D1; lia). agx AG89 SV5 ltac:(fun H => unfold SAVE0_CELLS in H; cbn [cells_size csize Nat.add] in H; clear - H; lia).
    agx AG89 PAY5 ltac:(fun H => clear - H PLEN D2; lia). agx AG89 NBU3 ltac:(fun H => clear - H; lia). agx AG89 CF3 ltac:(fun H => rewrite CFL0 in H; clear - H; lia).
    agx AG89 ZSH3 ltac:(fun H => rewrite repeat_length in H; clear - H SHTR SOFF; lia). agx AG89 HI5 ltac:(fun H => clear - H SL1 LOW YPl; lia).
    agx AG89 BJ ltac:(fun H => clear - H DSP; lia). agx AG89 BJ4 ltac:(fun H => clear - H DSP4; lia).
    assert (DR9 : drest_at b0segs m9 S r0).
    { apply (BzContracts.drest_transport b0segs _ m8 m9 S r0 DR8 MU9 WM9); cbn [disjoint_from]; (split; [clear; lia| exact I]). }
    assert (AFR9 : aframe A m9).
    { apply (aframe_tr A _ m8 m9 AFR8 MU9 WM9); cbn [A a_P a_fb a_shf disjoint_from]; (split; [| exact I]); [clear - SL1 LOW YPl; lia| clear - SL1 LOW YPl; lia| clear - GS1; lia| clear - GS2; lia]. }
    assert (LIB9 : OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_libA.TwinB__.LIB_A m9) by (apply (B0_sessK.lib_of_munch _ m8 m9 LIB8 MU9); intros x Hx; cbn [outside]; split; [clear - Hx IE; lia| exact I]).
    (* [comment removed for export] *)
    assert (SM1 : b_small cx = 1) by (rewrite <- HSM in SM01 |- *; clear - SM01 SMALLNZ; lia).
    assert (NBE : nb = 200000 * (uc - 48)) by (unfold nb; clear; lia).
    assert (PNZ : p <> 0) by (clear - P0; lia). assert (P4NZ : p4 <> 0) by (clear - P40; lia).
    eapply (HOV Σ3 m9 F8 fc8 uc 0 p p4 rest (BlkS J16 J4) (DSM (sm_tt d0) p p4 (sm_sbcrc d0) (sm_sccrc d0) (sm_cbcrc d0) (sm_cccrc d0) (sm_nInUse d0)) c9 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SOK3).
    + rewrite LV3, LV2, LV1, NBE. unfold dblocks, nb4. rewrite (proj2 (Z.eqb_neq p 0) PNZ), (proj2 (Z.eqb_neq p4 0) P4NZ). reflexivity.
    + rewrite CR3, CR2, CR1. unfold DEC10_COST. change (mcost 3600000) with 7216384. unfold mcost, nb, nb4. destruct (_ <=? _); destruct (_ <=? _); clear - UC; lia.
    + exact ART9. + exact MI9. + exact PR9. + exact PAYEQ. + exact UC.
    + unfold dpureA. cbn [cx_blocks b_len b_dlen b_small b_n b_s b_tt b_ll16 b_ll4]. repeat (split; [first [assumption| clear - UC; lia| reflexivity]|]).
      unfold dsepA. cbn [cx_blocks b_s b_strm b_src b_len b_dst b_dlen b_n b_tt b_ll16 b_ll4]. fold S STRM SRC len. unfold disj.
      pose proof (LD _ _ ZLIV1) as DZ. pose proof (LD _ _ ltac:(rewrite LV1; exact OLIV)) as DO. pose proof (FD fS kS ltac:(rewrite FRS2, FRS1; right; exact FSIN)) as DFR.
      pose proof (LD4 _ _ ltac:(rewrite LV2; right; exact ZLIV1)) as DZ4. pose proof (LD4 _ _ ltac:(rewrite LV2, LV1; right; exact OLIV)) as DO4.
      pose proof (FD4 fS kS ltac:(rewrite FRS3, FRS2, FRS1; right; exact FSIN)) as DFR4. pose proof (LD4 _ _ PLIV2) as D164.
      unfold disj in DZ, DO, DZ4, DO4, D164. rewrite NBE in DSP, DZ, DO, DFR, D164. unfold nb4 in DSP4, DZ4, DO4, DFR4, D164.
      split; [intros X; exfalso; apply X; reflexivity|].
      split. { intros _. split; [exact DSP|]. split; [clear - DFR FSLO FSHI; lia|]. split; [clear - DZ ZLO ZHI; lia| clear - DO OLO OHI; lia]. }
      split. { intros _. split; [exact DSP4|]. split; [clear - DFR4 FSLO FSHI; lia|]. split; [clear - DZ4 ZLO ZHI; lia| clear - DO4 OLO OHI; lia]. }
      intros _ _. exact D164.
    + right. split; [clear - UC; lia|]. right. repeat split; [exact SM1| exact PNZ| exact P4NZ].
    + apply d10_blkS; cbn [cx_blocks b_small b_n b_ll16 b_ll4]; [exact SM1| clear - UC; lia| rewrite <- NBE; exact BJ| exact BJ4].
    + exact HD7. + exact NBU3. + exact CF3. + exact MID9. + exact MT0. + reflexivity. + reflexivity. + exact CCC0. + exact SV5. + exact DR9. + exact STRM7. + exact PAY5. + exact LIB9. + exact ZSH3.
    + exact LO9. + exact HI5. + exact AFR9. + exact ST9. + exact Hc9.
Qed.
End D10T.
