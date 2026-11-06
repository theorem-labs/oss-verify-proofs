(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import ShapeAlg.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import ImageA RzCPS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Layout RT_iface D_defs D_kit I_read RT_liveprim RT_globals.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require L_libA D_libiface.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.L2 Require Import L2Kit L2Act L2StmtD A0_fs_L2f A0_sessK A0F_decK A0F_decX A0F_dec_L2a A0F_dec_L2b.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel BzTac BzTables CmpMem AsanKit AsanKit2 AsanCut.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzDefs BzInv BzContracts.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState BzDBlock BzDK BzDU5 BzDOKp DecCutFA A0F_decV A0F_decRet A0F_decCutsA A0F_dec_pro1 A0F_dec_U0.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOKp OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutFA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decV OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decRet OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decCutsA.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.
#[local] Notation mem := (word -> option byte).

(* [comment removed for export] *)
Definition dk_ph_h0 (cx : bctx) : dsh :=
  DSH (b_strm cx) 14 (Z_to_bv 8 0) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0] 0 (Z_to_bv 8 0) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]
      0 0 0 0 (b_n cx) (Z_to_bv 8 (b_small cx)) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0] 0 0 0 (Z_to_bv 64 0) (Z_to_bv 64 0).

Lemma dk_mod16_q : forall x, x mod 16 = 0 -> exists q, x = 16 * q.
Proof. intros x H. exists (x / 16). Z.div_mod_to_equations. lia. Qed.

Section DECT.
Context {ACEIL__ : ACeil}.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis AF_DRV : forall Σ m, ART RT Σ m -> drv_consts m.
Hypothesis AF_PRIM : af_live_primary RT.
Hypothesis SMAL : stack_malloc_contract RT 0.
Hypothesis MSET : memset_icontract RT e_asan_memset.
Hypothesis HBCC : hbCreateDecodeTables_contract RT.

Theorem decompress14_cps : decompress14_contract RT.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m cx payload J d s zp zn op on lo usp W
    FDO MST Ha0 TP CEQ DML LIB0 DLIVE DPURE PLEN N1 NZF NZS DP ST14 AV FRMAX CRED ART0 MI0 ST0 LOW LOR SPT AL.
  subst a0. intros T c Hc Hk.
  destruct DLIVE as (SLIV & ZLIV & ZLO & ZHI & OLIV & OLO & OHI & TLIV & L16LIV & L4LIV & (fS & kS & FSIN & FSLO & FSHI) & T8 & ZSH).
  pose proof DPURE as (LEN0 & DLEN0 & SM01 & NR & S16 & TT16 & L1616 & L416 & SEP).
  pose proof alloc_ceiling_range as ACR.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR. fold usp in SPR.
  unfold RT_STACK, DEC_STACK in LOR.
  destruct (dk_mod16_q _ AL) as [qsp ALQ].
  set (P := 32 * ((usp - 832) / 32)).
  assert (PF : lo + 65536 + 256 <= P /\ P + 832 <= usp /\ usp <= P + 848 /\ P mod 16 = 0 /\ P mod 32 = 0 /\ exists q, P = 32 * q).
  { subst P. split; [clear - ALQ LOR; Z.div_mod_to_equations; lia|]. split; [clear - ALQ; Z.div_mod_to_equations; lia|]. split; [clear - ALQ; Z.div_mod_to_equations; lia|].
    split; [clear; Z.div_mod_to_equations; lia|]. split; [clear; Z.div_mod_to_equations; lia|]. exists ((usp - 832) / 32). reflexivity. }
  destruct PF as (YPl4 & YPh & YPa & SPA & SP32 & qP & PQ).
  assert (YPl : lo <= P) by (clear - YPl4; lia).
  clearbody P.
  pose proof (AF_PRIM Σ m _ _ ART0 SLIV ltac:(clear; lia)) as IE. unfold SEGTOP_A in IE.
  destruct (fs_aconsts_of_art RT AF Σ m ART0) as [AC AU].
  (* [comment removed for export] *)
  set (A1 := ACT ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m cx (dk_ph_h0 cx) (bs_of cx J s) lo A0F_decK.DG1 A0F_decK.DSV payload P 0 0 0 0).
  eapply (l1_realizes RT AF Σ PMc _ T c MST Hc).
  eapply (A0F_dec_pro1.A0F_pro1 A1 P _ YPl YPh YPa AL ltac:(cbn [A1 a_lo]; clear - LOW CEQ ACR; lia) qP m); [exact PQ| exact ST0| exact (kmem_inv_N _ _ MI0)| exact AC| exact AU|].
  intros m1 jb ng jg b1 b2 FR FRT GEO NG ST1 NMI1 MU1 WM1. apply evt_done. clear Hc. intros c1 Hc1.
  cbn [A1 a_lo a_sp a_s2 a_s3 a_s6 a_s7 a_s8 a_s9 a_s10 a_s11] in FRT, GEO, ST1, MU1, Hc1. fold usp in GEO, MU1.
  assert (MU1k : KFrame.munch [(P, usp)] m m1) by exact MU1.
  assert (ART1 : ART RT Σ m1).
  { apply (art_of_munch RT AF Σ m m1 [(P, usp)] P ART0 ltac:(clear - LOW YPl; lia) MU1k WM1). per_interval. left. unfold USTACK_TOP in *. match goal with HX : _ <= _ < _ |- _ => clear - SPT HX YPl; lia end. }
  assert (MI1 : KMem.mem_inv asegs m1).
  { apply (kmem_inv_munch' asegs [(P, usp)] m m1 MI0 MU1k NMI1). intros x Hx. revert Hx. refine (not_outside_cons _ _ _ _ _ _ _); [intro| refine (not_outside_nil _ _)].
    unfold KMem.UTOP, USTACK_TOP in *. match goal with HX : _ <= _ < _ |- _ => clear - SPT HX; lia end. }
  pose proof (ck_intro P CStack) as KP. pose proof (ck_intro usp CStack) as KU. pose proof (ck_intro lo CStack) as KLO.
  (* [comment removed for export] *)
  refine (cps_realizes asegs _ _ T c1 _ Hc1 _).
  { eapply (SMAL Σ PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 64 lo FDO MST ltac:(left; reflexivity) TP).
    - reflexivity.
    - change (fs_size 0) with 64. clear; lia.
    - reflexivity.
    - exact FRMAX.
    - exact CRED.
    - exact ART1.
    - exact MI1.
    - unfold call_ok. rewrite unsigned_lit by (clear - YPl YPh SPR LOW ACR CEQ; lia). unfold STACK_WIN, USTACK_TOP, RT_STACK in *.
      split; [exact ST1|]. split; [exact LOW|]. split; [clear - YPl4; lia|]. split; [clear - SPT YPh; lia| exact SPA]. }
  intros c2 (Σ1 & f & Hq2 & FRS1 & LV1 & SP1 & CR1 & FPOS & F64 & FTOP). change (fs_size 0) with 64 in *.
  destruct (ASTA_unpack RT Σ1 _ _ c2 Hq2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & WRF & WRS & ZSHF) & Hc2). clear Hq2.
  destruct RS2 as (u0 & u1 & u2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->).
  rewrite unsigned_lit in ST2, PRES2 by (clear - YPl YPh SPR LOW ACR CEQ; lia). change (64 - 8) with 56 in WRF. change (64 / 8) with 8 in WRS.
  rewrite (KMState.ret_pc_even 0x9e3d8 ltac:(lia) eq_refl) in Hc2.
  (* [comment removed for export] *)
  set (S := b_s cx) in *. set (STRM := b_strm cx) in *.
  set (Wc := [(S, S + 64144); (STRM, STRM + 20)] ++ blk_ivls cx).
  assert (TLIV0 : b_small cx = 0 -> In (b_tt cx, 400000 * b_n cx) (rt_live RT Σ)) by (intros E; exact (TLIV (NZF E))).
  assert (LLIV0 : b_small cx = 1 -> In (b_ll16 cx, 200000 * b_n cx) (rt_live RT Σ) /\ In (b_ll4 cx, 50000 * b_n cx) (rt_live RT Σ))
    by (intros E; destruct (NZS E) as [N16 N4]; split; [exact (L16LIV N16)| exact (L4LIV N4)]).
  assert (FSIN' : in_fframe (rt_frames RT Σ) STRM -> True) by (intros _; exact I).
  assert (WCF : forall x, ~ outside Wc x ->
            (S <= x < S + 64144) \/ (STRM <= x < STRM + 20) \/
            (b_small cx = 0 /\ b_tt cx <= x < b_tt cx + 400000 * b_n cx) \/
            (b_small cx = 1 /\ (b_ll16 cx <= x < b_ll16 cx + 200000 * b_n cx \/ b_ll4 cx <= x < b_ll4 cx + 50000 * b_n cx))).
  { intros x Hx. unfold Wc, blk_ivls in Hx. destruct SM01 as [E|E]; rewrite E in Hx; cbn [Z.eqb app outside] in Hx; clear - Hx E; lia. }
  assert (WCL : forall x, ~ outside Wc x -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp x).
  { intros x Hx. destruct (WCF x Hx) as [C|[C|[[E C]|[E [C|C]]]]].
    - right; right; left. exists S, 64144. split; [exact SLIV| exact C].
    - right; right; right; left. exists fS, kS. split; [exact FSIN| clear - C FSLO FSHI; lia].
    - right; right; left. exists (b_tt cx), (400000 * b_n cx). split; [exact (TLIV0 E)| exact C].
    - right; right; left. exists (b_ll16 cx), (200000 * b_n cx). split; [exact (proj1 (LLIV0 E))| exact C].
    - right; right; left. exists (b_ll4 cx), (50000 * b_n cx). split; [exact (proj2 (LLIV0 E))| exact C]. }
  set (SHF := f / 8 + 2147450880). change (shad f) with SHF in WRS, ZSHF.
  destruct (act_setup RT AF Σ Σ1 m m2 0 f SHF 64 8 lo P usp Wc eq_refl eq_refl eq_refl eq_refl ART0 ART2 FRS1 LV1 SP1 LOW
              ltac:(unfold RT_STACK; clear - YPl4; lia) ltac:(clear - YPh; lia) SPT SPA WCL) as (G & SOK & _ & FSEG & FHI & SHR0 & SHR1 & GSELF & GLV).
  assert (ANF : sanchor f SHF) by (split; [clear - F64; Z.div_mod_to_equations; lia| reflexivity]).
  clearbody SHF. unfold SEGTOP_A in FSEG.
  set (SHS := S / 8 + 2147450880). assert (ANS : sanchor S SHS) by (split; [clear - S16; Z.div_mod_to_equations; lia| reflexivity]). clearbody SHS.
  set (SHT := STRM / 8 + 2147450880). assert (ANT : sanchor STRM SHT) by (split; [exact T8| reflexivity]).
  assert (ZSH' : bytes_at a0segs m SHT (repeat z8 10)) by exact ZSH.
  (* [comment removed for export] *)
  set (A := ACT ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F2 fc2 m2 cx (dk_ph_h0 cx) (bs_of cx J s) lo A0F_decK.DG1 A0F_decK.DSV payload P f SHS SHT SHF).
  pose proof (dpureF_jwf _ _ _ _ _ _ DP) as JW. unfold jk_wf in JW. destruct JW as (_ & _ & _ & _ & _ & JQ1 & JQ2).
  pose proof (in_rel_length _ _ (dpureF_in _ _ _ _ _ _ DP)) as IRL.
  assert (AOK : act_ok AIHI0 A).
  { apply (dec_act_ok RT AF Σ1 m2 A zp zn op on (rt_frames RT Σ) fS kS ART2 ltac:(rewrite SP1; exact CEQ) FRS1 FSIN FSLO FSHI T8);
      cbn [A a_cx a_lo a_P a_sp a_h0 a_b0 a_payload a_shs a_sht a_shf a_fb]; rewrite ?LV1; try assumption; try reflexivity.
    - clear - LOW CEQ; lia.
    - clear - YPl4; lia.
    - fold usp. clear - YPh YPa; lia.
    - unfold dsh_wf, dk_ph_h0. cbn. repeat split; try reflexivity; clear - N1 NR; lia.
    - unfold bzs_wf, bs_of. cbn. repeat split; try assumption; clear - IRL PLEN LEN0 DLEN0 AV; lia.
    - unfold dk_ph_h0. cbn [sh_small]. apply unsigned_lit8. clear - SM01; lia. }
  (* [comment removed for export] *)
  pose proof (af_live_range RT AF Σ m _ _ ART0 SLIV) as (SL0 & SL1 & _). pose proof (af_live_offshadow RT AF Σ m _ _ ART0 SLIV) as SOFF.
  pose proof (af_live_range RT AF Σ m _ _ ART0 ZLIV) as (ZL0 & ZL1 & _).
  pose proof (af_frames_range RT AF Σ m _ _ ART0 FSIN) as (FS0 & FS1 & _). pose proof (af_frames_align RT AF Σ m _ _ ART0 FSIN) as (FS64 & FSSEG).
  pose proof (af_frames_hi RT AF Σ m _ _ ART0 FSIN) as FSOFF. unfold SEGTOP_A in FSSEG.
  assert (BLKR : forall x, ~ outside (blk_ivls cx) x -> 0 < x < lo /\ (x < 0x10000 \/ 0x61e000 <= x) /\ (x < 0x7fff7000 \/ 0x10007fff8000 <= x)).
  { intros x Hx. unfold blk_ivls in Hx. destruct SM01 as [E|E]; rewrite E in Hx; cbn [Z.eqb outside] in Hx.
    - pose proof (af_live_range RT AF Σ m _ _ ART0 (TLIV0 E)) as (B0 & B1 & B2). pose proof (af_live_offshadow RT AF Σ m _ _ ART0 (TLIV0 E)) as B3.
      unfold SEGTOP_A in B2. clear - Hx B0 B1 B2 B3 LOW. lia.
    - destruct (LLIV0 E) as [L16 L4].
      pose proof (af_live_range RT AF Σ m _ _ ART0 L16) as (B0 & B1 & B2). pose proof (af_live_offshadow RT AF Σ m _ _ ART0 L16) as B3.
      pose proof (af_live_range RT AF Σ m _ _ ART0 L4) as (C0 & C1 & C2). pose proof (af_live_offshadow RT AF Σ m _ _ ART0 L4) as C3.
      unfold SEGTOP_A in B2, C2. clear - Hx B0 B1 B2 B3 C0 C1 C2 C3 LOW. lia. }
  assert (DFLO : forall x, dfp cx x -> 0 < x < lo).
  { intros x [D|[D|[D|D]]]; [fold S in D; clear - D SL0 SL1 LOW; lia| fold STRM in D; clear - D FS0 FS1 FSLO FSHI LOW; lia| clear - D ZL0 ZL1 ZLO ZHI LOW; lia| exact (proj1 (BLKR x D))]. }
  assert (WCOUT : forall x, (0x10000 <= x < 0x61e000) \/ (0x7fff7000 <= x < 0x10007fff8000) -> outside Wc x).
  { intros x Hx. unfold Wc. cbn [app outside]. split; [clear - Hx IE SOFF; lia|]. split; [clear - Hx FSSEG FSOFF FSLO FSHI; lia|].
    destruct (outside_dec (blk_ivls cx) x) as [O|O]; [exact O| exfalso]. pose proof (BLKR x O) as B. clear - Hx B. lia. }
  (* [comment removed for export] *)
  assert (ACL0 : forall x, dfp cx x -> aclient (rt_live RT Σ) (rt_frames RT Σ) P x).
  { intros x [D|[D|[D|D]]].
    - right; right; left. exists S, 64144. split; [exact SLIV| exact D].
    - right; right; right; left. exists fS, kS. split; [exact FSIN| fold STRM in D; clear - D FSLO FSHI; lia].
    - right; right; left. exists zp, zn. split; [exact ZLIV| clear - D ZLO ZHI; lia].
    - unfold blk_ivls in D. destruct SM01 as [E|E]; rewrite E in D; cbn [Z.eqb outside] in D.
      + right; right; left. exists (b_tt cx), (400000 * b_n cx). split; [exact (TLIV0 E)| clear - D; lia].
      + assert (C : (b_ll16 cx <= x < b_ll16 cx + 200000 * b_n cx) \/ (b_ll4 cx <= x < b_ll4 cx + 50000 * b_n cx)) by (clear - D; lia).
        destruct C as [C|C]; right; right; left; [exists (b_ll16 cx), (200000 * b_n cx)| exists (b_ll4 cx), (50000 * b_n cx)]; (split; [first [exact (proj1 (LLIV0 E))| exact (proj2 (LLIV0 E))]| exact C]). }
  assert (DM1 : dmemL cx payload m1 (dvF cx J d s)).
  { apply (dmemLF_agree cx payload m m1 J d s PLEN); [| exact DML]. apply (agree_of_nmunch [(P, usp)] m m1 _ MU1). intros x Hx. cbn [KFrame.outside NFrame.outside].
    pose proof (DFLO x Hx) as B. split; [clear - B YPl; lia| exact I]. }
  assert (DM2L : dmemL cx payload m2 (dvF cx J d s)).
  { apply (dmemLF_agree cx payload m1 m2 J d s PLEN); [| exact DM1]. exact (agree_of_pres _ _ _ m1 m2 _ PRES2 ACL0). }
  assert (LIB1 : L_libA.LIB_A m1) by (apply (lib_of_munch [(P, usp)] m m1 LIB0 MU1); intros x Hx; cbn [outside]; split; [clear - Hx YPl LOW CEQ ACR; lia| exact I]).
  assert (LIB2 : L_libA.LIB_A m2) by (apply (lib_of_pfp _ _ _ [] m1 m2 LIB1 (pfp_of_pres _ _ _ [] m1 m2 PRES2)); intros x _; exact I).
  assert (SHTR : 0x7fff8000 <= SHT /\ SHT + 10 <= 0x10007fff8000).
  { pose proof (af_sp0_range RT AF Σ m ART0) as (_ & SP0T). unfold USTACK_TOP, STACK_WIN in *. subst SHT. clear - FS0 FS1 FSLO FSHI SP0T. Z.div_mod_to_equations. lia. }
  assert (SHTC : forall x, SHT <= x < SHT + 10 -> in_fframe_shadow (rt_frames RT Σ) x).
  { intros x Hx. exists fS, kS. split; [exact FSIN|]. unfold shad, SHB. subst SHT.
    pose proof FSHI as FSHI'. revert FSHI'. generalize (fs_size kS). intros fsz FSHI'. clear - Hx FSLO FSHI' FS64 T8. Z.div_mod_to_equations. lia. }
  assert (ZSH1 : bytes_at a0segs m1 SHT (repeat z8 10)).
  { apply (bytes_at_agree a0segs m m1 SHT _ ZSH'). apply (agree_of_nmunch [(P, usp)] m m1 _ MU1). intros x Hx. cbv beta in Hx. rewrite repeat_length in Hx. change (Z.of_nat 10) with 10 in Hx.
    cbn [KFrame.outside NFrame.outside]. split; [clear - Hx SHTR YPl LOW CEQ ACR; lia| exact I]. }
  assert (ZSH2 : bytes_at a0segs m2 SHT (repeat z8 10)).
  { apply (bytes_at_agree a0segs m1 m2 SHT _ ZSH1). apply (agree_of_pres _ _ _ m1 m2 _ PRES2). intros x Hx. cbv beta in Hx. rewrite repeat_length in Hx. change (Z.of_nat 10) with 10 in Hx.
    right; right; right; right. exact (SHTC x Hx). }
  (* [comment removed for export] *)
  assert (KZSH : forall m', PRESI usp (rt_frames RT Σ) (rt_live RT Σ) Wc m2 m' -> bytes_at a0segs m' SHT (repeat z8 10)).
  { intros m' PR. apply (bytes_at_agree a0segs m2 m' SHT _ ZSH2). intros a Ha. cbv beta in Ha. rewrite repeat_length in Ha. change (Z.of_nat 10) with 10 in Ha.
    apply PR. split; [right; right; right; right; exact (SHTC _ Ha)| apply WCOUT; right; clear - Ha SHTR; lia]. }
  assert (KLIB : forall m', PRESI usp (rt_frames RT Σ) (rt_live RT Σ) Wc m2 m' -> L_libA.LIB_A m').
  { intros m' PR. apply (L_libA.LIB_locA m2 m' LIB2). intros a (lo' & hi' & HIn & Hx). refine (PR a _).
    assert (R : 0xc4000 <= bv_unsigned a < 0xc4400 \/ 0xc4500 <= bv_unsigned a < 0xc4d00).
    { unfold D_libiface.LIB_FP in HIn. cbn [In] in HIn. destruct HIn as [HI|[HI|[]]]; injection HI as <- <-; [left| right]; exact Hx. }
    clear HIn Hx. split.
    - right; left. split.
      + exists 0xc3fe0, 0xc5ad8. split; [unfold CLIENT_STATIC; cbn [In]; left; reflexivity| clear - R; lia].
      + intros (l2 & h2 & HIn2 & Hx2). unfold RT_STATIC in HIn2. cbn [In] in HIn2.
        repeat (destruct HIn2 as [HI|HIn2]; [injection HI as <- <-; clear - R Hx2; lia|]). exact HIn2.
    - apply WCOUT. left. clear - R. lia. }
  (* [comment removed for export] *)
  assert (STEP2 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) P [] m1 m2) by exact (pfp_of_pres _ _ _ [] m1 m2 PRES2).
  clear ST1 DM1 LIB1 ZSH1 ZSH' DML. unfold FT_REGS in FRT. cbn [A1 a_s11 a_s10 a_s9 a_s8 a_s7 a_s6 a_s5 a_s4 a_s3 a_s2 a_s1 a_s0 a_ra] in FRT.
  xfer_rt G I STEP2 WM2 m1 m2.
  destruct (n_wr_at_rw_CB m2 f 56 WRF ltac:(clear; lia)) as (jf & FFJ). destruct (n_wr_at_rw_CB m2 SHF 8 WRS ltac:(clear; lia)) as (js & FSJ).
  destruct (release_inline2 AF G (mi := m2) Σ1 m2 eq_refl SOK ART2) as (_ & fl & _ & FLP & _). replace (f + 64 - 8) with (f + 56) in FLP by (clear; lia).
  (* [comment removed for export] *)
  assert (IV : INV RT A (rt_sp0 RT Σ) (rt_frames RT Σ) (rt_live RT Σ) Wc m2 (rt_credit RT Σ - 1) Σ1 m2).
  { unfold INV. cbn [A a_sp a_fb]. split; [exact SOK|]. split; [exact LV1|]. split; [exact CR1|]. split; [exact ART2|]. split; [exact MI2| apply presi_refl]. }
  set (Fu := (9 * length (s_in s) + 64)%nat).
  assert (FU : fuel_ok Fu d s).
  { unfold fuel_ok. subst Fu. pose proof (dpureF_bl _ _ _ _ _ _ DP) as BL. rewrite Nat2Z.inj_add, Nat2Z.inj_mul. cbn [Z.of_nat Pos.of_succ_nat]. clear - BL. lia. }
  set (R0 := drun Fu 14 (d_sv d) d s).
  pose proof (af_sp0_range RT AF Σ m ART0) as (_ & SP0T).
  assert (HKF : forall c' (Σ2 : rts RT) (m' : mem) (rv : Z) (L : dsv) (d' : dst) (s' : dstrm) (J' : jk)
      (z0 z1 z2 g1 g2 g3 g4 g5 g6 g7 z3 z4 z5 z6 : word) F' fc',
    DRet rv L d' s' = R0 ->
    ASTA RT Σ2 PMc (eq (MS (mkR ra sp gp tp z0 z1 z2 s0 s1 (Z_to_bv 64 rv) g1 g2 g3 g4 g5 g6 g7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 z3 z4 z5 z6)
                           F' (ret_pc ra) fc' None m' (seg_rom a0segs))) c' ->
    rt_frames RT Σ2 = rt_frames RT Σ -> rt_live RT Σ2 = rt_live RT Σ -> rt_sp0 RT Σ2 = rt_sp0 RT Σ -> rt_credit RT Σ2 = rt_credit RT Σ - 1 ->
    ART RT Σ2 m' -> KMem.mem_inv asegs m' -> stk asegs m' lo usp -> PRESI usp (rt_frames RT Σ) (rt_live RT Σ) Wc m2 m' ->
    dmem DI_A0 cx A0F_decK.DG1 A0F_decK.DSV payload m' (dvF cx J' (d_set_sv d' L) s') ->
    dpureF cx (bs_of cx J s) payload J' (d_set_sv d' L) s' -> dpost14 (d_set_sv d' L) ->
    realizes asegs c' T).
  { intros c' Σ2 m' rv L d' s' J' z0 z1 z2 g1 g2 g3 g4 g5 g6 g7 z3 z4 z5 z6 F' fc' ER Hc' FRS2 LV2 SP2 CR2 ART' MI' ST' PR' DM' DP' DPO'.
    apply Hk. exists Σ2. split; [| split; [exact LV2| split; [exact FRS2| split; [exact SP2| exact CR2]]]].
    eapply ASTA_conseq; [exact Hc'|]. intros ms <-. exists m', z0, z1, z2, g1, g2, g3, g4, g5, g6, g7, z3, z4, z5, z6, F', fc', J'.
    pose proof (BzDU5.BzDRv.decompress_rv d s) as RV.
    rewrite (decompress_eq14 d s) in RV |- * by (rewrite ST14; unfold BZ_X_MAGIC_1; clear; lia). rewrite ST14 in RV |- *.
    fold Fu in RV |- *. fold R0 in RV |- *. rewrite <- ER in RV |- *. cbn [dfin] in RV |- *.
    split; [reflexivity|]. split; [exact ART'|]. split; [exact MI'|]. split; [exact ST'|].
    split; [exact (dmemL_of m' cx _ _ _ _ DM')|]. split; [exact (KLIB m' PR')|]. split; [exact DP'|].
    split.
    - unfold dpost14W. split; [intros E2; exact (DPO' E2)|]. split; [| exact RV].
      intros _. pose proof (dpureF_rep _ _ _ _ _ _ DP') as RP. unfold drep in RP. change (2^32) with 4294967296 in RP. tauto.
    - exact (pres_final RT AF Σ lo P usp Wc m m1 m2 m' ART0 LOW YPl ltac:(clear - YPh; lia) MU1 PRES2 PR'). }
  (* [comment removed for export] *)
  assert (H14 : A0F_cut_H14 A (QL RT PMc T Σ1 R0) Fu).
  { refine (dec_H14 RT AF AF_DRV MSET HBCC A (rt_sp0 RT Σ) (rt_frames RT Σ) (rt_live RT Σ) Wc G m2 PMc FDO MST T AOK TP eq_refl eq_refl _ _ _ zp zn fS kS
              SLIV ZLIV ZLO ZHI TLIV0 LLIV0 FSIN FSLO FSHI (rt_credit RT Σ - 1) R0 HKF KLIB KZSH _ FHI _ _ IE CEQ Σ1 m2 F2 fc2 IV Fu).
    - cbn [A a_lo a_P]. unfold RT_STACK. clear - YPl4. lia.
    - intros x Hx. unfold W14, DSTATE_SIZE in Hx. cbn [A a_cx a_P a_sp a_fb a_shf] in Hx |- *. fold S STRM usp in Hx |- *.
      unfold Wc, blk_ivls in *. destruct SM01 as [E|E]; rewrite E in *; cbn [Z.eqb app outside KFrame.outside] in *; clear - Hx; lia.
    - intros x Hx. cbn [A a_cx] in Hx. fold S in Hx. unfold Wc. cbn [app outside]. clear - Hx. lia.
    - cbn [A a_cx]. fold STRM. clear - FSOFF FSLO FSHI. lia.
    - cbn [A a_P]. clear - YPl4 LOW CEQ ACR. lia.
    - cbn [A a_sp]. fold usp. unfold USTACK_TOP in SPT. clear - SPT. lia. }
  pose proof (dk_ash RT AF A (rt_sp0 RT Σ) (rt_frames RT Σ) (rt_live RT Σ) Wc m2 AOK zp zn SLIV ZLIV ZLO ZHI TLIV0 LLIV0 (rt_credit RT Σ - 1) KZSH
                ltac:(cbn [A a_cx]; fold STRM; clear - FSOFF FSLO FSHI; lia) FHI ltac:(cbn [A a_P]; clear - YPl4 LOW CEQ ACR; lia)
                ltac:(cbn [A a_sp]; fold usp; unfold USTACK_TOP in SPT; clear - SPT; lia) Σ1 m2 F2 fc2 IV) as ASH.
  eapply (l1_realizes RT AF Σ1 PMc _ T c2 MST Hc2).
  eapply evt_mono;
    [ eapply (A0F_dec_U0.A0F_dec14_entry A AOK ASH (QL RT PMc T Σ1 R0) Fu J d s jb jf js fl ng jg); cbn [A a_cx a_g1 a_sv a_payload a_m0 a_lo a_P a_sp a_b0 a_fb a_shf];
      [exact H14| exact (dmem_of_L RT AF AF_DRV Σ1 m2 cx payload _ ART2 LIB2 DM2L)| exact FR| exact FRT| exact GEO| exact NG| exact FFJ| exact (ro_C8_KN m2 _ _ FLP)| exact FSJ
      | exact ST2| exact (kmem_inv_N _ _ MI2)| exact DP| exact ST14| exact FU]
    | intros ms' HQ; exact (HQ (eq_refl R0)) ].
Qed.
End DECT.
