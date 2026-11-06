(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.AS Require Import Zp7 Z1b.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS Z119 FP.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Sj Require Import Zpf SjTape Zpk.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Spec Require Import Prelim Stdio Zpb Z3o.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Import Zvw Z4d.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.B Require Import Layout Zks Zkt Zi4 D_defs D_kit D_clx Z87 Z82 I_lkit Sj_rtf Zpm Zpl Zq2 Zq3
  Sj_new Zpt Zps Zpo Zwn Zsl Z4a Z73 Z5g Z6m Z71 Z5h Z5i Z5j
  Z6q Z6y Z6p Z45 Z5k Z4e Z4c Z4l Z4m Z4n Z4o Z52 Z57 Z54 Z56
  Z55 Z5b Z4q Z59 Z5a.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section TopA.
Variable RT : rt_sig.
Variable LIB : mem -> Prop.
Hypothesis LIB_loc : fp_local LIB_FP LIB.
Hypothesis AF : art_facts RT.

Hypothesis RC0 : rt_contracts RT.
Hypothesis SM2 : stack_malloc_contract_f RT 2.
Hypothesis MSET : memset_icontract_f RT e_asan_memset.
Hypothesis MCPY : memcpy_icontract_f RT e_asan_memcpy.
Hypothesis NEWA : new_cps RT e_newarr_nt.
Hypothesis DELA : del_cps RT e_delarr.
Hypothesis AFC : forall Σ m, ART RT Σ m -> cli_got_nothrow m.

Hypothesis SPL : splitinto_cpsA RT.
Hypothesis EMPF : emplf_cpsA RT.
Hypothesis EMPS : empls_cpsA RT.
Hypothesis VDES : vdestroy_cpsA RT.
Hypothesis PID : pid_cps RT LIB.
Hypothesis PID0 : pid0_cps RT LIB.
Hypothesis PDT : pdtor_cps RT (pdone RT).
Hypothesis HELEM : forall E, aenvA_ok E -> atp_elem_cpsA RT E TAPE_MAX_DEPTH.

Local Ltac ul := unfold FUZZ_STACK, PID_STACK in *; unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.

Theorem fuzz_one_t2A : fuzz_one_cps RT LIB.
Proof using LIB_loc AF RC0 SM2 MSET MCPY NEWA DELA AFC SPL EMPF EMPS VDES PID PID0 PDT HELEM.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m d bs lo
    FDO MST EA0 EA1 ETP D0 BSL BS INLV FRS0 LVPOS LVB CR0 S0C LIB0 IOS ART0 MI0 ST0 LOW LOR SPT SPA SPLE FRM.
  intros T c (Hc & FC0) Hk.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
  assert (LENc : zlength (chars bs) < 2^26) by (rewrite chars_length; exact BSL).
  pose proof (vcb_ok (chars bs) LENc) as VCB.

  apply (lftoi_vec RT LIB LIB_loc AF SM2 SPL EMPF EMPS Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m d bs lo
           FDO MST EA0 EA1 ETP D0 BSL BS INLV FRS0 LVPOS LVB CR0 LIB0 ART0 MI0 ST0 LOW LOR SPT SPA FRM T c (conj Hc FC0)).
  intros c1 ((Σ1 & sp' & f & A & Hc1 & SPR & SPA' & FPOS & F64 & FR1' & FSEG2 & FSELF & SHB0 & SHT) & FC1). fold usp in Hc1, SPR.
  destruct (ASTA_unpack_f RT Σ1 _ _ c1 Hc1 FC1) as (ms1 & (m1 & x1 & u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & s2y & u3 & u4 & u5 & u6 & F1 & fc1 & h3 & t & jp & -> & FRM1 & INV1) & _ & Hc1').
  clear Hc1. subst tp.

  apply (lftoi_par1 RT LIB LIB_loc AF MSET Σ Σ1 PMc m m1 usp sp' f A lo d bs ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x1 u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 s2y u3 u4 u5 u6 F1 fc1 h3 t jp
           FDO MST D0 BSL INLV FRS0 LOW LOR SPT SPA INV1 SPR SPA' FPOS F64 FR1' FSEG2 FSELF SHB0 SHT FRM1 T c1 (conj Hc1' FC1)).
  intros c2 ((Σ2 & sp2 & f2 & A2 & Hc2 & VL2 & CR2 & SPR2 & SPA2 & FPOS2 & F642 & FR2 & FSEG22 & FSELF2 & SHB2 & SHT2) & FC2).
  destruct (ASTA_unpack_f RT Σ2 _ _ c2 Hc2 FC2) as (ms2 & (m2 & y1 & v0 & v1 & v2 & e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & s2z & s7y & s8y & v3 & v4 & v5 & v6 & F2 & fc2
                                                  & h3' & t' & p1 & p17 & p57 & -> & FRM2 & INV2 & FP2) & _ & Hc2'). clear Hc2.

  apply (lftoi_par2 RT LIB LIB_loc AF MSET MCPY NEWA DELA PID PID0 AFC Σ Σ2 PMc m m2 usp sp2 f2 A2 lo d bs ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
           y1 v0 v1 v2 e0 e1 e2 e3 e4 e5 e6 e7 s2z s7y s8y v3 v4 v5 v6 F2 fc2 h3' t' p1 p17 p57
           FDO MST D0 BSL INLV FRS0 LVPOS LVB CR0 ltac:(clear - VCB; lia) LOW LOR SPT SPA INV2 FP2 VL2 CR2 SPR2 SPA2 FPOS2 F642 FR2 FSEG22 FSELF2 SHB2 SHT2 FRM2 T c2 (conj Hc2' FC2)).
  intros c3 ((Σg & sp3 & f3 & A3 & impl & idx & oc & ia & tape & sbuf & Hc3 & SPR3 & SPA3 & FPOS3 & F643 & FR3 & FSEG3 & FSELF3 & SHB3 & SHT3 & LVg & MODS & CRg) & FC3).
  destruct (ASTA_unpack_f RT Σg _ _ c3 Hc3 FC3) as (ms3 & (mg & z1 & w0 & w1 & w2 & g0 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & s2w & s6z & s7z & s8z & w3 & w4 & w5 & w6 & F3 & fc3
                                                  & h3'' & t'' & j20 & r & -> & FRM3 & INV3 & RC3 & R64 & OKR & PD3 & PST3) & _ & Hc3'). clear Hc3.

  apply (lftoi_par3 RT LIB LIB_loc AF RC0 PDT VDES HELEM Σ Σg PMc m mg usp sp3 f3 A3 lo d bs ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
           z1 w0 w1 w2 g0 g1 g2 g3 g4 g5 g6 g7 s2w s6z s7z s8z w3 w4 w5 w6 F3 fc3 h3'' t'' j20 impl idx oc ia tape sbuf r
           FDO MST D0 BSL INLV FRS0 LVPOS LVB CR0 VCB LOW LOR SPT SPA INV3 RC3 R64 OKR PD3 PST3 SPR3 SPA3 FPOS3 F643 FR3 FSEG3 FSELF3 SHB3 SHT3 LVg MODS CRg FRM3
           T c3 (conj Hc3' FC3)).
  intros c4 ((Σ4 & Hc4 & LV4 & FRS4 & SP4 & CR4) & FC4).
  apply Hk. split; [| exact FC4]. exists Σ4. rewrite ESP. split; [| split; [exact LV4| split; [exact FRS4| split; [exact SP4| exact CR4]]]].
  eapply ASTA_conseq; [exact Hc4|]. intros ms (m' & RS & AFT & PRES & LB). exists m'.
  split; [exact RS|]. split; [exact AFT|]. split; [exact PRES| exact LB].
Qed.

End TopA.
