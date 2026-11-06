(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim StrFun Stdio SjModel AtpModel.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjTape SjTapeList.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Sj_stage1_kit Atp_h_defs.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.B Require Import Layout RT_iface RT_iface2 RT_iface3 RT_iface5 D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_rtf Sj_akit Sj_acps Sj_hkit Sj_hkit2
     Sj_num_akit Sj_h_alloc Sj_stage2_iface Atp_fzwA Atp_setcapA Atp_activewA Atp_activeA Atp_defsA Atp_kitA Atp_h_defsA Atp_pidiA Atp_pdtorA
     Pj_lftoi1A Pj_defsA Pj_os_defsA El_defsA El_lf1A El_lf2A El_lf2bA El_phasesA El_frontA El_parsekA El_armkitA Atp_arrlA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Section Arm0.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable PMc : Model -> Prop.

Local Ltac ul := unfold FUZZ_STACK, PID_STACK in *; unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, SHB in *; lia.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Theorem arm0_okA : forall W, arm_cpsA RT PMc W 0.
Proof using AF.
  intros W Σ K X E sel idx jr jos t ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 t3 t4 t5 t6 F fc m
    FDO MST LK OKE LE WFS SEL IDX AL FRS LPA LVB CRB ARTg MIg STg NEED AM FRM XD AUX SPB POST.
  assert (NEED16 : lf_lo X + 16 <= lf_S1 X - 16) by (clear - NEED; unfold arm_needA in NEED; cbn in NEED; ul).
  pose proof (arm_entry_kit RT AF X E Σ 0 sel idx jr jos t m 16 LK OKE LE AL FRS ARTg AM ltac:(lia) NEED16) as (ARTM & SZN & AIM & SZD & SZT & SHBM).
  pose proof LK as [(SPR & SPA') (SPT & SPA) (LLO & LOR) (FPOS & F64 & FSEG & FLO) (FSELF & SHB0 & SHT)].
  destruct X as [usp sp' f lo]. cbn [lf_usp lf_S1 lf_F lf_lo] in *.
  destruct LE as (EDOC & EFD & EKD & ELO & EHI). cbn [lf_usp lf_S1 lf_F lf_lo] in EDOC, EFD, EKD, ELO, EHI.
  pose proof AM as (C16 & C100 & C128 & CE & CO & CS & AI & LIB & NL & IOS). cbn [lf_usp lf_S1 lf_F lf_lo] in C16, C100, C128, CE, CO, CS.
  pose proof (ael_root_elem E OKE) as [_ NR].
  pose proof OKE as OK'. destruct OK' as [_ _ _ _ _ _ _ _ (D8 & DF & DL & DS & DT) _ _].
  change (el_arm_pcA 0) with 0xb2360. unfold lf_st. cbn [lf_usp lf_S1 lf_F lf_lo].
  assert (ES : bv_unsigned (wz sp') = sp') by (apply unsigned_lit; ul).
  assert (DOCR : 0 < ae_DOC E < 2^47) by (rewrite EDOC; clear - FPOS FLO LOR SPT; ul).
  assert (FR47 : 0 < f /\ f + 1024 < 2^47 /\ 0 < sp' /\ sp' + 152 < 2^47) by (clear - FPOS FLO LOR SPT SPR; ul).
  replace (sp' - 16) with (sp' + -16) in SZD by lia.
  apply (aevt_evt RT AF PMc MST).

  zstep. zstep. step. if_lia. astep. replace (ae_DOC E mod 8) with 0 by lia. step. if_lia. zstep. zstep. zstep.
  eapply (tix_cps E OKE _ m F fc sp' 1 0xb2380);
    [exact AI| lia| exact (shb_cells_of_art RT AF Σ m ARTg)| exact SZD| rewrite ELO; exact STg| rewrite ELO; lia| rewrite EHI; clear - SPR; lia| clear - SPA'; Z.div_mod_to_equations; lia
    | exact MIg| lia| reflexivity|].
  intros m1 xa1 xa3 xa4 MU1 WM1 MI1 ST1. rewrite ELO in ST1.

  zstep. apply evt_done.
  replace (sp' + -16) with (sp' - 16) in MU1 by lia.
  apply (POST false (rt_credit RT Σ) Σ m1 fc F).
  exact (arm_post_below RT AF W 0 (mkLF usp sp' f lo) E Σ sel idx jr jos t m m1 fc 16 LK OKE (conj EDOC (conj EFD (conj EKD (conj ELO EHI)))) AL FRS ARTg AM ltac:(lia) NEED16
           MU1 WM1 MI1 ST1 FRM eq_refl).
Qed.
End Arm0.
