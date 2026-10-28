(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 BsWalk RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_PrsStmt LbB_WoGen LbB_WoDefs LbB_WoKit.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Section WKit2.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

  Lemma wchain_call : forall e ff fp XSc sk LBk m', wpre H e -> winv H e ff fp XSc sk LBk m' ->
    as_chain H m' (wSP e) ((wSP e, bv_unsigned (w_ra e)) :: w_CH e)
    /\ (forall f r, In (f, r) ((wSP e, bv_unsigned (w_ra e)) :: w_CH e) -> wS1 e + 16 <= f).
  Proof.
    intros e ff fp XSc sk LBk m' HP HI.
    pose proof (wchain H HH e ff fp XSc sk LBk m' HP HI) as CH0.
    pose proof (winv_sv H e ff fp XSc sk LBk m' HI) as SV.
    pose proof (wpre_geo H e HP) as (CE & LO & SH1 & SH2 & SP16 & _).
    pose proof (wS1_facts H e HP) as (_ & S1SP & _ & _ & _ & _).
    pose proof aceil_facts as ACF.
    pose proof HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
                      & CHU & _).
    change (wsaved e) with ([C8 (w_s11 e); C8 (w_s10 e); C8 (w_s9 e); C8 (w_s8 e); C8 (w_s7 e); C8 (w_s6 e); C8 (w_s5 e); C8 (w_s4 e);
                             C8 (w_s3 e); C8 (w_s2 e); C8 (w_s1 e)] ++ [C8 (w_s0 e); C8 (w_ra e)]) in SV.
    apply rw_cells_app in SV as [_ SV2]. cbn [cells_size csize] in SV2. unfold WO_SAVED in SV2.
    replace (wSP e - 104 + Z.of_nat (8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + 0))))))))))))
      with (wSP e - 16) in SV2 by lia.
    pose proof (bv_unsigned_in_range 64 (w_s0 e)) as R0. pose proof (bv_unsigned_in_range 64 (w_ra e)) as R1.
    change (bv_modulus 64) with (2 ^ 64) in R0, R1.
    split.
    - eapply (ah_chain_cons H HH); [exact CH0 | lia | lia | exact SP16 | unfold AAPP_HI in *; lia | unfold AAPP_HI in *; lia |].
      rewrite !Z_to_bv_bv_unsigned. exact SV2.
    - intros f r [EQ|IN]; [injection EQ as <- <-; lia|]. pose proof (CHU f r IN). lia.
  Qed.

  Lemma wtrace : forall e pc0 p, wpre H e -> In (pc0, p) PO_PF ->
    trace_ok (as_TR H) pc0 (p ++ bv_unsigned (w_ra e) :: map snd (w_CH e)).
  Proof.
    intros e pc0 p HP IN.
    pose proof HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PF & _).
    exact (pf_ok_site (as_TR H) PO_PF (bv_unsigned (w_ra e)) (w_CH e) pc0 p PF IN).
  Qed.

  Lemma wtrace_dtor : forall e r, wpre H e -> In (APC0_FREE, [r]) PO_PF ->
    trace_ok (as_TR H) APC0_FREE (r :: map snd ((wSP e, bv_unsigned (w_ra e)) :: w_CH e)).
  Proof. intros e r HP IN. exact (wtrace e APC0_FREE [r] HP IN). Qed.

  Lemma wpm_pf : forall e, wpre H e -> pf_ok (as_TR H) PM_PF AWO_PM_RA ((wSP e, bv_unsigned (w_ra e)) :: w_CH e).
  Proof.
    intros e HP.
    pose proof HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PF & _).
    eapply pf_ok_call; [exact PF|]. unfold PO_PF. apply incl_appr. apply incl_refl.
  Qed.
End WKit2.
