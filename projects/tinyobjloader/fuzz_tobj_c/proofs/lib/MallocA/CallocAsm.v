(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "False"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "SVar"; "swf"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "Wcan"; "UStopLe"; "UStopLeOrPc"; "AE_A"; "L_calloc_null"; "L_calloc_ok"; "calloc_contractA"; "calloc_contractA_ex"; "@Corelib.Init.Datatypes"; "bool"; "list"; "true"; "prod"; "cons"; "nil"; "pair"; "Some"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "entailsA"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.CallocPosts"; "Lconv_S"; "s_fin"; "F_topr"; "Lc_null"; "Lc_ok"; "Lconv"; "PRODs"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "segments_reserved"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "m_vmmaps"; "vm_reserved"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM"; "IMG_M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "dfp_static"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec2"; "IMG_S"; "@stdpp.bitvector.definitions"; "bv"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require MemoFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RebuildM SpineMallocI SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocSec2 TopGlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ak.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ci.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ct.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cz.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require d0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require dm.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.TopGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SpineCallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineCallocI2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.CallocPosts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ci.CallocHit0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cy.CallocHit0E OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ct.CallocHit1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cy.CallocHit1E OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cy.SpineCallocSecOK0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cz.SpineCallocSecOK0E OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cy.SpineCallocSecOK0W1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.d0.SpineCallocSecOK0EW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cb.CRefillPlug0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dm.CRefillPlug1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bv.SpineCallocOvi OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c0.SpineCallocOviW1.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma Wcv_0 : ltac2:(tb__ "0|0|
S0S10S6S1cS8U0A1S9A2A1S12A3"). Proof. MemoFast.vmc. Qed.
Lemma Dcv_0 : ltac2:(tb__ "0|5|
S0S18S13S11S13S3S3A2M0A1M1S11S4A1M2A2M3A1S25S1bS20S8U0A1M4S9A2A1S1cG4S9A2A2S17G3S16G1G2S14G0S16S3S3S5PcA1S22A4S15G0A1A3S14S4S1eS15S4A1A3A4A2A3"). Proof. MemoFast.vmc. Qed.
Lemma ENTcv_0 : ltac2:(tb__ "0|1|
S0S10S1aS21S8U0A1M0S9A2SdSbG0S9A3S1dA3S12A3"). Proof. MemoFast.vmc. Qed.
Lemma ENTnl_0 : ltac2:(tb__ "0|1|
S0S10S1aS1fS8U0A1M0S9A2ScSbG0S9A3S1dA3S12A3"). Proof. MemoFast.vmc. Qed.
Lemma Wcv_1 : ltac2:(tb__ "0|0|
S0S10S6S1cS8U1A1SaA2A1S12A3"). Proof. MemoFast.vmc. Qed.
Lemma Dcv_1 : ltac2:(tb__ "0|5|
S0S18S13S11S13S3S3A2M0A1M1S11S4A1M2A2M3A1S25S1bS20S8U1A1M4SaA2A1S1cG4SaA2A2S17G3S16G1G2S14G0S16S3S3S5PcA1S22A4S15G0A1A3S14S4S1eS15S4A1A3A4A2A3"). Proof. MemoFast.vmc. Qed.
Lemma ENTcv_1 : ltac2:(tb__ "0|1|
S0S10S1aS21S8U1A1M0SaA2SdSbG0SaA3S1dA3S12A3"). Proof. MemoFast.vmc. Qed.
Lemma ENTnl_1 : ltac2:(tb__ "0|1|
S0S10S1aS1fS8U1A1M0SaA2ScSbG0SaA3S1dA3S12A3"). Proof. MemoFast.vmc. Qed.

Section ASM.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTM : ltac2:(tb__ "0|0|
S23S19VCST;R1A2S19S2bR2A2S1F_;F_;Fa;").
Hypothesis HCSTS : ltac2:(tb__ "0|0|
S23S19VCST;R1A2S19S2dR2A2S1F_;F_;Fa;").
Hypothesis HCSTD : ltac2:(tb__ "0|0|
S23S19VCST;R1A2S2S2cR2A1A1F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segsA.

Lemma law_res_c : ltac2:(tb__ "0|1|
S2aS7S11S2eQ40A1M0A1S27VAInv;R4R3R2R1A4S0S11S13G0G0A2A1S29S28R2A1A1S26S24A1A3F_;Fmd;Ftp;Frho;FA;").
Proof. intros A rho tp md (_ & _ & _ & _ & HM & _). destruct HM as (_ & _ & _ & _ & _ & _ & _ & HL). exact (proj1 HL). Qed.

Theorem calloc_contract_A : ltac2:(tb__ "0|0|
SeS24SbVAInv;VCST;VXGL;A5").
Proof.
  apply calloc_contractA_of_T. intros W st ok A Kc rho tp HW HKc Hokl Hokpl.
  destruct HW as [E|[E|[]]]; injection E as <- <-.
  - destruct (Z_lt_dec (bv_unsigned (rw rho 12%positive) * bv_unsigned (rw rho 13%positive)) (2 ^ 64)) as [Hmul|Hov].
    + eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (calloc_conv CST XGL (Wcan 0) UStopLe Wcv_0 Dcv_0 ENTcv_0 ENTnl_0 A Kc rho tp w Hmul Hw) |].
      exact (calloc_hit_0_P CST XGL HCST HXGL HCSTM HCSTD ok A Kc rho tp (PFc CST XGL (Wcan 0) UStopLe A Kc) (or_intror (or_introl eq_refl)) HKc Hokl Hokpl Hmul
               (fun Hz rhoE => refill_all_0 CST XGL HCST HXGL HCSTM HCSTD ok A Kc (rho_c rho) tp HKc Hokl Hokpl Hz rhoE)
               (calloc_sec_ok_0 CST XGL HCST HXGL HCSTM HCSTS HCSTD law_res_c ok A Kc (rho_c rho) tp HKc Hokl Hokpl)).
    + exact (calloc_ov_0 CST XGL HCST HXGL HCSTM HCSTS ok A Kc rho tp (Posts_calloc AE_A AInv CST XGL (Wcan 0) UStopLe A Kc) HKc Hokl (or_introl eq_refl) ltac:(lia)).
  - destruct (Z_lt_dec (bv_unsigned (rw rho 12%positive) * bv_unsigned (rw rho 13%positive)) (2 ^ 64)) as [Hmul|Hov].
    + eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (calloc_conv CST XGL (Wcan 1) UStopLeOrPc Wcv_1 Dcv_1 ENTcv_1 ENTnl_1 A Kc rho tp w Hmul Hw) |].
      exact (calloc_hit_1_P CST XGL HCST HXGL HCSTM HCSTD ok A Kc rho tp (PFc CST XGL (Wcan 1) UStopLeOrPc A Kc) (or_intror (or_introl eq_refl)) HKc Hokl Hokpl Hmul
               (fun Hz rhoE => refill_all_1 CST XGL HCST HXGL HCSTM HCSTD ok A Kc (rho_c rho) tp HKc Hokl Hokpl Hz rhoE)
               (calloc_sec_ok_1 CST XGL HCST HXGL HCSTM HCSTS HCSTD law_res_c ok A Kc (rho_c rho) tp HKc Hokl Hokpl)).
    + exact (calloc_ov_1 CST XGL HCST HXGL HCSTM HCSTS ok A Kc rho tp (Posts_calloc AE_A AInv CST XGL (Wcan 1) UStopLeOrPc A Kc) HKc Hokl (or_introl eq_refl) ltac:(lia)).
Qed.

Theorem calloc_contract_A_ex : ltac2:(tb__ "0|0|
SfS24SbVAInv;VCST;VXGL;A5").
Proof.
  apply calloc_contractA_ex_of_T. intros W st A Kc rho tp HW HKc.
  destruct HW as [E|[E|[]]]; injection E as <- <-.
  - destruct (Z_lt_dec (bv_unsigned (rw rho 12%positive) * bv_unsigned (rw rho 13%positive)) (2 ^ 64)) as [Hmul|Hov].
    + eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (calloc_conv CST XGL (Wcan 0) UStopLe Wcv_0 Dcv_0 ENTcv_0 ENTnl_0 A Kc rho tp w Hmul Hw) |].
      exact (ecalloc_hit_0_P CST XGL HCST HXGL HCSTM HCSTD A Kc rho tp (PFc CST XGL (Wcan 0) UStopLe A Kc) (or_intror (or_introl eq_refl)) HKc Hmul
               (fun Hz rhoE => erefill_all_0 CST XGL HCST HXGL HCSTM HCSTD A Kc (rho_c rho) tp HKc Hz rhoE)
               (ecalloc_sec_ok_0 CST XGL HCST HXGL HCSTM HCSTS HCSTD law_res_c A Kc (rho_c rho) tp HKc)).
    + exact (ecalloc_ov_0 CST XGL HCST HXGL HCSTM HCSTS A Kc rho tp (Posts_calloc AE_A AInv CST XGL (Wcan 0) UStopLe A Kc) HKc (or_introl eq_refl) ltac:(lia)).
  - destruct (Z_lt_dec (bv_unsigned (rw rho 12%positive) * bv_unsigned (rw rho 13%positive)) (2 ^ 64)) as [Hmul|Hov].
    + eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (calloc_conv CST XGL (Wcan 1) UStopLeOrPc Wcv_1 Dcv_1 ENTcv_1 ENTnl_1 A Kc rho tp w Hmul Hw) |].
      exact (ecalloc_hit_1_P CST XGL HCST HXGL HCSTM HCSTD A Kc rho tp (PFc CST XGL (Wcan 1) UStopLeOrPc A Kc) (or_intror (or_introl eq_refl)) HKc Hmul
               (fun Hz rhoE => erefill_all_1 CST XGL HCST HXGL HCSTM HCSTD A Kc (rho_c rho) tp HKc Hz rhoE)
               (ecalloc_sec_ok_1 CST XGL HCST HXGL HCSTM HCSTS HCSTD law_res_c A Kc (rho_c rho) tp HKc)).
    + exact (ecalloc_ov_1 CST XGL HCST HXGL HCSTM HCSTS A Kc rho tp (Posts_calloc AE_A AInv CST XGL (Wcan 1) UStopLeOrPc A Kc) HKc (or_introl eq_refl) ltac:(lia)).
Qed.
End ASM.
