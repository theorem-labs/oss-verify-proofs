(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iq.
From Stdlib Require NArith PArith.
From LinuxProcessSemantics.Riscv Require Decode DecodeC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ix.

(* [comment removed for export] *)
Module SegQ3D_qc_arith.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "rw"; "SLit"; "valuation"; "SPUlt"; "SVar"; "eval"; "holds"; "SPBranch"; "SPNot"; "SPUle"; "@Corelib.Numbers.BinNums"; "Z"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "bv_signed"; "bv_unsigned"; "@Corelib.Init.Datatypes"; "cons"; "app"; "list"; "nil"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "pow"; "lt"; "mul"; "opp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.SegQ3D_states"; "clsB"; "@Corelib.Lists.ListDef"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m9.SegQ3D_qc_arith"; "FC_it"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iq.SegQ3D_qi_arith"; "FQ_stk"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_EQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "max_count"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "V_DEPTH"; "pre_facts"; "top_high"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iq.SegQ3D_qc_defs"; "factsC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQ3_states"; "DEPTH_R"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundL SymSoundV SymSoundM SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3 SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Inv Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ_defs SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ie.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQtr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ3R_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require il.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require im.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require id.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require io.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iq.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.SegQ3_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.SegQ3D_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.SegQ3G_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQtr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.SegQ3R_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ3R_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.SegQ3DM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.SegQ3D_inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.im.SegQ3D_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.SegQI_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.id.SegQI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQI_side OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.SegQC_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SegQ3D_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SegQ3D_qi_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iq.SegQ3D_qi_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iq.SegQ3D_qc_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma signed_add15 : ltac2:(tb__ "0|5|
S5SdS0SdS10Q40M0S3R2S22A2A2R1A3S1S16S1bS18Z2M1Z28A2A1R2A2S16R2N600A2A2S1S0SdS11G0S8R4S26S7PfA1S4Zc0M2A1A2A2M3A2S17S17R3G2A2M4S18G1Z40A2A2A3S0SdS10G0G3A2G4A3A2F_;F_;FD;Frho;").
Proof.
  intros rho D HD HR. pose proof (signed_neg_unsigned (rw rho V_DEPTH) D HD ltac:(lia)) as EU.
  assert (E1 : bv_unsigned (eval rho (add (SVar 15) (SLit 192))) = D + 192 + 2 ^ 64).
  { unfold add. cbn [eval]. rewrite add_val. change (rw rho 15%positive) with (rw rho V_DEPTH). rewrite EU, u64_lit by lia. rewrite Z.mod_small by lia. lia. }
  split; [exact E1|]. rewrite signed_of_unsigned, E1. unfold snorm. cbv zeta. rewrite (Z.mod_small (D + 192 + 2 ^ 64)) by lia.
  replace (D + 192 + 2 ^ 64 <? 2 ^ 63) with false by (symmetry; apply Z.ltb_ge; lia). lia.
Qed.

Lemma stk_facts_hold : ltac2:(tb__ "0|0|
S25S5S24R2R1A2S1dS2S9R2A1S23S28A1A3S1dS2S9R3A1S1fA3F_;F_;Frho;FA;").
Proof.
  intros A rho HT HF. destruct (stk_facts A rho HT HF) as (HD & HTOP & Hsp). pose proof (topG_range (aa_geom A)) as TG.
  pose proof (F_sp_holds A rho HT HF) as HSP. unfold F_sp in HSP. cbn [holds eval] in HSP. rewrite u64_lit in HSP by lia.
  pose proof (Forall_inv (Forall_inv_tail HF)) as Hf. unfold holds, F_sp_high in Hf. cbn [eval] in Hf. rewrite add_val in Hf. rewrite u64_lit in Hf by lia.
  pose proof (signed_neg_unsigned (rw rho V_DEPTH) _ eq_refl ltac:(lia)) as EU. rewrite EU in Hf.
  replace (bv_unsigned (rw rho 10%positive) + (bv_signed (rw rho V_DEPTH) + 2 ^ 64)) with (bv_unsigned (rw rho 10%positive) + bv_signed (rw rho V_DEPTH) + 1 * 2 ^ 64) in Hf by lia.
  rewrite Z.mod_add in Hf by lia. rewrite Z.mod_small in Hf by lia.
  destruct (signed_add15 rho _ eq_refl HD) as [EA ES].
  assert (ESP : bv_unsigned (eval rho spD) = bv_unsigned (rw rho 10%positive) - 192).
  { unfold spD. rewrite (eval_add_lit A rho (SVar 10) (bv_unsigned (rw rho 10%positive)) (-192)); [apply u64_lit; lia | cbn [eval]; symmetry; apply Z_to_bv_bv_unsigned | lia | lia | lia]. }
  unfold FQ_stk. repeat apply Forall_cons; try apply Forall_nil.
  - cbn [holds]. change (eval rho (SLit 140735332483072)) with (Z_to_bv 64 140735332483072). rewrite u64_lit by lia.
    unfold add at 1. cbn [eval]. rewrite add_val. fold (add (SVar 15) (SLit 192)). rewrite ESP, EA.
    replace (bv_unsigned (rw rho 10%positive) - 192 + (bv_signed (rw rho V_DEPTH) + 192 + 2 ^ 64)) with (bv_unsigned (rw rho 10%positive) + bv_signed (rw rho V_DEPTH) + 1 * 2 ^ 64) by lia.
    rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. exact Hf.
  - cbn [holds branch_taken]. apply negb_true_iff. unfold bv_lts. apply Z.ltb_ge. rewrite ES. change (eval rho (SLit (-1024))) with (Z_to_bv 64 (-1024)). rewrite signed_lit.
    change (snorm (-1024)) with (-1024). lia.
  - cbn [holds branch_taken]. apply negb_true_iff. unfold bv_lts. apply Z.ltb_ge. rewrite ES. change (eval rho (SLit (-1099511627776))) with (Z_to_bv 64 (-1099511627776)). rewrite signed_lit.
    change (snorm (-1099511627776)) with (-1099511627776). lia.
Qed.

Lemma clsB_val : ltac2:(tb__ "0|7|
S5SdSdSdS0SfQ40M0A1M1S3R4Pa6A2SeG0R2A2A3S0G1S3R5P9bA2SeG0R4A2A3S0SdR4S17S17R5S1aZ18M2S18Z2M3Z20A2M4A2A2S1aZ10M5R3A2A2A3S16Z0M6R4A2S19S1aG5R5A2G4A2S16G6R8A2S19R8S18G3Z40A2A2S0G1S8RbS1cA2SeG0G2A2A3F_;F_;F_;F_;F_;F_;F_;Fy;Fa;FSB;Frho;").
Proof.
  intros rho SB a y E166 E155 Ea Hy Hy2 HSB Ha. apply bv_eq. rewrite (u64_lit 24) by lia.
  unfold clsB, vB, vSB. rewrite U_srl_lit, U_sll_lit, U_sub. cbn [eval]. rewrite E166, E155, !u64_lit by lia. change (27 mod 64) with 27. change (59 mod 64) with 59. unfold M64v.
  replace (a - SB) with (24 * 2 ^ 32 + 16 * y) by lia. rewrite (Z.mod_small (24 * 2 ^ 32 + 16 * y)) by lia.
  replace ((24 * 2 ^ 32 + 16 * y) * 2 ^ 27) with (16 * y * 2 ^ 27 + 24 * 2 ^ 59) by lia.
  rewrite Z.mod_small by lia. rewrite Z.div_add by lia. rewrite Z.div_small by lia. reflexivity.
Qed.

Definition FC_it : list sprop := ltac2:(tb__ "0|2|
S12S2S6S4Z0A1M0S1cA2S12S2S6S1cS4Z20A1A2S12S2SbSaS20S7PcfA1M1G0A3A1S12S2S6S7PceA1G1A2S12S2ScG1S4Z100A1A2S15S2A1A3A3A3A3A3").
Lemma factsC_eq : ltac2:(tb__ "0|0|
S0S14S2A1S27S13S2S1fS1eA3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma qc_it_facts : ltac2:(tb__ "0|4|
S5SdS0SfQ40M0A1M1S8R2S1cA2SeG0Z18M2A2A3S0G1S3R3PceA2SeG0R2A2A3S0G1S3R4PcfA2SeG0S21G2A1M3A2A3S1S16Z0R4A2S19R4G3A2A2S1dS2S9R6A1S1eA3F_;F_;F_;F_;Fk;Frho;").
Proof.
  intros rho k EC E206 E207 Hk. change (max_count 24) with 2 in *. unfold FC_it. repeat apply Forall_cons; try apply Forall_nil.
  - cbn [holds]. rewrite EC. change (eval rho (SLit 0)) with (Z_to_bv 64 0). rewrite !u64_lit by lia. lia.
  - cbn [holds]. rewrite EC. change (eval rho (SLit 32)) with (Z_to_bv 64 32). rewrite !u64_lit by lia. lia.
  - cbn [holds branch_taken eval]. rewrite E207. intros HB. unfold bv_eqb in HB. apply Z.eqb_eq in HB. rewrite !u64_lit in HB by lia. lia.
  - cbn [holds eval]. rewrite E206, E207, !u64_lit by lia. lia.
  - cbn [holds eval]. rewrite E207, !u64_lit by lia. lia.
Qed.
End SegQ3D_qc_arith.

(* [comment removed for export] *)
Module F0A_iL0A.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "KcA"; "Kc_ok"; "@Corelib.Init.Datatypes"; "list"; "false"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m9.F0A_iL0A.IL0A"; "contF"; "econtF"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.F0A_cL0A"; "ED_L0A_1"; "ED_L0A_2"; "Ebg_L0A"; "Edr_L0A"; "P0_L0A"; "TD_L0A_1"; "TD_L0A_2"; "Xf_L0A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "HDF"; "HDFE"; "depot_onlyKf"; "rigF"; "JF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5"; "hd_link"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymEntail SymFrame SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CompleteA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ix.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ie.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.F0A_skelc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.F0A_cL0A.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section IL0A.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let W : list ulink := Wcan 0.
Let st : ustop := UStopLe.
Let JFi (b : bool) (A : AA) (Kc : KcA) (rho1 : valuation) : jpredA := ltac2:(tb__ "0|0|
S1fU0S1Vb;VA;VKc;Vrho1;A6").

Definition contF (keep : Z -> Prop) (ok : world -> Prop) (A : AA) (Kc : KcA) (rho1 : valuation) (E : axst) (Q : assn) : Prop := ltac2:(tb__ "0|0|
SaS0S0S4SbQ40A1A1S1dVA;R4A2S20Vkeep;Vrho1;R4A3S10Vsegs;Vok;S7Vsegs;VJFi;S5R6VKc;R5A4VE;R4R3A5VQ;A4F_;F_;FtpE;FrhoE;Frho1';FA';").
Definition econtF (keep : Z -> Prop) (A : AA) (Kc : KcA) (rho1 : valuation) (E : axst) (Q : world -> Prop) : Prop := ltac2:(tb__ "0|0|
SaS0S0S4SbQ40A1A1S1dVA;R4A2S20Vkeep;Vrho1;R4A3SfVsegs;S7Vsegs;VJFi;S5R6VKc;R5A4VE;R4R3A5VQ;A3F_;F_;FtpE;FrhoE;Frho1';FA';").

Theorem free_spine_L0A : ltac2:(tb__ "0|1|
SeOF_;S11OF_;SaS2S0S0S4SbQ40A1A1S12S3R5A1S9Vsegs;R8S8R6A1A3S1eR6R5A2S1bU0M0S1RbRaR9R8R6S13S18R4AaS1bG0S1RcRbRaR9R7S14S19R5AaScRdRcRbRaR8S15R6A7ScReRdRcRbR9S16R7A7ScRfReRdRcRaS1aR8A7S0S10Vsegs;R10S7Vsegs;VJFi;S6RfReRcA4S17R1RbA5RaA4FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR HD1 HD2 HBIG HQ3 HXF rhoP.
  assert (HUS : stopJ_stable W st) by (first [apply stopJ_stable_le | apply stopJ_stable_nil]).
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Eps_L0A rhoX tpX) Q)
            /\ (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Ebg_L0A rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (f0_s4 0%nat st false Eps_L0A C3_L0A Ems_L0A C4_L0A TM0_L0A run4_L0A RM_L0A D3_L0A W3_L0A EQ3_L0A NX3b_L0A RUN4_L0A L4_L0A D4_L0A W4_L0A EQ4_L0A
             HeM_L0A HchkM_L0A HTM_L0A FBM_L0A ok A' Kc rho rho1' tpX Q HUS HKc Hok HR').
    intros rhoM tpM. rewrite ETM_L0A.
    apply (f0_s5 0%nat st q_L0A false TM_L0A Eq_L0A EQ_L0A TQ0_L0A run5_L0A RQ_L0A NX5_L0A RUN5_L0A L5_L0A AXQ_L0A HeQ_L0A HchkQ_L0A HTQ_L0A FBQ_L0A
             ok A' Kc rho1' tpM Q HUS HKc Hok).
    intros rhoQ. rewrite ETQ_L0A.
    apply (f0_s6 0%nat st false TQ_L0A Edr_L0A Xf_L0A run6_L0A NX6_L0A RUN6_L0A L6_L0A ok A' Kc rho1' tpM Q HUS HKc Hok).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (f0_s1c 0%nat st true P0_L0A exits1_L0A Cert1_L0A ok A Kc rho1 tp Q HUS HKc Hok).
  intros E rhoE HinE. unfold exits1_L0A in HinE. destruct HinE as [<-|[<-|[]]].
  - apply (f0_s2 0%nat st true S1c_L0A_1 C2_L0A_1 EfD_L0A_1 ED_L0A_1 run2_L0A_1 D2_L0A_1 W2_L0A_1 NX2_L0A_1 EQ2_L0A_1 RUN2_L0A_1 L2_L0A_1 AXD_L0A_1
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 0%nat st false TD_L0A_1 TDr_L0A_1 CD_L0A Eps_L0A Ebg_L0A run3_L0A AXDr_L0A_1 ENTD_L0A_1 RUN3_L0A L3_L0A NX3_L0A
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 0%nat st true S1c_L0A_2 C2_L0A_2 EfD_L0A_2 ED_L0A_2 run2_L0A_2 D2_L0A_2 W2_L0A_2 NX2_L0A_2 EQ2_L0A_2 RUN2_L0A_2 L2_L0A_2 AXD_L0A_2
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 0%nat st false TD_L0A_2 TDr_L0A_2 CD_L0A Eps_L0A Ebg_L0A run3_L0A AXDr_L0A_2 ENTD_L0A_2 RUN3_L0A L3_L0A NX3_L0A
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
Qed.

Theorem efree_spine_L0A : ltac2:(tb__ "0|1|
SeOF_;SaS2S0S0S4SbQ40A1A1S11OF_;S3R5A1S1eR5R4A2S1cU0M0S1R9R8R7R5S13S18R3A9S1cG0S1RaR9R8R6S14S19R4A9SdRbRaR9R7S15R5A6SdRcRbRaR8S16R6A6SdRdRcRbR9S1aR7A6S0SfVsegs;S7Vsegs;VJFi;S6ReRdRbA4S17R1RaA5R9A3FrhoP;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR HD1 HD2 HBIG HQ3 HXF rhoP.
  assert (HUS : stopJ_stable W st) by (first [apply stopJ_stable_le | apply stopJ_stable_nil]).
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Eps_L0A rhoX tpX) Q)
            /\ (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Ebg_L0A rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (ef0_s4 0%nat st false Eps_L0A C3_L0A Ems_L0A C4_L0A TM0_L0A run4_L0A RM_L0A D3_L0A W3_L0A EQ3_L0A NX3b_L0A RUN4_L0A L4_L0A D4_L0A W4_L0A EQ4_L0A
             HeM_L0A HchkM_L0A HTM_L0A FBM_L0A A' Kc rho rho1' tpX Q HUS HKc HR').
    intros rhoM tpM. rewrite ETM_L0A.
    apply (ef0_s5 0%nat st q_L0A false TM_L0A Eq_L0A EQ_L0A TQ0_L0A run5_L0A RQ_L0A NX5_L0A RUN5_L0A L5_L0A AXQ_L0A HeQ_L0A HchkQ_L0A HTQ_L0A FBQ_L0A
             A' Kc rho1' tpM Q HUS HKc).
    intros rhoQ. rewrite ETQ_L0A.
    apply (ef0_s6 0%nat st false TQ_L0A Edr_L0A Xf_L0A run6_L0A NX6_L0A RUN6_L0A L6_L0A A' Kc rho1' tpM Q HUS HKc).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (ef0_s1c 0%nat st true P0_L0A exits1_L0A (eq_refl : (GW <=? ss_next (ax_S P0_L0A))%positive = true) ECert1_L0A A Kc rho1 tp Q HUS HKc).
  intros E rhoE HinE. unfold exits1_L0A in HinE. destruct HinE as [<-|[<-|[]]].
  - apply (ef0_s2 0%nat st true S1c_L0A_1 C2_L0A_1 EfD_L0A_1 ED_L0A_1 run2_L0A_1 D2_L0A_1 W2_L0A_1 NX2_L0A_1 EQ2_L0A_1 RUN2_L0A_1 L2_L0A_1 AXD_L0A_1
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 0%nat st false TD_L0A_1 TDr_L0A_1 CD_L0A Eps_L0A Ebg_L0A run3_L0A AXDr_L0A_1 ENTD_L0A_1 RUN3_L0A L3_L0A NX3_L0A
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 0%nat st true S1c_L0A_2 C2_L0A_2 EfD_L0A_2 ED_L0A_2 run2_L0A_2 D2_L0A_2 W2_L0A_2 NX2_L0A_2 EQ2_L0A_2 RUN2_L0A_2 L2_L0A_2 AXD_L0A_2
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 0%nat st false TD_L0A_2 TDr_L0A_2 CD_L0A Eps_L0A Ebg_L0A run3_L0A AXDr_L0A_2 ENTD_L0A_2 RUN3_L0A L3_L0A NX3_L0A
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
Qed.
End IL0A.
End F0A_iL0A.

(* [comment removed for export] *)
Module F0A_iL0Be.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "KcA"; "Kc_ok"; "@Corelib.Init.Datatypes"; "list"; "false"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m9.F0A_iL0Be.IL0Be"; "contF"; "econtF"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.F0A_cL0Be"; "ED_L0Be_1"; "ED_L0Be_2"; "Ebg_L0Be"; "Edr_L0Be"; "P0_L0Be"; "TD_L0Be_1"; "TD_L0Be_2"; "Xf_L0Be"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "HDF"; "HDFE"; "depot_onlyKf"; "rigF"; "JF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5"; "hd_link"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymEntail SymFrame SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CompleteA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ix.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ie.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.F0A_skelc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.F0A_cL0Be.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section IL0Be.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let W : list ulink := Wcan 0.
Let st : ustop := UStopLe.
Let JFi (b : bool) (A : AA) (Kc : KcA) (rho1 : valuation) : jpredA := ltac2:(tb__ "0|0|
S1fU0S1Vb;VA;VKc;Vrho1;A6").

Definition contF (keep : Z -> Prop) (ok : world -> Prop) (A : AA) (Kc : KcA) (rho1 : valuation) (E : axst) (Q : assn) : Prop := ltac2:(tb__ "0|0|
SaS0S0S4SbQ40A1A1S1dVA;R4A2S20Vkeep;Vrho1;R4A3S10Vsegs;Vok;S7Vsegs;VJFi;S5R6VKc;R5A4VE;R4R3A5VQ;A4F_;F_;FtpE;FrhoE;Frho1';FA';").
Definition econtF (keep : Z -> Prop) (A : AA) (Kc : KcA) (rho1 : valuation) (E : axst) (Q : world -> Prop) : Prop := ltac2:(tb__ "0|0|
SaS0S0S4SbQ40A1A1S1dVA;R4A2S20Vkeep;Vrho1;R4A3SfVsegs;S7Vsegs;VJFi;S5R6VKc;R5A4VE;R4R3A5VQ;A3F_;F_;FtpE;FrhoE;Frho1';FA';").

Theorem free_spine_L0Be : ltac2:(tb__ "0|1|
SeOF_;S11OF_;SaS2S0S0S4SbQ40A1A1S12S3R5A1S9Vsegs;R8S8R6A1A3S1eR6R5A2S1bU0M0S1RbRaR9R8R6S13S18R4AaS1bG0S1RcRbRaR9R7S14S19R5AaScRdRcRbRaR8S15R6A7ScReRdRcRbR9S16R7A7ScRfReRdRcRaS1aR8A7S0S10Vsegs;R10S7Vsegs;VJFi;S6RfReRcA4S17R1RbA5RaA4FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR HD1 HD2 HBIG HQ3 HXF rhoP.
  assert (HUS : stopJ_stable W st) by (first [apply stopJ_stable_le | apply stopJ_stable_nil]).
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Eps_L0Be rhoX tpX) Q)
            /\ (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Ebg_L0Be rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (f0_s4 0%nat st false Eps_L0Be C3_L0Be Ems_L0Be C4_L0Be TM0_L0Be run4_L0Be RM_L0Be D3_L0Be W3_L0Be EQ3_L0Be NX3b_L0Be RUN4_L0Be L4_L0Be D4_L0Be W4_L0Be EQ4_L0Be
             HeM_L0Be HchkM_L0Be HTM_L0Be FBM_L0Be ok A' Kc rho rho1' tpX Q HUS HKc Hok HR').
    intros rhoM tpM. rewrite ETM_L0Be.
    apply (f0_s5 0%nat st q_L0Be false TM_L0Be Eq_L0Be EQ_L0Be TQ0_L0Be run5_L0Be RQ_L0Be NX5_L0Be RUN5_L0Be L5_L0Be AXQ_L0Be HeQ_L0Be HchkQ_L0Be HTQ_L0Be FBQ_L0Be
             ok A' Kc rho1' tpM Q HUS HKc Hok).
    intros rhoQ. rewrite ETQ_L0Be.
    apply (f0_s6 0%nat st false TQ_L0Be Edr_L0Be Xf_L0Be run6_L0Be NX6_L0Be RUN6_L0Be L6_L0Be ok A' Kc rho1' tpM Q HUS HKc Hok).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (f0_s1c 0%nat st true P0_L0Be exits1_L0Be Cert1_L0Be ok A Kc rho1 tp Q HUS HKc Hok).
  intros E rhoE HinE. unfold exits1_L0Be in HinE. destruct HinE as [<-|[<-|[]]].
  - apply (f0_s2 0%nat st true S1c_L0Be_1 C2_L0Be_1 EfD_L0Be_1 ED_L0Be_1 run2_L0Be_1 D2_L0Be_1 W2_L0Be_1 NX2_L0Be_1 EQ2_L0Be_1 RUN2_L0Be_1 L2_L0Be_1 AXD_L0Be_1
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 0%nat st false TD_L0Be_1 TDr_L0Be_1 CD_L0Be Eps_L0Be Ebg_L0Be run3_L0Be AXDr_L0Be_1 ENTD_L0Be_1 RUN3_L0Be L3_L0Be NX3_L0Be
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 0%nat st true S1c_L0Be_2 C2_L0Be_2 EfD_L0Be_2 ED_L0Be_2 run2_L0Be_2 D2_L0Be_2 W2_L0Be_2 NX2_L0Be_2 EQ2_L0Be_2 RUN2_L0Be_2 L2_L0Be_2 AXD_L0Be_2
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 0%nat st false TD_L0Be_2 TDr_L0Be_2 CD_L0Be Eps_L0Be Ebg_L0Be run3_L0Be AXDr_L0Be_2 ENTD_L0Be_2 RUN3_L0Be L3_L0Be NX3_L0Be
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
Qed.

Theorem efree_spine_L0Be : ltac2:(tb__ "0|1|
SeOF_;SaS2S0S0S4SbQ40A1A1S11OF_;S3R5A1S1eR5R4A2S1cU0M0S1R9R8R7R5S13S18R3A9S1cG0S1RaR9R8R6S14S19R4A9SdRbRaR9R7S15R5A6SdRcRbRaR8S16R6A6SdRdRcRbR9S1aR7A6S0SfVsegs;S7Vsegs;VJFi;S6ReRdRbA4S17R1RaA5R9A3FrhoP;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR HD1 HD2 HBIG HQ3 HXF rhoP.
  assert (HUS : stopJ_stable W st) by (first [apply stopJ_stable_le | apply stopJ_stable_nil]).
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Eps_L0Be rhoX tpX) Q)
            /\ (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Ebg_L0Be rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (ef0_s4 0%nat st false Eps_L0Be C3_L0Be Ems_L0Be C4_L0Be TM0_L0Be run4_L0Be RM_L0Be D3_L0Be W3_L0Be EQ3_L0Be NX3b_L0Be RUN4_L0Be L4_L0Be D4_L0Be W4_L0Be EQ4_L0Be
             HeM_L0Be HchkM_L0Be HTM_L0Be FBM_L0Be A' Kc rho rho1' tpX Q HUS HKc HR').
    intros rhoM tpM. rewrite ETM_L0Be.
    apply (ef0_s5 0%nat st q_L0Be false TM_L0Be Eq_L0Be EQ_L0Be TQ0_L0Be run5_L0Be RQ_L0Be NX5_L0Be RUN5_L0Be L5_L0Be AXQ_L0Be HeQ_L0Be HchkQ_L0Be HTQ_L0Be FBQ_L0Be
             A' Kc rho1' tpM Q HUS HKc).
    intros rhoQ. rewrite ETQ_L0Be.
    apply (ef0_s6 0%nat st false TQ_L0Be Edr_L0Be Xf_L0Be run6_L0Be NX6_L0Be RUN6_L0Be L6_L0Be A' Kc rho1' tpM Q HUS HKc).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (ef0_s1c 0%nat st true P0_L0Be exits1_L0Be (eq_refl : (GW <=? ss_next (ax_S P0_L0Be))%positive = true) ECert1_L0Be A Kc rho1 tp Q HUS HKc).
  intros E rhoE HinE. unfold exits1_L0Be in HinE. destruct HinE as [<-|[<-|[]]].
  - apply (ef0_s2 0%nat st true S1c_L0Be_1 C2_L0Be_1 EfD_L0Be_1 ED_L0Be_1 run2_L0Be_1 D2_L0Be_1 W2_L0Be_1 NX2_L0Be_1 EQ2_L0Be_1 RUN2_L0Be_1 L2_L0Be_1 AXD_L0Be_1
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 0%nat st false TD_L0Be_1 TDr_L0Be_1 CD_L0Be Eps_L0Be Ebg_L0Be run3_L0Be AXDr_L0Be_1 ENTD_L0Be_1 RUN3_L0Be L3_L0Be NX3_L0Be
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 0%nat st true S1c_L0Be_2 C2_L0Be_2 EfD_L0Be_2 ED_L0Be_2 run2_L0Be_2 D2_L0Be_2 W2_L0Be_2 NX2_L0Be_2 EQ2_L0Be_2 RUN2_L0Be_2 L2_L0Be_2 AXD_L0Be_2
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 0%nat st false TD_L0Be_2 TDr_L0Be_2 CD_L0Be Eps_L0Be Ebg_L0Be run3_L0Be AXDr_L0Be_2 ENTD_L0Be_2 RUN3_L0Be L3_L0Be NX3_L0Be
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
Qed.
End IL0Be.
End F0A_iL0Be.

(* [comment removed for export] *)
Module F0A_iL0Bf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "KcA"; "Kc_ok"; "@Corelib.Init.Datatypes"; "list"; "false"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m9.F0A_iL0Bf.IL0Bf"; "contF"; "econtF"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.F0A_cL0Bf"; "ED_L0Bf_1"; "ED_L0Bf_2"; "Ebg_L0Bf"; "Edr_L0Bf"; "P0_L0Bf"; "TD_L0Bf_1"; "TD_L0Bf_2"; "Xf_L0Bf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "HDF"; "HDFE"; "depot_onlyKf"; "rigF"; "JF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5"; "hd_link"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymEntail SymFrame SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CompleteA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ix.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ie.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.F0A_skelc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.F0A_cL0Bf.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section IL0Bf.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let W : list ulink := Wcan 0.
Let st : ustop := UStopLe.
Let JFi (b : bool) (A : AA) (Kc : KcA) (rho1 : valuation) : jpredA := ltac2:(tb__ "0|0|
S1fU0S1Vb;VA;VKc;Vrho1;A6").

Definition contF (keep : Z -> Prop) (ok : world -> Prop) (A : AA) (Kc : KcA) (rho1 : valuation) (E : axst) (Q : assn) : Prop := ltac2:(tb__ "0|0|
SaS0S0S4SbQ40A1A1S1dVA;R4A2S20Vkeep;Vrho1;R4A3S10Vsegs;Vok;S7Vsegs;VJFi;S5R6VKc;R5A4VE;R4R3A5VQ;A4F_;F_;FtpE;FrhoE;Frho1';FA';").
Definition econtF (keep : Z -> Prop) (A : AA) (Kc : KcA) (rho1 : valuation) (E : axst) (Q : world -> Prop) : Prop := ltac2:(tb__ "0|0|
SaS0S0S4SbQ40A1A1S1dVA;R4A2S20Vkeep;Vrho1;R4A3SfVsegs;S7Vsegs;VJFi;S5R6VKc;R5A4VE;R4R3A5VQ;A3F_;F_;FtpE;FrhoE;Frho1';FA';").

Theorem free_spine_L0Bf : ltac2:(tb__ "0|1|
SeOF_;S11OF_;SaS2S0S0S4SbQ40A1A1S12S3R5A1S9Vsegs;R8S8R6A1A3S1eR6R5A2S1bU0M0S1RbRaR9R8R6S13S18R4AaS1bG0S1RcRbRaR9R7S14S19R5AaScRdRcRbRaR8S15R6A7ScReRdRcRbR9S16R7A7ScRfReRdRcRaS1aR8A7S0S10Vsegs;R10S7Vsegs;VJFi;S6RfReRcA4S17R1RbA5RaA4FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR HD1 HD2 HBIG HQ3 HXF rhoP.
  assert (HUS : stopJ_stable W st) by (first [apply stopJ_stable_le | apply stopJ_stable_nil]).
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Eps_L0Bf rhoX tpX) Q)
            /\ (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Ebg_L0Bf rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (f0_s4 0%nat st false Eps_L0Bf C3_L0Bf Ems_L0Bf C4_L0Bf TM0_L0Bf run4_L0Bf RM_L0Bf D3_L0Bf W3_L0Bf EQ3_L0Bf NX3b_L0Bf RUN4_L0Bf L4_L0Bf D4_L0Bf W4_L0Bf EQ4_L0Bf
             HeM_L0Bf HchkM_L0Bf HTM_L0Bf FBM_L0Bf ok A' Kc rho rho1' tpX Q HUS HKc Hok HR').
    intros rhoM tpM. rewrite ETM_L0Bf.
    apply (f0_s5 0%nat st q_L0Bf false TM_L0Bf Eq_L0Bf EQ_L0Bf TQ0_L0Bf run5_L0Bf RQ_L0Bf NX5_L0Bf RUN5_L0Bf L5_L0Bf AXQ_L0Bf HeQ_L0Bf HchkQ_L0Bf HTQ_L0Bf FBQ_L0Bf
             ok A' Kc rho1' tpM Q HUS HKc Hok).
    intros rhoQ. rewrite ETQ_L0Bf.
    apply (f0_s6 0%nat st false TQ_L0Bf Edr_L0Bf Xf_L0Bf run6_L0Bf NX6_L0Bf RUN6_L0Bf L6_L0Bf ok A' Kc rho1' tpM Q HUS HKc Hok).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (f0_s1c 0%nat st true P0_L0Bf exits1_L0Bf Cert1_L0Bf ok A Kc rho1 tp Q HUS HKc Hok).
  intros E rhoE HinE. unfold exits1_L0Bf in HinE. destruct HinE as [<-|[<-|[]]].
  - apply (f0_s2 0%nat st true S1c_L0Bf_1 C2_L0Bf_1 EfD_L0Bf_1 ED_L0Bf_1 run2_L0Bf_1 D2_L0Bf_1 W2_L0Bf_1 NX2_L0Bf_1 EQ2_L0Bf_1 RUN2_L0Bf_1 L2_L0Bf_1 AXD_L0Bf_1
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 0%nat st false TD_L0Bf_1 TDr_L0Bf_1 CD_L0Bf Eps_L0Bf Ebg_L0Bf run3_L0Bf AXDr_L0Bf_1 ENTD_L0Bf_1 RUN3_L0Bf L3_L0Bf NX3_L0Bf
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 0%nat st true S1c_L0Bf_2 C2_L0Bf_2 EfD_L0Bf_2 ED_L0Bf_2 run2_L0Bf_2 D2_L0Bf_2 W2_L0Bf_2 NX2_L0Bf_2 EQ2_L0Bf_2 RUN2_L0Bf_2 L2_L0Bf_2 AXD_L0Bf_2
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 0%nat st false TD_L0Bf_2 TDr_L0Bf_2 CD_L0Bf Eps_L0Bf Ebg_L0Bf run3_L0Bf AXDr_L0Bf_2 ENTD_L0Bf_2 RUN3_L0Bf L3_L0Bf NX3_L0Bf
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
Qed.

Theorem efree_spine_L0Bf : ltac2:(tb__ "0|1|
SeOF_;SaS2S0S0S4SbQ40A1A1S11OF_;S3R5A1S1eR5R4A2S1cU0M0S1R9R8R7R5S13S18R3A9S1cG0S1RaR9R8R6S14S19R4A9SdRbRaR9R7S15R5A6SdRcRbRaR8S16R6A6SdRdRcRbR9S1aR7A6S0SfVsegs;S7Vsegs;VJFi;S6ReRdRbA4S17R1RaA5R9A3FrhoP;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR HD1 HD2 HBIG HQ3 HXF rhoP.
  assert (HUS : stopJ_stable W st) by (first [apply stopJ_stable_le | apply stopJ_stable_nil]).
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Eps_L0Bf rhoX tpX) Q)
            /\ (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Ebg_L0Bf rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (ef0_s4 0%nat st false Eps_L0Bf C3_L0Bf Ems_L0Bf C4_L0Bf TM0_L0Bf run4_L0Bf RM_L0Bf D3_L0Bf W3_L0Bf EQ3_L0Bf NX3b_L0Bf RUN4_L0Bf L4_L0Bf D4_L0Bf W4_L0Bf EQ4_L0Bf
             HeM_L0Bf HchkM_L0Bf HTM_L0Bf FBM_L0Bf A' Kc rho rho1' tpX Q HUS HKc HR').
    intros rhoM tpM. rewrite ETM_L0Bf.
    apply (ef0_s5 0%nat st q_L0Bf false TM_L0Bf Eq_L0Bf EQ_L0Bf TQ0_L0Bf run5_L0Bf RQ_L0Bf NX5_L0Bf RUN5_L0Bf L5_L0Bf AXQ_L0Bf HeQ_L0Bf HchkQ_L0Bf HTQ_L0Bf FBQ_L0Bf
             A' Kc rho1' tpM Q HUS HKc).
    intros rhoQ. rewrite ETQ_L0Bf.
    apply (ef0_s6 0%nat st false TQ_L0Bf Edr_L0Bf Xf_L0Bf run6_L0Bf NX6_L0Bf RUN6_L0Bf L6_L0Bf A' Kc rho1' tpM Q HUS HKc).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (ef0_s1c 0%nat st true P0_L0Bf exits1_L0Bf (eq_refl : (GW <=? ss_next (ax_S P0_L0Bf))%positive = true) ECert1_L0Bf A Kc rho1 tp Q HUS HKc).
  intros E rhoE HinE. unfold exits1_L0Bf in HinE. destruct HinE as [<-|[<-|[]]].
  - apply (ef0_s2 0%nat st true S1c_L0Bf_1 C2_L0Bf_1 EfD_L0Bf_1 ED_L0Bf_1 run2_L0Bf_1 D2_L0Bf_1 W2_L0Bf_1 NX2_L0Bf_1 EQ2_L0Bf_1 RUN2_L0Bf_1 L2_L0Bf_1 AXD_L0Bf_1
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 0%nat st false TD_L0Bf_1 TDr_L0Bf_1 CD_L0Bf Eps_L0Bf Ebg_L0Bf run3_L0Bf AXDr_L0Bf_1 ENTD_L0Bf_1 RUN3_L0Bf L3_L0Bf NX3_L0Bf
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 0%nat st true S1c_L0Bf_2 C2_L0Bf_2 EfD_L0Bf_2 ED_L0Bf_2 run2_L0Bf_2 D2_L0Bf_2 W2_L0Bf_2 NX2_L0Bf_2 EQ2_L0Bf_2 RUN2_L0Bf_2 L2_L0Bf_2 AXD_L0Bf_2
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 0%nat st false TD_L0Bf_2 TDr_L0Bf_2 CD_L0Bf Eps_L0Bf Ebg_L0Bf run3_L0Bf AXDr_L0Bf_2 ENTD_L0Bf_2 RUN3_L0Bf L3_L0Bf NX3_L0Bf
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
Qed.
End IL0Bf.
End F0A_iL0Bf.

(* [comment removed for export] *)
Module F0A_iL1A.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "KcA"; "Kc_ok"; "@Corelib.Init.Datatypes"; "list"; "false"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m9.F0A_iL1A.IL1A"; "contF"; "econtF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "HDF"; "HDFE"; "depot_onlyKf"; "rigF"; "JF"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.F0A_cL1A"; "ED_L1A_1"; "ED_L1A_2"; "ED_L1A_3"; "Ebg_L1A"; "Edr_L1A"; "P0_L1A"; "TD_L1A_1"; "TD_L1A_2"; "TD_L1A_3"; "Xf_L1A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5"; "hd_link"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymEntail SymFrame SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CompleteA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ix.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ie.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.F0A_skelc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.F0A_cL1A.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section IL1A.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let W : list ulink := Wcan 1.
Let st : ustop := UStopLe.
Let JFi (b : bool) (A : AA) (Kc : KcA) (rho1 : valuation) : jpredA := ltac2:(tb__ "0|0|
S12U1S1Vb;VA;VKc;Vrho1;A6").

Definition contF (keep : Z -> Prop) (ok : world -> Prop) (A : AA) (Kc : KcA) (rho1 : valuation) (E : axst) (Q : assn) : Prop := ltac2:(tb__ "0|0|
SaS0S0S4SbQ40A1A1S10VA;R4A2S22Vkeep;Vrho1;R4A3S15Vsegs;Vok;S7Vsegs;VJFi;S5R6VKc;R5A4VE;R4R3A5VQ;A4F_;F_;FtpE;FrhoE;Frho1';FA';").
Definition econtF (keep : Z -> Prop) (A : AA) (Kc : KcA) (rho1 : valuation) (E : axst) (Q : world -> Prop) : Prop := ltac2:(tb__ "0|0|
SaS0S0S4SbQ40A1A1S10VA;R4A2S22Vkeep;Vrho1;R4A3S14Vsegs;S7Vsegs;VJFi;S5R6VKc;R5A4VE;R4R3A5VQ;A3F_;F_;FtpE;FrhoE;Frho1';FA';").

Theorem free_spine_L1A : ltac2:(tb__ "0|1|
S13OF_;S16OF_;SaS2S0S0S4SbQ40A1A1S17S3R5A1S9Vsegs;R8S8R6A1A3S11R6R5A2SeU1M0S1RbRaR9R8R6S18S1eR4AaSeG0S1RcRbRaR9R7S19S1fR5AaSeG0S1RdRcRbRaR8S1aS20R6AaScReRdRcRbR9S1bR7A7ScRfReRdRcRaS1cR8A7ScR10RfReRdRbS21R9A7S0S15Vsegs;R11S7Vsegs;VJFi;S6R10RfRdA4S1dR1RcA5RbA4FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR HD1 HD2 HD3 HBIG HQ3 HXF rhoP.
  assert (HUS : stopJ_stable W st) by (first [apply stopJ_stable_le | apply stopJ_stable_nil]).
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Eps_L1A rhoX tpX) Q)
            /\ (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Ebg_L1A rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (f0_s4 1%nat st false Eps_L1A C3_L1A Ems_L1A C4_L1A TM0_L1A run4_L1A RM_L1A D3_L1A W3_L1A EQ3_L1A NX3b_L1A RUN4_L1A L4_L1A D4_L1A W4_L1A EQ4_L1A
             HeM_L1A HchkM_L1A HTM_L1A FBM_L1A ok A' Kc rho rho1' tpX Q HUS HKc Hok HR').
    intros rhoM tpM. rewrite ETM_L1A.
    apply (f0_s5 1%nat st q_L1A false TM_L1A Eq_L1A EQ_L1A TQ0_L1A run5_L1A RQ_L1A NX5_L1A RUN5_L1A L5_L1A AXQ_L1A HeQ_L1A HchkQ_L1A HTQ_L1A FBQ_L1A
             ok A' Kc rho1' tpM Q HUS HKc Hok).
    intros rhoQ. rewrite ETQ_L1A.
    apply (f0_s6 1%nat st false TQ_L1A Edr_L1A Xf_L1A run6_L1A NX6_L1A RUN6_L1A L6_L1A ok A' Kc rho1' tpM Q HUS HKc Hok).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (f0_s1c 1%nat st true P0_L1A exits1_L1A Cert1_L1A ok A Kc rho1 tp Q HUS HKc Hok).
  intros E rhoE HinE. unfold exits1_L1A in HinE. destruct HinE as [<-|[<-|[<-|[]]]].
  - apply (f0_s2 1%nat st true S1c_L1A_1 C2_L1A_1 EfD_L1A_1 ED_L1A_1 run2_L1A_1 D2_L1A_1 W2_L1A_1 NX2_L1A_1 EQ2_L1A_1 RUN2_L1A_1 L2_L1A_1 AXD_L1A_1
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 1%nat st false TD_L1A_1 TDr_L1A_1 CD_L1A Eps_L1A Ebg_L1A run3_L1A AXDr_L1A_1 ENTD_L1A_1 RUN3_L1A L3_L1A NX3_L1A
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 1%nat st true S1c_L1A_2 C2_L1A_2 EfD_L1A_2 ED_L1A_2 run2_L1A_2 D2_L1A_2 W2_L1A_2 NX2_L1A_2 EQ2_L1A_2 RUN2_L1A_2 L2_L1A_2 AXD_L1A_2
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 1%nat st false TD_L1A_2 TDr_L1A_2 CD_L1A Eps_L1A Ebg_L1A run3_L1A AXDr_L1A_2 ENTD_L1A_2 RUN3_L1A L3_L1A NX3_L1A
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 1%nat st true S1c_L1A_3 C2_L1A_3 EfD_L1A_3 ED_L1A_3 run2_L1A_3 D2_L1A_3 W2_L1A_3 NX2_L1A_3 EQ2_L1A_3 RUN2_L1A_3 L2_L1A_3 AXD_L1A_3
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD3. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 1%nat st false TD_L1A_3 TDr_L1A_3 CD_L1A Eps_L1A Ebg_L1A run3_L1A AXDr_L1A_3 ENTD_L1A_3 RUN3_L1A L3_L1A NX3_L1A
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
Qed.

Theorem efree_spine_L1A : ltac2:(tb__ "0|1|
S13OF_;SaS2S0S0S4SbQ40A1A1S16OF_;S3R5A1S11R5R4A2SfU1M0S1R9R8R7R5S18S1eR3A9SfG0S1RaR9R8R6S19S1fR4A9SfG0S1RbRaR9R7S1aS20R5A9SdRcRbRaR8S1bR6A6SdRdRcRbR9S1cR7A6SdReRdRcRaS21R8A6S0S14Vsegs;S7Vsegs;VJFi;S6RfReRcA4S1dR1RbA5RaA3FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR HD1 HD2 HD3 HBIG HQ3 HXF rhoP.
  assert (HUS : stopJ_stable W st) by (first [apply stopJ_stable_le | apply stopJ_stable_nil]).
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Eps_L1A rhoX tpX) Q)
            /\ (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Ebg_L1A rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (ef0_s4 1%nat st false Eps_L1A C3_L1A Ems_L1A C4_L1A TM0_L1A run4_L1A RM_L1A D3_L1A W3_L1A EQ3_L1A NX3b_L1A RUN4_L1A L4_L1A D4_L1A W4_L1A EQ4_L1A
             HeM_L1A HchkM_L1A HTM_L1A FBM_L1A A' Kc rho rho1' tpX Q HUS HKc HR').
    intros rhoM tpM. rewrite ETM_L1A.
    apply (ef0_s5 1%nat st q_L1A false TM_L1A Eq_L1A EQ_L1A TQ0_L1A run5_L1A RQ_L1A NX5_L1A RUN5_L1A L5_L1A AXQ_L1A HeQ_L1A HchkQ_L1A HTQ_L1A FBQ_L1A
             A' Kc rho1' tpM Q HUS HKc).
    intros rhoQ. rewrite ETQ_L1A.
    apply (ef0_s6 1%nat st false TQ_L1A Edr_L1A Xf_L1A run6_L1A NX6_L1A RUN6_L1A L6_L1A A' Kc rho1' tpM Q HUS HKc).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (ef0_s1c 1%nat st true P0_L1A exits1_L1A (eq_refl : (GW <=? ss_next (ax_S P0_L1A))%positive = true) ECert1_L1A A Kc rho1 tp Q HUS HKc).
  intros E rhoE HinE. unfold exits1_L1A in HinE. destruct HinE as [<-|[<-|[<-|[]]]].
  - apply (ef0_s2 1%nat st true S1c_L1A_1 C2_L1A_1 EfD_L1A_1 ED_L1A_1 run2_L1A_1 D2_L1A_1 W2_L1A_1 NX2_L1A_1 EQ2_L1A_1 RUN2_L1A_1 L2_L1A_1 AXD_L1A_1
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 1%nat st false TD_L1A_1 TDr_L1A_1 CD_L1A Eps_L1A Ebg_L1A run3_L1A AXDr_L1A_1 ENTD_L1A_1 RUN3_L1A L3_L1A NX3_L1A
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 1%nat st true S1c_L1A_2 C2_L1A_2 EfD_L1A_2 ED_L1A_2 run2_L1A_2 D2_L1A_2 W2_L1A_2 NX2_L1A_2 EQ2_L1A_2 RUN2_L1A_2 L2_L1A_2 AXD_L1A_2
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 1%nat st false TD_L1A_2 TDr_L1A_2 CD_L1A Eps_L1A Ebg_L1A run3_L1A AXDr_L1A_2 ENTD_L1A_2 RUN3_L1A L3_L1A NX3_L1A
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 1%nat st true S1c_L1A_3 C2_L1A_3 EfD_L1A_3 ED_L1A_3 run2_L1A_3 D2_L1A_3 W2_L1A_3 NX2_L1A_3 EQ2_L1A_3 RUN2_L1A_3 L2_L1A_3 AXD_L1A_3
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD3. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 1%nat st false TD_L1A_3 TDr_L1A_3 CD_L1A Eps_L1A Ebg_L1A run3_L1A AXDr_L1A_3 ENTD_L1A_3 RUN3_L1A L3_L1A NX3_L1A
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
Qed.
End IL1A.
End F0A_iL1A.

(* [comment removed for export] *)
Module F0A_iL1Be.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "KcA"; "Kc_ok"; "@Corelib.Init.Datatypes"; "list"; "false"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m9.F0A_iL1Be.IL1Be"; "contF"; "econtF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "HDF"; "HDFE"; "depot_onlyKf"; "rigF"; "JF"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.F0A_cL1Be"; "ED_L1Be_1"; "ED_L1Be_2"; "ED_L1Be_3"; "Ebg_L1Be"; "Edr_L1Be"; "P0_L1Be"; "TD_L1Be_1"; "TD_L1Be_2"; "TD_L1Be_3"; "Xf_L1Be"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5"; "hd_link"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymEntail SymFrame SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CompleteA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ix.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ie.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.F0A_skelc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.F0A_cL1Be.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section IL1Be.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let W : list ulink := Wcan 1.
Let st : ustop := UStopLe.
Let JFi (b : bool) (A : AA) (Kc : KcA) (rho1 : valuation) : jpredA := ltac2:(tb__ "0|0|
S12U1S1Vb;VA;VKc;Vrho1;A6").

Definition contF (keep : Z -> Prop) (ok : world -> Prop) (A : AA) (Kc : KcA) (rho1 : valuation) (E : axst) (Q : assn) : Prop := ltac2:(tb__ "0|0|
SaS0S0S4SbQ40A1A1S10VA;R4A2S22Vkeep;Vrho1;R4A3S15Vsegs;Vok;S7Vsegs;VJFi;S5R6VKc;R5A4VE;R4R3A5VQ;A4F_;F_;FtpE;FrhoE;Frho1';FA';").
Definition econtF (keep : Z -> Prop) (A : AA) (Kc : KcA) (rho1 : valuation) (E : axst) (Q : world -> Prop) : Prop := ltac2:(tb__ "0|0|
SaS0S0S4SbQ40A1A1S10VA;R4A2S22Vkeep;Vrho1;R4A3S14Vsegs;S7Vsegs;VJFi;S5R6VKc;R5A4VE;R4R3A5VQ;A3F_;F_;FtpE;FrhoE;Frho1';FA';").

Theorem free_spine_L1Be : ltac2:(tb__ "0|1|
S13OF_;S16OF_;SaS2S0S0S4SbQ40A1A1S17S3R5A1S9Vsegs;R8S8R6A1A3S11R6R5A2SeU1M0S1RbRaR9R8R6S18S1eR4AaSeG0S1RcRbRaR9R7S19S1fR5AaSeG0S1RdRcRbRaR8S1aS20R6AaScReRdRcRbR9S1bR7A7ScRfReRdRcRaS1cR8A7ScR10RfReRdRbS21R9A7S0S15Vsegs;R11S7Vsegs;VJFi;S6R10RfRdA4S1dR1RcA5RbA4FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR HD1 HD2 HD3 HBIG HQ3 HXF rhoP.
  assert (HUS : stopJ_stable W st) by (first [apply stopJ_stable_le | apply stopJ_stable_nil]).
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Eps_L1Be rhoX tpX) Q)
            /\ (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Ebg_L1Be rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (f0_s4 1%nat st false Eps_L1Be C3_L1Be Ems_L1Be C4_L1Be TM0_L1Be run4_L1Be RM_L1Be D3_L1Be W3_L1Be EQ3_L1Be NX3b_L1Be RUN4_L1Be L4_L1Be D4_L1Be W4_L1Be EQ4_L1Be
             HeM_L1Be HchkM_L1Be HTM_L1Be FBM_L1Be ok A' Kc rho rho1' tpX Q HUS HKc Hok HR').
    intros rhoM tpM. rewrite ETM_L1Be.
    apply (f0_s5 1%nat st q_L1Be false TM_L1Be Eq_L1Be EQ_L1Be TQ0_L1Be run5_L1Be RQ_L1Be NX5_L1Be RUN5_L1Be L5_L1Be AXQ_L1Be HeQ_L1Be HchkQ_L1Be HTQ_L1Be FBQ_L1Be
             ok A' Kc rho1' tpM Q HUS HKc Hok).
    intros rhoQ. rewrite ETQ_L1Be.
    apply (f0_s6 1%nat st false TQ_L1Be Edr_L1Be Xf_L1Be run6_L1Be NX6_L1Be RUN6_L1Be L6_L1Be ok A' Kc rho1' tpM Q HUS HKc Hok).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (f0_s1c 1%nat st true P0_L1Be exits1_L1Be Cert1_L1Be ok A Kc rho1 tp Q HUS HKc Hok).
  intros E rhoE HinE. unfold exits1_L1Be in HinE. destruct HinE as [<-|[<-|[<-|[]]]].
  - apply (f0_s2 1%nat st true S1c_L1Be_1 C2_L1Be_1 EfD_L1Be_1 ED_L1Be_1 run2_L1Be_1 D2_L1Be_1 W2_L1Be_1 NX2_L1Be_1 EQ2_L1Be_1 RUN2_L1Be_1 L2_L1Be_1 AXD_L1Be_1
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 1%nat st false TD_L1Be_1 TDr_L1Be_1 CD_L1Be Eps_L1Be Ebg_L1Be run3_L1Be AXDr_L1Be_1 ENTD_L1Be_1 RUN3_L1Be L3_L1Be NX3_L1Be
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 1%nat st true S1c_L1Be_2 C2_L1Be_2 EfD_L1Be_2 ED_L1Be_2 run2_L1Be_2 D2_L1Be_2 W2_L1Be_2 NX2_L1Be_2 EQ2_L1Be_2 RUN2_L1Be_2 L2_L1Be_2 AXD_L1Be_2
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 1%nat st false TD_L1Be_2 TDr_L1Be_2 CD_L1Be Eps_L1Be Ebg_L1Be run3_L1Be AXDr_L1Be_2 ENTD_L1Be_2 RUN3_L1Be L3_L1Be NX3_L1Be
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 1%nat st true S1c_L1Be_3 C2_L1Be_3 EfD_L1Be_3 ED_L1Be_3 run2_L1Be_3 D2_L1Be_3 W2_L1Be_3 NX2_L1Be_3 EQ2_L1Be_3 RUN2_L1Be_3 L2_L1Be_3 AXD_L1Be_3
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD3. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 1%nat st false TD_L1Be_3 TDr_L1Be_3 CD_L1Be Eps_L1Be Ebg_L1Be run3_L1Be AXDr_L1Be_3 ENTD_L1Be_3 RUN3_L1Be L3_L1Be NX3_L1Be
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
Qed.

Theorem efree_spine_L1Be : ltac2:(tb__ "0|1|
S13OF_;SaS2S0S0S4SbQ40A1A1S16OF_;S3R5A1S11R5R4A2SfU1M0S1R9R8R7R5S18S1eR3A9SfG0S1RaR9R8R6S19S1fR4A9SfG0S1RbRaR9R7S1aS20R5A9SdRcRbRaR8S1bR6A6SdRdRcRbR9S1cR7A6SdReRdRcRaS21R8A6S0S14Vsegs;S7Vsegs;VJFi;S6RfReRcA4S1dR1RbA5RaA3FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR HD1 HD2 HD3 HBIG HQ3 HXF rhoP.
  assert (HUS : stopJ_stable W st) by (first [apply stopJ_stable_le | apply stopJ_stable_nil]).
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Eps_L1Be rhoX tpX) Q)
            /\ (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Ebg_L1Be rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (ef0_s4 1%nat st false Eps_L1Be C3_L1Be Ems_L1Be C4_L1Be TM0_L1Be run4_L1Be RM_L1Be D3_L1Be W3_L1Be EQ3_L1Be NX3b_L1Be RUN4_L1Be L4_L1Be D4_L1Be W4_L1Be EQ4_L1Be
             HeM_L1Be HchkM_L1Be HTM_L1Be FBM_L1Be A' Kc rho rho1' tpX Q HUS HKc HR').
    intros rhoM tpM. rewrite ETM_L1Be.
    apply (ef0_s5 1%nat st q_L1Be false TM_L1Be Eq_L1Be EQ_L1Be TQ0_L1Be run5_L1Be RQ_L1Be NX5_L1Be RUN5_L1Be L5_L1Be AXQ_L1Be HeQ_L1Be HchkQ_L1Be HTQ_L1Be FBQ_L1Be
             A' Kc rho1' tpM Q HUS HKc).
    intros rhoQ. rewrite ETQ_L1Be.
    apply (ef0_s6 1%nat st false TQ_L1Be Edr_L1Be Xf_L1Be run6_L1Be NX6_L1Be RUN6_L1Be L6_L1Be A' Kc rho1' tpM Q HUS HKc).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (ef0_s1c 1%nat st true P0_L1Be exits1_L1Be (eq_refl : (GW <=? ss_next (ax_S P0_L1Be))%positive = true) ECert1_L1Be A Kc rho1 tp Q HUS HKc).
  intros E rhoE HinE. unfold exits1_L1Be in HinE. destruct HinE as [<-|[<-|[<-|[]]]].
  - apply (ef0_s2 1%nat st true S1c_L1Be_1 C2_L1Be_1 EfD_L1Be_1 ED_L1Be_1 run2_L1Be_1 D2_L1Be_1 W2_L1Be_1 NX2_L1Be_1 EQ2_L1Be_1 RUN2_L1Be_1 L2_L1Be_1 AXD_L1Be_1
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 1%nat st false TD_L1Be_1 TDr_L1Be_1 CD_L1Be Eps_L1Be Ebg_L1Be run3_L1Be AXDr_L1Be_1 ENTD_L1Be_1 RUN3_L1Be L3_L1Be NX3_L1Be
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 1%nat st true S1c_L1Be_2 C2_L1Be_2 EfD_L1Be_2 ED_L1Be_2 run2_L1Be_2 D2_L1Be_2 W2_L1Be_2 NX2_L1Be_2 EQ2_L1Be_2 RUN2_L1Be_2 L2_L1Be_2 AXD_L1Be_2
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 1%nat st false TD_L1Be_2 TDr_L1Be_2 CD_L1Be Eps_L1Be Ebg_L1Be run3_L1Be AXDr_L1Be_2 ENTD_L1Be_2 RUN3_L1Be L3_L1Be NX3_L1Be
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 1%nat st true S1c_L1Be_3 C2_L1Be_3 EfD_L1Be_3 ED_L1Be_3 run2_L1Be_3 D2_L1Be_3 W2_L1Be_3 NX2_L1Be_3 EQ2_L1Be_3 RUN2_L1Be_3 L2_L1Be_3 AXD_L1Be_3
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD3. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 1%nat st false TD_L1Be_3 TDr_L1Be_3 CD_L1Be Eps_L1Be Ebg_L1Be run3_L1Be AXDr_L1Be_3 ENTD_L1Be_3 RUN3_L1Be L3_L1Be NX3_L1Be
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
Qed.
End IL1Be.
End F0A_iL1Be.

