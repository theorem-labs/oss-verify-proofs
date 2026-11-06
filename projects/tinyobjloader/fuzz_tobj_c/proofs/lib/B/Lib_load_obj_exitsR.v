(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "positive"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sprop"; "holds"; "SPUle"; "rw"; "SLit"; "SVar"; "rm"; "ss_facts"; "SAlu"; "sprop_below"; "sprop_eqb"; "ss_next"; "swf"; "@Corelib.Init.Datatypes"; "cons"; "bool"; "nil"; "true"; "prod"; "list"; "pair"; "fst"; "option"; "snd"; "@Corelib.Init.Logic"; "eq"; "and"; "True"; "@Corelib.Lists.ListDef"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_exitsR"; "ldefR"; "rate2"; "K_after0R"; "V_ldR"; "fact_nv"; "PhisS"; "fact_nt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_lglue"; "ldef"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "axwf"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_defs"; "vLEN"; "NP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_exits"; "K_after0"; "X_after"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "uval"; "@Stdlib.Lists.List"; "In"; "forallb"; "existsb"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loop"; "pNX"; "xLD"; "xLK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "leaf_matchesA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF"; "phi_reads"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "mul"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CFGA GlueA SummaryA SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR TobjJAS TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.ObjZeroA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import ObjEmptyA PinA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Lib_rom_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_defs Lib_load_obj_pro Lib_load_obj_pro2 Lib_load_obj_loop Lib_load_obj_disp Lib_load_obj_lglue Lib_load_obj_hv0 Lib_load_obj_bud Lib_load_obj_exits.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr LOAddr LOLAddr HVAddr.

Definition vNV : sv := SVar 401.
Definition fact_nv : sprop := SPUle vNV pNX.
Definition fact_nt : sprop := SPUle (SVar 410) pNX.
Definition rate2 : list sprop := ltac2:(tb__ "0|0|
S10S3S22S10S3S24S12S3A1A3A3").
Definition K_after0R : axst := ax_add_facts rate2 K_after0.

Definition ldefR (rho : valuation) : Prop := ltac2:(tb__ "0|0|
S1bS25Vrho;A1S1dS3S4Vrho;A1S1fA3A2").
Definition V_ldR : list positive := ltac2:(tb__ "0|0|
S10S0P1d2S10S0P1d4S10S0P191S10S0P19aS10S0P1eaS12S0A1A3A3A3A3A3").
Definition PhisS : list (list positive * (valuation -> Prop)) := ltac2:(tb__ "0|4|
S10S14S15S0A1M0S2OFrho;M1A2S16G0G1S21S1eA4S10S14G0S2OF_;M2A2M3S16G0G2S12S0A1S2S1cL_;A4S12G3A1A3A3").

Lemma ldefR_ldef : ltac2:(tb__ "0|0|
S2S1eR1A1S25R2A1F_;Frho;"). Proof. intros rho [H _]. exact H. Qed.
Lemma ldefR_rate : ltac2:(tb__ "0|0|
S2S1eR1A1S1dS3S4R2A1S1fA3F_;Frho;"). Proof. intros rho [_ H]. exact H. Qed.
Lemma ldefR_nv : ltac2:(tb__ "0|0|
S2S1eR1A1S4R2S22A2F_;Frho;"). Proof. intros rho [_ H]. exact (Forall_inv H). Qed.
Lemma ldefR_intro : ltac2:(tb__ "0|0|
S2S25R1A1S1dS3S4R2A1S1fA3S1eR3A1F_;F_;Frho;"). Proof. intros rho H1 H2. split; assumption. Qed.

Lemma rate2_keep : ltac2:(tb__ "0|1|
S2S2S0S30S0R1S21A3S1aS29Q40A1S6R4R2A2S6R3R2A2A3F_;Fv;S1dS3S4R3A1S1fA3M0G0F_;F_;Frho';Frho;").
Proof.
  intros rho rho' HV H.
  assert (E1 : rw rho 401 = rw rho' 401) by (apply HV; cbn; tauto). assert (E3 : rw rho 410 = rw rho' 410) by (apply HV; cbn; tauto).
  assert (E5 : rw rho 490 = rw rho' 490) by (apply HV; cbn; tauto).
  unfold rate2, fact_nv, fact_nt, vNV, pNX in *.
  inversion H as [|? ? A1 H1]; subst. inversion H1 as [|? ? A3 _]; subst.
  rewrite h_ule in A1, A3. unfold uval in A1, A3. cbn [eval] in A1, A3.
  repeat constructor; rewrite h_ule; unfold uval; cbn [eval]; rewrite <- ?E1, <- ?E3, <- ?E5; assumption.
Qed.
Lemma ldefR_reads : phi_reads V_ldR ldefR.
Proof.
  intros rho rho' HV _ HM [HD HN]. split; [|exact (rate2_keep rho rho' HV HN)].
  intros z Hz. rewrite <- HM. apply HD.
  rewrite <- (uval_rw rho rho' 466 xLD eq_refl ltac:(apply HV; cbn; tauto)), <- (uval_rw rho rho' 468 xLK eq_refl ltac:(apply HV; cbn; tauto)). exact Hz.
Qed.
Lemma PhisS_reads : ltac2:(tb__ "0|3|
S1dS14S15S0A1M0S2OF_;M1A2M2G2S39S17G0G1R1A3S19G0G1R1A3A2Lp;S23A3").
Proof. constructor; [exact ldefR_reads | constructor; [intros rho rho' _ _ _ _; exact I | constructor]]. Qed.

Lemma ldefR_keep : ltac2:(tb__ "0|4|
S2S2S0S30S0R1S21A3S1aS29Q40M0A1S6R4R2A2S6R3R2A2A3F_;Fv;S1S1bS3bS2fR4S35A2M1R1A2S3cR1S3aG1S3dZ10S2fR4S36A2A2A2A2A2S1aS18S29Q8A1A1S9R4S2aG0R2A2M2A2S9R5G2A2A3F_;Fz;S1eR4A1M3G3F_;F_;F_;Frho';Frho;").
Proof.
  intros rho rho' HV HM [HD HN]. split; [|exact (rate2_keep rho rho' HV HN)].
  intros z Hz.
  rewrite (uval_rw rho rho' 466 xLD eq_refl ltac:(apply HV; cbn; tauto)), (uval_rw rho rho' 468 xLK eq_refl ltac:(apply HV; cbn; tauto)) in Hz.
  rewrite (HM z Hz). exact (HD z Hz).
Qed.

Lemma rate2_bounds : ltac2:(tb__ "0|1|
S2S1dS3S4R1A1S1fA3S4R2S5S34SbS33S2bS7Z1A1A3A2A2S4R3S5S2bS7Z4000000A1A2A2S1bS4R4S5S8P191A1S7ZffffffffA1M0A2A2S4R4S5S8P19aA1G0A2A2A2F_;F_;F_;Frho;").
Proof.
  intros rho H HN HL. unfold rate2, fact_nv, fact_nt, vNV in H.
  inversion H as [|? ? A1 H1]; subst. inversion H1 as [|? ? A3 _]; subst.
  rewrite h_ule in A1, A3, HN, HL. rewrite uval_lit in HL by lia.
  pose proof (uval_range rho pNX) as RN. pose proof (uval_range rho vLEN) as RL.
  assert (E1 : uval rho (SAlu ALU_ADD vLEN (SLit 1)) = uval rho vLEN + 1) by (rewrite uval_add_small; rewrite uval_lit by lia; lia).
  split; rewrite h_ule, uval_lit by lia; lia.
Qed.

Lemma exitsR_checks : ltac2:(tb__ "0|2|
S1bS1aS11S37S2cS2eS10S26S20S12S26A1A3A3S13A3S1bS1aS11S28S20A1S13A3S1bS1aS11SfS27S20A1M0A1S13A3S1bS1aS26S38S20SaS27S2dA1A1M1A2S2dA3S1bS1aS11S31S3ScSeG0A1A1G1A3S13A3S1aS11S31S3S3S32S3SdR1A1SaG0A1A3Lf;S1fA3S13A3A2A2A2A2A2").
Proof. repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
