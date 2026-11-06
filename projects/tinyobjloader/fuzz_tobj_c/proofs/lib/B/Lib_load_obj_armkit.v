(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "uval"; "@Stdlib.ZArith.BinInt.Z"; "le"; "mul"; "add"; "lt"; "pow"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loop"; "xLK"; "xLD"; "xLC"; "pI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rm"; "sv"; "rw"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "@Corelib.Init.Datatypes"; "prod"; "list"; "option"; "pair"; "@Stdlib.Lists.List"; "In"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs"; "kb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_lglue"; "V_B"; "V_L"; "tblB"; "tblL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve"; "B32"; "B_EW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAK"; "keptK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "alloc_lawsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV TobjArena ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TobjJVA InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAM2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR TobjJAS TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import ResidualA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.ObjZeroA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import ObjEmptyA PinA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Lib_rom_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_defs Lib_load_obj_pro Lib_load_obj_pro2 Lib_load_obj_loop Lib_load_obj_disp Lib_load_obj_lglue Lib_load_obj_bud.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr LOAddr LOLAddr.

Lemma tblL_kept : ltac2:(tb__ "0|5|
ScScS7S19S7R1S1eA3S10S13Q40M0A1SfR3R2A2SfR4R2A2A3F_;Fv;S6S11S1S0R4S9A2M1R1A2S4R1S3G1S2Z10S0R4S8A2M2A2A2A2A2S10S17S13Q8A1A1SdR4S14G0R2A2M3A2SdR5G3A2A3F_;Fz;S1S0R4SaA2G2A2S20R5A1M4G4F_;F_;F_;F_;Frho';Frho;").
Proof.
  intros rho rho' HV HM Hck [(T & H1 & H2 & H3 & H4) HD].
  assert (E466 : uval rho' xLD = uval rho xLD) by (apply (uval_rw rho rho' 466 xLD eq_refl); symmetry; apply HV; cbn; tauto).
  assert (E14 : uval rho' vLEN = uval rho vLEN) by (apply (uval_rw rho rho' 14 vLEN eq_refl); symmetry; apply HV; cbn; tauto).
  assert (E467 : uval rho' xLC = uval rho xLC) by (apply (uval_rw rho rho' 467 xLC eq_refl); symmetry; apply HV; cbn; tauto).
  assert (E468 : uval rho' xLK = uval rho xLK) by (apply (uval_rw rho rho' 468 xLK eq_refl); symmetry; apply HV; cbn; tauto).
  assert (E460 : uval rho' pI = uval rho pI) by (apply (uval_rw rho rho' 460 pI eq_refl); symmetry; apply HV; cbn; tauto).
  assert (E490 : uval rho' pNX = uval rho pNX) by (apply (uval_rw rho rho' 490 pNX eq_refl); symmetry; apply HV; cbn; tauto).
  split.
  - exists T. rewrite E466, E14, E467, E460, E490. split; [|split; [exact H2 | split; [exact H3 | exact H4]]].
    eapply decodes_ext; [|exact H1]. intros z Hz. apply HM. lia.
  - intros z Hz. rewrite E466, E468 in Hz. rewrite (HM z Hz). exact (HD z Hz).
Qed.
Lemma tblB_kept : ltac2:(tb__ "0|4|
ScScS7S19S7R1S1dA3S10S13Q40M0A1SfR3R2A2SfR4R2A2A3F_;Fv;S6S11S1S0R4S9A2M1R1A2S4R1S3G1S2Z10S0R4S8A2A2A2A2A2S10S17S13Q8A1A1SdR4S14G0R2A2M2A2SdR5G2A2A3F_;Fz;S4S0R4SbA2S0R4SaA2A2S1S0R5SaA2S0R5S8A2A2S1fR6A1M3G3F_;F_;F_;F_;F_;Frho';Frho;").
Proof.
  intros rho rho' HV HM Hi Hck (HT & R1 & R2).
  assert (E466 : uval rho' xLD = uval rho xLD) by (apply (uval_rw rho rho' 466 xLD eq_refl); symmetry; apply HV; cbn; tauto).
  assert (E460 : uval rho' pI = uval rho pI) by (apply (uval_rw rho rho' 460 pI eq_refl); symmetry; apply HV; cbn; tauto).
  assert (E480 : uval rho' pPOS = uval rho pPOS) by (apply (uval_rw rho rho' 480 pPOS eq_refl); symmetry; apply HV; cbn; tauto).
  assert (E481 : uval rho' pLNL = uval rho pLNL) by (apply (uval_rw rho rho' 481 pLNL eq_refl); symmetry; apply HV; cbn; tauto).
  pose proof (uval_range rho pI) as RI.
  split; [|split].
  - apply (tblL_kept rho rho'); [intros v Hv; apply HV; cbn in Hv |- *; tauto | exact HM | exact Hck | exact HT].
  - rewrite E466, E460, E480. rewrite (rd64_ext (rm rho) (rm rho')); [exact R1|]. intros z Hz. apply HM. nia.
  - rewrite E466, E460, E481. rewrite (rd64_ext (rm rho) (rm rho')); [exact R2|]. intros z Hz. apply HM. nia.
Qed.

Lemma room4_arith : ltac2:(tb__ "0|1|
S6S6S6S6S1Z0M0R4A2S1R5S2Z3R4A2A2S1R5S3R4Z1A2A2S1R5S5Z2Z1aA2A2S11S1G0R5A2S1R5Z8A2A2S1S2Z4S3R9R6A2A2S22A2F_;F_;F_;F_;F_;Fd;Flen;Fnx;Fc;").
Proof. intros. unfold B_EW, Lib_vec_reserve.B_EW. lia. Qed.

Section Sum.
Variable AInv : ltac2:(tb__ "0|0|
S25ScS16S13Q40A1A1S1aOF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
S24S1bVAInv;VCST;A3").
Variable Kc : KcA.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S16S15S15S6S6A2S6A2A1").
Variable BX : bxt.
Variable rho0 : valuation.

Lemma keptK_lines : ltac2:(tb__ "0|4|
ScS16S15SeSeA2M0A1S16S15S15SeS6A2SeA2A1ScS23VCST;Vrho0;VFB;VFF;R4R3R2R1A8S19G0S18SeSeS9S1cZ10M1S8A2A4R4A3S12S10S6S0R6S9A2Z0A3A1S1S3S0R7S9A2S2G1S0R7S8A2A2A2S5Z2Z2fA2A2S1S2G1S0R8S8A2A2S21A2S6S11S1S0RaS9A2M2R1A2S4R1S3G2S2G1S0RaS8A2A2A2A2A2S10S17S13Q8A1A1SdR8S14Q40R2A2M3A2SdRbG3A2A3F_;Fz;F_;F_;F_;F_;F_;Frho';Ffr;Fkept;Frho;").
Proof using .
  intros rho kept fr rho' HK Hin Hnz Htop Hk z Hz.
  pose proof (uval_range rho xLD) as RD. pose proof (uval_range rho xLK) as RK.
  apply (HK z); [lia|].
  right; right; left. exists (uval rho xLD), (uval rho (kb 16 xLK)). split.
  - apply (proj2 (TobjJV.In_FBx FB rho kept _)). right. exists (xLD, kb 16 xLK). split; [exact Hin|]. split; [exact Hnz | reflexivity].
  - unfold kb. rewrite uval_mul_lit by (unfold B32, Lib_vec_reserve.B32 in Hk; lia). lia.
Qed.
End Sum.
