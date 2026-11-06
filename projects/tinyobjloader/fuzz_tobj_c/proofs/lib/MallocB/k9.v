(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k6.
From Stdlib Require FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineCallocSec4I SpineCallocSec4IL SpineCallocSec4ILW1 SpineCallocSec4IW1.

(* [comment removed for export] *)
Module SpineMallocSec5JW2.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "sobj"; "obj_range"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "DG"; "aa_geom"; "ag_pab"; "@Corelib.Init.Datatypes"; "list"; "nil"; "pair"; "prod"; "fst"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3"; "JGs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jm.SpineMallocSec3IW2"; "nx0"; "@Corelib.Init.Logic"; "eq"; "and"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "ulink"; "KcA"; "Kc_ok"; "UStopLeOrPc"; "ustop"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "world"; "assn"; "etriple"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jn.DepotCallS"; "AXK"; "dlink"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger"; "sepZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dblocks"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "secmapsize"; "stopJ_stable"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.SecBump"; "bumpP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k6.SpineMallocSec5IW2"; "C5ac"; "C5bc"; "X5ac"; "X5bc"; "EXoa"; "EXob"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "kPtrArrayReserve"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocSec4IW2"; "T4ac"; "T4bc"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ii.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jl.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jm.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocSec4IW2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require js.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k6.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.CertMallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SegD_refl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.SecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.SecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jm.SpineMallocSec3IW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineMallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocSec4IW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertMallocSU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jq.SpineMallocSec5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jn.DepotCallS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.js.SpineMallocSec6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k6.SpineMallocSec5IW2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 2. Let st : ustop := UStopLe. Let tmax : Z := 4.
Let GS0 : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3.GS nx0.

Lemma EXZa_0 : ltac2:(tb__ "0|3|
S6S19S2S1eQ40A1M0S2SaG0A1S20S4S0S10S1S13U2Vst;S14S6S2eR1A1LX;R9R8R7R6A8S31R5R4R3A6S23S4R3S33A3S16S2aSeS0S0S5R7R4A2M1A3R3A2S2bR3SfS0S0G1A3A2A2S17S16S2aS36R4A2S2bR4S35A2A2S16S2aS9S8RcA1A1M2R4A2S2bR4S2cG2S37A2A2A2A2F_;F_;F_;Fz;Fo;Fw;Ftp;FrhoE;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a rhoE tp w o z Hw Ho Hz. pose proof (SPA_facts_hold segsA _ rhoE X5ac tp w Hw) as HF. destruct w as [tr [ms md]].
  pose proof (proj2 Hw) as HJ. cbn [w_tr w_cfg cfg_model fst snd] in HJ.
  pose proof (proj1 (Forall_forall _ _) HF _ FXBa_0) as HBR.
  destruct Ho as [<-|[<-|[<-|[]]]].
  - left. exact (ex2_band 2%nat st tmax nx0 Hnx_0 (fun X : AA => bumpP X) A Kc rho a rhoE tp tr md z HJ Hz).
  - left. exact (ex1_band 2%nat st tmax nx0 Hnx_0 (fun X : AA => bumpP X) A Kc rho a rhoE tp tr md z HJ Hz).
  - right. exact (exblk_pab 2%nat st tmax nx0 Hnx_0 (fun X : AA => bumpP X) A Kc rho a rhoE tp tr md z (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) HJ HBR Hz).
Qed.

Theorem depot_call_S_2ha : ltac2:(tb__ "0|6|
S20OF_;S6S19S2S1eQ40M0A1M1S21S15S1cVst;S1bA3S15SaS18A1VW;SbS18A1A3F_;S29VW;Vst;A2S1aR6A1S12S1R9S11R7A1A3S2dS1RaS11R8A1A3S7S2S2SaG1A1M2SdS0S0A2M3S23G3R1S27R5A1A3S26R2ScS0S0S1dG0RdA2S28S1dG0S3RePcA2A2A1A4A2F_;Fbn;S25R5RdR4A3S1fS1R11S10S1S13U2M4Vst;S14S24S6S2eR1A1LX;M5R6A2R10RfR5RdA8S2fR4R3A5RcA4F_;F_;Ftp';FrhoX;Frho';FG2;S2G2S1fS1ReS10S1S13G4Vst;S14G5RdRcRbRaA8S31R2R1A5R9A4Ftp;FrhoE;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Proof.
  exact (depot_call_S 2%nat st tmax nx0 Hnx_0 NXG_0 (fun X : AA => bumpP X) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl)
           Htmax_0 X5ac C5ac NXEa_0 FBEa_0 F192a_0 FDEPa_0 FUNWa_0 WX5ra_0 DX5ra_0 SPL1a_0 SPL2a_0 SPL3a_0 SPL4a_0
           s4a_i R4a_i T4a_i HERa_0 HT4a_0 XX4a_0 FBX4a_0 Hchk4a_0 NX4a_0 WG10a_0 WG15a_0 WG12a_0 EXoa FAM4a_0 EXZa_0 NEWOa_0 XPosta_0
           FBT4a_0 XT4a_0 RB1a_0 RB2a_0 nobja PERM_nda_0 PERM_lta_0 PERM_cova_0 PERM_lena_0 MRG1a_0 MRG2a_0 MRG3a_0 MRG4a_0 sda_i ENT5a_0 SID5a_0 R4cova_0).
Qed.

Theorem depot_call_SE_2ha : ltac2:(tb__ "0|6|
S6S19S2S1eQ40M0A1M1S20OF_;S15S1cVst;S1bA3S15SaS18A1VW;SbS18A1A3F_;S29VW;Vst;A2S1aR6A1S7S2S2SaG1A1M2SdS0S0A2M3S23G3R1S27R5A1A3S26R2ScS0S0S1dG0RbA2S28S1dG0S3RcPcA2A2A1A4A2F_;Fbn;S25R5RbR4A3S22S1S10S1S13U2M4Vst;S14S24S6S2eR1A1LX;M5R6A2ReRdR5RbA8S2fR4R3A5RaA3F_;F_;Ftp';FrhoX;Frho';FG2;S2G2S22S1S10S1S13G4Vst;S14G5RbRaR9R8A8S31R2R1A5R7A3Ftp;FrhoE;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;").
Proof.
  exact (depot_call_SE 2%nat st tmax nx0 Hnx_0 NXG_0 (fun X : AA => bumpP X) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl)
           Htmax_0 X5ac C5ac NXEa_0 FBEa_0 F192a_0 FDEPa_0 FUNWa_0 WX5ra_0 DX5ra_0 SPL1a_0 SPL2a_0 SPL3a_0 SPL4a_0
           s4a_i R4a_i T4a_i HERa_0 HT4a_0 XX4a_0 FBX4a_0 Hchk4a_0 NX4a_0 WG10a_0 WG15a_0 WG12a_0 EXoa FAM4a_0 EXZa_0 NEWOa_0 XPosta_0
           FBT4a_0 XT4a_0 RB1a_0 RB2a_0 nobja PERM_nda_0 PERM_lta_0 PERM_cova_0 PERM_lena_0 MRG1a_0 MRG2a_0 MRG3a_0 MRG4a_0 sda_i ENT5a_0 SID5a_0 R4cova_0).
Qed.

Theorem sec_g41_2ha : ltac2:(tb__ "0|6|
S20OF_;S6S19S2S1eQ40M0A1M1S21S15S1cVst;S1bA3S15SaS18A1VW;SbS18A1A3F_;S29VW;Vst;A2S1aR6A1S12S1R9S11R7A1A3S2dS1RaS11R8A1A3S7S2S2SaG1A1M2SdS0S0A2M3S23G3R1S27R5A1A3S26R2ScS0S0S1dG0RdA2S28S1dG0S3RePcA2A2A1A4A2F_;Fbn;S25R5RdR4A3S1fS1R11S10S1S13U2M4Vst;S14S24S6S2eR1A1LX;M5R6A2R10RfR5RdA8S2fR4R3A5RcA4F_;F_;Ftp';FrhoX;Frho';FG2;S2G2S1fS1ReS10S1S13G4Vst;S14G5RdRcRbRaA8S38R2R1A5R9A4FtX;FrX;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Proof.
  exact (sec_g41 2%nat st tmax nx0 Hnx_0 NXG_0 (fun X : AA => bumpP X) T4ac U4ac X5ac C5ac WU4a_0 DU4a_0 NXU4a_0 HU4a_0 Cert5a_0 depot_call_S_2ha).
Qed.

Lemma EXZb_0 : ltac2:(tb__ "0|3|
S6S19S2S1eQ40A1M0S2SaG0A1S20S4S0S10S1S13U2Vst;S14S6R1LX;R9R8R7R6A8S32R5R4R3A6S23S4R3S34A3S16S2aSeS0S0S5R7R4A2M1A3R3A2S2bR3SfS0S0G1A3A2A2S17S16S2aS36R4A2S2bR4S35A2A2S16S2aS9S8RcA1A1M2R4A2S2bR4S2cG2S37A2A2A2A2F_;F_;F_;Fz;Fo;Fw;Ftp;FrhoE;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a rhoE tp w o z Hw Ho Hz. pose proof (SPA_facts_hold segsA _ rhoE X5bc tp w Hw) as HF. destruct w as [tr [ms md]].
  pose proof (proj2 Hw) as HJ. cbn [w_tr w_cfg cfg_model fst snd] in HJ.
  pose proof (proj1 (Forall_forall _ _) HF _ FXBb_0) as HBR.
  destruct Ho as [<-|[<-|[<-|[]]]].
  - left. exact (ex2_band 2%nat st tmax nx0 Hnx_0 (fun X : AA => X) A Kc rho a rhoE tp tr md z HJ Hz).
  - left. exact (ex1_band 2%nat st tmax nx0 Hnx_0 (fun X : AA => X) A Kc rho a rhoE tp tr md z HJ Hz).
  - right. exact (exw_pab 2%nat st tmax nx0 Hnx_0 (fun X : AA => X) A Kc rho a rhoE tp tr md z (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) HJ HBR Hz).
Qed.

Theorem depot_call_S_2hb : ltac2:(tb__ "0|6|
S20OF_;S6S19S2S1eQ40M0A1M1S21S15S1cVst;S1bA3S15SaS18A1VW;SbS18A1A3F_;S29VW;Vst;A2S1aR6A1S12S1R9S11R7A1A3S2dS1RaS11R8A1A3S7S2S2SaG1A1M2SdS0S0A2M3S23G3R1S27R5A1A3S26R2ScS0S0S1dG0RdA2S28S1dG0S3RePcA2A2A1A4A2F_;Fbn;S25R5RdR4A3S1fS1R11S10S1S13U2M4Vst;S14S24S6R1LX;M5R6A2R10RfR5RdA8S30R4R3A5RcA4F_;F_;Ftp';FrhoX;Frho';FG2;S2G2S1fS1ReS10S1S13G4Vst;S14G5RdRcRbRaA8S32R2R1A5R9A4Ftp;FrhoE;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Proof.
  exact (depot_call_S 2%nat st tmax nx0 Hnx_0 NXG_0 (fun X : AA => X) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl)
           Htmax_0 X5bc C5bc NXEb_0 FBEb_0 F192b_0 FDEPb_0 FUNWb_0 WX5rb_0 DX5rb_0 SPL1b_0 SPL2b_0 SPL3b_0 SPL4b_0
           s4b_i R4b_i T4b_i HERb_0 HT4b_0 XX4b_0 FBX4b_0 Hchk4b_0 NX4b_0 WG10b_0 WG15b_0 WG12b_0 EXob FAM4b_0 EXZb_0 NEWOb_0 XPostb_0
           FBT4b_0 XT4b_0 RB1b_0 RB2b_0 nobjb PERM_ndb_0 PERM_ltb_0 PERM_covb_0 PERM_lenb_0 MRG1b_0 MRG2b_0 MRG3b_0 MRG4b_0 sdb_i ENT5b_0 SID5b_0 R4covb_0).
Qed.

Theorem depot_call_SE_2hb : ltac2:(tb__ "0|6|
S6S19S2S1eQ40M0A1M1S20OF_;S15S1cVst;S1bA3S15SaS18A1VW;SbS18A1A3F_;S29VW;Vst;A2S1aR6A1S7S2S2SaG1A1M2SdS0S0A2M3S23G3R1S27R5A1A3S26R2ScS0S0S1dG0RbA2S28S1dG0S3RcPcA2A2A1A4A2F_;Fbn;S25R5RbR4A3S22S1S10S1S13U2M4Vst;S14S24S6R1LX;M5R6A2ReRdR5RbA8S30R4R3A5RaA3F_;F_;Ftp';FrhoX;Frho';FG2;S2G2S22S1S10S1S13G4Vst;S14G5RbRaR9R8A8S32R2R1A5R7A3Ftp;FrhoE;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;").
Proof.
  exact (depot_call_SE 2%nat st tmax nx0 Hnx_0 NXG_0 (fun X : AA => X) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl)
           Htmax_0 X5bc C5bc NXEb_0 FBEb_0 F192b_0 FDEPb_0 FUNWb_0 WX5rb_0 DX5rb_0 SPL1b_0 SPL2b_0 SPL3b_0 SPL4b_0
           s4b_i R4b_i T4b_i HERb_0 HT4b_0 XX4b_0 FBX4b_0 Hchk4b_0 NX4b_0 WG10b_0 WG15b_0 WG12b_0 EXob FAM4b_0 EXZb_0 NEWOb_0 XPostb_0
           FBT4b_0 XT4b_0 RB1b_0 RB2b_0 nobjb PERM_ndb_0 PERM_ltb_0 PERM_covb_0 PERM_lenb_0 MRG1b_0 MRG2b_0 MRG3b_0 MRG4b_0 sdb_i ENT5b_0 SID5b_0 R4covb_0).
Qed.

Theorem sec_g41_2hb : ltac2:(tb__ "0|6|
S20OF_;S6S19S2S1eQ40M0A1M1S21S15S1cVst;S1bA3S15SaS18A1VW;SbS18A1A3F_;S29VW;Vst;A2S1aR6A1S12S1R9S11R7A1A3S2dS1RaS11R8A1A3S7S2S2SaG1A1M2SdS0S0A2M3S23G3R1S27R5A1A3S26R2ScS0S0S1dG0RdA2S28S1dG0S3RePcA2A2A1A4A2F_;Fbn;S25R5RdR4A3S1fS1R11S10S1S13U2M4Vst;S14S24S6R1LX;M5R6A2R10RfR5RdA8S30R4R3A5RcA4F_;F_;Ftp';FrhoX;Frho';FG2;S2G2S1fS1ReS10S1S13G4Vst;S14G5RdRcRbRaA8S39R2R1A5R9A4FtX;FrX;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Proof.
  exact (sec_g41 2%nat st tmax nx0 Hnx_0 NXG_0 (fun X : AA => X) T4bc U4bc X5bc C5bc WU4b_0 DU4b_0 NXU4b_0 HU4b_0 Cert5b_0 depot_call_S_2hb).
Qed.
End INST.
End SpineMallocSec5JW2.

(* [comment removed for export] *)
Module SpineCallocSec6.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "or"; "@Corelib.Init.Datatypes"; "list"; "bool"; "true"; "cons"; "prod"; "nil"; "option"; "pair"; "app"; "Some"; "nat"; "None"; "fst"; "snd"; "length"; "S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sobj"; "sv"; "sprop"; "ss_next"; "eval"; "ss_facts"; "rw"; "holds"; "obj_range"; "sprop_below"; "swf"; "SLit"; "SVar"; "ss_objs"; "rm"; "DUnknown"; "SPBranch"; "SPNot"; "cell"; "mkObj"; "ranges_disjoint"; "sstate"; "SAlu"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_geom"; "ageom"; "aa_ptr_committed"; "aa_sec"; "sec_chunk"; "ag_pab"; "DG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_setS"; "leafA"; "la_state"; "entailsA"; "mkLeafA"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "LQA"; "jpredA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "seq"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "div"; "sub"; "modulo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3"; "skel"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "world"; "assn"; "@Stdlib.Lists.List"; "forallb"; "incl"; "In"; "existsb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "Sh"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "kPtrArrayReserve"; "kPtrArrayCommit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "secmapsize"; "stopJ_stable"; "secneeded"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase"; "stopJ_w"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocST"; "O_1"; "O_2"; "carveS"; "BR"; "O_blk"; "O_w"; "Pret_ms"; "Pret_mz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3"; "range_noband"; "SKEL0"; "JGs"; "noband"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.im.CertCallocSV"; "F_A"; "F_B"; "L3"; "O_3"; "B3"; "B4"; "F_par"; "O_3b"; "a2e8"; "perm7"; "BP9"; "CPC"; "F_g7"; "F_g8"; "F_g9"; "L3b"; "a0e7"; "a2e6"; "a2e7"; "osplit"; "END8"; "O_4z"; "PGST"; "UE9"; "fx8"; "sel7"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_EQ"; "ALU_AND"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP"; "MSENT"; "M48"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSS"; "V_NCH"; "V_NRES"; "nxS";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Str_memsetZ"; "Pre_mszA"; "Posts_mszA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CDepotCall"; "isSome"; "omrg"; "oreb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k5.CDepotCallS"; "AXK"; "dlink"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger"; "sepZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dblocks"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "ltb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "nodupN"; "select"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "merge_objs_at"; "rebase_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsSymJump"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.CertCallocSU"; "DPENT"; "F_g4"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA EntailA CFGA GlueA GlueA2 SummaryA SysCallA MmapA MmapFixedA LedgerA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts Placement StartLib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import StartDefsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildSM SMGlue InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNullInit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildM.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineCallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.SpineCallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineCallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.SpineCallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.RebuildN.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import MmapSymA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require il.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineCallocSec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jp.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.CertCallocSN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineCallocSec OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jv.SpineCallocSec2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.SegD_cost OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.LedgerLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.InvD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.DepotK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.CSecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SecReveal OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.InvReveal OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import EnsureMapA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CDepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CDepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.CSecBump.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import SecLog2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require il.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jx.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require id.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require im.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jb.CInvEnsure OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.CertCallocSU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jx.SpineCallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k6.SpineCallocSec5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.id.DepotKP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k5.CDepotCallS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.im.CertCallocSV.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section SEC6.
Variable nW : nat. Variable st : ustop. Variable tmax : Z.
Let W : list ulink := Wcan nW.
Let segs : list Segment := segsA.
Variable nx : positive.
Hypothesis Hnx : ltac2:(tb__ "0|0|
S0S3cS9eVW;Vst;Vtmax;A3Vnx;A3").
Hypothesis NXG : ltac2:(tb__ "0|0|
S0S5S93Sb6Vnx;A2S6A3").
Let GS : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3.GS nx.
Let JG (BX : AA -> AA) : AA -> KcA -> valuation -> word -> jpredA := ltac2:(tb__ "0|0|
S77VnW;Vst;Vnx;VBX;A4").

Lemma run_band : ltac2:(tb__ "0|3|
S2cS2cF_;S2cS46S14S3eQ40M0A1M1S14S4G1A1S4S56A1S55VJG;R9R8R7R6R5R4R3R2R1A9S3bS1S4fS5eS3dG0R7A2A1M2R1A2S50R1S4eG2S51S63S3dG0S1bR8PcA2A2A1Z8A2A2A2A2S1S4fS60R2A2S50R2S5fA2A2F_;Fz;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FBX;").
Proof.
  intros BX A Kc rho a r tp tr md HJ z Hz.
  pose proof (JGs_nums nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (HN & SMB & _ & _ & IMG & HTOP & _). cbn zeta in *.
  set (ua := bv_unsigned a) in *. set (L := secmapsize (bv_unsigned (rw rho 12%positive))) in *. unfold IMG_HI in IMG.
  pose proof (Sh_in_band ua ltac:(clear -IMG HTOP SMB; lia)) as B1. pose proof (Sh_in_band (ua + L) ltac:(clear -IMG HTOP SMB; lia)) as B2.
  assert (DS : Sh ua + L / 8 <= Sh (ua + L)).
  { unfold Sh. assert (ua / 8 + L / 8 <= (ua + L) / 8); [|lia]. apply Z.div_le_lower_bound; [lia|]. pose proof (Z.mul_div_le ua 8). pose proof (Z.mul_div_le L 8). lia. }
  clear -Hz B1 B2 DS. lia.
Qed.

Lemma ex1_band : ltac2:(tb__ "0|2|
S2cS2cF_;S2cS46S14S3eQ40A1M0S14S4G0A1S4S56A1S55S3bVJG;RaR9R8R7R6R5R4R3R2A9S1S4fS10S3bS3bS1dR6S6aVnx;A1A2M1A3R2A2S50R2S11S3bS3bG1A3A2A2S1S4fS60R3A2S50R3S5fA2A2F_;F_;Fz;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FBX;").
Proof.
  intros BX A Kc rho a r tp tr md z HJ Hz.
  pose proof (site1_bounds nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (EB & _ & LE).
  unfold O_1, L1 in Hz. rewrite obj_range_mk in Hz by lia. cbn [fst snd] in Hz. rewrite EB in Hz.
  apply (run_band BX A Kc rho a r tp tr md HJ z). clear -Hz LE. lia.
Qed.

Lemma ex2_band : ltac2:(tb__ "0|2|
S2cS2cF_;S2cS46S14S3eQ40A1M0S14S4G0A1S4S56A1S55S3bVJG;RaR9R8R7R6R5R4R3R2A9S1S4fS10S3bS3bS1dR6S6bVnx;A1A2M1A3R2A2S50R2S11S3bS3bG1A3A2A2S1S4fS60R3A2S50R3S5fA2A2F_;F_;Fz;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FBX;").
Proof.
  intros BX A Kc rho a r tp tr md z HJ Hz.
  pose proof (site2_vals nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (_ & EB & _ & EL & LR). cbn zeta in EB, EL, LR.
  pose proof (JGs_nums nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (HN & SMB & _ & _ & _ & _ & ENS & _). cbn zeta in HN, SMB, ENS.
  unfold O_2, obj_range, obj_lo_of, obj_hi_of in Hz. cbn [ob_base ob_lo ob_hi fst snd] in Hz.
  rewrite soff_lit_small in Hz by lia. rewrite (soff_of_val r L2 _ EL) in Hz by (clear -LR; lia). rewrite EB in Hz.
  apply (run_band BX A Kc rho a r tp tr md HJ z).
  assert (0 <= secneeded (bv_unsigned (rw rho 12%positive)) / 8) by (apply Z.div_pos; [rewrite ENS; pose proof (round_up_ge' (bv_unsigned (rw rho 12%positive)) 8 ltac:(lia)); lia | lia]).
  clear -Hz LR H. lia.
Qed.

Lemma exblk_pab : ltac2:(tb__ "0|3|
S2cS2cFx;S2cS46S14S3eQ40A1M0S14S4G0A1S4S56A1S55S3bS2cS0S2eS2dRbR1A1A1S2dR1A1A3FX;S2cS0S4S31A1S30RcR1A1A1S30R1A1A3FX;S2cS0S3bS2fRdR1A1A1S4eS2fR1A1S62A2A3FX;VJG;RdRcRbRaR9R8R7R6R5A9S1cR9S25S94S21S9cA1S21S9dA1A3A2S1S4fS10S3bS3bS1dRaS6eA2M1A3R6A2S50R6S11S3bS3bG1A3A2A2S1S4fS32S2dRfA1A1M2R7A2S50R7S4eG2S61A2A2A2F_;F_;F_;F_;F_;F_;Fz;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FBX;").
Proof.
  intros BX A Kc rho a r tp tr md z BXg BXs BXp HJ HBR Hz.
  pose proof (JGs_rigidS nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (_ & _ & _ & _ & _ & _ & _ & E145 & E146 & E147 & _).
  destruct HJ as (_ & _ & HA & _). pose proof (AInvA_pab _ _ _ _ HA) as X. rewrite BXg, BXs, BXp in X. cbn [aa_geom aa_sec aa_ptr_committed bumpV] in X. cbn zeta in X.
  destruct X as (P1 & P2 & P3 & P4 & P5 & P6 & _).
  set (G := aa_geom A) in *. set (c := aa_ptr_committed A) in *.
  pose proof (topG_range G) as TG. pose proof (Zle_0_nat (length (aa_sec A))) as NN.
  unfold kPtrArrayReserve, kPtrArrayCommit, PG, IMG_HI in *.
  assert (C17 : c mod 2 ^ 17 = 0).
  { pose proof (Z.mod_add c 1 (2 ^ 17) ltac:(lia)) as MA. rewrite <- MA. rewrite <- P6. f_equal. }
  pose proof (Z.div_mod c (2 ^ 17) ltac:(lia)) as X. rewrite C17, Z.add_0_r in X.
  pose proof (Z.div_mod c 8 ltac:(lia)) as X8.
  assert (C8 : c mod 8 = 0) by (rewrite X; replace (2 ^ 17 * (c / 2 ^ 17)) with ((2 ^ 14 * (c / 2 ^ 17)) * 8) by lia; apply Z_mod_mult).
  rewrite C8, Z.add_0_r in X8.
  cbn [holds eval] in HBR. rewrite E147, E146 in HBR. fold c in HBR.
  assert (C0 : 0 <= c).
  { destruct (Z_lt_le_dec c 0) as [Hneg|]; [exfalso | assumption].
    assert (Ec : c = - 2 ^ 17) by (clear -X Hneg P5 NN; lia).
    assert (En : Z.of_nat (length (aa_sec A)) = 0) by (clear -Ec P5 NN; lia).
    rewrite En, Ec in HBR. vm_compute in HBR. discriminate HBR. }
  pose proof (Z.div_pos c 8 ltac:(lia) ltac:(lia)) as DP. pose proof (Z.div_le_mono c (2 ^ 23) 8 ltac:(clear -P5; lia) ltac:(clear -P5; lia)) as DM. cbn in DM.
  rewrite bt_eq_lit in HBR by (clear -DP DM NN P5; lia). apply Z.eqb_eq in HBR.
  assert (HcN : 8 * Z.of_nat (length (aa_sec A)) = c) by (rewrite HBR; clear -X8; lia).
  assert (R64 : 0 <= ag_pab G + Z.of_nat (length (aa_sec A)) * 8 < 2 ^ 64) by (clear -P1 P2 TG HcN P5 NN; lia).
  assert (EBw : bv_unsigned (eval r Bw) = ag_pab G + c).
  { unfold Bw. cbn [eval]. rewrite E145, E147, add_val, sll_val. fold G. rewrite !u64_lit by (clear -P1 P2 TG NN HcN P5; lia).
    change (3 mod 64) with 3. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
    rewrite (Z.mod_small (Z.of_nat (length (aa_sec A)) * 8)) by (clear -NN HcN P5; lia). rewrite (Z.mod_small _ _ R64). clear -HcN. lia. }
  unfold O_blk in Hz. rewrite obj_range_mk in Hz by lia. cbn [fst snd] in Hz. rewrite EBw in Hz. clear -Hz P5 C0. lia.
Qed.

Lemma exw_pab : ltac2:(tb__ "0|3|
S2cS2cFx;S2cS46S14S3eQ40A1M0S14S4G0A1S4S56A1S55S3bS2cS0S2eS2dRbR1A1A1S2dR1A1A3FX;S2cS0S4S31A1S30RcR1A1A1S30R1A1A3FX;S2cS0S3bS2fRdR1A1A1S2fR1A1A3FX;VJG;RdRcRbRaR9R8R7R6R5A9S1cR9S26S25S94S21S9cA1S21S9dA1A3A1A2S1S4fS10S3bS3bS1dRaS6fA2M1A3R6A2S50R6S11S3bS3bG1A3A2A2S1S4fS32S2dRfA1A1M2R7A2S50R7S4eG2S61A2A2A2F_;F_;F_;F_;F_;F_;Fz;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FBX;").
Proof.
  intros BX A Kc rho a r tp tr md z BXg BXs BXp HJ HBR Hz.
  pose proof (site_b nW st tmax nx Hnx Pret_ms Pret_ms Pret_ms Pret_ms eq_refl eq_refl BX A Kc rho a r tp tr md BXg BXs BXp HJ HBR) as (EBw & B1 & B2 & B3 & _). cbn zeta in EBw, B1, B2, B3.
  unfold O_w in Hz. rewrite obj_range_mk in Hz by lia. cbn [fst snd] in Hz. rewrite EBw in Hz. clear -Hz B1 B2 B3. lia.
Qed.

Lemma pab_noband : ltac2:(tb__ "0|2|
S2cS2cFx;S2cS46S14S3eQ40A1M0S14S4G0A1S4S56A1S55S2cS0S2eS2dRaR1A1A1S2dR1A1A3FX;VJG;RaR9R8R7R6R5R4R3R2A9S3bS1S4fS32S2dRbA1A1M1R1A2S50R1S4eG1S61A2A2A2S78R2A1F_;Fz;F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FBX;").
Proof.
  intros BX A Kc rho a r tp tr md BXg HJ z Hz. destruct HJ as (_ & _ & HA & _).
  pose proof (AInvA_pab _ _ _ _ HA) as X. rewrite BXg in X. cbn [aa_geom bumpV] in X. cbn zeta in X. destruct X as (_ & _ & _ & P4 & _).
  unfold noband. clear -P4 Hz. lia.
Qed.
Lemma pxa_noband : ltac2:(tb__ "0|2|
S2cS2cFx;S2cS46S14S3eQ40A1M0S14S4G0A1S4S56A1S55S2cS0S2eS2dRaR1A1A1S2dR1A1A3FX;S2cS0S4S31A1S30RbR1A1A1S30R1A1A3FX;S2cS0S3bS2fRcR1A1A1S4eS2fR1A1S62A2A3FX;VJG;RcRbRaR9R8R7R6R5R4A9S4cS17S1cR8A1S7S17S25S94S21S9cA1S21S9dA1A3S9S17A1A3A3S4S15A1S0S4S8S8S16S16A2S16A2M1A1S4bS15G1S54R1A4S4bS15G1S54S7S15S6eS9S15A1A3A4A3S4cS15S15S75S1dRcR1A2A1Lo;R2A3F_;Fl;F_;F_;F_;F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FBX;").
Proof.
  intros BX A Kc rho a r tp tr md BXg BXs BXp HJ HF l EE. apply Forall_inv in HF.
  destruct l as [|o [|o' l']]; try (cbn in EE; discriminate EE). assert (Es : skel o = skel O_blk) by (cbn in EE; congruence).
  apply Forall_cons; [|apply Forall_nil]. rewrite (obj_range_skel r o O_blk Es). intros z Hz.
  exact (pab_noband BX A Kc rho a r tp tr md BXg HJ z (exblk_pab BX A Kc rho a r tp tr md z BXg BXs BXp HJ HF Hz)).
Qed.
Lemma pxb_noband : ltac2:(tb__ "0|2|
S2cS2cFx;S2cS46S14S3eQ40A1M0S14S4G0A1S4S56A1S55S2cS0S2eS2dRaR1A1A1S2dR1A1A3FX;S2cS0S4S31A1S30RbR1A1A1S30R1A1A3FX;S2cS0S3bS2fRcR1A1A1S2fR1A1A3FX;VJG;RcRbRaR9R8R7R6R5R4A9S4cS17S1cR8A1S7S17S26S25S94S21S9cA1S21S9dA1A3A1S9S17A1A3A3S4S15A1S0S4S8S8S16S16A2S16A2M1A1S4bS15G1S54R1A4S4bS15G1S54S7S15S6fS9S15A1A3A4A3S4cS15S15S75S1dRcR1A2A1Lo;R2A3F_;Fl;F_;F_;F_;F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FBX;").
Proof.
  intros BX A Kc rho a r tp tr md BXg BXs BXp HJ HF l EE. apply Forall_inv in HF.
  destruct l as [|o [|o' l']]; try (cbn in EE; discriminate EE). assert (Es : skel o = skel O_w) by (cbn in EE; congruence).
  apply Forall_cons; [|apply Forall_nil]. rewrite (obj_range_skel r o O_w Es). intros z Hz.
  exact (pab_noband BX A Kc rho a r tp tr md BXg HJ z (exw_pab BX A Kc rho a r tp tr md z BXg BXs BXp HJ HF Hz)).
Qed.

Section G41.
Variable BX : AA -> AA.
Variables (T4 U4 X5 C5 : axst).
Hypothesis WU4 : ltac2:(tb__ "0|0|
S0S5S1fS34VU4;A1A1S6A3").
Hypothesis DU4 : ltac2:(tb__ "0|4|
S0SaS8S4S8S16S16A2M0A1M1S4S17A1M2A2M3A1S67S34VT4;A1S34VU4;A1A2SdG3SbG1G2S9G0A1Sb5Vnx;A1A4A2A3").
Hypothesis NXU4 : ltac2:(tb__ "0|0|
S0S3cS18S34VU4;A1A1S18S34VT4;A1A1A3").
Hypothesis HU4 : ltac2:(tb__ "0|0|
S0S35S36VT4;S34VU4;A1A2VU4;A3").
Hypothesis Cert5 : ltac2:(tb__ "0|1|
S0S5S68S72Ufa0S7S3bSb4S9S3bA1A3VGS;S7S35VU4;S9S35A1M0A3S7S35VX5;G0A3A6S6A3").

Hypothesis HDS : ltac2:(tb__ "0|4|
S58OF_;S2cS46S14S3eQ40M0A1M1S59S66VW;Vst;A2S64VW;Vst;A2S47R6A1S42Vsegs;R9S41R7A1A3Sa4Vsegs;RaS41R8A1A3S33S14S14S4G1A1M2S8S3bS3bA2M3S5cG3R1SabR5A1A3SaaR2SbS3bS3bS3dG0RdA2S63S3dG0S1bRePcA2A2A1A4A2F_;Fbn;Sa9R5RdR4A3S57Vsegs;R11S40Vsegs;VJG;Sa8VBX;R6A2R10RfR5RdA5VC5;R4R3A5RcA4F_;F_;Ftp';FrhoX;Frho';FG2;S14G2S57Vsegs;ReS40Vsegs;VJG;VBX;RdRcRbRaA5VX5;R2R1A5R9A4Ftp;FrhoE;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").

Theorem sec_g41 : ltac2:(tb__ "0|4|
S58OF_;S2cS46S14S3eQ40M0A1M1S59S66VW;Vst;A2S64VW;Vst;A2S47R6A1S42Vsegs;R9S41R7A1A3Sa4Vsegs;RaS41R8A1A3S33S14S14S4G1A1M2S8S3bS3bA2M3S5cG3R1SabR5A1A3SaaR2SbS3bS3bS3dG0RdA2S63S3dG0S1bRePcA2A2A1A4A2F_;Fbn;Sa9R5RdR4A3S57Vsegs;R11S40Vsegs;VJG;Sa8VBX;R6A2R10RfR5RdA5VC5;R4R3A5RcA4F_;F_;Ftp';FrhoX;Frho';FG2;S14G2S57Vsegs;ReS40Vsegs;VJG;VBX;RdRcRbRaA5VT4;R2R1A5R9A4FtX;FrX;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho a Q HW HUS HKc Hokl Hokpl Hcont rX tX.
  pose proof (JG_okf nW st nx BX ok A Kc rho a Hokl) as Hokf. pose proof (JG_stable nW st tmax nx Hnx NXG BX A Kc rho a HUS HKc) as HST.
  eapply triple_conseq; [intros w Hw; exact (RSU4 nW st tmax nx Hnx T4 U4 WU4 DU4 NXU4 HU4 BX A Kc rho a rX tX w Hw) | intros w Hw; exact Hw |].
  apply (cfg_soundA segs 4000%nat [DPENT] GS [U4] [X5] (JG BX A Kc rho a) ok Q tX Hokf HST Cert5); [|left; reflexivity].
  intros E rE HinE. destruct HinE as [<-|[]].
  eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw |].
  exact (HDS ok A Kc rho a Q HW HUS HKc Hokl Hokpl Hcont rE tX).
Qed.
End G41.

Lemma diamond_hold : ltac2:(tb__ "0|2|
S2cS2cFx;S2cS46S14S3eQ40A1M0S14S4G0A1S4S56A1S55S2cS0S2eS2dRaR1A1A1S2dR1A1A3FX;VJG;RaR9R8R7R6R5R4R3R2A9S3S4cS17S1cR6A1M1S79Vnx;A1A3S4cS17G1S7aVnx;A1A3A2F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FBX;").
Proof.
  intros BX A Kc rho a r tp tr md BXg HJ.
  pose proof (JGs_rigidS nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (_ & Enx & _ & E142 & _ & _ & E155 & _).
  pose proof (JGs_nums nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (HN & SMB & _ & _ & IMG & HTOP & _). cbn zeta in *.
  destruct HJ as (_ & _ & HA & HP & _). destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & SSP & _).
  pose proof (proj1 HA) as HG. rewrite BXg in HG. cbn [aa_geom bumpV] in HG.
  pose proof (geom_nums _ HG) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S1 & S2 & _). rewrite kSpaceSize_val in S2. unfold HIGH_SHADOW_END in S1.
  unfold sepZ in SSP. cbn [fst snd] in SSP. rewrite kSpaceSize_val in SSP.
  pose proof (urange a) as Ra. unfold IMG_HI in IMG.
  set (ua := bv_unsigned a) in *. set (L := secmapsize (bv_unsigned (rw rho 12%positive))) in *. set (SB := ag_spacebeg (aa_geom A)) in *.
  pose proof (topG_range (aa_geom A)) as TG.
  assert (RSB : 0 <= SB < 2 ^ 64) by (clear -S1 S2 TG; lia).
  assert (RL : 0 <= L < 2 ^ 64) by (clear -SMB HN; lia).
  destruct SSP as [SA|SB'].
  - left. unfold F_A. apply Forall_cons; [|apply Forall_nil]. cbn [holds eval]. rewrite Enx, E142, E155, add_val. fold ua L SB.
    rewrite (u64_lit L RL), (u64_lit SB RSB). rewrite Z.mod_small by (clear -IMG HTOP SMB; lia). exact SA.
  - right. unfold F_B. apply Forall_cons; [|apply Forall_nil]. cbn [holds eval]. rewrite Enx, E155, add_val. fold ua SB.
    rewrite (u64_lit SB RSB). rewrite u64_lit by lia. rewrite Z.mod_small by (clear -S1 S2 TG; lia). clear -SB'. lia.
Qed.

Lemma site3_vals : ltac2:(tb__ "0|3|
S2cS2cF_;S2cS46S14S3eQ40M0A1M1S14S4G1A1S4S56A1S55VJG;R9R8R7R6R5R4R3R2R1A9S1S0S3bS3dG0S19R5S7dVnx;A1A2A2S4eS5eS3dG0R6A2A1Z200A2A3S1S0G1S19R5S8aVnx;A1A2S19R5S7bA2M2A3S0S3bS3dG0G2A2Z100A3A2A2F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FBX;").
Proof.
  intros BX A Kc rho a r tp tr md HJ.
  pose proof (JGs_rigidS nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (_ & Enx & _).
  pose proof (JGs_nums nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (HN & SMB & _ & AL & IMG & HTOP & _). cbn zeta in *.
  pose proof (urange a) as Ra. unfold PG in AL. set (ua := bv_unsigned a) in *. unfold IMG_HI in IMG.
  assert (D1 : (ua + 4096) / 8 = ua / 8 + 512) by (replace (ua + 4096) with (ua + 512 * 8) by lia; rewrite Z.div_add by lia; reflexivity).
  assert (D2 : (ua + 6136) / 8 = ua / 8 + 767) by (replace (ua + 6136) with (ua + 767 * 8) by lia; rewrite Z.div_add by lia; reflexivity).
  pose proof (Z.div_pos ua 8 ltac:(lia) ltac:(lia)) as DP. pose proof (Z.div_lt_upper_bound ua 8 (2 ^ 61) ltac:(lia) ltac:(lia)) as DU.
  split; [|split].
  - unfold B3. cbn [eval]. rewrite Enx, add_val, srl_val, add_val, !u64_lit by lia. fold ua. change (3 mod 64) with 3.
    rewrite (Z.mod_small (ua + 4096)) by (clear -Ra HTOP SMB; lia). rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. rewrite D1.
    unfold Sh, SHADOW_OFF. rewrite Z.mod_small by (clear -DP DU; lia). lia.
  - unfold a2e6, L3. cbn [eval]. rewrite Enx. apply bv_eq.
    rewrite sub_val, add_val, !srl_val, !add_val, !u64_lit by lia. fold ua. change (3 mod 64) with 3.
    rewrite (Z.mod_small (ua + 4096)) by (clear -Ra HTOP SMB; lia). rewrite (Z.mod_small (ua + 6136)) by (clear -Ra HTOP SMB; lia).
    rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. rewrite D1, D2.
    rewrite (Z.mod_small (ua / 8 + 767 + 1)) by (clear -DP DU; lia). replace (ua / 8 + 767 + 1 - (ua / 8 + 512)) with 256 by lia. reflexivity.
  - unfold L3. cbn [eval]. apply u64_lit. lia.
Qed.

Section G43.
Variable BX : AA -> AA.
Hypothesis BXg : ltac2:(tb__ "0|0|
S2cS0S2eS2dVBX;R1A1A1S2dR1A1A3FX;").

Variable PX : list sobj.
Variable FXP : list sprop.
Hypothesis PX_noband : ltac2:(tb__ "0|2|
S2cS46S14S3eQ40A1M0S14S4G0A1S4S56A1S55VJG;VBX;R8R7R6R5R4R3R2R1A9S4cS17S1cR5A1VFXP;A3S4S15A1S0S4S8S8S16S16A2S16A2M1A1S4bS15G1S54R1A4S4bS15G1S54VPX;A4A3S4cS15S15S75S1dR9R1A2A1Lo;R2A3F_;Fl;F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;").
Variables (C5 C5A C5B Y6A Y6B E6 CT6 CO6 T6 : axst) (sA sB s6 : wsub) (R6 : list sobj).
Let D6 : axst := ltac2:(tb__ "0|0|
S96VT6;S1aS34VCO6;A1A1A2").
Hypothesis HC5A : ltac2:(tb__ "0|0|
S0S35S69S79Vnx;A1VC5;A2VC5A;A3").
Hypothesis HC5B : ltac2:(tb__ "0|0|
S0S35S69S7aVnx;A1VC5;A2VC5B;A3").
Hypothesis FBA : ltac2:(tb__ "0|0|
S0S5S5aS17S1eS18S34VC5;A1A1A1S79Vnx;A1A3S6A3").
Hypothesis FBB : ltac2:(tb__ "0|0|
S0S5S5aS17S1eS18S34VC5;A1A1A1S7aVnx;A1A3S6A3").
Hypothesis Cert6A : ltac2:(tb__ "0|1|
S0S5S68S72Ufa0S7S3bS9aS9S3bA1A3VGS;S7S35VC5A;S9S35A1M0A3S7S35VY6A;G0A3A6S6A3").
Hypothesis Cert6B : ltac2:(tb__ "0|1|
S0S5S68S72Ufa0S7S3bS9aS9S3bA1A3VGS;S7S35VC5B;S9S35A1M0A3S7S35VY6B;G0A3A6S6A3").
Hypothesis E6A : ltac2:(tb__ "0|0|
S0S5S39VY6A;VE6;VsA;A3S6A3").
Hypothesis I6A : ltac2:(tb__ "0|0|
S0S5Sa2VsA;VGS;A2S6A3").
Hypothesis E6B : ltac2:(tb__ "0|0|
S0S5S39VY6B;VE6;VsB;A3S6A3").
Hypothesis I6B : ltac2:(tb__ "0|0|
S0S5Sa2VsB;VGS;A2S6A3").

Hypothesis WC6 : ltac2:(tb__ "0|0|
S0S5S1fS34VCT6;A1A1S6A3").
Hypothesis DF6 : ltac2:(tb__ "0|4|
S0SaS8S4S8S16S16A2M0A1M1S4S17A1M2A2M3A1S67S34VE6;A1S34VCT6;A1A2SdG3SbG1G2S7G0SbS16S16S8aVnx;A1S7bA4S9G0A1A3S9S17A1A4A2A3").
Hypothesis NX6 : ltac2:(tb__ "0|0|
S0S3cS18S34VCT6;A1A1S18S34VE6;A1A1A3").
Hypothesis HC6 : ltac2:(tb__ "0|0|
S0S35S36VE6;S34VCT6;A1A2VCT6;A3").
Hypothesis SK6 : ltac2:(tb__ "0|1|
S0S4S8S8S16S16A2S16A2M0A1S4bS15G0S54S22S34VCT6;A1A1A4S4bS15G0S54ScS15S7S15S6bVnx;A1S7S15S6aVnx;A1S9S15A1A3A3ScS15S76VnW;Vnx;A2VPX;A3A3A4A3").
Hypothesis FC6 : ltac2:(tb__ "0|0|
S5bS17ScS17S4aVW;Vst;A2S49S48A1A3S1aS34VCT6;A1A1A3").
Hypothesis FX6 : ltac2:(tb__ "0|0|
S5bS17VFXP;S1aS34VCT6;A1A1A3").
Hypothesis XC6 : ax_X CT6 = [].
Hypothesis HCO6 : ltac2:(tb__ "0|0|
S0S35S6cVCT6;S28S7dVnx;A1S20Z0A1S7bS9S27A1S24A5A2VCO6;A3").
Hypothesis WCO6 : ltac2:(tb__ "0|0|
S0S5S1fS34VCO6;A1A1S6A3").
Hypothesis He6 : ltac2:(tb__ "0|1|
S0SaS4S15A1M0A1S98VCO6;S73Vs6;A3SdG0VR6;A2A3").
Hypothesis Hchk6 : ltac2:(tb__ "0|0|
S0S5S97VCO6;S73Vs6;VR6;S4bS37S35S38S74A4A5S6A3").
Hypothesis HT6 : ltac2:(tb__ "0|0|
S0S35S99Vs6;S73S70VCO6;VR6;A5VT6;A3").
Hypothesis FBC6 : ltac2:(tb__ "0|1|
S0S5S5aS17S1eS18S34VCO6;A1M0A1A1S1aG0A1A3S6A3").
Hypothesis FBT6 : ltac2:(tb__ "0|0|
S0S5S5aS17S1eS18S34VT6;A1A1A1S1aS34VCO6;A1A1A3S6A3").
Hypothesis NXC6 : ltac2:(tb__ "0|0|
S0S5S93VGS;S18S34VCO6;A1A1A2S6A3").

Lemma RS6 : ltac2:(tb__ "0|1|
S2cS46S14S3eQ40A1M0S14S4G0A1S58S66VW;Vst;A2S40Vsegs;VJG;VBX;R8R7R6R5A5VE6;R4R3R2A6S40Vsegs;VJG;VBX;R9R8R7R6A5VCT6;R5R4R3A6F_;F_;Fw;Ftp;FrhoX;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a rhoX tp w HW Hw. destruct w as [tr [ms md]]. rewrite <- HC6.
  eapply SPA_restate; [exact WC6 | exact DF6 | exact NX6 | | constructor | exact Hw].
  unfold diffs_ok. apply Forall_cons; [|apply Forall_nil]. cbn [fst snd].
  exact (proj1 (proj2 (site3_vals BX A Kc rho a rhoX tp tr md (proj2 Hw)))).
Qed.

Lemma HBL6 : ltac2:(tb__ "0|b|
S2cS46S14S3eQ40M0A1M1S14S4G1A1S58S40Vsegs;VJG;VBX;R7R6R5R4A5VCT6;R3R2R1A6S1S4fS5eS3dG0R5A2A1M2S3dG0S19R4S7dVnx;A1M3A2A2M4A2S1S4fS4eG4S3dG0S19R4S7bA2A2A2S4eG2S51S63S3dG0S1bR6PcA2A2A1Z8A2A2A2S1S4S15A1M5S0S4S8S8S16S16A2S16A2M6A1M7S4bS15G6S54R1A4M8S4bS15G6S54S7S15S6bVnx;A1S7S15S6aVnx;A1S9S15A1A3A3A4A3S4cS15S15S29S1dR7R1A2SbS3bS3bS3dG0S19R7G3A2A2M9S4eG9S3dG0S19R7S7bA2A2A2A4A2Lo;R2A3MaF_;Fl;G5S0G7G8S4bS15G6S54VPX;A4A3GaF_;Fl;A2A2A2F_;Fw;Ftp;FrhoX;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a rhoX tp w Hw. pose proof (SPA_facts_hold segs _ rhoX CT6 tp w Hw) as HF. destruct w as [tr [ms md]].
  pose proof (proj2 Hw) as HJ. cbn [w_tr w_cfg cfg_model fst snd] in HJ.
  destruct (site3_vals BX A Kc rho a rhoX tp tr md HJ) as (EB & _ & EL). rewrite EB, EL.
  destruct (site2_vals nW st tmax nx Hnx BX A Kc rho a rhoX tp tr md HJ) as (_ & EB2 & _ & EL2 & BL2 & _). cbn zeta in EB2, EL2, BL2.
  destruct (site1_bounds nW st tmax nx Hnx BX A Kc rho a rhoX tp tr md HJ) as (EB1 & EL1 & BB1).
  pose proof (JGs_nums nW st tmax nx Hnx BX A Kc rho a rhoX tp tr md HJ) as (HN & SMB & SMM & AL & IMG & TOP & ENS & EMS & R8M & R8B). cbn zeta in *.
  assert (V512 : 512 <= secneeded (bv_unsigned (rw rho 12%positive)) / 8) by (rewrite ENS; apply Z.div_le_lower_bound; clear -R8B HN; lia).
  assert (L9216 : 9216 <= secmapsize (bv_unsigned (rw rho 12%positive)) / 8) by (apply Z.div_le_lower_bound; clear -SMB; lia).
  split; [lia|]. split; [clear -L9216; lia|]. split.
  - intros l2 EE. destruct l2 as [|o [|o' [|o'' l2']]]; try (cbn in EE; discriminate EE).
    assert (Es : skel o = skel (O_2 nx)) by (cbn in EE; congruence). assert (Es' : skel o' = skel (O_1 nx)) by (cbn in EE; congruence).
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + rewrite (obj_range_skel rhoX o (O_2 nx) Es). unfold O_2, obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi fst snd].
      rewrite soff_lit_small by lia. rewrite (soff_of_val rhoX L2 _ EL2) by (clear -BL2; lia). rewrite EB2.
      unfold ranges_disjoint. cbn [fst snd]. right. right. right. clear -V512. lia.
    + rewrite (obj_range_skel rhoX o' (O_1 nx) Es'). unfold O_1, L1. rewrite obj_range_mk by lia. rewrite EB1.
      unfold ranges_disjoint. cbn [fst snd]. right. right. left. lia.
  - intros l2 EE. pose proof (run_band BX A Kc rho a rhoX tp tr md HJ) as RB.
    assert (HFX : Forall (holds rhoX) FXP) by (apply Forall_forall; intros p Hp; exact (proj1 (Forall_forall _ _) HF p (FX6 p Hp))).
    pose proof (PX_noband A Kc rho a rhoX tp tr md HJ HFX l2 EE) as NB.
    eapply Forall_impl; [|exact NB]. intros o Ho. cbn beta in Ho. unfold ranges_disjoint. cbn [fst snd].
    destruct (Z_lt_le_dec (fst (obj_range rhoX o)) (snd (obj_range rhoX o))) as [NE|]; [|left; lia].
    destruct (Z_le_gt_dec (snd (obj_range rhoX o)) (Sh (bv_unsigned a) + 512)) as [|G1]; [right; right; left; lia|].
    destruct (Z_le_gt_dec (Sh (bv_unsigned a) + 512 + 256) (fst (obj_range rhoX o))) as [|G2]; [right; right; right; lia|].
    exfalso. set (x := Z.max (fst (obj_range rhoX o)) (Sh (bv_unsigned a) + 512)).
    pose proof (Ho x ltac:(unfold x; lia)) as NBx. pose proof (RB x ltac:(unfold x; clear -L9216 G1 G2 NE; lia)) as Bx.
    unfold noband in NBx. clear -NBx Bx. lia.
Qed.

Theorem sec_g43 : ltac2:(tb__ "0|5|
S58OF_;S2cS46S14S3eQ40M0A1M1S59S66VW;Vst;A2S64VW;Vst;A2S47R6A1S42Vsegs;R9S41R7A1A3S3bS1S4fS5eS3dG0R7A2A1M2R1A2S50R1S4eG2S51S63S3dG0S1bR8PcA2A2A1Z8A2A2A2A2S2S0SaS3eQ8A1M3A1S23R9S3fG0R2A2A2SfG3A1A3A1F_;Fz;S14S4G1A1M4S57Vsegs;RdS40Vsegs;VJG;VBX;RcRbRaR9A5VD6;R2R1A5R8A4FtpY;FrhoY;S14G4S57Vsegs;ReS40Vsegs;VJG;VBX;RdRcRbRaA5VC5;R2R1A5R9A4FtX;FrX;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho a Q HW HUS HKc Hokl RUNDEF HCONT rX tX.
  pose proof (JG_okf nW st nx BX ok A Kc rho a Hokl) as Hokf. pose proof (JG_stable nW st tmax nx Hnx NXG BX A Kc rho a HUS HKc) as HST.
  assert (SL : slink (bv_unsigned a) (secmapsize (bv_unsigned (rw rho 12%positive))) rho rho).
  { split; [intros i; reflexivity|]. split; [intros l; reflexivity|]. split; [intros x; left; reflexivity | exact RUNDEF]. }

  assert (TAIL : forall rE tE, triple segs ok (SPA segs (JG BX A Kc rho a) E6 rE tE) Q).
  { intros rE tE.
    apply (ms_step nW st tmax nx Hnx NXG BX BXg E6 CT6 CO6 T6 (B3 nx) L3 [O_2 nx; O_1 nx] PX Pre_memsetA Pret_ms Posts_memsetA s6 R6 eq_refl
             (fun ok0 Jx r0 t0 Ho Hs => memset_sumA ok0 Jx r0 t0 Ho Hs) eq_refl RS6 HBL6 SK6 FC6 XC6 HCO6 WCO6 He6 Hchk6 HT6 FBC6 FBT6 NXC6
             ok A Kc rho rho a tE Q HW HUS HKc Hokl SL).
    intros rhoY tpY. exact (HCONT rhoY tpY). }

  apply (triple_conseq (P:=fun w => SPA segs (JG BX A Kc rho a) C5A rX tX w \/ SPA segs (JG BX A Kc rho a) C5B rX tX w)
           (SPA segs (JG BX A Kc rho a) C5 rX tX) (Q:=Q)); [intros w Hw | intros w Hw; exact Hw |].
  { destruct w as [tr [ms md]]. destruct (diamond_hold BX A Kc rho a rX tX tr md BXg (proj2 Hw)) as [FA|FB]; [left; rewrite <- HC5A | right; rewrite <- HC5B].
    - split; [|exact (proj2 Hw)]. exact (smatchA_add_facts segs rX tX (F_A nx) _ _ (proj1 Hw) FA FBA).
    - split; [|exact (proj2 Hw)]. exact (smatchA_add_facts segs rX tX (F_B nx) _ _ (proj1 Hw) FB FBB). }
  apply triple_disj.
  - apply (cfg_soundA segs 4000%nat [MSENT] GS [C5A] [Y6A] (JG BX A Kc rho a) ok Q tX Hokf HST Cert6A); [|left; reflexivity].
    intros E rE HinE. destruct HinE as [<-|[]].
    eapply triple_conseq; [intros w Hw; exact (join4 nW st tmax nx Hnx NXG BX A Kc rho a Y6A E6 sA rE tX w HUS HKc E6A I6A Hw) | intros w Hw; right; exact Hw |].
    apply TAIL.
  - apply (cfg_soundA segs 4000%nat [MSENT] GS [C5B] [Y6B] (JG BX A Kc rho a) ok Q tX Hokf HST Cert6B); [|left; reflexivity].
    intros E rE HinE. destruct HinE as [<-|[]].
    eapply triple_conseq; [intros w Hw; exact (join4 nW st tmax nx Hnx NXG BX A Kc rho a Y6B E6 sB rE tX w HUS HKc E6B I6B Hw) | intros w Hw; right; exact Hw |].
    apply TAIL.
Qed.
End G43.

Lemma ms_call : ltac2:(tb__ "0|8|
S2cS2cF_;S35S35S35S35S4S37A1M0Sa3S4S15A1M1S0G0R3S7S37S3aR4Sb2A2S9S37A1A3A3S58OF_;M2S44S14S4S3eQ40A1M3A1M4S42Vsegs;R4R3A3S45Vsegs;Sa1R4A3S57Vsegs;R6S40Vsegs;R5RcR4R3A5S43Vsegs;R5Sa1R4R3RaA6A4F_;F_;Ftp;Frho;FJx;Fok;S0S3cS18S34R7A1A1Sa1A3S0SaG1A1S98RaR8R5A3SdG1R4A2A3S0S5S97RbR9R6R5S4bS37S35S38R7A4A5S6A3S0S35S99R7RaR9RcR6A5RbA3S0S5S5aS17S1eS18S34RdA1M5A1A1M6S1aG5A1A3S6A3S0S5S5aS17G6S1aS34ReA1A1A3S6A3S0S5S93VGS;S18S34RfA1A1A2S6A3G2S2cS46S14G3G4S59S64VW;Vst;A2S47R6A1S42Vsegs;R9S41R7A1A3S14G4S57Vsegs;RcS40Vsegs;VJG;R1dRbRaR9R8A5M7S96R1bS1aS34R1cA1A1A2R2R1A5R6A4FtpY;FrhoY;S14S57Vsegs;RcS40Vsegs;G7R1cR1R7A5R6A4FrhoX;F_;F_;F_;F_;FQ;Ftp;Fa;Frho;FKc;FA;Fok;F_;F_;F_;F_;F_;F_;F_;F_;F_;FR;Fs;FPosts;FPret;FPre;FT;FCM;FBX;").
Proof.
  intros BX CM T Pre Pret Posts s R HPosts Hsum NPre He Hchk HT FBC FBT NXC ok A Kc rho a tp Q HUS HKc Hokf HD rhoX.
  pose proof (JG_stable nW st tmax nx Hnx NXG BX A Kc rho a HUS HKc) as HST.
  set (Jf := (fun (_ : valuation) t tr md => JG BX A Kc rho a rhoX t tr md) : jpredA).
  assert (Jf_okf : ok_frameA segs ok Jf).
  { intros r t tr ms md msv' HJ HMI Hh Hp Hs. exact (Hokf rhoX t tr ms md msv' (JG_K nW st nx BX A Kc rho a _ _ _ _ HJ) HMI Hh Hp Hs). }
  assert (Jf_st : stableA segs NF Jf).
  { intros r r' t tr md md' Hag Hme HJ. unfold Jf in *. eapply HST; [apply agree_below_refl | exact Hme | exact HJ]. }
  apply (triple_pre_pure segs ok _ _ (Forall (holds rhoX) (ss_facts (ax_S CM)))).
  { intros w Hw. exact (SPA_facts_hold segs _ rhoX CM tp w Hw). }
  intros HFC.
  apply (call_soundA segs ok (JG BX A Kc rho a) Jf Jf (JG BX A Kc rho a) CM Pre s R Posts Q rhoX tp He Hchk).
  - intros rho1 tp1. rewrite NPre. exact (Hsum ok Jf rho1 tp1 Jf_okf Jf_st).
  - intros tr ms md Hsm HJ. exact HJ.
  - intros Lf rho' rhoL tpL tr ms md tr' md' HinL Hsm HJ HLK HJ'. unfold Jf in HJ'.
    eapply HST; [| apply mat_equiv_refl | exact HJ'].
    eapply agree_below_le; [apply Pos.leb_le; exact NXC | exact (proj1 HLK)].
  - intros Lf rho' tpL HinL Hag. rewrite HPosts in HinL. destruct HinL as [<-|[]]. cbn [la_state]. rewrite HT.
    eapply triple_conseq; [intros w Hw | intros w Hw; exact Hw | apply (HD rho' tpL)].
    apply SPA_refacts; [exact Hw | exact FBT |]. intros _.
    exact (Forall_holds_agree _ rhoX rho' _ Hag FBC HFC).
Qed.

Lemma F_g7_hold : ltac2:(tb__ "0|1|
S2cS2cF_;S2cS46S14S3eQ40A1M0S14S4G0A1S4S56A1S55VJG;R9R8R7R6R5R4R3R2R1A9S4cS17S1cR5A1S85Vnx;A1A3F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FBX;").
Proof.
  intros BX A Kc rho a r tp tr md HJ.
  pose proof (JGs_rigidS nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (E12 & Enx & _).
  pose proof (JGs_nums nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (HN & SMB & _ & AL & IMG & HTOP & ENS & EMS & R8M & R8B). cbn zeta in *.
  pose proof (urange a) as Ra. set (ua := bv_unsigned a) in *. set (nv := bv_unsigned (rw rho 12%positive)) in *. unfold IMG_HI in IMG.
  assert (LB : nv + 6151 <= secmapsize nv).
  { rewrite EMS, ENS. pose proof (round_up_ge' (round_up nv 8 + 4096) PG ltac:(unfold PG; lia)). unfold PG in *. lia. }
  unfold F_g7, RUE. apply Forall_cons; [|apply Forall_nil]. cbn [holds eval branch_taken]. intros H. unfold bv_ltu in H. apply Z.ltb_lt in H.
  rewrite and_val, !add_val, Enx, E12, !u64_lit in H by lia. fold ua nv in H.
  rewrite (Z.mod_small (ua + 6144)) in H by (clear -Ra HTOP SMB; lia). rewrite (Z.mod_small (ua + 6144 + nv)) in H by (clear -Ra HTOP LB HN SMB; lia).
  rewrite (Z.mod_small (ua + 6144 + nv + 7)) in H by (clear -Ra HTOP LB HN SMB; lia).
  rewrite (land_m8E nW st tmax nx Hnx) in H by (clear -Ra HTOP LB HN SMB; lia). pose proof (Z.mod_pos_bound (ua + 6144 + nv + 7) 8 ltac:(lia)) as MB. clear -H MB HTOP LB Ra HN SMB. lia.
Qed.

Lemma site7_vals : ltac2:(tb__ "0|9|
S2cS2cF_;S2cS46S14S3eQ40M0A1M1S14S4G1A1S4S56A1S55VJG;R9R8R7R6R5R4R3R2R1A9S3dG0S1bR7PcA2A2S3bS3dG0R7A2S3bS65R2A1S3bS63R3A1S3bS1S0G1S19R9S89Vnx;A1A2S19R9S6dVnx;A1A2M2A3S1S0G1S19R9S8bVnx;A1A2S19R9S88A2M3A3S1S0S3bS3dG0G2A2S4eS4eS5eR3A1S51R2Z8M4A2M5A2Z100M6A2A3S1S0S3bS3dG0G3A2S52S52S51R1G4A2M7G5A2G6A2A3S1S4fZ200M8G5A2S4fS4eG5G8A2G7A2A2A2A2A2A2TMS;TVNS;Tua;Tnv;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FBX;").
Proof.
  intros BX A Kc rho a r tp tr md HJ.
  pose proof (JGs_rigidS nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (E12 & Enx & E141 & E142 & _).
  pose proof (JGs_nums nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (HN & SMB & SMM & AL & IMG & TOP & ENS & EMS & R8M & R8B).
  pose proof (site2_vals nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (_ & _ & _ & EL2 & BL2 & _).
  pose proof (urange a) as Ra. cbn zeta in *. set (nv := bv_unsigned (rw rho 12%positive)) in *. set (ua := bv_unsigned a) in *.
  set (VNS := secneeded nv) in *. set (MS := secmapsize nv) in *. unfold IMG_HI in IMG.
  assert (V8 : VNS mod 8 = 0) by (rewrite ENS, Z.add_mod, R8M by lia; reflexivity).
  assert (M8 : MS mod 8 = 0).
  { pose proof (Z.div_mod MS 4096 ltac:(lia)) as X. unfold PG in SMM. rewrite SMM, Z.add_0_r in X. rewrite X. replace (4096 * (MS / 4096)) with ((512 * (MS / 4096)) * 8) by lia. apply Z_mod_mult. }
  assert (A8 : ua mod 8 = 0).
  { pose proof (Z.div_mod ua 4096 ltac:(lia)) as X. unfold PG in AL. rewrite AL, Z.add_0_r in X. rewrite X. replace (4096 * (ua / 4096)) with ((512 * (ua / 4096)) * 8) by lia. apply Z_mod_mult. }
  assert (VB : 68609 <= VNS <= nv + 4103) by (rewrite ENS; clear -R8B HN; lia).
  assert (MB : VNS + 4096 <= MS <= VNS + 8191).
  { rewrite EMS. unfold PG. pose proof (round_up_ge' VNS 4096 ltac:(lia)) as H. clear -H. lia. }
  pose proof (Z.div_mod VNS 8 ltac:(lia)) as DV. pose proof (Z.div_mod MS 8 ltac:(lia)) as DM. pose proof (Z.div_mod ua 8 ltac:(lia)) as DA.
  rewrite V8 in DV. rewrite M8 in DM. rewrite A8 in DA.
  assert (SHB : Sh ua + MS / 8 < 2 ^ 45) by (unfold Sh, SHADOW_OFF; clear -TOP DM DA Ra MB VB; lia).

  assert (ERUE : bv_unsigned (eval r (RUE nx)) = ua + 2048 + VNS).
  { unfold RUE. cbn [eval]. rewrite Enx, E12, and_val, !add_val, !u64_lit by lia. fold ua nv.
    rewrite (Z.mod_small (ua + 6144)) by (clear -Ra TOP MB VB; lia). rewrite (Z.mod_small (ua + 6144 + nv)) by (clear -Ra TOP MB VB HN; lia).
    rewrite (Z.mod_small (ua + 6144 + nv + 7)) by (clear -Ra TOP MB VB HN; lia). rewrite (land_m8E nW st tmax nx Hnx) by (clear -Ra TOP MB VB HN; lia).
    rewrite ENS. unfold round_up. replace (ua + 6144 + nv + 7) with (nv + 8 - 1 + (ua / 8 + 768) * 8) by (clear -DA; lia). rewrite Z_mod_plus_full.
    pose proof (Z.div_mod (nv + 8 - 1) 8 ltac:(lia)) as X. clear -X DA. lia. }
  assert (EA0 : bv_unsigned (eval r (a0e7 nx)) = Sh ua + VNS / 8 + 256).
  { unfold a0e7. cbn [eval]. change (eval r (RUE nx)) with (eval r (RUE nx)). rewrite add_val, srl_val. cbn [eval] in ERUE. rewrite ERUE.
    rewrite !u64_lit by lia. change (3 mod 64) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
    replace (ua + 2048 + VNS) with ((ua / 8 + 256 + VNS / 8) * 8) by (clear -DA DV; lia). rewrite Z.div_mul by lia.
    unfold Sh, SHADOW_OFF in *. rewrite Z.mod_small; clear -SHB DM DA DV MB Ra VB; lia. }
  assert (EB : bv_unsigned (eval r (BR nx)) = Sh ua + VNS / 8 + 256).
  { unfold BR, shS, vMAPn. cbn [eval]. rewrite Enx, E141.
    rewrite !add_val. rewrite !srl_val. rewrite !u64_lit by (unfold SHADOW_OFF in *; lia).
    fold ua. change (3 mod 64) with 3. rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
    unfold Sh, SHADOW_OFF in *. rewrite !Z.mod_small; clear -SHB DM DA DV MB Ra VB; lia. }
  assert (EL : bv_unsigned (eval r L3b) = MS / 8 - VNS / 8 - 256).
  { unfold L3b. cbn [eval]. rewrite add_val. cbn [eval] in EL2. rewrite EL2, u64_lit by lia. rewrite Z.mod_small by (clear -BL2; lia). lia. }
  assert (EA2 : bv_unsigned (eval r (a2e7 nx)) = MS / 8 - VNS / 8 - 256).
  { unfold a2e7. cbn [eval]. cbn [eval] in ERUE. rewrite E141, Enx.
    rewrite !sub_val, !add_val, !srl_val, !add_val, !sub_val, !add_val, and_val, add_val. rewrite ERUE.
    replace (bv_unsigned (Z_to_bv 64 (-8))) with (2 ^ 64 - 8) by reflexivity.
    rewrite !u64_lit by lia. fold ua. change (3 mod 64) with 3. rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
    rewrite (Z.mod_small (VNS + 4095)) by lia. rewrite (land_m4096E nW st tmax nx Hnx) by lia.
    assert (ERU : VNS + 4095 - (VNS + 4095) mod 4096 + 4096 = MS).
    { rewrite EMS. unfold round_up, PG. pose proof (Z.div_mod (VNS + 4096 - 1) 4096 ltac:(lia)). replace (VNS + 4095) with (VNS + 4096 - 1) by lia. lia. }
    set (RPG := VNS + 4095 - (VNS + 4095) mod 4096) in *.
    rewrite (Z.mod_small (ua + 4096)) by (clear -Ra TOP MB VB; lia).

    rewrite (Z.add_mod_idemp_l (ua + 4096 - (ua + 2048 + VNS))) by lia.
    rewrite (Z.add_mod_idemp_r (ua + 2048 + VNS)) by lia.
    replace (ua + 2048 + VNS + (ua + 4096 - (ua + 2048 + VNS) + RPG)) with (ua + MS) by (clear -ERU; lia).
    rewrite (Z.mod_small (ua + MS)) by (clear -Ra TOP MB VB; lia).
    replace ((ua + MS + (2 ^ 64 - 8)) mod 2 ^ 64) with (ua + MS - 8).
    2:{ replace (ua + MS + (2 ^ 64 - 8)) with (ua + MS - 8 + 1 * 2 ^ 64) by lia. rewrite Z_mod_plus_full. symmetry. apply Z.mod_small. clear -Ra TOP MB VB IMG. lia. }
    replace (ua + MS - 8) with ((MS / 8 + ua / 8 - 1) * 8) by (clear -DA DM; lia). rewrite Z.div_mul by lia.
    replace (ua + 2048 + VNS) with ((ua / 8 + 256 + VNS / 8) * 8) by (clear -DA DV; lia). rewrite Z.div_mul by lia.
    rewrite (Z.mod_small (MS / 8 + ua / 8 - 1 + 1)) by (clear -DA DM DV MB Ra VB TOP IMG; lia). rewrite Z.mod_small by (clear -DA DM DV MB Ra VB TOP IMG; lia). lia. }
  split; [apply bv_eq; rewrite EA0, EB; reflexivity|]. split; [apply bv_eq; rewrite EA2, EL; reflexivity|].
  split; [exact EB|]. split; [exact EL|]. split; [clear -DV VB; lia | clear -DV DM MB; lia].
Qed.

Section G44.
Variable BX : AA -> AA.
Hypothesis BXg : ltac2:(tb__ "0|0|
S2cS0S2eS2dVBX;R1A1A1S2dR1A1A3FX;").
Variable PX : list sobj.
Variable FXP : list sprop.
Hypothesis PX_noband : ltac2:(tb__ "0|2|
S2cS46S14S3eQ40A1M0S14S4G0A1S4S56A1S55VJG;VBX;R8R7R6R5R4R3R2R1A9S4cS17S1cR5A1VFXP;A3S4S15A1S0S4S8S8S16S16A2S16A2M1A1S4bS15G1S54R1A4S4bS15G1S54VPX;A4A3S4cS15S15S75S1dR9R1A2A1Lo;R2A3F_;Fl;F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;").
Variables (D6 U7 ET7 CT7 CO7 CR7 CS7 CM7 T7 : axst) (s7 : wsub) (R7 : list sobj) (n7 : nat).
Let D7 : axst := ltac2:(tb__ "0|0|
S96VT7;S1aS34VCM7;A1A1A2").
Hypothesis WU7 : ltac2:(tb__ "0|0|
S0S5S1fS34VU7;A1A1S6A3").
Hypothesis DU7 : ltac2:(tb__ "0|4|
S0SaS8S4S8S16S16A2M0A1M1S4S17A1M2A2M3A1S67S34VD6;A1S34VU7;A1A2SdG3SbG1G2S9G0A1S85Vnx;A1A4A2A3").
Hypothesis NXU7 : ltac2:(tb__ "0|0|
S0S3cS18S34VU7;A1A1S18S34VD6;A1A1A3").
Hypothesis HU7 : ltac2:(tb__ "0|0|
S0S35S36VD6;S34VU7;A1A2VU7;A3").
Hypothesis Cert7 : ltac2:(tb__ "0|1|
S0S5S68S72Ufa0S7S3bS9aS9S3bA1A3VGS;S7S35VU7;S9S35A1M0A3S7S35VET7;G0A3A6S6A3").
Hypothesis WC7 : ltac2:(tb__ "0|0|
S0S5S1fS34VCT7;A1A1S6A3").
Hypothesis DF7 : ltac2:(tb__ "0|4|
S0SaS8S4S8S16S16A2M0A1M1S4S17A1M2A2M3A1S67S34VET7;A1S34VCT7;A1A2SdG3SbG1G2S7G0SbS16S16S89Vnx;A1S6dVnx;A1A4S7G0SbS16S16S8bVnx;A1S88A4S9G0A1A3A3S9S17A1A4A2A3").
Hypothesis NX7 : ltac2:(tb__ "0|0|
S0S3cS18S34VCT7;A1A1S18S34VET7;A1A1A3").
Hypothesis HC7 : ltac2:(tb__ "0|0|
S0S35S36VET7;S34VCT7;A1A2VCT7;A3").
Hypothesis SK7 : ltac2:(tb__ "0|1|
S0S4S8S8S16S16A2S16A2M0A1S4bS15G0S54S22S34VCT7;A1A1A4S4bS15G0S54ScS15S7S15S7cVnx;A1S7S15S6bVnx;A1S7S15S6aVnx;A1S9S15A1A3A3A3ScS15S76VnW;Vnx;A2VPX;A3A3A4A3").
Hypothesis FC7 : ltac2:(tb__ "0|0|
S5bS17ScS17S4aVW;Vst;A2S49S48A1A3S1aS34VCT7;A1A1A3").
Hypothesis FX7 : ltac2:(tb__ "0|0|
S5bS17VFXP;S1aS34VCT7;A1A1A3").
Hypothesis XC7 : ax_X CT7 = [].
Hypothesis HCO7 : ltac2:(tb__ "0|0|
S0S35S6cVCT7;S28S6dVnx;A1S20Z0A1S20Z100A1S9S27A1S24A5A2VCO7;A3").
Hypothesis WCO7 : ltac2:(tb__ "0|0|
S0S5S1fS34VCO7;A1A1S6A3").

Hypothesis RB7 : ltac2:(tb__ "0|0|
S0S5Sa5S2aSb1S34VCO7;A1U1A2A2S6A3").
Hypothesis HCR7 : ltac2:(tb__ "0|0|
S0S35Sa7VCO7;U1A2VCR7;A3").
Hypothesis LEN7 : ltac2:(tb__ "0|0|
S0SeS12S15S22S34VCR7;A1A1A2Vn7;A3").
Hypothesis PERM_nd7 : ltac2:(tb__ "0|0|
S0S5SaeS82Vn7;A1A1S6A3").
Hypothesis PERM_lt7 : ltac2:(tb__ "0|0|
S0S5S5aSeSeSadR1Vn7;A2Li;S82Vn7;A1A3S6A3").
Hypothesis PERM_cov7 : ltac2:(tb__ "0|0|
S0S5S5aSeSeS5dSeSacR1A1S82Vn7;A1A3Li;S4dU0Vn7;A2A3S6A3").
Hypothesis HCS7 : ltac2:(tb__ "0|0|
S0S35S92VCR7;A1VCS7;A3").
Hypothesis MRG7 : ltac2:(tb__ "0|0|
S0S5Sa5S2aSb0S34VCS7;A1U1A2A2S6A3").
Hypothesis HCM7 : ltac2:(tb__ "0|0|
S0S35Sa6VCS7;U1A2VCM7;A3").
Hypothesis He7 : ltac2:(tb__ "0|1|
S0SaS4S15A1M0A1S98VCM7;S73Vs7;A3SdG0VR7;A2A3").
Hypothesis Hchk7 : ltac2:(tb__ "0|0|
S0S5S97VCM7;S73Vs7;VR7;S4bS37S35S38S74A4A5S6A3").
Hypothesis HT7 : ltac2:(tb__ "0|0|
S0S35S99Vs7;S73S70VCM7;VR7;A5VT7;A3").
Hypothesis FBC7 : ltac2:(tb__ "0|1|
S0S5S5aS17S1eS18S34VCM7;A1M0A1A1S1aG0A1A3S6A3").
Hypothesis FBT7 : ltac2:(tb__ "0|0|
S0S5S5aS17S1eS18S34VT7;A1A1A1S1aS34VCM7;A1A1A3S6A3").
Hypothesis NXC7 : ltac2:(tb__ "0|0|
S0S5S93VGS;S18S34VCM7;A1A1A2S6A3").

Lemma RSU7 : ltac2:(tb__ "0|1|
S2cS46S14S3eQ40A1M0S14S4G0A1S58S40Vsegs;VJG;VBX;R7R6R5R4A5VD6;R3R2R1A6S40Vsegs;VJG;VBX;R8R7R6R5A5VU7;R4R3R2A6F_;Fw;Ftp;FrhoX;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a rhoX tp w Hw. destruct w as [tr [ms md]]. rewrite <- HU7.
  eapply SPA_restate; [exact WU7 | exact DU7 | exact NXU7 | constructor | | exact Hw].
  exact (F_g7_hold BX A Kc rho a rhoX tp tr md (proj2 Hw)).
Qed.

Lemma prep7 : ltac2:(tb__ "0|4|
S2cS46S14S3eQ40M0A1M1S14S4G1A1S58S66VW;Vst;A2S3bS1S4fS5eS3dG0R6A2A1M2R1A2S50R1S4eG2S51S63S3dG0S1bR7PcA2A2A1Z8A2A2A2A2S2S0SaS3eQ8A1M3A1S23R8S3fG0R2A2A2SfG3A1A3A1F_;Fz;S40Vsegs;VJG;VBX;R9R8R7R6A5VET7;R5R4R3A6S40Vsegs;VJG;VBX;RaR9R8R7A5VCM7;R6R5R4A6F_;F_;F_;Fw;Ftp;FrhoX;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a rhoX tp w HW RUNDEF Hw. destruct w as [tr [ms md]].
  pose proof (proj2 Hw) as HJ. cbn [w_tr w_cfg cfg_model fst snd] in HJ.
  destruct (site7_vals BX A Kc rho a rhoX tp tr md HJ) as (EA0 & EA2 & EB & EL & V512 & VM). cbn zeta in EB, EL, V512, VM.
  destruct (site3_vals BX A Kc rho a rhoX tp tr md HJ) as (EB3 & _ & EL3).
  destruct (site2_vals nW st tmax nx Hnx BX A Kc rho a rhoX tp tr md HJ) as (_ & EB2 & _ & EL2 & BL2 & _). cbn zeta in EB2, EL2, BL2.
  destruct (site1_bounds nW st tmax nx Hnx BX A Kc rho a rhoX tp tr md HJ) as (EB1 & EL1 & BB1).

  assert (HC : SPA segs (JG BX A Kc rho a) CT7 rhoX tp (tr, mkCfg ms md)).
  { rewrite <- HC7. eapply SPA_restate; [exact WC7 | exact DF7 | exact NX7 | | constructor | exact Hw].
    unfold diffs_ok. apply Forall_cons; [exact EA0|]. apply Forall_cons; [exact EA2 | apply Forall_nil]. }
  pose proof (SPA_facts_hold segs _ rhoX CT7 tp _ HC) as HF.

  assert (SL : slink (bv_unsigned a) (secmapsize (bv_unsigned (rw rho 12%positive))) rho rho).
  { split; [intros i; reflexivity|]. split; [intros l; reflexivity|]. split; [intros x; left; reflexivity | exact RUNDEF]. }
  assert (E256 : bv_unsigned (eval rhoX (SLit 256)) = 256) by (cbn [eval]; apply u64_lit; lia).
  assert (HCO : SPA segs (JG BX A Kc rho a) CO7 rhoX tp (tr, mkCfg ms md)).
  { rewrite <- HCO7. apply (carve_piece nW st tmax nx Hnx BX CT7 (BR nx) (SLit 256) A Kc rho rho a rhoX tp _ SL HC); [rewrite HCO7; exact WCO7 | exact XC7 | | |].
    - rewrite EB. clear -V512. lia.
    - rewrite EB, E256. clear -VM. lia.
    - rewrite EB, E256. pose proof (run_band BX A Kc rho a rhoX tp tr md HJ) as RB.
      apply (pieces_disjoint nW st tmax nx Hnx BX BXg CT7 [O_3 nx; O_2 nx; O_1 nx] PX A Kc rho a rhoX tp _ _ _ HW HC SK7 FC7).
      + apply (RB (Sh (bv_unsigned a) + secneeded (bv_unsigned (rw rho 12%positive)) / 8 + 256)). clear -V512 VM. lia.
      + pose proof (RB (Sh (bv_unsigned a) + secneeded (bv_unsigned (rw rho 12%positive)) / 8 + 256 + 256 - 1) ltac:(clear -V512 VM; lia)). lia.
      + intros l2 EE. destruct l2 as [|o [|o' [|o'' [|o3 l2']]]]; try (cbn in EE; discriminate EE).
        assert (Es : skel o = skel (O_3 nx)) by (cbn in EE; congruence). assert (Es' : skel o' = skel (O_2 nx)) by (cbn in EE; congruence).
        assert (Es'' : skel o'' = skel (O_1 nx)) by (cbn in EE; congruence).
        apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
        * rewrite (obj_range_skel rhoX o (O_3 nx) Es). unfold O_3, L3. rewrite obj_range_mk by lia. rewrite EB3.
          unfold ranges_disjoint. cbn [fst snd]. right. right. left. clear -V512. lia.
        * rewrite (obj_range_skel rhoX o' (O_2 nx) Es'). unfold O_2, obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi fst snd].
          rewrite soff_lit_small by lia. rewrite (soff_of_val rhoX L2 _ EL2) by (clear -BL2; lia). rewrite EB2.
          unfold ranges_disjoint. cbn [fst snd]. right. right. right. lia.
        * rewrite (obj_range_skel rhoX o'' (O_1 nx) Es''). unfold O_1, L1. rewrite obj_range_mk by lia. rewrite EB1.
          unfold ranges_disjoint. cbn [fst snd]. right. right. left. clear -V512. lia.
      + intros l2 EE.
        assert (HFX : Forall (holds rhoX) FXP) by (apply Forall_forall; intros p Hp; exact (proj1 (Forall_forall _ _) HF p (FX7 p Hp))).
        pose proof (PX_noband A Kc rho a rhoX tp tr md HJ HFX l2 EE) as NB.
        eapply Forall_impl; [|exact NB]. intros o Ho. cbn beta in Ho. unfold ranges_disjoint. cbn [fst snd].
        set (lo := Sh (bv_unsigned a) + secneeded (bv_unsigned (rw rho 12%positive)) / 8 + 256) in *.
        destruct (Z_lt_le_dec (fst (obj_range rhoX o)) (snd (obj_range rhoX o))) as [NE|]; [|left; lia].
        destruct (Z_le_gt_dec (snd (obj_range rhoX o)) lo) as [|G1]; [right; right; left; lia|].
        destruct (Z_le_gt_dec (lo + 256) (fst (obj_range rhoX o))) as [|G2]; [right; right; right; lia|].
        exfalso. set (x := Z.max (fst (obj_range rhoX o)) lo).
        pose proof (Ho x ltac:(unfold x; lia)) as NBx. pose proof (RB x ltac:(unfold x, lo in *; clear -V512 VM G1 G2 NE; lia)) as Bx.
        unfold noband in NBx. clear -NBx Bx. lia. }

  assert (XCO : ax_X CO7 = []) by (rewrite <- HCO7; exact XC7).
  assert (HCR : SPA segs (JG BX A Kc rho a) CR7 rhoX tp (tr, mkCfg ms md)).
  { rewrite <- HCR7. unfold oreb. destruct (rebase_obj_at (ax_S CO7) 1) as [S'|] eqn:E; [|exact HCO]. eapply (SPA_rebase segs); [exact E | exact XCO | exact HCO]. }
  assert (HCS : SPA segs (JG BX A Kc rho a) CS7 rhoX tp (tr, mkCfg ms md)).
  { rewrite <- HCS7. unfold sel7. rewrite LEN7. apply (SPA_select segs); [exact HCR | exact PERM_nd7 | |].
    - intros i Hi. rewrite LEN7. apply Nat.ltb_lt. exact (proj1 (forallb_forall _ _) PERM_lt7 i Hi).
    - intros i Hi. rewrite LEN7 in Hi. pose proof (proj1 (forallb_forall _ _) PERM_cov7 i ltac:(apply in_seq; lia)) as X.
      apply existsb_exists in X as (j & Hj & E). apply Nat.eqb_eq in E. subst j. exact Hj. }
  rewrite <- HCM7. unfold omrg. destruct (merge_objs_at (ax_S CS7) 1) as [S'|] eqn:E; [|exact HCS]. eapply (SPA_merge segs); [exact E | exact HCS].
Qed.

Theorem sec_g44 : ltac2:(tb__ "0|5|
S58OF_;S2cS46S14S3eQ40M0A1M1S59S66VW;Vst;A2S64VW;Vst;A2S47R6A1S42Vsegs;R9S41R7A1A3S3bS1S4fS5eS3dG0R7A2A1M2R1A2S50R1S4eG2S51S63S3dG0S1bR8PcA2A2A1Z8A2A2A2A2S2S0SaS3eQ8A1M3A1S23R9S3fG0R2A2A2SfG3A1A3A1F_;Fz;S14S4G1A1M4S57Vsegs;RdS40Vsegs;VJG;VBX;RcRbRaR9A5VD7;R2R1A5R8A4FtpY;FrhoY;S14G4S57Vsegs;ReS40Vsegs;VJG;VBX;RdRcRbRaA5VD6;R2R1A5R9A4FtX;FrX;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho a Q HW HUS HKc Hokl RUNDEF HCONT rX tX.
  pose proof (JG_okf nW st nx BX ok A Kc rho a Hokl) as Hokf. pose proof (JG_stable nW st tmax nx Hnx NXG BX A Kc rho a HUS HKc) as HST.
  eapply triple_conseq; [intros w Hw; exact (RSU7 A Kc rho a rX tX w Hw) | intros w Hw; exact Hw |].
  apply (cfg_soundA segs 4000%nat [MSENT] GS [U7] [ET7] (JG BX A Kc rho a) ok Q tX Hokf HST Cert7); [|left; reflexivity].
  intros E rE HinE. destruct HinE as [<-|[]].
  eapply triple_conseq; [intros w Hw; exact (prep7 A Kc rho a rE tX w HW RUNDEF Hw) | intros w Hw; right; exact Hw |].
  exact (ms_call BX CM7 T7 Pre_memsetA Pret_ms Posts_memsetA s7 R7 eq_refl (fun ok0 Jx r0 t0 Ho Hs => memset_sumA ok0 Jx r0 t0 Ho Hs) eq_refl
           He7 Hchk7 HT7 FBC7 FBT7 NXC7 ok A Kc rho a tX Q HUS HKc Hokl HCONT rE).
Qed.
End G44.

Lemma site8_vals : ltac2:(tb__ "0|5|
S2cS2cF_;S2cS46S14S3eQ40M0A1M1S14S4G1A1S4S56A1S55VJG;R9R8R7R6R5R4R3R2R1A9S3dG0S1bR7PcM2A2A2S3bS3dG0R7A2S3bS1S0S3bS3dG0S19R7S7eVnx;A1A2A2S4eS5eR1A1Z300A2A3S1S0S3bS3dG0S19R7S81Vnx;A1A2A2S51R2Z8M3A2A3S1S0S3bS3dG0S19R7S2bS95S21G2A1S20S9bA1A3A2A2S52R2S53R2G3A2A2M4A3S0S3bS3dG0S19R7S8dVnx;A1A2A2S52S4eS4eR1Z1800A2G4A2G3A2A3A2A2A2Tua;Tnv;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FBX;").
Proof.
  intros BX A Kc rho a r tp tr md HJ.
  pose proof (JGs_rigidS nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (E12 & Enx & _).
  pose proof (JGs_nums nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (HN & SMB & SMM & AL & IMG & TOP & ENS & EMS & R8M & R8B).
  pose proof (urange a) as Ra. cbn zeta in *. set (nv := bv_unsigned (rw rho 12%positive)) in *. set (ua := bv_unsigned a) in *. unfold IMG_HI in IMG.
  assert (A8 : ua mod 8 = 0).
  { pose proof (Z.div_mod ua 4096 ltac:(lia)) as X. unfold PG in AL. rewrite AL, Z.add_0_r in X. rewrite X. replace (4096 * (ua / 4096)) with ((512 * (ua / 4096)) * 8) by lia. apply Z_mod_mult. }
  pose proof (Z.div_mod ua 8 ltac:(lia)) as DA. rewrite A8, Z.add_0_r in DA.
  pose proof (Z.div_mod nv 8 ltac:(lia)) as DN. pose proof (Z.mod_pos_bound nv 8 ltac:(lia)) as MN.
  assert (EN8 : bv_unsigned (eval r (SAlu ALU_AND (SVar 12) (SLit M48))) = nv - nv mod 8).
  { cbn [eval]. rewrite and_val, E12, !u64_lit by (unfold M48; lia). fold nv. apply land_M48. clear -HN. lia. }
  assert (EE : bv_unsigned (eval r (END8 nx)) = ua + 6144 + (nv - nv mod 8) - 8).
  { unfold END8. cbn [eval] in EN8 |- *. rewrite add_val, add_val, EN8, add_val, Enx, !u64_lit by lia. fold ua.
    replace (bv_unsigned (Z_to_bv 64 (-8))) with (2 ^ 64 - 8) by reflexivity.
    rewrite (Z.mod_small (ua + 6144)) by (clear -Ra TOP SMB; lia). rewrite (Z.mod_small (ua + 6144 + (nv - nv mod 8))) by (clear -Ra TOP SMB HN MN; lia).
    replace (ua + 6144 + (nv - nv mod 8) + (2 ^ 64 - 8)) with (ua + 6144 + (nv - nv mod 8) - 8 + 1 * 2 ^ 64) by lia. rewrite Z_mod_plus_full.
    apply Z.mod_small. clear -Ra TOP SMB HN MN IMG. lia. }
  assert (D1 : (ua + 6144) / 8 = ua / 8 + 768) by (replace (ua + 6144) with (ua + 768 * 8) by lia; rewrite Z.div_add by lia; reflexivity).
  pose proof (Z.div_pos ua 8 ltac:(lia) ltac:(lia)) as DP. pose proof (Z.div_lt_upper_bound ua 8 (2 ^ 61) ltac:(lia) ltac:(lia)) as DU.
  split; [|split; [|split; [exact EN8 | exact EE]]].
  - unfold B4. cbn [eval]. rewrite Enx, add_val, srl_val, add_val, !u64_lit by lia. fold ua. change (3 mod 64) with 3.
    rewrite (Z.mod_small (ua + 6144)) by (clear -Ra TOP SMB; lia). rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. rewrite D1.
    unfold Sh, SHADOW_OFF. rewrite Z.mod_small by (clear -DP DU; lia). lia.
  - unfold a2e8. cbn [eval]. cbn [eval] in EE. rewrite sub_val, add_val, !srl_val, EE, add_val, Enx, !u64_lit by lia. fold ua. change (3 mod 64) with 3.
    rewrite (Z.mod_small (ua + 6144)) by (clear -Ra TOP SMB; lia). rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. rewrite D1.
    replace (ua + 6144 + (nv - nv mod 8) - 8) with ((ua / 8 + 767 + nv / 8) * 8) by (clear -DA DN; lia). rewrite Z.div_mul by lia.
    pose proof (Z.div_pos nv 8 ltac:(lia) ltac:(lia)) as NP. pose proof (Z.div_lt_upper_bound nv 8 (2 ^ 36) ltac:(lia) ltac:(clear -HN; lia)) as NU.
    rewrite (Z.mod_small (ua / 8 + 767 + nv / 8 + 1)) by (clear -DP DU NP NU; lia).
    replace (ua / 8 + 767 + nv / 8 + 1 - (ua / 8 + 768)) with (nv / 8) by lia. apply Z.mod_small. clear -NP NU. lia.
Qed.

Lemma F_g8_hold : ltac2:(tb__ "0|1|
S2cS2cF_;S2cS46S14S3eQ40A1M0S14S4G0A1S4S56A1S55VJG;R9R8R7R6R5R4R3R2R1A9S4cS17S1cR5A1S86Vnx;A1A3F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FBX;").
Proof.
  intros BX A Kc rho a r tp tr md HJ.
  destruct (site8_vals BX A Kc rho a r tp tr md HJ) as (_ & EL & EN8 & EE). cbn zeta in EL, EN8, EE.
  pose proof (JGs_nums nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (HN & SMB & _ & _ & IMG & TOP & ENS & EMS & _). cbn zeta in *.
  pose proof (urange a) as Ra. set (nv := bv_unsigned (rw rho 12%positive)) in *. set (ua := bv_unsigned a) in *. unfold IMG_HI in IMG.
  assert (LB : nv + 6151 <= secmapsize nv).
  { rewrite EMS, ENS. pose proof (round_up_ge' (round_up nv 8 + 4096) PG ltac:(unfold PG; lia)). pose proof (round_up_ge' nv 8 ltac:(lia)). unfold PG in *. lia. }
  pose proof (Z.mod_pos_bound nv 8 ltac:(lia)) as MN.
  pose proof (Z.div_pos nv 8 ltac:(lia) ltac:(lia)) as NP. pose proof (Z.div_lt_upper_bound nv 8 (2 ^ 36) ltac:(lia) ltac:(clear -HN; lia)) as NU.
  unfold F_g8. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
  - cbn [holds branch_taken]. unfold bv_ltu. apply Z.ltb_lt. rewrite EL. cbn [eval]. rewrite u64_lit by lia. clear -NP NU. lia.
  - cbn [holds branch_taken]. intros H. unfold bv_ltu in H. apply Z.ltb_lt in H. rewrite EE in H. cbn [eval] in H. rewrite u64_lit in H by lia. clear -H Ra TOP SMB HN MN LB. lia.
  - cbn [holds branch_taken]. intros H. unfold bv_eqb in H. apply Z.eqb_eq in H. rewrite EN8 in H. cbn [eval] in H. rewrite u64_lit in H by lia. clear -H HN MN. lia.
Qed.

Section G45.
Variable BX : AA -> AA.
Hypothesis BXg : ltac2:(tb__ "0|0|
S2cS0S2eS2dVBX;R1A1A1S2dR1A1A3FX;").
Variable PX : list sobj.
Variable FXP : list sprop.
Hypothesis PX_noband : ltac2:(tb__ "0|2|
S2cS46S14S3eQ40A1M0S14S4G0A1S4S56A1S55VJG;VBX;R8R7R6R5R4R3R2R1A9S4cS17S1cR5A1VFXP;A3S4S15A1S0S4S8S8S16S16A2S16A2M1A1S4bS15G1S54R1A4S4bS15G1S54VPX;A4A3S4cS15S15S75S1dR9R1A2A1Lo;R2A3F_;Fl;F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;").
Variables (D7 U8 ET8 CT8 CO8 T8 : axst) (s8 : wsub) (R8 : list sobj).
Let D8 : axst := ltac2:(tb__ "0|0|
S96VT8;S1aS34VCO8;A1A1A2").
Hypothesis WU8 : ltac2:(tb__ "0|0|
S0S5S1fS34VU8;A1A1S6A3").
Hypothesis DU8 : ltac2:(tb__ "0|4|
S0SaS8S4S8S16S16A2M0A1M1S4S17A1M2A2M3A1S67S34VD7;A1S34VU8;A1A2SdG3SbG1G2S9G0A1S86Vnx;A1A4A2A3").
Hypothesis NXU8 : ltac2:(tb__ "0|0|
S0S3cS18S34VU8;A1A1S18S34VD7;A1A1A3").
Hypothesis HU8 : ltac2:(tb__ "0|0|
S0S35S36VD7;S34VU8;A1A2VU8;A3").
Hypothesis Cert8 : ltac2:(tb__ "0|1|
S0S5S68S72Ufa0S7S3bS9aS9S3bA1A3VGS;S7S35VU8;S9S35A1M0A3S7S35VET8;G0A3A6S6A3").
Hypothesis WC8 : ltac2:(tb__ "0|0|
S0S5S1fS34VCT8;A1A1S6A3").
Hypothesis DF8 : ltac2:(tb__ "0|4|
S0SaS8S4S8S16S16A2M0A1M1S4S17A1M2A2M3A1S67S34VET8;A1S34VCT8;A1A2SdG3SbG1G2S9G0A1S91Vnx;A1A4A2A3").
Hypothesis NX8 : ltac2:(tb__ "0|0|
S0S3cS18S34VCT8;A1A1S18S34VET8;A1A1A3").
Hypothesis HC8 : ltac2:(tb__ "0|0|
S0S35S36VET8;S34VCT8;A1A2VCT8;A3").
Hypothesis SK8 : ltac2:(tb__ "0|1|
S0S4S8S8S16S16A2S16A2M0A1S4bS15G0S54S22S34VCT8;A1A1A4S4bS15G0S54ScS15S7S15S80Vnx;A1S7S15S7cVnx;A1S7S15S6aVnx;A1S9S15A1A3A3A3ScS15S76VnW;Vnx;A2VPX;A3A3A4A3").
Hypothesis FC8 : ltac2:(tb__ "0|0|
S5bS17ScS17S4aVW;Vst;A2S49S48A1A3S1aS34VCT8;A1A1A3").
Hypothesis FX8 : ltac2:(tb__ "0|0|
S5bS17VFXP;S1aS34VCT8;A1A1A3").
Hypothesis XC8 : ax_X CT8 = [].
Hypothesis HCO8 : ltac2:(tb__ "0|0|
S0S35S6cVCT8;S28S7eVnx;A1S20Z0A1S81Vnx;A1S9S27A1S24A5A2VCO8;A3").
Hypothesis WCO8 : ltac2:(tb__ "0|0|
S0S5S1fS34VCO8;A1A1S6A3").
Hypothesis He8 : ltac2:(tb__ "0|1|
S0SaS4S15A1M0A1S98VCO8;S9fVs8;A3SdG0VR8;A2A3").
Hypothesis Hchk8 : ltac2:(tb__ "0|0|
S0S5S97VCO8;S9fVs8;VR8;S4bS37S35S38Sa0A4A5S6A3").
Hypothesis HT8 : ltac2:(tb__ "0|0|
S0S35S99Vs8;S9fS71VCO8;VR8;A5VT8;A3").
Hypothesis FBC8 : ltac2:(tb__ "0|1|
S0S5S5aS17S1eS18S34VCO8;A1M0A1A1S1aG0A1A3S6A3").
Hypothesis FBT8 : ltac2:(tb__ "0|0|
S0S5S5aS17S1eS18S34VT8;A1A1A1S1aS34VCO8;A1A1A3S6A3").
Hypothesis NXC8 : ltac2:(tb__ "0|0|
S0S5S93VGS;S18S34VCO8;A1A1A2S6A3").

Lemma RSU8 : ltac2:(tb__ "0|1|
S2cS46S14S3eQ40A1M0S14S4G0A1S58S40Vsegs;VJG;VBX;R7R6R5R4A5VD7;R3R2R1A6S40Vsegs;VJG;VBX;R8R7R6R5A5VU8;R4R3R2A6F_;Fw;Ftp;FrhoX;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a rhoX tp w Hw. destruct w as [tr [ms md]]. rewrite <- HU8.
  eapply SPA_restate; [exact WU8 | exact DU8 | exact NXU8 | constructor | | exact Hw].
  exact (F_g8_hold BX A Kc rho a rhoX tp tr md (proj2 Hw)).
Qed.

Lemma RS8 : ltac2:(tb__ "0|1|
S2cS46S14S3eQ40A1M0S14S4G0A1S58S66VW;Vst;A2S40Vsegs;VJG;VBX;R8R7R6R5A5VET8;R4R3R2A6S40Vsegs;VJG;VBX;R9R8R7R6A5VCT8;R5R4R3A6F_;F_;Fw;Ftp;FrhoX;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a rhoX tp w HW Hw. destruct w as [tr [ms md]]. rewrite <- HC8.
  eapply SPA_restate; [exact WC8 | exact DF8 | exact NX8 | constructor | | exact Hw].
  destruct (site8_vals BX A Kc rho a rhoX tp tr md (proj2 Hw)) as (_ & EL & _). cbn zeta in EL.
  pose proof (JGs_nums nW st tmax nx Hnx BX A Kc rho a rhoX tp tr md (proj2 Hw)) as (HN & _). cbn zeta in HN.
  unfold fx8. apply Forall_cons; [|apply Forall_nil]. cbn [holds]. rewrite EL. cbn [eval]. rewrite u64_lit by lia.
  pose proof (Z.div_lt_upper_bound (bv_unsigned (rw rho 12%positive)) 8 (2 ^ 36) ltac:(lia) ltac:(clear -HN; lia)) as NU. clear -NU. lia.
Qed.

Lemma HBL8 : ltac2:(tb__ "0|c|
S2cS46S14S3eQ40M0A1M1S14S4G1A1S58S40Vsegs;VJG;VBX;R7R6R5R4A5VCT8;R3R2R1A6S1S4fS5eS3dG0R5A2A1M2S3dG0S19R4S7eVnx;A1M3A2A2M4A2S1S4fS4eG4S3dG0S19R4S81Vnx;A1M5A2A2A2S4eG2S51S63S3dG0S1bR6PcA2A2A1Z8A2A2A2S1S4S15A1M6S0S4S8S8S16S16A2S16A2M7A1M8S4bS15G7S54R1A4M9S4bS15G7S54S7S15S80Vnx;A1S7S15S7cVnx;A1S7S15S6aVnx;A1S9S15A1A3A3A3A4A3S4cS15S15S29S1dR7R1A2SbS3bS3bS3dG0S19R7G3A2A2MaS4eGaS3dG0S19R7G5A2A2A2A4A2Lo;R2A3MbF_;Fl;G6S0G8G9S4bS15G7S54VPX;A4A3GbF_;Fl;A2A2A2F_;Fw;Ftp;FrhoX;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a rhoX tp w Hw. pose proof (SPA_facts_hold segs _ rhoX CT8 tp w Hw) as HF. destruct w as [tr [ms md]].
  pose proof (proj2 Hw) as HJ. cbn [w_tr w_cfg cfg_model fst snd] in HJ.
  destruct (site8_vals BX A Kc rho a rhoX tp tr md HJ) as (EB & EL & _). cbn zeta in EB, EL. rewrite EB, EL.
  destruct (site7_vals BX A Kc rho a rhoX tp tr md HJ) as (_ & _ & EBR & EL3b & V512 & VM). cbn zeta in EBR, EL3b, V512, VM.
  destruct (site3_vals BX A Kc rho a rhoX tp tr md HJ) as (EB3 & _ & EL3).
  destruct (site1_bounds nW st tmax nx Hnx BX A Kc rho a rhoX tp tr md HJ) as (EB1 & EL1 & BB1).
  pose proof (JGs_nums nW st tmax nx Hnx BX A Kc rho a rhoX tp tr md HJ) as (HN & SMB & SMM & AL & IMG & TOP & ENS & EMS & R8M & R8B). cbn zeta in *.
  set (nv := bv_unsigned (rw rho 12%positive)) in *.

  assert (NV8 : nv / 8 <= secneeded nv / 8 - 512).
  { rewrite ENS. replace (round_up nv 8 + 4096) with (round_up nv 8 + 512 * 8) by lia. rewrite Z.div_add by lia.
    pose proof (Z.div_le_mono nv (round_up nv 8) 8 ltac:(lia) ltac:(clear -R8B; lia)). lia. }
  pose proof (Z.div_pos nv 8 ltac:(lia) ltac:(lia)) as NP.
  split; [lia|]. split; [clear -NV8 VM; lia|]. split.
  - intros l2 EE. destruct l2 as [|o [|o' [|o'' [|o3 l2']]]]; try (cbn in EE; discriminate EE).
    assert (Es : skel o = skel (O_3b nx)) by (cbn in EE; congruence). assert (Es' : skel o' = skel (O_3 nx)) by (cbn in EE; congruence).
    assert (Es'' : skel o'' = skel (O_1 nx)) by (cbn in EE; congruence).
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
    + rewrite (obj_range_skel rhoX o (O_3b nx) Es). unfold O_3b, obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi fst snd].
      rewrite soff_lit_small by lia. rewrite EBR. unfold ranges_disjoint. cbn [fst snd]. right. right. right. clear -NV8. lia.
    + rewrite (obj_range_skel rhoX o' (O_3 nx) Es'). unfold O_3, L3. rewrite obj_range_mk by lia. rewrite EB3.
      unfold ranges_disjoint. cbn [fst snd]. right. right. left. lia.
    + rewrite (obj_range_skel rhoX o'' (O_1 nx) Es''). unfold O_1, L1. rewrite obj_range_mk by lia. rewrite EB1.
      unfold ranges_disjoint. cbn [fst snd]. right. right. left. lia.
  - intros l2 EE. pose proof (run_band BX A Kc rho a rhoX tp tr md HJ) as RB.
    assert (HFX : Forall (holds rhoX) FXP) by (apply Forall_forall; intros p Hp; exact (proj1 (Forall_forall _ _) HF p (FX8 p Hp))).
    pose proof (PX_noband A Kc rho a rhoX tp tr md HJ HFX l2 EE) as NB.
    eapply Forall_impl; [|exact NB]. intros o Ho. cbn beta in Ho. unfold ranges_disjoint. cbn [fst snd].
    set (lo := Sh (bv_unsigned a) + 768) in *.
    destruct (Z_lt_le_dec (fst (obj_range rhoX o)) (snd (obj_range rhoX o))) as [NE|]; [|left; lia].
    destruct (Z_le_gt_dec (snd (obj_range rhoX o)) lo) as [|G1]; [right; right; left; lia|].
    destruct (Z_le_gt_dec (lo + nv / 8) (fst (obj_range rhoX o))) as [|G2]; [right; right; right; lia|].
    exfalso. set (x := Z.max (fst (obj_range rhoX o)) lo).
    pose proof (Ho x ltac:(unfold x; lia)) as NBx. pose proof (RB x ltac:(unfold x, lo in *; fold nv; clear -NV8 VM G1 G2 NE NP; lia)) as Bx.
    unfold noband in NBx. clear -NBx Bx. lia.
Qed.

Theorem sec_g45 : ltac2:(tb__ "0|5|
S58OF_;S2cS46S14S3eQ40M0A1M1S59S66VW;Vst;A2S64VW;Vst;A2S47R6A1S42Vsegs;R9S41R7A1A3S3bS1S4fS5eS3dG0R7A2A1M2R1A2S50R1S4eG2S51S63S3dG0S1bR8PcA2A2A1Z8A2A2A2A2S2S0SaS3eQ8A1M3A1S23R9S3fG0R2A2A2SfG3A1A3A1F_;Fz;S14S4G1A1M4S57Vsegs;RdS40Vsegs;VJG;VBX;RcRbRaR9A5VD8;R2R1A5R8A4FtpY;FrhoY;S14G4S57Vsegs;ReS40Vsegs;VJG;VBX;RdRcRbRaA5VD7;R2R1A5R9A4FtX;FrX;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho a Q HW HUS HKc Hokl RUNDEF HCONT rX tX.
  pose proof (JG_okf nW st nx BX ok A Kc rho a Hokl) as Hokf. pose proof (JG_stable nW st tmax nx Hnx NXG BX A Kc rho a HUS HKc) as HST.
  assert (SL : slink (bv_unsigned a) (secmapsize (bv_unsigned (rw rho 12%positive))) rho rho).
  { split; [intros i; reflexivity|]. split; [intros l; reflexivity|]. split; [intros x; left; reflexivity | exact RUNDEF]. }
  eapply triple_conseq; [intros w Hw; exact (RSU8 A Kc rho a rX tX w Hw) | intros w Hw; exact Hw |].
  apply (cfg_soundA segs 4000%nat [MSENT] GS [U8] [ET8] (JG BX A Kc rho a) ok Q tX Hokf HST Cert8); [|left; reflexivity].
  intros E rE HinE. destruct HinE as [<-|[]].
  eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw |].
  apply (ms_step nW st tmax nx Hnx NXG BX BXg ET8 CT8 CO8 T8 (B4 nx) (a2e8 nx) [O_3b nx; O_3 nx; O_1 nx] PX Pre_mszA Pret_mz Posts_mszA s8 R8 eq_refl
           (fun ok0 Jx r0 t0 Ho Hs => memsetZ_sumA ok0 Jx Ho Hs r0 t0) eq_refl RS8 HBL8 SK8 FC8 XC8 HCO8 WCO8 He8 Hchk8 HT8 FBC8 FBT8 NXC8
           ok A Kc rho rho a tX Q HW HUS HKc Hokl SL).
  intros rhoY tpY. exact (HCONT rhoY tpY).
Qed.
End G45.

Lemma site9_vals : ltac2:(tb__ "0|3|
S2cS2cF_;S2cS46S14S3eQ40M0A1M1S14S4G1A1S4S56A1S55VJG;R9R8R7R6R5R4R3R2R1A9S3dG0S1bR7PcA2A2S3bS3dG0R7A2S3bS1S0S3bS3dG0S19R7S90Vnx;A1A2A2S4eS4eR1Z1800A2S52R2S53R2Z8M2A2A2A2A3S0S3bS3dG0S19R7S83Vnx;A1A2A2S4eS4eS5eR1A1Z300A2S51R2G2A2A2A3A2Tua;Tnv;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FBX;").
Proof.
  intros BX A Kc rho a r tp tr md HJ.
  destruct (site8_vals BX A Kc rho a r tp tr md HJ) as (_ & _ & EN8 & _). cbn zeta in EN8.
  pose proof (JGs_rigidS nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (E12 & Enx & _).
  pose proof (JGs_nums nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (HN & SMB & SMM & AL & IMG & TOP & ENS & EMS & R8M & R8B).
  pose proof (urange a) as Ra. cbn zeta in *. set (nv := bv_unsigned (rw rho 12%positive)) in *. set (ua := bv_unsigned a) in *. unfold IMG_HI in IMG.
  assert (LB : nv + 6151 <= secmapsize nv).
  { rewrite EMS, ENS. pose proof (round_up_ge' (round_up nv 8 + 4096) PG ltac:(unfold PG; lia)). pose proof (round_up_ge' nv 8 ltac:(lia)). unfold PG in *. lia. }
  assert (A8 : ua mod 8 = 0).
  { pose proof (Z.div_mod ua 4096 ltac:(lia)) as X. unfold PG in AL. rewrite AL, Z.add_0_r in X. rewrite X. replace (4096 * (ua / 4096)) with ((512 * (ua / 4096)) * 8) by lia. apply Z_mod_mult. }
  pose proof (Z.div_mod ua 8 ltac:(lia)) as DA. rewrite A8, Z.add_0_r in DA.
  pose proof (Z.div_mod nv 8 ltac:(lia)) as DN. pose proof (Z.mod_pos_bound nv 8 ltac:(lia)) as MN.
  assert (EU : bv_unsigned (eval r (UE9 nx)) = ua + 6144 + (nv - nv mod 8)).
  { unfold UE9. cbn [eval] in EN8 |- *. rewrite add_val, EN8, add_val, Enx, !u64_lit by lia. fold ua.
    rewrite (Z.mod_small (ua + 6144)) by (clear -Ra TOP SMB; lia). apply Z.mod_small. clear -Ra TOP SMB HN MN LB. lia. }
  split; [exact EU|].
  unfold BP9. cbn [eval]. cbn [eval] in EU. rewrite add_val, srl_val, EU, !u64_lit by lia. change (3 mod 64) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  replace (ua + 6144 + (nv - nv mod 8)) with ((ua / 8 + 768 + nv / 8) * 8) by (clear -DA DN; lia). rewrite Z.div_mul by lia.
  pose proof (Z.div_pos ua 8 ltac:(lia) ltac:(lia)) as DP. pose proof (Z.div_lt_upper_bound ua 8 (2 ^ 61) ltac:(lia) ltac:(lia)) as DU.
  pose proof (Z.div_pos nv 8 ltac:(lia) ltac:(lia)) as NP. pose proof (Z.div_lt_upper_bound nv 8 (2 ^ 36) ltac:(lia) ltac:(clear -HN; lia)) as NU.
  unfold Sh, SHADOW_OFF. rewrite Z.mod_small by (clear -DP DU NP NU; lia). lia.
Qed.

Lemma F_g9_hold : ltac2:(tb__ "0|1|
S2cS2cF_;S2cS46S14S3eQ40A1M0S14S4G0A1S4S56A1S55VJG;R9R8R7R6R5R4R3R2R1A9S4cS17S1cR5A1S87Vnx;A1A3F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FBX;").
Proof.
  intros BX A Kc rho a r tp tr md HJ.
  destruct (site9_vals BX A Kc rho a r tp tr md HJ) as (EU & _). cbn zeta in EU.
  pose proof (JGs_nums nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (HN & SMB & _ & _ & IMG & TOP & ENS & EMS & _). cbn zeta in *.
  pose proof (urange a) as Ra. set (nv := bv_unsigned (rw rho 12%positive)) in *. set (ua := bv_unsigned a) in *.
  assert (LB : nv + 6151 <= secmapsize nv).
  { rewrite EMS, ENS. pose proof (round_up_ge' (round_up nv 8 + 4096) PG ltac:(unfold PG; lia)). pose proof (round_up_ge' nv 8 ltac:(lia)). unfold PG in *. lia. }
  pose proof (Z.mod_pos_bound nv 8 ltac:(lia)) as MN.
  unfold F_g9. apply Forall_cons; [|apply Forall_nil]. cbn [holds branch_taken]. intros H. unfold bv_ltu in H. apply Z.ltb_lt in H.
  rewrite EU in H. cbn [eval] in H. rewrite u64_lit in H by lia. clear -H Ra TOP SMB HN MN LB. lia.
Qed.

Lemma nmod8_of_par : ltac2:(tb__ "0|3|
S2cS2cF_;S2cS46S14S3eQ40M0A1M1S14S4G1A1S4S56A1S55VJG;R9R8R7R6R5R4R3R2R1A9S1S1cR5S7fA2S0S3bS53S3dG0S1bR8PcA2A2Z8A2Z0A3M2F_;S1cR5S26S7fA1A2S2G2A1F_;A2F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FBX;").
Proof.
  intros BX A Kc rho a r tp tr md HJ.
  destruct (site8_vals BX A Kc rho a r tp tr md HJ) as (_ & _ & EN8 & _). cbn zeta in EN8.
  pose proof (JGs_rigidS nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (E12 & _).
  assert (EQ : branch_taken BC_EQ (eval r (SVar 12)) (eval r (SAlu ALU_AND (SVar 12) (SLit M48))) = (bv_unsigned (rw rho 12%positive) mod 8 =? 0)).
  { cbn [branch_taken]. unfold bv_eqb. rewrite EN8. cbn [eval]. rewrite E12.
    pose proof (Z.mod_pos_bound (bv_unsigned (rw rho 12%positive)) 8 ltac:(lia)) as MN.
    destruct (Z.eqb_spec (bv_unsigned (rw rho 12%positive) mod 8) 0) as [E|NE]; [apply Z.eqb_eq; lia | apply Z.eqb_neq; lia]. }
  unfold F_par. cbn [holds]. rewrite EQ. split.
  - intros H. apply Z.eqb_eq in H. exact H.
  - intros H E. apply H. apply Z.eqb_eq. exact E.
Qed.

Section G46.
Variable BX : AA -> AA.
Hypothesis BXg : ltac2:(tb__ "0|0|
S2cS0S2eS2dVBX;R1A1A1S2dR1A1A3FX;").
Variable PX : list sobj.
Variable FXP : list sprop.
Hypothesis PX_noband : ltac2:(tb__ "0|2|
S2cS46S14S3eQ40A1M0S14S4G0A1S4S56A1S55VJG;VBX;R8R7R6R5R4R3R2R1A9S4cS17S1cR5A1VFXP;A3S4S15A1S0S4S8S8S16S16A2S16A2M1A1S4bS15G1S54R1A4S4bS15G1S54VPX;A4A3S4cS15S15S75S1dR9R1A2A1Lo;R2A3F_;Fl;F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;").
Variables (D8 U9 E9f E9p CO9p E9q : axst).
Hypothesis WU9 : ltac2:(tb__ "0|0|
S0S5S1fS34VU9;A1A1S6A3").
Hypothesis DU9 : ltac2:(tb__ "0|4|
S0SaS8S4S8S16S16A2M0A1M1S4S17A1M2A2M3A1S67S34VD8;A1S34VU9;A1A2SdG3SbG1G2S9G0A1S87Vnx;A1A4A2A3").
Hypothesis NXU9 : ltac2:(tb__ "0|0|
S0S3cS18S34VU9;A1A1S18S34VD8;A1A1A3").
Hypothesis HU9 : ltac2:(tb__ "0|0|
S0S35S36VD8;S34VU9;A1A2VU9;A3").
Hypothesis Cert9 : ltac2:(tb__ "0|1|
S0S5S68S72Ufa0S7S3bS84S7S3bS8fS9S3bA1A3A3VGS;S7S35VU9;S9S35A1M0A3S7S35VE9f;S7S35VE9p;G0A3A3A6S6A3").
Hypothesis SK9 : ltac2:(tb__ "0|1|
S0S4S8S8S16S16A2S16A2M0A1S4bS15G0S54S22S34VE9p;A1A1A4S4bS15G0S54ScS15S7S15S8eVnx;A1S7S15S80Vnx;A1S7S15S7cVnx;A1S7S15S6aVnx;A1S9S15A1A3A3A3A3ScS15S76VnW;Vnx;A2VPX;A3A3A4A3").
Hypothesis FC9 : ltac2:(tb__ "0|0|
S5bS17ScS17S4aVW;Vst;A2S49S48A1A3S1aS34VE9p;A1A1A3").
Hypothesis FX9 : ltac2:(tb__ "0|0|
S5bS17VFXP;S1aS34VE9p;A1A1A3").
Hypothesis FP9 : ltac2:(tb__ "0|0|
S5cS17S26S7fA1S1aS34VE9p;A1A1A3").
Hypothesis XC9 : ax_X E9p = [].
Hypothesis HCO9 : ltac2:(tb__ "0|0|
S0S35S6cVE9p;S28S83Vnx;A1S20Z0A1S20Z1A1S9S27A1S24A5A2VCO9p;A3").
Hypothesis WCO9 : ltac2:(tb__ "0|0|
S0S5S1fS34VCO9p;A1A1S6A3").
Hypothesis Cert9q : ltac2:(tb__ "0|1|
S0S5S68S72Ufa0S7S3bS84S9S3bA1A3VGS;S7S35VCO9p;S9S35A1M0A3S7S35VE9q;G0A3A6S6A3").

Lemma RSU9 : ltac2:(tb__ "0|1|
S2cS46S14S3eQ40A1M0S14S4G0A1S58S40Vsegs;VJG;VBX;R7R6R5R4A5VD8;R3R2R1A6S40Vsegs;VJG;VBX;R8R7R6R5A5VU9;R4R3R2A6F_;Fw;Ftp;FrhoX;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a rhoX tp w Hw. destruct w as [tr [ms md]]. rewrite <- HU9.
  eapply SPA_restate; [exact WU9 | exact DU9 | exact NXU9 | constructor | | exact Hw].
  exact (F_g9_hold BX A Kc rho a rhoX tp tr md (proj2 Hw)).
Qed.

Lemma prep9 : ltac2:(tb__ "0|4|
S2cS46S14S3eQ40M0A1M1S14S4G1A1S58S66VW;Vst;A2S3bS1S4fS5eS3dG0R6A2A1M2R1A2S50R1S4eG2S51S63S3dG0S1bR7PcA2A2A1Z8A2A2A2A2S2S0SaS3eQ8A1M3A1S23R8S3fG0R2A2A2SfG3A1A3A1F_;Fz;S40Vsegs;VJG;VBX;R9R8R7R6A5VE9p;R5R4R3A6S40Vsegs;VJG;VBX;RaR9R8R7A5VCO9p;R6R5R4A6F_;F_;F_;Fw;Ftp;FrhoX;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a rhoX tp w HW RUNDEF Hw. pose proof (SPA_facts_hold segs _ rhoX E9p tp w Hw) as HF. destruct w as [tr [ms md]].
  pose proof (proj2 Hw) as HJ. cbn [w_tr w_cfg cfg_model fst snd] in HJ.
  destruct (site9_vals BX A Kc rho a rhoX tp tr md HJ) as (_ & EB). cbn zeta in EB.
  destruct (site8_vals BX A Kc rho a rhoX tp tr md HJ) as (EB4 & EL4 & _). cbn zeta in EB4, EL4.
  destruct (site7_vals BX A Kc rho a rhoX tp tr md HJ) as (_ & _ & EBR & EL3b & V512 & VM). cbn zeta in EBR, EL3b, V512, VM.
  destruct (site3_vals BX A Kc rho a rhoX tp tr md HJ) as (EB3 & _ & EL3).
  destruct (site1_bounds nW st tmax nx Hnx BX A Kc rho a rhoX tp tr md HJ) as (EB1 & EL1 & BB1).
  pose proof (JGs_nums nW st tmax nx Hnx BX A Kc rho a rhoX tp tr md HJ) as (HN & SMB & SMM & AL & IMG & TOP & ENS & EMS & R8M & R8B). cbn zeta in *.
  pose proof (proj2 (nmod8_of_par BX A Kc rho a rhoX tp tr md HJ) (proj1 (Forall_forall _ _) HF _ FP9)) as NM8.
  set (nv := bv_unsigned (rw rho 12%positive)) in *.

  assert (NV8 : secneeded nv / 8 = nv / 8 + 1 + 512).
  { rewrite ENS. replace (round_up nv 8 + 4096) with (round_up nv 8 + 512 * 8) by lia. rewrite Z.div_add by lia. f_equal.
    unfold round_up. rewrite Z.div_mul by lia. pose proof (Z.div_mod nv 8 ltac:(lia)) as DN. pose proof (Z.mod_pos_bound nv 8 ltac:(lia)) as MN.
    symmetry. apply Z.div_unique with (nv mod 8 - 1); lia. }
  pose proof (Z.div_pos nv 8 ltac:(lia) ltac:(lia)) as NP.
  assert (SL : slink (bv_unsigned a) (secmapsize nv) rho rho).
  { split; [intros i; reflexivity|]. split; [intros l; reflexivity|]. split; [intros x; left; reflexivity | exact RUNDEF]. }
  assert (E1 : bv_unsigned (eval rhoX (SLit 1)) = 1) by (cbn [eval]; apply u64_lit; lia).
  rewrite <- HCO9. apply (carve_piece nW st tmax nx Hnx BX E9p (BP9 nx) (SLit 1) A Kc rho rho a rhoX tp _ SL Hw); [rewrite HCO9; exact WCO9 | exact XC9 | | |].
  - rewrite EB. clear -NP. lia.
  - rewrite EB, E1. fold nv. clear -NV8 VM. lia.
  - rewrite EB, E1. pose proof (run_band BX A Kc rho a rhoX tp tr md HJ) as RB.
    apply (pieces_disjoint nW st tmax nx Hnx BX BXg E9p [O_4z nx; O_3b nx; O_3 nx; O_1 nx] PX A Kc rho a rhoX tp _ _ _ HW Hw SK9 FC9).
    + apply (RB (Sh (bv_unsigned a) + 768 + nv / 8)). fold nv. clear -NV8 VM NP. lia.
    + pose proof (RB (Sh (bv_unsigned a) + 768 + nv / 8) ltac:(fold nv; clear -NV8 VM NP; lia)). lia.
    + intros l2 EE. destruct l2 as [|o [|o' [|o'' [|o3 [|o4 l2']]]]]; try (cbn in EE; discriminate EE).
      assert (Es : skel o = skel (O_4z nx)) by (cbn in EE; congruence). assert (Es' : skel o' = skel (O_3b nx)) by (cbn in EE; congruence).
      assert (Es'' : skel o'' = skel (O_3 nx)) by (cbn in EE; congruence). assert (Es3 : skel o3 = skel (O_1 nx)) by (cbn in EE; congruence).
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
      * rewrite (obj_range_skel rhoX o (O_4z nx) Es). unfold O_4z, obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi fst snd].
        rewrite soff_lit_small by lia. rewrite (soff_of_val rhoX (a2e8 nx) _ EL4) by (pose proof (Z.div_lt_upper_bound nv 8 (2 ^ 36) ltac:(lia) ltac:(clear -HN; lia)); fold nv; lia). rewrite EB4.
        unfold ranges_disjoint. cbn [fst snd]. right. right. left. fold nv. lia.
      * rewrite (obj_range_skel rhoX o' (O_3b nx) Es'). unfold O_3b, obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi fst snd].
        rewrite soff_lit_small by lia. rewrite EBR. unfold ranges_disjoint. cbn [fst snd]. right. right. right. clear -NV8. lia.
      * rewrite (obj_range_skel rhoX o'' (O_3 nx) Es''). unfold O_3, L3. rewrite obj_range_mk by lia. rewrite EB3.
        unfold ranges_disjoint. cbn [fst snd]. right. right. left. clear -NP. lia.
      * rewrite (obj_range_skel rhoX o3 (O_1 nx) Es3). unfold O_1, L1. rewrite obj_range_mk by lia. rewrite EB1.
        unfold ranges_disjoint. cbn [fst snd]. right. right. left. clear -NP. lia.
    + intros l2 EE.
      assert (HFX : Forall (holds rhoX) FXP) by (apply Forall_forall; intros p Hp; exact (proj1 (Forall_forall _ _) HF p (FX9 p Hp))).
      pose proof (PX_noband A Kc rho a rhoX tp tr md HJ HFX l2 EE) as NB.
      eapply Forall_impl; [|exact NB]. intros o Ho. cbn beta in Ho. unfold ranges_disjoint. cbn [fst snd].
      set (lo := Sh (bv_unsigned a) + 768 + nv / 8) in *.
      destruct (Z_lt_le_dec (fst (obj_range rhoX o)) (snd (obj_range rhoX o))) as [NE|]; [|left; lia].
      destruct (Z_le_gt_dec (snd (obj_range rhoX o)) lo) as [|G1]; [right; right; left; lia|].
      destruct (Z_le_gt_dec (lo + 1) (fst (obj_range rhoX o))) as [|G2]; [right; right; right; lia|].
      exfalso. pose proof (Ho lo ltac:(lia)) as NBx. pose proof (RB lo ltac:(unfold lo; fold nv; clear -NV8 VM NP; lia)) as Bx.
      unfold noband in NBx. clear -NBx Bx. lia.
Qed.

Theorem sec_g46 : ltac2:(tb__ "0|5|
S58OF_;S2cS46S14S3eQ40M0A1M1S59S66VW;Vst;A2S64VW;Vst;A2S47R6A1S42Vsegs;R9S41R7A1A3S3bS1S4fS5eS3dG0R7A2A1M2R1A2S50R1S4eG2S51S63S3dG0S1bR8PcA2A2A1Z8A2A2A2A2S2S0SaS3eQ8A1M3A1S23R9S3fG0R2A2A2SfG3A1A3A1F_;Fz;S14S4G1A1M4S57Vsegs;RdS40Vsegs;VJG;VBX;RcRbRaR9A5VE9f;R2R1A5R8A4FtpY;FrhoY;S14G4S57Vsegs;ReS40Vsegs;VJG;VBX;RdRcRbRaA5VE9q;R2R1A5R9A4FtpY;FrhoY;S14G4S57Vsegs;RfS40Vsegs;VJG;VBX;ReRdRcRbA5VD8;R2R1A5RaA4FtX;FrX;F_;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho a Q HW HUS HKc Hokl RUNDEF HCF HCQ rX tX.
  pose proof (JG_okf nW st nx BX ok A Kc rho a Hokl) as Hokf. pose proof (JG_stable nW st tmax nx Hnx NXG BX A Kc rho a HUS HKc) as HST.
  eapply triple_conseq; [intros w Hw; exact (RSU9 A Kc rho a rX tX w Hw) | intros w Hw; exact Hw |].
  apply (cfg_soundA segs 4000%nat [CPC; PGST] GS [U9] [E9f; E9p] (JG BX A Kc rho a) ok Q tX Hokf HST Cert9); [|left; reflexivity].
  intros E rE HinE. destruct HinE as [<-|[<-|[]]].
  - eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | exact (HCF rE tX)].
  - eapply triple_conseq; [intros w Hw; exact (prep9 A Kc rho a rE tX w HW RUNDEF Hw) | intros w Hw; right; exact Hw |].
    apply (cfg_soundA segs 4000%nat [CPC] GS [CO9p] [E9q] (JG BX A Kc rho a) ok Q tX Hokf HST Cert9q); [|left; reflexivity].
    intros E rE' HinE. destruct HinE as [<-|[]].
    eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | exact (HCQ rE' tX)].
Qed.
End G46.

Section G47.
Variable BX : AA -> AA.
Variables (E S9a S9b D9 : axst) (iM : nat) (perm : list nat).
Hypothesis HS9a : ltac2:(tb__ "0|0|
S0S35S8cVE;ViM;S20Z1800A1A3VS9a;A3").
Hypothesis HS9b : ltac2:(tb__ "0|0|
S0S35S8cVS9a;S13ViM;A1S20Z2800A1A3VS9b;A3").
Hypothesis HD9 : ltac2:(tb__ "0|1|
S0S35S36VS9b;Sb3S34VS9b;A1M0SafS22G0A1Vperm;A2A2A2VD9;A3").
Hypothesis NDp : nodupN perm = true.
Hypothesis BNDp : ltac2:(tb__ "0|0|
S0S5S5aSeSeSadR1S12S15S22S34VS9b;A1A1A2A2Li;Vperm;A3S6A3").
Hypothesis COVp : ltac2:(tb__ "0|0|
S0S5S5aSeSeS5dSeSacR1A1Vperm;A3Li;S4dU0S12S15S22S34VS9b;A1A1A2A2A3S6A3").

Lemma prepF : ltac2:(tb__ "0|1|
S2cS46S14S3eQ40A1M0S14S4G0A1S58S40Vsegs;VJG;VBX;R7R6R5R4A5VE;R3R2R1A6S40Vsegs;VJG;VBX;R8R7R6R5A5VS9b;R4R3R2A6F_;Fw;Ftp;FrhoX;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a rhoX tp w Hw.
  assert (Ha : SPA segs (JG BX A Kc rho a) S9a rhoX tp w).
  { rewrite <- HS9a. unfold osplit. destruct (split_obj_at (ax_S E) iM (SLit 6144)) as [S'|] eqn:E1; [|exact Hw]. eapply (SPA_split segs); [exact E1 | exact Hw]. }
  rewrite <- HS9b. unfold osplit. destruct (split_obj_at (ax_S S9a) (S iM) (SLit 10240)) as [S'|] eqn:E2; [|exact Ha]. eapply (SPA_split segs); [exact E2 | exact Ha].
Qed.
Lemma prepD : ltac2:(tb__ "0|1|
S2cS46S14S3eQ40A1M0S14S4G0A1S58S40Vsegs;VJG;VBX;R7R6R5R4A5VE;R3R2R1A6S40Vsegs;VJG;VBX;R8R7R6R5A5VD9;R4R3R2A6F_;Fw;Ftp;FrhoX;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a rhoX tp w Hw. rewrite <- HD9.
  apply (SPA_select segs (JG BX A Kc rho a) rhoX S9b perm tp w (prepF A Kc rho a rhoX tp w Hw) NDp).
  - intros i Hi. apply Nat.ltb_lt. exact (proj1 (forallb_forall _ _) BNDp i Hi).
  - intros i Hi. pose proof (proj1 (forallb_forall _ _) COVp i ltac:(apply in_seq; exact (conj (Nat.le_0_l i) Hi))) as X.
    apply existsb_exists in X as (i' & Hi' & Ei). apply Nat.eqb_eq in Ei. subst i'. exact Hi'.
Qed.

Theorem sec_g47 : ltac2:(tb__ "0|2|
S58OF_;S2cS46S14S3eQ40A1M0S59S14S4G0A1M1S57Vsegs;R8S40Vsegs;VJG;VBX;R7R6R5R4A5VD9;R2R1A5R3A4FtpY;FrhoY;S14G1S57Vsegs;R9S40Vsegs;VJG;VBX;R8R7R6R5A5VE;R2R1A5R4A4FtX;FrX;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho a Q HCONT rX tX.
  eapply triple_conseq; [intros w Hw; exact (prepD A Kc rho a rX tX w Hw) | intros w Hw; exact Hw | exact (HCONT rX tX)].
Qed.

Section DIAMOND.
Hypothesis BXg : ltac2:(tb__ "0|0|
S2cS0S2eS2dVBX;R1A1A1S2dR1A1A3FX;").
Variables D9A D9B : axst.
Hypothesis HD9A : ltac2:(tb__ "0|0|
S0S35S69S79Vnx;A1VD9;A2VD9A;A3").
Hypothesis HD9B : ltac2:(tb__ "0|0|
S0S35S69S7aVnx;A1VD9;A2VD9B;A3").
Hypothesis FBA9 : ltac2:(tb__ "0|0|
S0S5S5aS17S1eS18S34VD9;A1A1A1S79Vnx;A1A3S6A3").
Hypothesis FBB9 : ltac2:(tb__ "0|0|
S0S5S5aS17S1eS18S34VD9;A1A1A1S7aVnx;A1A3S6A3").
Theorem sec_g47d : ltac2:(tb__ "0|2|
S58OF_;S2cS46S14S3eQ40A1M0S59S14S4G0A1M1S57Vsegs;R8S40Vsegs;VJG;VBX;R7R6R5R4A5VD9A;R2R1A5R3A4FtpY;FrhoY;S14G1S57Vsegs;R9S40Vsegs;VJG;VBX;R8R7R6R5A5VD9B;R2R1A5R4A4FtpY;FrhoY;S14G1S57Vsegs;RaS40Vsegs;VJG;VBX;R9R8R7R6A5VE;R2R1A5R5A4FtX;FrX;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho a Q HCA HCB rX tX.
  apply (triple_conseq (P:=fun w => SPA segs (JG BX A Kc rho a) D9A rX tX w \/ SPA segs (JG BX A Kc rho a) D9B rX tX w)
           (SPA segs (JG BX A Kc rho a) E rX tX) (Q:=Q)); [intros w Hw0 | intros w Hw; exact Hw |].
  { pose proof (prepD A Kc rho a rX tX w Hw0) as Hw. destruct w as [tr [ms md]].
    destruct (diamond_hold BX A Kc rho a rX tX tr md BXg (proj2 Hw)) as [FA|FB]; [left; rewrite <- HD9A | right; rewrite <- HD9B].
    - split; [|exact (proj2 Hw)]. exact (smatchA_add_facts segs rX tX (F_A nx) _ _ (proj1 Hw) FA FBA9).
    - split; [|exact (proj2 Hw)]. exact (smatchA_add_facts segs rX tX (F_B nx) _ _ (proj1 Hw) FB FBB9). }
  apply triple_disj; [exact (HCA rX tX) | exact (HCB rX tX)].
Qed.
End DIAMOND.
End G47.
End SEC6.
End SpineCallocSec6.

(* [comment removed for export] *)
Module SpineCallocSec4IE.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "bool"; "nil"; "true"; "None"; "length"; "list"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_ecfgA"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "SLit"; "ss_next"; "rw"; "rm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_geom"; "aa_sec"; "sec_chunk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3"; "JGs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jq.SpineCallocSec3I"; "nx0"; "D2c"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineCallocSec4I"; "CO3bc"; "G3c"; "L3ac"; "U2c"; "T4ac"; "T4bc"; "X3a3c"; "X3ac"; "X3bc"; "Y4a0c"; "Y4a1c"; "Y4b0c"; "Y4b1c"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "secmapsize"; "stopJ_stable"; "@Stdlib.ZArith.BinInt.Z"; "add"; "lt"; "div"; "le"; "of_nat"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.CSecBump"; "bumpP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "Sh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jx.SpineCallocSec4"; "slink4"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jx.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineCallocSec4I.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k6.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.CSecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.CSecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jq.SpineCallocSec3I OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jx.SpineCallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineCallocSec4I OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k1.SpineCallocSecE1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k6.SpineCallocSecE2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import CallocBase2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ii.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.CallocPosts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 0. Let st : ustop := UStopLe. Let tmax : Z := 2.
Let GS0 : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3.GS nx0.

Lemma NXEU2_0 : ltac2:(tb__ "0|0|
SdS1S16VGS0;S12S15S27A1A1A2S3A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXEG3_0 : ltac2:(tb__ "0|0|
SdS1S16VGS0;S12S15S25A1A1A2S3A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXEL3a_0 : ltac2:(tb__ "0|0|
SdS1S16VGS0;S12S15S26A1A1A2S3A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXECOb_0 : ltac2:(tb__ "0|0|
SdS1S16VGS0;S12S15S24A1A1A2S3A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert3_0 : ltac2:(tb__ "0|3|
SdS1SaScUfa0S0SbZ706a0S0SbZ410f0S2SbA1A3A3VGS0;S0S8S9S27Z1S11Z0M0A1M1A3S2S8A1M2A3S0S8S9S2bG0G1A3S0S8S9S2cG0G1A3G2A3A3A6S3A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [0x706a0; 0x410f0] GS0 [mkVNA U2c 1 (SLit 0)] [mkVNA X3ac 0 (SLit 0); mkVNA X3bc 0 (SLit 0)] [SpineCallocSec4I.run3]); [exact SpineCallocSec4I.run3__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma ECert3a_0 : ltac2:(tb__ "0|3|
SdS1SaScUfa0S0SbZ410f0S2SbA1A3VGS0;S0S8S9S25Z1S11Z0M0A1M1A3S2S8A1M2A3S0S8S9S2aG0G1A3G2A3A6S3A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [0x410f0] GS0 [mkVNA G3c 1 (SLit 0)] [mkVNA X3a3c 0 (SLit 0)] [SpineCallocSec4I.run3a]); [exact SpineCallocSec4I.run3a__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma ECert4a_0 : ltac2:(tb__ "0|3|
SdS1SaScUfa0S0SbZ3c614S2SbA1A3VGS0;S0S8S9S26Z1S11Z0M0A1M1A3S2S8A1M2A3S0S8S9S2dG0G1A3S0S8S9S2eG0G1A3G2A3A3A6S3A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [0x3c614] GS0 [mkVNA L3ac 1 (SLit 0)] [mkVNA Y4a0c 0 (SLit 0); mkVNA Y4a1c 0 (SLit 0)] [SpineCallocSec4I.run4a]); [exact SpineCallocSec4I.run4a__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma ECert4b_0 : ltac2:(tb__ "0|3|
SdS1SaScUfa0S0SbZ3c614S2SbA1A3VGS0;S0S8S9S24Z1S11Z0M0A1M1A3S2S8A1M2A3S0S8S9S2fG0G1A3S0S8S9S30G0G1A3G2A3A3A6S3A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [0x3c614] GS0 [mkVNA CO3bc 1 (SLit 0)] [mkVNA Y4b0c 0 (SLit 0); mkVNA Y4b1c 0 (SLit 0)] [SpineCallocSec4I.run4b]); [exact SpineCallocSec4I.run4b__runeq | vm_cast_no_check (eq_refl true)]. Qed.

Theorem esec_g3_0h : ltac2:(tb__ "0|8|
S1dS3bS10S18Q40M0A1M1S1bOF_;S32VW;Vst;A2S3cR5A1S34S33S37S5S20S1fR7A1A2A1Z1A2S38Z2Z14A2A2SbSeS36S3aS17G0R6A2A1M2R1A2S34R1S33G2S35S31S17G0S13R7PcM3A2A2A1Z8A2A2A2A2SfSdS7S18Q8A1M4A1S14R8S19G0R2A2A2S4G4A1A3A1F_;Fz;S10S10S6G1A1M5S3dS1eRcA1S17G0R9A2S31S17G0S13RaG3A2A2A1RaR3A5S1aScS1cScS21U0M6Vst;S22S1dS39R1A1LX;RdRcR4RaA8S28R3R2A5R9A3F_;FtY;FrY;Frho'';S10G5S1aScS1cScS21G6Vst;S22S1dR1LX;M7RcRbRaR9A8S29R2R1A5R8A3FtY;FrY;S10G5S1aScS1cScS21G6Vst;S22G7RdRcRbRaA8S23R2R1A5R9A3FtX;FrX;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a Q HUS HKc Hok RUNDEF HCa HCb rX tX.
  eapply esec_g3 with
    (nW := 0%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (AX := (fun X : AA => X)) (AXg := (fun X => eq_refl)) (AXs := (fun X => eq_refl))
    (AXp := (fun X => eq_refl)) (AXb := (fun X => eq_refl)) (D2 := D2c) (U2 := U2c) (X3a := X3ac) (X3b := X3bc) (CS3 := CS3c) (G3 := G3c) (X3a3 := X3a3c) (L3a := L3ac)
    (L3b := L3bc) (CO3b := CO3bc) (T4a := T4ac) (T4b := T4bc) (Y4a0 := Y4a0c) (Y4a1 := Y4a1c) (Y4b0 := Y4b0c) (Y4b1 := Y4b1c) (sLa := sLa) (sLb := sLb) (s4a0 := s4a0)
    (s4a1 := s4a1) (s4b0 := s4b0) (s4b1 := s4b1) (WU2 := WU2_0) (DU2 := DU2_0) (NXU2 := NXU2_0) (HU2 := HU2_0) (Cert3 := Cert3_0) (WC3 := WC3_0) (DC3 := DC3_0)
    (NXC3 := NXC3_0) (HC3 := HC3_0) (FX3a := FX3a_0) (IC3 := IC3_0) (R17 := R17_0) (R10 := R10_0) (BBw := BBw_0) (R11 := R11_0) (R12 := R12_0) (R13 := R13_0)
    (R14 := R14_0) (R15 := R15_0) (XC3 := XC3_0) (SK3 := SK3_0) (FC3 := FC3_0) (FCS3 := FCS3_0) (NXS3 := NXS3_0) (HG3 := HG3_0) (Cert3a := Cert3a_0) (ELa := ELa_0)
    (IDa := IDa_0) (GLa := GLa_0) (FBLa := FBLa_0) (HL3a := HL3a_0) (ELb := ELb_0) (IDb := IDb_0) (GLb := GLb_0) (FBLb := FBLb_0) (HL3b := HL3b_0) (HCOb := HCOb_0)
    (WCOb := WCOb_0) (XCb := XCb_0) (SKb := SKb_0) (FCb := FCb_0) (FXb := FXb_0) (Cert4a := Cert4a_0) (E4a0 := E4a0_0) (I4a0 := I4a0_0) (E4a1 := E4a1_0) (I4a1 := I4a1_0)
    (Cert4b := Cert4b_0) (E4b0 := E4b0_0) (I4b0 := I4b0_0) (E4b1 := E4b1_0) (I4b1 := I4b1_0) (NXEU2 := NXEU2_0) (NXEG3 := NXEG3_0) (NXEL3a := NXEL3a_0)
    (NXECOb := NXECOb_0) (ECert3 := ECert3_0) (ECert3a := ECert3a_0) (ECert4a := ECert4a_0) (ECert4b := ECert4b_0);
    [hw_discharge | exact HUS | exact HKc | exact Hok | exact RUNDEF | exact HCa | exact HCb].
Qed.
End INST.
End SpineCallocSec4IE.

(* [comment removed for export] *)
Module SpineCallocSec4IEL.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "bool"; "nil"; "true"; "None"; "length"; "list"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_ecfgA"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "SLit"; "ss_next"; "rw"; "rm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_geom"; "aa_sec"; "sec_chunk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3"; "JGs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k1.SpineCallocSec3IL"; "nx0"; "D2c"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineCallocSec4IL"; "CO3bc"; "G3c"; "L3ac"; "U2c"; "T4ac"; "T4bc"; "X3a3c"; "X3ac"; "X3bc"; "Y4a0c"; "Y4a1c"; "Y4b0c"; "Y4b1c"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "secmapsize"; "stopJ_stable"; "@Stdlib.ZArith.BinInt.Z"; "add"; "lt"; "div"; "le"; "of_nat"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.CSecBump"; "bumpP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "Sh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jx.SpineCallocSec4"; "slink4"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jx.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineCallocSec4IL.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k6.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.CSecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.CSecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k1.SpineCallocSec3IL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jx.SpineCallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineCallocSec4IL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k1.SpineCallocSecE1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k6.SpineCallocSecE2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import CallocBase2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ii.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.CallocPosts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 0. Let st : ustop := UStopLe. Let tmax : Z := 2.
Let GS0 : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3.GS nx0.

Lemma NXEU2_0 : ltac2:(tb__ "0|0|
SdS1S16VGS0;S12S15S27A1A1A2S3A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXEG3_0 : ltac2:(tb__ "0|0|
SdS1S16VGS0;S12S15S25A1A1A2S3A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXEL3a_0 : ltac2:(tb__ "0|0|
SdS1S16VGS0;S12S15S26A1A1A2S3A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXECOb_0 : ltac2:(tb__ "0|0|
SdS1S16VGS0;S12S15S24A1A1A2S3A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert3_0 : ltac2:(tb__ "0|3|
SdS1SaScUfa0S0SbZ706a0S0SbZ410f0S2SbA1A3A3VGS0;S0S8S9S27Z1S11Z0M0A1M1A3S2S8A1M2A3S0S8S9S2bG0G1A3S0S8S9S2cG0G1A3G2A3A3A6S3A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [0x706a0; 0x410f0] GS0 [mkVNA U2c 1 (SLit 0)] [mkVNA X3ac 0 (SLit 0); mkVNA X3bc 0 (SLit 0)] [SpineCallocSec4IL.run3]); [exact SpineCallocSec4IL.run3__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma ECert3a_0 : ltac2:(tb__ "0|3|
SdS1SaScUfa0S0SbZ410f0S2SbA1A3VGS0;S0S8S9S25Z1S11Z0M0A1M1A3S2S8A1M2A3S0S8S9S2aG0G1A3G2A3A6S3A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [0x410f0] GS0 [mkVNA G3c 1 (SLit 0)] [mkVNA X3a3c 0 (SLit 0)] [SpineCallocSec4IL.run3a]); [exact SpineCallocSec4IL.run3a__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma ECert4a_0 : ltac2:(tb__ "0|3|
SdS1SaScUfa0S0SbZ3c614S2SbA1A3VGS0;S0S8S9S26Z1S11Z0M0A1M1A3S2S8A1M2A3S0S8S9S2dG0G1A3S0S8S9S2eG0G1A3G2A3A3A6S3A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [0x3c614] GS0 [mkVNA L3ac 1 (SLit 0)] [mkVNA Y4a0c 0 (SLit 0); mkVNA Y4a1c 0 (SLit 0)] [SpineCallocSec4IL.run4a]); [exact SpineCallocSec4IL.run4a__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma ECert4b_0 : ltac2:(tb__ "0|3|
SdS1SaScUfa0S0SbZ3c614S2SbA1A3VGS0;S0S8S9S24Z1S11Z0M0A1M1A3S2S8A1M2A3S0S8S9S2fG0G1A3S0S8S9S30G0G1A3G2A3A3A6S3A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [0x3c614] GS0 [mkVNA CO3bc 1 (SLit 0)] [mkVNA Y4b0c 0 (SLit 0); mkVNA Y4b1c 0 (SLit 0)] [SpineCallocSec4IL.run4b]); [exact SpineCallocSec4IL.run4b__runeq | vm_cast_no_check (eq_refl true)]. Qed.

Theorem esec_g3_0l : ltac2:(tb__ "0|8|
S1dS3bS10S18Q40M0A1M1S1bOF_;S32VW;Vst;A2S3cR5A1S34S33S37S5S20S1fR7A1A2A1Z1A2S38Z2Z14A2A2SbSeS36S3aS17G0R6A2A1M2R1A2S34R1S33G2S35S31S17G0S13R7PcM3A2A2A1Z8A2A2A2A2SfSdS7S18Q8A1M4A1S14R8S19G0R2A2A2S4G4A1A3A1F_;Fz;S10S10S6G1A1M5S3dS1eRcA1S17G0R9A2S31S17G0S13RaG3A2A2A1RaR3A5S1aScS1cScS21U0M6Vst;S22S1dS39R1A1LX;RdRcR4RaA8S28R3R2A5R9A3F_;FtY;FrY;Frho'';S10G5S1aScS1cScS21G6Vst;S22S1dR1LX;M7RcRbRaR9A8S29R2R1A5R8A3FtY;FrY;S10G5S1aScS1cScS21G6Vst;S22G7RdRcRbRaA8S23R2R1A5R9A3FtX;FrX;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a Q HUS HKc Hok RUNDEF HCa HCb rX tX.
  eapply esec_g3 with
    (nW := 0%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (AX := (fun X : AA => X)) (AXg := (fun X => eq_refl)) (AXs := (fun X => eq_refl))
    (AXp := (fun X => eq_refl)) (AXb := (fun X => eq_refl)) (D2 := D2c) (U2 := U2c) (X3a := X3ac) (X3b := X3bc) (CS3 := CS3c) (G3 := G3c) (X3a3 := X3a3c) (L3a := L3ac)
    (L3b := L3bc) (CO3b := CO3bc) (T4a := T4ac) (T4b := T4bc) (Y4a0 := Y4a0c) (Y4a1 := Y4a1c) (Y4b0 := Y4b0c) (Y4b1 := Y4b1c) (sLa := sLa) (sLb := sLb) (s4a0 := s4a0)
    (s4a1 := s4a1) (s4b0 := s4b0) (s4b1 := s4b1) (WU2 := WU2_0) (DU2 := DU2_0) (NXU2 := NXU2_0) (HU2 := HU2_0) (Cert3 := Cert3_0) (WC3 := WC3_0) (DC3 := DC3_0)
    (NXC3 := NXC3_0) (HC3 := HC3_0) (FX3a := FX3a_0) (IC3 := IC3_0) (R17 := R17_0) (R10 := R10_0) (BBw := BBw_0) (R11 := R11_0) (R12 := R12_0) (R13 := R13_0)
    (R14 := R14_0) (R15 := R15_0) (XC3 := XC3_0) (SK3 := SK3_0) (FC3 := FC3_0) (FCS3 := FCS3_0) (NXS3 := NXS3_0) (HG3 := HG3_0) (Cert3a := Cert3a_0) (ELa := ELa_0)
    (IDa := IDa_0) (GLa := GLa_0) (FBLa := FBLa_0) (HL3a := HL3a_0) (ELb := ELb_0) (IDb := IDb_0) (GLb := GLb_0) (FBLb := FBLb_0) (HL3b := HL3b_0) (HCOb := HCOb_0)
    (WCOb := WCOb_0) (XCb := XCb_0) (SKb := SKb_0) (FCb := FCb_0) (FXb := FXb_0) (Cert4a := Cert4a_0) (E4a0 := E4a0_0) (I4a0 := I4a0_0) (E4a1 := E4a1_0) (I4a1 := I4a1_0)
    (Cert4b := Cert4b_0) (E4b0 := E4b0_0) (I4b0 := I4b0_0) (E4b1 := E4b1_0) (I4b1 := I4b1_0) (NXEU2 := NXEU2_0) (NXEG3 := NXEG3_0) (NXEL3a := NXEL3a_0)
    (NXECOb := NXECOb_0) (ECert3 := ECert3_0) (ECert3a := ECert3a_0) (ECert4a := ECert4a_0) (ECert4b := ECert4b_0);
    [hw_discharge | exact HUS | exact HKc | exact Hok | exact RUNDEF | exact HCa | exact HCb].
Qed.
End INST.
End SpineCallocSec4IEL.

(* [comment removed for export] *)
Module SpineCallocSec4IELW1.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "bool"; "nil"; "true"; "None"; "length"; "list"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_ecfgA"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "SLit"; "ss_next"; "rw"; "rm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_geom"; "aa_sec"; "sec_chunk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3"; "JGs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k1.SpineCallocSec3ILW1"; "nx0"; "D2c"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineCallocSec4ILW1"; "CO3bc"; "G3c"; "L3ac"; "U2c"; "T4ac"; "T4bc"; "X3a3c"; "X3ac"; "X3bc"; "Y4a0c"; "Y4a1c"; "Y4b0c"; "Y4b1c"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "secmapsize"; "stopJ_stable"; "@Stdlib.ZArith.BinInt.Z"; "add"; "lt"; "div"; "le"; "of_nat"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.CSecBump"; "bumpP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "Sh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jx.SpineCallocSec4"; "slink4"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jx.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineCallocSec4ILW1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k6.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.CSecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.CSecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k1.SpineCallocSec3ILW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jx.SpineCallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineCallocSec4ILW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k1.SpineCallocSecE1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k6.SpineCallocSecE2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import CallocBase2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ii.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.CallocPosts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 1. Let st : ustop := UStopLeOrPc. Let tmax : Z := 3.
Let GS0 : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3.GS nx0.

Lemma NXEU2_0 : ltac2:(tb__ "0|0|
SdS1S16VGS0;S12S15S27A1A1A2S3A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXEG3_0 : ltac2:(tb__ "0|0|
SdS1S16VGS0;S12S15S25A1A1A2S3A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXEL3a_0 : ltac2:(tb__ "0|0|
SdS1S16VGS0;S12S15S26A1A1A2S3A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXECOb_0 : ltac2:(tb__ "0|0|
SdS1S16VGS0;S12S15S24A1A1A2S3A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert3_0 : ltac2:(tb__ "0|3|
SdS1SaScUfa0S0SbZ706a0S0SbZ410f0S2SbA1A3A3VGS0;S0S8S9S27Z1S11Z0M0A1M1A3S2S8A1M2A3S0S8S9S2bG0G1A3S0S8S9S2cG0G1A3G2A3A3A6S3A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [0x706a0; 0x410f0] GS0 [mkVNA U2c 1 (SLit 0)] [mkVNA X3ac 0 (SLit 0); mkVNA X3bc 0 (SLit 0)] [SpineCallocSec4ILW1.run3]); [exact SpineCallocSec4ILW1.run3__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma ECert3a_0 : ltac2:(tb__ "0|3|
SdS1SaScUfa0S0SbZ410f0S2SbA1A3VGS0;S0S8S9S25Z1S11Z0M0A1M1A3S2S8A1M2A3S0S8S9S2aG0G1A3G2A3A6S3A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [0x410f0] GS0 [mkVNA G3c 1 (SLit 0)] [mkVNA X3a3c 0 (SLit 0)] [SpineCallocSec4ILW1.run3a]); [exact SpineCallocSec4ILW1.run3a__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma ECert4a_0 : ltac2:(tb__ "0|3|
SdS1SaScUfa0S0SbZ3c614S2SbA1A3VGS0;S0S8S9S26Z1S11Z0M0A1M1A3S2S8A1M2A3S0S8S9S2dG0G1A3S0S8S9S2eG0G1A3G2A3A3A6S3A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [0x3c614] GS0 [mkVNA L3ac 1 (SLit 0)] [mkVNA Y4a0c 0 (SLit 0); mkVNA Y4a1c 0 (SLit 0)] [SpineCallocSec4ILW1.run4a]); [exact SpineCallocSec4ILW1.run4a__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma ECert4b_0 : ltac2:(tb__ "0|3|
SdS1SaScUfa0S0SbZ3c614S2SbA1A3VGS0;S0S8S9S24Z1S11Z0M0A1M1A3S2S8A1M2A3S0S8S9S2fG0G1A3S0S8S9S30G0G1A3G2A3A3A6S3A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [0x3c614] GS0 [mkVNA CO3bc 1 (SLit 0)] [mkVNA Y4b0c 0 (SLit 0); mkVNA Y4b1c 0 (SLit 0)] [SpineCallocSec4ILW1.run4b]); [exact SpineCallocSec4ILW1.run4b__runeq | vm_cast_no_check (eq_refl true)]. Qed.

Theorem esec_g3_1l : ltac2:(tb__ "0|8|
S1dS3bS10S18Q40M0A1M1S1bOF_;S32VW;Vst;A2S3cR5A1S34S33S37S5S20S1fR7A1A2A1Z1A2S38Z2Z14A2A2SbSeS36S3aS17G0R6A2A1M2R1A2S34R1S33G2S35S31S17G0S13R7PcM3A2A2A1Z8A2A2A2A2SfSdS7S18Q8A1M4A1S14R8S19G0R2A2A2S4G4A1A3A1F_;Fz;S10S10S6G1A1M5S3dS1eRcA1S17G0R9A2S31S17G0S13RaG3A2A2A1RaR3A5S1aScS1cScS21U1M6Vst;S22S1dS39R1A1LX;RdRcR4RaA8S28R3R2A5R9A3F_;FtY;FrY;Frho'';S10G5S1aScS1cScS21G6Vst;S22S1dR1LX;M7RcRbRaR9A8S29R2R1A5R8A3FtY;FrY;S10G5S1aScS1cScS21G6Vst;S22G7RdRcRbRaA8S23R2R1A5R9A3FtX;FrX;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a Q HUS HKc Hok RUNDEF HCa HCb rX tX.
  eapply esec_g3 with
    (nW := 1%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (AX := (fun X : AA => X)) (AXg := (fun X => eq_refl)) (AXs := (fun X => eq_refl))
    (AXp := (fun X => eq_refl)) (AXb := (fun X => eq_refl)) (D2 := D2c) (U2 := U2c) (X3a := X3ac) (X3b := X3bc) (CS3 := CS3c) (G3 := G3c) (X3a3 := X3a3c) (L3a := L3ac)
    (L3b := L3bc) (CO3b := CO3bc) (T4a := T4ac) (T4b := T4bc) (Y4a0 := Y4a0c) (Y4a1 := Y4a1c) (Y4b0 := Y4b0c) (Y4b1 := Y4b1c) (sLa := sLa) (sLb := sLb) (s4a0 := s4a0)
    (s4a1 := s4a1) (s4b0 := s4b0) (s4b1 := s4b1) (WU2 := WU2_0) (DU2 := DU2_0) (NXU2 := NXU2_0) (HU2 := HU2_0) (Cert3 := Cert3_0) (WC3 := WC3_0) (DC3 := DC3_0)
    (NXC3 := NXC3_0) (HC3 := HC3_0) (FX3a := FX3a_0) (IC3 := IC3_0) (R17 := R17_0) (R10 := R10_0) (BBw := BBw_0) (R11 := R11_0) (R12 := R12_0) (R13 := R13_0)
    (R14 := R14_0) (R15 := R15_0) (XC3 := XC3_0) (SK3 := SK3_0) (FC3 := FC3_0) (FCS3 := FCS3_0) (NXS3 := NXS3_0) (HG3 := HG3_0) (Cert3a := Cert3a_0) (ELa := ELa_0)
    (IDa := IDa_0) (GLa := GLa_0) (FBLa := FBLa_0) (HL3a := HL3a_0) (ELb := ELb_0) (IDb := IDb_0) (GLb := GLb_0) (FBLb := FBLb_0) (HL3b := HL3b_0) (HCOb := HCOb_0)
    (WCOb := WCOb_0) (XCb := XCb_0) (SKb := SKb_0) (FCb := FCb_0) (FXb := FXb_0) (Cert4a := Cert4a_0) (E4a0 := E4a0_0) (I4a0 := I4a0_0) (E4a1 := E4a1_0) (I4a1 := I4a1_0)
    (Cert4b := Cert4b_0) (E4b0 := E4b0_0) (I4b0 := I4b0_0) (E4b1 := E4b1_0) (I4b1 := I4b1_0) (NXEU2 := NXEU2_0) (NXEG3 := NXEG3_0) (NXEL3a := NXEL3a_0)
    (NXECOb := NXECOb_0) (ECert3 := ECert3_0) (ECert3a := ECert3a_0) (ECert4a := ECert4a_0) (ECert4b := ECert4b_0);
    [hw_discharge | exact HUS | exact HKc | exact Hok | exact RUNDEF | exact HCa | exact HCb].
Qed.
End INST.
End SpineCallocSec4IELW1.

(* [comment removed for export] *)
Module SpineCallocSec4IEW1.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "bool"; "nil"; "true"; "None"; "length"; "list"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_ecfgA"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "SLit"; "ss_next"; "rw"; "rm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_geom"; "aa_sec"; "sec_chunk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3"; "JGs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k1.SpineCallocSec3IW1"; "nx0"; "D2c"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineCallocSec4IW1"; "CO3bc"; "G3c"; "L3ac"; "U2c"; "T4ac"; "T4bc"; "X3a3c"; "X3ac"; "X3bc"; "Y4a0c"; "Y4a1c"; "Y4b0c"; "Y4b1c"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "secmapsize"; "stopJ_stable"; "@Stdlib.ZArith.BinInt.Z"; "add"; "lt"; "div"; "le"; "of_nat"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.CSecBump"; "bumpP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "Sh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jx.SpineCallocSec4"; "slink4"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jx.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineCallocSec4IW1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k6.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.CSecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.CSecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k1.SpineCallocSec3IW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jx.SpineCallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineCallocSec4IW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k1.SpineCallocSecE1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k6.SpineCallocSecE2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import CallocBase2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ii.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.CallocPosts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 1. Let st : ustop := UStopLeOrPc. Let tmax : Z := 3.
Let GS0 : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3.GS nx0.

Lemma NXEU2_0 : ltac2:(tb__ "0|0|
SdS1S16VGS0;S12S15S27A1A1A2S3A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXEG3_0 : ltac2:(tb__ "0|0|
SdS1S16VGS0;S12S15S25A1A1A2S3A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXEL3a_0 : ltac2:(tb__ "0|0|
SdS1S16VGS0;S12S15S26A1A1A2S3A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXECOb_0 : ltac2:(tb__ "0|0|
SdS1S16VGS0;S12S15S24A1A1A2S3A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert3_0 : ltac2:(tb__ "0|3|
SdS1SaScUfa0S0SbZ706a0S0SbZ410f0S2SbA1A3A3VGS0;S0S8S9S27Z1S11Z0M0A1M1A3S2S8A1M2A3S0S8S9S2bG0G1A3S0S8S9S2cG0G1A3G2A3A3A6S3A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [0x706a0; 0x410f0] GS0 [mkVNA U2c 1 (SLit 0)] [mkVNA X3ac 0 (SLit 0); mkVNA X3bc 0 (SLit 0)] [SpineCallocSec4IW1.run3]); [exact SpineCallocSec4IW1.run3__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma ECert3a_0 : ltac2:(tb__ "0|3|
SdS1SaScUfa0S0SbZ410f0S2SbA1A3VGS0;S0S8S9S25Z1S11Z0M0A1M1A3S2S8A1M2A3S0S8S9S2aG0G1A3G2A3A6S3A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [0x410f0] GS0 [mkVNA G3c 1 (SLit 0)] [mkVNA X3a3c 0 (SLit 0)] [SpineCallocSec4IW1.run3a]); [exact SpineCallocSec4IW1.run3a__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma ECert4a_0 : ltac2:(tb__ "0|3|
SdS1SaScUfa0S0SbZ3c614S2SbA1A3VGS0;S0S8S9S26Z1S11Z0M0A1M1A3S2S8A1M2A3S0S8S9S2dG0G1A3S0S8S9S2eG0G1A3G2A3A3A6S3A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [0x3c614] GS0 [mkVNA L3ac 1 (SLit 0)] [mkVNA Y4a0c 0 (SLit 0); mkVNA Y4a1c 0 (SLit 0)] [SpineCallocSec4IW1.run4a]); [exact SpineCallocSec4IW1.run4a__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma ECert4b_0 : ltac2:(tb__ "0|3|
SdS1SaScUfa0S0SbZ3c614S2SbA1A3VGS0;S0S8S9S24Z1S11Z0M0A1M1A3S2S8A1M2A3S0S8S9S2fG0G1A3S0S8S9S30G0G1A3G2A3A3A6S3A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [0x3c614] GS0 [mkVNA CO3bc 1 (SLit 0)] [mkVNA Y4b0c 0 (SLit 0); mkVNA Y4b1c 0 (SLit 0)] [SpineCallocSec4IW1.run4b]); [exact SpineCallocSec4IW1.run4b__runeq | vm_cast_no_check (eq_refl true)]. Qed.

Theorem esec_g3_1h : ltac2:(tb__ "0|8|
S1dS3bS10S18Q40M0A1M1S1bOF_;S32VW;Vst;A2S3cR5A1S34S33S37S5S20S1fR7A1A2A1Z1A2S38Z2Z14A2A2SbSeS36S3aS17G0R6A2A1M2R1A2S34R1S33G2S35S31S17G0S13R7PcM3A2A2A1Z8A2A2A2A2SfSdS7S18Q8A1M4A1S14R8S19G0R2A2A2S4G4A1A3A1F_;Fz;S10S10S6G1A1M5S3dS1eRcA1S17G0R9A2S31S17G0S13RaG3A2A2A1RaR3A5S1aScS1cScS21U1M6Vst;S22S1dS39R1A1LX;RdRcR4RaA8S28R3R2A5R9A3F_;FtY;FrY;Frho'';S10G5S1aScS1cScS21G6Vst;S22S1dR1LX;M7RcRbRaR9A8S29R2R1A5R8A3FtY;FrY;S10G5S1aScS1cScS21G6Vst;S22G7RdRcRbRaA8S23R2R1A5R9A3FtX;FrX;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a Q HUS HKc Hok RUNDEF HCa HCb rX tX.
  eapply esec_g3 with
    (nW := 1%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (AX := (fun X : AA => X)) (AXg := (fun X => eq_refl)) (AXs := (fun X => eq_refl))
    (AXp := (fun X => eq_refl)) (AXb := (fun X => eq_refl)) (D2 := D2c) (U2 := U2c) (X3a := X3ac) (X3b := X3bc) (CS3 := CS3c) (G3 := G3c) (X3a3 := X3a3c) (L3a := L3ac)
    (L3b := L3bc) (CO3b := CO3bc) (T4a := T4ac) (T4b := T4bc) (Y4a0 := Y4a0c) (Y4a1 := Y4a1c) (Y4b0 := Y4b0c) (Y4b1 := Y4b1c) (sLa := sLa) (sLb := sLb) (s4a0 := s4a0)
    (s4a1 := s4a1) (s4b0 := s4b0) (s4b1 := s4b1) (WU2 := WU2_0) (DU2 := DU2_0) (NXU2 := NXU2_0) (HU2 := HU2_0) (Cert3 := Cert3_0) (WC3 := WC3_0) (DC3 := DC3_0)
    (NXC3 := NXC3_0) (HC3 := HC3_0) (FX3a := FX3a_0) (IC3 := IC3_0) (R17 := R17_0) (R10 := R10_0) (BBw := BBw_0) (R11 := R11_0) (R12 := R12_0) (R13 := R13_0)
    (R14 := R14_0) (R15 := R15_0) (XC3 := XC3_0) (SK3 := SK3_0) (FC3 := FC3_0) (FCS3 := FCS3_0) (NXS3 := NXS3_0) (HG3 := HG3_0) (Cert3a := Cert3a_0) (ELa := ELa_0)
    (IDa := IDa_0) (GLa := GLa_0) (FBLa := FBLa_0) (HL3a := HL3a_0) (ELb := ELb_0) (IDb := IDb_0) (GLb := GLb_0) (FBLb := FBLb_0) (HL3b := HL3b_0) (HCOb := HCOb_0)
    (WCOb := WCOb_0) (XCb := XCb_0) (SKb := SKb_0) (FCb := FCb_0) (FXb := FXb_0) (Cert4a := Cert4a_0) (E4a0 := E4a0_0) (I4a0 := I4a0_0) (E4a1 := E4a1_0) (I4a1 := I4a1_0)
    (Cert4b := Cert4b_0) (E4b0 := E4b0_0) (I4b0 := I4b0_0) (E4b1 := E4b1_0) (I4b1 := I4b1_0) (NXEU2 := NXEU2_0) (NXEG3 := NXEG3_0) (NXEL3a := NXEL3a_0)
    (NXECOb := NXECOb_0) (ECert3 := ECert3_0) (ECert3a := ECert3a_0) (ECert4a := ECert4a_0) (ECert4b := ECert4b_0);
    [hw_discharge | exact HUS | exact HKc | exact Hok | exact RUNDEF | exact HCa | exact HCb].
Qed.
End INST.
End SpineCallocSec4IEW1.

