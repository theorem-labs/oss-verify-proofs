(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jz.
From Stdlib Require FunctionalExtensionality.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k6.

(* [comment removed for export] *)
Module SpineMallocSec5JL.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "sobj"; "obj_range"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "DG"; "aa_geom"; "ag_pab"; "@Corelib.Init.Datatypes"; "list"; "nil"; "pair"; "prod"; "fst"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3"; "JGs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jm.SpineMallocSec3IL"; "nx0"; "@Corelib.Init.Logic"; "eq"; "and"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "ulink"; "KcA"; "Kc_ok"; "UStopLeOrPc"; "ustop"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "world"; "assn"; "etriple"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jn.DepotCallS"; "AXK"; "dlink"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger"; "sepZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dblocks"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "secmapsize"; "stopJ_stable"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.SecBump"; "bumpP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jz.SpineMallocSec5IL"; "C5ac"; "C5bc"; "X5ac"; "X5bc"; "EXoa"; "EXob"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "kPtrArrayReserve"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocSec4IL"; "T4ac"; "T4bc"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocSec4IL.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require js.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jz.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.CertMallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SegD_refl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.SecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.SecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jm.SpineMallocSec3IL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineMallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocSec4IL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertMallocSU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jq.SpineMallocSec5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jn.DepotCallS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.js.SpineMallocSec6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jz.SpineMallocSec5IL.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 0. Let st : ustop := UStopLe. Let tmax : Z := 2.
Let GS0 : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3.GS nx0.

Lemma EXZa_0 : ltac2:(tb__ "0|3|
S6S19S2S1eQ40A1M0S2SaG0A1S20S4S0S10S1S13U0Vst;S14S6S2eR1A1LX;R9R8R7R6A8S31R5R4R3A6S23S4R3S33A3S16S2aSeS0S0S5R7R4A2M1A3R3A2S2bR3SfS0S0G1A3A2A2S17S16S2aS36R4A2S2bR4S35A2A2S16S2aS9S8RcA1A1M2R4A2S2bR4S2cG2S37A2A2A2A2F_;F_;F_;Fz;Fo;Fw;Ftp;FrhoE;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a rhoE tp w o z Hw Ho Hz. pose proof (SPA_facts_hold segsA _ rhoE X5ac tp w Hw) as HF. destruct w as [tr [ms md]].
  pose proof (proj2 Hw) as HJ. cbn [w_tr w_cfg cfg_model fst snd] in HJ.
  pose proof (proj1 (Forall_forall _ _) HF _ FXBa_0) as HBR.
  destruct Ho as [<-|[<-|[<-|[]]]].
  - left. exact (ex2_band 0%nat st tmax nx0 Hnx_0 (fun X : AA => bumpP X) A Kc rho a rhoE tp tr md z HJ Hz).
  - left. exact (ex1_band 0%nat st tmax nx0 Hnx_0 (fun X : AA => bumpP X) A Kc rho a rhoE tp tr md z HJ Hz).
  - right. exact (exblk_pab 0%nat st tmax nx0 Hnx_0 (fun X : AA => bumpP X) A Kc rho a rhoE tp tr md z (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) HJ HBR Hz).
Qed.

Theorem depot_call_S_0la : ltac2:(tb__ "0|6|
S20OF_;S6S19S2S1eQ40M0A1M1S21S15S1cVst;S1bA3S15SaS18A1VW;SbS18A1A3F_;S29VW;Vst;A2S1aR6A1S12S1R9S11R7A1A3S2dS1RaS11R8A1A3S7S2S2SaG1A1M2SdS0S0A2M3S23G3R1S27R5A1A3S26R2ScS0S0S1dG0RdA2S28S1dG0S3RePcA2A2A1A4A2F_;Fbn;S25R5RdR4A3S1fS1R11S10S1S13U0M4Vst;S14S24S6S2eR1A1LX;M5R6A2R10RfR5RdA8S2fR4R3A5RcA4F_;F_;Ftp';FrhoX;Frho';FG2;S2G2S1fS1ReS10S1S13G4Vst;S14G5RdRcRbRaA8S31R2R1A5R9A4Ftp;FrhoE;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Proof.
  exact (depot_call_S 0%nat st tmax nx0 Hnx_0 NXG_0 (fun X : AA => bumpP X) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl)
           Htmax_0 X5ac C5ac NXEa_0 FBEa_0 F192a_0 FDEPa_0 FUNWa_0 WX5ra_0 DX5ra_0 SPL1a_0 SPL2a_0 SPL3a_0 SPL4a_0
           s4a_i R4a_i T4a_i HERa_0 HT4a_0 XX4a_0 FBX4a_0 Hchk4a_0 NX4a_0 WG10a_0 WG15a_0 WG12a_0 EXoa FAM4a_0 EXZa_0 NEWOa_0 XPosta_0
           FBT4a_0 XT4a_0 RB1a_0 RB2a_0 nobja PERM_nda_0 PERM_lta_0 PERM_cova_0 PERM_lena_0 MRG1a_0 MRG2a_0 MRG3a_0 MRG4a_0 sda_i ENT5a_0 SID5a_0 R4cova_0).
Qed.

Theorem depot_call_SE_0la : ltac2:(tb__ "0|6|
S6S19S2S1eQ40M0A1M1S20OF_;S15S1cVst;S1bA3S15SaS18A1VW;SbS18A1A3F_;S29VW;Vst;A2S1aR6A1S7S2S2SaG1A1M2SdS0S0A2M3S23G3R1S27R5A1A3S26R2ScS0S0S1dG0RbA2S28S1dG0S3RcPcA2A2A1A4A2F_;Fbn;S25R5RbR4A3S22S1S10S1S13U0M4Vst;S14S24S6S2eR1A1LX;M5R6A2ReRdR5RbA8S2fR4R3A5RaA3F_;F_;Ftp';FrhoX;Frho';FG2;S2G2S22S1S10S1S13G4Vst;S14G5RbRaR9R8A8S31R2R1A5R7A3Ftp;FrhoE;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;").
Proof.
  exact (depot_call_SE 0%nat st tmax nx0 Hnx_0 NXG_0 (fun X : AA => bumpP X) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl)
           Htmax_0 X5ac C5ac NXEa_0 FBEa_0 F192a_0 FDEPa_0 FUNWa_0 WX5ra_0 DX5ra_0 SPL1a_0 SPL2a_0 SPL3a_0 SPL4a_0
           s4a_i R4a_i T4a_i HERa_0 HT4a_0 XX4a_0 FBX4a_0 Hchk4a_0 NX4a_0 WG10a_0 WG15a_0 WG12a_0 EXoa FAM4a_0 EXZa_0 NEWOa_0 XPosta_0
           FBT4a_0 XT4a_0 RB1a_0 RB2a_0 nobja PERM_nda_0 PERM_lta_0 PERM_cova_0 PERM_lena_0 MRG1a_0 MRG2a_0 MRG3a_0 MRG4a_0 sda_i ENT5a_0 SID5a_0 R4cova_0).
Qed.

Theorem sec_g41_0la : ltac2:(tb__ "0|6|
S20OF_;S6S19S2S1eQ40M0A1M1S21S15S1cVst;S1bA3S15SaS18A1VW;SbS18A1A3F_;S29VW;Vst;A2S1aR6A1S12S1R9S11R7A1A3S2dS1RaS11R8A1A3S7S2S2SaG1A1M2SdS0S0A2M3S23G3R1S27R5A1A3S26R2ScS0S0S1dG0RdA2S28S1dG0S3RePcA2A2A1A4A2F_;Fbn;S25R5RdR4A3S1fS1R11S10S1S13U0M4Vst;S14S24S6S2eR1A1LX;M5R6A2R10RfR5RdA8S2fR4R3A5RcA4F_;F_;Ftp';FrhoX;Frho';FG2;S2G2S1fS1ReS10S1S13G4Vst;S14G5RdRcRbRaA8S38R2R1A5R9A4FtX;FrX;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Proof.
  exact (sec_g41 0%nat st tmax nx0 Hnx_0 NXG_0 (fun X : AA => bumpP X) T4ac U4ac X5ac C5ac WU4a_0 DU4a_0 NXU4a_0 HU4a_0 Cert5a_0 depot_call_S_0la).
Qed.

Lemma EXZb_0 : ltac2:(tb__ "0|3|
S6S19S2S1eQ40A1M0S2SaG0A1S20S4S0S10S1S13U0Vst;S14S6R1LX;R9R8R7R6A8S32R5R4R3A6S23S4R3S34A3S16S2aSeS0S0S5R7R4A2M1A3R3A2S2bR3SfS0S0G1A3A2A2S17S16S2aS36R4A2S2bR4S35A2A2S16S2aS9S8RcA1A1M2R4A2S2bR4S2cG2S37A2A2A2A2F_;F_;F_;Fz;Fo;Fw;Ftp;FrhoE;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a rhoE tp w o z Hw Ho Hz. pose proof (SPA_facts_hold segsA _ rhoE X5bc tp w Hw) as HF. destruct w as [tr [ms md]].
  pose proof (proj2 Hw) as HJ. cbn [w_tr w_cfg cfg_model fst snd] in HJ.
  pose proof (proj1 (Forall_forall _ _) HF _ FXBb_0) as HBR.
  destruct Ho as [<-|[<-|[<-|[]]]].
  - left. exact (ex2_band 0%nat st tmax nx0 Hnx_0 (fun X : AA => X) A Kc rho a rhoE tp tr md z HJ Hz).
  - left. exact (ex1_band 0%nat st tmax nx0 Hnx_0 (fun X : AA => X) A Kc rho a rhoE tp tr md z HJ Hz).
  - right. exact (exw_pab 0%nat st tmax nx0 Hnx_0 (fun X : AA => X) A Kc rho a rhoE tp tr md z (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) HJ HBR Hz).
Qed.

Theorem depot_call_S_0lb : ltac2:(tb__ "0|6|
S20OF_;S6S19S2S1eQ40M0A1M1S21S15S1cVst;S1bA3S15SaS18A1VW;SbS18A1A3F_;S29VW;Vst;A2S1aR6A1S12S1R9S11R7A1A3S2dS1RaS11R8A1A3S7S2S2SaG1A1M2SdS0S0A2M3S23G3R1S27R5A1A3S26R2ScS0S0S1dG0RdA2S28S1dG0S3RePcA2A2A1A4A2F_;Fbn;S25R5RdR4A3S1fS1R11S10S1S13U0M4Vst;S14S24S6R1LX;M5R6A2R10RfR5RdA8S30R4R3A5RcA4F_;F_;Ftp';FrhoX;Frho';FG2;S2G2S1fS1ReS10S1S13G4Vst;S14G5RdRcRbRaA8S32R2R1A5R9A4Ftp;FrhoE;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Proof.
  exact (depot_call_S 0%nat st tmax nx0 Hnx_0 NXG_0 (fun X : AA => X) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl)
           Htmax_0 X5bc C5bc NXEb_0 FBEb_0 F192b_0 FDEPb_0 FUNWb_0 WX5rb_0 DX5rb_0 SPL1b_0 SPL2b_0 SPL3b_0 SPL4b_0
           s4b_i R4b_i T4b_i HERb_0 HT4b_0 XX4b_0 FBX4b_0 Hchk4b_0 NX4b_0 WG10b_0 WG15b_0 WG12b_0 EXob FAM4b_0 EXZb_0 NEWOb_0 XPostb_0
           FBT4b_0 XT4b_0 RB1b_0 RB2b_0 nobjb PERM_ndb_0 PERM_ltb_0 PERM_covb_0 PERM_lenb_0 MRG1b_0 MRG2b_0 MRG3b_0 MRG4b_0 sdb_i ENT5b_0 SID5b_0 R4covb_0).
Qed.

Theorem depot_call_SE_0lb : ltac2:(tb__ "0|6|
S6S19S2S1eQ40M0A1M1S20OF_;S15S1cVst;S1bA3S15SaS18A1VW;SbS18A1A3F_;S29VW;Vst;A2S1aR6A1S7S2S2SaG1A1M2SdS0S0A2M3S23G3R1S27R5A1A3S26R2ScS0S0S1dG0RbA2S28S1dG0S3RcPcA2A2A1A4A2F_;Fbn;S25R5RbR4A3S22S1S10S1S13U0M4Vst;S14S24S6R1LX;M5R6A2ReRdR5RbA8S30R4R3A5RaA3F_;F_;Ftp';FrhoX;Frho';FG2;S2G2S22S1S10S1S13G4Vst;S14G5RbRaR9R8A8S32R2R1A5R7A3Ftp;FrhoE;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;").
Proof.
  exact (depot_call_SE 0%nat st tmax nx0 Hnx_0 NXG_0 (fun X : AA => X) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl)
           Htmax_0 X5bc C5bc NXEb_0 FBEb_0 F192b_0 FDEPb_0 FUNWb_0 WX5rb_0 DX5rb_0 SPL1b_0 SPL2b_0 SPL3b_0 SPL4b_0
           s4b_i R4b_i T4b_i HERb_0 HT4b_0 XX4b_0 FBX4b_0 Hchk4b_0 NX4b_0 WG10b_0 WG15b_0 WG12b_0 EXob FAM4b_0 EXZb_0 NEWOb_0 XPostb_0
           FBT4b_0 XT4b_0 RB1b_0 RB2b_0 nobjb PERM_ndb_0 PERM_ltb_0 PERM_covb_0 PERM_lenb_0 MRG1b_0 MRG2b_0 MRG3b_0 MRG4b_0 sdb_i ENT5b_0 SID5b_0 R4covb_0).
Qed.

Theorem sec_g41_0lb : ltac2:(tb__ "0|6|
S20OF_;S6S19S2S1eQ40M0A1M1S21S15S1cVst;S1bA3S15SaS18A1VW;SbS18A1A3F_;S29VW;Vst;A2S1aR6A1S12S1R9S11R7A1A3S2dS1RaS11R8A1A3S7S2S2SaG1A1M2SdS0S0A2M3S23G3R1S27R5A1A3S26R2ScS0S0S1dG0RdA2S28S1dG0S3RePcA2A2A1A4A2F_;Fbn;S25R5RdR4A3S1fS1R11S10S1S13U0M4Vst;S14S24S6R1LX;M5R6A2R10RfR5RdA8S30R4R3A5RcA4F_;F_;Ftp';FrhoX;Frho';FG2;S2G2S1fS1ReS10S1S13G4Vst;S14G5RdRcRbRaA8S39R2R1A5R9A4FtX;FrX;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Proof.
  exact (sec_g41 0%nat st tmax nx0 Hnx_0 NXG_0 (fun X : AA => X) T4bc U4bc X5bc C5bc WU4b_0 DU4b_0 NXU4b_0 HU4b_0 Cert5b_0 depot_call_S_0lb).
Qed.
End INST.
End SpineMallocSec5JL.

(* [comment removed for export] *)
Module SpineMallocSecE3.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "False"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_setS"; "leafA"; "la_state"; "entailsA"; "ax_base"; "mkLeafA"; "xr_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "valuation"; "sv"; "sprop"; "ss_next"; "ss_facts"; "rw"; "cell"; "SLit"; "rm"; "swf"; "sprop_below"; "eval"; "ss_objs"; "holds"; "rl"; "obj_range"; "DUnknown"; "mkObj"; "SPNot"; "SVar"; "odefault"; "ranges_disjoint"; "sstate"; "DZero"; "@Corelib.Init.Datatypes"; "list"; "bool"; "true"; "cons"; "nil"; "prod"; "pair"; "option"; "app"; "Some"; "nat"; "length"; "None"; "andb"; "S"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "LQA"; "jpredA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_geom"; "aa_sec"; "ageom"; "sec_chunk"; "aa_Km"; "aa_depot"; "DG"; "aa_ptr_committed"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "ulink"; "UStopLeOrPc"; "ustop"; "Kc_ok"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "AE_A"; "mem_keptA"; "L_malloc_ok"; "JL_malloc_ok"; "Posts_malloc"; "V_RES"; "base_sv"; "@Stdlib.Lists.List"; "In"; "forallb"; "incl"; "existsb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3"; "skel"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "world"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "div"; "lt"; "of_nat"; "eqb"; "leb"; "ltb"; "modulo"; "mul"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "secmapsize"; "stopJ_stable"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP"; "MSENT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "Sh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocST"; "O_1"; "carveS"; "O_2"; "Pret_ms"; "BR"; "Pret_mz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "LQPA"; "jpostA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.CertMallocSV"; "L3"; "F_A"; "O_3"; "O_UBs"; "B3"; "F_par"; "O_3b"; "perm7"; "B4"; "F_B"; "PGST"; "UBs"; "a2e6"; "a2e8"; "osplit"; "BP9"; "F_g7"; "F_g8"; "F_g9"; "L3b"; "O_4z"; "RSF"; "a0e7"; "a2e7"; "fx8"; "ic_c1"; "ic_c2"; "ic_nch"; "ic_nres"; "ic_pg"; "ic_rs"; "mc_cptr"; "mc_idx"; "mc_magic"; "mc_map"; "mc_ms"; "mc_ns"; "mc_size"; "mc_sizehi"; "mc_state"; "mc_type"; "sel7"; "xc_map";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger"; "sepZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dblocks"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.SecOKInv"; "bumpV"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3"; "SKEL0"; "range_noband"; "JGs"; "GS"; "slink"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "wsub"; "wsub_get"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jz.SpineMallocSec7"; "idxsF"; "idxsU"; "S2F"; "KUB"; "XF_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Str_memsetZ"; "Pre_mszA"; "Posts_mszA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "nodupN"; "select"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "ltb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "RsSymJump"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.CertMallocSS"; "nxS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertMallocSU"; "DPENT"; "F_g4"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall"; "isSome"; "omrg"; "oreb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jn.DepotCallS"; "AXK"; "dlink"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jz.SpineMallocSec6L"; "F_low"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "merge_objs_at"; "rebase_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM"; "IMG_M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocSec2"; "IMG_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k4.SpineMallocSecE3.SEC6E"; "slink_refl_of"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA EntailA CFGA GlueA GlueA2 SummaryA SysCallA MmapA MmapFixedA LedgerA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require MallocInv.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require io.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocS9 RebuildM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SpineMallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.RebuildN.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import MmapSymA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require id.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocSec SpineMallocSec2 SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jl.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.CertMallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.id.CertMallocSN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocSec OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocSec2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.SegD_cost OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.LedgerLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.InvD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.DepotK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.SecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SecReveal OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.InvReveal OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import EnsureMapA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ii.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.SecBump.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import SecLog2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require id.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ii.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jl.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jz.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jm.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jb.InvEnsure OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertMallocSU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineMallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jq.SpineMallocSec5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.id.DepotKP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jn.DepotCallS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.CertMallocSV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.RebuildS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jz.SpineMallocSec6L OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jz.SpineMallocSec7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jm.SpineMallocSecE1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jq.SpineMallocSecE2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require js.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jz.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jm.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jq.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.js.SpineMallocSec6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jz.SpineMallocSec6L OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jz.SpineMallocSec7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jm.SpineMallocSecE1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jq.SpineMallocSecE2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac rr X := intros; eapply X; revgoals; [> eassumption ..].

Section SEC6E.
Variable nW : nat. Variable st : ustop. Variable tmax : Z.
Let W : list ulink := Wcan nW.
Let segs : list Segment := segsA.
Variable nx : positive.
Hypothesis Hnx : ltac2:(tb__ "0|0|
S0S37SccVW;Vst;Vtmax;A3Vnx;A3").
Hypothesis NXG : ltac2:(tb__ "0|0|
S0S28S73ScfVnx;A2S29A3").
Let GS : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3.GS nx.
Let JG (BX : AA -> AA) : AA -> KcA -> valuation -> word -> jpredA := ltac2:(tb__ "0|0|
Sb8VnW;Vst;Vnx;VBX;A4").

Lemma ems_call : ltac2:(tb__ "0|7|
S3fS3fF_;S6S6S6S6S27S8A1M0SbcS27SeA1M1S0G0R3S2aS8ScR4ScbA2S2bS8A1A3A3S3dSfS27S39Q40A1M2A1M3S3eVsegs;S79R3A3S64Vsegs;S3bVsegs;R4RaR3R2A5S3cVsegs;R4S79R3R2R8A6A3F_;Ftp;Frho;FJx;S0S37S12S5R7A1A1S79A3S0S2eG1A1S84RaR8R5A3S30G1R4A2A3S0S28S83RbR9R6R5S48S8S6S9R7A4A5S29A3S0S6S85R7RaR9RcR6A5RbA3S0S28S5bS11S19S12S5RdA1M4A1A1M5S13G4A1A3S29A3S0S28S5bS11G5S13S5ReA1A1A3S29A3S0S28S73VGS;S12S5RfA1A1A2S29A3S3fS4bSfG2G3S65OF_;S72VW;Vst;A2S4fR6A1SfG3S64Vsegs;S3bVsegs;VJG;R1bRaR9R8R7A5M6S82R19S13S5R1aA1A1A2R2R1A5R5A3FtpY;FrhoY;SfS64Vsegs;S3bVsegs;G6R1aR1R6A5R5A3FrhoX;F_;F_;F_;FQ;Ftp;Fa;Frho;FKc;FA;F_;F_;F_;F_;F_;F_;F_;F_;F_;FR;Fs;FPosts;FPret;FPre;FT;FCM;FBX;").
Proof.
  intros BX CM T Pre Pret Posts s R HPosts Hsum NPre He Hchk HT FBC FBT NXC A Kc rho a tp Q HUS HKc HD rhoX.
  pose proof (JGs_stable nW st tmax nx Hnx NXG BX A Kc rho a HUS HKc) as HST.
  set (Jf := (fun (_ : valuation) t tr md => JG BX A Kc rho a rhoX t tr md) : jpredA).
  assert (Jf_st : stableA segs NF Jf).
  { intros r r' t tr md md' Hag Hme HJ. unfold Jf in *. eapply HST; [apply agree_below_refl | exact Hme | exact HJ]. }
  apply (etriple_pre_pure segs _ _ (Forall (holds rhoX) (ss_facts (ax_S CM)))).
  { intros w Hw. exact (SPA_facts_hold segs _ rhoX CM tp w Hw). }
  intros HFC.
  apply (call_completeA segs (JG BX A Kc rho a) Jf Jf (JG BX A Kc rho a) CM Pre s R Posts Q rhoX tp He Hchk).
  - intros rho1 tp1. rewrite NPre. exact (Hsum Jf rho1 tp1 Jf_st).
  - intros tr ms md Hsm HJ. exact HJ.
  - intros Lf rho' rhoL tpL tr ms md tr' md' HinL Hsm HJ HLK HJ'. unfold Jf in HJ'.
    eapply HST; [| apply mat_equiv_refl | exact HJ'].
    eapply agree_below_le; [apply Pos.leb_le; exact NXC | exact (proj1 HLK)].
  - intros Lf rho' tpL HinL Hag. rewrite HPosts in HinL. destruct HinL as [<-|[]]. cbn [la_state]. rewrite HT.
    eapply etriple_conseq; [intros w Hw | intros w Hw; exact Hw | apply (HD rho' tpL)].
    apply SPA_refacts; [exact Hw | exact FBT |]. intros _.
    exact (Forall_holds_agree _ rhoX rho' _ Hag FBC HFC).
Qed.

Definition slink_refl_of (rho : valuation) (a : word) : Prop := ltac2:(tb__ "0|3|
S36S1S66S78S38Q40M0Va;A2A1M1R1A2S69R1S67G1S68S71S38G0S14Vrho;PcA2A2A1Z8A2A2A2A2S2S0S2eS39Q8A1M2A1S17Vrho;S3aG0R2A2A2S33G2A1A3A1F_;Fz;").
Lemma slink_refl : ltac2:(tb__ "0|1|
SfS39Q40M0A1SdbR2R1A2SbaS38G0R2A2S71S38G0S14R3PcA2A2A1R3R3A4F_;Fa;Frho;").
Proof. intros rho a RD. split; [intros i; reflexivity|]. split; [intros l; reflexivity|]. split; [intros x; left; reflexivity | exact RD]. Qed.

Section G41E.
Variable BX : AA -> AA.
Variables (T4 U4 X5 C5 : axst).
Hypothesis WU4 : ltac2:(tb__ "0|0|
S0S28S18S5VU4;A1A1S29A3").
Hypothesis DU4 : ltac2:(tb__ "0|4|
S0S2eS2cS27S2cS10S10A2M0A1M1S27S11A1M2A2M3A1S77S5VT4;A1S5VU4;A1A2S30G3S2dG1G2S2bG0A1SceVnx;A1A4A2A3").
Hypothesis NXU4 : ltac2:(tb__ "0|0|
S0S37S12S5VU4;A1A1S12S5VT4;A1A1A3").
Hypothesis HU4 : ltac2:(tb__ "0|0|
S0S6S7VT4;S5VU4;A1A2VU4;A3").
Hypothesis Cert5 : ltac2:(tb__ "0|1|
S0S28S60S70Ufa0S2aS36ScdS2bS36A1A3VGS;S2aS6VU4;S2bS6A1M0A3S2aS6VX5;G0A3A6S29A3").
Hypothesis NXE5 : ltac2:(tb__ "0|0|
S0S28S73VGS;S12S5VU4;A1A1A2S29A3").
Hypothesis ECert5 : ltac2:(tb__ "0|3|
S0S28S61S70Ufa0S2aS36ScdS2bS36A1A3VGS;S2aS5eS5fVU4;Z1S16Z0M0A1M1A3S2bS5eA1M2A3S2aS5eS5fVX5;G0G1A3G2A3A6S29A3").
Hypothesis HDSE : ltac2:(tb__ "0|4|
S3fS4bSfS39Q40M0A1M1S65OF_;S0S4eVst;S4dA3S0S27S4cA1VW;S2bS4cA1A3F_;S72VW;Vst;A2S4fR6A1S46SfSfS27G1A1M2S2cS36S36A2M3S5aG3R1Sb4R5A1A3Sb3R2S2dS36S36S38G0RbA2S71S38G0S14RcPcA2A2A1A4A2F_;Fbn;Sd4R5RbR4A3S64Vsegs;S3bVsegs;VJG;Sd3VBX;R6A2ReRdR5RbA5VC5;R4R3A5RaA3F_;F_;Ftp';FrhoX;Frho';FG2;SfG2S64Vsegs;S3bVsegs;VJG;VBX;RbRaR9R8A5VX5;R2R1A5R7A3Ftp;FrhoE;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;").

Theorem esec_g41 : ltac2:(tb__ "0|4|
S3fS4bSfS39Q40M0A1M1S65OF_;S0S4eVst;S4dA3S0S27S4cA1VW;S2bS4cA1A3F_;S72VW;Vst;A2S4fR6A1S46SfSfS27G1A1M2S2cS36S36A2M3S5aG3R1Sb4R5A1A3Sb3R2S2dS36S36S38G0RbA2S71S38G0S14RcPcA2A2A1A4A2F_;Fbn;Sd4R5RbR4A3S64Vsegs;S3bVsegs;VJG;Sd3VBX;R6A2ReRdR5RbA5VC5;R4R3A5RaA3F_;F_;Ftp';FrhoX;Frho';FG2;SfG2S64Vsegs;S3bVsegs;VJG;VBX;RbRaR9R8A5VT4;R2R1A5R7A3FtX;FrX;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;").
Proof.
  assert (USED := (WU4, DU4, NXU4, HU4, Cert5, NXE5, ECert5, HDSE)); clear USED.
  intros A Kc rho a Q HW HUS HKc Hcont rX tX.
  pose proof (JGs_stable nW st tmax nx Hnx NXG BX A Kc rho a HUS HKc) as HST.
  apply (etc_pre (SPA segs (JG BX A Kc rho a) U4 rX tX)); [intros w Hw; exact (RSU4 nW st tmax nx Hnx T4 U4 WU4 DU4 NXU4 HU4 BX A Kc rho a rX tX w Hw)|].
  apply (ecfg_1 nx [DPENT] U4 X5 (JG BX A Kc rho a) Q tX rX HST NXE5 ECert5). intros rE.
  exact (HDSE A Kc rho a Q HW HUS HKc Hcont rE tX).
Qed.
End G41E.

Section G43E.
Variable BX : AA -> AA.
Hypothesis BXg : ltac2:(tb__ "0|0|
S3fS0S42S40VBX;R1A1A1S40R1A1A3FX;").
Variable PX : list sobj.
Variable FXP : list sprop.
Hypothesis PX_noband : ltac2:(tb__ "0|2|
S3fS4bSfS39Q40A1M0SfS27G0A1S27S7bA1S7aVJG;VBX;R8R7R6R5R4R3R2R1A9S49S11S1cR5A1VFXP;A3S27SeA1S0S27S2cS2cS10S10A2S10A2M1A1S48SeG1S63R1A4S48SeG1S63VPX;A4A3S49SeSeSb7S1eR9R1A2A1Lo;R2A3F_;Fl;F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;").
Variables (C5 C5A C5B Y6A Y6B E6 CT6 CO6 T6 : axst) (sA sB s6 : wsub) (R6 : list sobj).
Let D6 : axst := ltac2:(tb__ "0|0|
S82VT6;S13S5VCO6;A1A1A2").
Hypothesis HC5A : ltac2:(tb__ "0|0|
S0S6S62S89Vnx;A1VC5;A2VC5A;A3").
Hypothesis HC5B : ltac2:(tb__ "0|0|
S0S6S62S91Vnx;A1VC5;A2VC5B;A3").
Hypothesis FBA : ltac2:(tb__ "0|0|
S0S28S5bS11S19S12S5VC5;A1A1A1S89Vnx;A1A3S29A3").
Hypothesis FBB : ltac2:(tb__ "0|0|
S0S28S5bS11S19S12S5VC5;A1A1A1S91Vnx;A1A3S29A3").
Hypothesis Cert6A : ltac2:(tb__ "0|1|
S0S28S60S70Ufa0S2aS36S74S2bS36A1A3VGS;S2aS6VC5A;S2bS6A1M0A3S2aS6VY6A;G0A3A6S29A3").
Hypothesis Cert6B : ltac2:(tb__ "0|1|
S0S28S60S70Ufa0S2aS36S74S2bS36A1A3VGS;S2aS6VC5B;S2bS6A1M0A3S2aS6VY6B;G0A3A6S29A3").
Hypothesis E6A : ltac2:(tb__ "0|0|
S0S28SaVY6A;VE6;VsA;A3S29A3").
Hypothesis I6A : ltac2:(tb__ "0|0|
S0S28SbbVsA;VGS;A2S29A3").
Hypothesis E6B : ltac2:(tb__ "0|0|
S0S28SaVY6B;VE6;VsB;A3S29A3").
Hypothesis I6B : ltac2:(tb__ "0|0|
S0S28SbbVsB;VGS;A2S29A3").
Hypothesis WC6 : ltac2:(tb__ "0|0|
S0S28S18S5VCT6;A1A1S29A3").
Hypothesis DF6 : ltac2:(tb__ "0|4|
S0S2eS2cS27S2cS10S10A2M0A1M1S27S11A1M2A2M3A1S77S5VE6;A1S5VCT6;A1A2S30G3S2dG1G2S2aG0S2dS10S10S94Vnx;A1S88A4S2bG0A1A3S2bS11A1A4A2A3").
Hypothesis NX6 : ltac2:(tb__ "0|0|
S0S37S12S5VCT6;A1A1S12S5VE6;A1A1A3").
Hypothesis HC6 : ltac2:(tb__ "0|0|
S0S6S7VE6;S5VCT6;A1A2VCT6;A3").
Hypothesis SK6 : ltac2:(tb__ "0|1|
S0S27S2cS2cS10S10A2S10A2M0A1S48SeG0S63S1bS5VCT6;A1A1A4S48SeG0S63S2fSeS2aSeS7eVnx;A1S2aSeS7cVnx;A1S2bSeA1A3A3S2fSeSb6VnW;Vnx;A2VPX;A3A3A4A3").
Hypothesis FC6 : ltac2:(tb__ "0|0|
S5cS11S2fS11S52VW;Vst;A2S51S50A1A3S13S5VCT6;A1A1A3").
Hypothesis FX6 : ltac2:(tb__ "0|0|
S5cS11VFXP;S13S5VCT6;A1A1A3").
Hypothesis XC6 : ax_X CT6 = [].
Hypothesis HCO6 : ltac2:(tb__ "0|0|
S0S6S7dVCT6;S20S8cVnx;A1S16Z0A1S88S2bS15A1S1fA5A2VCO6;A3").
Hypothesis WCO6 : ltac2:(tb__ "0|0|
S0S28S18S5VCO6;A1A1S29A3").
Hypothesis He6 : ltac2:(tb__ "0|1|
S0S2eS27SeA1M0A1S84VCO6;S75Vs6;A3S30G0VR6;A2A3").
Hypothesis Hchk6 : ltac2:(tb__ "0|0|
S0S28S83VCO6;S75Vs6;VR6;S48S8S6S9S76A4A5S29A3").
Hypothesis HT6 : ltac2:(tb__ "0|0|
S0S6S85Vs6;S75S7fVCO6;VR6;A5VT6;A3").
Hypothesis FBC6 : ltac2:(tb__ "0|1|
S0S28S5bS11S19S12S5VCO6;A1M0A1A1S13G0A1A3S29A3").
Hypothesis FBT6 : ltac2:(tb__ "0|0|
S0S28S5bS11S19S12S5VT6;A1A1A1S13S5VCO6;A1A1A3S29A3").
Hypothesis NXC6 : ltac2:(tb__ "0|0|
S0S28S73VGS;S12S5VCO6;A1A1A2S29A3").
Hypothesis NXE6A : ltac2:(tb__ "0|0|
S0S28S73VGS;S12S5VC5A;A1A1A2S29A3").
Hypothesis ECert6A : ltac2:(tb__ "0|3|
S0S28S61S70Ufa0S2aS36S74S2bS36A1A3VGS;S2aS5eS5fVC5A;Z1S16Z0M0A1M1A3S2bS5eA1M2A3S2aS5eS5fVY6A;G0G1A3G2A3A6S29A3").
Hypothesis NXE6B : ltac2:(tb__ "0|0|
S0S28S73VGS;S12S5VC5B;A1A1A2S29A3").
Hypothesis ECert6B : ltac2:(tb__ "0|3|
S0S28S61S70Ufa0S2aS36S74S2bS36A1A3VGS;S2aS5eS5fVC5B;Z1S16Z0M0A1M1A3S2bS5eA1M2A3S2aS5eS5fVY6B;G0G1A3G2A3A6S29A3").
Lemma RS6' : ltac2:(tb__ "0|1|
S3fS4bSfS39Q40A1M0SfS27G0A1S65S0S4eVst;S4dA3S0S27S4cA1VW;S2bS4cA1A3F_;S3bVsegs;VJG;VBX;R8R7R6R5A5VE6;R4R3R2A6S3bVsegs;VJG;VBX;R9R8R7R6A5VCT6;R5R4R3A6F_;F_;Fw;Ftp;FrhoX;Fa;Frho;FKc;FA;").
Proof. rr RS6. Qed.
Lemma HBL6' : ltac2:(tb__ "0|b|
S3fS4bSfS39Q40M0A1M1SfS27G1A1S65S3bVsegs;VJG;VBX;R7R6R5R4A5VCT6;R3R2R1A6S1S66S78S38G0R5A2A1M2S38G0S1aR4S8cVnx;A1M3A2A2M4A2S1S66S67G4S38G0S1aR4S88A2A2A2S67G2S68S71S38G0S14R6PcA2A2A1Z8A2A2A2S1S27SeA1M5S0S27S2cS2cS10S10A2S10A2M6A1M7S48SeG6S63R1A4M8S48SeG6S63S2aSeS7eVnx;A1S2aSeS7cVnx;A1S2bSeA1A3A3A4A3S49SeSeS24S1eR7R1A2S2dS36S36S38G0S1aR7G3A2A2M9S67G9S38G0S1aR7S88A2A2A2A4A2Lo;R2A3MaF_;Fl;G5S0G7G8S48SeG6S63VPX;A4A3GaF_;Fl;A2A2A2F_;Fw;Ftp;FrhoX;Fa;Frho;FKc;FA;").
Proof. rr HBL6. Qed.

Theorem esec_g43 : ltac2:(tb__ "0|5|
S3fS4bSfS39Q40M0A1M1S65OF_;S0S4eVst;S4dA3S0S27S4cA1VW;S2bS4cA1A3F_;S72VW;Vst;A2S4fR6A1S36S1S66S78S38G0R6A2A1M2R1A2S69R1S67G2S68S71S38G0S14R7PcA2A2A1Z8A2A2A2A2S2S0S2eS39Q8A1M3A1S17R8S3aG0R2A2A2S33G3A1A3A1F_;Fz;SfS27G1A1M4S64Vsegs;S3bVsegs;VJG;VBX;RbRaR9R8A5VD6;R2R1A5R7A3FtpY;FrhoY;SfG4S64Vsegs;S3bVsegs;VJG;VBX;RcRbRaR9A5VC5;R2R1A5R8A3FtX;FrX;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;").
Proof.
  assert (USED := (BXg, PX_noband, HC5A, HC5B, FBA, FBB, Cert6A, Cert6B, E6A, I6A, E6B, I6B, WC6, DF6, NX6, HC6, SK6, FC6, FX6, XC6, HCO6, WCO6, He6, Hchk6, HT6, FBC6, FBT6, NXC6, NXE6A, ECert6A, NXE6B, ECert6B)); clear USED.
  intros A Kc rho a Q HW HUS HKc RUNDEF HCONT rX tX.
  pose proof (JGs_stable nW st tmax nx Hnx NXG BX A Kc rho a HUS HKc) as HST.
  pose proof (slink_refl rho a RUNDEF) as SL.
  assert (TAIL : forall rE tE, etriple segs (SPA segs (JG BX A Kc rho a) E6 rE tE) Q).
  { intros rE tE.
    apply (ems_step nW st tmax nx Hnx NXG BX BXg E6 CT6 CO6 T6 (B3 nx) L3 [O_2 nx; O_1 nx] PX Pre_memsetA Pret_ms Posts_memsetA s6 R6 eq_refl
             (fun Jx r0 t0 Hs => memset_sumA_ex Jx r0 t0 Hs) eq_refl RS6' HBL6' SK6 FC6 XC6 HCO6 WCO6 He6 Hchk6 HT6 FBC6 FBT6 NXC6
             A Kc rho rho a tE Q HW HUS HKc SL).
    intros rhoY tpY. exact (HCONT rhoY tpY). }
  apply (etc_pre (fun w => SPA segs (JG BX A Kc rho a) C5A rX tX w \/ SPA segs (JG BX A Kc rho a) C5B rX tX w)); [intros w Hw|].
  { destruct w as [tr [ms md]]. destruct (diamond_hold nW st tmax nx Hnx BX A Kc rho a rX tX tr md BXg (proj2 Hw)) as [FA|FB]; [left; rewrite <- HC5A | right; rewrite <- HC5B].
    - split; [|exact (proj2 Hw)]. exact (smatchA_add_facts segs rX tX (F_A nx) _ _ (proj1 Hw) FA FBA).
    - split; [|exact (proj2 Hw)]. exact (smatchA_add_facts segs rX tX (F_B nx) _ _ (proj1 Hw) FB FBB). }
  apply etriple_disj.
  - apply (ecfg_1 nx [MSENT] C5A Y6A (JG BX A Kc rho a) Q tX rX HST NXE6A ECert6A). intros rE.
    apply (etc_pre (SPA segs (JG BX A Kc rho a) E6 (rho_sub rE sA) tX)); [intros w Hw; exact (join4 nW st tmax nx Hnx NXG BX A Kc rho a Y6A E6 sA rE tX w HUS HKc E6A I6A Hw) | apply TAIL].
  - apply (ecfg_1 nx [MSENT] C5B Y6B (JG BX A Kc rho a) Q tX rX HST NXE6B ECert6B). intros rE.
    apply (etc_pre (SPA segs (JG BX A Kc rho a) E6 (rho_sub rE sB) tX)); [intros w Hw; exact (join4 nW st tmax nx Hnx NXG BX A Kc rho a Y6B E6 sB rE tX w HUS HKc E6B I6B Hw) | apply TAIL].
Qed.
End G43E.

Section G43LE.
Variable BX : AA -> AA.
Hypothesis BXg : ltac2:(tb__ "0|0|
S3fS0S42S40VBX;R1A1A1S40R1A1A3FX;").
Variable PX : list sobj.
Variable FXP : list sprop.
Hypothesis PX_noband : ltac2:(tb__ "0|2|
S3fS4bSfS39Q40A1M0SfS27G0A1S27S7bA1S7aVJG;VBX;R8R7R6R5R4R3R2R1A9S49S11S1cR5A1VFXP;A3S27SeA1S0S27S2cS2cS10S10A2S10A2M1A1S48SeG1S63R1A4S48SeG1S63VPX;A4A3S49SeSeSb7S1eR9R1A2A1Lo;R2A3F_;Fl;F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;").
Variables (C5 C5A Y6A E6 CT6 CO6 T6 : axst) (sA s6 : wsub) (R6 : list sobj).
Let D6 : axst := ltac2:(tb__ "0|0|
S82VT6;S13S5VCO6;A1A1A2").
Hypothesis FLOW : ltac2:(tb__ "0|0|
S5aS11Sd5Vnx;A1S13S5VC5;A1A1A3").
Hypothesis HC5A : ltac2:(tb__ "0|0|
S0S6S62S89Vnx;A1VC5;A2VC5A;A3").
Hypothesis FBA : ltac2:(tb__ "0|0|
S0S28S5bS11S19S12S5VC5;A1A1A1S89Vnx;A1A3S29A3").
Hypothesis Cert6A : ltac2:(tb__ "0|1|
S0S28S60S70Ufa0S2aS36S74S2bS36A1A3VGS;S2aS6VC5A;S2bS6A1M0A3S2aS6VY6A;G0A3A6S29A3").
Hypothesis E6A : ltac2:(tb__ "0|0|
S0S28SaVY6A;VE6;VsA;A3S29A3").
Hypothesis I6A : ltac2:(tb__ "0|0|
S0S28SbbVsA;VGS;A2S29A3").
Hypothesis WC6 : ltac2:(tb__ "0|0|
S0S28S18S5VCT6;A1A1S29A3").
Hypothesis DF6 : ltac2:(tb__ "0|4|
S0S2eS2cS27S2cS10S10A2M0A1M1S27S11A1M2A2M3A1S77S5VE6;A1S5VCT6;A1A2S30G3S2dG1G2S2aG0S2dS10S10S94Vnx;A1S88A4S2bG0A1A3S2bS11A1A4A2A3").
Hypothesis NX6 : ltac2:(tb__ "0|0|
S0S37S12S5VCT6;A1A1S12S5VE6;A1A1A3").
Hypothesis HC6 : ltac2:(tb__ "0|0|
S0S6S7VE6;S5VCT6;A1A2VCT6;A3").
Hypothesis SK6 : ltac2:(tb__ "0|1|
S0S27S2cS2cS10S10A2S10A2M0A1S48SeG0S63S1bS5VCT6;A1A1A4S48SeG0S63S2fSeS2aSeS7eVnx;A1S2aSeS7cVnx;A1S2bSeA1A3A3S2fSeSb6VnW;Vnx;A2VPX;A3A3A4A3").
Hypothesis FC6 : ltac2:(tb__ "0|0|
S5cS11S2fS11S52VW;Vst;A2S51S50A1A3S13S5VCT6;A1A1A3").
Hypothesis FX6 : ltac2:(tb__ "0|0|
S5cS11VFXP;S13S5VCT6;A1A1A3").
Hypothesis XC6 : ax_X CT6 = [].
Hypothesis HCO6 : ltac2:(tb__ "0|0|
S0S6S7dVCT6;S20S8cVnx;A1S16Z0A1S88S2bS15A1S1fA5A2VCO6;A3").
Hypothesis WCO6 : ltac2:(tb__ "0|0|
S0S28S18S5VCO6;A1A1S29A3").
Hypothesis He6 : ltac2:(tb__ "0|1|
S0S2eS27SeA1M0A1S84VCO6;S75Vs6;A3S30G0VR6;A2A3").
Hypothesis Hchk6 : ltac2:(tb__ "0|0|
S0S28S83VCO6;S75Vs6;VR6;S48S8S6S9S76A4A5S29A3").
Hypothesis HT6 : ltac2:(tb__ "0|0|
S0S6S85Vs6;S75S7fVCO6;VR6;A5VT6;A3").
Hypothesis FBC6 : ltac2:(tb__ "0|1|
S0S28S5bS11S19S12S5VCO6;A1M0A1A1S13G0A1A3S29A3").
Hypothesis FBT6 : ltac2:(tb__ "0|0|
S0S28S5bS11S19S12S5VT6;A1A1A1S13S5VCO6;A1A1A3S29A3").
Hypothesis NXC6 : ltac2:(tb__ "0|0|
S0S28S73VGS;S12S5VCO6;A1A1A2S29A3").
Hypothesis NXE6A : ltac2:(tb__ "0|0|
S0S28S73VGS;S12S5VC5A;A1A1A2S29A3").
Hypothesis ECert6A : ltac2:(tb__ "0|3|
S0S28S61S70Ufa0S2aS36S74S2bS36A1A3VGS;S2aS5eS5fVC5A;Z1S16Z0M0A1M1A3S2bS5eA1M2A3S2aS5eS5fVY6A;G0G1A3G2A3A6S29A3").

Theorem esec_g43_low : ltac2:(tb__ "0|5|
S3fS4bSfS39Q40M0A1M1S65OF_;S0S4eVst;S4dA3S0S27S4cA1VW;S2bS4cA1A3F_;S72VW;Vst;A2S4fR6A1S36S1S66S78S38G0R6A2A1M2R1A2S69R1S67G2S68S71S38G0S14R7PcA2A2A1Z8A2A2A2A2S2S0S2eS39Q8A1M3A1S17R8S3aG0R2A2A2S33G3A1A3A1F_;Fz;SfS27G1A1M4S64Vsegs;S3bVsegs;VJG;VBX;RbRaR9R8A5VD6;R2R1A5R7A3FtpY;FrhoY;SfG4S64Vsegs;S3bVsegs;VJG;VBX;RcRbRaR9A5VC5;R2R1A5R8A3FtX;FrX;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;").
Proof.
  assert (USED := (BXg, PX_noband, FLOW, HC5A, FBA, Cert6A, E6A, I6A, WC6, DF6, NX6, HC6, SK6, FC6, FX6, XC6, HCO6, WCO6, He6, Hchk6, HT6, FBC6, FBT6, NXC6, NXE6A, ECert6A)); clear USED.
  intros A Kc rho a Q HW HUS HKc RUNDEF HCONT rX tX.
  pose proof (JGs_stable nW st tmax nx Hnx NXG BX A Kc rho a HUS HKc) as HST.
  pose proof (slink_refl rho a RUNDEF) as SL.
  assert (TAIL : forall rE tE, etriple segs (SPA segs (JG BX A Kc rho a) E6 rE tE) Q).
  { intros rE tE.
    apply (ems_step nW st tmax nx Hnx NXG BX BXg E6 CT6 CO6 T6 (B3 nx) L3 [O_2 nx; O_1 nx] PX Pre_memsetA Pret_ms Posts_memsetA s6 R6 eq_refl
             (fun Jx r0 t0 Hs => memset_sumA_ex Jx r0 t0 Hs) eq_refl
             (RS6 nW st tmax nx Hnx BX E6 CT6 WC6 DF6 NX6 HC6) (HBL6 nW st tmax nx Hnx BX PX FXP PX_noband E6 CT6 NX6 FX6)
             SK6 FC6 XC6 HCO6 WCO6 He6 Hchk6 HT6 FBC6 FBT6 NXC6
             A Kc rho rho a tE Q HW HUS HKc SL).
    intros rhoY tpY. exact (HCONT rhoY tpY). }
  apply (etc_pre (SPA segs (JG BX A Kc rho a) C5A rX tX)); [intros w Hw|].
  { pose proof (proj1 (Forall_forall _ _) (SPA_facts_hold segsA _ rX C5 tX w Hw) _ FLOW) as HL.
    destruct w as [tr [ms md]]. rewrite <- HC5A.
    split; [|exact (proj2 Hw)]. exact (smatchA_add_facts segs rX tX (F_A nx) _ _ (proj1 Hw) (low_FA nW st tmax nx Hnx BX A Kc rho a rX tX tr md BXg (proj2 Hw) HL) FBA). }
  apply (ecfg_1 nx [MSENT] C5A Y6A (JG BX A Kc rho a) Q tX rX HST NXE6A ECert6A). intros rE.
  apply (etc_pre (SPA segs (JG BX A Kc rho a) E6 (rho_sub rE sA) tX)); [intros w Hw; exact (join4 nW st tmax nx Hnx NXG BX A Kc rho a Y6A E6 sA rE tX w HUS HKc E6A I6A Hw) | apply TAIL].
Qed.
End G43LE.

Lemma hint_low_etriple : ltac2:(tb__ "0|9|
S3fS3fF_;S6S6S27S11A1M0S0S28S18S5R2A1A1S29A3S0S2eS2cS27S2cS10S10A2M1A1M2G0A2M3A1S77S5R4A1M4S5R3A1A2S30G3S2dG2G0S2bG1A1R2A4A2A3S0S37S12G4A1S12S5R5A1M5A1A3S0S6S7R6G5A2R5A3S5aS11Sd5Vnx;A1M6S13S5R7A1A1A3S3fS4bSfS39Q40A1M7SfS27G7A1M8S27S7bA1S7aVJG;R11R8R7R6R5R4R3R2R1A9S1cR5G6A2S49S11S1cR6A1R10A3F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;S3fS4bSfG7S65OF_;SfG8S64Vsegs;S3bVsegs;VJG;R11R7R6R5R4A5RfR2R1A5R3A3FtY;FrY;SfG8S64Vsegs;S3bVsegs;VJG;R12R8R7R6R5A5R11R2R1A5R4A3FtX;FrX;F_;FQ;Fa;Frho;FKc;FA;F_;F_;F_;F_;F_;F_;FF;FD';FD;FBX;").
Proof.
  intros BX D D' F WD DD NXD HD FLOW FH A Kc rho a Q HC rX tX.
  apply (etc_pre (SPA segs (JG BX A Kc rho a) D' rX tX)); [intros w Hw; exact (hint_low nW st nx BX D D' F WD DD NXD HD FLOW FH A Kc rho a rX tX w Hw) | exact (HC rX tX)].
Qed.

Section G44E.
Variable BX : AA -> AA.
Hypothesis BXg : ltac2:(tb__ "0|0|
S3fS0S42S40VBX;R1A1A1S40R1A1A3FX;").
Variable PX : list sobj.
Variable FXP : list sprop.
Hypothesis PX_noband : ltac2:(tb__ "0|2|
S3fS4bSfS39Q40A1M0SfS27G0A1S27S7bA1S7aVJG;VBX;R8R7R6R5R4R3R2R1A9S49S11S1cR5A1VFXP;A3S27SeA1S0S27S2cS2cS10S10A2S10A2M1A1S48SeG1S63R1A4S48SeG1S63VPX;A4A3S49SeSeSb7S1eR9R1A2A1Lo;R2A3F_;Fl;F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;").
Variables (D6 U7 ET7 CT7 CO7 CR7 CS7 CM7 T7 : axst) (s7 : wsub) (R7 : list sobj) (n7 : nat).
Let D7 : axst := ltac2:(tb__ "0|0|
S82VT7;S13S5VCM7;A1A1A2").
Hypothesis WU7 : ltac2:(tb__ "0|0|
S0S28S18S5VU7;A1A1S29A3").
Hypothesis DU7 : ltac2:(tb__ "0|4|
S0S2eS2cS27S2cS10S10A2M0A1M1S27S11A1M2A2M3A1S77S5VD6;A1S5VU7;A1A2S30G3S2dG1G2S2bG0A1S98Vnx;A1A4A2A3").
Hypothesis NXU7 : ltac2:(tb__ "0|0|
S0S37S12S5VU7;A1A1S12S5VD6;A1A1A3").
Hypothesis HU7 : ltac2:(tb__ "0|0|
S0S6S7VD6;S5VU7;A1A2VU7;A3").
Hypothesis Cert7 : ltac2:(tb__ "0|1|
S0S28S60S70Ufa0S2aS36S74S2bS36A1A3VGS;S2aS6VU7;S2bS6A1M0A3S2aS6VET7;G0A3A6S29A3").
Hypothesis WC7 : ltac2:(tb__ "0|0|
S0S28S18S5VCT7;A1A1S29A3").
Hypothesis DF7 : ltac2:(tb__ "0|4|
S0S2eS2cS27S2cS10S10A2M0A1M1S27S11A1M2A2M3A1S77S5VET7;A1S5VCT7;A1A2S30G3S2dG1G2S2aG0S2dS10S10S9eVnx;A1S80Vnx;A1A4S2aG0S2dS10S10S9fVnx;A1S9bA4S2bG0A1A3A3S2bS11A1A4A2A3").
Hypothesis NX7 : ltac2:(tb__ "0|0|
S0S37S12S5VCT7;A1A1S12S5VET7;A1A1A3").
Hypothesis HC7 : ltac2:(tb__ "0|0|
S0S6S7VET7;S5VCT7;A1A2VCT7;A3").
Hypothesis SK7 : ltac2:(tb__ "0|1|
S0S27S2cS2cS10S10A2S10A2M0A1S48SeG0S63S1bS5VCT7;A1A1A4S48SeG0S63S2fSeS2aSeS8aVnx;A1S2aSeS7eVnx;A1S2aSeS7cVnx;A1S2bSeA1A3A3A3S2fSeSb6VnW;Vnx;A2VPX;A3A3A4A3").
Hypothesis FC7 : ltac2:(tb__ "0|0|
S5cS11S2fS11S52VW;Vst;A2S51S50A1A3S13S5VCT7;A1A1A3").
Hypothesis FX7 : ltac2:(tb__ "0|0|
S5cS11VFXP;S13S5VCT7;A1A1A3").
Hypothesis XC7 : ax_X CT7 = [].
Hypothesis HCO7 : ltac2:(tb__ "0|0|
S0S6S7dVCT7;S20S80Vnx;A1S16Z0A1S16Z100A1S2bS15A1S1fA5A2VCO7;A3").
Hypothesis WCO7 : ltac2:(tb__ "0|0|
S0S28S18S5VCO7;A1A1S29A3").
Hypothesis RB7 : ltac2:(tb__ "0|0|
S0S28Sd0S25Sd7S5VCO7;A1U1A2A2S29A3").
Hypothesis HCR7 : ltac2:(tb__ "0|0|
S0S6Sd2VCO7;U1A2VCR7;A3").
Hypothesis LEN7 : ltac2:(tb__ "0|0|
S0S31S32SeS1bS5VCR7;A1A1A2Vn7;A3").
Hypothesis PERM_nd7 : ltac2:(tb__ "0|0|
S0S28Sc6S8fVn7;A1A1S29A3").
Hypothesis PERM_lt7 : ltac2:(tb__ "0|0|
S0S28S5bS31S31Sc9R1Vn7;A2Li;S8fVn7;A1A3S29A3").
Hypothesis PERM_cov7 : ltac2:(tb__ "0|0|
S0S28S5bS31S31S5dS31Sc8R1A1S8fVn7;A1A3Li;S4aU0Vn7;A2A3S29A3").
Hypothesis HCS7 : ltac2:(tb__ "0|0|
S0S6Sb1VCR7;A1VCS7;A3").
Hypothesis MRG7 : ltac2:(tb__ "0|0|
S0S28Sd0S25Sd6S5VCS7;A1U1A2A2S29A3").
Hypothesis HCM7 : ltac2:(tb__ "0|0|
S0S6Sd1VCS7;U1A2VCM7;A3").
Hypothesis He7 : ltac2:(tb__ "0|1|
S0S2eS27SeA1M0A1S84VCM7;S75Vs7;A3S30G0VR7;A2A3").
Hypothesis Hchk7 : ltac2:(tb__ "0|0|
S0S28S83VCM7;S75Vs7;VR7;S48S8S6S9S76A4A5S29A3").
Hypothesis HT7 : ltac2:(tb__ "0|0|
S0S6S85Vs7;S75S7fVCM7;VR7;A5VT7;A3").
Hypothesis FBC7 : ltac2:(tb__ "0|1|
S0S28S5bS11S19S12S5VCM7;A1M0A1A1S13G0A1A3S29A3").
Hypothesis FBT7 : ltac2:(tb__ "0|0|
S0S28S5bS11S19S12S5VT7;A1A1A1S13S5VCM7;A1A1A3S29A3").
Hypothesis NXC7 : ltac2:(tb__ "0|0|
S0S28S73VGS;S12S5VCM7;A1A1A2S29A3").
Hypothesis NXE7 : ltac2:(tb__ "0|0|
S0S28S73VGS;S12S5VU7;A1A1A2S29A3").
Hypothesis ECert7 : ltac2:(tb__ "0|3|
S0S28S61S70Ufa0S2aS36S74S2bS36A1A3VGS;S2aS5eS5fVU7;Z1S16Z0M0A1M1A3S2bS5eA1M2A3S2aS5eS5fVET7;G0G1A3G2A3A6S29A3").
Lemma RSU7' : ltac2:(tb__ "0|1|
S3fS4bSfS39Q40A1M0SfS27G0A1S65S3bVsegs;VJG;VBX;R7R6R5R4A5VD6;R3R2R1A6S3bVsegs;VJG;VBX;R8R7R6R5A5VU7;R4R3R2A6F_;Fw;Ftp;FrhoX;Fa;Frho;FKc;FA;").
Proof. rr RSU7. Qed.
Lemma prep7' : ltac2:(tb__ "0|4|
S3fS4bSfS39Q40M0A1M1SfS27G1A1S65S0S4eVst;S4dA3S0S27S4cA1VW;S2bS4cA1A3F_;S36S1S66S78S38G0R6A2A1M2R1A2S69R1S67G2S68S71S38G0S14R7PcA2A2A1Z8A2A2A2A2S2S0S2eS39Q8A1M3A1S17R8S3aG0R2A2A2S33G3A1A3A1F_;Fz;S3bVsegs;VJG;VBX;R9R8R7R6A5VET7;R5R4R3A6S3bVsegs;VJG;VBX;RaR9R8R7A5VCM7;R6R5R4A6F_;F_;F_;Fw;Ftp;FrhoX;Fa;Frho;FKc;FA;").
Proof. rr prep7. Qed.

Theorem esec_g44 : ltac2:(tb__ "0|5|
S3fS4bSfS39Q40M0A1M1S65OF_;S0S4eVst;S4dA3S0S27S4cA1VW;S2bS4cA1A3F_;S72VW;Vst;A2S4fR6A1S36S1S66S78S38G0R6A2A1M2R1A2S69R1S67G2S68S71S38G0S14R7PcA2A2A1Z8A2A2A2A2S2S0S2eS39Q8A1M3A1S17R8S3aG0R2A2A2S33G3A1A3A1F_;Fz;SfS27G1A1M4S64Vsegs;S3bVsegs;VJG;VBX;RbRaR9R8A5VD7;R2R1A5R7A3FtpY;FrhoY;SfG4S64Vsegs;S3bVsegs;VJG;VBX;RcRbRaR9A5VD6;R2R1A5R8A3FtX;FrX;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;").
Proof.
  assert (USED := (BXg, PX_noband, WU7, DU7, NXU7, HU7, Cert7, WC7, DF7, NX7, HC7, SK7, FC7, FX7, XC7, HCO7, WCO7, RB7, HCR7, LEN7, PERM_nd7, PERM_lt7, PERM_cov7, HCS7, MRG7, HCM7, He7, Hchk7, HT7, FBC7, FBT7, NXC7, NXE7, ECert7)); clear USED.
  intros A Kc rho a Q HW HUS HKc RUNDEF HCONT rX tX.
  pose proof (JGs_stable nW st tmax nx Hnx NXG BX A Kc rho a HUS HKc) as HST.
  apply (etc_pre (SPA segs (JG BX A Kc rho a) U7 rX tX)); [intros w Hw; exact (RSU7' A Kc rho a rX tX w Hw)|].
  apply (ecfg_1 nx [MSENT] U7 ET7 (JG BX A Kc rho a) Q tX rX HST NXE7 ECert7). intros rE.
  apply (etc_pre (SPA segs (JG BX A Kc rho a) CM7 rE tX)); [intros w Hw; exact (prep7' A Kc rho a rE tX w HW RUNDEF Hw)|].
  exact (ems_call BX CM7 T7 Pre_memsetA Pret_ms Posts_memsetA s7 R7 eq_refl (fun Jx r0 t0 Hs => memset_sumA_ex Jx r0 t0 Hs) eq_refl
           He7 Hchk7 HT7 FBC7 FBT7 NXC7 A Kc rho a tX Q HUS HKc HCONT rE).
Qed.
End G44E.

Section G45E.
Variable BX : AA -> AA.
Hypothesis BXg : ltac2:(tb__ "0|0|
S3fS0S42S40VBX;R1A1A1S40R1A1A3FX;").
Variable PX : list sobj.
Variable FXP : list sprop.
Hypothesis PX_noband : ltac2:(tb__ "0|2|
S3fS4bSfS39Q40A1M0SfS27G0A1S27S7bA1S7aVJG;VBX;R8R7R6R5R4R3R2R1A9S49S11S1cR5A1VFXP;A3S27SeA1S0S27S2cS2cS10S10A2S10A2M1A1S48SeG1S63R1A4S48SeG1S63VPX;A4A3S49SeSeSb7S1eR9R1A2A1Lo;R2A3F_;Fl;F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;").
Variables (D7 U8 ET8 CT8 CO8 T8 : axst) (s8 : wsub) (R8 : list sobj).
Let D8 : axst := ltac2:(tb__ "0|0|
S82VT8;S13S5VCO8;A1A1A2").
Hypothesis WU8 : ltac2:(tb__ "0|0|
S0S28S18S5VU8;A1A1S29A3").
Hypothesis DU8 : ltac2:(tb__ "0|4|
S0S2eS2cS27S2cS10S10A2M0A1M1S27S11A1M2A2M3A1S77S5VD7;A1S5VU8;A1A2S30G3S2dG1G2S2bG0A1S99Vnx;A1A4A2A3").
Hypothesis NXU8 : ltac2:(tb__ "0|0|
S0S37S12S5VU8;A1A1S12S5VD7;A1A1A3").
Hypothesis HU8 : ltac2:(tb__ "0|0|
S0S6S7VD7;S5VU8;A1A2VU8;A3").
Hypothesis Cert8 : ltac2:(tb__ "0|1|
S0S28S60S70Ufa0S2aS36S74S2bS36A1A3VGS;S2aS6VU8;S2bS6A1M0A3S2aS6VET8;G0A3A6S29A3").
Hypothesis WC8 : ltac2:(tb__ "0|0|
S0S28S18S5VCT8;A1A1S29A3").
Hypothesis DF8 : ltac2:(tb__ "0|4|
S0S2eS2cS27S2cS10S10A2M0A1M1S27S11A1M2A2M3A1S77S5VET8;A1S5VCT8;A1A2S30G3S2dG1G2S2bG0A1Sa0Vnx;A1A4A2A3").
Hypothesis NX8 : ltac2:(tb__ "0|0|
S0S37S12S5VCT8;A1A1S12S5VET8;A1A1A3").
Hypothesis HC8 : ltac2:(tb__ "0|0|
S0S6S7VET8;S5VCT8;A1A2VCT8;A3").
Hypothesis SK8 : ltac2:(tb__ "0|1|
S0S27S2cS2cS10S10A2S10A2M0A1S48SeG0S63S1bS5VCT8;A1A1A4S48SeG0S63S2fSeS2aSeS8eVnx;A1S2aSeS8aVnx;A1S2aSeS7cVnx;A1S2bSeA1A3A3A3S2fSeSb6VnW;Vnx;A2VPX;A3A3A4A3").
Hypothesis FC8 : ltac2:(tb__ "0|0|
S5cS11S2fS11S52VW;Vst;A2S51S50A1A3S13S5VCT8;A1A1A3").
Hypothesis FX8 : ltac2:(tb__ "0|0|
S5cS11VFXP;S13S5VCT8;A1A1A3").
Hypothesis XC8 : ax_X CT8 = [].
Hypothesis HCO8 : ltac2:(tb__ "0|0|
S0S6S7dVCT8;S20S90Vnx;A1S16Z0A1S95Vnx;A1S2bS15A1S1fA5A2VCO8;A3").
Hypothesis WCO8 : ltac2:(tb__ "0|0|
S0S28S18S5VCO8;A1A1S29A3").
Hypothesis He8 : ltac2:(tb__ "0|1|
S0S2eS27SeA1M0A1S84VCO8;Sc4Vs8;A3S30G0VR8;A2A3").
Hypothesis Hchk8 : ltac2:(tb__ "0|0|
S0S28S83VCO8;Sc4Vs8;VR8;S48S8S6S9Sc5A4A5S29A3").
Hypothesis HT8 : ltac2:(tb__ "0|0|
S0S6S85Vs8;Sc4S81VCO8;VR8;A5VT8;A3").
Hypothesis FBC8 : ltac2:(tb__ "0|1|
S0S28S5bS11S19S12S5VCO8;A1M0A1A1S13G0A1A3S29A3").
Hypothesis FBT8 : ltac2:(tb__ "0|0|
S0S28S5bS11S19S12S5VT8;A1A1A1S13S5VCO8;A1A1A3S29A3").
Hypothesis NXC8 : ltac2:(tb__ "0|0|
S0S28S73VGS;S12S5VCO8;A1A1A2S29A3").
Hypothesis NXE8 : ltac2:(tb__ "0|0|
S0S28S73VGS;S12S5VU8;A1A1A2S29A3").
Hypothesis ECert8 : ltac2:(tb__ "0|3|
S0S28S61S70Ufa0S2aS36S74S2bS36A1A3VGS;S2aS5eS5fVU8;Z1S16Z0M0A1M1A3S2bS5eA1M2A3S2aS5eS5fVET8;G0G1A3G2A3A6S29A3").
Lemma RSU8' : ltac2:(tb__ "0|1|
S3fS4bSfS39Q40A1M0SfS27G0A1S65S3bVsegs;VJG;VBX;R7R6R5R4A5VD7;R3R2R1A6S3bVsegs;VJG;VBX;R8R7R6R5A5VU8;R4R3R2A6F_;Fw;Ftp;FrhoX;Fa;Frho;FKc;FA;").
Proof. rr RSU8. Qed.
Lemma RS8' : ltac2:(tb__ "0|1|
S3fS4bSfS39Q40A1M0SfS27G0A1S65S0S4eVst;S4dA3S0S27S4cA1VW;S2bS4cA1A3F_;S3bVsegs;VJG;VBX;R8R7R6R5A5VET8;R4R3R2A6S3bVsegs;VJG;VBX;R9R8R7R6A5VCT8;R5R4R3A6F_;F_;Fw;Ftp;FrhoX;Fa;Frho;FKc;FA;").
Proof. rr RS8. Qed.
Lemma HBL8' : ltac2:(tb__ "0|c|
S3fS4bSfS39Q40M0A1M1SfS27G1A1S65S3bVsegs;VJG;VBX;R7R6R5R4A5VCT8;R3R2R1A6S1S66S78S38G0R5A2A1M2S38G0S1aR4S90Vnx;A1M3A2A2M4A2S1S66S67G4S38G0S1aR4S95Vnx;A1M5A2A2A2S67G2S68S71S38G0S14R6PcA2A2A1Z8A2A2A2S1S27SeA1M6S0S27S2cS2cS10S10A2S10A2M7A1M8S48SeG7S63R1A4M9S48SeG7S63S2aSeS8eVnx;A1S2aSeS8aVnx;A1S2aSeS7cVnx;A1S2bSeA1A3A3A3A4A3S49SeSeS24S1eR7R1A2S2dS36S36S38G0S1aR7G3A2A2MaS67GaS38G0S1aR7G5A2A2A2A4A2Lo;R2A3MbF_;Fl;G6S0G8G9S48SeG7S63VPX;A4A3GbF_;Fl;A2A2A2F_;Fw;Ftp;FrhoX;Fa;Frho;FKc;FA;").
Proof. rr HBL8. Qed.

Theorem esec_g45 : ltac2:(tb__ "0|5|
S3fS4bSfS39Q40M0A1M1S65OF_;S0S4eVst;S4dA3S0S27S4cA1VW;S2bS4cA1A3F_;S72VW;Vst;A2S4fR6A1S36S1S66S78S38G0R6A2A1M2R1A2S69R1S67G2S68S71S38G0S14R7PcA2A2A1Z8A2A2A2A2S2S0S2eS39Q8A1M3A1S17R8S3aG0R2A2A2S33G3A1A3A1F_;Fz;SfS27G1A1M4S64Vsegs;S3bVsegs;VJG;VBX;RbRaR9R8A5VD8;R2R1A5R7A3FtpY;FrhoY;SfG4S64Vsegs;S3bVsegs;VJG;VBX;RcRbRaR9A5VD7;R2R1A5R8A3FtX;FrX;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;").
Proof.
  assert (USED := (BXg, PX_noband, WU8, DU8, NXU8, HU8, Cert8, WC8, DF8, NX8, HC8, SK8, FC8, FX8, XC8, HCO8, WCO8, He8, Hchk8, HT8, FBC8, FBT8, NXC8, NXE8, ECert8)); clear USED.
  intros A Kc rho a Q HW HUS HKc RUNDEF HCONT rX tX.
  pose proof (JGs_stable nW st tmax nx Hnx NXG BX A Kc rho a HUS HKc) as HST.
  pose proof (slink_refl rho a RUNDEF) as SL.
  apply (etc_pre (SPA segs (JG BX A Kc rho a) U8 rX tX)); [intros w Hw; exact (RSU8' A Kc rho a rX tX w Hw)|].
  apply (ecfg_1 nx [MSENT] U8 ET8 (JG BX A Kc rho a) Q tX rX HST NXE8 ECert8). intros rE.
  apply (ems_step nW st tmax nx Hnx NXG BX BXg ET8 CT8 CO8 T8 (B4 nx) (a2e8 nx) [O_3b nx; O_3 nx; O_1 nx] PX Pre_mszA Pret_mz Posts_mszA s8 R8 eq_refl
           (fun Jx r0 t0 Hs => memsetZ_sumA_ex Jx Hs r0 t0) eq_refl RS8' HBL8' SK8 FC8 XC8 HCO8 WCO8 He8 Hchk8 HT8 FBC8 FBT8 NXC8
           A Kc rho rho a tX Q HW HUS HKc SL).
  intros rhoY tpY. exact (HCONT rhoY tpY).
Qed.
End G45E.

Section G46E.
Variable BX : AA -> AA.
Hypothesis BXg : ltac2:(tb__ "0|0|
S3fS0S42S40VBX;R1A1A1S40R1A1A3FX;").
Variable PX : list sobj.
Variable FXP : list sprop.
Hypothesis PX_noband : ltac2:(tb__ "0|2|
S3fS4bSfS39Q40A1M0SfS27G0A1S27S7bA1S7aVJG;VBX;R8R7R6R5R4R3R2R1A9S49S11S1cR5A1VFXP;A3S27SeA1S0S27S2cS2cS10S10A2S10A2M1A1S48SeG1S63R1A4S48SeG1S63VPX;A4A3S49SeSeSb7S1eR9R1A2A1Lo;R2A3F_;Fl;F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;").
Variables (D8 U9 E9f E9p CO9p E9q : axst).
Hypothesis WU9 : ltac2:(tb__ "0|0|
S0S28S18S5VU9;A1A1S29A3").
Hypothesis DU9 : ltac2:(tb__ "0|4|
S0S2eS2cS27S2cS10S10A2M0A1M1S27S11A1M2A2M3A1S77S5VD8;A1S5VU9;A1A2S30G3S2dG1G2S2bG0A1S9aVnx;A1A4A2A3").
Hypothesis NXU9 : ltac2:(tb__ "0|0|
S0S37S12S5VU9;A1A1S12S5VD8;A1A1A3").
Hypothesis HU9 : ltac2:(tb__ "0|0|
S0S6S7VD8;S5VU9;A1A2VU9;A3").
Hypothesis Cert9 : ltac2:(tb__ "0|1|
S0S28S60S70Ufa0S2aS36S74S2aS36S92S2bS36A1A3A3VGS;S2aS6VU9;S2bS6A1M0A3S2aS6VE9f;S2aS6VE9p;G0A3A3A6S29A3").
Hypothesis SK9 : ltac2:(tb__ "0|1|
S0S27S2cS2cS10S10A2S10A2M0A1S48SeG0S63S1bS5VE9p;A1A1A4S48SeG0S63S2fSeS2aSeS9cVnx;A1S2aSeS8eVnx;A1S2aSeS8aVnx;A1S2aSeS7cVnx;A1S2bSeA1A3A3A3A3S2fSeSb6VnW;Vnx;A2VPX;A3A3A4A3").
Hypothesis FC9 : ltac2:(tb__ "0|0|
S5cS11S2fS11S52VW;Vst;A2S51S50A1A3S13S5VE9p;A1A1A3").
Hypothesis FX9 : ltac2:(tb__ "0|0|
S5cS11VFXP;S13S5VE9p;A1A1A3").
Hypothesis FP9 : ltac2:(tb__ "0|0|
S5aS11S21S8dA1S13S5VE9p;A1A1A3").
Hypothesis XC9 : ax_X E9p = [].
Hypothesis HCO9 : ltac2:(tb__ "0|0|
S0S6S7dVE9p;S20S97Vnx;A1S16Z0A1S16Z1A1S2bS15A1S1fA5A2VCO9p;A3").
Hypothesis WCO9 : ltac2:(tb__ "0|0|
S0S28S18S5VCO9p;A1A1S29A3").
Hypothesis Cert9q : ltac2:(tb__ "0|1|
S0S28S60S70Ufa0S2aS36S74S2bS36A1A3VGS;S2aS6VCO9p;S2bS6A1M0A3S2aS6VE9q;G0A3A6S29A3").
Hypothesis NXE9 : ltac2:(tb__ "0|0|
S0S28S73VGS;S12S5VU9;A1A1A2S29A3").
Hypothesis ECert9 : ltac2:(tb__ "0|3|
S0S28S61S70Ufa0S2aS36S74S2aS36S92S2bS36A1A3A3VGS;S2aS5eS5fVU9;Z1S16Z0M0A1M1A3S2bS5eA1M2A3S2aS5eS5fVE9f;G0G1A3S2aS5eS5fVE9p;G0G1A3G2A3A3A6S29A3").
Hypothesis NXE9q : ltac2:(tb__ "0|0|
S0S28S73VGS;S12S5VCO9p;A1A1A2S29A3").
Hypothesis ECert9q : ltac2:(tb__ "0|3|
S0S28S61S70Ufa0S2aS36S74S2bS36A1A3VGS;S2aS5eS5fVCO9p;Z1S16Z0M0A1M1A3S2bS5eA1M2A3S2aS5eS5fVE9q;G0G1A3G2A3A6S29A3").
Lemma RSU9' : ltac2:(tb__ "0|1|
S3fS4bSfS39Q40A1M0SfS27G0A1S65S3bVsegs;VJG;VBX;R7R6R5R4A5VD8;R3R2R1A6S3bVsegs;VJG;VBX;R8R7R6R5A5VU9;R4R3R2A6F_;Fw;Ftp;FrhoX;Fa;Frho;FKc;FA;").
Proof. rr RSU9. Qed.
Lemma prep9' : ltac2:(tb__ "0|4|
S3fS4bSfS39Q40M0A1M1SfS27G1A1S65S0S4eVst;S4dA3S0S27S4cA1VW;S2bS4cA1A3F_;S36S1S66S78S38G0R6A2A1M2R1A2S69R1S67G2S68S71S38G0S14R7PcA2A2A1Z8A2A2A2A2S2S0S2eS39Q8A1M3A1S17R8S3aG0R2A2A2S33G3A1A3A1F_;Fz;S3bVsegs;VJG;VBX;R9R8R7R6A5VE9p;R5R4R3A6S3bVsegs;VJG;VBX;RaR9R8R7A5VCO9p;R6R5R4A6F_;F_;F_;Fw;Ftp;FrhoX;Fa;Frho;FKc;FA;").
Proof. rr prep9. Qed.

Theorem esec_g46 : ltac2:(tb__ "0|5|
S3fS4bSfS39Q40M0A1M1S65OF_;S0S4eVst;S4dA3S0S27S4cA1VW;S2bS4cA1A3F_;S72VW;Vst;A2S4fR6A1S36S1S66S78S38G0R6A2A1M2R1A2S69R1S67G2S68S71S38G0S14R7PcA2A2A1Z8A2A2A2A2S2S0S2eS39Q8A1M3A1S17R8S3aG0R2A2A2S33G3A1A3A1F_;Fz;SfS27G1A1M4S64Vsegs;S3bVsegs;VJG;VBX;RbRaR9R8A5VE9f;R2R1A5R7A3FtpY;FrhoY;SfG4S64Vsegs;S3bVsegs;VJG;VBX;RcRbRaR9A5VE9q;R2R1A5R8A3FtpY;FrhoY;SfG4S64Vsegs;S3bVsegs;VJG;VBX;RdRcRbRaA5VD8;R2R1A5R9A3FtX;FrX;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;").
Proof.
  assert (USED := (BXg, PX_noband, WU9, DU9, NXU9, HU9, Cert9, SK9, FC9, FX9, FP9, XC9, HCO9, WCO9, Cert9q, NXE9, ECert9, NXE9q, ECert9q)); clear USED.
  intros A Kc rho a Q HW HUS HKc RUNDEF HCF HCQ rX tX.
  pose proof (JGs_stable nW st tmax nx Hnx NXG BX A Kc rho a HUS HKc) as HST.
  apply (etc_pre (SPA segs (JG BX A Kc rho a) U9 rX tX)); [intros w Hw; exact (RSU9' A Kc rho a rX tX w Hw)|].
  apply (ecfg_2 nx [MSENT; PGST] U9 E9f E9p (JG BX A Kc rho a) Q tX rX HST NXE9 ECert9); intros rE.
  - exact (HCF rE tX).
  - apply (etc_pre (SPA segs (JG BX A Kc rho a) CO9p rE tX)); [intros w Hw; exact (prep9' A Kc rho a rE tX w HW RUNDEF Hw)|].
    apply (ecfg_1 nx [MSENT] CO9p E9q (JG BX A Kc rho a) Q tX rE HST NXE9q ECert9q). intros rE'. exact (HCQ rE' tX).
Qed.
End G46E.

Section G47E.
Variable BX : AA -> AA.
Variables (E S9a S9b T9 : axst) (iM : nat) (s9 : wsub) (R9 : list sobj).
Let D9 : axst := ltac2:(tb__ "0|0|
S82VT9;S13S5VS9b;A1A1A2").
Hypothesis HS9a : ltac2:(tb__ "0|0|
S0S6S96VE;ViM;S16Z1800A1A3VS9a;A3").
Hypothesis HS9b : ltac2:(tb__ "0|0|
S0S6S96VS9a;S35ViM;A1S16Z2800A1A3VS9b;A3").
Hypothesis He9 : ltac2:(tb__ "0|1|
S0S2eS27SeA1M0A1S84VS9b;S75Vs9;A3S30G0VR9;A2A3").
Hypothesis Hchk9 : ltac2:(tb__ "0|0|
S0S28S83VS9b;S75Vs9;VR9;S48S8S6S9S76A4A5S29A3").
Hypothesis HT9 : ltac2:(tb__ "0|0|
S0S6S85Vs9;S75S7fVS9b;VR9;A5VT9;A3").
Hypothesis FBC9 : ltac2:(tb__ "0|1|
S0S28S5bS11S19S12S5VS9b;A1M0A1A1S13G0A1A3S29A3").
Hypothesis FBT9 : ltac2:(tb__ "0|0|
S0S28S5bS11S19S12S5VT9;A1A1A1S13S5VS9b;A1A1A3S29A3").
Hypothesis NXC9 : ltac2:(tb__ "0|0|
S0S28S73VGS;S12S5VS9b;A1A1A2S29A3").
Lemma prepF' : ltac2:(tb__ "0|1|
S3fS4bSfS39Q40A1M0SfS27G0A1S65S3bVsegs;VJG;VBX;R7R6R5R4A5VE;R3R2R1A6S3bVsegs;VJG;VBX;R8R7R6R5A5VS9b;R4R3R2A6F_;Fw;Ftp;FrhoX;Fa;Frho;FKc;FA;").
Proof. rr prepF. Qed.

Theorem esec_g47 : ltac2:(tb__ "0|2|
S3fS4bSfS39Q40A1M0S65OF_;S72VW;Vst;A2S4fR5A1SfS27G0A1M1S64Vsegs;S3bVsegs;VJG;VBX;R9R8R7R6A5VD9;R2R1A5R5A3FtpY;FrhoY;SfG1S64Vsegs;S3bVsegs;VJG;VBX;RaR9R8R7A5VE;R2R1A5R6A3FtX;FrX;F_;F_;F_;FQ;Fa;Frho;FKc;FA;").
Proof.
  assert (USED := (HS9a, HS9b, He9, Hchk9, HT9, FBC9, FBT9, NXC9)); clear USED.
  intros A Kc rho a Q HUS HKc HCONT rX tX.
  apply (etc_pre (SPA segs (JG BX A Kc rho a) S9b rX tX)); [intros w Hw; exact (prepF' A Kc rho a rX tX w Hw)|].
  exact (ems_call BX S9b T9 Pre_memsetA Pret_ms Posts_memsetA s9 R9 eq_refl (fun Jx r0 t0 Hs => memset_sumA_ex Jx r0 t0 Hs) eq_refl
           He9 Hchk9 HT9 FBC9 FBT9 NXC9 A Kc rho a tX Q HUS HKc HCONT rX).
Qed.
End G47E.
End SEC6E.

Section SEC7E.
Variable nW : nat. Variable st : ustop. Variable tmax : Z.
Let W : list ulink := Wcan nW.
Let segs : list Segment := segsA.
Variable nx : positive.
Hypothesis Hnx : ltac2:(tb__ "0|0|
S0S37SccVW;Vst;Vtmax;A3Vnx;A3").
Hypothesis NXG : ltac2:(tb__ "0|0|
S0S28S73ScfVnx;A2S29A3").
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTM : ltac2:(tb__ "0|0|
S36SbeVCST;R1A2SbeSd9R2A2S3F_;F_;Fa;").
Hypothesis HCSTS : ltac2:(tb__ "0|0|
S36SbeVCST;R1A2SbeSdaR2A2S3F_;F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let JG (BX : AA -> AA) : AA -> KcA -> valuation -> word -> jpredA := ltac2:(tb__ "0|0|
Sb8VnW;Vst;Vnx;VBX;A4").
Section FINE.
Variable BX : AA -> AA.
Hypothesis BXok : bx_ok BX.
Variables (blk : Z) (dpx : odefault) (NRESe : sv) (FXP : list sprop).
Hypothesis Hdpx : ltac2:(tb__ "0|0|
S4S0S23Vdpx;S1fA3S0S23Vdpx;S26A3A2").
Hypothesis HPATH : ltac2:(tb__ "0|4|
S3fS4bSfS39Q40M0A1M1SfS27G1A1S27S7bA1S7aVJG;VBX;R8R7R6R5R4R3R2R1A9S49S11S1cR5A1VFXP;A3VBX;Sb5RaS38G0S14R8PcA2A2A2A1S3fS1S1S66Z8M2Vblk;A2S66Vblk;Z20000A2A2S1S66S67S6fG2S6aS32S43S41RbA1A2A1A2Vblk;A2S47R1A1M3A2S0G1S1aR7VNRESe;A2S3aG0S68G3G2A2A2A3A2A2TAs;F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;").
Variable partial : bool.
Variable F : axst.
Variables swc c1 c2 c4 c5 mc xc : list cell.
Variable tyb : Z.
Let K : list sobj := KEPTF W swc.
Let RS : list sobj := ltac2:(tb__ "0|0|
S9dVnx;Vc1;Vc2;Vc4;Vc5;Vmc;Vxc;Vblk;Vdpx;Vpartial;Aa").
Let R : list sobj := RT_m1 ++ RS.
Hypothesis SELF : ltac2:(tb__ "0|0|
S0S27SeA1Sc7S1bS5VF;A1A1SbfVnW;Vpartial;A2A2S2fSeVK;VR;A3A3").
Hypothesis NDF : ltac2:(tb__ "0|0|
S0S28Sc6SbfVnW;Vpartial;A2A1S29A3").
Hypothesis BNDF : ltac2:(tb__ "0|0|
S0S28S5bS31S31Sc9R1S32SeS1bS5VF;A1A1A2A2Li;SbfVnW;Vpartial;A2A3S29A3").
Hypothesis COVF : ltac2:(tb__ "0|0|
S0S28S5bS31S31S5dS31Sc8R1A1SbfVnW;Vpartial;A2A3Li;S4aU0S32SeS1bS5VF;A1A1A2A2A3S29A3").
Hypothesis XFn : ax_X F = [].
Hypothesis BFb : ltac2:(tb__ "0|0|
S0S10SbVF;A1S59A3").
Hypothesis FPF : ltac2:(tb__ "0|0|
S5cS11S2fS11S52VW;Vst;A2S51S50A1A3S13S5VF;A1A1A3").
Hypothesis FXF : ltac2:(tb__ "0|0|
S5cS11VFXP;S13S5VF;A1A1A3").
Hypothesis FPAR : ltac2:(tb__ "0|0|
S5aS11S28S11Lpartial;Vpartial;S21S8dA1S8dX28x2S13S5VF;A1A1A3").
Hypothesis Hc1 : ltac2:(tb__ "0|0|
S1S5aS15Sa5Vc1;A3S1S5aS15Sa1Vc1;A3S1S5aS15Sa2Vc1;A3S1S5aS15Sa6Vc1;A3S1S5aS15Sa4VNRESe;A1Vc1;A3S5aS15Sa3Vc1;A3A2A2A2A2A2").
Hypothesis Hmc : ltac2:(tb__ "0|0|
S1S5aS15SaaVnx;A1Vmc;A3S1S5aS15SabVmc;A3S1S5aS15SacVmc;A3S1S5aS15Sa8Vmc;A3S1S5aS15Sa9Vmc;A3S1S5aS15Sa7Vnx;A1Vmc;A3S1S5aS15SafVmc;A3S1S5aS15Sb0Vtyb;A1Vmc;A3S1S5aS15SaeVmc;A3S5aS15SadVmc;A3A2A2A2A2A2A2A2A2A2").
Hypothesis Htyb : ltac2:(tb__ "0|0|
S0S28S34S34S6cZ0Vtyb;A2S6dVtyb;Z100A2A2S6bS6eVtyb;Z4A2Z1A2A2S29A3").
Hypothesis Hxc : ltac2:(tb__ "0|0|
S5aS15Sb2Vnx;A1Vxc;A3").
Let KU : list sobj := ltac2:(tb__ "0|0|
Sc2VW;Vswc;Vnx;A3").
Hypothesis WCU : ltac2:(tb__ "0|0|
S0S28S18ScaS5VF;A1S2fSeVK;S2aSeS8bVnx;A1S2bSeA1A3A3A2A1S29A3").
Hypothesis SELU : ltac2:(tb__ "0|0|
S0S27SeA1Sc7S2fSeVK;S2aSeS8bVnx;A1S2bSeA1A3A3Sc0VnW;A1A2VKU;A3").
Hypothesis NDU : ltac2:(tb__ "0|0|
S0S28Sc6Sc0VnW;A1A1S29A3").
Hypothesis BNDU : ltac2:(tb__ "0|0|
S0S28S5bS31S31Sc9R1S32SeS2fSeVK;S2aSeS8bVnx;A1S2bSeA1A3A3A2A2Li;Sc0VnW;A1A3S29A3").
Hypothesis COVU : ltac2:(tb__ "0|0|
S0S28S5bS31S31S5dS31Sc8R1A1Sc0VnW;A1A3Li;S4aU0S32SeS2fSeVK;S2aSeS8bVnx;A1S2bSeA1A3A3A2A2A3S29A3").
Hypothesis W9 : ltac2:(tb__ "0|0|
S0S28S18Sc1VF;VKU;A2A1S29A3").
Hypothesis D9 : ltac2:(tb__ "0|4|
S0S2eS2cS27S2cS10S10A2M0A1M1S27S11A1M2A2M3A1S77ScaS5VF;A1VKU;A2Sc1VF;VKU;A2A2S30G3S2dG1G2S2aG0S2dS10S10S16Sd8A1S22P18A1A4S2bG0A1A3S2bS11A1A4A2A3").
Hypothesis XB9 : ltac2:(tb__ "0|0|
S0S28SdS12S5VF;A1A1S2dS10S10S93Vnx;A1S22PcA1A4A2S29A3").
Variable s9 : wsub.
Hypothesis ENT9 : ltac2:(tb__ "0|0|
S0S28SaSc3VF;VKU;Vnx;A3S55S53VW;Vst;A3Vs9;A3S29A3").
Hypothesis SID9 : ltac2:(tb__ "0|0|
S0S28SbbVs9;S79A2S29A3").
Hypothesis G110 : ltac2:(tb__ "0|0|
S0S10SbdVs9;S58A2S93Vnx;A1A3").
Variable DF9 : axst.
Hypothesis CertF : ltac2:(tb__ "0|1|
S0S28S60S70Ufa0S2bS36A1Sb9Vnx;A1S2aS6VDF9;S2bS6A1M0A3S2aS6VF;G0A3A6S29A3").
Let GS : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3.GS nx.
Hypothesis NXEF : ltac2:(tb__ "0|0|
S0S28S73VGS;S12S5VDF9;A1A1A2S29A3").
Hypothesis ECertF : ltac2:(tb__ "0|3|
S0S28S61S70Ufa0S2bS36A1VGS;S2aS5eS5fVDF9;Z1S16Z0M0A1M1A3S2bS5eA1M2A3S2aS5eS5fVF;G0G1A3G2A3A6S29A3").
Lemma sec_finish'_P : ltac2:(tb__ "0|6|
S3fS4bSfSfS39Q40M0A1M1SfS27G1A1M2G2S65S27S2cS6S87A2M3A1S5aG3S2dS6S87S55S53VW;Vst;A3S56VAInv;VCST;VXGL;RaR9A5A4R1A3S0S4eVst;S4dA3S0S27S4cA1VW;S2bS4cA1A3F_;S4fRbA1S37S0G1S14RbR1A2S14RcR1A2A3Fi;S37S0S27S39Q8A1A1S1dRcR1A2S1dRdR1A2A3Fl;S54VCST;VXGL;RfRfS17RdA1S17RcA1A6S66S6aS32S43S41R10A1A2A1S44R10A1A2S2cS36S36A2M4S5aG4R1Sb4S45VBX;Sb5R12S38G0S14RfPcM5A2A2A2A1A1A1A3Sb3R2S2dS36S36S38G0RfA2S71S38G0S14R10G5A2A2A1A4A2F_;Fbn;S3bVsegs;VJG;VBX;R12R11RfReA5VF;RdRbRaA6S86Vsegs;S79R11RdRaRbA6F_;F_;F_;F_;F_;F_;F_;F_;F_;FPosts;Fw;Ftp;Ftp0;FrhoE;Fa;Frho;Frho0;FKc;FA;").
Proof. rr sec_finish_P. Qed.
Lemma sec_finish' : ltac2:(tb__ "0|5|
S3fS4bSfSfS39Q40M0A1M1SfS27G1A1M2G2S65S0S4eVst;S4dA3S0S27S4cA1VW;S2bS4cA1A3F_;S4fR9A1S37S0G1S14R9R1A2S14RaR1A2A3Fi;S37S0S27S39Q8A1A1S1dRaR1A2S1dRbR1A2A3Fl;S54VCST;VXGL;RdRdS17RbA1S17RaA1A6S66S6aS32S43S41ReA1A2A1S44ReA1A2S2cS36S36A2M3S5aG3R1Sb4S45VBX;Sb5R10S38G0S14RdPcM4A2A2A2A1A1A1A3Sb3R2S2dS36S36S38G0RdA2S71S38G0S14ReG4A2A2A1A4A2F_;Fbn;S3bVsegs;VJG;VBX;R10RfRdRcA5VF;RbR9R8A6S86Vsegs;S79RfRbS57S53VAInv;VCST;VXGL;VW;Vst;R11R10A8R9A6F_;F_;F_;F_;F_;F_;F_;F_;Fw;Ftp;Ftp0;FrhoE;Fa;Frho;Frho0;FKc;FA;").
Proof. intros A Kc rho0 rho a rhoE tp0 tp w. apply sec_finish'_P. unfold Posts_malloc. right. left. reflexivity. Qed.

Theorem esec_g48_P : ltac2:(tb__ "0|6|
S3fS4bSfSfS39Q40M0A1M1S27G1A1M2S27S2cS6S87A2M3A1S5aG3S2dS6S87S55S53VW;Vst;A3S56VAInv;VCST;VXGL;R7R6A5A4R1A3S0S4eVst;S4dA3S0S27S4cA1VW;S2bS4cA1A3F_;S72VW;Vst;A2S4fR9A1S37S0G1S14R9R1A2S14RaR1A2A3Fi;S37S0S27S39Q8A1A1S1dRaR1A2S1dRbR1A2A3Fl;S54VCST;VXGL;RdRdS17RbA1S17RaA1A6S66S6aS32S43S41ReA1A2A1S44ReA1A2S2cS36S36A2M4S5aG4R1Sb4S45VBX;Sb5R10S38G0S14RdPcM5A2A2A2A1A1A1A3Sb3R2S2dS36S36S38G0RdA2S71S38G0S14ReG5A2A2A1A4A2F_;Fbn;SfG2S64Vsegs;S3bVsegs;VJG;VBX;R12R11RfReA5VDF9;R2R1A5S86Vsegs;S79R10RdRcA5A3FtpX;FrhoX;F_;F_;F_;F_;F_;F_;F_;F_;F_;FPosts;Ftp0;Fa;Frho;Frho0;FKc;FA;").
Proof.
  assert (USED := (BXok, Hdpx, HPATH, SELF, NDF, BNDF, COVF, XFn, BFb, FPF, FXF, FPAR, Hc1, Hmc, Htyb, Hxc, WCU, SELU, NDU, BNDU, COVU, W9, D9, XB9, ENT9, SID9, G110, CertF, NXEF, ECertF)); clear USED.
  intros A Kc rho0 rho a tp0 Posts HPin HW HUS HKc HLw HLl HKEPT0 HL9 HDB rhoX tpX.
  pose proof (JGs_stable nW st tmax nx Hnx NXG BX A Kc rho a HUS HKc) as HST.
  apply (ecfg_1 nx [] DF9 F (JG BX A Kc rho a) _ tpX rhoX HST NXEF ECertF). intros rE.
  intros w Hw. exists w. split; [apply wsteps_refl|].
  exact (sec_finish'_P A Kc rho0 rho a rE tp0 tpX w Posts HPin HW HKc HLw HLl HKEPT0 HL9 HDB Hw).
Qed.
Theorem esec_g48 : ltac2:(tb__ "0|5|
S3fS4bSfSfS39Q40M0A1M1S27G1A1M2S0S4eVst;S4dA3S0S27S4cA1VW;S2bS4cA1A3F_;S72VW;Vst;A2S4fR7A1S37S0G1S14R7R1A2S14R8R1A2A3Fi;S37S0S27S39Q8A1A1S1dR8R1A2S1dR9R1A2A3Fl;S54VCST;VXGL;RbRbS17R9A1S17R8A1A6S66S6aS32S43S41RcA1A2A1S44RcA1A2S2cS36S36A2M3S5aG3R1Sb4S45VBX;Sb5ReS38G0S14RbPcM4A2A2A2A1A1A1A3Sb3R2S2dS36S36S38G0RbA2S71S38G0S14RcG4A2A2A1A4A2F_;Fbn;SfG2S64Vsegs;S3bVsegs;VJG;VBX;R10RfRdRcA5VDF9;R2R1A5S86Vsegs;S79ReRbS57S53VAInv;VCST;VXGL;VW;Vst;R10RfA8A5A3FtpX;FrhoX;F_;F_;F_;F_;F_;F_;F_;F_;Ftp0;Fa;Frho;Frho0;FKc;FA;").
Proof.
  intros A Kc rho0 rho a tp0. apply esec_g48_P. unfold Posts_malloc. right. left. reflexivity.
Qed.
End FINE.
End SEC7E.
End SpineMallocSecE3.

(* [comment removed for export] *)
Module SpineCallocSecOK.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "rm"; "rl"; "sprop"; "SVar"; "reg_sv"; "ss_facts"; "sv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_sec"; "DG"; "sec_chunk"; "aa_geom"; "aa_Km"; "aa_fs_busy"; "aa_live"; "ageom"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "@Corelib.Init.Datatypes"; "list"; "pair"; "prod"; "None"; "app"; "length"; "option"; "true"; "bool"; "false"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "False"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "jpredA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "secmapsize"; "stopJ_stable"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "mem_keptA"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "div"; "of_nat"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger"; "sepZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dblocks"; "dfp_static"; "@Stdlib.Lists.List"; "In"; "incl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k5.CDepotCallS"; "AXK"; "dlink"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "ms_gpr"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "smatch_pendingA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "Sh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3"; "JGsC"; "clsP"; "slink"; "JGs"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "m_vmmaps"; "with_vmmaps"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.CSecBump"; "bumpP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase"; "stopJ_w"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSS"; "CS1"; "V_MS"; "nxS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jx.SpineCallocSec4"; "slink4"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "mmap_place_ok"; "mmap_rw_vm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "rho_set_rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.CallocPosts"; "PFc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1"; "F_fam"; "F_s1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull"; "F_geom_fn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jv.SpineCallocSec2"; "IMG_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1"; "JG"; "@Stdlib.PArith.BinPos.Pos"; "leb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA MmapA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts StartLib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocSP SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineCallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.RebuildN.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import MmapSymA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require il.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineCallocSec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jx.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CDepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k6.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.CertCallocSN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineCallocSec OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jv.SpineCallocSec2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.InvD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.CSecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.CSecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SecRoom OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jx.SpineCallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CDepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k5.CDepotCallS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k6.CSecLinks.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import CallocBase2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineCallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ii.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CallocArith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineCallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineCallocI2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.CallocPosts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section OK.
Variable nW : nat. Variable st : ustop. Variable nx : positive. Variable hi : bool.
Let W : list ulink := Wcan nW.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTS : ltac2:(tb__ "0|0|
S14S58VCST;R1A2S58S65R2A2S26F_;F_;Fa;").
Hypothesis HCSTD : ltac2:(tb__ "0|0|
S14S58VCST;R1A2S25S3eR2A1A1F_;Fa;").
Let JGs : ltac2:(tb__ "0|0|
SbSbF_;SbS30S2S17Q40A1S2dFa;Frho;FKc;FA;FAX;") := ltac2:(tb__ "0|0|
S4bVnW;Vst;Vnx;A3").
Let JGsC : ltac2:(tb__ "0|0|
SbSbF_;SbS30S2S17Q40A1S2dFa;Frho;FKc;FA;FAX;") := ltac2:(tb__ "0|0|
S48VnW;Vst;Vnx;A3").
Let Posts (A : AA) (Kc : KcA) : ltac2:(tb__ "0|0|
S19S1bS5aS52A2A1") := ltac2:(tb__ "0|0|
S61VCST;VXGL;VW;Vst;VA;VKc;A6").

Variables (E1 D2 T4a T4b C5a C5b : axst).

Hypothesis HG12 : ltac2:(tb__ "0|5|
S28OF_;SbS30S2S17Q40M0A1M1S19G1A1M2S29S2fVW;Vst;A2S31R6A1S2cS0R9S2bR7A1A3S49Vhi;S16G0R6A2S2eS16G0S3R7PcM3A2A2A1A3S2S2G2S4aS16G0RaA2S2eS16G0S3RbG3A2A2A1RbR3A4S27S0RfS2aS0VJGs;SbR1LX;M4ReRdR4RbA5VD2;R3R2A5R9A4F_;FtpY;FrhoY;Frho';S2S27S0RdS2aS0VJGsC;G4RcRbRaR9A5VE1;R1R8A5R7A4FrhoX;F_;F_;F_;F_;F_;FQ;Ftp;Fa;Frho;FKc;FA;Fok;").
Hypothesis HG3 : ltac2:(tb__ "0|7|
S28OF_;SbS30S2S17Q40M0A1M1S29S2fVW;Vst;A2S31R5A1S2cS0R8S2bR6A1A3S45S0R9S2bR7A1A3S38S37S3aS1eSeScR9A1A2A1Z1A2S3bZ2Z14A2A2S14S24S36S47S16G0R8A2A1M2R1A2S38R1S37G2S39S2eS16G0S3R9PcM3A2A2A1Z8A2A2A2A2S25S23S1fS17Q8A1M4A1S4RaS18G0R2A2A2S1cG4A1A3A1F_;Fz;S2S2S19G1A1M5S5bSfReA1S16G0RbA2S2eS16G0S3RcG3A2A2A1RcR3A5S27S0R10S2aS0VJGs;SbS53R1A1LX;RfReR4RcA5VT4a;R3R2A5RbA4F_;FtY;FrY;Frho'';S2G5S27S0RfS2aS0VJGs;SbR1LX;M6ReRdRcRbA5VT4b;R2R1A5RaA4FtY;FrY;S2G5S27S0R10S2aS0VJGs;G6RfReRdRcA5VD2;R2R1A5RbA4FtX;FrX;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Hypothesis HG41a : ltac2:(tb__ "0|5|
S28OF_;SbS30S2S17Q40M0A1M1S29S54VW;Vst;A2S2fVW;Vst;A2S31R6A1S2cS0R9S2bR7A1A3S45S0RaS2bR8A1A3SdS2S2S19G1A1M2S1bS14S14A2M3S3fG3R1S3dR5A1A3S3cR2S1aS14S14S16G0RdA2S2eS16G0S3RePcA2A2A1A4A2F_;Fbn;S42R5RdR4A3S27S0R11S2aS0VJGs;S41SbS53R1A1LX;M4R6A2R10RfR5RdA5VC5a;R4R3A5RcA4F_;F_;Ftp';FrhoX;Frho';FG2;S2G2S27S0ReS2aS0VJGs;G4RdRcRbRaA5VT4a;R2R1A5R9A4FtX;FrX;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Hypothesis HG41b : ltac2:(tb__ "0|5|
S28OF_;SbS30S2S17Q40M0A1M1S29S54VW;Vst;A2S2fVW;Vst;A2S31R6A1S2cS0R9S2bR7A1A3S45S0RaS2bR8A1A3SdS2S2S19G1A1M2S1bS14S14A2M3S3fG3R1S3dR5A1A3S3cR2S1aS14S14S16G0RdA2S2eS16G0S3RePcA2A2A1A4A2F_;Fbn;S42R5RdR4A3S27S0R11S2aS0VJGs;S41SbR1LX;M4R6A2R10RfR5RdA5VC5b;R4R3A5RcA4F_;F_;Ftp';FrhoX;Frho';FG2;S2G2S27S0ReS2aS0VJGs;G4RdRcRbRaA5VT4b;R2R1A5R9A4FtX;FrX;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Hypothesis HTLa : ltac2:(tb__ "0|8|
S28OF_;SbS30S2S2S17Q40M0A1M1S19G1A1M2SdS2fVW;Vst;A2S31R7A1S2cS0RaS2bR8A1A3S15S23G1S3R8R1A2S3R9R1A2A3Fi;S15S23S19S17Q8A1M3A1S5R9R1A2S5RaR1A2A3Fl;S32VCST;VXGL;RcRcS4RaA1S4R9A1A6S36S3aS1eSeScRdA1A2A1S10RdA1A2S1bS14S14A2M4S3fG4R1S3dR9A1A3S3cR2S1aS14S14S16G0RcA2M5S2eS16G0S3RdPcA2A2A1M6A4A2F_;Fbn;S14S24S36S47G5A1M7R1A2S38R1S37G7S39G6Z8A2A2A2A2S25S23S1fG3A1S4ReS18G0R2A2A2S1cG3A1A3A1F_;Fz;S2G2S27S0R13S2aS0VJGs;S41SbS53R1A1LX;RcA2R12R11RfReA5VC5a;R2R1A5S51S0S50R10RdVPosts;R12R11A2A5A4FtX;FrX;F_;F_;F_;F_;F_;F_;F_;F_;F_;FG2;Ftp0;Fa;Frho;Frho0;FKc;FA;Fok;").
Hypothesis HTLb : ltac2:(tb__ "0|8|
S28OF_;SbS30S2S2S17Q40M0A1M1S19G1A1M2SdS2fVW;Vst;A2S31R7A1S2cS0RaS2bR8A1A3S15S23G1S3R8R1A2S3R9R1A2A3Fi;S15S23S19S17Q8A1M3A1S5R9R1A2S5RaR1A2A3Fl;S32VCST;VXGL;RcRcS4RaA1S4R9A1A6S36S3aS1eSeScRdA1A2A1S10RdA1A2S1bS14S14A2M4S3fG4R1S3dR9A1A3S3cR2S1aS14S14S16G0RcA2M5S2eS16G0S3RdPcA2A2A1M6A4A2F_;Fbn;S14S24S36S47G5A1M7R1A2S38R1S37G7S39G6Z8A2A2A2A2S25S23S1fG3A1S4ReS18G0R2A2A2S1cG3A1A3A1F_;Fz;S2G2S27S0R13S2aS0VJGs;S41SbR1LX;RcA2R12R11RfReA5VC5b;R2R1A5S51S0S50R10RdVPosts;R12R11A2A5A4FtX;FrX;F_;F_;F_;F_;F_;F_;F_;F_;F_;FG2;Ftp0;Fa;Frho;Frho0;FKc;FA;Fok;").

Lemma c5_pure : ltac2:(tb__ "0|7|
SbSbF_;SdSbS30S2S2S2S2S17Q40M0A1M1S2S19G1A1S19S4dA1S4cSbS23S13SfReR1A1A1SfR1A1A3FX;SbS23S19SeA1ScRfR1A1A1ScR1A1A3FX;SbS23S19S1bS14S14A2M2A1M3S12R10R1A1A1S12R1A1A3FX;SbS23S19G3A1S11R11R1A1A1S11R1A1A3FX;S16G0R9A2S14S2eS16G0S3RePcM4A2A2A1S14S4aR2R1RfReA4S5bSfR12A1R3R2RfReA5S42R14RfReA3G2S3fG2R1S3dR16A1A3S3cR2S1aS14S14R7R6A4A2F_;Fbn;VJGs;S41R17R16A2R15R14R10RfReRdRcRbA9S24S32VCST;VXGL;R16R16S4R14A1S4R11A1A6S24S14S24S36S47R8A1M5R1A2S38R1S37G5S39S2eS16G0S3R12G4A2A2A1Z8A2A2A2A2S25S23S1fS17Q8A1M6A1S4R13S18G0R2A2A2S1cG6A1A3A1F_;Fz;S24S15S23G1S3R12R1A2S3R15R1A2A3Fi;S24S15S23S19G6A1S5R12R1A2S5R15R1A2A3Fl;G2S3fG2R1S3dR18A1A3S3cR2S1aS14S14R9S2eS16G0S3R13G4A2A2A1A4A2F_;Fbn;A2A2A2A2F_;F_;F_;F_;F_;TL;Tua;F_;F_;F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho3;Frho2;Frho1;Frho;FKc;FA;FG2;FBX;").
Proof.
  intros BX G2 A Kc rho rho1 rho2 rho3 a r tp tr md BXg BXs BXl BXf ua L SL1 SL4 DL HDB HJ.
  assert (E12 : rw rho3 12%positive = rw rho 12%positive).
  { destruct SL1 as (W1 & _). destruct SL4 as (W2 & _). destruct DL as (W3 & _). rewrite W3, W2. apply W1. }
  unfold JGs, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3.JGs in HJ. rewrite E12 in HJ. fold L in HJ. cbn zeta in HJ.
  destruct HJ as (_ & _ & HA & HPD & _ & _ & _ & Hnv & _).
  set (nv := bv_unsigned (rw rho 12%positive)) in *.
  set (As := AXK BX G2 (bumpV A nv)) in *.
  assert (Eg : aa_geom As = aa_geom A) by (unfold As, AXK; cbn [aa_geom bumpK with_depot]; rewrite BXg; reflexivity).
  assert (Es : aa_sec As = aa_sec A) by (unfold As, AXK; cbn [aa_sec bumpK with_depot]; rewrite BXs; reflexivity).
  assert (El : aa_live As = aa_live A) by (unfold As, AXK; cbn [aa_live bumpK with_depot]; rewrite BXl; reflexivity).
  assert (Ef : aa_fs_busy As = aa_fs_busy A) by (unfold As, AXK; cbn [aa_fs_busy bumpK with_depot]; rewrite BXf; reflexivity).
  assert (Ed : aa_depot As = G2) by reflexivity.
  assert (HPDs : pendS As ua L md).
  { destruct HPD as (PM & PAL & PL0 & PDI & ST & SC & SD & SF & SS & SP & SX & SDB).
    unfold pendS. rewrite Eg, Es, Ed. repeat (split; [assumption|]). exact HDB. }
  rewrite <- Eg in SL4. rewrite <- Ed in DL.
  destruct (links_kept CST XGL HCST HXGL HCSTS HCSTD As r tp md nv ua rho rho1 rho2 rho3 HA Hnv HPDs SL1 SL4 DL) as (HK & RD & HW & HL).
  rewrite E12. fold nv L.
  split; [|split; [exact RD|split; [exact HW|split; [exact HL|exact HDB]]]].
  -
    assert (CA : forall x, client_addrA CST As x <-> client_addrA CST A x).
    { intros x. unfold client_addrA, client_mut_addrA, aa_frames. rewrite Eg, El, Ef. reflexivity. }
    assert (CS : forall x, client_shadowA CST XGL As x <-> client_shadowA CST XGL A x).
    { intros x. unfold client_shadowA. split; (intros [(y & Hy & E)|H]; [left; exists y; split; [apply CA; exact Hy | exact E] | right; exact H]). }
    destruct HK as [K1 K2]. split.
    + intros x Bx Hx. apply K1; [exact Bx|]. destruct Hx as [(C1 & C2 & NE)|(C1 & C2 & Hd)]; [left | right]; (split; [|split]); try assumption; first [apply CA | apply CS]; assumption.
    + intros x j Hx Hj Hd. apply (K2 x j); [|exact Hj|exact Hd]. destruct Hx as [[C1 C2]|GX]; [left; split; apply CA; assumption | right; exact GX].
Qed.

Lemma d2_pure : ltac2:(tb__ "0|2|
SbS30S2S17Q40A1M0S2S19G0A1S19S4dA1S4cVJGs;SbR1LX;R8R7R6R5R4R3R2R1A9S24S38S37S3aS1eSeScR9A1A2A1M1Z1A2S3bZ2Z14A2A2S36G1S10R9A1A2A2F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a r tp tr md HJ. unfold JGs, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3.JGs in HJ. cbn zeta in HJ.
  destruct HJ as (_ & _ & HA & _ & _ & _ & _ & _ & _ & HBO).
  set (nv := bv_unsigned (rw rho 12%positive)) in *.
  split.
  - pose proof (AInvA_sec_bound segsA _ r tp md HA) as SB. cbn [aa_sec bumpV] in SB.
    assert (E : large_live (bumpV A nv) = large_live A) by reflexivity. rewrite E in SB.
    pose proof (budget_ok_alloc_room A nv HBO) as RM. unfold sec_room, SEC_SLACK in RM. clear -SB RM. lia.
  - destruct HA as (_ & _ & _ & _ & HM & _). destruct HM as (_ & _ & _ & _ & _ & _ & _ & HLd).
    destruct HLd as (_ & _ & _ & _ & _ & _ & _ & _ & L9 & _). cbn [aa_sec aa_Km bumpV] in L9. exact L9.
Qed.

Theorem sec_ok_chain : ltac2:(tb__ "0|2|
S28OF_;SbS30S2S17Q40M0A1M1S19G1A1S54VW;Vst;A2S2fVW;Vst;A2S31R6A1S2cS0R9S2bR7A1A3S45S0RaS2bR8A1A3S49Vhi;S16G0R7A2S2eS16G0S3R8PcA2A2A1A3S2S27S0RdS2aS0VJGsC;SbR1LX;RcRbRaR9A5VE1;R1R8A5S51S0S50RaR8VPosts;RcRbA2A5A4FrhoX;F_;F_;F_;F_;F_;F_;Ftp;Fa;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho a tp HW HUS HKc Hokl Hokpl HC rhoX.
  set (ua := bv_unsigned a) in *. set (L := secmapsize (bv_unsigned (rw rho 12%positive))) in *.
  apply (HG12 ok A Kc rho a tp _ HUS HKc Hokl HC). intros rho1 rhoY tpY SL1.
  apply (triple_pre_pure segsA ok _ _ (Z.of_nat (length (aa_sec A)) + 1 < 2 ^ 20 /\ Z.of_nat (length (aa_sec A)) <= aa_Km A)).
  { intros [tr [ms md]] Hw. exact (d2_pure A Kc rho1 a rhoY tpY tr md (proj2 Hw)). }
  intros [HRM HL9].
  assert (E1r : rw rho1 12%positive = rw rho 12%positive) by (destruct SL1 as (W1 & _); apply W1).
  assert (RD1 : forall z, Sh ua <= z < Sh ua + L / 8 -> rm rho1 (Z_to_bv 64 z) <> None) by (destruct SL1 as (_ & _ & _ & D1); exact D1).
  apply (HG3 ok A Kc rho1 a _ HUS HKc Hokl Hokpl HRM); [rewrite E1r; exact RD1 | |].
  -
    rewrite E1r. fold ua L. intros rho2 rY tY SL4.
    assert (E2r : rw rho2 12%positive = rw rho 12%positive) by (destruct SL4 as (W2 & _); rewrite W2; exact E1r).
    apply (HG41a ok A Kc rho2 a _ HW HUS HKc Hokl Hokpl). rewrite E2r. fold ua L. intros G2 rho3 rhoX3 tp3 HDB DL.
    apply (triple_pre_pure segsA ok _ _ _ (fun w Hw => c5_pure (fun X : AA => bumpP X) G2 A Kc rho rho1 rho2 rho3 a rhoX3 tp3 (w_tr w) (cfg_model (w_cfg w))
             (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) SL1 SL4 DL HDB (proj2 Hw))).
    intros (HK & RD & HWr & HLr & HDB3).
    exact (HTLa ok A Kc rho rho3 a tp G2 HUS HKc Hokl HWr HLr HK HL9 HDB3 RD rhoX3 tp3).
  -
    intros rY tY.
    apply (HG41b ok A Kc rho1 a _ HW HUS HKc Hokl Hokpl). rewrite E1r. fold ua L. intros G2 rho3 rhoX3 tp3 HDB DL.
    apply (triple_pre_pure segsA ok _ _ _ (fun w Hw => c5_pure (fun X : AA => X) G2 A Kc rho rho1 rho1 rho3 a rhoX3 tp3 (w_tr w) (cfg_model (w_cfg w))
             (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) SL1 (slink4_refl (aa_geom A) ua L rho1 RD1) DL HDB (proj2 Hw))).
    intros (HK & RD & HWr & HLr & HDB3).
    exact (HTLb ok A Kc rho rho3 a tp G2 HUS HKc Hokl HWr HLr HK HL9 HDB3 RD rhoX3 tp3).
Qed.
End OK.

Section GRANT.
Variable nW : nat. Variable st : ustop. Variable tmax : Z.
Let W : list ulink := Wcan nW.
Variable nx : positive.
Hypothesis Hnx : ltac2:(tb__ "0|0|
S23S15S57VW;Vst;Vtmax;A3Vnx;A3").
Hypothesis NXG : ltac2:(tb__ "0|0|
S23S21S67S1Vnx;A2S20A3").
Hypothesis R11 : ltac2:(tb__ "0|0|
S23SaS8S59S55VW;Vst;Vtmax;A3A1ZbA2S7S56A1A3").
Hypothesis FC1 : ltac2:(tb__ "0|0|
S40S6S1dS6S1dS6S1dS6S1dS6S35VW;Vst;A2S34S33A1A3S64A3S63A3S62Vtmax;Z8A2A3S9S59S55VW;Vst;Vtmax;A3A1A1A3").

Lemma grant_Jo : ltac2:(tb__ "0|3|
SbS30S2S2S19S17Q40A1M0A1S19S4dA1M1S44S4cG0S2fVW;Vst;A2S31R9A1S46S0R8R7S55VW;Vst;Vtmax;A3S1aG1S5cR6S5dR5R4A2A4A5S66VW;Vst;RcRbRaR9R8R7R5A9S5eS43R7U0A2S43R7U3A2R6S43R7U1M2A2R5A5S48VnW;Vst;Vnx;SbR1LX;ReRdRcR6S60RbVnx;R6A3RaR9S4fS5fS4eR7A1S43R8G2A2R6A3R7A2AcF_;F_;F_;F_;F_;Fa;Fmd;Fms;Ftr;Ftp;FrhoX;Frho;FKc;FA;").
Proof.
  intros A Kc rho rhoX tp tr ms md a HUS HKc Hsp HJG Hpl.
  set (nv := bv_unsigned (rw rho 12%positive)).
  pose proof (JG_rigidS nW st A Kc rho rhoX tp tr md HJG) as (E12 & _ & E142 & _).
  assert (Hnv : 64513 <= nv < 2 ^ 39).
  { pose proof (proj1 (Forall_forall _ _) (smatch_pendingA_facts segsA rhoX tp _ _ Hsp) (SPUle (SLit (rzf_lo 8)) (SVar 12))
                  ltac:(apply FC1; apply in_or_app; right; unfold F_fam; cbn [In]; left; reflexivity)) as F.
    destruct HJG as [_ HJ]. destruct HJ as (_ & _ & _ & _ & _ & HN & _). cbn [eval] in HN. rewrite E12 in HN.
    cbn [holds eval rzf_lo] in F. rewrite E12, u64_lit in F by lia. fold nv in F, HN. clear -F HN. lia. }
  pose proof (round_up_ge' nv 8 ltac:(lia)) as RU1. pose proof (round_up_ge' (secneeded nv) PG ltac:(unfold PG; lia)) as RU2.
  pose proof (round_up_mod (secneeded nv) PG ltac:(unfold PG; lia)) as RM2. unfold PG in RU2, RM2.
  assert (NS : secneeded nv = round_up nv 8 + 4096) by reflexivity.
  assert (MS : secmapsize nv = round_up (secneeded nv) 4096 + 4096) by reflexivity.
  assert (BMS : nv + 8192 <= secmapsize nv <= nv + 12294 /\ secmapsize nv mod 4096 = 0).
  { rewrite MS. split; [lia|]. rewrite Z.add_mod, RM2 by lia. reflexivity. }
  pose proof (mmap_len_sym segsA rhoX tp (CS1 W st tmax) tr ms md (SVar V_MS) (secmapsize nv) Hsp R11
                ltac:(cbn [eval]; unfold V_MS; rewrite E142; apply u64_lit; lia) (proj2 BMS) ltac:(lia)) as [_ HnZ].
  apply (JGsC_of_Sec nW st tmax nx Hnx (fun X : AA => X) A Kc rho a _ tp tr _ (fun X => eq_refl)). pose proof Hnx as Hnx'. unfold W in Hnx'.
  unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.CSecOKInv.JGsC, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.CSecOKInv.JGs. rewrite Hnx'.
  assert (NXG' : Pos.leb GW (nxS W st tmax) = true) by (rewrite Hnx; exact NXG).
  pose proof (JGsC_grant W st tmax A Kc rho rhoX tp tr md a (ms_gpr ms 1) (ms_gpr ms 0) (ms_gpr ms 3) HUS HKc HJG
                (smatch_pendingA_MI segsA rhoX tp _ tr ms md Hsp) Hnv HnZ Hpl NXG') as H.
  unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.CSecOKInv.JGsC, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.CSecOKInv.JGs in H. rewrite Hnx in H. exact H.
Qed.

Lemma cls_split : ltac2:(tb__ "0|5|
S28OF_;SbS30S2S17Q40M0A1M1S5aS2S19G1A1S29S49S20S16G0R5A2S2eS16G0S3R6PcM2A2A2A1A3S27S0RaS2aS0S48VnW;Vst;Vnx;SbR1LX;M3R9R8R7R6A8R5R4R3A5R2A4F_;S49S22S16G0R6A2S2eS16G0S3R7G2A2A2A1A3S27S0RbS2aS0S48VnW;Vst;Vnx;G3RaR9R8R7A8R6R5R4A5R3A4M4F_;G4F_;F_;FQ;Ftp;FrhoX;FE;Fa;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho a E rhoX tp Q HH HL.
  apply (triple_pre_pure segsA ok _ _ (clsP true (bv_unsigned a) (secmapsize (bv_unsigned (rw rho 12%positive)))
                                       \/ clsP false (bv_unsigned a) (secmapsize (bv_unsigned (rw rho 12%positive))))).
  - intros [tr [ms md]] Hw. pose proof (proj2 Hw) as HJ. cbn [w_tr w_cfg cfg_model fst snd] in HJ.
    destruct HJ as [HJ _]. unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3.JGs in HJ. cbn zeta in HJ. destruct HJ as (_ & _ & _ & HPD & _).
    destruct HPD as (_ & _ & _ & PDI & _). destruct PDI as (_ & _ & _ & _ & PDB).
    unfold clsP. destruct PDB as [X|X]; [right; exact X | left; exact X].
  - intros [X|X]; [exact (HH X) | exact (HL X)].
Qed.
End GRANT.
End SpineCallocSecOK.

(* [comment removed for export] *)
Module SpineMallocSec6IL.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "leafA"; "ax_setS"; "ax_X"; "la_state"; "entailsA"; "xr_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "sprop"; "cell"; "ss_next"; "ss_facts"; "swf"; "SLit"; "ss_objs"; "sprop_below"; "SVar"; "DUnknown"; "mkObj"; "SPNot"; "sstate"; "DZero"; "SAlu"; "SPBranch"; "c_off"; "c_val"; "ob_cells"; "sv_eqb"; "@Corelib.Init.Datatypes"; "true"; "bool"; "nil"; "cons"; "list"; "prod"; "app"; "nat"; "option"; "pair"; "Some"; "length"; "false"; "andb"; "S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jm.SpineMallocSec3IL"; "nx0"; "@Stdlib.Lists.List"; "In"; "forallb"; "incl"; "existsb"; "find"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@Corelib.Lists.ListDef"; "map"; "seq"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP"; "MSENT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jz.SpineMallocSec7"; "KEPTF"; "KUB"; "idxsF"; "idxsU"; "S2F"; "XF_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.CertMallocSV"; "O_UBs"; "F_par"; "UBs"; "osplit"; "O_3"; "perm7"; "F_A"; "L3"; "O_3b"; "PGST"; "RSF"; "ic_c1"; "ic_c2"; "ic_nch"; "ic_nres"; "ic_pg"; "ic_rs"; "mc_cptr"; "mc_idx"; "mc_magic"; "mc_map"; "mc_ms"; "mc_ns"; "mc_size"; "mc_sizehi"; "mc_state"; "mc_type"; "B3"; "B4"; "BP9"; "F_g7"; "F_g8"; "F_g9"; "L3b"; "O_4z"; "a0e7"; "a2e6"; "a2e7"; "a2e8"; "fx8"; "sel7"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3"; "skel"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA"; "runsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k4.SpineMallocSec6IL.INST"; "FFfa"; "FFfb"; "FFqa"; "FFqb"; "mcfa"; "mcfb"; "mcqa"; "mcqb"; "CT6a"; "CT6b"; "CT7a"; "CT7b"; "CT8a"; "CT8b"; "CO6a"; "CO6b"; "CO8a"; "CO8b"; "swcfa"; "swcfb"; "swcqa"; "swcqb"; "CM7a"; "CM7b"; "D6La"; "D6Lb"; "D7La"; "D7Lb"; "D8La"; "D8Lb"; "S9bfa"; "S9bfb"; "S9bqa"; "S9bqb"; "E9pa"; "E9pb"; "U7a"; "U7b"; "U8a"; "U8b"; "U9a"; "U9b"; "c1fa"; "c1fb"; "c1qa"; "c1qb"; "FXPa"; "FXPb"; "n7a"; "n7b"; "D6a"; "D6b"; "D7a"; "D7b"; "D8a"; "D8b"; "CO7a"; "CO7b"; "CO9pa"; "CO9pb"; "E6a"; "E6b"; "ET7a"; "ET7b"; "ET8a"; "ET8b"; "PXa"; "PXb"; "tybfa"; "tybfb"; "tybqa"; "tybqb"; "C5Aa"; "C5Ab"; "CR7a"; "CR7b"; "CS7a"; "CS7b"; "D9fa"; "D9fb"; "D9qa"; "D9qb"; "R6a"; "R6b"; "R7a"; "R7b"; "R8a"; "R8b"; "R9fa"; "R9fb"; "R9qa"; "R9qb"; "T6a"; "T6b"; "T7a"; "T7b"; "T8a"; "T8b"; "T9fa"; "T9fb"; "T9qa"; "T9qb"; "s6a"; "s6b"; "s7a"; "s7b"; "s8a"; "s8b"; "s9fa"; "s9fb"; "s9qa"; "s9qb"; "sFfa"; "sFfb"; "sFqa"; "sFqb"; "E9fa"; "E9fb"; "E9qa"; "E9qb"; "S9afa"; "S9afb"; "S9aqa"; "S9aqb"; "Y6Aa"; "Y6Ab"; "iMfa"; "iMfb"; "iMqa"; "iMqb"; "s6Aa"; "s6Ab"; "c2fa"; "c2fb"; "c2qa"; "c2qb"; "c4fa"; "c4fb"; "c4qa"; "c4qb";
"c5fa"; "c5fb"; "c5qa"; "c5qb"; "run6Aa"; "run6Ab"; "run7a"; "run7b"; "run8a"; "run8b"; "run9a"; "run9b"; "run9qa"; "run9qb"; "runFfa"; "runFfb"; "runFqa"; "runFqb"; "xcfa"; "xcfb"; "xcqa"; "xcqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "AE_A"; "L_malloc_ok"; "V_RES"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "ltb"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocST"; "O_1"; "Pret_ms"; "carveS"; "BR"; "O_2"; "Pret_mz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "select"; "nodupN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3"; "SKEL0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jz.SpineMallocSec6L"; "F_low"; "F_g7L"; "F_g8L"; "F_g9L"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Str_memsetZ"; "Pre_mszA"; "Posts_mszA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "wsub_get"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.CertMallocSS"; "V_NRES"; "V_NCH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1"; "RT_m1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall"; "isSome"; "omrg"; "oreb"; "@Stdlib.ZArith.BinInt.Z"; "eqb"; "leb"; "ltb"; "modulo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jz.SpineMallocSec5IL"; "C5ac"; "C5bc"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_EQ"; "aluop"; "mulop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "merge_objs_at"; "rebase_obj_at"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocS9 SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ii.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jl.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jm.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocSec4IL.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require js.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jz.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.CertMallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SegD_refl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.SecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.SecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jm.SpineMallocSec3IL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineMallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocSec4IL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertMallocSU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jq.SpineMallocSec5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jn.DepotCallS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.CertMallocSV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.js.SpineMallocSec6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jz.SpineMallocSec6L OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jz.SpineMallocSec5IL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jz.SpineMallocSec7.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition tyb_of (mc : list cell) : Z := ltac2:(tb__ "0|4|
S28SdA1S35Lx;S34SdSdS1fS1cR1A1S11Z17f1A1A2Lc;Vmc;A3SdSbS35Lx;S1dR1A1S35R1Lt;S36Z0M0Li;S144SbSbG0Lb;La;M1Lop;M2G2S145G1Lop;M3G3S21S37SbG0La;Lw;Lsgn;S36SbS35G0Lk;Li;Ll;Xbx8Lc;G0X28x2").
Definition cells_at (i : nat) (F : axst) : list cell := ltac2:(tb__ "0|0|
S1eS3bSaVi;S12S2VF;A1A1S122S2fA1A4A1").

Section INST.
Let W : list ulink := Wcan 0. Let st : ustop := UStopLe. Let tmax : Z := 2.
Let GS0 : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3.GS nx0.

Definition PXa : list sobj := [O_blk].
Definition FXPa : list sprop := ltac2:(tb__ "0|0|
S23ScS1bS143S14S135A1S14S134A1A3S22ScA1A3").

Definition C5Aa : axst := Eval vm_compute in (ax_add_facts (F_A nx0) C5ac).
Lemma HC5Aa_0 : ltac2:(tb__ "0|0|
S0S3S71S4cS2fA1S140A2SbbA3"). Proof. vm_cast_no_check (@eq_refl _ (C5Aa)). Qed.
Lemma FBAa_0 : ltac2:(tb__ "0|0|
S0S21S31ScS13SeS2S140A1A1A1S4cS2fA1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FLOWa_0 : ltac2:(tb__ "0|0|
S30ScS12cS2fA1SfS2S140A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Definition run6Aa : option (list leafA) := Eval vm_compute in (runT6 C5Aa).
Lemma run6Aa__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S4A1A1M0A1S72S38Ufa0S23S35S3fS22S35A1A3S23S3SbbS22S3A1A3A4S23G0S103S22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run6Aa]). Qed.
Definition Y6Aa : axst := Eval vm_compute in (leafS 0 run6Aa).
Lemma Cert6Aa_0 : ltac2:(tb__ "0|1|
S0S21S70S38Ufa0S23S35S3fS22S35A1A3VGS0;S23S3SbbS22S3A1M0A3S23S3SefG0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] GS0 [C5Aa] [Y6Aa] [run6Aa]); [exact run6Aa__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition E6a : axst := Eval vm_compute in (rmF (F_A nx0) Y6Aa).
Definition s6Aa : wsub := Eval vm_compute in (infer_sub GS0 (ax_S Y6Aa) (ax_S E6a)).
Lemma E6Aa_0 : ltac2:(tb__ "0|0|
S0S21S8SefSafSf5A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma I6Aa_0 : ltac2:(tb__ "0|0|
S0S21S132Sf5VGS0;A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition CT6a : axst := Eval vm_compute in (rstS E6a ru6 []).
Definition CO6a : axst := Eval vm_compute in (carveS CT6a (O_3 nx0)).
Lemma WC6a_0 : ltac2:(tb__ "0|0|
S0S21S10S2S7bA1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DF6a_0 : ltac2:(tb__ "0|4|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S3eS2SafA1S2S7bA1A2S2aG3S29G1G2S23G0S29SbSbS6aS2fA1S4dA4S22G0A1A3S22ScA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(a2e6 nx0, L3)], @nil sprop))). Qed.
Lemma NX6a_0 : ltac2:(tb__ "0|0|
S0S36SeS2S7bA1A1SeS2SafA1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S E6a))). Qed.
Lemma HC6a_0 : ltac2:(tb__ "0|0|
S0S3S5SafS2S7bA1A2S7bA3"). Proof. vm_cast_no_check (@eq_refl _ (CT6a)). Qed.
Lemma SK6a_0 : ltac2:(tb__ "0|1|
S0S24S25S25SbSbA2SbA2M0A1S39SaG0S6fS12S2S7bA1A1A4S39SaG0S6fS26SaS23SaS126S2fA1S23SaS122S2fA1S22SaA1A3A3S26SaS12bU0S2fA2Sb5A3A3A4A3"). Proof. vm_cast_no_check (@eq_refl _ (map skel ([O_2 nx0; O_1 nx0] ++ SKEL0 0%nat nx0 ++ PXa))). Qed.
Lemma FC6a_0 : ltac2:(tb__ "0|0|
S32ScS26ScS117VW;Vst;A2S116S115A1A3SfS2S7bA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FX6a_0 : ltac2:(tb__ "0|0|
S32ScSa1SfS2S7bA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma XC6a_0 : ltac2:(tb__ "0|1|
S0S24S25SbSbA2M0A1S6S7bA1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma HCO6a_0 : ltac2:(tb__ "0|0|
S0S3S124S7bS16S61S2fA1S11Z0A1S4dS22SdA1S15A5A2S81A3"). Proof. vm_cast_no_check (@eq_refl _ (CO6a)). Qed.
Lemma WCO6a_0 : ltac2:(tb__ "0|0|
S0S21S10S2S81A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition s6a : wsub := Eval vm_compute in (callsub CO6a Pre_memsetA).
Definition R6a : list sobj := Eval vm_compute in (callR CO6a Pre_memsetA s6a).
Definition T6a : axst := Eval vm_compute in (callT CO6a Pre_memsetA Pret_ms s6a R6a).
Lemma He6a_0 : ltac2:(tb__ "0|1|
S0S28S24SaA1M0A1S11dS81S3cSd9A3S2aG0Sc5A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some R6a)). Qed.
Lemma Hchk6a_0 : ltac2:(tb__ "0|0|
S0S21S11cS81S3cSd9Sc5S39S4S3S7S3dA4A5S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HT6a_0 : ltac2:(tb__ "0|0|
S0S3S11eSd9S3cS123S81Sc5A5ScfA3"). Proof. vm_cast_no_check (@eq_refl _ (T6a)). Qed.
Lemma FBC6a_0 : ltac2:(tb__ "0|1|
S0S21S31ScS13SeS2S81A1M0A1A1SfG0A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT6a_0 : ltac2:(tb__ "0|0|
S0S21S31ScS13SeS2ScfA1A1A1SfS2S81A1A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXC6a_0 : ltac2:(tb__ "0|0|
S0S21S121VGS0;SeS2S81A1A1A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition D6a : axst := Eval vm_compute in (ax_with_facts T6a (ss_facts (ax_S CO6a))).
Lemma HD6a_0 : ltac2:(tb__ "0|0|
S0S3S11bScfSfS2S81A1A1A2Sa5A3"). Proof. vm_cast_no_check (@eq_refl _ (D6a)). Qed.

Definition D6La : axst := Eval vm_compute in (rstS D6a [] (F_g7L nx0)).
Lemma WD6La_0 : ltac2:(tb__ "0|0|
S0S21S10S2S8bA1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DD6La_0 : ltac2:(tb__ "0|4|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S3eS2Sa5A1S2S8bA1A2S2aG3S29G1G2S22G0A1S12dS2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g7L nx0))). Qed.
Lemma NXD6La_0 : ltac2:(tb__ "0|0|
S0S36SeS2S8bA1A1SeS2Sa5A1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D6a))). Qed.
Lemma HD6La_0 : ltac2:(tb__ "0|0|
S0S3S5Sa5S2S8bA1A2S8bA3"). Proof. vm_cast_no_check (@eq_refl _ (D6La)). Qed.
Lemma FLOW6a_0 : ltac2:(tb__ "0|0|
S30ScS12cS2fA1SfS2Sa5A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Definition U7a : axst := Eval vm_compute in (U7p nx0 D6La).
Lemma WU7a_0 : ltac2:(tb__ "0|0|
S0S21S10S2S97A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DU7a_0 : ltac2:(tb__ "0|4|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S3eS2S8bA1S2S97A1A2S2aG3S29G1G2S22G0A1S64S2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g7 nx0))). Qed.
Lemma NXU7a_0 : ltac2:(tb__ "0|0|
S0S36SeS2S97A1A1SeS2S8bA1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D6La))). Qed.
Lemma HU7a_0 : ltac2:(tb__ "0|0|
S0S3S5S8bS2S97A1A2S97A3"). Proof. vm_cast_no_check (@eq_refl _ (U7a)). Qed.
Definition run7a : option (list leafA) := Eval vm_compute in (runT6 U7a).
Lemma run7a__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S4A1A1M0A1S72S38Ufa0S23S35S3fS22S35A1A3S23S3S97S22S3A1A3A4S23G0S105S22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run7a]). Qed.
Definition ET7a : axst := Eval vm_compute in (leafS 0 run7a).
Lemma Cert7a_0 : ltac2:(tb__ "0|1|
S0S21S70S38Ufa0S23S35S3fS22S35A1A3VGS0;S23S3S97S22S3A1M0A3S23S3Sb1G0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] GS0 [U7a] [ET7a] [run7a]); [exact run7a__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition CT7a : axst := Eval vm_compute in (rstS ET7a (ru7 nx0) []).
Definition CO7a : axst := Eval vm_compute in (carveS CT7a (O_3n nx0)).
Definition CR7a : axst := Eval vm_compute in (DepotCall.oreb CO7a 1).
Definition n7a : nat := Eval vm_compute in (length (ss_objs (ax_S CR7a))).
Definition CS7a : axst := Eval vm_compute in (sel7 CR7a).
Definition CM7a : axst := Eval vm_compute in (DepotCall.omrg CS7a 1).
Lemma WC7a_0 : ltac2:(tb__ "0|0|
S0S21S10S2S7dA1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DF7a_0 : ltac2:(tb__ "0|4|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S3eS2Sb1A1S2S7dA1A2S2aG3S29G1G2S23G0S29SbSbS69S2fA1S125S2fA1A4S23G0S29SbSbS6bS2fA1S67A4S22G0A1A3A3S22ScA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(a0e7 nx0, BR nx0); (a2e7 nx0, L3b)], @nil sprop))). Qed.
Lemma NX7a_0 : ltac2:(tb__ "0|0|
S0S36SeS2S7dA1A1SeS2Sb1A1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S ET7a))). Qed.
Lemma HC7a_0 : ltac2:(tb__ "0|0|
S0S3S5Sb1S2S7dA1A2S7dA3"). Proof. vm_cast_no_check (@eq_refl _ (CT7a)). Qed.
Lemma SK7a_0 : ltac2:(tb__ "0|1|
S0S24S25S25SbSbA2SbA2M0A1S39SaG0S6fS12S2S7dA1A1A4S39SaG0S6fS26SaS23SaS4aS2fA1S23SaS126S2fA1S23SaS122S2fA1S22SaA1A3A3A3S26SaS12bU0S2fA2Sb5A3A3A4A3"). Proof. vm_cast_no_check (@eq_refl _ (map skel ([O_3 nx0; O_2 nx0; O_1 nx0] ++ SKEL0 0%nat nx0 ++ PXa))). Qed.
Lemma FC7a_0 : ltac2:(tb__ "0|0|
S32ScS26ScS117VW;Vst;A2S116S115A1A3SfS2S7dA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FX7a_0 : ltac2:(tb__ "0|0|
S32ScSa1SfS2S7dA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma XC7a_0 : ltac2:(tb__ "0|1|
S0S24S25SbSbA2M0A1S6S7dA1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma HCO7a_0 : ltac2:(tb__ "0|0|
S0S3S124S7dS16S125S2fA1S11Z0A1S11Z100A1S22SdA1S15A5A2SabA3"). Proof. vm_cast_no_check (@eq_refl _ (CO7a)). Qed.
Lemma WCO7a_0 : ltac2:(tb__ "0|0|
S0S21S10S2SabA1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RB7a_0 : ltac2:(tb__ "0|0|
S0S21S139S18S147S2SabA1U1A2A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HCR7a_0 : ltac2:(tb__ "0|0|
S0S3S13bSabU1A2SbdA3"). Proof. vm_cast_no_check (@eq_refl _ (CR7a)). Qed.
Lemma LEN7a_0 : ltac2:(tb__ "0|0|
S0S27S2bSaS12S2SbdA1A1A2Sa3A3"). Proof. vm_cast_no_check (@eq_refl _ (n7a)). Qed.
Lemma PERM_nd7a_0 : ltac2:(tb__ "0|0|
S0S21S129S4bSa3A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma PERM_lt7a_0 : ltac2:(tb__ "0|0|
S0S21S31S27S27S120R1Sa3A2Li;S4bSa3A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma PERM_cov7a_0 : ltac2:(tb__ "0|0|
S0S21S31S27S27S33S27S11fR1A1S4bSa3A1A3Li;S3aU0Sa3A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HCS7a_0 : ltac2:(tb__ "0|0|
S0S3S6eSbdA1SbfA3"). Proof. vm_cast_no_check (@eq_refl _ (CS7a)). Qed.
Lemma MRG7a_0 : ltac2:(tb__ "0|0|
S0S21S139S18S146S2SbfA1U1A2A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HCM7a_0 : ltac2:(tb__ "0|0|
S0S3S13aSbfU1A2S89A3"). Proof. vm_cast_no_check (@eq_refl _ (CM7a)). Qed.
Definition s7a : wsub := Eval vm_compute in (callsub CM7a Pre_memsetA).
Definition R7a : list sobj := Eval vm_compute in (callR CM7a Pre_memsetA s7a).
Definition T7a : axst := Eval vm_compute in (callT CM7a Pre_memsetA Pret_ms s7a R7a).
Lemma He7a_0 : ltac2:(tb__ "0|1|
S0S28S24SaA1M0A1S11dS89S3cSdbA3S2aG0Sc7A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some R7a)). Qed.
Lemma Hchk7a_0 : ltac2:(tb__ "0|0|
S0S21S11cS89S3cSdbSc7S39S4S3S7S3dA4A5S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HT7a_0 : ltac2:(tb__ "0|0|
S0S3S11eSdbS3cS123S89Sc7A5Sd1A3"). Proof. vm_cast_no_check (@eq_refl _ (T7a)). Qed.
Lemma FBC7a_0 : ltac2:(tb__ "0|1|
S0S21S31ScS13SeS2S89A1M0A1A1SfG0A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT7a_0 : ltac2:(tb__ "0|0|
S0S21S31ScS13SeS2Sd1A1A1A1SfS2S89A1A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXC7a_0 : ltac2:(tb__ "0|0|
S0S21S121VGS0;SeS2S89A1A1A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition D7a : axst := Eval vm_compute in (ax_with_facts T7a (ss_facts (ax_S CM7a))).
Lemma HD7a_0 : ltac2:(tb__ "0|0|
S0S3S11bSd1SfS2S89A1A1A2Sa7A3"). Proof. vm_cast_no_check (@eq_refl _ (D7a)). Qed.

Definition D7La : axst := Eval vm_compute in (rstS D7a [] (F_g8L nx0)).
Lemma WD7La_0 : ltac2:(tb__ "0|0|
S0S21S10S2S8dA1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DD7La_0 : ltac2:(tb__ "0|4|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S3eS2Sa7A1S2S8dA1A2S2aG3S29G1G2S22G0A1S12eS2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g8L nx0))). Qed.
Lemma NXD7La_0 : ltac2:(tb__ "0|0|
S0S36SeS2S8dA1A1SeS2Sa7A1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D7a))). Qed.
Lemma HD7La_0 : ltac2:(tb__ "0|0|
S0S3S5Sa7S2S8dA1A2S8dA3"). Proof. vm_cast_no_check (@eq_refl _ (D7La)). Qed.
Lemma FLOW7a_0 : ltac2:(tb__ "0|0|
S30ScS12cS2fA1SfS2Sa7A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Definition U8a : axst := Eval vm_compute in (U8p nx0 D7La).
Lemma WU8a_0 : ltac2:(tb__ "0|0|
S0S21S10S2S99A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DU8a_0 : ltac2:(tb__ "0|4|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S3eS2S8dA1S2S99A1A2S2aG3S29G1G2S22G0A1S65S2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g8 nx0))). Qed.
Lemma NXU8a_0 : ltac2:(tb__ "0|0|
S0S36SeS2S99A1A1SeS2S8dA1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D7La))). Qed.
Lemma HU8a_0 : ltac2:(tb__ "0|0|
S0S3S5S8dS2S99A1A2S99A3"). Proof. vm_cast_no_check (@eq_refl _ (U8a)). Qed.
Definition run8a : option (list leafA) := Eval vm_compute in (runT6 U8a).
Lemma run8a__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S4A1A1M0A1S72S38Ufa0S23S35S3fS22S35A1A3S23S3S99S22S3A1A3A4S23G0S107S22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run8a]). Qed.
Definition ET8a : axst := Eval vm_compute in (leafS 0 run8a).
Lemma Cert8a_0 : ltac2:(tb__ "0|1|
S0S21S70S38Ufa0S23S35S3fS22S35A1A3VGS0;S23S3S99S22S3A1M0A3S23S3Sb3G0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] GS0 [U8a] [ET8a] [run8a]); [exact run8a__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition CT8a : axst := Eval vm_compute in (CT8p nx0 ET8a).
Definition CO8a : axst := Eval vm_compute in (carveS CT8a (O_4 nx0)).
Lemma WC8a_0 : ltac2:(tb__ "0|0|
S0S21S10S2S7fA1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DF8a_0 : ltac2:(tb__ "0|4|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S3eS2Sb3A1S2S7fA1A2S2aG3S29G1G2S22G0A1S6dS2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), fx8 nx0))). Qed.
Lemma NX8a_0 : ltac2:(tb__ "0|0|
S0S36SeS2S7fA1A1SeS2Sb3A1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S ET8a))). Qed.
Lemma HC8a_0 : ltac2:(tb__ "0|0|
S0S3S5Sb3S2S7fA1A2S7fA3"). Proof. vm_cast_no_check (@eq_refl _ (CT8a)). Qed.
Lemma SK8a_0 : ltac2:(tb__ "0|1|
S0S24S25S25SbSbA2SbA2M0A1S39SaG0S6fS12S2S7fA1A1A4S39SaG0S6fS26SaS23SaS4eS2fA1S23SaS4aS2fA1S23SaS122S2fA1S22SaA1A3A3A3S26SaS12bU0S2fA2Sb5A3A3A4A3"). Proof. vm_cast_no_check (@eq_refl _ (map skel ([O_3b nx0; O_3 nx0; O_1 nx0] ++ SKEL0 0%nat nx0 ++ PXa))). Qed.
Lemma FC8a_0 : ltac2:(tb__ "0|0|
S32ScS26ScS117VW;Vst;A2S116S115A1A3SfS2S7fA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FX8a_0 : ltac2:(tb__ "0|0|
S32ScSa1SfS2S7fA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma XC8a_0 : ltac2:(tb__ "0|1|
S0S24S25SbSbA2M0A1S6S7fA1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma HCO8a_0 : ltac2:(tb__ "0|0|
S0S3S124S7fS16S62S2fA1S11Z0A1S6cS2fA1S22SdA1S15A5A2S83A3"). Proof. vm_cast_no_check (@eq_refl _ (CO8a)). Qed.
Lemma WCO8a_0 : ltac2:(tb__ "0|0|
S0S21S10S2S83A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition s8a : wsub := Eval vm_compute in (callsub CO8a Pre_mszA).
Definition R8a : list sobj := Eval vm_compute in (callR CO8a Pre_mszA s8a).
Definition T8a : axst := Eval vm_compute in (callT CO8a Pre_mszA Pret_mz s8a R8a).
Lemma He8a_0 : ltac2:(tb__ "0|1|
S0S28S24SaA1M0A1S11dS83S130SddA3S2aG0Sc9A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some R8a)). Qed.
Lemma Hchk8a_0 : ltac2:(tb__ "0|0|
S0S21S11cS83S130SddSc9S39S4S3S7S131A4A5S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HT8a_0 : ltac2:(tb__ "0|0|
S0S3S11eSddS130S127S83Sc9A5Sd3A3"). Proof. vm_cast_no_check (@eq_refl _ (T8a)). Qed.
Lemma FBC8a_0 : ltac2:(tb__ "0|1|
S0S21S31ScS13SeS2S83A1M0A1A1SfG0A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT8a_0 : ltac2:(tb__ "0|0|
S0S21S31ScS13SeS2Sd3A1A1A1SfS2S83A1A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXC8a_0 : ltac2:(tb__ "0|0|
S0S21S121VGS0;SeS2S83A1A1A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition D8a : axst := Eval vm_compute in (ax_with_facts T8a (ss_facts (ax_S CO8a))).
Lemma HD8a_0 : ltac2:(tb__ "0|0|
S0S3S11bSd3SfS2S83A1A1A2Sa9A3"). Proof. vm_cast_no_check (@eq_refl _ (D8a)). Qed.

Definition D8La : axst := Eval vm_compute in (rstS D8a [] (F_g9L nx0)).
Lemma WD8La_0 : ltac2:(tb__ "0|0|
S0S21S10S2S8fA1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DD8La_0 : ltac2:(tb__ "0|4|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S3eS2Sa9A1S2S8fA1A2S2aG3S29G1G2S22G0A1S12fS2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g9L nx0))). Qed.
Lemma NXD8La_0 : ltac2:(tb__ "0|0|
S0S36SeS2S8fA1A1SeS2Sa9A1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D8a))). Qed.
Lemma HD8La_0 : ltac2:(tb__ "0|0|
S0S3S5Sa9S2S8fA1A2S8fA3"). Proof. vm_cast_no_check (@eq_refl _ (D8La)). Qed.
Lemma FLOW8a_0 : ltac2:(tb__ "0|0|
S30ScS12cS2fA1SfS2Sa9A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Definition U9a : axst := Eval vm_compute in (U9p nx0 D8La).
Lemma WU9a_0 : ltac2:(tb__ "0|0|
S0S21S10S2S9bA1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DU9a_0 : ltac2:(tb__ "0|4|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S3eS2S8fA1S2S9bA1A2S2aG3S29G1G2S22G0A1S66S2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g9 nx0))). Qed.
Lemma NXU9a_0 : ltac2:(tb__ "0|0|
S0S36SeS2S9bA1A1SeS2S8fA1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D8La))). Qed.
Lemma HU9a_0 : ltac2:(tb__ "0|0|
S0S3S5S8fS2S9bA1A2S9bA3"). Proof. vm_cast_no_check (@eq_refl _ (U9a)). Qed.
Definition run9a : option (list leafA) := Eval vm_compute in (runT9 U9a).
Lemma run9a__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S4A1A1M0A1S72S38Ufa0S23S35S3fS23S35S4fS22S35A1A3A3S23S3S9bS22S3A1A3A4S23G0S109S22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run9a]). Qed.
Definition E9fa : axst := Eval vm_compute in (leafS 0 run9a).
Definition E9pa : axst := Eval vm_compute in (leafS 1 run9a).
Lemma Cert9a_0 : ltac2:(tb__ "0|1|
S0S21S70S38Ufa0S23S35S3fS23S35S4fS22S35A1A3A3VGS0;S23S3S9bS22S3A1M0A3S23S3Se7S23S3S95G0A3A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT; PGST] GS0 [U9a] [E9fa; E9pa] [run9a]); [exact run9a__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma SK9a_0 : ltac2:(tb__ "0|1|
S0S24S25S25SbSbA2SbA2M0A1S39SaG0S6fS12S2S95A1A1A4S39SaG0S6fS26SaS23SaS68S2fA1S23SaS4eS2fA1S23SaS4aS2fA1S23SaS122S2fA1S22SaA1A3A3A3A3S26SaS12bU0S2fA2Sb5A3A3A4A3"). Proof. vm_cast_no_check (@eq_refl _ (map skel ([O_4z nx0; O_3b nx0; O_3 nx0; O_1 nx0] ++ SKEL0 0%nat nx0 ++ PXa))). Qed.
Lemma FC9a_0 : ltac2:(tb__ "0|0|
S32ScS26ScS117VW;Vst;A2S116S115A1A3SfS2S95A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FX9a_0 : ltac2:(tb__ "0|0|
S32ScSa1SfS2S95A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FP9a_0 : ltac2:(tb__ "0|0|
S30ScS17S47A1SfS2S95A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Lemma XC9a_0 : ltac2:(tb__ "0|1|
S0S24S25SbSbA2M0A1S6S95A1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Definition CO9pa : axst := Eval vm_compute in (carveS E9pa (mkObj (BP9 nx0) (SLit 0) (SLit 1) [] DUnknown)).
Lemma HCO9a_0 : ltac2:(tb__ "0|0|
S0S3S124S95S16S63S2fA1S11Z0A1S11Z1A1S22SdA1S15A5A2SadA3"). Proof. vm_cast_no_check (@eq_refl _ (CO9pa)). Qed.
Lemma WCO9a_0 : ltac2:(tb__ "0|0|
S0S21S10S2SadA1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition run9qa : option (list leafA) := Eval vm_compute in (runT6 CO9pa).
Lemma run9qa__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S4A1A1M0A1S72S38Ufa0S23S35S3fS22S35A1A3S23S3SadS22S3A1A3A4S23G0S10bS22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run9qa]). Qed.
Definition E9qa : axst := Eval vm_compute in (leafS 0 run9qa).
Lemma Cert9qa_0 : ltac2:(tb__ "0|1|
S0S21S70S38Ufa0S23S35S3fS22S35A1A3VGS0;S23S3SadS22S3A1M0A3S23S3Se9G0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] GS0 [CO9pa] [E9qa] [run9qa]); [exact run9qa__runeq | vm_cast_no_check (eq_refl true)]. Qed.

Definition iMfa : nat := Eval vm_compute in (find_map nx0 (ss_objs (ax_S E9fa)) 0).
Definition S9afa : axst := Eval vm_compute in (osplit E9fa iMfa (SLit 6144)).
Definition S9bfa : axst := Eval vm_compute in (osplit S9afa (S iMfa) (SLit 10240)).
Lemma HS9afa_0 : ltac2:(tb__ "0|0|
S0S3S49Se7Sf1S11Z1800A1A3SebA3"). Proof. vm_cast_no_check (@eq_refl _ (S9afa)). Qed.
Lemma HS9bfa_0 : ltac2:(tb__ "0|0|
S0S3S49SebS2eSf1A1S11Z2800A1A3S91A3"). Proof. vm_cast_no_check (@eq_refl _ (S9bfa)). Qed.
Definition s9fa : wsub := Eval vm_compute in (callsub S9bfa Pre_memsetA).
Definition R9fa : list sobj := Eval vm_compute in (callR S9bfa Pre_memsetA s9fa).
Definition T9fa : axst := Eval vm_compute in (callT S9bfa Pre_memsetA Pret_ms s9fa R9fa).
Lemma He9fa_0 : ltac2:(tb__ "0|1|
S0S28S24SaA1M0A1S11dS91S3cSdfA3S2aG0ScbA2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some R9fa)). Qed.
Lemma Hchk9fa_0 : ltac2:(tb__ "0|0|
S0S21S11cS91S3cSdfScbS39S4S3S7S3dA4A5S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HT9fa_0 : ltac2:(tb__ "0|0|
S0S3S11eSdfS3cS123S91ScbA5Sd5A3"). Proof. vm_cast_no_check (@eq_refl _ (T9fa)). Qed.
Lemma FBC9fa_0 : ltac2:(tb__ "0|1|
S0S21S31ScS13SeS2S91A1M0A1A1SfG0A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT9fa_0 : ltac2:(tb__ "0|0|
S0S21S31ScS13SeS2Sd5A1A1A1SfS2S91A1A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXC9fa_0 : ltac2:(tb__ "0|0|
S0S21S121VGS0;SeS2S91A1A1A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition D9fa : axst := Eval vm_compute in (ax_with_facts T9fa (ss_facts (ax_S S9bfa))).
Lemma HD9fa_0 : ltac2:(tb__ "0|0|
S0S3S11bSd5SfS2S91A1A1A2Sc1A3"). Proof. vm_cast_no_check (@eq_refl _ (D9fa)). Qed.
Definition runFfa : option (list leafA) := Eval vm_compute in (runTF D9fa).
Lemma runFfa__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S4A1A1M0A1S72S38Ufa0S22S35A1S23S3Sc1S22S3A1A3A4S23G0S10dS22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [runFfa]). Qed.
Definition FFfa : axst := Eval vm_compute in (leafS 0 runFfa).
Lemma CertFfa_0 : ltac2:(tb__ "0|1|
S0S21S70S38Ufa0S22S35A1VGS0;S23S3Sc1S22S3A1M0A3S23S3S73G0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [] GS0 [D9fa] [FFfa] [runFfa]); [exact runFfa__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition swcfa : list cell := Eval vm_compute in (cells_at 5 FFfa).
Definition c1fa : list cell := Eval vm_compute in (cells_at 38 FFfa).
Definition c2fa : list cell := Eval vm_compute in (cells_at 39 FFfa).
Definition c4fa : list cell := Eval vm_compute in (cells_at 41 FFfa).
Definition c5fa : list cell := Eval vm_compute in (cells_at 45 FFfa).
Definition mcfa : list cell := Eval vm_compute in (cells_at 46 FFfa).
Definition xcfa : list cell := Eval vm_compute in (cells_at 48 FFfa).
Definition tybfa : Z := Eval vm_compute in (tyb_of mcfa).
Lemma SELFfa_0 : ltac2:(tb__ "0|0|
S0S24SaA1S128S12S2S73A1A1S42U0S2cA2A2S26SaS40VW;S85A2S26SaS137S50S2fS9dSf7SfbSffS77S111Z20000S19S2cAaA3A3A3"). Proof. vm_cast_no_check (@eq_refl _ (KEPTF W swcfa ++ RT_m1 ++ RSF nx0 c1fa c2fa c4fa c5fa mcfa xcfa 131072 DZero false)). Qed.
Lemma NDFfa_0 : ltac2:(tb__ "0|0|
S0S21S129S42U0S2cA2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDFfa_0 : ltac2:(tb__ "0|0|
S0S21S31S27S27S120R1S2bSaS12S2S73A1A1A2A2Li;S42U0S2cA2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVFfa_0 : ltac2:(tb__ "0|1|
S0S21S31S27S27S33S27S11fR1A1S42U0M0S2cA2A3Li;S3aG0S2bSaS12S2S73A1A1A2A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XFnfa_0 : ltac2:(tb__ "0|1|
S0S24S25SbSbA2M0A1S6S73A1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma BFbfa_0 : ax_base FFfa = base_sv. Proof. vm_cast_no_check (@eq_refl _ (base_sv)). Qed.
Lemma FPFfa_0 : ltac2:(tb__ "0|0|
S32ScS26ScS117VW;Vst;A2S116S115A1A3SfS2S73A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FXFfa_0 : ltac2:(tb__ "0|0|
S32ScSa1SfS2S73A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FPARfa_0 : ltac2:(tb__ "0|0|
S30ScS21ScL_;S2cS17S47A1S47X21x2SfS2S73A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Lemma Hc1fa_0 : ltac2:(tb__ "0|0|
S1S30SdS55S9dA3S1S30SdS51S9dA3S1S30SdS52S9dA3S1S30SdS56S9dA3S1S30SdS54S1aS142S14S134A1S11Z4000A1A3A1S9dA3S30SdS53S9dA3A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (ic_pg) c1fa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c1) c1fa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c2) c1fa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_rs) c1fa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_nres (SAlu ALU_ADD (SVar V_NRES) (SLit 16384))) c1fa ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (ic_nch) c1fa ltac:(vm_cast_no_check (eq_refl true)))))))). Qed.
Lemma Hmcfa_0 : ltac2:(tb__ "0|0|
S1S30SdS5aS2fA1S77A3S1S30SdS5bS77A3S1S30SdS5cS77A3S1S30SdS58S77A3S1S30SdS59S77A3S1S30SdS57S2fA1S77A3S1S30SdS5fS77A3S1S30SdS60Sb7A1S77A3S1S30SdS5eS77A3S30SdS5dS77A3A2A2A2A2A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (mc_map nx0) mcfa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ms) mcfa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ns) mcfa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_idx) mcfa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_magic) mcfa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_cptr nx0) mcfa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_state) mcfa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_type tybfa) mcfa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_sizehi) mcfa ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (mc_size) mcfa ltac:(vm_cast_no_check (eq_refl true)))))))))))). Qed.
Lemma Htybfa_0 : ltac2:(tb__ "0|0|
S0S21S2dS2dS13dZ0Sb7A2S13eSb7Z100A2A2S13cS13fSb7Z4A2Z1A2A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma Hxcfa_0 : In (xc_map nx0) xcfa. Proof. exact (In_of_cellb (xc_map nx0) xcfa ltac:(vm_cast_no_check (eq_refl true))). Qed.
Lemma WCUfa_0 : ltac2:(tb__ "0|0|
S0S21S10S12aS2S73A1S26SaS40VW;S85A2S23SaS46S2fA1S22SaA1A3A3A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SELUfa_0 : ltac2:(tb__ "0|0|
S0S24SaA1S128S26SaS40VW;S85A2S23SaS46S2fA1S22SaA1A3A3S43U0A1A2S41VW;S85S2fA3A3"). Proof. vm_cast_no_check (@eq_refl _ (KUB W swcfa nx0)). Qed.
Lemma NDUfa_0 : nodupN (idxsU 0%nat) = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDUfa_0 : ltac2:(tb__ "0|0|
S0S21S31S27S27S120R1S2bSaS26SaS40VW;S85A2S23SaS46S2fA1S22SaA1A3A3A2A2Li;S43U0A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVUfa_0 : ltac2:(tb__ "0|1|
S0S21S31S27S27S33S27S11fR1A1S43U0M0A1A3Li;S3aG0S2bSaS26SaS40VW;S85A2S23SaS46S2fA1S22SaA1A3A3A2A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W9fa_0 : ltac2:(tb__ "0|0|
S0S21S10S44S73S41VW;S85S2fA3A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D9fa_0 : ltac2:(tb__ "0|5|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S3eS12aS2S73A1S41VW;S85S2fA3M4A2S44S73G4A2A2S2aG3S29G1G2S23G0S29SbSbS11S138A1S14P18A1A4S22G0A1A3S22ScA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(SLit TP_A, SVar 24)], @nil sprop))). Qed.
Lemma XB9fa_0 : ltac2:(tb__ "0|0|
S0S21S9SeS2S73A1A1S29SbSbS48S2fA1S14PcA1A4A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sFfa : wsub := Eval vm_compute in (infer_sub NF (S2F FFfa (KUB W swcfa nx0)) (ax_S (L_malloc_ok AE_A W st))).
Lemma ENT9fa_0 : ltac2:(tb__ "0|0|
S0S21S8S45S73S41VW;S85S2fA3S2fA3S119S118VW;Vst;A3Se3A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID9fa_0 : ltac2:(tb__ "0|0|
S0S21S132Se3S136A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma G110fa_0 : ltac2:(tb__ "0|0|
S0SbS133Se3S11aA2S48S2fA1A3"). Proof. vm_cast_no_check (@eq_refl _ (UBs nx0)). Qed.

Definition iMqa : nat := Eval vm_compute in (find_map nx0 (ss_objs (ax_S E9qa)) 0).
Definition S9aqa : axst := Eval vm_compute in (osplit E9qa iMqa (SLit 6144)).
Definition S9bqa : axst := Eval vm_compute in (osplit S9aqa (S iMqa) (SLit 10240)).
Lemma HS9aqa_0 : ltac2:(tb__ "0|0|
S0S3S49Se9Sf3S11Z1800A1A3SedA3"). Proof. vm_cast_no_check (@eq_refl _ (S9aqa)). Qed.
Lemma HS9bqa_0 : ltac2:(tb__ "0|0|
S0S3S49SedS2eSf3A1S11Z2800A1A3S93A3"). Proof. vm_cast_no_check (@eq_refl _ (S9bqa)). Qed.
Definition s9qa : wsub := Eval vm_compute in (callsub S9bqa Pre_memsetA).
Definition R9qa : list sobj := Eval vm_compute in (callR S9bqa Pre_memsetA s9qa).
Definition T9qa : axst := Eval vm_compute in (callT S9bqa Pre_memsetA Pret_ms s9qa R9qa).
Lemma He9qa_0 : ltac2:(tb__ "0|1|
S0S28S24SaA1M0A1S11dS93S3cSe1A3S2aG0ScdA2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some R9qa)). Qed.
Lemma Hchk9qa_0 : ltac2:(tb__ "0|0|
S0S21S11cS93S3cSe1ScdS39S4S3S7S3dA4A5S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HT9qa_0 : ltac2:(tb__ "0|0|
S0S3S11eSe1S3cS123S93ScdA5Sd7A3"). Proof. vm_cast_no_check (@eq_refl _ (T9qa)). Qed.
Lemma FBC9qa_0 : ltac2:(tb__ "0|1|
S0S21S31ScS13SeS2S93A1M0A1A1SfG0A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT9qa_0 : ltac2:(tb__ "0|0|
S0S21S31ScS13SeS2Sd7A1A1A1SfS2S93A1A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXC9qa_0 : ltac2:(tb__ "0|0|
S0S21S121VGS0;SeS2S93A1A1A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition D9qa : axst := Eval vm_compute in (ax_with_facts T9qa (ss_facts (ax_S S9bqa))).
Lemma HD9qa_0 : ltac2:(tb__ "0|0|
S0S3S11bSd7SfS2S93A1A1A2Sc3A3"). Proof. vm_cast_no_check (@eq_refl _ (D9qa)). Qed.
Definition runFqa : option (list leafA) := Eval vm_compute in (runTF D9qa).
Lemma runFqa__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S4A1A1M0A1S72S38Ufa0S22S35A1S23S3Sc3S22S3A1A3A4S23G0S10fS22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [runFqa]). Qed.
Definition FFqa : axst := Eval vm_compute in (leafS 0 runFqa).
Lemma CertFqa_0 : ltac2:(tb__ "0|1|
S0S21S70S38Ufa0S22S35A1VGS0;S23S3Sc3S22S3A1M0A3S23S3S75G0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [] GS0 [D9qa] [FFqa] [runFqa]); [exact runFqa__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition swcqa : list cell := Eval vm_compute in (cells_at 5 FFqa).
Definition c1qa : list cell := Eval vm_compute in (cells_at 38 FFqa).
Definition c2qa : list cell := Eval vm_compute in (cells_at 39 FFqa).
Definition c4qa : list cell := Eval vm_compute in (cells_at 41 FFqa).
Definition c5qa : list cell := Eval vm_compute in (cells_at 45 FFqa).
Definition mcqa : list cell := Eval vm_compute in (cells_at 46 FFqa).
Definition xcqa : list cell := Eval vm_compute in (cells_at 48 FFqa).
Definition tybqa : Z := Eval vm_compute in (tyb_of mcqa).
Lemma SELFqa_0 : ltac2:(tb__ "0|0|
S0S24SaA1S128S12S2S75A1A1S42U0S20A2A2S26SaS40VW;S87A2S26SaS137S50S2fS9fSf9SfdS101S79S113Z20000S19S20AaA3A3A3"). Proof. vm_cast_no_check (@eq_refl _ (KEPTF W swcqa ++ RT_m1 ++ RSF nx0 c1qa c2qa c4qa c5qa mcqa xcqa 131072 DZero true)). Qed.
Lemma NDFqa_0 : ltac2:(tb__ "0|0|
S0S21S129S42U0S20A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDFqa_0 : ltac2:(tb__ "0|0|
S0S21S31S27S27S120R1S2bSaS12S2S75A1A1A2A2Li;S42U0S20A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVFqa_0 : ltac2:(tb__ "0|1|
S0S21S31S27S27S33S27S11fR1A1S42U0M0S20A2A3Li;S3aG0S2bSaS12S2S75A1A1A2A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XFnqa_0 : ltac2:(tb__ "0|1|
S0S24S25SbSbA2M0A1S6S75A1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma BFbqa_0 : ax_base FFqa = base_sv. Proof. vm_cast_no_check (@eq_refl _ (base_sv)). Qed.
Lemma FPFqa_0 : ltac2:(tb__ "0|0|
S32ScS26ScS117VW;Vst;A2S116S115A1A3SfS2S75A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FXFqa_0 : ltac2:(tb__ "0|0|
S32ScSa1SfS2S75A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FPARqa_0 : ltac2:(tb__ "0|0|
S30ScS21ScL_;S20S17S47A1S47X21x2SfS2S75A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Lemma Hc1qa_0 : ltac2:(tb__ "0|0|
S1S30SdS55S9fA3S1S30SdS51S9fA3S1S30SdS52S9fA3S1S30SdS56S9fA3S1S30SdS54S1aS142S14S134A1S11Z4000A1A3A1S9fA3S30SdS53S9fA3A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (ic_pg) c1qa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c1) c1qa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c2) c1qa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_rs) c1qa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_nres (SAlu ALU_ADD (SVar V_NRES) (SLit 16384))) c1qa ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (ic_nch) c1qa ltac:(vm_cast_no_check (eq_refl true)))))))). Qed.
Lemma Hmcqa_0 : ltac2:(tb__ "0|0|
S1S30SdS5aS2fA1S79A3S1S30SdS5bS79A3S1S30SdS5cS79A3S1S30SdS58S79A3S1S30SdS59S79A3S1S30SdS57S2fA1S79A3S1S30SdS5fS79A3S1S30SdS60Sb9A1S79A3S1S30SdS5eS79A3S30SdS5dS79A3A2A2A2A2A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (mc_map nx0) mcqa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ms) mcqa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ns) mcqa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_idx) mcqa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_magic) mcqa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_cptr nx0) mcqa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_state) mcqa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_type tybqa) mcqa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_sizehi) mcqa ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (mc_size) mcqa ltac:(vm_cast_no_check (eq_refl true)))))))))))). Qed.
Lemma Htybqa_0 : ltac2:(tb__ "0|0|
S0S21S2dS2dS13dZ0Sb9A2S13eSb9Z100A2A2S13cS13fSb9Z4A2Z1A2A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma Hxcqa_0 : In (xc_map nx0) xcqa. Proof. exact (In_of_cellb (xc_map nx0) xcqa ltac:(vm_cast_no_check (eq_refl true))). Qed.
Lemma WCUqa_0 : ltac2:(tb__ "0|0|
S0S21S10S12aS2S75A1S26SaS40VW;S87A2S23SaS46S2fA1S22SaA1A3A3A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SELUqa_0 : ltac2:(tb__ "0|0|
S0S24SaA1S128S26SaS40VW;S87A2S23SaS46S2fA1S22SaA1A3A3S43U0A1A2S41VW;S87S2fA3A3"). Proof. vm_cast_no_check (@eq_refl _ (KUB W swcqa nx0)). Qed.
Lemma NDUqa_0 : nodupN (idxsU 0%nat) = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDUqa_0 : ltac2:(tb__ "0|0|
S0S21S31S27S27S120R1S2bSaS26SaS40VW;S87A2S23SaS46S2fA1S22SaA1A3A3A2A2Li;S43U0A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVUqa_0 : ltac2:(tb__ "0|1|
S0S21S31S27S27S33S27S11fR1A1S43U0M0A1A3Li;S3aG0S2bSaS26SaS40VW;S87A2S23SaS46S2fA1S22SaA1A3A3A2A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W9qa_0 : ltac2:(tb__ "0|0|
S0S21S10S44S75S41VW;S87S2fA3A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D9qa_0 : ltac2:(tb__ "0|5|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S3eS12aS2S75A1S41VW;S87S2fA3M4A2S44S75G4A2A2S2aG3S29G1G2S23G0S29SbSbS11S138A1S14P18A1A4S22G0A1A3S22ScA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(SLit TP_A, SVar 24)], @nil sprop))). Qed.
Lemma XB9qa_0 : ltac2:(tb__ "0|0|
S0S21S9SeS2S75A1A1S29SbSbS48S2fA1S14PcA1A4A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sFqa : wsub := Eval vm_compute in (infer_sub NF (S2F FFqa (KUB W swcqa nx0)) (ax_S (L_malloc_ok AE_A W st))).
Lemma ENT9qa_0 : ltac2:(tb__ "0|0|
S0S21S8S45S75S41VW;S87S2fA3S2fA3S119S118VW;Vst;A3Se5A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID9qa_0 : ltac2:(tb__ "0|0|
S0S21S132Se5S136A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma G110qa_0 : ltac2:(tb__ "0|0|
S0SbS133Se5S11aA2S48S2fA1A3"). Proof. vm_cast_no_check (@eq_refl _ (UBs nx0)). Qed.

Definition PXb : list sobj := [O_w].
Definition FXPb : list sprop := ltac2:(tb__ "0|0|
S23ScS17S1bS143S14S135A1S14S134A1A3A1S22ScA1A3").

Definition C5Ab : axst := Eval vm_compute in (ax_add_facts (F_A nx0) C5bc).
Lemma HC5Ab_0 : ltac2:(tb__ "0|0|
S0S3S71S4cS2fA1S141A2SbcA3"). Proof. vm_cast_no_check (@eq_refl _ (C5Ab)). Qed.
Lemma FBAb_0 : ltac2:(tb__ "0|0|
S0S21S31ScS13SeS2S141A1A1A1S4cS2fA1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FLOWb_0 : ltac2:(tb__ "0|0|
S30ScS12cS2fA1SfS2S141A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Definition run6Ab : option (list leafA) := Eval vm_compute in (runT6 C5Ab).
Lemma run6Ab__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S4A1A1M0A1S72S38Ufa0S23S35S3fS22S35A1A3S23S3SbcS22S3A1A3A4S23G0S104S22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run6Ab]). Qed.
Definition Y6Ab : axst := Eval vm_compute in (leafS 0 run6Ab).
Lemma Cert6Ab_0 : ltac2:(tb__ "0|1|
S0S21S70S38Ufa0S23S35S3fS22S35A1A3VGS0;S23S3SbcS22S3A1M0A3S23S3Sf0G0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] GS0 [C5Ab] [Y6Ab] [run6Ab]); [exact run6Ab__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition E6b : axst := Eval vm_compute in (rmF (F_A nx0) Y6Ab).
Definition s6Ab : wsub := Eval vm_compute in (infer_sub GS0 (ax_S Y6Ab) (ax_S E6b)).
Lemma E6Ab_0 : ltac2:(tb__ "0|0|
S0S21S8Sf0Sb0Sf6A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma I6Ab_0 : ltac2:(tb__ "0|0|
S0S21S132Sf6VGS0;A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition CT6b : axst := Eval vm_compute in (rstS E6b ru6 []).
Definition CO6b : axst := Eval vm_compute in (carveS CT6b (O_3 nx0)).
Lemma WC6b_0 : ltac2:(tb__ "0|0|
S0S21S10S2S7cA1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DF6b_0 : ltac2:(tb__ "0|4|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S3eS2Sb0A1S2S7cA1A2S2aG3S29G1G2S23G0S29SbSbS6aS2fA1S4dA4S22G0A1A3S22ScA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(a2e6 nx0, L3)], @nil sprop))). Qed.
Lemma NX6b_0 : ltac2:(tb__ "0|0|
S0S36SeS2S7cA1A1SeS2Sb0A1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S E6b))). Qed.
Lemma HC6b_0 : ltac2:(tb__ "0|0|
S0S3S5Sb0S2S7cA1A2S7cA3"). Proof. vm_cast_no_check (@eq_refl _ (CT6b)). Qed.
Lemma SK6b_0 : ltac2:(tb__ "0|1|
S0S24S25S25SbSbA2SbA2M0A1S39SaG0S6fS12S2S7cA1A1A4S39SaG0S6fS26SaS23SaS126S2fA1S23SaS122S2fA1S22SaA1A3A3S26SaS12bU0S2fA2Sb6A3A3A4A3"). Proof. vm_cast_no_check (@eq_refl _ (map skel ([O_2 nx0; O_1 nx0] ++ SKEL0 0%nat nx0 ++ PXb))). Qed.
Lemma FC6b_0 : ltac2:(tb__ "0|0|
S32ScS26ScS117VW;Vst;A2S116S115A1A3SfS2S7cA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FX6b_0 : ltac2:(tb__ "0|0|
S32ScSa2SfS2S7cA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma XC6b_0 : ltac2:(tb__ "0|1|
S0S24S25SbSbA2M0A1S6S7cA1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma HCO6b_0 : ltac2:(tb__ "0|0|
S0S3S124S7cS16S61S2fA1S11Z0A1S4dS22SdA1S15A5A2S82A3"). Proof. vm_cast_no_check (@eq_refl _ (CO6b)). Qed.
Lemma WCO6b_0 : ltac2:(tb__ "0|0|
S0S21S10S2S82A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition s6b : wsub := Eval vm_compute in (callsub CO6b Pre_memsetA).
Definition R6b : list sobj := Eval vm_compute in (callR CO6b Pre_memsetA s6b).
Definition T6b : axst := Eval vm_compute in (callT CO6b Pre_memsetA Pret_ms s6b R6b).
Lemma He6b_0 : ltac2:(tb__ "0|1|
S0S28S24SaA1M0A1S11dS82S3cSdaA3S2aG0Sc6A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some R6b)). Qed.
Lemma Hchk6b_0 : ltac2:(tb__ "0|0|
S0S21S11cS82S3cSdaSc6S39S4S3S7S3dA4A5S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HT6b_0 : ltac2:(tb__ "0|0|
S0S3S11eSdaS3cS123S82Sc6A5Sd0A3"). Proof. vm_cast_no_check (@eq_refl _ (T6b)). Qed.
Lemma FBC6b_0 : ltac2:(tb__ "0|1|
S0S21S31ScS13SeS2S82A1M0A1A1SfG0A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT6b_0 : ltac2:(tb__ "0|0|
S0S21S31ScS13SeS2Sd0A1A1A1SfS2S82A1A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXC6b_0 : ltac2:(tb__ "0|0|
S0S21S121VGS0;SeS2S82A1A1A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition D6b : axst := Eval vm_compute in (ax_with_facts T6b (ss_facts (ax_S CO6b))).
Lemma HD6b_0 : ltac2:(tb__ "0|0|
S0S3S11bSd0SfS2S82A1A1A2Sa6A3"). Proof. vm_cast_no_check (@eq_refl _ (D6b)). Qed.

Definition D6Lb : axst := Eval vm_compute in (rstS D6b [] (F_g7L nx0)).
Lemma WD6Lb_0 : ltac2:(tb__ "0|0|
S0S21S10S2S8cA1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DD6Lb_0 : ltac2:(tb__ "0|4|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S3eS2Sa6A1S2S8cA1A2S2aG3S29G1G2S22G0A1S12dS2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g7L nx0))). Qed.
Lemma NXD6Lb_0 : ltac2:(tb__ "0|0|
S0S36SeS2S8cA1A1SeS2Sa6A1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D6b))). Qed.
Lemma HD6Lb_0 : ltac2:(tb__ "0|0|
S0S3S5Sa6S2S8cA1A2S8cA3"). Proof. vm_cast_no_check (@eq_refl _ (D6Lb)). Qed.
Lemma FLOW6b_0 : ltac2:(tb__ "0|0|
S30ScS12cS2fA1SfS2Sa6A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Definition U7b : axst := Eval vm_compute in (U7p nx0 D6Lb).
Lemma WU7b_0 : ltac2:(tb__ "0|0|
S0S21S10S2S98A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DU7b_0 : ltac2:(tb__ "0|4|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S3eS2S8cA1S2S98A1A2S2aG3S29G1G2S22G0A1S64S2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g7 nx0))). Qed.
Lemma NXU7b_0 : ltac2:(tb__ "0|0|
S0S36SeS2S98A1A1SeS2S8cA1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D6Lb))). Qed.
Lemma HU7b_0 : ltac2:(tb__ "0|0|
S0S3S5S8cS2S98A1A2S98A3"). Proof. vm_cast_no_check (@eq_refl _ (U7b)). Qed.
Definition run7b : option (list leafA) := Eval vm_compute in (runT6 U7b).
Lemma run7b__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S4A1A1M0A1S72S38Ufa0S23S35S3fS22S35A1A3S23S3S98S22S3A1A3A4S23G0S106S22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run7b]). Qed.
Definition ET7b : axst := Eval vm_compute in (leafS 0 run7b).
Lemma Cert7b_0 : ltac2:(tb__ "0|1|
S0S21S70S38Ufa0S23S35S3fS22S35A1A3VGS0;S23S3S98S22S3A1M0A3S23S3Sb2G0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] GS0 [U7b] [ET7b] [run7b]); [exact run7b__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition CT7b : axst := Eval vm_compute in (rstS ET7b (ru7 nx0) []).
Definition CO7b : axst := Eval vm_compute in (carveS CT7b (O_3n nx0)).
Definition CR7b : axst := Eval vm_compute in (DepotCall.oreb CO7b 1).
Definition n7b : nat := Eval vm_compute in (length (ss_objs (ax_S CR7b))).
Definition CS7b : axst := Eval vm_compute in (sel7 CR7b).
Definition CM7b : axst := Eval vm_compute in (DepotCall.omrg CS7b 1).
Lemma WC7b_0 : ltac2:(tb__ "0|0|
S0S21S10S2S7eA1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DF7b_0 : ltac2:(tb__ "0|4|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S3eS2Sb2A1S2S7eA1A2S2aG3S29G1G2S23G0S29SbSbS69S2fA1S125S2fA1A4S23G0S29SbSbS6bS2fA1S67A4S22G0A1A3A3S22ScA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(a0e7 nx0, BR nx0); (a2e7 nx0, L3b)], @nil sprop))). Qed.
Lemma NX7b_0 : ltac2:(tb__ "0|0|
S0S36SeS2S7eA1A1SeS2Sb2A1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S ET7b))). Qed.
Lemma HC7b_0 : ltac2:(tb__ "0|0|
S0S3S5Sb2S2S7eA1A2S7eA3"). Proof. vm_cast_no_check (@eq_refl _ (CT7b)). Qed.
Lemma SK7b_0 : ltac2:(tb__ "0|1|
S0S24S25S25SbSbA2SbA2M0A1S39SaG0S6fS12S2S7eA1A1A4S39SaG0S6fS26SaS23SaS4aS2fA1S23SaS126S2fA1S23SaS122S2fA1S22SaA1A3A3A3S26SaS12bU0S2fA2Sb6A3A3A4A3"). Proof. vm_cast_no_check (@eq_refl _ (map skel ([O_3 nx0; O_2 nx0; O_1 nx0] ++ SKEL0 0%nat nx0 ++ PXb))). Qed.
Lemma FC7b_0 : ltac2:(tb__ "0|0|
S32ScS26ScS117VW;Vst;A2S116S115A1A3SfS2S7eA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FX7b_0 : ltac2:(tb__ "0|0|
S32ScSa2SfS2S7eA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma XC7b_0 : ltac2:(tb__ "0|1|
S0S24S25SbSbA2M0A1S6S7eA1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma HCO7b_0 : ltac2:(tb__ "0|0|
S0S3S124S7eS16S125S2fA1S11Z0A1S11Z100A1S22SdA1S15A5A2SacA3"). Proof. vm_cast_no_check (@eq_refl _ (CO7b)). Qed.
Lemma WCO7b_0 : ltac2:(tb__ "0|0|
S0S21S10S2SacA1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RB7b_0 : ltac2:(tb__ "0|0|
S0S21S139S18S147S2SacA1U1A2A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HCR7b_0 : ltac2:(tb__ "0|0|
S0S3S13bSacU1A2SbeA3"). Proof. vm_cast_no_check (@eq_refl _ (CR7b)). Qed.
Lemma LEN7b_0 : ltac2:(tb__ "0|0|
S0S27S2bSaS12S2SbeA1A1A2Sa4A3"). Proof. vm_cast_no_check (@eq_refl _ (n7b)). Qed.
Lemma PERM_nd7b_0 : ltac2:(tb__ "0|0|
S0S21S129S4bSa4A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma PERM_lt7b_0 : ltac2:(tb__ "0|0|
S0S21S31S27S27S120R1Sa4A2Li;S4bSa4A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma PERM_cov7b_0 : ltac2:(tb__ "0|0|
S0S21S31S27S27S33S27S11fR1A1S4bSa4A1A3Li;S3aU0Sa4A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HCS7b_0 : ltac2:(tb__ "0|0|
S0S3S6eSbeA1Sc0A3"). Proof. vm_cast_no_check (@eq_refl _ (CS7b)). Qed.
Lemma MRG7b_0 : ltac2:(tb__ "0|0|
S0S21S139S18S146S2Sc0A1U1A2A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HCM7b_0 : ltac2:(tb__ "0|0|
S0S3S13aSc0U1A2S8aA3"). Proof. vm_cast_no_check (@eq_refl _ (CM7b)). Qed.
Definition s7b : wsub := Eval vm_compute in (callsub CM7b Pre_memsetA).
Definition R7b : list sobj := Eval vm_compute in (callR CM7b Pre_memsetA s7b).
Definition T7b : axst := Eval vm_compute in (callT CM7b Pre_memsetA Pret_ms s7b R7b).
Lemma He7b_0 : ltac2:(tb__ "0|1|
S0S28S24SaA1M0A1S11dS8aS3cSdcA3S2aG0Sc8A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some R7b)). Qed.
Lemma Hchk7b_0 : ltac2:(tb__ "0|0|
S0S21S11cS8aS3cSdcSc8S39S4S3S7S3dA4A5S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HT7b_0 : ltac2:(tb__ "0|0|
S0S3S11eSdcS3cS123S8aSc8A5Sd2A3"). Proof. vm_cast_no_check (@eq_refl _ (T7b)). Qed.
Lemma FBC7b_0 : ltac2:(tb__ "0|1|
S0S21S31ScS13SeS2S8aA1M0A1A1SfG0A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT7b_0 : ltac2:(tb__ "0|0|
S0S21S31ScS13SeS2Sd2A1A1A1SfS2S8aA1A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXC7b_0 : ltac2:(tb__ "0|0|
S0S21S121VGS0;SeS2S8aA1A1A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition D7b : axst := Eval vm_compute in (ax_with_facts T7b (ss_facts (ax_S CM7b))).
Lemma HD7b_0 : ltac2:(tb__ "0|0|
S0S3S11bSd2SfS2S8aA1A1A2Sa8A3"). Proof. vm_cast_no_check (@eq_refl _ (D7b)). Qed.

Definition D7Lb : axst := Eval vm_compute in (rstS D7b [] (F_g8L nx0)).
Lemma WD7Lb_0 : ltac2:(tb__ "0|0|
S0S21S10S2S8eA1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DD7Lb_0 : ltac2:(tb__ "0|4|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S3eS2Sa8A1S2S8eA1A2S2aG3S29G1G2S22G0A1S12eS2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g8L nx0))). Qed.
Lemma NXD7Lb_0 : ltac2:(tb__ "0|0|
S0S36SeS2S8eA1A1SeS2Sa8A1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D7b))). Qed.
Lemma HD7Lb_0 : ltac2:(tb__ "0|0|
S0S3S5Sa8S2S8eA1A2S8eA3"). Proof. vm_cast_no_check (@eq_refl _ (D7Lb)). Qed.
Lemma FLOW7b_0 : ltac2:(tb__ "0|0|
S30ScS12cS2fA1SfS2Sa8A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Definition U8b : axst := Eval vm_compute in (U8p nx0 D7Lb).
Lemma WU8b_0 : ltac2:(tb__ "0|0|
S0S21S10S2S9aA1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DU8b_0 : ltac2:(tb__ "0|4|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S3eS2S8eA1S2S9aA1A2S2aG3S29G1G2S22G0A1S65S2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g8 nx0))). Qed.
Lemma NXU8b_0 : ltac2:(tb__ "0|0|
S0S36SeS2S9aA1A1SeS2S8eA1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D7Lb))). Qed.
Lemma HU8b_0 : ltac2:(tb__ "0|0|
S0S3S5S8eS2S9aA1A2S9aA3"). Proof. vm_cast_no_check (@eq_refl _ (U8b)). Qed.
Definition run8b : option (list leafA) := Eval vm_compute in (runT6 U8b).
Lemma run8b__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S4A1A1M0A1S72S38Ufa0S23S35S3fS22S35A1A3S23S3S9aS22S3A1A3A4S23G0S108S22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run8b]). Qed.
Definition ET8b : axst := Eval vm_compute in (leafS 0 run8b).
Lemma Cert8b_0 : ltac2:(tb__ "0|1|
S0S21S70S38Ufa0S23S35S3fS22S35A1A3VGS0;S23S3S9aS22S3A1M0A3S23S3Sb4G0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] GS0 [U8b] [ET8b] [run8b]); [exact run8b__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition CT8b : axst := Eval vm_compute in (CT8p nx0 ET8b).
Definition CO8b : axst := Eval vm_compute in (carveS CT8b (O_4 nx0)).
Lemma WC8b_0 : ltac2:(tb__ "0|0|
S0S21S10S2S80A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DF8b_0 : ltac2:(tb__ "0|4|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S3eS2Sb4A1S2S80A1A2S2aG3S29G1G2S22G0A1S6dS2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), fx8 nx0))). Qed.
Lemma NX8b_0 : ltac2:(tb__ "0|0|
S0S36SeS2S80A1A1SeS2Sb4A1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S ET8b))). Qed.
Lemma HC8b_0 : ltac2:(tb__ "0|0|
S0S3S5Sb4S2S80A1A2S80A3"). Proof. vm_cast_no_check (@eq_refl _ (CT8b)). Qed.
Lemma SK8b_0 : ltac2:(tb__ "0|1|
S0S24S25S25SbSbA2SbA2M0A1S39SaG0S6fS12S2S80A1A1A4S39SaG0S6fS26SaS23SaS4eS2fA1S23SaS4aS2fA1S23SaS122S2fA1S22SaA1A3A3A3S26SaS12bU0S2fA2Sb6A3A3A4A3"). Proof. vm_cast_no_check (@eq_refl _ (map skel ([O_3b nx0; O_3 nx0; O_1 nx0] ++ SKEL0 0%nat nx0 ++ PXb))). Qed.
Lemma FC8b_0 : ltac2:(tb__ "0|0|
S32ScS26ScS117VW;Vst;A2S116S115A1A3SfS2S80A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FX8b_0 : ltac2:(tb__ "0|0|
S32ScSa2SfS2S80A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma XC8b_0 : ltac2:(tb__ "0|1|
S0S24S25SbSbA2M0A1S6S80A1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma HCO8b_0 : ltac2:(tb__ "0|0|
S0S3S124S80S16S62S2fA1S11Z0A1S6cS2fA1S22SdA1S15A5A2S84A3"). Proof. vm_cast_no_check (@eq_refl _ (CO8b)). Qed.
Lemma WCO8b_0 : ltac2:(tb__ "0|0|
S0S21S10S2S84A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition s8b : wsub := Eval vm_compute in (callsub CO8b Pre_mszA).
Definition R8b : list sobj := Eval vm_compute in (callR CO8b Pre_mszA s8b).
Definition T8b : axst := Eval vm_compute in (callT CO8b Pre_mszA Pret_mz s8b R8b).
Lemma He8b_0 : ltac2:(tb__ "0|1|
S0S28S24SaA1M0A1S11dS84S130SdeA3S2aG0ScaA2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some R8b)). Qed.
Lemma Hchk8b_0 : ltac2:(tb__ "0|0|
S0S21S11cS84S130SdeScaS39S4S3S7S131A4A5S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HT8b_0 : ltac2:(tb__ "0|0|
S0S3S11eSdeS130S127S84ScaA5Sd4A3"). Proof. vm_cast_no_check (@eq_refl _ (T8b)). Qed.
Lemma FBC8b_0 : ltac2:(tb__ "0|1|
S0S21S31ScS13SeS2S84A1M0A1A1SfG0A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT8b_0 : ltac2:(tb__ "0|0|
S0S21S31ScS13SeS2Sd4A1A1A1SfS2S84A1A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXC8b_0 : ltac2:(tb__ "0|0|
S0S21S121VGS0;SeS2S84A1A1A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition D8b : axst := Eval vm_compute in (ax_with_facts T8b (ss_facts (ax_S CO8b))).
Lemma HD8b_0 : ltac2:(tb__ "0|0|
S0S3S11bSd4SfS2S84A1A1A2SaaA3"). Proof. vm_cast_no_check (@eq_refl _ (D8b)). Qed.

Definition D8Lb : axst := Eval vm_compute in (rstS D8b [] (F_g9L nx0)).
Lemma WD8Lb_0 : ltac2:(tb__ "0|0|
S0S21S10S2S90A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DD8Lb_0 : ltac2:(tb__ "0|4|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S3eS2SaaA1S2S90A1A2S2aG3S29G1G2S22G0A1S12fS2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g9L nx0))). Qed.
Lemma NXD8Lb_0 : ltac2:(tb__ "0|0|
S0S36SeS2S90A1A1SeS2SaaA1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D8b))). Qed.
Lemma HD8Lb_0 : ltac2:(tb__ "0|0|
S0S3S5SaaS2S90A1A2S90A3"). Proof. vm_cast_no_check (@eq_refl _ (D8Lb)). Qed.
Lemma FLOW8b_0 : ltac2:(tb__ "0|0|
S30ScS12cS2fA1SfS2SaaA1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Definition U9b : axst := Eval vm_compute in (U9p nx0 D8Lb).
Lemma WU9b_0 : ltac2:(tb__ "0|0|
S0S21S10S2S9cA1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DU9b_0 : ltac2:(tb__ "0|4|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S3eS2S90A1S2S9cA1A2S2aG3S29G1G2S22G0A1S66S2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g9 nx0))). Qed.
Lemma NXU9b_0 : ltac2:(tb__ "0|0|
S0S36SeS2S9cA1A1SeS2S90A1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D8Lb))). Qed.
Lemma HU9b_0 : ltac2:(tb__ "0|0|
S0S3S5S90S2S9cA1A2S9cA3"). Proof. vm_cast_no_check (@eq_refl _ (U9b)). Qed.
Definition run9b : option (list leafA) := Eval vm_compute in (runT9 U9b).
Lemma run9b__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S4A1A1M0A1S72S38Ufa0S23S35S3fS23S35S4fS22S35A1A3A3S23S3S9cS22S3A1A3A4S23G0S10aS22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run9b]). Qed.
Definition E9fb : axst := Eval vm_compute in (leafS 0 run9b).
Definition E9pb : axst := Eval vm_compute in (leafS 1 run9b).
Lemma Cert9b_0 : ltac2:(tb__ "0|1|
S0S21S70S38Ufa0S23S35S3fS23S35S4fS22S35A1A3A3VGS0;S23S3S9cS22S3A1M0A3S23S3Se8S23S3S96G0A3A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT; PGST] GS0 [U9b] [E9fb; E9pb] [run9b]); [exact run9b__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma SK9b_0 : ltac2:(tb__ "0|1|
S0S24S25S25SbSbA2SbA2M0A1S39SaG0S6fS12S2S96A1A1A4S39SaG0S6fS26SaS23SaS68S2fA1S23SaS4eS2fA1S23SaS4aS2fA1S23SaS122S2fA1S22SaA1A3A3A3A3S26SaS12bU0S2fA2Sb6A3A3A4A3"). Proof. vm_cast_no_check (@eq_refl _ (map skel ([O_4z nx0; O_3b nx0; O_3 nx0; O_1 nx0] ++ SKEL0 0%nat nx0 ++ PXb))). Qed.
Lemma FC9b_0 : ltac2:(tb__ "0|0|
S32ScS26ScS117VW;Vst;A2S116S115A1A3SfS2S96A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FX9b_0 : ltac2:(tb__ "0|0|
S32ScSa2SfS2S96A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FP9b_0 : ltac2:(tb__ "0|0|
S30ScS17S47A1SfS2S96A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Lemma XC9b_0 : ltac2:(tb__ "0|1|
S0S24S25SbSbA2M0A1S6S96A1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Definition CO9pb : axst := Eval vm_compute in (carveS E9pb (mkObj (BP9 nx0) (SLit 0) (SLit 1) [] DUnknown)).
Lemma HCO9b_0 : ltac2:(tb__ "0|0|
S0S3S124S96S16S63S2fA1S11Z0A1S11Z1A1S22SdA1S15A5A2SaeA3"). Proof. vm_cast_no_check (@eq_refl _ (CO9pb)). Qed.
Lemma WCO9b_0 : ltac2:(tb__ "0|0|
S0S21S10S2SaeA1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition run9qb : option (list leafA) := Eval vm_compute in (runT6 CO9pb).
Lemma run9qb__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S4A1A1M0A1S72S38Ufa0S23S35S3fS22S35A1A3S23S3SaeS22S3A1A3A4S23G0S10cS22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run9qb]). Qed.
Definition E9qb : axst := Eval vm_compute in (leafS 0 run9qb).
Lemma Cert9qb_0 : ltac2:(tb__ "0|1|
S0S21S70S38Ufa0S23S35S3fS22S35A1A3VGS0;S23S3SaeS22S3A1M0A3S23S3SeaG0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] GS0 [CO9pb] [E9qb] [run9qb]); [exact run9qb__runeq | vm_cast_no_check (eq_refl true)]. Qed.

Definition iMfb : nat := Eval vm_compute in (find_map nx0 (ss_objs (ax_S E9fb)) 0).
Definition S9afb : axst := Eval vm_compute in (osplit E9fb iMfb (SLit 6144)).
Definition S9bfb : axst := Eval vm_compute in (osplit S9afb (S iMfb) (SLit 10240)).
Lemma HS9afb_0 : ltac2:(tb__ "0|0|
S0S3S49Se8Sf2S11Z1800A1A3SecA3"). Proof. vm_cast_no_check (@eq_refl _ (S9afb)). Qed.
Lemma HS9bfb_0 : ltac2:(tb__ "0|0|
S0S3S49SecS2eSf2A1S11Z2800A1A3S92A3"). Proof. vm_cast_no_check (@eq_refl _ (S9bfb)). Qed.
Definition s9fb : wsub := Eval vm_compute in (callsub S9bfb Pre_memsetA).
Definition R9fb : list sobj := Eval vm_compute in (callR S9bfb Pre_memsetA s9fb).
Definition T9fb : axst := Eval vm_compute in (callT S9bfb Pre_memsetA Pret_ms s9fb R9fb).
Lemma He9fb_0 : ltac2:(tb__ "0|1|
S0S28S24SaA1M0A1S11dS92S3cSe0A3S2aG0SccA2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some R9fb)). Qed.
Lemma Hchk9fb_0 : ltac2:(tb__ "0|0|
S0S21S11cS92S3cSe0SccS39S4S3S7S3dA4A5S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HT9fb_0 : ltac2:(tb__ "0|0|
S0S3S11eSe0S3cS123S92SccA5Sd6A3"). Proof. vm_cast_no_check (@eq_refl _ (T9fb)). Qed.
Lemma FBC9fb_0 : ltac2:(tb__ "0|1|
S0S21S31ScS13SeS2S92A1M0A1A1SfG0A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT9fb_0 : ltac2:(tb__ "0|0|
S0S21S31ScS13SeS2Sd6A1A1A1SfS2S92A1A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXC9fb_0 : ltac2:(tb__ "0|0|
S0S21S121VGS0;SeS2S92A1A1A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition D9fb : axst := Eval vm_compute in (ax_with_facts T9fb (ss_facts (ax_S S9bfb))).
Lemma HD9fb_0 : ltac2:(tb__ "0|0|
S0S3S11bSd6SfS2S92A1A1A2Sc2A3"). Proof. vm_cast_no_check (@eq_refl _ (D9fb)). Qed.
Definition runFfb : option (list leafA) := Eval vm_compute in (runTF D9fb).
Lemma runFfb__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S4A1A1M0A1S72S38Ufa0S22S35A1S23S3Sc2S22S3A1A3A4S23G0S10eS22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [runFfb]). Qed.
Definition FFfb : axst := Eval vm_compute in (leafS 0 runFfb).
Lemma CertFfb_0 : ltac2:(tb__ "0|1|
S0S21S70S38Ufa0S22S35A1VGS0;S23S3Sc2S22S3A1M0A3S23S3S74G0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [] GS0 [D9fb] [FFfb] [runFfb]); [exact runFfb__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition swcfb : list cell := Eval vm_compute in (cells_at 5 FFfb).
Definition c1fb : list cell := Eval vm_compute in (cells_at 38 FFfb).
Definition c2fb : list cell := Eval vm_compute in (cells_at 39 FFfb).
Definition c4fb : list cell := Eval vm_compute in (cells_at 41 FFfb).
Definition c5fb : list cell := Eval vm_compute in (cells_at 45 FFfb).
Definition mcfb : list cell := Eval vm_compute in (cells_at 46 FFfb).
Definition xcfb : list cell := Eval vm_compute in (cells_at 48 FFfb).
Definition tybfb : Z := Eval vm_compute in (tyb_of mcfb).
Lemma SELFfb_0 : ltac2:(tb__ "0|0|
S0S24SaA1S128S12S2S74A1A1S42U0S2cA2A2S26SaS40VW;S86A2S26SaS137S50S2fS9eSf8SfcS100S78S112Z8S15S2cAaA3A3A3"). Proof. vm_cast_no_check (@eq_refl _ (KEPTF W swcfb ++ RT_m1 ++ RSF nx0 c1fb c2fb c4fb c5fb mcfb xcfb 8 DUnknown false)). Qed.
Lemma NDFfb_0 : ltac2:(tb__ "0|0|
S0S21S129S42U0S2cA2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDFfb_0 : ltac2:(tb__ "0|0|
S0S21S31S27S27S120R1S2bSaS12S2S74A1A1A2A2Li;S42U0S2cA2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVFfb_0 : ltac2:(tb__ "0|1|
S0S21S31S27S27S33S27S11fR1A1S42U0M0S2cA2A3Li;S3aG0S2bSaS12S2S74A1A1A2A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XFnfb_0 : ltac2:(tb__ "0|1|
S0S24S25SbSbA2M0A1S6S74A1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma BFbfb_0 : ax_base FFfb = base_sv. Proof. vm_cast_no_check (@eq_refl _ (base_sv)). Qed.
Lemma FPFfb_0 : ltac2:(tb__ "0|0|
S32ScS26ScS117VW;Vst;A2S116S115A1A3SfS2S74A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FXFfb_0 : ltac2:(tb__ "0|0|
S32ScSa2SfS2S74A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FPARfb_0 : ltac2:(tb__ "0|0|
S30ScS21ScL_;S2cS17S47A1S47X21x2SfS2S74A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Lemma Hc1fb_0 : ltac2:(tb__ "0|0|
S1S30SdS55S9eA3S1S30SdS51S9eA3S1S30SdS52S9eA3S1S30SdS56S9eA3S1S30SdS54S14S134A1A1S9eA3S30SdS53S9eA3A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (ic_pg) c1fb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c1) c1fb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c2) c1fb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_rs) c1fb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_nres (SVar V_NRES)) c1fb ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (ic_nch) c1fb ltac:(vm_cast_no_check (eq_refl true)))))))). Qed.
Lemma Hmcfb_0 : ltac2:(tb__ "0|0|
S1S30SdS5aS2fA1S78A3S1S30SdS5bS78A3S1S30SdS5cS78A3S1S30SdS58S78A3S1S30SdS59S78A3S1S30SdS57S2fA1S78A3S1S30SdS5fS78A3S1S30SdS60Sb8A1S78A3S1S30SdS5eS78A3S30SdS5dS78A3A2A2A2A2A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (mc_map nx0) mcfb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ms) mcfb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ns) mcfb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_idx) mcfb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_magic) mcfb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_cptr nx0) mcfb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_state) mcfb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_type tybfb) mcfb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_sizehi) mcfb ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (mc_size) mcfb ltac:(vm_cast_no_check (eq_refl true)))))))))))). Qed.
Lemma Htybfb_0 : ltac2:(tb__ "0|0|
S0S21S2dS2dS13dZ0Sb8A2S13eSb8Z100A2A2S13cS13fSb8Z4A2Z1A2A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma Hxcfb_0 : In (xc_map nx0) xcfb. Proof. exact (In_of_cellb (xc_map nx0) xcfb ltac:(vm_cast_no_check (eq_refl true))). Qed.
Lemma WCUfb_0 : ltac2:(tb__ "0|0|
S0S21S10S12aS2S74A1S26SaS40VW;S86A2S23SaS46S2fA1S22SaA1A3A3A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SELUfb_0 : ltac2:(tb__ "0|0|
S0S24SaA1S128S26SaS40VW;S86A2S23SaS46S2fA1S22SaA1A3A3S43U0A1A2S41VW;S86S2fA3A3"). Proof. vm_cast_no_check (@eq_refl _ (KUB W swcfb nx0)). Qed.
Lemma NDUfb_0 : nodupN (idxsU 0%nat) = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDUfb_0 : ltac2:(tb__ "0|0|
S0S21S31S27S27S120R1S2bSaS26SaS40VW;S86A2S23SaS46S2fA1S22SaA1A3A3A2A2Li;S43U0A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVUfb_0 : ltac2:(tb__ "0|1|
S0S21S31S27S27S33S27S11fR1A1S43U0M0A1A3Li;S3aG0S2bSaS26SaS40VW;S86A2S23SaS46S2fA1S22SaA1A3A3A2A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W9fb_0 : ltac2:(tb__ "0|0|
S0S21S10S44S74S41VW;S86S2fA3A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D9fb_0 : ltac2:(tb__ "0|5|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S3eS12aS2S74A1S41VW;S86S2fA3M4A2S44S74G4A2A2S2aG3S29G1G2S23G0S29SbSbS11S138A1S14P18A1A4S22G0A1A3S22ScA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(SLit TP_A, SVar 24)], @nil sprop))). Qed.
Lemma XB9fb_0 : ltac2:(tb__ "0|0|
S0S21S9SeS2S74A1A1S29SbSbS48S2fA1S14PcA1A4A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sFfb : wsub := Eval vm_compute in (infer_sub NF (S2F FFfb (KUB W swcfb nx0)) (ax_S (L_malloc_ok AE_A W st))).
Lemma ENT9fb_0 : ltac2:(tb__ "0|0|
S0S21S8S45S74S41VW;S86S2fA3S2fA3S119S118VW;Vst;A3Se4A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID9fb_0 : ltac2:(tb__ "0|0|
S0S21S132Se4S136A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma G110fb_0 : ltac2:(tb__ "0|0|
S0SbS133Se4S11aA2S48S2fA1A3"). Proof. vm_cast_no_check (@eq_refl _ (UBs nx0)). Qed.

Definition iMqb : nat := Eval vm_compute in (find_map nx0 (ss_objs (ax_S E9qb)) 0).
Definition S9aqb : axst := Eval vm_compute in (osplit E9qb iMqb (SLit 6144)).
Definition S9bqb : axst := Eval vm_compute in (osplit S9aqb (S iMqb) (SLit 10240)).
Lemma HS9aqb_0 : ltac2:(tb__ "0|0|
S0S3S49SeaSf4S11Z1800A1A3SeeA3"). Proof. vm_cast_no_check (@eq_refl _ (S9aqb)). Qed.
Lemma HS9bqb_0 : ltac2:(tb__ "0|0|
S0S3S49SeeS2eSf4A1S11Z2800A1A3S94A3"). Proof. vm_cast_no_check (@eq_refl _ (S9bqb)). Qed.
Definition s9qb : wsub := Eval vm_compute in (callsub S9bqb Pre_memsetA).
Definition R9qb : list sobj := Eval vm_compute in (callR S9bqb Pre_memsetA s9qb).
Definition T9qb : axst := Eval vm_compute in (callT S9bqb Pre_memsetA Pret_ms s9qb R9qb).
Lemma He9qb_0 : ltac2:(tb__ "0|1|
S0S28S24SaA1M0A1S11dS94S3cSe2A3S2aG0SceA2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some R9qb)). Qed.
Lemma Hchk9qb_0 : ltac2:(tb__ "0|0|
S0S21S11cS94S3cSe2SceS39S4S3S7S3dA4A5S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HT9qb_0 : ltac2:(tb__ "0|0|
S0S3S11eSe2S3cS123S94SceA5Sd8A3"). Proof. vm_cast_no_check (@eq_refl _ (T9qb)). Qed.
Lemma FBC9qb_0 : ltac2:(tb__ "0|1|
S0S21S31ScS13SeS2S94A1M0A1A1SfG0A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT9qb_0 : ltac2:(tb__ "0|0|
S0S21S31ScS13SeS2Sd8A1A1A1SfS2S94A1A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXC9qb_0 : ltac2:(tb__ "0|0|
S0S21S121VGS0;SeS2S94A1A1A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition D9qb : axst := Eval vm_compute in (ax_with_facts T9qb (ss_facts (ax_S S9bqb))).
Lemma HD9qb_0 : ltac2:(tb__ "0|0|
S0S3S11bSd8SfS2S94A1A1A2Sc4A3"). Proof. vm_cast_no_check (@eq_refl _ (D9qb)). Qed.
Definition runFqb : option (list leafA) := Eval vm_compute in (runTF D9qb).
Lemma runFqb__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S4A1A1M0A1S72S38Ufa0S22S35A1S23S3Sc4S22S3A1A3A4S23G0S110S22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [runFqb]). Qed.
Definition FFqb : axst := Eval vm_compute in (leafS 0 runFqb).
Lemma CertFqb_0 : ltac2:(tb__ "0|1|
S0S21S70S38Ufa0S22S35A1VGS0;S23S3Sc4S22S3A1M0A3S23S3S76G0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [] GS0 [D9qb] [FFqb] [runFqb]); [exact runFqb__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition swcqb : list cell := Eval vm_compute in (cells_at 5 FFqb).
Definition c1qb : list cell := Eval vm_compute in (cells_at 38 FFqb).
Definition c2qb : list cell := Eval vm_compute in (cells_at 39 FFqb).
Definition c4qb : list cell := Eval vm_compute in (cells_at 41 FFqb).
Definition c5qb : list cell := Eval vm_compute in (cells_at 45 FFqb).
Definition mcqb : list cell := Eval vm_compute in (cells_at 46 FFqb).
Definition xcqb : list cell := Eval vm_compute in (cells_at 48 FFqb).
Definition tybqb : Z := Eval vm_compute in (tyb_of mcqb).
Lemma SELFqb_0 : ltac2:(tb__ "0|0|
S0S24SaA1S128S12S2S76A1A1S42U0S20A2A2S26SaS40VW;S88A2S26SaS137S50S2fSa0SfaSfeS102S7aS114Z8S15S20AaA3A3A3"). Proof. vm_cast_no_check (@eq_refl _ (KEPTF W swcqb ++ RT_m1 ++ RSF nx0 c1qb c2qb c4qb c5qb mcqb xcqb 8 DUnknown true)). Qed.
Lemma NDFqb_0 : ltac2:(tb__ "0|0|
S0S21S129S42U0S20A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDFqb_0 : ltac2:(tb__ "0|0|
S0S21S31S27S27S120R1S2bSaS12S2S76A1A1A2A2Li;S42U0S20A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVFqb_0 : ltac2:(tb__ "0|1|
S0S21S31S27S27S33S27S11fR1A1S42U0M0S20A2A3Li;S3aG0S2bSaS12S2S76A1A1A2A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XFnqb_0 : ltac2:(tb__ "0|1|
S0S24S25SbSbA2M0A1S6S76A1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma BFbqb_0 : ax_base FFqb = base_sv. Proof. vm_cast_no_check (@eq_refl _ (base_sv)). Qed.
Lemma FPFqb_0 : ltac2:(tb__ "0|0|
S32ScS26ScS117VW;Vst;A2S116S115A1A3SfS2S76A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FXFqb_0 : ltac2:(tb__ "0|0|
S32ScSa2SfS2S76A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FPARqb_0 : ltac2:(tb__ "0|0|
S30ScS21ScL_;S20S17S47A1S47X21x2SfS2S76A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Lemma Hc1qb_0 : ltac2:(tb__ "0|0|
S1S30SdS55Sa0A3S1S30SdS51Sa0A3S1S30SdS52Sa0A3S1S30SdS56Sa0A3S1S30SdS54S14S134A1A1Sa0A3S30SdS53Sa0A3A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (ic_pg) c1qb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c1) c1qb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c2) c1qb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_rs) c1qb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_nres (SVar V_NRES)) c1qb ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (ic_nch) c1qb ltac:(vm_cast_no_check (eq_refl true)))))))). Qed.
Lemma Hmcqb_0 : ltac2:(tb__ "0|0|
S1S30SdS5aS2fA1S7aA3S1S30SdS5bS7aA3S1S30SdS5cS7aA3S1S30SdS58S7aA3S1S30SdS59S7aA3S1S30SdS57S2fA1S7aA3S1S30SdS5fS7aA3S1S30SdS60SbaA1S7aA3S1S30SdS5eS7aA3S30SdS5dS7aA3A2A2A2A2A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (mc_map nx0) mcqb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ms) mcqb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ns) mcqb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_idx) mcqb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_magic) mcqb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_cptr nx0) mcqb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_state) mcqb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_type tybqb) mcqb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_sizehi) mcqb ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (mc_size) mcqb ltac:(vm_cast_no_check (eq_refl true)))))))))))). Qed.
Lemma Htybqb_0 : ltac2:(tb__ "0|0|
S0S21S2dS2dS13dZ0SbaA2S13eSbaZ100A2A2S13cS13fSbaZ4A2Z1A2A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma Hxcqb_0 : In (xc_map nx0) xcqb. Proof. exact (In_of_cellb (xc_map nx0) xcqb ltac:(vm_cast_no_check (eq_refl true))). Qed.
Lemma WCUqb_0 : ltac2:(tb__ "0|0|
S0S21S10S12aS2S76A1S26SaS40VW;S88A2S23SaS46S2fA1S22SaA1A3A3A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SELUqb_0 : ltac2:(tb__ "0|0|
S0S24SaA1S128S26SaS40VW;S88A2S23SaS46S2fA1S22SaA1A3A3S43U0A1A2S41VW;S88S2fA3A3"). Proof. vm_cast_no_check (@eq_refl _ (KUB W swcqb nx0)). Qed.
Lemma NDUqb_0 : nodupN (idxsU 0%nat) = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDUqb_0 : ltac2:(tb__ "0|0|
S0S21S31S27S27S120R1S2bSaS26SaS40VW;S88A2S23SaS46S2fA1S22SaA1A3A3A2A2Li;S43U0A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVUqb_0 : ltac2:(tb__ "0|1|
S0S21S31S27S27S33S27S11fR1A1S43U0M0A1A3Li;S3aG0S2bSaS26SaS40VW;S88A2S23SaS46S2fA1S22SaA1A3A3A2A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W9qb_0 : ltac2:(tb__ "0|0|
S0S21S10S44S76S41VW;S88S2fA3A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D9qb_0 : ltac2:(tb__ "0|5|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S3eS12aS2S76A1S41VW;S88S2fA3M4A2S44S76G4A2A2S2aG3S29G1G2S23G0S29SbSbS11S138A1S14P18A1A4S22G0A1A3S22ScA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(SLit TP_A, SVar 24)], @nil sprop))). Qed.
Lemma XB9qb_0 : ltac2:(tb__ "0|0|
S0S21S9SeS2S76A1A1S29SbSbS48S2fA1S14PcA1A4A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sFqb : wsub := Eval vm_compute in (infer_sub NF (S2F FFqb (KUB W swcqb nx0)) (ax_S (L_malloc_ok AE_A W st))).
Lemma ENT9qb_0 : ltac2:(tb__ "0|0|
S0S21S8S45S76S41VW;S88S2fA3S2fA3S119S118VW;Vst;A3Se6A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID9qb_0 : ltac2:(tb__ "0|0|
S0S21S132Se6S136A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma G110qb_0 : ltac2:(tb__ "0|0|
S0SbS133Se6S11aA2S48S2fA1A3"). Proof. vm_cast_no_check (@eq_refl _ (UBs nx0)). Qed.
End INST.
End SpineMallocSec6IL.

(* [comment removed for export] *)
Module SpineMallocSec6I.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "leafA"; "ax_X"; "ax_setS"; "la_state"; "entailsA"; "xr_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "sprop"; "cell"; "ss_next"; "ss_facts"; "swf"; "SLit"; "sprop_below"; "ss_objs"; "SVar"; "DUnknown"; "mkObj"; "SPNot"; "sstate"; "DZero"; "SAlu"; "SPBranch"; "c_off"; "c_val"; "ob_cells"; "sv_eqb"; "@Corelib.Init.Datatypes"; "true"; "bool"; "nil"; "cons"; "list"; "prod"; "app"; "nat"; "option"; "pair"; "Some"; "length"; "false"; "andb"; "S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jm.SpineMallocSec3I"; "nx0"; "@Stdlib.Lists.List"; "In"; "forallb"; "incl"; "existsb"; "find"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@Corelib.Lists.ListDef"; "map"; "seq"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP"; "MSENT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jz.SpineMallocSec7"; "KEPTF"; "KUB"; "idxsF"; "idxsU"; "S2F"; "XF_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA"; "runsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.CertMallocSV"; "O_UBs"; "F_par"; "UBs"; "osplit"; "O_3"; "perm7"; "F_A"; "F_B"; "L3"; "O_3b"; "PGST"; "RSF"; "ic_c1"; "ic_c2"; "ic_nch"; "ic_nres"; "ic_pg"; "ic_rs"; "mc_cptr"; "mc_idx"; "mc_magic"; "mc_map"; "mc_ms"; "mc_ns"; "mc_size"; "mc_sizehi"; "mc_state"; "mc_type"; "B3"; "B4"; "BP9"; "F_g7"; "F_g8"; "F_g9"; "L3b"; "O_4z"; "a0e7"; "a2e6"; "a2e7"; "a2e8"; "fx8"; "sel7"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3"; "skel"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k4.SpineMallocSec6I.INST"; "FFfa"; "FFfb"; "FFqa"; "FFqb"; "mcfa"; "mcfb"; "mcqa"; "mcqb"; "CT6a"; "CT6b"; "CT7a"; "CT7b"; "CT8a"; "CT8b"; "CO6a"; "CO6b"; "CO8a"; "CO8b"; "swcfa"; "swcfb"; "swcqa"; "swcqb"; "CM7a"; "CM7b"; "S9bfa"; "S9bfb"; "S9bqa"; "S9bqb"; "E9pa"; "E9pb"; "U7a"; "U7b"; "U8a"; "U8b"; "U9a"; "U9b"; "c1fa"; "c1fb"; "c1qa"; "c1qb"; "FXPa"; "FXPb"; "n7a"; "n7b"; "E6a"; "E6b"; "CO7a"; "CO7b"; "CO9pa"; "CO9pb"; "D6a"; "D6b"; "D7a"; "D7b"; "D8a"; "D8b"; "ET7a"; "ET7b"; "ET8a"; "ET8b"; "PXa"; "PXb"; "tybfa"; "tybfb"; "tybqa"; "tybqb"; "C5Aa"; "C5Ab"; "C5Ba"; "C5Bb"; "CR7a"; "CR7b"; "CS7a"; "CS7b"; "D9fa"; "D9fb"; "D9qa"; "D9qb"; "R6a"; "R6b"; "R7a"; "R7b"; "R8a"; "R8b"; "R9fa"; "R9fb"; "R9qa"; "R9qb"; "T6a"; "T6b"; "T7a"; "T7b"; "T8a"; "T8b"; "T9fa"; "T9fb"; "T9qa"; "T9qb"; "s6a"; "s6b"; "s7a"; "s7b"; "s8a"; "s8b"; "s9fa"; "s9fb"; "s9qa"; "s9qb"; "sFfa"; "sFfb"; "sFqa"; "sFqb"; "E9fa"; "E9fb"; "E9qa"; "E9qb"; "S9afa"; "S9afb"; "S9aqa"; "S9aqb"; "Y6Aa"; "Y6Ab"; "Y6Ba"; "Y6Bb"; "iMfa"; "iMfb"; "iMqa"; "iMqb"; "s6Aa"; "s6Ab"; "s6Ba"; "s6Bb"; "c2fa"; "c2fb"; "c2qa"; "c2qb"; "c4fa"; "c4fb"; "c4qa"; "c4qb";
"c5fa"; "c5fb"; "c5qa"; "c5qb"; "run6Aa"; "run6Ab"; "run6Ba"; "run6Bb"; "run7a"; "run7b"; "run8a"; "run8b"; "run9a"; "run9b"; "run9qa"; "run9qb"; "runFfa"; "runFfb"; "runFqa"; "runFqb"; "xcfa"; "xcfb"; "xcqa"; "xcqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "AE_A"; "L_malloc_ok"; "V_RES"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "ltb"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocST"; "O_1"; "Pret_ms"; "carveS"; "BR"; "O_2"; "Pret_mz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "select"; "nodupN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "wsub_get"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3"; "SKEL0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Str_memsetZ"; "Pre_mszA"; "Posts_mszA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.CertMallocSS"; "V_NRES"; "V_NCH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1"; "RT_m1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall"; "isSome"; "omrg"; "oreb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jz.SpineMallocSec5I"; "C5ac"; "C5bc"; "@Stdlib.ZArith.BinInt.Z"; "eqb"; "leb"; "ltb"; "modulo"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_EQ"; "aluop"; "mulop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "merge_objs_at"; "rebase_obj_at"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocS9 SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ii.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jl.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jm.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocSec4I.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require js.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jz.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.CertMallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SegD_refl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.SecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.SecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jm.SpineMallocSec3I OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineMallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocSec4I OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertMallocSU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jq.SpineMallocSec5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jn.DepotCallS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.CertMallocSV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.js.SpineMallocSec6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jz.SpineMallocSec5I OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jz.SpineMallocSec7.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition tyb_of (mc : list cell) : Z := ltac2:(tb__ "0|4|
S28SdA1S35Lx;S34SdSdS1fS1cR1A1S11Z17f1A1A2Lc;Vmc;A3SdSbS35Lx;S1dR1A1S35R1Lt;S36Z0M0Li;S143SbSbG0Lb;La;M1Lop;M2G2S144G1Lop;M3G3S21S37SbG0La;Lw;Lsgn;S36SbS35G0Lk;Li;Ll;Xbx8Lc;G0X28x2").
Definition cells_at (i : nat) (F : axst) : list cell := ltac2:(tb__ "0|0|
S1eS3bSaVi;S13S2VF;A1A1S125S2fA1A4A1").

Section INST.
Let W : list ulink := Wcan 0. Let st : ustop := UStopLe. Let tmax : Z := 2.
Let GS0 : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3.GS nx0.

Definition PXa : list sobj := [O_blk].
Definition FXPa : list sprop := ltac2:(tb__ "0|0|
S23ScS1bS142S14S134A1S14S133A1A3S22ScA1A3").

Definition C5Aa : axst := Eval vm_compute in (ax_add_facts (F_A nx0) C5ac).
Definition C5Ba : axst := Eval vm_compute in (ax_add_facts (F_B nx0) C5ac).
Lemma HC5Aa_0 : ltac2:(tb__ "0|0|
S0S3S47S4fS2fA1S13bA2Sb6A3"). Proof. vm_cast_no_check (@eq_refl _ (C5Aa)). Qed.
Lemma HC5Ba_0 : ltac2:(tb__ "0|0|
S0S3S47S50S2fA1S13bA2Sb8A3"). Proof. vm_cast_no_check (@eq_refl _ (C5Ba)). Qed.
Lemma FBAa_0 : ltac2:(tb__ "0|0|
S0S21S31ScS12SeS2S13bA1A1A1S4fS2fA1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBBa_0 : ltac2:(tb__ "0|0|
S0S21S31ScS12SeS2S13bA1A1A1S50S2fA1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition run6Aa : option (list leafA) := Eval vm_compute in (runT6 C5Aa).
Lemma run6Aa__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S4A1A1M0A1S48S38Ufa0S23S35S3eS22S35A1A3S23S3Sb6S22S3A1A3A4S23G0S104S22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run6Aa]). Qed.
Definition Y6Aa : axst := Eval vm_compute in (leafS 0 run6Aa).
Lemma Cert6Aa_0 : ltac2:(tb__ "0|1|
S0S21S46S38Ufa0S23S35S3eS22S35A1A3VGS0;S23S3Sb6S22S3A1M0A3S23S3SecG0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] GS0 [C5Aa] [Y6Aa] [run6Aa]); [exact run6Aa__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition run6Ba : option (list leafA) := Eval vm_compute in (runT6 C5Ba).
Lemma run6Ba__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S4A1A1M0A1S48S38Ufa0S23S35S3eS22S35A1A3S23S3Sb8S22S3A1A3A4S23G0S106S22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run6Ba]). Qed.
Definition Y6Ba : axst := Eval vm_compute in (leafS 0 run6Ba).
Lemma Cert6Ba_0 : ltac2:(tb__ "0|1|
S0S21S46S38Ufa0S23S35S3eS22S35A1A3VGS0;S23S3Sb8S22S3A1M0A3S23S3SeeG0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] GS0 [C5Ba] [Y6Ba] [run6Ba]); [exact run6Ba__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition E6a : axst := Eval vm_compute in (rmF (F_A nx0) Y6Aa).
Definition s6Aa : wsub := Eval vm_compute in (infer_sub GS0 (ax_S Y6Aa) (ax_S E6a)).
Lemma E6Aa_0 : ltac2:(tb__ "0|0|
S0S21S8SecSa0Sf4A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma I6Aa_0 : ltac2:(tb__ "0|0|
S0S21S12dSf4VGS0;A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition s6Ba : wsub := Eval vm_compute in (infer_sub GS0 (ax_S Y6Ba) (ax_S E6a)).
Lemma E6Ba_0 : ltac2:(tb__ "0|0|
S0S21S8SeeSa0Sf6A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma I6Ba_0 : ltac2:(tb__ "0|0|
S0S21S12dSf6VGS0;A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition CT6a : axst := Eval vm_compute in (rstS E6a ru6 []).
Definition CO6a : axst := Eval vm_compute in (carveS CT6a (O_3 nx0)).
Lemma WC6a_0 : ltac2:(tb__ "0|0|
S0S21S10S2S7cA1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DF6a_0 : ltac2:(tb__ "0|4|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S45S2Sa0A1S2S7cA1A2S2aG3S29G1G2S23G0S29SbSbS6eS2fA1S51A4S22G0A1A3S22ScA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(a2e6 nx0, L3)], @nil sprop))). Qed.
Lemma NX6a_0 : ltac2:(tb__ "0|0|
S0S36SeS2S7cA1A1SeS2Sa0A1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S E6a))). Qed.
Lemma HC6a_0 : ltac2:(tb__ "0|0|
S0S3S6Sa0S2S7cA1A2S7cA3"). Proof. vm_cast_no_check (@eq_refl _ (CT6a)). Qed.
Lemma SK6a_0 : ltac2:(tb__ "0|1|
S0S24S25S25SbSbA2SbA2M0A1S39SaG0S73S13S2S7cA1A1A4S39SaG0S73S26SaS23SaS129S2fA1S23SaS125S2fA1S22SaA1A3A3S26SaS130U0S2fA2Sb0A3A3A4A3"). Proof. vm_cast_no_check (@eq_refl _ (map skel ([O_2 nx0; O_1 nx0] ++ SKEL0 0%nat nx0 ++ PXa))). Qed.
Lemma FC6a_0 : ltac2:(tb__ "0|0|
S32ScS26ScS11aVW;Vst;A2S119S118A1A3SfS2S7cA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FX6a_0 : ltac2:(tb__ "0|0|
S32ScS9cSfS2S7cA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma XC6a_0 : ltac2:(tb__ "0|1|
S0S24S25SbSbA2M0A1S5S7cA1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma HCO6a_0 : ltac2:(tb__ "0|0|
S0S3S127S7cS16S65S2fA1S11Z0A1S51S22SdA1S15A5A2S82A3"). Proof. vm_cast_no_check (@eq_refl _ (CO6a)). Qed.
Lemma WCO6a_0 : ltac2:(tb__ "0|0|
S0S21S10S2S82A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition s6a : wsub := Eval vm_compute in (callsub CO6a Pre_memsetA).
Definition R6a : list sobj := Eval vm_compute in (callR CO6a Pre_memsetA s6a).
Definition T6a : axst := Eval vm_compute in (callT CO6a Pre_memsetA Pret_ms s6a R6a).
Lemma He6a_0 : ltac2:(tb__ "0|1|
S0S28S24SaA1M0A1S120S82S3cSd6A3S2aG0Sc2A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some R6a)). Qed.
Lemma Hchk6a_0 : ltac2:(tb__ "0|0|
S0S21S11fS82S3cSd6Sc2S39S4S3S7S3dA4A5S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HT6a_0 : ltac2:(tb__ "0|0|
S0S3S121Sd6S3cS126S82Sc2A5SccA3"). Proof. vm_cast_no_check (@eq_refl _ (T6a)). Qed.
Lemma FBC6a_0 : ltac2:(tb__ "0|1|
S0S21S31ScS12SeS2S82A1M0A1A1SfG0A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT6a_0 : ltac2:(tb__ "0|0|
S0S21S31ScS12SeS2SccA1A1A1SfS2S82A1A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXC6a_0 : ltac2:(tb__ "0|0|
S0S21S124VGS0;SeS2S82A1A1A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition D6a : axst := Eval vm_compute in (ax_with_facts T6a (ss_facts (ax_S CO6a))).
Lemma HD6a_0 : ltac2:(tb__ "0|0|
S0S3S11eSccSfS2S82A1A1A2Sa6A3"). Proof. vm_cast_no_check (@eq_refl _ (D6a)). Qed.

Definition U7a : axst := Eval vm_compute in (U7p nx0 D6a).
Lemma WU7a_0 : ltac2:(tb__ "0|0|
S0S21S10S2S92A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DU7a_0 : ltac2:(tb__ "0|4|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S45S2Sa6A1S2S92A1A2S2aG3S29G1G2S22G0A1S68S2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g7 nx0))). Qed.
Lemma NXU7a_0 : ltac2:(tb__ "0|0|
S0S36SeS2S92A1A1SeS2Sa6A1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D6a))). Qed.
Lemma HU7a_0 : ltac2:(tb__ "0|0|
S0S3S6Sa6S2S92A1A2S92A3"). Proof. vm_cast_no_check (@eq_refl _ (U7a)). Qed.
Definition run7a : option (list leafA) := Eval vm_compute in (runT6 U7a).
Lemma run7a__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S4A1A1M0A1S48S38Ufa0S23S35S3eS22S35A1A3S23S3S92S22S3A1A3A4S23G0S108S22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run7a]). Qed.
Definition ET7a : axst := Eval vm_compute in (leafS 0 run7a).
Lemma Cert7a_0 : ltac2:(tb__ "0|1|
S0S21S46S38Ufa0S23S35S3eS22S35A1A3VGS0;S23S3S92S22S3A1M0A3S23S3SacG0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] GS0 [U7a] [ET7a] [run7a]); [exact run7a__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition CT7a : axst := Eval vm_compute in (rstS ET7a (ru7 nx0) []).
Definition CO7a : axst := Eval vm_compute in (carveS CT7a (O_3n nx0)).
Definition CR7a : axst := Eval vm_compute in (DepotCall.oreb CO7a 1).
Definition n7a : nat := Eval vm_compute in (length (ss_objs (ax_S CR7a))).
Definition CS7a : axst := Eval vm_compute in (sel7 CR7a).
Definition CM7a : axst := Eval vm_compute in (DepotCall.omrg CS7a 1).
Lemma WC7a_0 : ltac2:(tb__ "0|0|
S0S21S10S2S7eA1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DF7a_0 : ltac2:(tb__ "0|4|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S45S2SacA1S2S7eA1A2S2aG3S29G1G2S23G0S29SbSbS6dS2fA1S128S2fA1A4S23G0S29SbSbS6fS2fA1S6bA4S22G0A1A3A3S22ScA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(a0e7 nx0, BR nx0); (a2e7 nx0, L3b)], @nil sprop))). Qed.
Lemma NX7a_0 : ltac2:(tb__ "0|0|
S0S36SeS2S7eA1A1SeS2SacA1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S ET7a))). Qed.
Lemma HC7a_0 : ltac2:(tb__ "0|0|
S0S3S6SacS2S7eA1A2S7eA3"). Proof. vm_cast_no_check (@eq_refl _ (CT7a)). Qed.
Lemma SK7a_0 : ltac2:(tb__ "0|1|
S0S24S25S25SbSbA2SbA2M0A1S39SaG0S73S13S2S7eA1A1A4S39SaG0S73S26SaS23SaS4dS2fA1S23SaS129S2fA1S23SaS125S2fA1S22SaA1A3A3A3S26SaS130U0S2fA2Sb0A3A3A4A3"). Proof. vm_cast_no_check (@eq_refl _ (map skel ([O_3 nx0; O_2 nx0; O_1 nx0] ++ SKEL0 0%nat nx0 ++ PXa))). Qed.
Lemma FC7a_0 : ltac2:(tb__ "0|0|
S32ScS26ScS11aVW;Vst;A2S119S118A1A3SfS2S7eA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FX7a_0 : ltac2:(tb__ "0|0|
S32ScS9cSfS2S7eA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma XC7a_0 : ltac2:(tb__ "0|1|
S0S24S25SbSbA2M0A1S5S7eA1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma HCO7a_0 : ltac2:(tb__ "0|0|
S0S3S127S7eS16S128S2fA1S11Z0A1S11Z100A1S22SdA1S15A5A2Sa2A3"). Proof. vm_cast_no_check (@eq_refl _ (CO7a)). Qed.
Lemma WCO7a_0 : ltac2:(tb__ "0|0|
S0S21S10S2Sa2A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RB7a_0 : ltac2:(tb__ "0|0|
S0S21S138S18S146S2Sa2A1U1A2A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HCR7a_0 : ltac2:(tb__ "0|0|
S0S3S13aSa2U1A2SbaA3"). Proof. vm_cast_no_check (@eq_refl _ (CR7a)). Qed.
Lemma LEN7a_0 : ltac2:(tb__ "0|0|
S0S27S2bSaS13S2SbaA1A1A2S9eA3"). Proof. vm_cast_no_check (@eq_refl _ (n7a)). Qed.
Lemma PERM_nd7a_0 : ltac2:(tb__ "0|0|
S0S21S12cS4eS9eA1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma PERM_lt7a_0 : ltac2:(tb__ "0|0|
S0S21S31S27S27S123R1S9eA2Li;S4eS9eA1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma PERM_cov7a_0 : ltac2:(tb__ "0|0|
S0S21S31S27S27S33S27S122R1A1S4eS9eA1A3Li;S3aU0S9eA2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HCS7a_0 : ltac2:(tb__ "0|0|
S0S3S72SbaA1SbcA3"). Proof. vm_cast_no_check (@eq_refl _ (CS7a)). Qed.
Lemma MRG7a_0 : ltac2:(tb__ "0|0|
S0S21S138S18S145S2SbcA1U1A2A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HCM7a_0 : ltac2:(tb__ "0|0|
S0S3S139SbcU1A2S8aA3"). Proof. vm_cast_no_check (@eq_refl _ (CM7a)). Qed.
Definition s7a : wsub := Eval vm_compute in (callsub CM7a Pre_memsetA).
Definition R7a : list sobj := Eval vm_compute in (callR CM7a Pre_memsetA s7a).
Definition T7a : axst := Eval vm_compute in (callT CM7a Pre_memsetA Pret_ms s7a R7a).
Lemma He7a_0 : ltac2:(tb__ "0|1|
S0S28S24SaA1M0A1S120S8aS3cSd8A3S2aG0Sc4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some R7a)). Qed.
Lemma Hchk7a_0 : ltac2:(tb__ "0|0|
S0S21S11fS8aS3cSd8Sc4S39S4S3S7S3dA4A5S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HT7a_0 : ltac2:(tb__ "0|0|
S0S3S121Sd8S3cS126S8aSc4A5SceA3"). Proof. vm_cast_no_check (@eq_refl _ (T7a)). Qed.
Lemma FBC7a_0 : ltac2:(tb__ "0|1|
S0S21S31ScS12SeS2S8aA1M0A1A1SfG0A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT7a_0 : ltac2:(tb__ "0|0|
S0S21S31ScS12SeS2SceA1A1A1SfS2S8aA1A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXC7a_0 : ltac2:(tb__ "0|0|
S0S21S124VGS0;SeS2S8aA1A1A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition D7a : axst := Eval vm_compute in (ax_with_facts T7a (ss_facts (ax_S CM7a))).
Lemma HD7a_0 : ltac2:(tb__ "0|0|
S0S3S11eSceSfS2S8aA1A1A2Sa8A3"). Proof. vm_cast_no_check (@eq_refl _ (D7a)). Qed.

Definition U8a : axst := Eval vm_compute in (U8p nx0 D7a).
Lemma WU8a_0 : ltac2:(tb__ "0|0|
S0S21S10S2S94A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DU8a_0 : ltac2:(tb__ "0|4|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S45S2Sa8A1S2S94A1A2S2aG3S29G1G2S22G0A1S69S2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g8 nx0))). Qed.
Lemma NXU8a_0 : ltac2:(tb__ "0|0|
S0S36SeS2S94A1A1SeS2Sa8A1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D7a))). Qed.
Lemma HU8a_0 : ltac2:(tb__ "0|0|
S0S3S6Sa8S2S94A1A2S94A3"). Proof. vm_cast_no_check (@eq_refl _ (U8a)). Qed.
Definition run8a : option (list leafA) := Eval vm_compute in (runT6 U8a).
Lemma run8a__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S4A1A1M0A1S48S38Ufa0S23S35S3eS22S35A1A3S23S3S94S22S3A1A3A4S23G0S10aS22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run8a]). Qed.
Definition ET8a : axst := Eval vm_compute in (leafS 0 run8a).
Lemma Cert8a_0 : ltac2:(tb__ "0|1|
S0S21S46S38Ufa0S23S35S3eS22S35A1A3VGS0;S23S3S94S22S3A1M0A3S23S3SaeG0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] GS0 [U8a] [ET8a] [run8a]); [exact run8a__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition CT8a : axst := Eval vm_compute in (CT8p nx0 ET8a).
Definition CO8a : axst := Eval vm_compute in (carveS CT8a (O_4 nx0)).
Lemma WC8a_0 : ltac2:(tb__ "0|0|
S0S21S10S2S80A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DF8a_0 : ltac2:(tb__ "0|4|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S45S2SaeA1S2S80A1A2S2aG3S29G1G2S22G0A1S71S2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), fx8 nx0))). Qed.
Lemma NX8a_0 : ltac2:(tb__ "0|0|
S0S36SeS2S80A1A1SeS2SaeA1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S ET8a))). Qed.
Lemma HC8a_0 : ltac2:(tb__ "0|0|
S0S3S6SaeS2S80A1A2S80A3"). Proof. vm_cast_no_check (@eq_refl _ (CT8a)). Qed.
Lemma SK8a_0 : ltac2:(tb__ "0|1|
S0S24S25S25SbSbA2SbA2M0A1S39SaG0S73S13S2S80A1A1A4S39SaG0S73S26SaS23SaS52S2fA1S23SaS4dS2fA1S23SaS125S2fA1S22SaA1A3A3A3S26SaS130U0S2fA2Sb0A3A3A4A3"). Proof. vm_cast_no_check (@eq_refl _ (map skel ([O_3b nx0; O_3 nx0; O_1 nx0] ++ SKEL0 0%nat nx0 ++ PXa))). Qed.
Lemma FC8a_0 : ltac2:(tb__ "0|0|
S32ScS26ScS11aVW;Vst;A2S119S118A1A3SfS2S80A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FX8a_0 : ltac2:(tb__ "0|0|
S32ScS9cSfS2S80A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma XC8a_0 : ltac2:(tb__ "0|1|
S0S24S25SbSbA2M0A1S5S80A1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma HCO8a_0 : ltac2:(tb__ "0|0|
S0S3S127S80S16S66S2fA1S11Z0A1S70S2fA1S22SdA1S15A5A2S84A3"). Proof. vm_cast_no_check (@eq_refl _ (CO8a)). Qed.
Lemma WCO8a_0 : ltac2:(tb__ "0|0|
S0S21S10S2S84A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition s8a : wsub := Eval vm_compute in (callsub CO8a Pre_mszA).
Definition R8a : list sobj := Eval vm_compute in (callR CO8a Pre_mszA s8a).
Definition T8a : axst := Eval vm_compute in (callT CO8a Pre_mszA Pret_mz s8a R8a).
Lemma He8a_0 : ltac2:(tb__ "0|1|
S0S28S24SaA1M0A1S120S84S131SdaA3S2aG0Sc6A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some R8a)). Qed.
Lemma Hchk8a_0 : ltac2:(tb__ "0|0|
S0S21S11fS84S131SdaSc6S39S4S3S7S132A4A5S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HT8a_0 : ltac2:(tb__ "0|0|
S0S3S121SdaS131S12aS84Sc6A5Sd0A3"). Proof. vm_cast_no_check (@eq_refl _ (T8a)). Qed.
Lemma FBC8a_0 : ltac2:(tb__ "0|1|
S0S21S31ScS12SeS2S84A1M0A1A1SfG0A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT8a_0 : ltac2:(tb__ "0|0|
S0S21S31ScS12SeS2Sd0A1A1A1SfS2S84A1A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXC8a_0 : ltac2:(tb__ "0|0|
S0S21S124VGS0;SeS2S84A1A1A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition D8a : axst := Eval vm_compute in (ax_with_facts T8a (ss_facts (ax_S CO8a))).
Lemma HD8a_0 : ltac2:(tb__ "0|0|
S0S3S11eSd0SfS2S84A1A1A2SaaA3"). Proof. vm_cast_no_check (@eq_refl _ (D8a)). Qed.

Definition U9a : axst := Eval vm_compute in (U9p nx0 D8a).
Lemma WU9a_0 : ltac2:(tb__ "0|0|
S0S21S10S2S96A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DU9a_0 : ltac2:(tb__ "0|4|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S45S2SaaA1S2S96A1A2S2aG3S29G1G2S22G0A1S6aS2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g9 nx0))). Qed.
Lemma NXU9a_0 : ltac2:(tb__ "0|0|
S0S36SeS2S96A1A1SeS2SaaA1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D8a))). Qed.
Lemma HU9a_0 : ltac2:(tb__ "0|0|
S0S3S6SaaS2S96A1A2S96A3"). Proof. vm_cast_no_check (@eq_refl _ (U9a)). Qed.
Definition run9a : option (list leafA) := Eval vm_compute in (runT9 U9a).
Lemma run9a__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S4A1A1M0A1S48S38Ufa0S23S35S3eS23S35S53S22S35A1A3A3S23S3S96S22S3A1A3A4S23G0S10cS22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run9a]). Qed.
Definition E9fa : axst := Eval vm_compute in (leafS 0 run9a).
Definition E9pa : axst := Eval vm_compute in (leafS 1 run9a).
Lemma Cert9a_0 : ltac2:(tb__ "0|1|
S0S21S46S38Ufa0S23S35S3eS23S35S53S22S35A1A3A3VGS0;S23S3S96S22S3A1M0A3S23S3Se4S23S3S90G0A3A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT; PGST] GS0 [U9a] [E9fa; E9pa] [run9a]); [exact run9a__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma SK9a_0 : ltac2:(tb__ "0|1|
S0S24S25S25SbSbA2SbA2M0A1S39SaG0S73S13S2S90A1A1A4S39SaG0S73S26SaS23SaS6cS2fA1S23SaS52S2fA1S23SaS4dS2fA1S23SaS125S2fA1S22SaA1A3A3A3A3S26SaS130U0S2fA2Sb0A3A3A4A3"). Proof. vm_cast_no_check (@eq_refl _ (map skel ([O_4z nx0; O_3b nx0; O_3 nx0; O_1 nx0] ++ SKEL0 0%nat nx0 ++ PXa))). Qed.
Lemma FC9a_0 : ltac2:(tb__ "0|0|
S32ScS26ScS11aVW;Vst;A2S119S118A1A3SfS2S90A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FX9a_0 : ltac2:(tb__ "0|0|
S32ScS9cSfS2S90A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FP9a_0 : ltac2:(tb__ "0|0|
S30ScS17S4aA1SfS2S90A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Lemma XC9a_0 : ltac2:(tb__ "0|1|
S0S24S25SbSbA2M0A1S5S90A1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Definition CO9pa : axst := Eval vm_compute in (carveS E9pa (mkObj (BP9 nx0) (SLit 0) (SLit 1) [] DUnknown)).
Lemma HCO9a_0 : ltac2:(tb__ "0|0|
S0S3S127S90S16S67S2fA1S11Z0A1S11Z1A1S22SdA1S15A5A2Sa4A3"). Proof. vm_cast_no_check (@eq_refl _ (CO9pa)). Qed.
Lemma WCO9a_0 : ltac2:(tb__ "0|0|
S0S21S10S2Sa4A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition run9qa : option (list leafA) := Eval vm_compute in (runT6 CO9pa).
Lemma run9qa__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S4A1A1M0A1S48S38Ufa0S23S35S3eS22S35A1A3S23S3Sa4S22S3A1A3A4S23G0S10eS22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run9qa]). Qed.
Definition E9qa : axst := Eval vm_compute in (leafS 0 run9qa).
Lemma Cert9qa_0 : ltac2:(tb__ "0|1|
S0S21S46S38Ufa0S23S35S3eS22S35A1A3VGS0;S23S3Sa4S22S3A1M0A3S23S3Se6G0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] GS0 [CO9pa] [E9qa] [run9qa]); [exact run9qa__runeq | vm_cast_no_check (eq_refl true)]. Qed.

Definition iMfa : nat := Eval vm_compute in (find_map nx0 (ss_objs (ax_S E9fa)) 0).
Definition S9afa : axst := Eval vm_compute in (osplit E9fa iMfa (SLit 6144)).
Definition S9bfa : axst := Eval vm_compute in (osplit S9afa (S iMfa) (SLit 10240)).
Lemma HS9afa_0 : ltac2:(tb__ "0|0|
S0S3S4cSe4Sf0S11Z1800A1A3Se8A3"). Proof. vm_cast_no_check (@eq_refl _ (S9afa)). Qed.
Lemma HS9bfa_0 : ltac2:(tb__ "0|0|
S0S3S4cSe8S2eSf0A1S11Z2800A1A3S8cA3"). Proof. vm_cast_no_check (@eq_refl _ (S9bfa)). Qed.
Definition s9fa : wsub := Eval vm_compute in (callsub S9bfa Pre_memsetA).
Definition R9fa : list sobj := Eval vm_compute in (callR S9bfa Pre_memsetA s9fa).
Definition T9fa : axst := Eval vm_compute in (callT S9bfa Pre_memsetA Pret_ms s9fa R9fa).
Lemma He9fa_0 : ltac2:(tb__ "0|1|
S0S28S24SaA1M0A1S120S8cS3cSdcA3S2aG0Sc8A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some R9fa)). Qed.
Lemma Hchk9fa_0 : ltac2:(tb__ "0|0|
S0S21S11fS8cS3cSdcSc8S39S4S3S7S3dA4A5S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HT9fa_0 : ltac2:(tb__ "0|0|
S0S3S121SdcS3cS126S8cSc8A5Sd2A3"). Proof. vm_cast_no_check (@eq_refl _ (T9fa)). Qed.
Lemma FBC9fa_0 : ltac2:(tb__ "0|1|
S0S21S31ScS12SeS2S8cA1M0A1A1SfG0A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT9fa_0 : ltac2:(tb__ "0|0|
S0S21S31ScS12SeS2Sd2A1A1A1SfS2S8cA1A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXC9fa_0 : ltac2:(tb__ "0|0|
S0S21S124VGS0;SeS2S8cA1A1A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition D9fa : axst := Eval vm_compute in (ax_with_facts T9fa (ss_facts (ax_S S9bfa))).
Lemma HD9fa_0 : ltac2:(tb__ "0|0|
S0S3S11eSd2SfS2S8cA1A1A2SbeA3"). Proof. vm_cast_no_check (@eq_refl _ (D9fa)). Qed.
Definition runFfa : option (list leafA) := Eval vm_compute in (runTF D9fa).
Lemma runFfa__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S4A1A1M0A1S48S38Ufa0S22S35A1S23S3SbeS22S3A1A3A4S23G0S110S22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [runFfa]). Qed.
Definition FFfa : axst := Eval vm_compute in (leafS 0 runFfa).
Lemma CertFfa_0 : ltac2:(tb__ "0|1|
S0S21S46S38Ufa0S22S35A1VGS0;S23S3SbeS22S3A1M0A3S23S3S74G0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [] GS0 [D9fa] [FFfa] [runFfa]); [exact runFfa__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition swcfa : list cell := Eval vm_compute in (cells_at 5 FFfa).
Definition c1fa : list cell := Eval vm_compute in (cells_at 38 FFfa).
Definition c2fa : list cell := Eval vm_compute in (cells_at 39 FFfa).
Definition c4fa : list cell := Eval vm_compute in (cells_at 41 FFfa).
Definition c5fa : list cell := Eval vm_compute in (cells_at 45 FFfa).
Definition mcfa : list cell := Eval vm_compute in (cells_at 46 FFfa).
Definition xcfa : list cell := Eval vm_compute in (cells_at 48 FFfa).
Definition tybfa : Z := Eval vm_compute in (tyb_of mcfa).
Lemma SELFfa_0 : ltac2:(tb__ "0|0|
S0S24SaA1S12bS13S2S74A1A1S41U0S2cA2A2S26SaS3fVW;S86A2S26SaS136S54S2fS98Sf8SfcS100S78S114Z20000S19S2cAaA3A3A3"). Proof. vm_cast_no_check (@eq_refl _ (KEPTF W swcfa ++ RT_m1 ++ RSF nx0 c1fa c2fa c4fa c5fa mcfa xcfa 131072 DZero false)). Qed.
Lemma NDFfa_0 : ltac2:(tb__ "0|0|
S0S21S12cS41U0S2cA2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDFfa_0 : ltac2:(tb__ "0|0|
S0S21S31S27S27S123R1S2bSaS13S2S74A1A1A2A2Li;S41U0S2cA2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVFfa_0 : ltac2:(tb__ "0|1|
S0S21S31S27S27S33S27S122R1A1S41U0M0S2cA2A3Li;S3aG0S2bSaS13S2S74A1A1A2A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XFnfa_0 : ltac2:(tb__ "0|1|
S0S24S25SbSbA2M0A1S5S74A1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma BFbfa_0 : ax_base FFfa = base_sv. Proof. vm_cast_no_check (@eq_refl _ (base_sv)). Qed.
Lemma FPFfa_0 : ltac2:(tb__ "0|0|
S32ScS26ScS11aVW;Vst;A2S119S118A1A3SfS2S74A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FXFfa_0 : ltac2:(tb__ "0|0|
S32ScS9cSfS2S74A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FPARfa_0 : ltac2:(tb__ "0|0|
S30ScS21ScL_;S2cS17S4aA1S4aX21x2SfS2S74A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Lemma Hc1fa_0 : ltac2:(tb__ "0|0|
S1S30SdS59S98A3S1S30SdS55S98A3S1S30SdS56S98A3S1S30SdS5aS98A3S1S30SdS58S1aS141S14S133A1S11Z4000A1A3A1S98A3S30SdS57S98A3A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (ic_pg) c1fa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c1) c1fa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c2) c1fa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_rs) c1fa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_nres (SAlu ALU_ADD (SVar V_NRES) (SLit 16384))) c1fa ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (ic_nch) c1fa ltac:(vm_cast_no_check (eq_refl true)))))))). Qed.
Lemma Hmcfa_0 : ltac2:(tb__ "0|0|
S1S30SdS5eS2fA1S78A3S1S30SdS5fS78A3S1S30SdS60S78A3S1S30SdS5cS78A3S1S30SdS5dS78A3S1S30SdS5bS2fA1S78A3S1S30SdS63S78A3S1S30SdS64Sb2A1S78A3S1S30SdS62S78A3S30SdS61S78A3A2A2A2A2A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (mc_map nx0) mcfa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ms) mcfa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ns) mcfa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_idx) mcfa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_magic) mcfa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_cptr nx0) mcfa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_state) mcfa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_type tybfa) mcfa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_sizehi) mcfa ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (mc_size) mcfa ltac:(vm_cast_no_check (eq_refl true)))))))))))). Qed.
Lemma Htybfa_0 : ltac2:(tb__ "0|0|
S0S21S2dS2dS13eZ0Sb2A2S13fSb2Z100A2A2S13dS140Sb2Z4A2Z1A2A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma Hxcfa_0 : In (xc_map nx0) xcfa. Proof. exact (In_of_cellb (xc_map nx0) xcfa ltac:(vm_cast_no_check (eq_refl true))). Qed.
Lemma WCUfa_0 : ltac2:(tb__ "0|0|
S0S21S10S12fS2S74A1S26SaS3fVW;S86A2S23SaS49S2fA1S22SaA1A3A3A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SELUfa_0 : ltac2:(tb__ "0|0|
S0S24SaA1S12bS26SaS3fVW;S86A2S23SaS49S2fA1S22SaA1A3A3S42U0A1A2S40VW;S86S2fA3A3"). Proof. vm_cast_no_check (@eq_refl _ (KUB W swcfa nx0)). Qed.
Lemma NDUfa_0 : nodupN (idxsU 0%nat) = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDUfa_0 : ltac2:(tb__ "0|0|
S0S21S31S27S27S123R1S2bSaS26SaS3fVW;S86A2S23SaS49S2fA1S22SaA1A3A3A2A2Li;S42U0A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVUfa_0 : ltac2:(tb__ "0|1|
S0S21S31S27S27S33S27S122R1A1S42U0M0A1A3Li;S3aG0S2bSaS26SaS3fVW;S86A2S23SaS49S2fA1S22SaA1A3A3A2A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W9fa_0 : ltac2:(tb__ "0|0|
S0S21S10S43S74S40VW;S86S2fA3A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D9fa_0 : ltac2:(tb__ "0|5|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S45S12fS2S74A1S40VW;S86S2fA3M4A2S43S74G4A2A2S2aG3S29G1G2S23G0S29SbSbS11S137A1S14P18A1A4S22G0A1A3S22ScA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(SLit TP_A, SVar 24)], @nil sprop))). Qed.
Lemma XB9fa_0 : ltac2:(tb__ "0|0|
S0S21S9SeS2S74A1A1S29SbSbS4bS2fA1S14PcA1A4A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sFfa : wsub := Eval vm_compute in (infer_sub NF (S2F FFfa (KUB W swcfa nx0)) (ax_S (L_malloc_ok AE_A W st))).
Lemma ENT9fa_0 : ltac2:(tb__ "0|0|
S0S21S8S44S74S40VW;S86S2fA3S2fA3S11cS11bVW;Vst;A3Se0A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID9fa_0 : ltac2:(tb__ "0|0|
S0S21S12dSe0S135A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma G110fa_0 : ltac2:(tb__ "0|0|
S0SbS12eSe0S11dA2S4bS2fA1A3"). Proof. vm_cast_no_check (@eq_refl _ (UBs nx0)). Qed.

Definition iMqa : nat := Eval vm_compute in (find_map nx0 (ss_objs (ax_S E9qa)) 0).
Definition S9aqa : axst := Eval vm_compute in (osplit E9qa iMqa (SLit 6144)).
Definition S9bqa : axst := Eval vm_compute in (osplit S9aqa (S iMqa) (SLit 10240)).
Lemma HS9aqa_0 : ltac2:(tb__ "0|0|
S0S3S4cSe6Sf2S11Z1800A1A3SeaA3"). Proof. vm_cast_no_check (@eq_refl _ (S9aqa)). Qed.
Lemma HS9bqa_0 : ltac2:(tb__ "0|0|
S0S3S4cSeaS2eSf2A1S11Z2800A1A3S8eA3"). Proof. vm_cast_no_check (@eq_refl _ (S9bqa)). Qed.
Definition s9qa : wsub := Eval vm_compute in (callsub S9bqa Pre_memsetA).
Definition R9qa : list sobj := Eval vm_compute in (callR S9bqa Pre_memsetA s9qa).
Definition T9qa : axst := Eval vm_compute in (callT S9bqa Pre_memsetA Pret_ms s9qa R9qa).
Lemma He9qa_0 : ltac2:(tb__ "0|1|
S0S28S24SaA1M0A1S120S8eS3cSdeA3S2aG0ScaA2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some R9qa)). Qed.
Lemma Hchk9qa_0 : ltac2:(tb__ "0|0|
S0S21S11fS8eS3cSdeScaS39S4S3S7S3dA4A5S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HT9qa_0 : ltac2:(tb__ "0|0|
S0S3S121SdeS3cS126S8eScaA5Sd4A3"). Proof. vm_cast_no_check (@eq_refl _ (T9qa)). Qed.
Lemma FBC9qa_0 : ltac2:(tb__ "0|1|
S0S21S31ScS12SeS2S8eA1M0A1A1SfG0A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT9qa_0 : ltac2:(tb__ "0|0|
S0S21S31ScS12SeS2Sd4A1A1A1SfS2S8eA1A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXC9qa_0 : ltac2:(tb__ "0|0|
S0S21S124VGS0;SeS2S8eA1A1A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition D9qa : axst := Eval vm_compute in (ax_with_facts T9qa (ss_facts (ax_S S9bqa))).
Lemma HD9qa_0 : ltac2:(tb__ "0|0|
S0S3S11eSd4SfS2S8eA1A1A2Sc0A3"). Proof. vm_cast_no_check (@eq_refl _ (D9qa)). Qed.
Definition runFqa : option (list leafA) := Eval vm_compute in (runTF D9qa).
Lemma runFqa__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S4A1A1M0A1S48S38Ufa0S22S35A1S23S3Sc0S22S3A1A3A4S23G0S112S22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [runFqa]). Qed.
Definition FFqa : axst := Eval vm_compute in (leafS 0 runFqa).
Lemma CertFqa_0 : ltac2:(tb__ "0|1|
S0S21S46S38Ufa0S22S35A1VGS0;S23S3Sc0S22S3A1M0A3S23S3S76G0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [] GS0 [D9qa] [FFqa] [runFqa]); [exact runFqa__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition swcqa : list cell := Eval vm_compute in (cells_at 5 FFqa).
Definition c1qa : list cell := Eval vm_compute in (cells_at 38 FFqa).
Definition c2qa : list cell := Eval vm_compute in (cells_at 39 FFqa).
Definition c4qa : list cell := Eval vm_compute in (cells_at 41 FFqa).
Definition c5qa : list cell := Eval vm_compute in (cells_at 45 FFqa).
Definition mcqa : list cell := Eval vm_compute in (cells_at 46 FFqa).
Definition xcqa : list cell := Eval vm_compute in (cells_at 48 FFqa).
Definition tybqa : Z := Eval vm_compute in (tyb_of mcqa).
Lemma SELFqa_0 : ltac2:(tb__ "0|0|
S0S24SaA1S12bS13S2S76A1A1S41U0S20A2A2S26SaS3fVW;S88A2S26SaS136S54S2fS9aSfaSfeS102S7aS116Z20000S19S20AaA3A3A3"). Proof. vm_cast_no_check (@eq_refl _ (KEPTF W swcqa ++ RT_m1 ++ RSF nx0 c1qa c2qa c4qa c5qa mcqa xcqa 131072 DZero true)). Qed.
Lemma NDFqa_0 : ltac2:(tb__ "0|0|
S0S21S12cS41U0S20A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDFqa_0 : ltac2:(tb__ "0|0|
S0S21S31S27S27S123R1S2bSaS13S2S76A1A1A2A2Li;S41U0S20A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVFqa_0 : ltac2:(tb__ "0|1|
S0S21S31S27S27S33S27S122R1A1S41U0M0S20A2A3Li;S3aG0S2bSaS13S2S76A1A1A2A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XFnqa_0 : ltac2:(tb__ "0|1|
S0S24S25SbSbA2M0A1S5S76A1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma BFbqa_0 : ax_base FFqa = base_sv. Proof. vm_cast_no_check (@eq_refl _ (base_sv)). Qed.
Lemma FPFqa_0 : ltac2:(tb__ "0|0|
S32ScS26ScS11aVW;Vst;A2S119S118A1A3SfS2S76A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FXFqa_0 : ltac2:(tb__ "0|0|
S32ScS9cSfS2S76A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FPARqa_0 : ltac2:(tb__ "0|0|
S30ScS21ScL_;S20S17S4aA1S4aX21x2SfS2S76A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Lemma Hc1qa_0 : ltac2:(tb__ "0|0|
S1S30SdS59S9aA3S1S30SdS55S9aA3S1S30SdS56S9aA3S1S30SdS5aS9aA3S1S30SdS58S1aS141S14S133A1S11Z4000A1A3A1S9aA3S30SdS57S9aA3A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (ic_pg) c1qa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c1) c1qa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c2) c1qa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_rs) c1qa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_nres (SAlu ALU_ADD (SVar V_NRES) (SLit 16384))) c1qa ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (ic_nch) c1qa ltac:(vm_cast_no_check (eq_refl true)))))))). Qed.
Lemma Hmcqa_0 : ltac2:(tb__ "0|0|
S1S30SdS5eS2fA1S7aA3S1S30SdS5fS7aA3S1S30SdS60S7aA3S1S30SdS5cS7aA3S1S30SdS5dS7aA3S1S30SdS5bS2fA1S7aA3S1S30SdS63S7aA3S1S30SdS64Sb4A1S7aA3S1S30SdS62S7aA3S30SdS61S7aA3A2A2A2A2A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (mc_map nx0) mcqa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ms) mcqa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ns) mcqa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_idx) mcqa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_magic) mcqa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_cptr nx0) mcqa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_state) mcqa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_type tybqa) mcqa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_sizehi) mcqa ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (mc_size) mcqa ltac:(vm_cast_no_check (eq_refl true)))))))))))). Qed.
Lemma Htybqa_0 : ltac2:(tb__ "0|0|
S0S21S2dS2dS13eZ0Sb4A2S13fSb4Z100A2A2S13dS140Sb4Z4A2Z1A2A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma Hxcqa_0 : In (xc_map nx0) xcqa. Proof. exact (In_of_cellb (xc_map nx0) xcqa ltac:(vm_cast_no_check (eq_refl true))). Qed.
Lemma WCUqa_0 : ltac2:(tb__ "0|0|
S0S21S10S12fS2S76A1S26SaS3fVW;S88A2S23SaS49S2fA1S22SaA1A3A3A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SELUqa_0 : ltac2:(tb__ "0|0|
S0S24SaA1S12bS26SaS3fVW;S88A2S23SaS49S2fA1S22SaA1A3A3S42U0A1A2S40VW;S88S2fA3A3"). Proof. vm_cast_no_check (@eq_refl _ (KUB W swcqa nx0)). Qed.
Lemma NDUqa_0 : nodupN (idxsU 0%nat) = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDUqa_0 : ltac2:(tb__ "0|0|
S0S21S31S27S27S123R1S2bSaS26SaS3fVW;S88A2S23SaS49S2fA1S22SaA1A3A3A2A2Li;S42U0A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVUqa_0 : ltac2:(tb__ "0|1|
S0S21S31S27S27S33S27S122R1A1S42U0M0A1A3Li;S3aG0S2bSaS26SaS3fVW;S88A2S23SaS49S2fA1S22SaA1A3A3A2A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W9qa_0 : ltac2:(tb__ "0|0|
S0S21S10S43S76S40VW;S88S2fA3A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D9qa_0 : ltac2:(tb__ "0|5|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S45S12fS2S76A1S40VW;S88S2fA3M4A2S43S76G4A2A2S2aG3S29G1G2S23G0S29SbSbS11S137A1S14P18A1A4S22G0A1A3S22ScA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(SLit TP_A, SVar 24)], @nil sprop))). Qed.
Lemma XB9qa_0 : ltac2:(tb__ "0|0|
S0S21S9SeS2S76A1A1S29SbSbS4bS2fA1S14PcA1A4A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sFqa : wsub := Eval vm_compute in (infer_sub NF (S2F FFqa (KUB W swcqa nx0)) (ax_S (L_malloc_ok AE_A W st))).
Lemma ENT9qa_0 : ltac2:(tb__ "0|0|
S0S21S8S44S76S40VW;S88S2fA3S2fA3S11cS11bVW;Vst;A3Se2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID9qa_0 : ltac2:(tb__ "0|0|
S0S21S12dSe2S135A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma G110qa_0 : ltac2:(tb__ "0|0|
S0SbS12eSe2S11dA2S4bS2fA1A3"). Proof. vm_cast_no_check (@eq_refl _ (UBs nx0)). Qed.

Definition PXb : list sobj := [O_w].
Definition FXPb : list sprop := ltac2:(tb__ "0|0|
S23ScS17S1bS142S14S134A1S14S133A1A3A1S22ScA1A3").

Definition C5Ab : axst := Eval vm_compute in (ax_add_facts (F_A nx0) C5bc).
Definition C5Bb : axst := Eval vm_compute in (ax_add_facts (F_B nx0) C5bc).
Lemma HC5Ab_0 : ltac2:(tb__ "0|0|
S0S3S47S4fS2fA1S13cA2Sb7A3"). Proof. vm_cast_no_check (@eq_refl _ (C5Ab)). Qed.
Lemma HC5Bb_0 : ltac2:(tb__ "0|0|
S0S3S47S50S2fA1S13cA2Sb9A3"). Proof. vm_cast_no_check (@eq_refl _ (C5Bb)). Qed.
Lemma FBAb_0 : ltac2:(tb__ "0|0|
S0S21S31ScS12SeS2S13cA1A1A1S4fS2fA1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBBb_0 : ltac2:(tb__ "0|0|
S0S21S31ScS12SeS2S13cA1A1A1S50S2fA1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition run6Ab : option (list leafA) := Eval vm_compute in (runT6 C5Ab).
Lemma run6Ab__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S4A1A1M0A1S48S38Ufa0S23S35S3eS22S35A1A3S23S3Sb7S22S3A1A3A4S23G0S105S22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run6Ab]). Qed.
Definition Y6Ab : axst := Eval vm_compute in (leafS 0 run6Ab).
Lemma Cert6Ab_0 : ltac2:(tb__ "0|1|
S0S21S46S38Ufa0S23S35S3eS22S35A1A3VGS0;S23S3Sb7S22S3A1M0A3S23S3SedG0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] GS0 [C5Ab] [Y6Ab] [run6Ab]); [exact run6Ab__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition run6Bb : option (list leafA) := Eval vm_compute in (runT6 C5Bb).
Lemma run6Bb__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S4A1A1M0A1S48S38Ufa0S23S35S3eS22S35A1A3S23S3Sb9S22S3A1A3A4S23G0S107S22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run6Bb]). Qed.
Definition Y6Bb : axst := Eval vm_compute in (leafS 0 run6Bb).
Lemma Cert6Bb_0 : ltac2:(tb__ "0|1|
S0S21S46S38Ufa0S23S35S3eS22S35A1A3VGS0;S23S3Sb9S22S3A1M0A3S23S3SefG0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] GS0 [C5Bb] [Y6Bb] [run6Bb]); [exact run6Bb__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition E6b : axst := Eval vm_compute in (rmF (F_A nx0) Y6Ab).
Definition s6Ab : wsub := Eval vm_compute in (infer_sub GS0 (ax_S Y6Ab) (ax_S E6b)).
Lemma E6Ab_0 : ltac2:(tb__ "0|0|
S0S21S8SedSa1Sf5A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma I6Ab_0 : ltac2:(tb__ "0|0|
S0S21S12dSf5VGS0;A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition s6Bb : wsub := Eval vm_compute in (infer_sub GS0 (ax_S Y6Bb) (ax_S E6b)).
Lemma E6Bb_0 : ltac2:(tb__ "0|0|
S0S21S8SefSa1Sf7A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma I6Bb_0 : ltac2:(tb__ "0|0|
S0S21S12dSf7VGS0;A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition CT6b : axst := Eval vm_compute in (rstS E6b ru6 []).
Definition CO6b : axst := Eval vm_compute in (carveS CT6b (O_3 nx0)).
Lemma WC6b_0 : ltac2:(tb__ "0|0|
S0S21S10S2S7dA1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DF6b_0 : ltac2:(tb__ "0|4|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S45S2Sa1A1S2S7dA1A2S2aG3S29G1G2S23G0S29SbSbS6eS2fA1S51A4S22G0A1A3S22ScA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(a2e6 nx0, L3)], @nil sprop))). Qed.
Lemma NX6b_0 : ltac2:(tb__ "0|0|
S0S36SeS2S7dA1A1SeS2Sa1A1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S E6b))). Qed.
Lemma HC6b_0 : ltac2:(tb__ "0|0|
S0S3S6Sa1S2S7dA1A2S7dA3"). Proof. vm_cast_no_check (@eq_refl _ (CT6b)). Qed.
Lemma SK6b_0 : ltac2:(tb__ "0|1|
S0S24S25S25SbSbA2SbA2M0A1S39SaG0S73S13S2S7dA1A1A4S39SaG0S73S26SaS23SaS129S2fA1S23SaS125S2fA1S22SaA1A3A3S26SaS130U0S2fA2Sb1A3A3A4A3"). Proof. vm_cast_no_check (@eq_refl _ (map skel ([O_2 nx0; O_1 nx0] ++ SKEL0 0%nat nx0 ++ PXb))). Qed.
Lemma FC6b_0 : ltac2:(tb__ "0|0|
S32ScS26ScS11aVW;Vst;A2S119S118A1A3SfS2S7dA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FX6b_0 : ltac2:(tb__ "0|0|
S32ScS9dSfS2S7dA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma XC6b_0 : ltac2:(tb__ "0|1|
S0S24S25SbSbA2M0A1S5S7dA1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma HCO6b_0 : ltac2:(tb__ "0|0|
S0S3S127S7dS16S65S2fA1S11Z0A1S51S22SdA1S15A5A2S83A3"). Proof. vm_cast_no_check (@eq_refl _ (CO6b)). Qed.
Lemma WCO6b_0 : ltac2:(tb__ "0|0|
S0S21S10S2S83A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition s6b : wsub := Eval vm_compute in (callsub CO6b Pre_memsetA).
Definition R6b : list sobj := Eval vm_compute in (callR CO6b Pre_memsetA s6b).
Definition T6b : axst := Eval vm_compute in (callT CO6b Pre_memsetA Pret_ms s6b R6b).
Lemma He6b_0 : ltac2:(tb__ "0|1|
S0S28S24SaA1M0A1S120S83S3cSd7A3S2aG0Sc3A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some R6b)). Qed.
Lemma Hchk6b_0 : ltac2:(tb__ "0|0|
S0S21S11fS83S3cSd7Sc3S39S4S3S7S3dA4A5S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HT6b_0 : ltac2:(tb__ "0|0|
S0S3S121Sd7S3cS126S83Sc3A5ScdA3"). Proof. vm_cast_no_check (@eq_refl _ (T6b)). Qed.
Lemma FBC6b_0 : ltac2:(tb__ "0|1|
S0S21S31ScS12SeS2S83A1M0A1A1SfG0A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT6b_0 : ltac2:(tb__ "0|0|
S0S21S31ScS12SeS2ScdA1A1A1SfS2S83A1A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXC6b_0 : ltac2:(tb__ "0|0|
S0S21S124VGS0;SeS2S83A1A1A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition D6b : axst := Eval vm_compute in (ax_with_facts T6b (ss_facts (ax_S CO6b))).
Lemma HD6b_0 : ltac2:(tb__ "0|0|
S0S3S11eScdSfS2S83A1A1A2Sa7A3"). Proof. vm_cast_no_check (@eq_refl _ (D6b)). Qed.

Definition U7b : axst := Eval vm_compute in (U7p nx0 D6b).
Lemma WU7b_0 : ltac2:(tb__ "0|0|
S0S21S10S2S93A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DU7b_0 : ltac2:(tb__ "0|4|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S45S2Sa7A1S2S93A1A2S2aG3S29G1G2S22G0A1S68S2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g7 nx0))). Qed.
Lemma NXU7b_0 : ltac2:(tb__ "0|0|
S0S36SeS2S93A1A1SeS2Sa7A1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D6b))). Qed.
Lemma HU7b_0 : ltac2:(tb__ "0|0|
S0S3S6Sa7S2S93A1A2S93A3"). Proof. vm_cast_no_check (@eq_refl _ (U7b)). Qed.
Definition run7b : option (list leafA) := Eval vm_compute in (runT6 U7b).
Lemma run7b__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S4A1A1M0A1S48S38Ufa0S23S35S3eS22S35A1A3S23S3S93S22S3A1A3A4S23G0S109S22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run7b]). Qed.
Definition ET7b : axst := Eval vm_compute in (leafS 0 run7b).
Lemma Cert7b_0 : ltac2:(tb__ "0|1|
S0S21S46S38Ufa0S23S35S3eS22S35A1A3VGS0;S23S3S93S22S3A1M0A3S23S3SadG0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] GS0 [U7b] [ET7b] [run7b]); [exact run7b__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition CT7b : axst := Eval vm_compute in (rstS ET7b (ru7 nx0) []).
Definition CO7b : axst := Eval vm_compute in (carveS CT7b (O_3n nx0)).
Definition CR7b : axst := Eval vm_compute in (DepotCall.oreb CO7b 1).
Definition n7b : nat := Eval vm_compute in (length (ss_objs (ax_S CR7b))).
Definition CS7b : axst := Eval vm_compute in (sel7 CR7b).
Definition CM7b : axst := Eval vm_compute in (DepotCall.omrg CS7b 1).
Lemma WC7b_0 : ltac2:(tb__ "0|0|
S0S21S10S2S7fA1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DF7b_0 : ltac2:(tb__ "0|4|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S45S2SadA1S2S7fA1A2S2aG3S29G1G2S23G0S29SbSbS6dS2fA1S128S2fA1A4S23G0S29SbSbS6fS2fA1S6bA4S22G0A1A3A3S22ScA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(a0e7 nx0, BR nx0); (a2e7 nx0, L3b)], @nil sprop))). Qed.
Lemma NX7b_0 : ltac2:(tb__ "0|0|
S0S36SeS2S7fA1A1SeS2SadA1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S ET7b))). Qed.
Lemma HC7b_0 : ltac2:(tb__ "0|0|
S0S3S6SadS2S7fA1A2S7fA3"). Proof. vm_cast_no_check (@eq_refl _ (CT7b)). Qed.
Lemma SK7b_0 : ltac2:(tb__ "0|1|
S0S24S25S25SbSbA2SbA2M0A1S39SaG0S73S13S2S7fA1A1A4S39SaG0S73S26SaS23SaS4dS2fA1S23SaS129S2fA1S23SaS125S2fA1S22SaA1A3A3A3S26SaS130U0S2fA2Sb1A3A3A4A3"). Proof. vm_cast_no_check (@eq_refl _ (map skel ([O_3 nx0; O_2 nx0; O_1 nx0] ++ SKEL0 0%nat nx0 ++ PXb))). Qed.
Lemma FC7b_0 : ltac2:(tb__ "0|0|
S32ScS26ScS11aVW;Vst;A2S119S118A1A3SfS2S7fA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FX7b_0 : ltac2:(tb__ "0|0|
S32ScS9dSfS2S7fA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma XC7b_0 : ltac2:(tb__ "0|1|
S0S24S25SbSbA2M0A1S5S7fA1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma HCO7b_0 : ltac2:(tb__ "0|0|
S0S3S127S7fS16S128S2fA1S11Z0A1S11Z100A1S22SdA1S15A5A2Sa3A3"). Proof. vm_cast_no_check (@eq_refl _ (CO7b)). Qed.
Lemma WCO7b_0 : ltac2:(tb__ "0|0|
S0S21S10S2Sa3A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RB7b_0 : ltac2:(tb__ "0|0|
S0S21S138S18S146S2Sa3A1U1A2A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HCR7b_0 : ltac2:(tb__ "0|0|
S0S3S13aSa3U1A2SbbA3"). Proof. vm_cast_no_check (@eq_refl _ (CR7b)). Qed.
Lemma LEN7b_0 : ltac2:(tb__ "0|0|
S0S27S2bSaS13S2SbbA1A1A2S9fA3"). Proof. vm_cast_no_check (@eq_refl _ (n7b)). Qed.
Lemma PERM_nd7b_0 : ltac2:(tb__ "0|0|
S0S21S12cS4eS9fA1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma PERM_lt7b_0 : ltac2:(tb__ "0|0|
S0S21S31S27S27S123R1S9fA2Li;S4eS9fA1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma PERM_cov7b_0 : ltac2:(tb__ "0|0|
S0S21S31S27S27S33S27S122R1A1S4eS9fA1A3Li;S3aU0S9fA2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HCS7b_0 : ltac2:(tb__ "0|0|
S0S3S72SbbA1SbdA3"). Proof. vm_cast_no_check (@eq_refl _ (CS7b)). Qed.
Lemma MRG7b_0 : ltac2:(tb__ "0|0|
S0S21S138S18S145S2SbdA1U1A2A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HCM7b_0 : ltac2:(tb__ "0|0|
S0S3S139SbdU1A2S8bA3"). Proof. vm_cast_no_check (@eq_refl _ (CM7b)). Qed.
Definition s7b : wsub := Eval vm_compute in (callsub CM7b Pre_memsetA).
Definition R7b : list sobj := Eval vm_compute in (callR CM7b Pre_memsetA s7b).
Definition T7b : axst := Eval vm_compute in (callT CM7b Pre_memsetA Pret_ms s7b R7b).
Lemma He7b_0 : ltac2:(tb__ "0|1|
S0S28S24SaA1M0A1S120S8bS3cSd9A3S2aG0Sc5A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some R7b)). Qed.
Lemma Hchk7b_0 : ltac2:(tb__ "0|0|
S0S21S11fS8bS3cSd9Sc5S39S4S3S7S3dA4A5S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HT7b_0 : ltac2:(tb__ "0|0|
S0S3S121Sd9S3cS126S8bSc5A5ScfA3"). Proof. vm_cast_no_check (@eq_refl _ (T7b)). Qed.
Lemma FBC7b_0 : ltac2:(tb__ "0|1|
S0S21S31ScS12SeS2S8bA1M0A1A1SfG0A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT7b_0 : ltac2:(tb__ "0|0|
S0S21S31ScS12SeS2ScfA1A1A1SfS2S8bA1A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXC7b_0 : ltac2:(tb__ "0|0|
S0S21S124VGS0;SeS2S8bA1A1A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition D7b : axst := Eval vm_compute in (ax_with_facts T7b (ss_facts (ax_S CM7b))).
Lemma HD7b_0 : ltac2:(tb__ "0|0|
S0S3S11eScfSfS2S8bA1A1A2Sa9A3"). Proof. vm_cast_no_check (@eq_refl _ (D7b)). Qed.

Definition U8b : axst := Eval vm_compute in (U8p nx0 D7b).
Lemma WU8b_0 : ltac2:(tb__ "0|0|
S0S21S10S2S95A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DU8b_0 : ltac2:(tb__ "0|4|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S45S2Sa9A1S2S95A1A2S2aG3S29G1G2S22G0A1S69S2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g8 nx0))). Qed.
Lemma NXU8b_0 : ltac2:(tb__ "0|0|
S0S36SeS2S95A1A1SeS2Sa9A1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D7b))). Qed.
Lemma HU8b_0 : ltac2:(tb__ "0|0|
S0S3S6Sa9S2S95A1A2S95A3"). Proof. vm_cast_no_check (@eq_refl _ (U8b)). Qed.
Definition run8b : option (list leafA) := Eval vm_compute in (runT6 U8b).
Lemma run8b__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S4A1A1M0A1S48S38Ufa0S23S35S3eS22S35A1A3S23S3S95S22S3A1A3A4S23G0S10bS22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run8b]). Qed.
Definition ET8b : axst := Eval vm_compute in (leafS 0 run8b).
Lemma Cert8b_0 : ltac2:(tb__ "0|1|
S0S21S46S38Ufa0S23S35S3eS22S35A1A3VGS0;S23S3S95S22S3A1M0A3S23S3SafG0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] GS0 [U8b] [ET8b] [run8b]); [exact run8b__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition CT8b : axst := Eval vm_compute in (CT8p nx0 ET8b).
Definition CO8b : axst := Eval vm_compute in (carveS CT8b (O_4 nx0)).
Lemma WC8b_0 : ltac2:(tb__ "0|0|
S0S21S10S2S81A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DF8b_0 : ltac2:(tb__ "0|4|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S45S2SafA1S2S81A1A2S2aG3S29G1G2S22G0A1S71S2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), fx8 nx0))). Qed.
Lemma NX8b_0 : ltac2:(tb__ "0|0|
S0S36SeS2S81A1A1SeS2SafA1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S ET8b))). Qed.
Lemma HC8b_0 : ltac2:(tb__ "0|0|
S0S3S6SafS2S81A1A2S81A3"). Proof. vm_cast_no_check (@eq_refl _ (CT8b)). Qed.
Lemma SK8b_0 : ltac2:(tb__ "0|1|
S0S24S25S25SbSbA2SbA2M0A1S39SaG0S73S13S2S81A1A1A4S39SaG0S73S26SaS23SaS52S2fA1S23SaS4dS2fA1S23SaS125S2fA1S22SaA1A3A3A3S26SaS130U0S2fA2Sb1A3A3A4A3"). Proof. vm_cast_no_check (@eq_refl _ (map skel ([O_3b nx0; O_3 nx0; O_1 nx0] ++ SKEL0 0%nat nx0 ++ PXb))). Qed.
Lemma FC8b_0 : ltac2:(tb__ "0|0|
S32ScS26ScS11aVW;Vst;A2S119S118A1A3SfS2S81A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FX8b_0 : ltac2:(tb__ "0|0|
S32ScS9dSfS2S81A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma XC8b_0 : ltac2:(tb__ "0|1|
S0S24S25SbSbA2M0A1S5S81A1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma HCO8b_0 : ltac2:(tb__ "0|0|
S0S3S127S81S16S66S2fA1S11Z0A1S70S2fA1S22SdA1S15A5A2S85A3"). Proof. vm_cast_no_check (@eq_refl _ (CO8b)). Qed.
Lemma WCO8b_0 : ltac2:(tb__ "0|0|
S0S21S10S2S85A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition s8b : wsub := Eval vm_compute in (callsub CO8b Pre_mszA).
Definition R8b : list sobj := Eval vm_compute in (callR CO8b Pre_mszA s8b).
Definition T8b : axst := Eval vm_compute in (callT CO8b Pre_mszA Pret_mz s8b R8b).
Lemma He8b_0 : ltac2:(tb__ "0|1|
S0S28S24SaA1M0A1S120S85S131SdbA3S2aG0Sc7A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some R8b)). Qed.
Lemma Hchk8b_0 : ltac2:(tb__ "0|0|
S0S21S11fS85S131SdbSc7S39S4S3S7S132A4A5S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HT8b_0 : ltac2:(tb__ "0|0|
S0S3S121SdbS131S12aS85Sc7A5Sd1A3"). Proof. vm_cast_no_check (@eq_refl _ (T8b)). Qed.
Lemma FBC8b_0 : ltac2:(tb__ "0|1|
S0S21S31ScS12SeS2S85A1M0A1A1SfG0A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT8b_0 : ltac2:(tb__ "0|0|
S0S21S31ScS12SeS2Sd1A1A1A1SfS2S85A1A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXC8b_0 : ltac2:(tb__ "0|0|
S0S21S124VGS0;SeS2S85A1A1A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition D8b : axst := Eval vm_compute in (ax_with_facts T8b (ss_facts (ax_S CO8b))).
Lemma HD8b_0 : ltac2:(tb__ "0|0|
S0S3S11eSd1SfS2S85A1A1A2SabA3"). Proof. vm_cast_no_check (@eq_refl _ (D8b)). Qed.

Definition U9b : axst := Eval vm_compute in (U9p nx0 D8b).
Lemma WU9b_0 : ltac2:(tb__ "0|0|
S0S21S10S2S97A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DU9b_0 : ltac2:(tb__ "0|4|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S45S2SabA1S2S97A1A2S2aG3S29G1G2S22G0A1S6aS2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g9 nx0))). Qed.
Lemma NXU9b_0 : ltac2:(tb__ "0|0|
S0S36SeS2S97A1A1SeS2SabA1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D8b))). Qed.
Lemma HU9b_0 : ltac2:(tb__ "0|0|
S0S3S6SabS2S97A1A2S97A3"). Proof. vm_cast_no_check (@eq_refl _ (U9b)). Qed.
Definition run9b : option (list leafA) := Eval vm_compute in (runT9 U9b).
Lemma run9b__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S4A1A1M0A1S48S38Ufa0S23S35S3eS23S35S53S22S35A1A3A3S23S3S97S22S3A1A3A4S23G0S10dS22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run9b]). Qed.
Definition E9fb : axst := Eval vm_compute in (leafS 0 run9b).
Definition E9pb : axst := Eval vm_compute in (leafS 1 run9b).
Lemma Cert9b_0 : ltac2:(tb__ "0|1|
S0S21S46S38Ufa0S23S35S3eS23S35S53S22S35A1A3A3VGS0;S23S3S97S22S3A1M0A3S23S3Se5S23S3S91G0A3A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT; PGST] GS0 [U9b] [E9fb; E9pb] [run9b]); [exact run9b__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma SK9b_0 : ltac2:(tb__ "0|1|
S0S24S25S25SbSbA2SbA2M0A1S39SaG0S73S13S2S91A1A1A4S39SaG0S73S26SaS23SaS6cS2fA1S23SaS52S2fA1S23SaS4dS2fA1S23SaS125S2fA1S22SaA1A3A3A3A3S26SaS130U0S2fA2Sb1A3A3A4A3"). Proof. vm_cast_no_check (@eq_refl _ (map skel ([O_4z nx0; O_3b nx0; O_3 nx0; O_1 nx0] ++ SKEL0 0%nat nx0 ++ PXb))). Qed.
Lemma FC9b_0 : ltac2:(tb__ "0|0|
S32ScS26ScS11aVW;Vst;A2S119S118A1A3SfS2S91A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FX9b_0 : ltac2:(tb__ "0|0|
S32ScS9dSfS2S91A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FP9b_0 : ltac2:(tb__ "0|0|
S30ScS17S4aA1SfS2S91A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Lemma XC9b_0 : ltac2:(tb__ "0|1|
S0S24S25SbSbA2M0A1S5S91A1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Definition CO9pb : axst := Eval vm_compute in (carveS E9pb (mkObj (BP9 nx0) (SLit 0) (SLit 1) [] DUnknown)).
Lemma HCO9b_0 : ltac2:(tb__ "0|0|
S0S3S127S91S16S67S2fA1S11Z0A1S11Z1A1S22SdA1S15A5A2Sa5A3"). Proof. vm_cast_no_check (@eq_refl _ (CO9pb)). Qed.
Lemma WCO9b_0 : ltac2:(tb__ "0|0|
S0S21S10S2Sa5A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition run9qb : option (list leafA) := Eval vm_compute in (runT6 CO9pb).
Lemma run9qb__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S4A1A1M0A1S48S38Ufa0S23S35S3eS22S35A1A3S23S3Sa5S22S3A1A3A4S23G0S10fS22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run9qb]). Qed.
Definition E9qb : axst := Eval vm_compute in (leafS 0 run9qb).
Lemma Cert9qb_0 : ltac2:(tb__ "0|1|
S0S21S46S38Ufa0S23S35S3eS22S35A1A3VGS0;S23S3Sa5S22S3A1M0A3S23S3Se7G0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] GS0 [CO9pb] [E9qb] [run9qb]); [exact run9qb__runeq | vm_cast_no_check (eq_refl true)]. Qed.

Definition iMfb : nat := Eval vm_compute in (find_map nx0 (ss_objs (ax_S E9fb)) 0).
Definition S9afb : axst := Eval vm_compute in (osplit E9fb iMfb (SLit 6144)).
Definition S9bfb : axst := Eval vm_compute in (osplit S9afb (S iMfb) (SLit 10240)).
Lemma HS9afb_0 : ltac2:(tb__ "0|0|
S0S3S4cSe5Sf1S11Z1800A1A3Se9A3"). Proof. vm_cast_no_check (@eq_refl _ (S9afb)). Qed.
Lemma HS9bfb_0 : ltac2:(tb__ "0|0|
S0S3S4cSe9S2eSf1A1S11Z2800A1A3S8dA3"). Proof. vm_cast_no_check (@eq_refl _ (S9bfb)). Qed.
Definition s9fb : wsub := Eval vm_compute in (callsub S9bfb Pre_memsetA).
Definition R9fb : list sobj := Eval vm_compute in (callR S9bfb Pre_memsetA s9fb).
Definition T9fb : axst := Eval vm_compute in (callT S9bfb Pre_memsetA Pret_ms s9fb R9fb).
Lemma He9fb_0 : ltac2:(tb__ "0|1|
S0S28S24SaA1M0A1S120S8dS3cSddA3S2aG0Sc9A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some R9fb)). Qed.
Lemma Hchk9fb_0 : ltac2:(tb__ "0|0|
S0S21S11fS8dS3cSddSc9S39S4S3S7S3dA4A5S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HT9fb_0 : ltac2:(tb__ "0|0|
S0S3S121SddS3cS126S8dSc9A5Sd3A3"). Proof. vm_cast_no_check (@eq_refl _ (T9fb)). Qed.
Lemma FBC9fb_0 : ltac2:(tb__ "0|1|
S0S21S31ScS12SeS2S8dA1M0A1A1SfG0A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT9fb_0 : ltac2:(tb__ "0|0|
S0S21S31ScS12SeS2Sd3A1A1A1SfS2S8dA1A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXC9fb_0 : ltac2:(tb__ "0|0|
S0S21S124VGS0;SeS2S8dA1A1A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition D9fb : axst := Eval vm_compute in (ax_with_facts T9fb (ss_facts (ax_S S9bfb))).
Lemma HD9fb_0 : ltac2:(tb__ "0|0|
S0S3S11eSd3SfS2S8dA1A1A2SbfA3"). Proof. vm_cast_no_check (@eq_refl _ (D9fb)). Qed.
Definition runFfb : option (list leafA) := Eval vm_compute in (runTF D9fb).
Lemma runFfb__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S4A1A1M0A1S48S38Ufa0S22S35A1S23S3SbfS22S3A1A3A4S23G0S111S22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [runFfb]). Qed.
Definition FFfb : axst := Eval vm_compute in (leafS 0 runFfb).
Lemma CertFfb_0 : ltac2:(tb__ "0|1|
S0S21S46S38Ufa0S22S35A1VGS0;S23S3SbfS22S3A1M0A3S23S3S75G0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [] GS0 [D9fb] [FFfb] [runFfb]); [exact runFfb__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition swcfb : list cell := Eval vm_compute in (cells_at 5 FFfb).
Definition c1fb : list cell := Eval vm_compute in (cells_at 38 FFfb).
Definition c2fb : list cell := Eval vm_compute in (cells_at 39 FFfb).
Definition c4fb : list cell := Eval vm_compute in (cells_at 41 FFfb).
Definition c5fb : list cell := Eval vm_compute in (cells_at 45 FFfb).
Definition mcfb : list cell := Eval vm_compute in (cells_at 46 FFfb).
Definition xcfb : list cell := Eval vm_compute in (cells_at 48 FFfb).
Definition tybfb : Z := Eval vm_compute in (tyb_of mcfb).
Lemma SELFfb_0 : ltac2:(tb__ "0|0|
S0S24SaA1S12bS13S2S75A1A1S41U0S2cA2A2S26SaS3fVW;S87A2S26SaS136S54S2fS99Sf9SfdS101S79S115Z8S15S2cAaA3A3A3"). Proof. vm_cast_no_check (@eq_refl _ (KEPTF W swcfb ++ RT_m1 ++ RSF nx0 c1fb c2fb c4fb c5fb mcfb xcfb 8 DUnknown false)). Qed.
Lemma NDFfb_0 : ltac2:(tb__ "0|0|
S0S21S12cS41U0S2cA2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDFfb_0 : ltac2:(tb__ "0|0|
S0S21S31S27S27S123R1S2bSaS13S2S75A1A1A2A2Li;S41U0S2cA2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVFfb_0 : ltac2:(tb__ "0|1|
S0S21S31S27S27S33S27S122R1A1S41U0M0S2cA2A3Li;S3aG0S2bSaS13S2S75A1A1A2A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XFnfb_0 : ltac2:(tb__ "0|1|
S0S24S25SbSbA2M0A1S5S75A1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma BFbfb_0 : ax_base FFfb = base_sv. Proof. vm_cast_no_check (@eq_refl _ (base_sv)). Qed.
Lemma FPFfb_0 : ltac2:(tb__ "0|0|
S32ScS26ScS11aVW;Vst;A2S119S118A1A3SfS2S75A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FXFfb_0 : ltac2:(tb__ "0|0|
S32ScS9dSfS2S75A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FPARfb_0 : ltac2:(tb__ "0|0|
S30ScS21ScL_;S2cS17S4aA1S4aX21x2SfS2S75A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Lemma Hc1fb_0 : ltac2:(tb__ "0|0|
S1S30SdS59S99A3S1S30SdS55S99A3S1S30SdS56S99A3S1S30SdS5aS99A3S1S30SdS58S14S133A1A1S99A3S30SdS57S99A3A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (ic_pg) c1fb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c1) c1fb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c2) c1fb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_rs) c1fb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_nres (SVar V_NRES)) c1fb ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (ic_nch) c1fb ltac:(vm_cast_no_check (eq_refl true)))))))). Qed.
Lemma Hmcfb_0 : ltac2:(tb__ "0|0|
S1S30SdS5eS2fA1S79A3S1S30SdS5fS79A3S1S30SdS60S79A3S1S30SdS5cS79A3S1S30SdS5dS79A3S1S30SdS5bS2fA1S79A3S1S30SdS63S79A3S1S30SdS64Sb3A1S79A3S1S30SdS62S79A3S30SdS61S79A3A2A2A2A2A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (mc_map nx0) mcfb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ms) mcfb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ns) mcfb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_idx) mcfb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_magic) mcfb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_cptr nx0) mcfb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_state) mcfb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_type tybfb) mcfb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_sizehi) mcfb ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (mc_size) mcfb ltac:(vm_cast_no_check (eq_refl true)))))))))))). Qed.
Lemma Htybfb_0 : ltac2:(tb__ "0|0|
S0S21S2dS2dS13eZ0Sb3A2S13fSb3Z100A2A2S13dS140Sb3Z4A2Z1A2A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma Hxcfb_0 : In (xc_map nx0) xcfb. Proof. exact (In_of_cellb (xc_map nx0) xcfb ltac:(vm_cast_no_check (eq_refl true))). Qed.
Lemma WCUfb_0 : ltac2:(tb__ "0|0|
S0S21S10S12fS2S75A1S26SaS3fVW;S87A2S23SaS49S2fA1S22SaA1A3A3A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SELUfb_0 : ltac2:(tb__ "0|0|
S0S24SaA1S12bS26SaS3fVW;S87A2S23SaS49S2fA1S22SaA1A3A3S42U0A1A2S40VW;S87S2fA3A3"). Proof. vm_cast_no_check (@eq_refl _ (KUB W swcfb nx0)). Qed.
Lemma NDUfb_0 : nodupN (idxsU 0%nat) = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDUfb_0 : ltac2:(tb__ "0|0|
S0S21S31S27S27S123R1S2bSaS26SaS3fVW;S87A2S23SaS49S2fA1S22SaA1A3A3A2A2Li;S42U0A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVUfb_0 : ltac2:(tb__ "0|1|
S0S21S31S27S27S33S27S122R1A1S42U0M0A1A3Li;S3aG0S2bSaS26SaS3fVW;S87A2S23SaS49S2fA1S22SaA1A3A3A2A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W9fb_0 : ltac2:(tb__ "0|0|
S0S21S10S43S75S40VW;S87S2fA3A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D9fb_0 : ltac2:(tb__ "0|5|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S45S12fS2S75A1S40VW;S87S2fA3M4A2S43S75G4A2A2S2aG3S29G1G2S23G0S29SbSbS11S137A1S14P18A1A4S22G0A1A3S22ScA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(SLit TP_A, SVar 24)], @nil sprop))). Qed.
Lemma XB9fb_0 : ltac2:(tb__ "0|0|
S0S21S9SeS2S75A1A1S29SbSbS4bS2fA1S14PcA1A4A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sFfb : wsub := Eval vm_compute in (infer_sub NF (S2F FFfb (KUB W swcfb nx0)) (ax_S (L_malloc_ok AE_A W st))).
Lemma ENT9fb_0 : ltac2:(tb__ "0|0|
S0S21S8S44S75S40VW;S87S2fA3S2fA3S11cS11bVW;Vst;A3Se1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID9fb_0 : ltac2:(tb__ "0|0|
S0S21S12dSe1S135A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma G110fb_0 : ltac2:(tb__ "0|0|
S0SbS12eSe1S11dA2S4bS2fA1A3"). Proof. vm_cast_no_check (@eq_refl _ (UBs nx0)). Qed.

Definition iMqb : nat := Eval vm_compute in (find_map nx0 (ss_objs (ax_S E9qb)) 0).
Definition S9aqb : axst := Eval vm_compute in (osplit E9qb iMqb (SLit 6144)).
Definition S9bqb : axst := Eval vm_compute in (osplit S9aqb (S iMqb) (SLit 10240)).
Lemma HS9aqb_0 : ltac2:(tb__ "0|0|
S0S3S4cSe7Sf3S11Z1800A1A3SebA3"). Proof. vm_cast_no_check (@eq_refl _ (S9aqb)). Qed.
Lemma HS9bqb_0 : ltac2:(tb__ "0|0|
S0S3S4cSebS2eSf3A1S11Z2800A1A3S8fA3"). Proof. vm_cast_no_check (@eq_refl _ (S9bqb)). Qed.
Definition s9qb : wsub := Eval vm_compute in (callsub S9bqb Pre_memsetA).
Definition R9qb : list sobj := Eval vm_compute in (callR S9bqb Pre_memsetA s9qb).
Definition T9qb : axst := Eval vm_compute in (callT S9bqb Pre_memsetA Pret_ms s9qb R9qb).
Lemma He9qb_0 : ltac2:(tb__ "0|1|
S0S28S24SaA1M0A1S120S8fS3cSdfA3S2aG0ScbA2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some R9qb)). Qed.
Lemma Hchk9qb_0 : ltac2:(tb__ "0|0|
S0S21S11fS8fS3cSdfScbS39S4S3S7S3dA4A5S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HT9qb_0 : ltac2:(tb__ "0|0|
S0S3S121SdfS3cS126S8fScbA5Sd5A3"). Proof. vm_cast_no_check (@eq_refl _ (T9qb)). Qed.
Lemma FBC9qb_0 : ltac2:(tb__ "0|1|
S0S21S31ScS12SeS2S8fA1M0A1A1SfG0A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT9qb_0 : ltac2:(tb__ "0|0|
S0S21S31ScS12SeS2Sd5A1A1A1SfS2S8fA1A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXC9qb_0 : ltac2:(tb__ "0|0|
S0S21S124VGS0;SeS2S8fA1A1A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition D9qb : axst := Eval vm_compute in (ax_with_facts T9qb (ss_facts (ax_S S9bqb))).
Lemma HD9qb_0 : ltac2:(tb__ "0|0|
S0S3S11eSd5SfS2S8fA1A1A2Sc1A3"). Proof. vm_cast_no_check (@eq_refl _ (D9qb)). Qed.
Definition runFqb : option (list leafA) := Eval vm_compute in (runTF D9qb).
Lemma runFqb__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S4A1A1M0A1S48S38Ufa0S22S35A1S23S3Sc1S22S3A1A3A4S23G0S113S22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [runFqb]). Qed.
Definition FFqb : axst := Eval vm_compute in (leafS 0 runFqb).
Lemma CertFqb_0 : ltac2:(tb__ "0|1|
S0S21S46S38Ufa0S22S35A1VGS0;S23S3Sc1S22S3A1M0A3S23S3S77G0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [] GS0 [D9qb] [FFqb] [runFqb]); [exact runFqb__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition swcqb : list cell := Eval vm_compute in (cells_at 5 FFqb).
Definition c1qb : list cell := Eval vm_compute in (cells_at 38 FFqb).
Definition c2qb : list cell := Eval vm_compute in (cells_at 39 FFqb).
Definition c4qb : list cell := Eval vm_compute in (cells_at 41 FFqb).
Definition c5qb : list cell := Eval vm_compute in (cells_at 45 FFqb).
Definition mcqb : list cell := Eval vm_compute in (cells_at 46 FFqb).
Definition xcqb : list cell := Eval vm_compute in (cells_at 48 FFqb).
Definition tybqb : Z := Eval vm_compute in (tyb_of mcqb).
Lemma SELFqb_0 : ltac2:(tb__ "0|0|
S0S24SaA1S12bS13S2S77A1A1S41U0S20A2A2S26SaS3fVW;S89A2S26SaS136S54S2fS9bSfbSffS103S7bS117Z8S15S20AaA3A3A3"). Proof. vm_cast_no_check (@eq_refl _ (KEPTF W swcqb ++ RT_m1 ++ RSF nx0 c1qb c2qb c4qb c5qb mcqb xcqb 8 DUnknown true)). Qed.
Lemma NDFqb_0 : ltac2:(tb__ "0|0|
S0S21S12cS41U0S20A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDFqb_0 : ltac2:(tb__ "0|0|
S0S21S31S27S27S123R1S2bSaS13S2S77A1A1A2A2Li;S41U0S20A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVFqb_0 : ltac2:(tb__ "0|1|
S0S21S31S27S27S33S27S122R1A1S41U0M0S20A2A3Li;S3aG0S2bSaS13S2S77A1A1A2A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XFnqb_0 : ltac2:(tb__ "0|1|
S0S24S25SbSbA2M0A1S5S77A1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma BFbqb_0 : ax_base FFqb = base_sv. Proof. vm_cast_no_check (@eq_refl _ (base_sv)). Qed.
Lemma FPFqb_0 : ltac2:(tb__ "0|0|
S32ScS26ScS11aVW;Vst;A2S119S118A1A3SfS2S77A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FXFqb_0 : ltac2:(tb__ "0|0|
S32ScS9dSfS2S77A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FPARqb_0 : ltac2:(tb__ "0|0|
S30ScS21ScL_;S20S17S4aA1S4aX21x2SfS2S77A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Lemma Hc1qb_0 : ltac2:(tb__ "0|0|
S1S30SdS59S9bA3S1S30SdS55S9bA3S1S30SdS56S9bA3S1S30SdS5aS9bA3S1S30SdS58S14S133A1A1S9bA3S30SdS57S9bA3A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (ic_pg) c1qb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c1) c1qb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c2) c1qb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_rs) c1qb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_nres (SVar V_NRES)) c1qb ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (ic_nch) c1qb ltac:(vm_cast_no_check (eq_refl true)))))))). Qed.
Lemma Hmcqb_0 : ltac2:(tb__ "0|0|
S1S30SdS5eS2fA1S7bA3S1S30SdS5fS7bA3S1S30SdS60S7bA3S1S30SdS5cS7bA3S1S30SdS5dS7bA3S1S30SdS5bS2fA1S7bA3S1S30SdS63S7bA3S1S30SdS64Sb5A1S7bA3S1S30SdS62S7bA3S30SdS61S7bA3A2A2A2A2A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (mc_map nx0) mcqb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ms) mcqb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ns) mcqb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_idx) mcqb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_magic) mcqb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_cptr nx0) mcqb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_state) mcqb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_type tybqb) mcqb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_sizehi) mcqb ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (mc_size) mcqb ltac:(vm_cast_no_check (eq_refl true)))))))))))). Qed.
Lemma Htybqb_0 : ltac2:(tb__ "0|0|
S0S21S2dS2dS13eZ0Sb5A2S13fSb5Z100A2A2S13dS140Sb5Z4A2Z1A2A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma Hxcqb_0 : In (xc_map nx0) xcqb. Proof. exact (In_of_cellb (xc_map nx0) xcqb ltac:(vm_cast_no_check (eq_refl true))). Qed.
Lemma WCUqb_0 : ltac2:(tb__ "0|0|
S0S21S10S12fS2S77A1S26SaS3fVW;S89A2S23SaS49S2fA1S22SaA1A3A3A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SELUqb_0 : ltac2:(tb__ "0|0|
S0S24SaA1S12bS26SaS3fVW;S89A2S23SaS49S2fA1S22SaA1A3A3S42U0A1A2S40VW;S89S2fA3A3"). Proof. vm_cast_no_check (@eq_refl _ (KUB W swcqb nx0)). Qed.
Lemma NDUqb_0 : nodupN (idxsU 0%nat) = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDUqb_0 : ltac2:(tb__ "0|0|
S0S21S31S27S27S123R1S2bSaS26SaS3fVW;S89A2S23SaS49S2fA1S22SaA1A3A3A2A2Li;S42U0A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVUqb_0 : ltac2:(tb__ "0|1|
S0S21S31S27S27S33S27S122R1A1S42U0M0A1A3Li;S3aG0S2bSaS26SaS3fVW;S89A2S23SaS49S2fA1S22SaA1A3A3A2A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W9qb_0 : ltac2:(tb__ "0|0|
S0S21S10S43S77S40VW;S89S2fA3A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D9qb_0 : ltac2:(tb__ "0|5|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S45S12fS2S77A1S40VW;S89S2fA3M4A2S43S77G4A2A2S2aG3S29G1G2S23G0S29SbSbS11S137A1S14P18A1A4S22G0A1A3S22ScA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(SLit TP_A, SVar 24)], @nil sprop))). Qed.
Lemma XB9qb_0 : ltac2:(tb__ "0|0|
S0S21S9SeS2S77A1A1S29SbSbS4bS2fA1S14PcA1A4A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sFqb : wsub := Eval vm_compute in (infer_sub NF (S2F FFqb (KUB W swcqb nx0)) (ax_S (L_malloc_ok AE_A W st))).
Lemma ENT9qb_0 : ltac2:(tb__ "0|0|
S0S21S8S44S77S40VW;S89S2fA3S2fA3S11cS11bVW;Vst;A3Se3A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID9qb_0 : ltac2:(tb__ "0|0|
S0S21S12dSe3S135A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma G110qb_0 : ltac2:(tb__ "0|0|
S0SbS12eSe3S11dA2S4bS2fA1A3"). Proof. vm_cast_no_check (@eq_refl _ (UBs nx0)). Qed.
End INST.
End SpineMallocSec6I.

(* [comment removed for export] *)
Module SpineMallocSec5JLW2.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "sobj"; "obj_range"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "DG"; "aa_geom"; "ag_pab"; "@Corelib.Init.Datatypes"; "list"; "nil"; "pair"; "prod"; "fst"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3"; "JGs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jm.SpineMallocSec3ILW2"; "nx0"; "@Corelib.Init.Logic"; "eq"; "and"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "ulink"; "KcA"; "Kc_ok"; "UStopLeOrPc"; "ustop"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "world"; "assn"; "etriple"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jn.DepotCallS"; "AXK"; "dlink"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger"; "sepZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dblocks"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "secmapsize"; "stopJ_stable"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.SecBump"; "bumpP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k6.SpineMallocSec5ILW2"; "C5ac"; "C5bc"; "X5ac"; "X5bc"; "EXoa"; "EXob"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "kPtrArrayReserve"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocSec4ILW2"; "T4ac"; "T4bc"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocSec4ILW2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require js.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k6.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.CertMallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SegD_refl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.SecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.SecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jm.SpineMallocSec3ILW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineMallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocSec4ILW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertMallocSU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jq.SpineMallocSec5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jn.DepotCallS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.js.SpineMallocSec6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k6.SpineMallocSec5ILW2.
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

Theorem depot_call_S_2la : ltac2:(tb__ "0|6|
S20OF_;S6S19S2S1eQ40M0A1M1S21S15S1cVst;S1bA3S15SaS18A1VW;SbS18A1A3F_;S29VW;Vst;A2S1aR6A1S12S1R9S11R7A1A3S2dS1RaS11R8A1A3S7S2S2SaG1A1M2SdS0S0A2M3S23G3R1S27R5A1A3S26R2ScS0S0S1dG0RdA2S28S1dG0S3RePcA2A2A1A4A2F_;Fbn;S25R5RdR4A3S1fS1R11S10S1S13U2M4Vst;S14S24S6S2eR1A1LX;M5R6A2R10RfR5RdA8S2fR4R3A5RcA4F_;F_;Ftp';FrhoX;Frho';FG2;S2G2S1fS1ReS10S1S13G4Vst;S14G5RdRcRbRaA8S31R2R1A5R9A4Ftp;FrhoE;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Proof.
  exact (depot_call_S 2%nat st tmax nx0 Hnx_0 NXG_0 (fun X : AA => bumpP X) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl)
           Htmax_0 X5ac C5ac NXEa_0 FBEa_0 F192a_0 FDEPa_0 FUNWa_0 WX5ra_0 DX5ra_0 SPL1a_0 SPL2a_0 SPL3a_0 SPL4a_0
           s4a_i R4a_i T4a_i HERa_0 HT4a_0 XX4a_0 FBX4a_0 Hchk4a_0 NX4a_0 WG10a_0 WG15a_0 WG12a_0 EXoa FAM4a_0 EXZa_0 NEWOa_0 XPosta_0
           FBT4a_0 XT4a_0 RB1a_0 RB2a_0 nobja PERM_nda_0 PERM_lta_0 PERM_cova_0 PERM_lena_0 MRG1a_0 MRG2a_0 MRG3a_0 MRG4a_0 sda_i ENT5a_0 SID5a_0 R4cova_0).
Qed.

Theorem depot_call_SE_2la : ltac2:(tb__ "0|6|
S6S19S2S1eQ40M0A1M1S20OF_;S15S1cVst;S1bA3S15SaS18A1VW;SbS18A1A3F_;S29VW;Vst;A2S1aR6A1S7S2S2SaG1A1M2SdS0S0A2M3S23G3R1S27R5A1A3S26R2ScS0S0S1dG0RbA2S28S1dG0S3RcPcA2A2A1A4A2F_;Fbn;S25R5RbR4A3S22S1S10S1S13U2M4Vst;S14S24S6S2eR1A1LX;M5R6A2ReRdR5RbA8S2fR4R3A5RaA3F_;F_;Ftp';FrhoX;Frho';FG2;S2G2S22S1S10S1S13G4Vst;S14G5RbRaR9R8A8S31R2R1A5R7A3Ftp;FrhoE;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;").
Proof.
  exact (depot_call_SE 2%nat st tmax nx0 Hnx_0 NXG_0 (fun X : AA => bumpP X) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl)
           Htmax_0 X5ac C5ac NXEa_0 FBEa_0 F192a_0 FDEPa_0 FUNWa_0 WX5ra_0 DX5ra_0 SPL1a_0 SPL2a_0 SPL3a_0 SPL4a_0
           s4a_i R4a_i T4a_i HERa_0 HT4a_0 XX4a_0 FBX4a_0 Hchk4a_0 NX4a_0 WG10a_0 WG15a_0 WG12a_0 EXoa FAM4a_0 EXZa_0 NEWOa_0 XPosta_0
           FBT4a_0 XT4a_0 RB1a_0 RB2a_0 nobja PERM_nda_0 PERM_lta_0 PERM_cova_0 PERM_lena_0 MRG1a_0 MRG2a_0 MRG3a_0 MRG4a_0 sda_i ENT5a_0 SID5a_0 R4cova_0).
Qed.

Theorem sec_g41_2la : ltac2:(tb__ "0|6|
S20OF_;S6S19S2S1eQ40M0A1M1S21S15S1cVst;S1bA3S15SaS18A1VW;SbS18A1A3F_;S29VW;Vst;A2S1aR6A1S12S1R9S11R7A1A3S2dS1RaS11R8A1A3S7S2S2SaG1A1M2SdS0S0A2M3S23G3R1S27R5A1A3S26R2ScS0S0S1dG0RdA2S28S1dG0S3RePcA2A2A1A4A2F_;Fbn;S25R5RdR4A3S1fS1R11S10S1S13U2M4Vst;S14S24S6S2eR1A1LX;M5R6A2R10RfR5RdA8S2fR4R3A5RcA4F_;F_;Ftp';FrhoX;Frho';FG2;S2G2S1fS1ReS10S1S13G4Vst;S14G5RdRcRbRaA8S38R2R1A5R9A4FtX;FrX;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Proof.
  exact (sec_g41 2%nat st tmax nx0 Hnx_0 NXG_0 (fun X : AA => bumpP X) T4ac U4ac X5ac C5ac WU4a_0 DU4a_0 NXU4a_0 HU4a_0 Cert5a_0 depot_call_S_2la).
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

Theorem depot_call_S_2lb : ltac2:(tb__ "0|6|
S20OF_;S6S19S2S1eQ40M0A1M1S21S15S1cVst;S1bA3S15SaS18A1VW;SbS18A1A3F_;S29VW;Vst;A2S1aR6A1S12S1R9S11R7A1A3S2dS1RaS11R8A1A3S7S2S2SaG1A1M2SdS0S0A2M3S23G3R1S27R5A1A3S26R2ScS0S0S1dG0RdA2S28S1dG0S3RePcA2A2A1A4A2F_;Fbn;S25R5RdR4A3S1fS1R11S10S1S13U2M4Vst;S14S24S6R1LX;M5R6A2R10RfR5RdA8S30R4R3A5RcA4F_;F_;Ftp';FrhoX;Frho';FG2;S2G2S1fS1ReS10S1S13G4Vst;S14G5RdRcRbRaA8S32R2R1A5R9A4Ftp;FrhoE;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Proof.
  exact (depot_call_S 2%nat st tmax nx0 Hnx_0 NXG_0 (fun X : AA => X) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl)
           Htmax_0 X5bc C5bc NXEb_0 FBEb_0 F192b_0 FDEPb_0 FUNWb_0 WX5rb_0 DX5rb_0 SPL1b_0 SPL2b_0 SPL3b_0 SPL4b_0
           s4b_i R4b_i T4b_i HERb_0 HT4b_0 XX4b_0 FBX4b_0 Hchk4b_0 NX4b_0 WG10b_0 WG15b_0 WG12b_0 EXob FAM4b_0 EXZb_0 NEWOb_0 XPostb_0
           FBT4b_0 XT4b_0 RB1b_0 RB2b_0 nobjb PERM_ndb_0 PERM_ltb_0 PERM_covb_0 PERM_lenb_0 MRG1b_0 MRG2b_0 MRG3b_0 MRG4b_0 sdb_i ENT5b_0 SID5b_0 R4covb_0).
Qed.

Theorem depot_call_SE_2lb : ltac2:(tb__ "0|6|
S6S19S2S1eQ40M0A1M1S20OF_;S15S1cVst;S1bA3S15SaS18A1VW;SbS18A1A3F_;S29VW;Vst;A2S1aR6A1S7S2S2SaG1A1M2SdS0S0A2M3S23G3R1S27R5A1A3S26R2ScS0S0S1dG0RbA2S28S1dG0S3RcPcA2A2A1A4A2F_;Fbn;S25R5RbR4A3S22S1S10S1S13U2M4Vst;S14S24S6R1LX;M5R6A2ReRdR5RbA8S30R4R3A5RaA3F_;F_;Ftp';FrhoX;Frho';FG2;S2G2S22S1S10S1S13G4Vst;S14G5RbRaR9R8A8S32R2R1A5R7A3Ftp;FrhoE;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;").
Proof.
  exact (depot_call_SE 2%nat st tmax nx0 Hnx_0 NXG_0 (fun X : AA => X) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl)
           Htmax_0 X5bc C5bc NXEb_0 FBEb_0 F192b_0 FDEPb_0 FUNWb_0 WX5rb_0 DX5rb_0 SPL1b_0 SPL2b_0 SPL3b_0 SPL4b_0
           s4b_i R4b_i T4b_i HERb_0 HT4b_0 XX4b_0 FBX4b_0 Hchk4b_0 NX4b_0 WG10b_0 WG15b_0 WG12b_0 EXob FAM4b_0 EXZb_0 NEWOb_0 XPostb_0
           FBT4b_0 XT4b_0 RB1b_0 RB2b_0 nobjb PERM_ndb_0 PERM_ltb_0 PERM_covb_0 PERM_lenb_0 MRG1b_0 MRG2b_0 MRG3b_0 MRG4b_0 sdb_i ENT5b_0 SID5b_0 R4covb_0).
Qed.

Theorem sec_g41_2lb : ltac2:(tb__ "0|6|
S20OF_;S6S19S2S1eQ40M0A1M1S21S15S1cVst;S1bA3S15SaS18A1VW;SbS18A1A3F_;S29VW;Vst;A2S1aR6A1S12S1R9S11R7A1A3S2dS1RaS11R8A1A3S7S2S2SaG1A1M2SdS0S0A2M3S23G3R1S27R5A1A3S26R2ScS0S0S1dG0RdA2S28S1dG0S3RePcA2A2A1A4A2F_;Fbn;S25R5RdR4A3S1fS1R11S10S1S13U2M4Vst;S14S24S6R1LX;M5R6A2R10RfR5RdA8S30R4R3A5RcA4F_;F_;Ftp';FrhoX;Frho';FG2;S2G2S1fS1ReS10S1S13G4Vst;S14G5RdRcRbRaA8S39R2R1A5R9A4FtX;FrX;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Proof.
  exact (sec_g41 2%nat st tmax nx0 Hnx_0 NXG_0 (fun X : AA => X) T4bc U4bc X5bc C5bc WU4b_0 DU4b_0 NXU4b_0 HU4b_0 Cert5b_0 depot_call_S_2lb).
Qed.
End INST.
End SpineMallocSec5JLW2.

