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
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cm.
From Stdlib Require FunctionalExtensionality.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ch.

(* [comment removed for export] *)
Module SpineCallocSec5JW1.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "sobj"; "obj_range"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "DG"; "aa_geom"; "ag_pab"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineCallocSec3"; "JGs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c1.SpineCallocSec3IW1"; "nx0"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@Corelib.Init.Datatypes"; "list"; "pair"; "prod"; "fst"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "world"; "assn"; "etriple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "Kc_ok"; "@Stdlib.Lists.List"; "In"; "@Corelib.Init.Logic"; "and"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c5.CDepotCallS"; "AXK"; "dlink"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase"; "stopJ_w"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger"; "sepZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "dblocks"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "secmapsize"; "stopJ_stable"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.CSecBump"; "bumpP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cm.SpineCallocSec5IW1"; "C5ac"; "C5bc"; "X5ac"; "X5bc"; "EXoa"; "EXob"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "kPtrArrayReserve"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineCallocSec4IW1"; "T4ac"; "T4bc"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require al.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require q0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineCallocSec4IW1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CDepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cm.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aq.SpineCallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_refl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.CSecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.CSecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineCallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c1.SpineCallocSec3IW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c5.SpineCallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineCallocSec4IW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bd.CertCallocSU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c4.SpineCallocSec5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CDepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c5.CDepotCallS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cc.SpineCallocSec6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cm.SpineCallocSec5IW1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CallocBase2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CallocBase2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.CallocPosts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 1. Let st : ustop := UStopLeOrPc. Let tmax : Z := 3.
Let GS0 : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineCallocSec3.GS nx0.

Lemma EXZa_0 : ltac2:(tb__ "0|3|
S6S1aS2S10Q40A1M0S2S11G0A1S17S4S0SaS1SdU1Vst;SeS6S2aR1A1LX;R9R8R7R6A8S2dR5R4R3A6S1cS4R3S2fA3S1dS26S14S0S0S5R7R4A2M1A3R3A2S27R3S15S0S0G1A3A2A2S1eS1dS26S32R4A2S27R4S31A2A2S1dS26S9S8RcA1A1M2R4A2S27R4S28G2S33A2A2A2A2F_;F_;F_;Fz;Fo;Fw;Ftp;FrhoE;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a rhoE tp w o z Hw Ho Hz. pose proof (SPA_facts_hold segsA _ rhoE X5ac tp w Hw) as HF. destruct w as [tr [ms md]].
  pose proof (proj2 Hw) as HJ. cbn [w_tr w_cfg cfg_model fst snd] in HJ.
  pose proof (proj1 (Forall_forall _ _) HF _ FXBa_0) as HBR.
  destruct Ho as [<-|[<-|[<-|[]]]].
  - left. exact (ex2_band 1%nat st tmax nx0 Hnx_0 (fun X : AA => bumpP X) A Kc rho a rhoE tp tr md z HJ Hz).
  - left. exact (ex1_band 1%nat st tmax nx0 Hnx_0 (fun X : AA => bumpP X) A Kc rho a rhoE tp tr md z HJ Hz).
  - right. exact (exblk_pab 1%nat st tmax nx0 Hnx_0 (fun X : AA => bumpP X) A Kc rho a rhoE tp tr md z (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) HJ HBR Hz).
Qed.

Theorem depot_call_S_1ha : ltac2:(tb__ "0|6|
S17OF_;S6S1aS2S10Q40M0A1M1S18S21VW;Vst;A2S25VW;Vst;A2S1bR6A1ScS1R9SbR7A1A3S29S1RaSbR8A1A3S7S2S2S11G1A1M2S13S0S0A2M3S1cG3R1S23R5A1A3S22R2S12S0S0SfG0RdA2S24SfG0S3RePcA2A2A1A4A2F_;Fbn;S20R5RdR4A3S16S1R11SaS1SdU1M4Vst;SeS1fS6S2aR1A1LX;M5R6A2R10RfR5RdA8S2bR4R3A5RcA4F_;F_;Ftp';FrhoX;Frho';FG2;S2G2S16S1ReSaS1SdG4Vst;SeG5RdRcRbRaA8S2dR2R1A5R9A4Ftp;FrhoE;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Proof.
  exact (depot_call_S 1%nat st tmax nx0 Hnx_0 NXG_0 (fun X : AA => bumpP X) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl)
           Htmax_0 X5ac C5ac NXEa_0 FBEa_0 F192a_0 FDEPa_0 FUNWa_0 WX5ra_0 DX5ra_0 SPL1a_0 SPL2a_0 SPL3a_0 SPL4a_0
           s4a_i R4a_i T4a_i HERa_0 HT4a_0 XX4a_0 FBX4a_0 Hchk4a_0 NX4a_0 WG10a_0 WG15a_0 WG12a_0 EXoa FAM4a_0 EXZa_0 NEWOa_0 XPosta_0
           FBT4a_0 XT4a_0 RB1a_0 RB2a_0 nobja PERM_nda_0 PERM_lta_0 PERM_cova_0 PERM_lena_0 MRG1a_0 MRG2a_0 MRG3a_0 MRG4a_0 sda_i ENT5a_0 SID5a_0 R4cova_0).
Qed.

Theorem depot_call_SE_1ha : ltac2:(tb__ "0|6|
S6S1aS2S10Q40M0A1M1S17OF_;S21VW;Vst;A2S25VW;Vst;A2S1bR6A1S7S2S2S11G1A1M2S13S0S0A2M3S1cG3R1S23R5A1A3S22R2S12S0S0SfG0RbA2S24SfG0S3RcPcA2A2A1A4A2F_;Fbn;S20R5RbR4A3S19S1SaS1SdU1M4Vst;SeS1fS6S2aR1A1LX;M5R6A2ReRdR5RbA8S2bR4R3A5RaA3F_;F_;Ftp';FrhoX;Frho';FG2;S2G2S19S1SaS1SdG4Vst;SeG5RbRaR9R8A8S2dR2R1A5R7A3Ftp;FrhoE;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;").
Proof.
  exact (depot_call_SE 1%nat st tmax nx0 Hnx_0 NXG_0 (fun X : AA => bumpP X) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl)
           Htmax_0 X5ac C5ac NXEa_0 FBEa_0 F192a_0 FDEPa_0 FUNWa_0 WX5ra_0 DX5ra_0 SPL1a_0 SPL2a_0 SPL3a_0 SPL4a_0
           s4a_i R4a_i T4a_i HERa_0 HT4a_0 XX4a_0 FBX4a_0 Hchk4a_0 NX4a_0 WG10a_0 WG15a_0 WG12a_0 EXoa FAM4a_0 EXZa_0 NEWOa_0 XPosta_0
           FBT4a_0 XT4a_0 RB1a_0 RB2a_0 nobja PERM_nda_0 PERM_lta_0 PERM_cova_0 PERM_lena_0 MRG1a_0 MRG2a_0 MRG3a_0 MRG4a_0 sda_i ENT5a_0 SID5a_0 R4cova_0).
Qed.

Theorem sec_g41_1ha : ltac2:(tb__ "0|6|
S17OF_;S6S1aS2S10Q40M0A1M1S18S21VW;Vst;A2S25VW;Vst;A2S1bR6A1ScS1R9SbR7A1A3S29S1RaSbR8A1A3S7S2S2S11G1A1M2S13S0S0A2M3S1cG3R1S23R5A1A3S22R2S12S0S0SfG0RdA2S24SfG0S3RePcA2A2A1A4A2F_;Fbn;S20R5RdR4A3S16S1R11SaS1SdU1M4Vst;SeS1fS6S2aR1A1LX;M5R6A2R10RfR5RdA8S2bR4R3A5RcA4F_;F_;Ftp';FrhoX;Frho';FG2;S2G2S16S1ReSaS1SdG4Vst;SeG5RdRcRbRaA8S34R2R1A5R9A4FtX;FrX;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Proof.
  exact (sec_g41 1%nat st tmax nx0 Hnx_0 NXG_0 (fun X : AA => bumpP X) T4ac U4ac X5ac C5ac WU4a_0 DU4a_0 NXU4a_0 HU4a_0 Cert5a_0 depot_call_S_1ha).
Qed.

Lemma EXZb_0 : ltac2:(tb__ "0|3|
S6S1aS2S10Q40A1M0S2S11G0A1S17S4S0SaS1SdU1Vst;SeS6R1LX;R9R8R7R6A8S2eR5R4R3A6S1cS4R3S30A3S1dS26S14S0S0S5R7R4A2M1A3R3A2S27R3S15S0S0G1A3A2A2S1eS1dS26S32R4A2S27R4S31A2A2S1dS26S9S8RcA1A1M2R4A2S27R4S28G2S33A2A2A2A2F_;F_;F_;Fz;Fo;Fw;Ftp;FrhoE;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a rhoE tp w o z Hw Ho Hz. pose proof (SPA_facts_hold segsA _ rhoE X5bc tp w Hw) as HF. destruct w as [tr [ms md]].
  pose proof (proj2 Hw) as HJ. cbn [w_tr w_cfg cfg_model fst snd] in HJ.
  pose proof (proj1 (Forall_forall _ _) HF _ FXBb_0) as HBR.
  destruct Ho as [<-|[<-|[<-|[]]]].
  - left. exact (ex2_band 1%nat st tmax nx0 Hnx_0 (fun X : AA => X) A Kc rho a rhoE tp tr md z HJ Hz).
  - left. exact (ex1_band 1%nat st tmax nx0 Hnx_0 (fun X : AA => X) A Kc rho a rhoE tp tr md z HJ Hz).
  - right. exact (exw_pab 1%nat st tmax nx0 Hnx_0 (fun X : AA => X) A Kc rho a rhoE tp tr md z (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) HJ HBR Hz).
Qed.

Theorem depot_call_S_1hb : ltac2:(tb__ "0|6|
S17OF_;S6S1aS2S10Q40M0A1M1S18S21VW;Vst;A2S25VW;Vst;A2S1bR6A1ScS1R9SbR7A1A3S29S1RaSbR8A1A3S7S2S2S11G1A1M2S13S0S0A2M3S1cG3R1S23R5A1A3S22R2S12S0S0SfG0RdA2S24SfG0S3RePcA2A2A1A4A2F_;Fbn;S20R5RdR4A3S16S1R11SaS1SdU1M4Vst;SeS1fS6R1LX;M5R6A2R10RfR5RdA8S2cR4R3A5RcA4F_;F_;Ftp';FrhoX;Frho';FG2;S2G2S16S1ReSaS1SdG4Vst;SeG5RdRcRbRaA8S2eR2R1A5R9A4Ftp;FrhoE;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Proof.
  exact (depot_call_S 1%nat st tmax nx0 Hnx_0 NXG_0 (fun X : AA => X) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl)
           Htmax_0 X5bc C5bc NXEb_0 FBEb_0 F192b_0 FDEPb_0 FUNWb_0 WX5rb_0 DX5rb_0 SPL1b_0 SPL2b_0 SPL3b_0 SPL4b_0
           s4b_i R4b_i T4b_i HERb_0 HT4b_0 XX4b_0 FBX4b_0 Hchk4b_0 NX4b_0 WG10b_0 WG15b_0 WG12b_0 EXob FAM4b_0 EXZb_0 NEWOb_0 XPostb_0
           FBT4b_0 XT4b_0 RB1b_0 RB2b_0 nobjb PERM_ndb_0 PERM_ltb_0 PERM_covb_0 PERM_lenb_0 MRG1b_0 MRG2b_0 MRG3b_0 MRG4b_0 sdb_i ENT5b_0 SID5b_0 R4covb_0).
Qed.

Theorem depot_call_SE_1hb : ltac2:(tb__ "0|6|
S6S1aS2S10Q40M0A1M1S17OF_;S21VW;Vst;A2S25VW;Vst;A2S1bR6A1S7S2S2S11G1A1M2S13S0S0A2M3S1cG3R1S23R5A1A3S22R2S12S0S0SfG0RbA2S24SfG0S3RcPcA2A2A1A4A2F_;Fbn;S20R5RbR4A3S19S1SaS1SdU1M4Vst;SeS1fS6R1LX;M5R6A2ReRdR5RbA8S2cR4R3A5RaA3F_;F_;Ftp';FrhoX;Frho';FG2;S2G2S19S1SaS1SdG4Vst;SeG5RbRaR9R8A8S2eR2R1A5R7A3Ftp;FrhoE;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;").
Proof.
  exact (depot_call_SE 1%nat st tmax nx0 Hnx_0 NXG_0 (fun X : AA => X) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl)
           Htmax_0 X5bc C5bc NXEb_0 FBEb_0 F192b_0 FDEPb_0 FUNWb_0 WX5rb_0 DX5rb_0 SPL1b_0 SPL2b_0 SPL3b_0 SPL4b_0
           s4b_i R4b_i T4b_i HERb_0 HT4b_0 XX4b_0 FBX4b_0 Hchk4b_0 NX4b_0 WG10b_0 WG15b_0 WG12b_0 EXob FAM4b_0 EXZb_0 NEWOb_0 XPostb_0
           FBT4b_0 XT4b_0 RB1b_0 RB2b_0 nobjb PERM_ndb_0 PERM_ltb_0 PERM_covb_0 PERM_lenb_0 MRG1b_0 MRG2b_0 MRG3b_0 MRG4b_0 sdb_i ENT5b_0 SID5b_0 R4covb_0).
Qed.

Theorem sec_g41_1hb : ltac2:(tb__ "0|6|
S17OF_;S6S1aS2S10Q40M0A1M1S18S21VW;Vst;A2S25VW;Vst;A2S1bR6A1ScS1R9SbR7A1A3S29S1RaSbR8A1A3S7S2S2S11G1A1M2S13S0S0A2M3S1cG3R1S23R5A1A3S22R2S12S0S0SfG0RdA2S24SfG0S3RePcA2A2A1A4A2F_;Fbn;S20R5RdR4A3S16S1R11SaS1SdU1M4Vst;SeS1fS6R1LX;M5R6A2R10RfR5RdA8S2cR4R3A5RcA4F_;F_;Ftp';FrhoX;Frho';FG2;S2G2S16S1ReSaS1SdG4Vst;SeG5RdRcRbRaA8S35R2R1A5R9A4FtX;FrX;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Proof.
  exact (sec_g41 1%nat st tmax nx0 Hnx_0 NXG_0 (fun X : AA => X) T4bc U4bc X5bc C5bc WU4b_0 DU4b_0 NXU4b_0 HU4b_0 Cert5b_0 depot_call_S_1hb).
Qed.
End INST.
End SpineCallocSec5JW1.

(* [comment removed for export] *)
Module SpineCallocSecE3.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "False"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_setS"; "leafA"; "la_state"; "entailsA"; "ax_base"; "mkLeafA"; "xr_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "valuation"; "sv"; "sprop"; "ss_next"; "ss_facts"; "rw"; "cell"; "SLit"; "rm"; "swf"; "sprop_below"; "ss_objs"; "eval"; "holds"; "rl"; "obj_range"; "DUnknown"; "mkObj"; "SPNot"; "SVar"; "odefault"; "ranges_disjoint"; "sstate"; "DZero"; "@Corelib.Init.Datatypes"; "bool"; "true"; "list"; "cons"; "nil"; "prod"; "pair"; "option"; "app"; "nat"; "Some"; "length"; "None"; "andb"; "S"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "LQA"; "jpredA"; "stableA"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_geom"; "ageom"; "aa_sec"; "sec_chunk"; "aa_Km"; "aa_depot"; "DG"; "aa_ptr_committed"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "Kc_ok"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "mem_keptA"; "V_RES"; "base_sv"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "seq"; "@Stdlib.Lists.List"; "In"; "forallb"; "incl"; "existsb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3"; "skel"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "div"; "lt"; "of_nat"; "eqb"; "leb"; "ltb"; "modulo"; "mul"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "secmapsize"; "stopJ_stable"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase"; "stopJ_w"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP"; "MSENT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "Sh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocST"; "O_1"; "carveS"; "O_2"; "Pret_ms"; "BR"; "Pret_mz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.CertCallocSV"; "F_A"; "L3"; "CPC"; "F_B"; "O_3"; "O_UBs"; "B3"; "F_par"; "O_3b"; "perm7"; "B4"; "PGST"; "UBs"; "a2e6"; "a2e8"; "osplit"; "BP9"; "F_g7"; "F_g8"; "F_g9"; "L3b"; "O_4z"; "RSF"; "a0e7"; "a2e7"; "fx8"; "ic_c1"; "ic_c2"; "ic_nch"; "ic_nres"; "ic_pg"; "ic_rs"; "mc_cptr"; "mc_idx"; "mc_magic"; "mc_map"; "mc_ms"; "mc_ns"; "mc_size"; "mc_sizehi"; "mc_state"; "mc_type"; "sel7"; "xc_map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger"; "sepZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "dblocks"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "LQPA"; "jpostA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.CSecOKInv"; "bumpV"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineCallocSec3"; "SKEL0"; "range_noband"; "JGs"; "GS"; "slink"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ch.SpineCallocSec7"; "idxsF"; "idxsU"; "S2F"; "KUB"; "XF_of"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "ltb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Str_memsetZ"; "Pre_mszA"; "Posts_mszA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "nodupN"; "select"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "wsub"; "wsub_get"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "RsSymJump"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.CallocPosts"; "Lc_ok"; "JLc_ok"; "PFc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CDepotCall"; "isSome"; "omrg"; "oreb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c5.CDepotCallS"; "AXK"; "dlink"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSS"; "nxS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bd.CertCallocSU"; "DPENT"; "F_g4"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ch.SpineCallocSec6L"; "F_low"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "merge_objs_at"; "rebase_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM"; "IMG_M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bx.SpineCallocSec2"; "IMG_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cq.SpineCallocSecE3.SEC6E"; "slink_refl_of"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA EntailA CFGA GlueA GlueA2 SummaryA SysCallA MmapA MmapFixedA LedgerA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require MallocInv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Placement StartLib StartDefsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fi.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Placement OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartLib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e8.StartGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SMGlue InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNullInit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require al.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineCallocS4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ba.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bi.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RebuildM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require MmapSymA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineCallocSec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bx.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require q0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require EnsureMapA CDepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SecLog2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ch.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ca.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.SpineCallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineCallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.SpineCallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineCallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineCallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.RebuildN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.MmapSymA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.CertCallocSN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineCallocSec OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bx.SpineCallocSec2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.SegD_cost OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.LedgerLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.InvD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.DepotK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.CSecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SecReveal OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvReveal OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineCallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.EnsureMapA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CDepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.CSecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SecLog2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b3.CInvEnsure OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bd.CertCallocSU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c5.SpineCallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c4.SpineCallocSec5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.DepotKP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c5.CDepotCallS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.CertCallocSV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.CRebuildS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ch.SpineCallocSec6L OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ch.SpineCallocSec7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c1.SpineCallocSecE1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ca.SpineCallocSecE2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ch.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ca.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cc.SpineCallocSec6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ch.SpineCallocSec6L OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ch.SpineCallocSec7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c1.SpineCallocSecE1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ca.SpineCallocSecE2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CallocBase2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ak.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CallocBase2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CallocArith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SpineCallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineCallocI2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.CallocPosts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase.
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
S0S37ScfVW;Vst;Vtmax;A3Vnx;A3").
Hypothesis NXG : ltac2:(tb__ "0|0|
S0S27S6cSd2Vnx;A2S28A3").
Let GS : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineCallocSec3.GS nx.
Let JG (BX : AA -> AA) : AA -> KcA -> valuation -> word -> jpredA := ltac2:(tb__ "0|0|
Sb3VnW;Vst;Vnx;VBX;A4").

Lemma ems_call : ltac2:(tb__ "0|7|
S3fS3fF_;S6S6S6S6S29S8A1M0Sc3S29SeA1M1S0G0R3S2aS8ScR4Sc6A2S2bS8A1A3A3S3aSfS29S3dQ40A1M2A1M3S3bVsegs;S75R3A3S5cVsegs;S38Vsegs;R4RaR3R2A5S39Vsegs;R4S75R3R2R8A6A3F_;Ftp;Frho;FJx;S0S37S12S5R7A1A1S75A3S0S2eG1A1SacRaR8R5A3S31G1R4A2A3S0S27SabRbR9R6R5S50S8S6S9R7A4A5S28A3S0S6SadR7RaR9RcR6A5RbA3S0S27S54S11S19S12S5RdA1M4A1A1M5S13G4A1A3S28A3S0S27S54S11G5S13S5ReA1A1A3S28A3S0S27S6cVGS;S12S5RfA1A1A2S28A3S3fS48SfG2G3S5dOF_;S6bVW;Vst;A2S49R6A1SfG3S5cVsegs;S38Vsegs;VJG;R1bRaR9R8R7A5M6SaaR19S13S5R1aA1A1A2R2R1A5R5A3FtpY;FrhoY;SfS5cVsegs;S38Vsegs;G6R1aR1R6A5R5A3FrhoX;F_;F_;F_;FQ;Ftp;Fa;Frho;FKc;FA;F_;F_;F_;F_;F_;F_;F_;F_;F_;FR;Fs;FPosts;FPret;FPre;FT;FCM;FBX;").
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
S36S1S5fS70S3cQ40M0Va;A2A1M1R1A2S62R1S60G1S61S6aS3cG0S14Vrho;PcA2A2A1Z8A2A2A2A2S2S0S2eS3dQ8A1M2A1S17Vrho;S3eG0R2A2A2S33G2A1A3A1F_;Fz;").
Lemma slink_refl : ltac2:(tb__ "0|1|
SfS3dQ40M0A1Sd9R2R1A2Sb5S3cG0R2A2S6aS3cG0S14R3PcA2A2A1R3R3A4F_;Fa;Frho;").
Proof. intros rho a RD. split; [intros i; reflexivity|]. split; [intros l; reflexivity|]. split; [intros x; left; reflexivity | exact RD]. Qed.

Section G41E.
Variable BX : AA -> AA.
Variables (T4 U4 X5 C5 : axst).
Hypothesis WU4 : ltac2:(tb__ "0|0|
S0S27S18S5VU4;A1A1S28A3").
Hypothesis DU4 : ltac2:(tb__ "0|4|
S0S2eS2cS29S2cS10S10A2M0A1M1S29S11A1M2A2M3A1S6eS5VT4;A1S5VU4;A1A2S31G3S2dG1G2S2bG0A1Sd1Vnx;A1A4A2A3").
Hypothesis NXU4 : ltac2:(tb__ "0|0|
S0S37S12S5VU4;A1A1S12S5VT4;A1A1A3").
Hypothesis HU4 : ltac2:(tb__ "0|0|
S0S6S7VT4;S5VU4;A1A2VU4;A3").
Hypothesis Cert5 : ltac2:(tb__ "0|1|
S0S27S59S69Ufa0S2aS36Sd0S2bS36A1A3VGS;S2aS6VU4;S2bS6A1M0A3S2aS6VX5;G0A3A6S28A3").
Hypothesis NXE5 : ltac2:(tb__ "0|0|
S0S27S6cVGS;S12S5VU4;A1A1A2S28A3").
Hypothesis ECert5 : ltac2:(tb__ "0|3|
S0S27S5aS69Ufa0S2aS36Sd0S2bS36A1A3VGS;S2aS57S58VU4;Z1S16Z0M0A1M1A3S2bS57A1M2A3S2aS57S58VX5;G0G1A3G2A3A6S28A3").
Hypothesis HDSE : ltac2:(tb__ "0|4|
S3fS48SfS3dQ40M0A1M1S5dOF_;S6dVW;Vst;A2S6bVW;Vst;A2S49R6A1S46SfSfS29G1A1M2S2cS36S36A2M3S53G3R1Sa9R5A1A3Sa8R2S2dS36S36S3cG0RbA2S6aS3cG0S14RcPcA2A2A1A4A2F_;Fbn;SceR5RbR4A3S5cVsegs;S38Vsegs;VJG;ScdVBX;R6A2ReRdR5RbA5VC5;R4R3A5RaA3F_;F_;Ftp';FrhoX;Frho';FG2;SfG2S5cVsegs;S38Vsegs;VJG;VBX;RbRaR9R8A5VX5;R2R1A5R7A3Ftp;FrhoE;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;").

Theorem esec_g41 : ltac2:(tb__ "0|4|
S3fS48SfS3dQ40M0A1M1S5dOF_;S6dVW;Vst;A2S6bVW;Vst;A2S49R6A1S46SfSfS29G1A1M2S2cS36S36A2M3S53G3R1Sa9R5A1A3Sa8R2S2dS36S36S3cG0RbA2S6aS3cG0S14RcPcA2A2A1A4A2F_;Fbn;SceR5RbR4A3S5cVsegs;S38Vsegs;VJG;ScdVBX;R6A2ReRdR5RbA5VC5;R4R3A5RaA3F_;F_;Ftp';FrhoX;Frho';FG2;SfG2S5cVsegs;S38Vsegs;VJG;VBX;RbRaR9R8A5VT4;R2R1A5R7A3FtX;FrX;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;").
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
S3fS0S41S40VBX;R1A1A1S40R1A1A3FX;").
Variable PX : list sobj.
Variable FXP : list sprop.
Hypothesis PX_noband : ltac2:(tb__ "0|2|
S3fS48SfS3dQ40A1M0SfS29G0A1S29S74A1S73VJG;VBX;R8R7R6R5R4R3R2R1A9S51S11S1cR5A1VFXP;A3S29SeA1S0S29S2cS2cS10S10A2S10A2M1A1S50SeG1S5eR1A4S50SeG1S5eVPX;A4A3S51SeSeSb2S1eR9R1A2A1Lo;R2A3F_;Fl;F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;").
Variables (C5 C5A C5B Y6A Y6B E6 CT6 CO6 T6 : axst) (sA sB s6 : wsub) (R6 : list sobj).
Let D6 : axst := ltac2:(tb__ "0|0|
SaaVT6;S13S5VCO6;A1A1A2").
Hypothesis HC5A : ltac2:(tb__ "0|0|
S0S6S5bS7cVnx;A1VC5;A2VC5A;A3").
Hypothesis HC5B : ltac2:(tb__ "0|0|
S0S6S5bS7fVnx;A1VC5;A2VC5B;A3").
Hypothesis FBA : ltac2:(tb__ "0|0|
S0S27S54S11S19S12S5VC5;A1A1A1S7cVnx;A1A3S28A3").
Hypothesis FBB : ltac2:(tb__ "0|0|
S0S27S54S11S19S12S5VC5;A1A1A1S7fVnx;A1A3S28A3").
Hypothesis Cert6A : ltac2:(tb__ "0|1|
S0S27S59S69Ufa0S2aS36S6fS2bS36A1A3VGS;S2aS6VC5A;S2bS6A1M0A3S2aS6VY6A;G0A3A6S28A3").
Hypothesis Cert6B : ltac2:(tb__ "0|1|
S0S27S59S69Ufa0S2aS36S6fS2bS36A1A3VGS;S2aS6VC5B;S2bS6A1M0A3S2aS6VY6B;G0A3A6S28A3").
Hypothesis E6A : ltac2:(tb__ "0|0|
S0S27SaVY6A;VE6;VsA;A3S28A3").
Hypothesis I6A : ltac2:(tb__ "0|0|
S0S27Sc2VsA;VGS;A2S28A3").
Hypothesis E6B : ltac2:(tb__ "0|0|
S0S27SaVY6B;VE6;VsB;A3S28A3").
Hypothesis I6B : ltac2:(tb__ "0|0|
S0S27Sc2VsB;VGS;A2S28A3").
Hypothesis WC6 : ltac2:(tb__ "0|0|
S0S27S18S5VCT6;A1A1S28A3").
Hypothesis DF6 : ltac2:(tb__ "0|4|
S0S2eS2cS29S2cS10S10A2M0A1M1S29S11A1M2A2M3A1S6eS5VE6;A1S5VCT6;A1A2S31G3S2dG1G2S2aG0S2dS10S10S89Vnx;A1S7dA4S2bG0A1A3S2bS11A1A4A2A3").
Hypothesis NX6 : ltac2:(tb__ "0|0|
S0S37S12S5VCT6;A1A1S12S5VE6;A1A1A3").
Hypothesis HC6 : ltac2:(tb__ "0|0|
S0S6S7VE6;S5VCT6;A1A2VCT6;A3").
Hypothesis SK6 : ltac2:(tb__ "0|1|
S0S29S2cS2cS10S10A2S10A2M0A1S50SeG0S5eS1aS5VCT6;A1A1A4S50SeG0S5eS2fSeS2aSeS78Vnx;A1S2aSeS76Vnx;A1S2bSeA1A3A3S2fSeSb1VnW;Vnx;A2VPX;A3A3A4A3").
Hypothesis FC6 : ltac2:(tb__ "0|0|
S55S11S2fS11S4cVW;Vst;A2S4bS4aA1A3S13S5VCT6;A1A1A3").
Hypothesis FX6 : ltac2:(tb__ "0|0|
S55S11VFXP;S13S5VCT6;A1A1A3").
Hypothesis XC6 : ax_X CT6 = [].
Hypothesis HCO6 : ltac2:(tb__ "0|0|
S0S6S77VCT6;S20S82Vnx;A1S16Z0A1S7dS2bS15A1S1fA5A2VCO6;A3").
Hypothesis WCO6 : ltac2:(tb__ "0|0|
S0S27S18S5VCO6;A1A1S28A3").
Hypothesis He6 : ltac2:(tb__ "0|1|
S0S2eS29SeA1M0A1SacVCO6;S71Vs6;A3S31G0VR6;A2A3").
Hypothesis Hchk6 : ltac2:(tb__ "0|0|
S0S27SabVCO6;S71Vs6;VR6;S50S8S6S9S72A4A5S28A3").
Hypothesis HT6 : ltac2:(tb__ "0|0|
S0S6SadVs6;S71S79VCO6;VR6;A5VT6;A3").
Hypothesis FBC6 : ltac2:(tb__ "0|1|
S0S27S54S11S19S12S5VCO6;A1M0A1A1S13G0A1A3S28A3").
Hypothesis FBT6 : ltac2:(tb__ "0|0|
S0S27S54S11S19S12S5VT6;A1A1A1S13S5VCO6;A1A1A3S28A3").
Hypothesis NXC6 : ltac2:(tb__ "0|0|
S0S27S6cVGS;S12S5VCO6;A1A1A2S28A3").
Hypothesis NXE6A : ltac2:(tb__ "0|0|
S0S27S6cVGS;S12S5VC5A;A1A1A2S28A3").
Hypothesis ECert6A : ltac2:(tb__ "0|3|
S0S27S5aS69Ufa0S2aS36S6fS2bS36A1A3VGS;S2aS57S58VC5A;Z1S16Z0M0A1M1A3S2bS57A1M2A3S2aS57S58VY6A;G0G1A3G2A3A6S28A3").
Hypothesis NXE6B : ltac2:(tb__ "0|0|
S0S27S6cVGS;S12S5VC5B;A1A1A2S28A3").
Hypothesis ECert6B : ltac2:(tb__ "0|3|
S0S27S5aS69Ufa0S2aS36S6fS2bS36A1A3VGS;S2aS57S58VC5B;Z1S16Z0M0A1M1A3S2bS57A1M2A3S2aS57S58VY6B;G0G1A3G2A3A6S28A3").
Lemma RS6' : ltac2:(tb__ "0|1|
S3fS48SfS3dQ40A1M0SfS29G0A1S5dS6dVW;Vst;A2S38Vsegs;VJG;VBX;R8R7R6R5A5VE6;R4R3R2A6S38Vsegs;VJG;VBX;R9R8R7R6A5VCT6;R5R4R3A6F_;F_;Fw;Ftp;FrhoX;Fa;Frho;FKc;FA;").
Proof. rr RS6. Qed.
Lemma HBL6' : ltac2:(tb__ "0|b|
S3fS48SfS3dQ40M0A1M1SfS29G1A1S5dS38Vsegs;VJG;VBX;R7R6R5R4A5VCT6;R3R2R1A6S1S5fS70S3cG0R5A2A1M2S3cG0S1bR4S82Vnx;A1M3A2A2M4A2S1S5fS60G4S3cG0S1bR4S7dA2A2A2S60G2S61S6aS3cG0S14R6PcA2A2A1Z8A2A2A2S1S29SeA1M5S0S29S2cS2cS10S10A2S10A2M6A1M7S50SeG6S5eR1A4M8S50SeG6S5eS2aSeS78Vnx;A1S2aSeS76Vnx;A1S2bSeA1A3A3A4A3S51SeSeS24S1eR7R1A2S2dS36S36S3cG0S1bR7G3A2A2M9S60G9S3cG0S1bR7S7dA2A2A2A4A2Lo;R2A3MaF_;Fl;G5S0G7G8S50SeG6S5eVPX;A4A3GaF_;Fl;A2A2A2F_;Fw;Ftp;FrhoX;Fa;Frho;FKc;FA;").
Proof. rr HBL6. Qed.

Theorem esec_g43 : ltac2:(tb__ "0|5|
S3fS48SfS3dQ40M0A1M1S5dOF_;S6dVW;Vst;A2S6bVW;Vst;A2S49R6A1S36S1S5fS70S3cG0R6A2A1M2R1A2S62R1S60G2S61S6aS3cG0S14R7PcA2A2A1Z8A2A2A2A2S2S0S2eS3dQ8A1M3A1S17R8S3eG0R2A2A2S33G3A1A3A1F_;Fz;SfS29G1A1M4S5cVsegs;S38Vsegs;VJG;VBX;RbRaR9R8A5VD6;R2R1A5R7A3FtpY;FrhoY;SfG4S5cVsegs;S38Vsegs;VJG;VBX;RcRbRaR9A5VC5;R2R1A5R8A3FtX;FrX;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;").
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
S3fS0S41S40VBX;R1A1A1S40R1A1A3FX;").
Variable PX : list sobj.
Variable FXP : list sprop.
Hypothesis PX_noband : ltac2:(tb__ "0|2|
S3fS48SfS3dQ40A1M0SfS29G0A1S29S74A1S73VJG;VBX;R8R7R6R5R4R3R2R1A9S51S11S1cR5A1VFXP;A3S29SeA1S0S29S2cS2cS10S10A2S10A2M1A1S50SeG1S5eR1A4S50SeG1S5eVPX;A4A3S51SeSeSb2S1eR9R1A2A1Lo;R2A3F_;Fl;F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;").
Variables (C5 C5A Y6A E6 CT6 CO6 T6 : axst) (sA s6 : wsub) (R6 : list sobj).
Let D6 : axst := ltac2:(tb__ "0|0|
SaaVT6;S13S5VCO6;A1A1A2").
Hypothesis FLOW : ltac2:(tb__ "0|0|
S53S11Sd3Vnx;A1S13S5VC5;A1A1A3").
Hypothesis HC5A : ltac2:(tb__ "0|0|
S0S6S5bS7cVnx;A1VC5;A2VC5A;A3").
Hypothesis FBA : ltac2:(tb__ "0|0|
S0S27S54S11S19S12S5VC5;A1A1A1S7cVnx;A1A3S28A3").
Hypothesis Cert6A : ltac2:(tb__ "0|1|
S0S27S59S69Ufa0S2aS36S6fS2bS36A1A3VGS;S2aS6VC5A;S2bS6A1M0A3S2aS6VY6A;G0A3A6S28A3").
Hypothesis E6A : ltac2:(tb__ "0|0|
S0S27SaVY6A;VE6;VsA;A3S28A3").
Hypothesis I6A : ltac2:(tb__ "0|0|
S0S27Sc2VsA;VGS;A2S28A3").
Hypothesis WC6 : ltac2:(tb__ "0|0|
S0S27S18S5VCT6;A1A1S28A3").
Hypothesis DF6 : ltac2:(tb__ "0|4|
S0S2eS2cS29S2cS10S10A2M0A1M1S29S11A1M2A2M3A1S6eS5VE6;A1S5VCT6;A1A2S31G3S2dG1G2S2aG0S2dS10S10S89Vnx;A1S7dA4S2bG0A1A3S2bS11A1A4A2A3").
Hypothesis NX6 : ltac2:(tb__ "0|0|
S0S37S12S5VCT6;A1A1S12S5VE6;A1A1A3").
Hypothesis HC6 : ltac2:(tb__ "0|0|
S0S6S7VE6;S5VCT6;A1A2VCT6;A3").
Hypothesis SK6 : ltac2:(tb__ "0|1|
S0S29S2cS2cS10S10A2S10A2M0A1S50SeG0S5eS1aS5VCT6;A1A1A4S50SeG0S5eS2fSeS2aSeS78Vnx;A1S2aSeS76Vnx;A1S2bSeA1A3A3S2fSeSb1VnW;Vnx;A2VPX;A3A3A4A3").
Hypothesis FC6 : ltac2:(tb__ "0|0|
S55S11S2fS11S4cVW;Vst;A2S4bS4aA1A3S13S5VCT6;A1A1A3").
Hypothesis FX6 : ltac2:(tb__ "0|0|
S55S11VFXP;S13S5VCT6;A1A1A3").
Hypothesis XC6 : ax_X CT6 = [].
Hypothesis HCO6 : ltac2:(tb__ "0|0|
S0S6S77VCT6;S20S82Vnx;A1S16Z0A1S7dS2bS15A1S1fA5A2VCO6;A3").
Hypothesis WCO6 : ltac2:(tb__ "0|0|
S0S27S18S5VCO6;A1A1S28A3").
Hypothesis He6 : ltac2:(tb__ "0|1|
S0S2eS29SeA1M0A1SacVCO6;S71Vs6;A3S31G0VR6;A2A3").
Hypothesis Hchk6 : ltac2:(tb__ "0|0|
S0S27SabVCO6;S71Vs6;VR6;S50S8S6S9S72A4A5S28A3").
Hypothesis HT6 : ltac2:(tb__ "0|0|
S0S6SadVs6;S71S79VCO6;VR6;A5VT6;A3").
Hypothesis FBC6 : ltac2:(tb__ "0|1|
S0S27S54S11S19S12S5VCO6;A1M0A1A1S13G0A1A3S28A3").
Hypothesis FBT6 : ltac2:(tb__ "0|0|
S0S27S54S11S19S12S5VT6;A1A1A1S13S5VCO6;A1A1A3S28A3").
Hypothesis NXC6 : ltac2:(tb__ "0|0|
S0S27S6cVGS;S12S5VCO6;A1A1A2S28A3").
Hypothesis NXE6A : ltac2:(tb__ "0|0|
S0S27S6cVGS;S12S5VC5A;A1A1A2S28A3").
Hypothesis ECert6A : ltac2:(tb__ "0|3|
S0S27S5aS69Ufa0S2aS36S6fS2bS36A1A3VGS;S2aS57S58VC5A;Z1S16Z0M0A1M1A3S2bS57A1M2A3S2aS57S58VY6A;G0G1A3G2A3A6S28A3").

Theorem esec_g43_low : ltac2:(tb__ "0|5|
S3fS48SfS3dQ40M0A1M1S5dOF_;S6dVW;Vst;A2S6bVW;Vst;A2S49R6A1S36S1S5fS70S3cG0R6A2A1M2R1A2S62R1S60G2S61S6aS3cG0S14R7PcA2A2A1Z8A2A2A2A2S2S0S2eS3dQ8A1M3A1S17R8S3eG0R2A2A2S33G3A1A3A1F_;Fz;SfS29G1A1M4S5cVsegs;S38Vsegs;VJG;VBX;RbRaR9R8A5VD6;R2R1A5R7A3FtpY;FrhoY;SfG4S5cVsegs;S38Vsegs;VJG;VBX;RcRbRaR9A5VC5;R2R1A5R8A3FtX;FrX;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;").
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
S3fS3fF_;S6S6S29S11A1M0S0S27S18S5R2A1A1S28A3S0S2eS2cS29S2cS10S10A2M1A1M2G0A2M3A1S6eS5R4A1M4S5R3A1A2S31G3S2dG2G0S2bG1A1R2A4A2A3S0S37S12G4A1S12S5R5A1M5A1A3S0S6S7R6G5A2R5A3S53S11Sd3Vnx;A1M6S13S5R7A1A1A3S3fS48SfS3dQ40A1M7SfS29G7A1M8S29S74A1S73VJG;R11R8R7R6R5R4R3R2R1A9S1cR5G6A2S51S11S1cR6A1R10A3F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;S3fS48SfG7S5dOF_;SfG8S5cVsegs;S38Vsegs;VJG;R11R7R6R5R4A5RfR2R1A5R3A3FtY;FrY;SfG8S5cVsegs;S38Vsegs;VJG;R12R8R7R6R5A5R11R2R1A5R4A3FtX;FrX;F_;FQ;Fa;Frho;FKc;FA;F_;F_;F_;F_;F_;F_;FF;FD';FD;FBX;").
Proof.
  intros BX D D' F WD DD NXD HD FLOW FH A Kc rho a Q HC rX tX.
  apply (etc_pre (SPA segs (JG BX A Kc rho a) D' rX tX)); [intros w Hw; exact (hint_low nW st nx BX D D' F WD DD NXD HD FLOW FH A Kc rho a rX tX w Hw) | exact (HC rX tX)].
Qed.

Section G44E.
Variable BX : AA -> AA.
Hypothesis BXg : ltac2:(tb__ "0|0|
S3fS0S41S40VBX;R1A1A1S40R1A1A3FX;").
Variable PX : list sobj.
Variable FXP : list sprop.
Hypothesis PX_noband : ltac2:(tb__ "0|2|
S3fS48SfS3dQ40A1M0SfS29G0A1S29S74A1S73VJG;VBX;R8R7R6R5R4R3R2R1A9S51S11S1cR5A1VFXP;A3S29SeA1S0S29S2cS2cS10S10A2S10A2M1A1S50SeG1S5eR1A4S50SeG1S5eVPX;A4A3S51SeSeSb2S1eR9R1A2A1Lo;R2A3F_;Fl;F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;").
Variables (D6 U7 ET7 CT7 CO7 CR7 CS7 CM7 T7 : axst) (s7 : wsub) (R7 : list sobj) (n7 : nat).
Let D7 : axst := ltac2:(tb__ "0|0|
SaaVT7;S13S5VCM7;A1A1A2").
Hypothesis WU7 : ltac2:(tb__ "0|0|
S0S27S18S5VU7;A1A1S28A3").
Hypothesis DU7 : ltac2:(tb__ "0|4|
S0S2eS2cS29S2cS10S10A2M0A1M1S29S11A1M2A2M3A1S6eS5VD6;A1S5VU7;A1A2S31G3S2dG1G2S2bG0A1S8dVnx;A1A4A2A3").
Hypothesis NXU7 : ltac2:(tb__ "0|0|
S0S37S12S5VU7;A1A1S12S5VD6;A1A1A3").
Hypothesis HU7 : ltac2:(tb__ "0|0|
S0S6S7VD6;S5VU7;A1A2VU7;A3").
Hypothesis Cert7 : ltac2:(tb__ "0|1|
S0S27S59S69Ufa0S2aS36S6fS2bS36A1A3VGS;S2aS6VU7;S2bS6A1M0A3S2aS6VET7;G0A3A6S28A3").
Hypothesis WC7 : ltac2:(tb__ "0|0|
S0S27S18S5VCT7;A1A1S28A3").
Hypothesis DF7 : ltac2:(tb__ "0|4|
S0S2eS2cS29S2cS10S10A2M0A1M1S29S11A1M2A2M3A1S6eS5VET7;A1S5VCT7;A1A2S31G3S2dG1G2S2aG0S2dS10S10S93Vnx;A1S7aVnx;A1A4S2aG0S2dS10S10S94Vnx;A1S90A4S2bG0A1A3A3S2bS11A1A4A2A3").
Hypothesis NX7 : ltac2:(tb__ "0|0|
S0S37S12S5VCT7;A1A1S12S5VET7;A1A1A3").
Hypothesis HC7 : ltac2:(tb__ "0|0|
S0S6S7VET7;S5VCT7;A1A2VCT7;A3").
Hypothesis SK7 : ltac2:(tb__ "0|1|
S0S29S2cS2cS10S10A2S10A2M0A1S50SeG0S5eS1aS5VCT7;A1A1A4S50SeG0S5eS2fSeS2aSeS80Vnx;A1S2aSeS78Vnx;A1S2aSeS76Vnx;A1S2bSeA1A3A3A3S2fSeSb1VnW;Vnx;A2VPX;A3A3A4A3").
Hypothesis FC7 : ltac2:(tb__ "0|0|
S55S11S2fS11S4cVW;Vst;A2S4bS4aA1A3S13S5VCT7;A1A1A3").
Hypothesis FX7 : ltac2:(tb__ "0|0|
S55S11VFXP;S13S5VCT7;A1A1A3").
Hypothesis XC7 : ax_X CT7 = [].
Hypothesis HCO7 : ltac2:(tb__ "0|0|
S0S6S77VCT7;S20S7aVnx;A1S16Z0A1S16Z100A1S2bS15A1S1fA5A2VCO7;A3").
Hypothesis WCO7 : ltac2:(tb__ "0|0|
S0S27S18S5VCO7;A1A1S28A3").
Hypothesis RB7 : ltac2:(tb__ "0|0|
S0S27ScaS25Sd5S5VCO7;A1U1A2A2S28A3").
Hypothesis HCR7 : ltac2:(tb__ "0|0|
S0S6SccVCO7;U1A2VCR7;A3").
Hypothesis LEN7 : ltac2:(tb__ "0|0|
S0S30S32SeS1aS5VCR7;A1A1A2Vn7;A3").
Hypothesis PERM_nd7 : ltac2:(tb__ "0|0|
S0S27Sc0S85Vn7;A1A1S28A3").
Hypothesis PERM_lt7 : ltac2:(tb__ "0|0|
S0S27S54S30S30SbdR1Vn7;A2Li;S85Vn7;A1A3S28A3").
Hypothesis PERM_cov7 : ltac2:(tb__ "0|0|
S0S27S54S30S30S56S30SbcR1A1S85Vn7;A1A3Li;S52U0Vn7;A2A3S28A3").
Hypothesis HCS7 : ltac2:(tb__ "0|0|
S0S6Sa6VCR7;A1VCS7;A3").
Hypothesis MRG7 : ltac2:(tb__ "0|0|
S0S27ScaS25Sd4S5VCS7;A1U1A2A2S28A3").
Hypothesis HCM7 : ltac2:(tb__ "0|0|
S0S6ScbVCS7;U1A2VCM7;A3").
Hypothesis He7 : ltac2:(tb__ "0|1|
S0S2eS29SeA1M0A1SacVCM7;S71Vs7;A3S31G0VR7;A2A3").
Hypothesis Hchk7 : ltac2:(tb__ "0|0|
S0S27SabVCM7;S71Vs7;VR7;S50S8S6S9S72A4A5S28A3").
Hypothesis HT7 : ltac2:(tb__ "0|0|
S0S6SadVs7;S71S79VCM7;VR7;A5VT7;A3").
Hypothesis FBC7 : ltac2:(tb__ "0|1|
S0S27S54S11S19S12S5VCM7;A1M0A1A1S13G0A1A3S28A3").
Hypothesis FBT7 : ltac2:(tb__ "0|0|
S0S27S54S11S19S12S5VT7;A1A1A1S13S5VCM7;A1A1A3S28A3").
Hypothesis NXC7 : ltac2:(tb__ "0|0|
S0S27S6cVGS;S12S5VCM7;A1A1A2S28A3").
Hypothesis NXE7 : ltac2:(tb__ "0|0|
S0S27S6cVGS;S12S5VU7;A1A1A2S28A3").
Hypothesis ECert7 : ltac2:(tb__ "0|3|
S0S27S5aS69Ufa0S2aS36S6fS2bS36A1A3VGS;S2aS57S58VU7;Z1S16Z0M0A1M1A3S2bS57A1M2A3S2aS57S58VET7;G0G1A3G2A3A6S28A3").
Lemma RSU7' : ltac2:(tb__ "0|1|
S3fS48SfS3dQ40A1M0SfS29G0A1S5dS38Vsegs;VJG;VBX;R7R6R5R4A5VD6;R3R2R1A6S38Vsegs;VJG;VBX;R8R7R6R5A5VU7;R4R3R2A6F_;Fw;Ftp;FrhoX;Fa;Frho;FKc;FA;").
Proof. rr RSU7. Qed.
Lemma prep7' : ltac2:(tb__ "0|4|
S3fS48SfS3dQ40M0A1M1SfS29G1A1S5dS6dVW;Vst;A2S36S1S5fS70S3cG0R6A2A1M2R1A2S62R1S60G2S61S6aS3cG0S14R7PcA2A2A1Z8A2A2A2A2S2S0S2eS3dQ8A1M3A1S17R8S3eG0R2A2A2S33G3A1A3A1F_;Fz;S38Vsegs;VJG;VBX;R9R8R7R6A5VET7;R5R4R3A6S38Vsegs;VJG;VBX;RaR9R8R7A5VCM7;R6R5R4A6F_;F_;F_;Fw;Ftp;FrhoX;Fa;Frho;FKc;FA;").
Proof. rr prep7. Qed.

Theorem esec_g44 : ltac2:(tb__ "0|5|
S3fS48SfS3dQ40M0A1M1S5dOF_;S6dVW;Vst;A2S6bVW;Vst;A2S49R6A1S36S1S5fS70S3cG0R6A2A1M2R1A2S62R1S60G2S61S6aS3cG0S14R7PcA2A2A1Z8A2A2A2A2S2S0S2eS3dQ8A1M3A1S17R8S3eG0R2A2A2S33G3A1A3A1F_;Fz;SfS29G1A1M4S5cVsegs;S38Vsegs;VJG;VBX;RbRaR9R8A5VD7;R2R1A5R7A3FtpY;FrhoY;SfG4S5cVsegs;S38Vsegs;VJG;VBX;RcRbRaR9A5VD6;R2R1A5R8A3FtX;FrX;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;").
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
S3fS0S41S40VBX;R1A1A1S40R1A1A3FX;").
Variable PX : list sobj.
Variable FXP : list sprop.
Hypothesis PX_noband : ltac2:(tb__ "0|2|
S3fS48SfS3dQ40A1M0SfS29G0A1S29S74A1S73VJG;VBX;R8R7R6R5R4R3R2R1A9S51S11S1cR5A1VFXP;A3S29SeA1S0S29S2cS2cS10S10A2S10A2M1A1S50SeG1S5eR1A4S50SeG1S5eVPX;A4A3S51SeSeSb2S1eR9R1A2A1Lo;R2A3F_;Fl;F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;").
Variables (D7 U8 ET8 CT8 CO8 T8 : axst) (s8 : wsub) (R8 : list sobj).
Let D8 : axst := ltac2:(tb__ "0|0|
SaaVT8;S13S5VCO8;A1A1A2").
Hypothesis WU8 : ltac2:(tb__ "0|0|
S0S27S18S5VU8;A1A1S28A3").
Hypothesis DU8 : ltac2:(tb__ "0|4|
S0S2eS2cS29S2cS10S10A2M0A1M1S29S11A1M2A2M3A1S6eS5VD7;A1S5VU8;A1A2S31G3S2dG1G2S2bG0A1S8eVnx;A1A4A2A3").
Hypothesis NXU8 : ltac2:(tb__ "0|0|
S0S37S12S5VU8;A1A1S12S5VD7;A1A1A3").
Hypothesis HU8 : ltac2:(tb__ "0|0|
S0S6S7VD7;S5VU8;A1A2VU8;A3").
Hypothesis Cert8 : ltac2:(tb__ "0|1|
S0S27S59S69Ufa0S2aS36S6fS2bS36A1A3VGS;S2aS6VU8;S2bS6A1M0A3S2aS6VET8;G0A3A6S28A3").
Hypothesis WC8 : ltac2:(tb__ "0|0|
S0S27S18S5VCT8;A1A1S28A3").
Hypothesis DF8 : ltac2:(tb__ "0|4|
S0S2eS2cS29S2cS10S10A2M0A1M1S29S11A1M2A2M3A1S6eS5VET8;A1S5VCT8;A1A2S31G3S2dG1G2S2bG0A1S95Vnx;A1A4A2A3").
Hypothesis NX8 : ltac2:(tb__ "0|0|
S0S37S12S5VCT8;A1A1S12S5VET8;A1A1A3").
Hypothesis HC8 : ltac2:(tb__ "0|0|
S0S6S7VET8;S5VCT8;A1A2VCT8;A3").
Hypothesis SK8 : ltac2:(tb__ "0|1|
S0S29S2cS2cS10S10A2S10A2M0A1S50SeG0S5eS1aS5VCT8;A1A1A4S50SeG0S5eS2fSeS2aSeS84Vnx;A1S2aSeS80Vnx;A1S2aSeS76Vnx;A1S2bSeA1A3A3A3S2fSeSb1VnW;Vnx;A2VPX;A3A3A4A3").
Hypothesis FC8 : ltac2:(tb__ "0|0|
S55S11S2fS11S4cVW;Vst;A2S4bS4aA1A3S13S5VCT8;A1A1A3").
Hypothesis FX8 : ltac2:(tb__ "0|0|
S55S11VFXP;S13S5VCT8;A1A1A3").
Hypothesis XC8 : ax_X CT8 = [].
Hypothesis HCO8 : ltac2:(tb__ "0|0|
S0S6S77VCT8;S20S86Vnx;A1S16Z0A1S8aVnx;A1S2bS15A1S1fA5A2VCO8;A3").
Hypothesis WCO8 : ltac2:(tb__ "0|0|
S0S27S18S5VCO8;A1A1S28A3").
Hypothesis He8 : ltac2:(tb__ "0|1|
S0S2eS29SeA1M0A1SacVCO8;SbeVs8;A3S31G0VR8;A2A3").
Hypothesis Hchk8 : ltac2:(tb__ "0|0|
S0S27SabVCO8;SbeVs8;VR8;S50S8S6S9SbfA4A5S28A3").
Hypothesis HT8 : ltac2:(tb__ "0|0|
S0S6SadVs8;SbeS7bVCO8;VR8;A5VT8;A3").
Hypothesis FBC8 : ltac2:(tb__ "0|1|
S0S27S54S11S19S12S5VCO8;A1M0A1A1S13G0A1A3S28A3").
Hypothesis FBT8 : ltac2:(tb__ "0|0|
S0S27S54S11S19S12S5VT8;A1A1A1S13S5VCO8;A1A1A3S28A3").
Hypothesis NXC8 : ltac2:(tb__ "0|0|
S0S27S6cVGS;S12S5VCO8;A1A1A2S28A3").
Hypothesis NXE8 : ltac2:(tb__ "0|0|
S0S27S6cVGS;S12S5VU8;A1A1A2S28A3").
Hypothesis ECert8 : ltac2:(tb__ "0|3|
S0S27S5aS69Ufa0S2aS36S6fS2bS36A1A3VGS;S2aS57S58VU8;Z1S16Z0M0A1M1A3S2bS57A1M2A3S2aS57S58VET8;G0G1A3G2A3A6S28A3").
Lemma RSU8' : ltac2:(tb__ "0|1|
S3fS48SfS3dQ40A1M0SfS29G0A1S5dS38Vsegs;VJG;VBX;R7R6R5R4A5VD7;R3R2R1A6S38Vsegs;VJG;VBX;R8R7R6R5A5VU8;R4R3R2A6F_;Fw;Ftp;FrhoX;Fa;Frho;FKc;FA;").
Proof. rr RSU8. Qed.
Lemma RS8' : ltac2:(tb__ "0|1|
S3fS48SfS3dQ40A1M0SfS29G0A1S5dS6dVW;Vst;A2S38Vsegs;VJG;VBX;R8R7R6R5A5VET8;R4R3R2A6S38Vsegs;VJG;VBX;R9R8R7R6A5VCT8;R5R4R3A6F_;F_;Fw;Ftp;FrhoX;Fa;Frho;FKc;FA;").
Proof. rr RS8. Qed.
Lemma HBL8' : ltac2:(tb__ "0|c|
S3fS48SfS3dQ40M0A1M1SfS29G1A1S5dS38Vsegs;VJG;VBX;R7R6R5R4A5VCT8;R3R2R1A6S1S5fS70S3cG0R5A2A1M2S3cG0S1bR4S86Vnx;A1M3A2A2M4A2S1S5fS60G4S3cG0S1bR4S8aVnx;A1M5A2A2A2S60G2S61S6aS3cG0S14R6PcA2A2A1Z8A2A2A2S1S29SeA1M6S0S29S2cS2cS10S10A2S10A2M7A1M8S50SeG7S5eR1A4M9S50SeG7S5eS2aSeS84Vnx;A1S2aSeS80Vnx;A1S2aSeS76Vnx;A1S2bSeA1A3A3A3A4A3S51SeSeS24S1eR7R1A2S2dS36S36S3cG0S1bR7G3A2A2MaS60GaS3cG0S1bR7G5A2A2A2A4A2Lo;R2A3MbF_;Fl;G6S0G8G9S50SeG7S5eVPX;A4A3GbF_;Fl;A2A2A2F_;Fw;Ftp;FrhoX;Fa;Frho;FKc;FA;").
Proof. rr HBL8. Qed.

Theorem esec_g45 : ltac2:(tb__ "0|5|
S3fS48SfS3dQ40M0A1M1S5dOF_;S6dVW;Vst;A2S6bVW;Vst;A2S49R6A1S36S1S5fS70S3cG0R6A2A1M2R1A2S62R1S60G2S61S6aS3cG0S14R7PcA2A2A1Z8A2A2A2A2S2S0S2eS3dQ8A1M3A1S17R8S3eG0R2A2A2S33G3A1A3A1F_;Fz;SfS29G1A1M4S5cVsegs;S38Vsegs;VJG;VBX;RbRaR9R8A5VD8;R2R1A5R7A3FtpY;FrhoY;SfG4S5cVsegs;S38Vsegs;VJG;VBX;RcRbRaR9A5VD7;R2R1A5R8A3FtX;FrX;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;").
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
S3fS0S41S40VBX;R1A1A1S40R1A1A3FX;").
Variable PX : list sobj.
Variable FXP : list sprop.
Hypothesis PX_noband : ltac2:(tb__ "0|2|
S3fS48SfS3dQ40A1M0SfS29G0A1S29S74A1S73VJG;VBX;R8R7R6R5R4R3R2R1A9S51S11S1cR5A1VFXP;A3S29SeA1S0S29S2cS2cS10S10A2S10A2M1A1S50SeG1S5eR1A4S50SeG1S5eVPX;A4A3S51SeSeSb2S1eR9R1A2A1Lo;R2A3F_;Fl;F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;").
Variables (D8 U9 E9f E9p CO9p E9q : axst).
Hypothesis WU9 : ltac2:(tb__ "0|0|
S0S27S18S5VU9;A1A1S28A3").
Hypothesis DU9 : ltac2:(tb__ "0|4|
S0S2eS2cS29S2cS10S10A2M0A1M1S29S11A1M2A2M3A1S6eS5VD8;A1S5VU9;A1A2S31G3S2dG1G2S2bG0A1S8fVnx;A1A4A2A3").
Hypothesis NXU9 : ltac2:(tb__ "0|0|
S0S37S12S5VU9;A1A1S12S5VD8;A1A1A3").
Hypothesis HU9 : ltac2:(tb__ "0|0|
S0S6S7VD8;S5VU9;A1A2VU9;A3").
Hypothesis Cert9 : ltac2:(tb__ "0|1|
S0S27S59S69Ufa0S2aS36S7eS2aS36S87S2bS36A1A3A3VGS;S2aS6VU9;S2bS6A1M0A3S2aS6VE9f;S2aS6VE9p;G0A3A3A6S28A3").
Hypothesis SK9 : ltac2:(tb__ "0|1|
S0S29S2cS2cS10S10A2S10A2M0A1S50SeG0S5eS1aS5VE9p;A1A1A4S50SeG0S5eS2fSeS2aSeS91Vnx;A1S2aSeS84Vnx;A1S2aSeS80Vnx;A1S2aSeS76Vnx;A1S2bSeA1A3A3A3A3S2fSeSb1VnW;Vnx;A2VPX;A3A3A4A3").
Hypothesis FC9 : ltac2:(tb__ "0|0|
S55S11S2fS11S4cVW;Vst;A2S4bS4aA1A3S13S5VE9p;A1A1A3").
Hypothesis FX9 : ltac2:(tb__ "0|0|
S55S11VFXP;S13S5VE9p;A1A1A3").
Hypothesis FP9 : ltac2:(tb__ "0|0|
S53S11S21S83A1S13S5VE9p;A1A1A3").
Hypothesis XC9 : ax_X E9p = [].
Hypothesis HCO9 : ltac2:(tb__ "0|0|
S0S6S77VE9p;S20S8cVnx;A1S16Z0A1S16Z1A1S2bS15A1S1fA5A2VCO9p;A3").
Hypothesis WCO9 : ltac2:(tb__ "0|0|
S0S27S18S5VCO9p;A1A1S28A3").
Hypothesis Cert9q : ltac2:(tb__ "0|1|
S0S27S59S69Ufa0S2aS36S7eS2bS36A1A3VGS;S2aS6VCO9p;S2bS6A1M0A3S2aS6VE9q;G0A3A6S28A3").
Hypothesis NXE9 : ltac2:(tb__ "0|0|
S0S27S6cVGS;S12S5VU9;A1A1A2S28A3").
Hypothesis ECert9 : ltac2:(tb__ "0|3|
S0S27S5aS69Ufa0S2aS36S7eS2aS36S87S2bS36A1A3A3VGS;S2aS57S58VU9;Z1S16Z0M0A1M1A3S2bS57A1M2A3S2aS57S58VE9f;G0G1A3S2aS57S58VE9p;G0G1A3G2A3A3A6S28A3").
Hypothesis NXE9q : ltac2:(tb__ "0|0|
S0S27S6cVGS;S12S5VCO9p;A1A1A2S28A3").
Hypothesis ECert9q : ltac2:(tb__ "0|3|
S0S27S5aS69Ufa0S2aS36S7eS2bS36A1A3VGS;S2aS57S58VCO9p;Z1S16Z0M0A1M1A3S2bS57A1M2A3S2aS57S58VE9q;G0G1A3G2A3A6S28A3").
Lemma RSU9' : ltac2:(tb__ "0|1|
S3fS48SfS3dQ40A1M0SfS29G0A1S5dS38Vsegs;VJG;VBX;R7R6R5R4A5VD8;R3R2R1A6S38Vsegs;VJG;VBX;R8R7R6R5A5VU9;R4R3R2A6F_;Fw;Ftp;FrhoX;Fa;Frho;FKc;FA;").
Proof. rr RSU9. Qed.
Lemma prep9' : ltac2:(tb__ "0|4|
S3fS48SfS3dQ40M0A1M1SfS29G1A1S5dS6dVW;Vst;A2S36S1S5fS70S3cG0R6A2A1M2R1A2S62R1S60G2S61S6aS3cG0S14R7PcA2A2A1Z8A2A2A2A2S2S0S2eS3dQ8A1M3A1S17R8S3eG0R2A2A2S33G3A1A3A1F_;Fz;S38Vsegs;VJG;VBX;R9R8R7R6A5VE9p;R5R4R3A6S38Vsegs;VJG;VBX;RaR9R8R7A5VCO9p;R6R5R4A6F_;F_;F_;Fw;Ftp;FrhoX;Fa;Frho;FKc;FA;").
Proof. rr prep9. Qed.

Theorem esec_g46 : ltac2:(tb__ "0|5|
S3fS48SfS3dQ40M0A1M1S5dOF_;S6dVW;Vst;A2S6bVW;Vst;A2S49R6A1S36S1S5fS70S3cG0R6A2A1M2R1A2S62R1S60G2S61S6aS3cG0S14R7PcA2A2A1Z8A2A2A2A2S2S0S2eS3dQ8A1M3A1S17R8S3eG0R2A2A2S33G3A1A3A1F_;Fz;SfS29G1A1M4S5cVsegs;S38Vsegs;VJG;VBX;RbRaR9R8A5VE9f;R2R1A5R7A3FtpY;FrhoY;SfG4S5cVsegs;S38Vsegs;VJG;VBX;RcRbRaR9A5VE9q;R2R1A5R8A3FtpY;FrhoY;SfG4S5cVsegs;S38Vsegs;VJG;VBX;RdRcRbRaA5VD8;R2R1A5R9A3FtX;FrX;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;").
Proof.
  assert (USED := (BXg, PX_noband, WU9, DU9, NXU9, HU9, Cert9, SK9, FC9, FX9, FP9, XC9, HCO9, WCO9, Cert9q, NXE9, ECert9, NXE9q, ECert9q)); clear USED.
  intros A Kc rho a Q HW HUS HKc RUNDEF HCF HCQ rX tX.
  pose proof (JGs_stable nW st tmax nx Hnx NXG BX A Kc rho a HUS HKc) as HST.
  apply (etc_pre (SPA segs (JG BX A Kc rho a) U9 rX tX)); [intros w Hw; exact (RSU9' A Kc rho a rX tX w Hw)|].
  apply (ecfg_2 nx [CPC; PGST] U9 E9f E9p (JG BX A Kc rho a) Q tX rX HST NXE9 ECert9); intros rE.
  - exact (HCF rE tX).
  - apply (etc_pre (SPA segs (JG BX A Kc rho a) CO9p rE tX)); [intros w Hw; exact (prep9' A Kc rho a rE tX w HW RUNDEF Hw)|].
    apply (ecfg_1 nx [CPC] CO9p E9q (JG BX A Kc rho a) Q tX rE HST NXE9q ECert9q). intros rE'. exact (HCQ rE' tX).
Qed.
End G46E.

Section G47E.
Variable BX : AA -> AA.
Variables (E S9a S9b D9 : axst) (iM : nat) (perm : list nat).
Hypothesis HS9a : ltac2:(tb__ "0|0|
S0S6S8bVE;ViM;S16Z1800A1A3VS9a;A3").
Hypothesis HS9b : ltac2:(tb__ "0|0|
S0S6S8bVS9a;S35ViM;A1S16Z2800A1A3VS9b;A3").
Hypothesis HD9 : ltac2:(tb__ "0|1|
S0S6S7VS9b;Sc5S5VS9b;A1M0Sc1S1aG0A1Vperm;A2A2A2VD9;A3").
Hypothesis NDp : nodupN perm = true.
Hypothesis BNDp : ltac2:(tb__ "0|0|
S0S27S54S30S30SbdR1S32SeS1aS5VS9b;A1A1A2A2Li;Vperm;A3S28A3").
Hypothesis COVp : ltac2:(tb__ "0|0|
S0S27S54S30S30S56S30SbcR1A1Vperm;A3Li;S52U0S32SeS1aS5VS9b;A1A1A2A2A3S28A3").
Lemma prepD' : ltac2:(tb__ "0|1|
S3fS48SfS3dQ40A1M0SfS29G0A1S5dS38Vsegs;VJG;VBX;R7R6R5R4A5VE;R3R2R1A6S38Vsegs;VJG;VBX;R8R7R6R5A5VD9;R4R3R2A6F_;Fw;Ftp;FrhoX;Fa;Frho;FKc;FA;").
Proof. rr prepD. Qed.
Theorem esec_g47 : ltac2:(tb__ "0|2|
S3fS48SfS3dQ40A1M0S5dOF_;SfS29G0A1M1S5cVsegs;S38Vsegs;VJG;VBX;R7R6R5R4A5VD9;R2R1A5R3A3FtpY;FrhoY;SfG1S5cVsegs;S38Vsegs;VJG;VBX;R8R7R6R5A5VE;R2R1A5R4A3FtX;FrX;F_;FQ;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a Q HCONT rX tX.
  apply (etc_pre (SPA segs (JG BX A Kc rho a) D9 rX tX)); [|exact (HCONT rX tX)].
  intros w Hw. exact (prepD' A Kc rho a rX tX w Hw).
Qed.
Section DIAMONDE.
Hypothesis BXg : ltac2:(tb__ "0|0|
S3fS0S41S40VBX;R1A1A1S40R1A1A3FX;").
Variables D9A D9B : axst.
Hypothesis HD9A : ltac2:(tb__ "0|0|
S0S6S5bS7cVnx;A1VD9;A2VD9A;A3").
Hypothesis HD9B : ltac2:(tb__ "0|0|
S0S6S5bS7fVnx;A1VD9;A2VD9B;A3").
Hypothesis FBA9 : ltac2:(tb__ "0|0|
S0S27S54S11S19S12S5VD9;A1A1A1S7cVnx;A1A3S28A3").
Hypothesis FBB9 : ltac2:(tb__ "0|0|
S0S27S54S11S19S12S5VD9;A1A1A1S7fVnx;A1A3S28A3").
Theorem esec_g47d : ltac2:(tb__ "0|2|
S3fS48SfS3dQ40A1M0S5dOF_;SfS29G0A1M1S5cVsegs;S38Vsegs;VJG;VBX;R7R6R5R4A5VD9A;R2R1A5R3A3FtpY;FrhoY;SfG1S5cVsegs;S38Vsegs;VJG;VBX;R8R7R6R5A5VD9B;R2R1A5R4A3FtpY;FrhoY;SfG1S5cVsegs;S38Vsegs;VJG;VBX;R9R8R7R6A5VE;R2R1A5R5A3FtX;FrX;F_;F_;FQ;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a Q HCA HCB rX tX w Hw0.
  pose proof (prepD' A Kc rho a rX tX w Hw0) as Hw. destruct w as [tr [ms md]].
  destruct (diamond_hold nW st tmax nx Hnx BX A Kc rho a rX tX tr md BXg (proj2 Hw)) as [FA|FB].
  - apply (HCA rX tX). rewrite <- HD9A. split; [|exact (proj2 Hw)]. exact (smatchA_add_facts segs rX tX (F_A nx) _ _ (proj1 Hw) FA FBA9).
  - apply (HCB rX tX). rewrite <- HD9B. split; [|exact (proj2 Hw)]. exact (smatchA_add_facts segs rX tX (F_B nx) _ _ (proj1 Hw) FB FBB9).
Qed.
End DIAMONDE.
End G47E.
End SEC6E.

Section SEC7E.
Variable nW : nat. Variable st : ustop. Variable tmax : Z.
Let W : list ulink := Wcan nW.
Let segs : list Segment := segsA.
Variable nx : positive.
Hypothesis Hnx : ltac2:(tb__ "0|0|
S0S37ScfVW;Vst;Vtmax;A3Vnx;A3").
Hypothesis NXG : ltac2:(tb__ "0|0|
S0S27S6cSd2Vnx;A2S28A3").
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTM : ltac2:(tb__ "0|0|
S36Sb6VCST;R1A2Sb6Sd7R2A2S3F_;F_;Fa;").
Hypothesis HCSTS : ltac2:(tb__ "0|0|
S36Sb6VCST;R1A2Sb6Sd8R2A2S3F_;F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let JG (BX : AA -> AA) : AA -> KcA -> valuation -> word -> jpredA := ltac2:(tb__ "0|0|
Sb3VnW;Vst;Vnx;VBX;A4").
Section FINE.
Variable BX : AA -> AA.
Hypothesis BXok : bx_ok BX.
Variables (blk : Z) (dpx : odefault) (NRESe : sv) (FXP : list sprop).
Hypothesis Hdpx : ltac2:(tb__ "0|0|
S4S0S23Vdpx;S1fA3S0S23Vdpx;S26A3A2").
Hypothesis HPATH : ltac2:(tb__ "0|4|
S3fS48SfS3dQ40M0A1M1SfS29G1A1S29S74A1S73VJG;VBX;R8R7R6R5R4R3R2R1A9S51S11S1cR5A1VFXP;A3VBX;Sb0RaS3cG0S14R8PcA2A2A2A1S3fS1S1S5fZ8M2Vblk;A2S5fVblk;Z20000A2A2S1S5fS60S68G2S63S32S43S42RbA1A2A1A2Vblk;A2S47R1A1M3A2S0G1S1bR7VNRESe;A2S3eG0S61G3G2A2A2A3A2A2TAs;F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;").
Variable partial : bool.
Variable F : axst.
Variables swc c1 c2 c4 c5 mc xc : list cell.
Variable tyb : Z.
Let K : list sobj := KEPTF W swc.
Let RS : list sobj := ltac2:(tb__ "0|0|
S92Vnx;Vc1;Vc2;Vc4;Vc5;Vmc;Vxc;Vblk;Vdpx;Vpartial;Aa").
Let R : list sobj := RT_m1 ++ RS.
Hypothesis SELF : ltac2:(tb__ "0|0|
S0S29SeA1Sc1S1aS5VF;A1A1Sb7VnW;Vpartial;A2A2S2fSeVK;VR;A3A3").
Hypothesis NDF : ltac2:(tb__ "0|0|
S0S27Sc0Sb7VnW;Vpartial;A2A1S28A3").
Hypothesis BNDF : ltac2:(tb__ "0|0|
S0S27S54S30S30SbdR1S32SeS1aS5VF;A1A1A2A2Li;Sb7VnW;Vpartial;A2A3S28A3").
Hypothesis COVF : ltac2:(tb__ "0|0|
S0S27S54S30S30S56S30SbcR1A1Sb7VnW;Vpartial;A2A3Li;S52U0S32SeS1aS5VF;A1A1A2A2A3S28A3").
Hypothesis XFn : ax_X F = [].
Hypothesis BFb : ltac2:(tb__ "0|0|
S0S10SbVF;A1S4fA3").
Hypothesis FPF : ltac2:(tb__ "0|0|
S55S11S2fS11S4cVW;Vst;A2S4bS4aA1A3S13S5VF;A1A1A3").
Hypothesis FXF : ltac2:(tb__ "0|0|
S55S11VFXP;S13S5VF;A1A1A3").
Hypothesis FPAR : ltac2:(tb__ "0|0|
S53S11S27S11Lpartial;Vpartial;S21S83A1S83X27x2S13S5VF;A1A1A3").
Hypothesis Hc1 : ltac2:(tb__ "0|0|
S1S53S15S9aVc1;A3S1S53S15S96Vc1;A3S1S53S15S97Vc1;A3S1S53S15S9bVc1;A3S1S53S15S99VNRESe;A1Vc1;A3S53S15S98Vc1;A3A2A2A2A2A2").
Hypothesis Hmc : ltac2:(tb__ "0|0|
S1S53S15S9fVnx;A1Vmc;A3S1S53S15Sa0Vmc;A3S1S53S15Sa1Vmc;A3S1S53S15S9dVmc;A3S1S53S15S9eVmc;A3S1S53S15S9cVnx;A1Vmc;A3S1S53S15Sa4Vmc;A3S1S53S15Sa5Vtyb;A1Vmc;A3S1S53S15Sa3Vmc;A3S53S15Sa2Vmc;A3A2A2A2A2A2A2A2A2A2").
Hypothesis Htyb : ltac2:(tb__ "0|0|
S0S27S34S34S65Z0Vtyb;A2S66Vtyb;Z100A2A2S64S67Vtyb;Z4A2Z1A2A2S28A3").
Hypothesis Hxc : ltac2:(tb__ "0|0|
S53S15Sa7Vnx;A1Vxc;A3").
Let KU : list sobj := ltac2:(tb__ "0|0|
SbaVW;Vswc;Vnx;A3").
Hypothesis WCU : ltac2:(tb__ "0|0|
S0S27S18Sc5S5VF;A1S2fSeVK;S2aSeS81Vnx;A1S2bSeA1A3A3A2A1S28A3").
Hypothesis SELU : ltac2:(tb__ "0|0|
S0S29SeA1Sc1S2fSeVK;S2aSeS81Vnx;A1S2bSeA1A3A3Sb8VnW;A1A2VKU;A3").
Hypothesis NDU : ltac2:(tb__ "0|0|
S0S27Sc0Sb8VnW;A1A1S28A3").
Hypothesis BNDU : ltac2:(tb__ "0|0|
S0S27S54S30S30SbdR1S32SeS2fSeVK;S2aSeS81Vnx;A1S2bSeA1A3A3A2A2Li;Sb8VnW;A1A3S28A3").
Hypothesis COVU : ltac2:(tb__ "0|0|
S0S27S54S30S30S56S30SbcR1A1Sb8VnW;A1A3Li;S52U0S32SeS2fSeVK;S2aSeS81Vnx;A1S2bSeA1A3A3A2A2A3S28A3").
Hypothesis W9 : ltac2:(tb__ "0|0|
S0S27S18Sb9VF;VKU;A2A1S28A3").
Hypothesis D9 : ltac2:(tb__ "0|4|
S0S2eS2cS29S2cS10S10A2M0A1M1S29S11A1M2A2M3A1S6eSc5S5VF;A1VKU;A2Sb9VF;VKU;A2A2S31G3S2dG1G2S2aG0S2dS10S10S16Sd6A1S22P18A1A4S2bG0A1A3S2bS11A1A4A2A3").
Hypothesis XB9 : ltac2:(tb__ "0|0|
S0S27SdS12S5VF;A1A1S2dS10S10S88Vnx;A1S22PcA1A4A2S28A3").
Variable s9 : wsub.
Hypothesis ENT9 : ltac2:(tb__ "0|0|
S0S27SaSbbVF;VKU;Vnx;A3Sc7VW;Vst;A2Vs9;A3S28A3").
Hypothesis SID9 : wsub_idc s9 = true.
Hypothesis G110 : ltac2:(tb__ "0|0|
S0S10Sc4Vs9;S4eA2S88Vnx;A1A3").
Variable DF9 : axst.
Hypothesis CertF : ltac2:(tb__ "0|1|
S0S27S59S69Ufa0S2bS36A1Sb4Vnx;A1S2aS6VDF9;S2bS6A1M0A3S2aS6VF;G0A3A6S28A3").
Let GS : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineCallocSec3.GS nx.
Hypothesis NXEF : ltac2:(tb__ "0|0|
S0S27S6cVGS;S12S5VDF9;A1A1A2S28A3").
Hypothesis ECertF : ltac2:(tb__ "0|3|
S0S27S5aS69Ufa0S2bS36A1VGS;S2aS57S58VDF9;Z1S16Z0M0A1M1A3S2bS57A1M2A3S2aS57S58VF;G0G1A3G2A3A6S28A3").
Lemma sec_finish'_P : ltac2:(tb__ "0|6|
S3fS48SfSfS3dQ40M0A1M1SfS29G1A1M2G2S5dS29S2cS6SafA2M3A1S53G3S2dS6SafSc7VW;Vst;A2Sc8VCST;VXGL;RaR9A4A4R1A3S6dVW;Vst;A2S49RbA1S37S0G1S14RbR1A2S14RcR1A2A3Fi;S37S0S29S3dQ8A1A1S1dRcR1A2S1dRdR1A2A3Fl;S4dVCST;VXGL;RfRfS17RdA1S17RcA1A6S5fS63S32S43S42R10A1A2A1S44R10A1A2S2cS36S36A2M4S53G4R1Sa9S45VBX;Sb0R12S3cG0S14RfPcM5A2A2A2A1A1A1A3Sa8R2S2dS36S36S3cG0RfA2S6aS3cG0S14R10G5A2A2A1A4A2F_;Fbn;S38Vsegs;VJG;VBX;R12R11RfReA5VF;RdRbRaA6SaeVsegs;S75R11RdRaRbA6F_;F_;F_;F_;F_;F_;F_;F_;F_;FPosts;Fw;Ftp;Ftp0;FrhoE;Fa;Frho;Frho0;FKc;FA;").
Proof. rr sec_finish_P. Qed.
Lemma sec_finish' : ltac2:(tb__ "0|5|
S3fS48SfSfS3dQ40M0A1M1SfS29G1A1M2G2S5dS6dVW;Vst;A2S49R9A1S37S0G1S14R9R1A2S14RaR1A2A3Fi;S37S0S29S3dQ8A1A1S1dRaR1A2S1dRbR1A2A3Fl;S4dVCST;VXGL;RdRdS17RbA1S17RaA1A6S5fS63S32S43S42ReA1A2A1S44ReA1A2S2cS36S36A2M3S53G3R1Sa9S45VBX;Sb0R10S3cG0S14RdPcM4A2A2A2A1A1A1A3Sa8R2S2dS36S36S3cG0RdA2S6aS3cG0S14ReG4A2A2A1A4A2F_;Fbn;S38Vsegs;VJG;VBX;R10RfRdRcA5VF;RbR9R8A6SaeVsegs;S75RfRbSc9VCST;VXGL;VW;Vst;R11R10A6R9A6F_;F_;F_;F_;F_;F_;F_;F_;Fw;Ftp;Ftp0;FrhoE;Fa;Frho;Frho0;FKc;FA;").
Proof. intros A Kc rho0 rho a rhoE tp0 tp w. apply sec_finish'_P. unfold PFc. right. left. reflexivity. Qed.

Theorem esec_g48_P : ltac2:(tb__ "0|6|
S3fS48SfSfS3dQ40M0A1M1S29G1A1M2S29S2cS6SafA2M3A1S53G3S2dS6SafSc7VW;Vst;A2Sc8VCST;VXGL;R7R6A4A4R1A3S6dVW;Vst;A2S6bVW;Vst;A2S49R9A1S37S0G1S14R9R1A2S14RaR1A2A3Fi;S37S0S29S3dQ8A1A1S1dRaR1A2S1dRbR1A2A3Fl;S4dVCST;VXGL;RdRdS17RbA1S17RaA1A6S5fS63S32S43S42ReA1A2A1S44ReA1A2S2cS36S36A2M4S53G4R1Sa9S45VBX;Sb0R10S3cG0S14RdPcM5A2A2A2A1A1A1A3Sa8R2S2dS36S36S3cG0RdA2S6aS3cG0S14ReG5A2A2A1A4A2F_;Fbn;SfG2S5cVsegs;S38Vsegs;VJG;VBX;R12R11RfReA5VDF9;R2R1A5SaeVsegs;S75R10RdRcA5A3FtpX;FrhoX;F_;F_;F_;F_;F_;F_;F_;F_;F_;FPosts;Ftp0;Fa;Frho;Frho0;FKc;FA;").
Proof.
  assert (USED := (BXok, Hdpx, HPATH, SELF, NDF, BNDF, COVF, XFn, BFb, FPF, FXF, FPAR, Hc1, Hmc, Htyb, Hxc, WCU, SELU, NDU, BNDU, COVU, W9, D9, XB9, ENT9, SID9, G110, CertF, NXEF, ECertF)); clear USED.
  intros A Kc rho0 rho a tp0 Posts HPin HW HUS HKc HLw HLl HKEPT0 HL9 HDB rhoX tpX.
  pose proof (JGs_stable nW st tmax nx Hnx NXG BX A Kc rho a HUS HKc) as HST.
  apply (ecfg_1 nx [] DF9 F (JG BX A Kc rho a) _ tpX rhoX HST NXEF ECertF). intros rE.
  intros w Hw. exists w. split; [apply wsteps_refl|].
  exact (sec_finish'_P A Kc rho0 rho a rE tp0 tpX w Posts HPin HW HKc HLw HLl HKEPT0 HL9 HDB Hw).
Qed.
Theorem esec_g48 : ltac2:(tb__ "0|5|
S3fS48SfSfS3dQ40M0A1M1S29G1A1M2S6dVW;Vst;A2S6bVW;Vst;A2S49R7A1S37S0G1S14R7R1A2S14R8R1A2A3Fi;S37S0S29S3dQ8A1A1S1dR8R1A2S1dR9R1A2A3Fl;S4dVCST;VXGL;RbRbS17R9A1S17R8A1A6S5fS63S32S43S42RcA1A2A1S44RcA1A2S2cS36S36A2M3S53G3R1Sa9S45VBX;Sb0ReS3cG0S14RbPcM4A2A2A2A1A1A1A3Sa8R2S2dS36S36S3cG0RbA2S6aS3cG0S14RcG4A2A2A1A4A2F_;Fbn;SfG2S5cVsegs;S38Vsegs;VJG;VBX;R10RfRdRcA5VDF9;R2R1A5SaeVsegs;S75ReRbSc9VCST;VXGL;VW;Vst;R10RfA6A5A3FtpX;FrhoX;F_;F_;F_;F_;F_;F_;F_;F_;Ftp0;Fa;Frho;Frho0;FKc;FA;").
Proof.
  intros A Kc rho0 rho a tp0. apply esec_g48_P. unfold PFc. right. left. reflexivity.
Qed.
End FINE.
End SEC7E.
End SpineCallocSecE3.

(* [comment removed for export] *)
Module SpineMallocSecOK0.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecI"; "st0"; "W0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "liftKA"; "SPA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@Corelib.Init.Datatypes"; "list"; "false"; "prod"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "AE_A"; "KcA"; "Kc_ok"; "Posts_malloc"; "@Corelib.Init.Logic"; "False"; "eq"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.CertMallocSS"; "ES1g"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "secmapsize"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3"; "JGsC"; "clsP"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "segments_reserved"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "m_vmmaps"; "vm_reserved"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1"; "E_s1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM"; "IMG_M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "dfp_static"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1"; "JG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec2"; "IMG_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3I"; "nx0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3IL"; "nx0"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA MmapA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts StartLib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RebuildM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require MmapSymA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ae.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocSec SpineMallocSec2 SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bt.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require q0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bw.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocSec4I.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ca.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cm.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocSec4IL.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cg.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.RebuildN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.MmapSymA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.CertMallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.CertMallocSN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.InvD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.SecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.SecRoom OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineMallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bp.DepotCallS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bw.SecLinks OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c0.SpineMallocSecOK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3I OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec4I OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ca.SpineMallocSec5I OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cc.SpineMallocSec5J OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cm.SpineMallocSec6J OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3IL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec4IL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ca.SpineMallocSec5IL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cg.SpineMallocSec5JL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cm.SpineMallocSec6JL.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section OK0.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTM : ltac2:(tb__ "0|0|
S10SdVCST;R1A2SdS27R2A2S1aF_;F_;Fa;").
Hypothesis HCSTS : ltac2:(tb__ "0|0|
S10SdVCST;R1A2SdS2aR2A2S1aF_;F_;Fa;").
Hypothesis HCSTD : ltac2:(tb__ "0|0|
S10SdVCST;R1A2S1cS28R2A1A1F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Hypothesis law_res : ltac2:(tb__ "0|1|
S8S3S9SeQ40A1M0A1S23VAInv;R4R3R2R1A4S1bS9SbG0G0A2A1S25S24R2A1A1S22S0A1A3F_;Fmd;Ftp;Frho;FA;").

Theorem sec_ok_0h : ltac2:(tb__ "0|2|
S12OF_;S8S17S3SeQ40M0A1M1S9G1A1S18R4A1S7S0R7S5R5A1A3S15S0R8S5R6A1A3S21ScSfG0R5A2S1fSfG0S4R6PcA2A2A1A3S3S11S0RbS6S0S20U0S1S2bS8R1LX;RaR9R8R7A8S1dS2S1Z2A3R1R6A5S14S0S13R8R6S19S16S1eS0A1VCST;VXGL;S2S1RaR9A8A5A4FrhoX;F_;F_;F_;F_;Ftp;Fa;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho a tp HKc Hokl Hokpl HC rhoX.
  exact (sec_ok_chain 0%nat st0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3I.nx0 true CST XGL HCST HXGL HCSTS HCSTD (ES1g W0 st0 2)
           OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3I.D2c SpineMallocSec4I.T4ac SpineMallocSec4I.T4bc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ca.SpineMallocSec5I.C5ac OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ca.SpineMallocSec5I.C5bc
           sec_g12_0h sec_g3_0h sec_g41_0ha sec_g41_0hb (sec_tail_0ha CST XGL HCST HXGL HCSTM HCSTS) (sec_tail_0hb CST XGL HCST HXGL HCSTM HCSTS)
           ok A Kc rho a tp ltac:(intros E; discriminate E) (stopJ_stable_le _) HKc Hokl Hokpl HC rhoX).
Qed.

Theorem sec_ok_0l : ltac2:(tb__ "0|2|
S12OF_;S8S17S3SeQ40M0A1M1S9G1A1S18R4A1S7S0R7S5R5A1A3S15S0R8S5R6A1A3S21SaSfG0R5A2S1fSfG0S4R6PcA2A2A1A3S3S11S0RbS6S0S20U0S1S2cS8R1LX;RaR9R8R7A8S1dS2S1Z2A3R1R6A5S14S0S13R8R6S19S16S1eS0A1VCST;VXGL;S2S1RaR9A8A5A4FrhoX;F_;F_;F_;F_;Ftp;Fa;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho a tp HKc Hokl Hokpl HC rhoX.
  exact (sec_ok_chain 0%nat st0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3IL.nx0 false CST XGL HCST HXGL HCSTS HCSTD (ES1g W0 st0 2)
           OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3IL.D2c SpineMallocSec4IL.T4ac SpineMallocSec4IL.T4bc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ca.SpineMallocSec5IL.C5ac OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ca.SpineMallocSec5IL.C5bc
           sec_g12_0l sec_g3_0l sec_g41_0la sec_g41_0lb (sec_tail_0la CST XGL HCST HXGL HCSTM HCSTS) (sec_tail_0lb CST XGL HCST HXGL HCSTM HCSTS)
           ok A Kc rho a tp ltac:(intros E; discriminate E) (stopJ_stable_le _) HKc Hokl Hokpl HC rhoX).
Qed.

Theorem malloc_sec_ok_0 : ltac2:(tb__ "0|0|
S12OF_;S8S17S3S9SeQ40A1A1S18R3A1S7Vsegs;R6S5R4A1A3S15Vsegs;R7S5R5A1A3S3S11Vsegs;R9S6Vsegs;S29S2S1R8R7R6A5S26S2S1Z2Z8A4R1R5A5S14Vsegs;S13R6R5S19S16VAInv;VCST;VXGL;S2S1R8R7A8A5A4FrhoE;F_;F_;F_;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp HKc Hokl Hokpl rhoE.
  apply (malloc_sec_0 CST XGL HCST HXGL HCSTM HCSTS law_res ok A Kc
           (fun a => OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3.JGsC 0%nat st0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3I.nx0 (fun X : AA => X) A Kc rho a) rho tp HKc Hokl Hokpl).
  - intros rhoX tr ms md a Hsp HJG Hpl. rewrite OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecI.NX1_0.
    exact (grant_Jo 0%nat st0 2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3I.nx0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3I.Hnx_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3I.NXG_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecI.R11_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecI.FC1_0 A Kc rho rhoX tp tr ms md a (stopJ_stable_le _) HKc Hsp HJG Hpl).
  - intros rhoX a. change (nxS W0 st0 2) with (nxS (Wcan 0) UStopLe 2). rewrite OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3I.Hnx_0.
    apply (cls_split 0%nat st0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3I.nx0 ok A Kc rho a (ES1g W0 st0 2) _ tp).
    + intros HC. exact (sec_ok_0h ok A Kc rho a tp HKc Hokl Hokpl HC _).
    + intros HC. exact (sec_ok_0l ok A Kc rho a tp HKc Hokl Hokpl HC _).
Qed.
End OK0.
End SpineMallocSecOK0.

(* [comment removed for export] *)
Module SpineMallocSec6IEL.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_ecfgA"; "@Corelib.Init.Datatypes"; "cons"; "bool"; "nil"; "true"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "ss_next"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP"; "MSENT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.CertMallocSV"; "PGST"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cg.SpineMallocSec6IL"; "C5Aa"; "C5Ab"; "CO9pa"; "CO9pb"; "D9fa"; "D9fb"; "D9qa"; "D9qb"; "U7a"; "U7b"; "U8a"; "U8b"; "U9a"; "U9b"; "E9fa"; "E9fb"; "E9pa"; "E9pb"; "E9qa"; "E9qb"; "ET7a"; "ET7b"; "ET8a"; "ET8b"; "FFfa"; "FFfb"; "FFqa"; "FFqb"; "Y6Aa"; "Y6Ab"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fi.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ao.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocS9 SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bt.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require q0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocSec4IL.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bw.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ca.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cg.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.CertMallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ao.SpineMallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_refl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.SecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3IL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineMallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec4IL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.CertMallocSU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bw.SpineMallocSec5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bp.DepotCallS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.CertMallocSV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c0.SpineMallocSec6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c4.SpineMallocSec6L OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ca.SpineMallocSec5IL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c4.SpineMallocSec7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cg.SpineMallocSec6IL.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 0. Let st : ustop := UStopLe. Let tmax : Z := 2.
Let GS0 : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3.GS nx0.

Lemma NXE6Aa_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS10A1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert6Aa_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S3S8SeS5S8A1A3VGS0;S3S0S1S10Z1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S2cG0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [MSENT] GS0 [mkVNA C5Aa 1 (SLit 0)] [mkVNA Y6Aa 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cg.SpineMallocSec6IL.run6Aa]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cg.SpineMallocSec6IL.run6Aa__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXE7a_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS18A1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert7a_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S3S8SeS5S8A1A3VGS0;S3S0S1S18Z1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S24G0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [MSENT] GS0 [mkVNA U7a 1 (SLit 0)] [mkVNA ET7a 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cg.SpineMallocSec6IL.run7a]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cg.SpineMallocSec6IL.run7a__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXE8a_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS1aA1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert8a_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S3S8SeS5S8A1A3VGS0;S3S0S1S1aZ1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S26G0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [MSENT] GS0 [mkVNA U8a 1 (SLit 0)] [mkVNA ET8a 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cg.SpineMallocSec6IL.run8a]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cg.SpineMallocSec6IL.run8a__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXE9a_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS1cA1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert9a_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S3S8SeS3S8SfS5S8A1A3A3VGS0;S3S0S1S1cZ1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S1eG0G1A3S3S0S1S20G0G1A3G2A3A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [MSENT; PGST] GS0 [mkVNA U9a 1 (SLit 0)] [mkVNA E9fa 0 (SLit 0); mkVNA E9pa 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cg.SpineMallocSec6IL.run9a]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cg.SpineMallocSec6IL.run9a__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXE9qa_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS12A1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert9qa_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S3S8SeS5S8A1A3VGS0;S3S0S1S12Z1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S22G0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [MSENT] GS0 [mkVNA CO9pa 1 (SLit 0)] [mkVNA E9qa 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cg.SpineMallocSec6IL.run9qa]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cg.SpineMallocSec6IL.run9qa__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXEFfa_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS14A1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECertFfa_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S5S8A1VGS0;S3S0S1S14Z1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S28G0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [] GS0 [mkVNA D9fa 1 (SLit 0)] [mkVNA FFfa 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cg.SpineMallocSec6IL.runFfa]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cg.SpineMallocSec6IL.runFfa__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXEFqa_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS16A1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECertFqa_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S5S8A1VGS0;S3S0S1S16Z1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S2aG0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [] GS0 [mkVNA D9qa 1 (SLit 0)] [mkVNA FFqa 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cg.SpineMallocSec6IL.runFqa]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cg.SpineMallocSec6IL.runFqa__runeq | vm_cast_no_check (eq_refl true)]. Qed.

Lemma NXE6Ab_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS11A1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert6Ab_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S3S8SeS5S8A1A3VGS0;S3S0S1S11Z1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S2dG0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [MSENT] GS0 [mkVNA C5Ab 1 (SLit 0)] [mkVNA Y6Ab 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cg.SpineMallocSec6IL.run6Ab]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cg.SpineMallocSec6IL.run6Ab__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXE7b_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS19A1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert7b_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S3S8SeS5S8A1A3VGS0;S3S0S1S19Z1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S25G0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [MSENT] GS0 [mkVNA U7b 1 (SLit 0)] [mkVNA ET7b 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cg.SpineMallocSec6IL.run7b]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cg.SpineMallocSec6IL.run7b__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXE8b_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS1bA1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert8b_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S3S8SeS5S8A1A3VGS0;S3S0S1S1bZ1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S27G0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [MSENT] GS0 [mkVNA U8b 1 (SLit 0)] [mkVNA ET8b 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cg.SpineMallocSec6IL.run8b]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cg.SpineMallocSec6IL.run8b__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXE9b_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS1dA1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert9b_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S3S8SeS3S8SfS5S8A1A3A3VGS0;S3S0S1S1dZ1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S1fG0G1A3S3S0S1S21G0G1A3G2A3A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [MSENT; PGST] GS0 [mkVNA U9b 1 (SLit 0)] [mkVNA E9fb 0 (SLit 0); mkVNA E9pb 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cg.SpineMallocSec6IL.run9b]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cg.SpineMallocSec6IL.run9b__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXE9qb_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS13A1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert9qb_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S3S8SeS5S8A1A3VGS0;S3S0S1S13Z1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S23G0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [MSENT] GS0 [mkVNA CO9pb 1 (SLit 0)] [mkVNA E9qb 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cg.SpineMallocSec6IL.run9qb]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cg.SpineMallocSec6IL.run9qb__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXEFfb_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS15A1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECertFfb_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S5S8A1VGS0;S3S0S1S15Z1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S29G0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [] GS0 [mkVNA D9fb 1 (SLit 0)] [mkVNA FFfb 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cg.SpineMallocSec6IL.runFfb]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cg.SpineMallocSec6IL.runFfb__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXEFqb_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS17A1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECertFqb_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S5S8A1VGS0;S3S0S1S17Z1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S2bG0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [] GS0 [mkVNA D9qb 1 (SLit 0)] [mkVNA FFqb 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cg.SpineMallocSec6IL.runFqb]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cg.SpineMallocSec6IL.runFqb__runeq | vm_cast_no_check (eq_refl true)]. Qed.
End INST.
End SpineMallocSec6IEL.

(* [comment removed for export] *)
Module SpineMallocSec6JEL.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "False"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rm"; "rw"; "valuation"; "rl"; "@Corelib.Init.Datatypes"; "list"; "pair"; "prod"; "None"; "length"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "DG"; "aa_Km"; "aa_sec"; "sec_chunk"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "div"; "lt"; "of_nat"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bp.DepotCallS"; "AXK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "Sh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "AE_A"; "KcA"; "Kc_ok"; "mem_keptA"; "JL_malloc_ok"; "L_malloc_ok"; "Posts_malloc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger"; "sepZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "dblocks"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "secmapsize"; "stopJ_stable"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3"; "JGs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3IL"; "nx0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SecBump"; "bumpP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ca.SpineMallocSec5IL"; "C5ac"; "C5bc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM"; "IMG_M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec2"; "IMG_S"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fi.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ao.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocS9 SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bt.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require q0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocSec4IL.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bw.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RebuildM SpineMallocSec2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ca.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cg.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cm.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cc.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.CertMallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ao.SpineMallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_refl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.SecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3IL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineMallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec4IL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.CertMallocSU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bw.SpineMallocSec5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bp.DepotCallS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.CertMallocSV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c0.SpineMallocSec6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c4.SpineMallocSec6L OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ca.SpineMallocSec5IL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c4.SpineMallocSec7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cg.SpineMallocSec6IL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cm.SpineMallocSec6JL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSecE1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bw.SpineMallocSecE2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cc.SpineMallocSecE3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cq.SpineMallocSec6IEL.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 0. Let st : ustop := UStopLe. Let tmax : Z := 2.
Let GS0 : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3.GS nx0.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTM : ltac2:(tb__ "0|0|
S0S30VCST;R1A2S30S39R2A2S6F_;F_;Fa;").
Hypothesis HCSTS : ltac2:(tb__ "0|0|
S0S30VCST;R1A2S30S3aR2A2S6F_;F_;Fa;").

Theorem esec_tail_0la_P : ltac2:(tb__ "0|9|
S11S28S9S9S1bQ40M0A1M1SbG1A1M2S12SbSdS22S24A2M3A1S1eG3ScS22S24S2cS27VW;Vst;A3S2bS2eS2A1VCST;VXGL;R8R7A5A4R1A3S33VW;Vst;A2S29R9A1S1S3G1S8R9R1A2S8RaR1A2A3Fi;S1S3SbS1bQ8A1M4A1SaRaR1A2SaRbR1A2A3Fl;S2aVCST;VXGL;RdRdS7RbA1S7RaA1A6S16S1aSfS15S14ReA1A2A1S13ReA1A2SdS0S0A2M5S1eG5R1S31RaA1A3S2fR2ScS0S0S1cG0RdA2M6S32S1cG0S8RePcA2A2A1M7A4A2F_;Fbn;S0S4S16S26G6A1M8R1A2S19R1S17G8S18G7Z8A2A2A2A2S5S3S10G4A1S7RfS1dG0R2A2A2SeG4A1A3A1F_;Fz;S9G2S1fS2S21S2S34U0Vst;S35S25S11S36R1A1LX;RdA2R13R12R10RfA8S37R2R1A5S23S2S20R11ReRcA5A3FtX;FrX;F_;F_;F_;F_;F_;F_;F_;F_;F_;FPosts;FG2;Ftp0;Fa;Frho;Frho0;FKc;FA;").
Proof.
  intros A Kc rho0 rho a tp0 G2 Posts HPin HUS HKc HLw HLl HKEPT HL9 HDB RUNDEF.
  set (BX := AXK (fun X : AA => bumpP X) G2). set (Q := LQPA segsA NF rho0 tp0 Posts).
  assert (HW : st = UStopLeOrPc -> W = []) by (intros E; discriminate E).
  assert (BXg : forall X, aa_geom (BX X) = aa_geom X) by (intros X; reflexivity).
  eapply esec_g43_low with
    (nW := 0%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (BX := BX) (BXg := BXg) (PX := PXa) (FXP := FXPa) (PX_noband := (PXnba_0 G2))
    (C5 := C5ac) (C5A := C5Aa) (Y6A := Y6Aa) (E6 := E6a) (CT6 := CT6a) (CO6 := CO6a) (T6 := T6a) (sA := s6Aa) (s6 := s6a) (R6 := R6a) (FLOW := FLOWa_0) (HC5A := HC5Aa_0)
    (FBA := FBAa_0) (Cert6A := Cert6Aa_0) (E6A := E6Aa_0) (I6A := I6Aa_0) (WC6 := WC6a_0) (DF6 := DF6a_0) (NX6 := NX6a_0) (HC6 := HC6a_0) (SK6 := SK6a_0) (FC6 := FC6a_0)
    (FX6 := FX6a_0) (XC6 := XC6a_0) (HCO6 := HCO6a_0) (WCO6 := WCO6a_0) (He6 := He6a_0) (Hchk6 := Hchk6a_0) (HT6 := HT6a_0) (FBC6 := FBC6a_0) (FBT6 := FBT6a_0)
    (NXC6 := NXC6a_0)
    (NXE6A := NXE6Aa_0) (ECert6A := ECert6Aa_0);
    [exact HW | exact HUS | exact HKc | exact RUNDEF |].
  intros rY6 tY6. rewrite HD6a_0.
  revert rY6 tY6. apply (hint_low_etriple 0%nat st nx0 BX D6a D6La (F_g7L nx0) WD6La_0 DD6La_0 NXD6La_0 HD6La_0 FLOW6a_0
           (fun A0 Kc0 r0 a0 r1 t1 tr1 md1 HJ1 HL1 => F_g7L_hold 0%nat st tmax nx0 Hnx_0 BX A0 Kc0 r0 a0 r1 t1 tr1 md1 HJ1 HL1) A Kc rho a Q). intros rY6 tY6.
  eapply esec_g44 with
    (nW := 0%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (BX := BX) (BXg := BXg) (PX := PXa) (FXP := FXPa) (PX_noband := (PXnba_0 G2))
    (D6 := D6La) (U7 := U7a) (ET7 := ET7a) (CT7 := CT7a) (CO7 := CO7a) (CR7 := CR7a) (CS7 := CS7a) (CM7 := CM7a) (T7 := T7a) (s7 := s7a) (R7 := R7a) (n7 := n7a)
    (WU7 := WU7a_0) (DU7 := DU7a_0) (NXU7 := NXU7a_0) (HU7 := HU7a_0) (Cert7 := Cert7a_0) (WC7 := WC7a_0) (DF7 := DF7a_0) (NX7 := NX7a_0) (HC7 := HC7a_0) (SK7 := SK7a_0)
    (FC7 := FC7a_0) (FX7 := FX7a_0) (XC7 := XC7a_0) (HCO7 := HCO7a_0) (WCO7 := WCO7a_0) (RB7 := RB7a_0) (HCR7 := HCR7a_0) (LEN7 := LEN7a_0) (PERM_nd7 := PERM_nd7a_0)
    (PERM_lt7 := PERM_lt7a_0) (PERM_cov7 := PERM_cov7a_0) (HCS7 := HCS7a_0) (MRG7 := MRG7a_0) (HCM7 := HCM7a_0) (He7 := He7a_0) (Hchk7 := Hchk7a_0) (HT7 := HT7a_0)
    (FBC7 := FBC7a_0) (FBT7 := FBT7a_0) (NXC7 := NXC7a_0)
    (NXE7 := NXE7a_0) (ECert7 := ECert7a_0);
    [exact HW | exact HUS | exact HKc | exact RUNDEF |].
  intros rY7 tY7. rewrite HD7a_0.
  revert rY7 tY7. apply (hint_low_etriple 0%nat st nx0 BX D7a D7La (F_g8L nx0) WD7La_0 DD7La_0 NXD7La_0 HD7La_0 FLOW7a_0
           (fun A0 Kc0 r0 a0 r1 t1 tr1 md1 HJ1 HL1 => F_g8L_hold 0%nat st tmax nx0 Hnx_0 BX A0 Kc0 r0 a0 r1 t1 tr1 md1 HJ1 HL1) A Kc rho a Q). intros rY7 tY7.
  eapply esec_g45 with
    (nW := 0%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (BX := BX) (BXg := BXg) (PX := PXa) (FXP := FXPa) (PX_noband := (PXnba_0 G2))
    (D7 := D7La) (U8 := U8a) (ET8 := ET8a) (CT8 := CT8a) (CO8 := CO8a) (T8 := T8a) (s8 := s8a) (R8 := R8a) (WU8 := WU8a_0) (DU8 := DU8a_0) (NXU8 := NXU8a_0)
    (HU8 := HU8a_0) (Cert8 := Cert8a_0) (WC8 := WC8a_0) (DF8 := DF8a_0) (NX8 := NX8a_0) (HC8 := HC8a_0) (SK8 := SK8a_0) (FC8 := FC8a_0) (FX8 := FX8a_0) (XC8 := XC8a_0)
    (HCO8 := HCO8a_0) (WCO8 := WCO8a_0) (He8 := He8a_0) (Hchk8 := Hchk8a_0) (HT8 := HT8a_0) (FBC8 := FBC8a_0) (FBT8 := FBT8a_0) (NXC8 := NXC8a_0)
    (NXE8 := NXE8a_0) (ECert8 := ECert8a_0);
    [exact HW | exact HUS | exact HKc | exact RUNDEF |].
  intros rY8 tY8. rewrite HD8a_0.
  revert rY8 tY8. apply (hint_low_etriple 0%nat st nx0 BX D8a D8La (F_g9L nx0) WD8La_0 DD8La_0 NXD8La_0 HD8La_0 FLOW8a_0
           (fun A0 Kc0 r0 a0 r1 t1 tr1 md1 HJ1 HL1 => F_g9L_hold 0%nat st tmax nx0 Hnx_0 BX A0 Kc0 r0 a0 r1 t1 tr1 md1 HJ1 HL1) A Kc rho a Q). intros rY8 tY8.
  eapply esec_g46 with
    (nW := 0%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (BX := BX) (BXg := BXg) (PX := PXa) (FXP := FXPa) (PX_noband := (PXnba_0 G2))
    (D8 := D8La) (U9 := U9a) (E9f := E9fa) (E9p := E9pa) (CO9p := CO9pa) (E9q := E9qa) (WU9 := WU9a_0) (DU9 := DU9a_0) (NXU9 := NXU9a_0) (HU9 := HU9a_0)
    (Cert9 := Cert9a_0) (SK9 := SK9a_0) (FC9 := FC9a_0) (FX9 := FX9a_0) (FP9 := FP9a_0) (XC9 := XC9a_0) (HCO9 := HCO9a_0) (WCO9 := WCO9a_0) (Cert9q := Cert9qa_0)
    (NXE9 := NXE9a_0) (ECert9 := ECert9a_0) (NXE9q := NXE9qa_0) (ECert9q := ECert9qa_0);
    [exact HW | exact HUS | exact HKc | exact RUNDEF | |].
  - intros rY9 tY9.
    eapply esec_g47 with
    (nW := 0%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (BX := BX) (E := E9fa) (S9a := S9afa) (S9b := S9bfa) (T9 := T9fa) (iM := iMfa)
    (s9 := s9fa) (R9 := R9fa) (HS9a := HS9afa_0) (HS9b := HS9bfa_0) (He9 := He9fa_0) (Hchk9 := Hchk9fa_0) (HT9 := HT9fa_0) (FBC9 := FBC9fa_0) (FBT9 := FBT9fa_0)
    (NXC9 := NXC9fa_0);
      [exact HUS | exact HKc |].
    intros rZ tZ. rewrite HD9fa_0.
    eapply esec_g48_P with
    (nW := 0%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (CST := CST) (XGL := XGL) (HCST := HCST) (HXGL := HXGL) (HCSTM := HCSTM)
    (HCSTS := HCSTS) (BX := BX) (BXok := (BXoka_0 G2)) (blk := 131072) (dpx := DZero) (NRESe := (SAlu ALU_ADD (SVar V_NRES) (SLit 16384))) (FXP := FXPa)
    (Hdpx := (or_intror eq_refl)) (HPATH := (HPATHa_0 G2)) (partial := false) (F := FFfa) (swc := swcfa) (c1 := c1fa) (c2 := c2fa) (c4 := c4fa) (c5 := c5fa) (mc := mcfa)
    (xc := xcfa) (tyb := tybfa) (SELF := SELFfa_0) (NDF := NDFfa_0) (BNDF := BNDFfa_0) (COVF := COVFfa_0) (XFn := XFnfa_0) (BFb := BFbfa_0) (FPF := FPFfa_0)
    (FXF := FXFfa_0) (FPAR := FPARfa_0) (Hc1 := Hc1fa_0) (Hmc := Hmcfa_0) (Htyb := Htybfa_0) (Hxc := Hxcfa_0) (WCU := WCUfa_0) (SELU := SELUfa_0) (NDU := NDUfa_0)
    (BNDU := BNDUfa_0) (COVU := COVUfa_0) (W9 := W9fa_0) (D9 := D9fa_0) (XB9 := XB9fa_0) (s9 := sFfa) (ENT9 := ENT9fa_0) (SID9 := SID9fa_0) (G110 := G110fa_0)
    (DF9 := D9fa) (CertF := CertFfa_0)
      (NXEF := NXEFfa_0) (ECertF := ECertFfa_0);
      [exact HPin | exact HW | exact HUS | exact HKc | exact HLw | exact HLl | exact HKEPT | exact HL9 | exact HDB].
  - intros rY9 tY9.
    eapply esec_g47 with
    (nW := 0%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (BX := BX) (E := E9qa) (S9a := S9aqa) (S9b := S9bqa) (T9 := T9qa) (iM := iMqa)
    (s9 := s9qa) (R9 := R9qa) (HS9a := HS9aqa_0) (HS9b := HS9bqa_0) (He9 := He9qa_0) (Hchk9 := Hchk9qa_0) (HT9 := HT9qa_0) (FBC9 := FBC9qa_0) (FBT9 := FBT9qa_0)
    (NXC9 := NXC9qa_0);
      [exact HUS | exact HKc |].
    intros rZ tZ. rewrite HD9qa_0.
    eapply esec_g48_P with
    (nW := 0%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (CST := CST) (XGL := XGL) (HCST := HCST) (HXGL := HXGL) (HCSTM := HCSTM)
    (HCSTS := HCSTS) (BX := BX) (BXok := (BXoka_0 G2)) (blk := 131072) (dpx := DZero) (NRESe := (SAlu ALU_ADD (SVar V_NRES) (SLit 16384))) (FXP := FXPa)
    (Hdpx := (or_intror eq_refl)) (HPATH := (HPATHa_0 G2)) (partial := true) (F := FFqa) (swc := swcqa) (c1 := c1qa) (c2 := c2qa) (c4 := c4qa) (c5 := c5qa) (mc := mcqa)
    (xc := xcqa) (tyb := tybqa) (SELF := SELFqa_0) (NDF := NDFqa_0) (BNDF := BNDFqa_0) (COVF := COVFqa_0) (XFn := XFnqa_0) (BFb := BFbqa_0) (FPF := FPFqa_0)
    (FXF := FXFqa_0) (FPAR := FPARqa_0) (Hc1 := Hc1qa_0) (Hmc := Hmcqa_0) (Htyb := Htybqa_0) (Hxc := Hxcqa_0) (WCU := WCUqa_0) (SELU := SELUqa_0) (NDU := NDUqa_0)
    (BNDU := BNDUqa_0) (COVU := COVUqa_0) (W9 := W9qa_0) (D9 := D9qa_0) (XB9 := XB9qa_0) (s9 := sFqa) (ENT9 := ENT9qa_0) (SID9 := SID9qa_0) (G110 := G110qa_0)
    (DF9 := D9qa) (CertF := CertFqa_0)
      (NXEF := NXEFqa_0) (ECertF := ECertFqa_0);
      [exact HPin | exact HW | exact HUS | exact HKc | exact HLw | exact HLl | exact HKEPT | exact HL9 | exact HDB].
Qed.

Theorem esec_tail_0la : ltac2:(tb__ "0|8|
S11S28S9S9S1bQ40M0A1M1SbG1A1M2S12S33VW;Vst;A2S29R7A1S1S3G1S8R7R1A2S8R8R1A2A3Fi;S1S3SbS1bQ8A1M3A1SaR8R1A2SaR9R1A2A3Fl;S2aVCST;VXGL;RbRbS7R9A1S7R8A1A6S16S1aSfS15S14RcA1A2A1S13RcA1A2SdS0S0A2M4S1eG4R1S31R8A1A3S2fR2ScS0S0S1cG0RbA2M5S32S1cG0S8RcPcA2A2A1M6A4A2F_;Fbn;S0S4S16S26G5A1M7R1A2S19R1S17G7S18G6Z8A2A2A2A2S5S3S10G3A1S7RdS1dG0R2A2A2SeG3A1A3A1F_;Fz;S9G2S1fS2S21S2S34U0Vst;S35S25S11S36R1A1LX;RbA2R11R10ReRdA8S37R2R1A5S23S2S20RfRcS2dS27S2eS2A1VCST;VXGL;VW;Vst;R11R10A8A5A3FtX;FrX;F_;F_;F_;F_;F_;F_;F_;F_;FG2;Ftp0;Fa;Frho;Frho0;FKc;FA;").
Proof.
  intros A Kc rho0 rho a tp0 G2. exact (esec_tail_0la_P A Kc rho0 rho a tp0 G2 (Posts_malloc AE_A (AInvA segsA) CST XGL W st A Kc) (or_intror (or_introl eq_refl))).
Qed.

Theorem esec_tail_0lb_P : ltac2:(tb__ "0|9|
S11S28S9S9S1bQ40M0A1M1SbG1A1M2S12SbSdS22S24A2M3A1S1eG3ScS22S24S2cS27VW;Vst;A3S2bS2eS2A1VCST;VXGL;R8R7A5A4R1A3S33VW;Vst;A2S29R9A1S1S3G1S8R9R1A2S8RaR1A2A3Fi;S1S3SbS1bQ8A1M4A1SaRaR1A2SaRbR1A2A3Fl;S2aVCST;VXGL;RdRdS7RbA1S7RaA1A6S16S1aSfS15S14ReA1A2A1S13ReA1A2SdS0S0A2M5S1eG5R1S31RaA1A3S2fR2ScS0S0S1cG0RdA2M6S32S1cG0S8RePcA2A2A1M7A4A2F_;Fbn;S0S4S16S26G6A1M8R1A2S19R1S17G8S18G7Z8A2A2A2A2S5S3S10G4A1S7RfS1dG0R2A2A2SeG4A1A3A1F_;Fz;S9G2S1fS2S21S2S34U0Vst;S35S25S11R1LX;RdA2R13R12R10RfA8S38R2R1A5S23S2S20R11ReRcA5A3FtX;FrX;F_;F_;F_;F_;F_;F_;F_;F_;F_;FPosts;FG2;Ftp0;Fa;Frho;Frho0;FKc;FA;").
Proof.
  intros A Kc rho0 rho a tp0 G2 Posts HPin HUS HKc HLw HLl HKEPT HL9 HDB RUNDEF.
  set (BX := AXK (fun X : AA => X) G2). set (Q := LQPA segsA NF rho0 tp0 Posts).
  assert (HW : st = UStopLeOrPc -> W = []) by (intros E; discriminate E).
  assert (BXg : forall X, aa_geom (BX X) = aa_geom X) by (intros X; reflexivity).
  eapply esec_g43_low with
    (nW := 0%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (BX := BX) (BXg := BXg) (PX := PXb) (FXP := FXPb) (PX_noband := (PXnbb_0 G2))
    (C5 := C5bc) (C5A := C5Ab) (Y6A := Y6Ab) (E6 := E6b) (CT6 := CT6b) (CO6 := CO6b) (T6 := T6b) (sA := s6Ab) (s6 := s6b) (R6 := R6b) (FLOW := FLOWb_0) (HC5A := HC5Ab_0)
    (FBA := FBAb_0) (Cert6A := Cert6Ab_0) (E6A := E6Ab_0) (I6A := I6Ab_0) (WC6 := WC6b_0) (DF6 := DF6b_0) (NX6 := NX6b_0) (HC6 := HC6b_0) (SK6 := SK6b_0) (FC6 := FC6b_0)
    (FX6 := FX6b_0) (XC6 := XC6b_0) (HCO6 := HCO6b_0) (WCO6 := WCO6b_0) (He6 := He6b_0) (Hchk6 := Hchk6b_0) (HT6 := HT6b_0) (FBC6 := FBC6b_0) (FBT6 := FBT6b_0)
    (NXC6 := NXC6b_0)
    (NXE6A := NXE6Ab_0) (ECert6A := ECert6Ab_0);
    [exact HW | exact HUS | exact HKc | exact RUNDEF |].
  intros rY6 tY6. rewrite HD6b_0.
  revert rY6 tY6. apply (hint_low_etriple 0%nat st nx0 BX D6b D6Lb (F_g7L nx0) WD6Lb_0 DD6Lb_0 NXD6Lb_0 HD6Lb_0 FLOW6b_0
           (fun A0 Kc0 r0 a0 r1 t1 tr1 md1 HJ1 HL1 => F_g7L_hold 0%nat st tmax nx0 Hnx_0 BX A0 Kc0 r0 a0 r1 t1 tr1 md1 HJ1 HL1) A Kc rho a Q). intros rY6 tY6.
  eapply esec_g44 with
    (nW := 0%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (BX := BX) (BXg := BXg) (PX := PXb) (FXP := FXPb) (PX_noband := (PXnbb_0 G2))
    (D6 := D6Lb) (U7 := U7b) (ET7 := ET7b) (CT7 := CT7b) (CO7 := CO7b) (CR7 := CR7b) (CS7 := CS7b) (CM7 := CM7b) (T7 := T7b) (s7 := s7b) (R7 := R7b) (n7 := n7b)
    (WU7 := WU7b_0) (DU7 := DU7b_0) (NXU7 := NXU7b_0) (HU7 := HU7b_0) (Cert7 := Cert7b_0) (WC7 := WC7b_0) (DF7 := DF7b_0) (NX7 := NX7b_0) (HC7 := HC7b_0) (SK7 := SK7b_0)
    (FC7 := FC7b_0) (FX7 := FX7b_0) (XC7 := XC7b_0) (HCO7 := HCO7b_0) (WCO7 := WCO7b_0) (RB7 := RB7b_0) (HCR7 := HCR7b_0) (LEN7 := LEN7b_0) (PERM_nd7 := PERM_nd7b_0)
    (PERM_lt7 := PERM_lt7b_0) (PERM_cov7 := PERM_cov7b_0) (HCS7 := HCS7b_0) (MRG7 := MRG7b_0) (HCM7 := HCM7b_0) (He7 := He7b_0) (Hchk7 := Hchk7b_0) (HT7 := HT7b_0)
    (FBC7 := FBC7b_0) (FBT7 := FBT7b_0) (NXC7 := NXC7b_0)
    (NXE7 := NXE7b_0) (ECert7 := ECert7b_0);
    [exact HW | exact HUS | exact HKc | exact RUNDEF |].
  intros rY7 tY7. rewrite HD7b_0.
  revert rY7 tY7. apply (hint_low_etriple 0%nat st nx0 BX D7b D7Lb (F_g8L nx0) WD7Lb_0 DD7Lb_0 NXD7Lb_0 HD7Lb_0 FLOW7b_0
           (fun A0 Kc0 r0 a0 r1 t1 tr1 md1 HJ1 HL1 => F_g8L_hold 0%nat st tmax nx0 Hnx_0 BX A0 Kc0 r0 a0 r1 t1 tr1 md1 HJ1 HL1) A Kc rho a Q). intros rY7 tY7.
  eapply esec_g45 with
    (nW := 0%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (BX := BX) (BXg := BXg) (PX := PXb) (FXP := FXPb) (PX_noband := (PXnbb_0 G2))
    (D7 := D7Lb) (U8 := U8b) (ET8 := ET8b) (CT8 := CT8b) (CO8 := CO8b) (T8 := T8b) (s8 := s8b) (R8 := R8b) (WU8 := WU8b_0) (DU8 := DU8b_0) (NXU8 := NXU8b_0)
    (HU8 := HU8b_0) (Cert8 := Cert8b_0) (WC8 := WC8b_0) (DF8 := DF8b_0) (NX8 := NX8b_0) (HC8 := HC8b_0) (SK8 := SK8b_0) (FC8 := FC8b_0) (FX8 := FX8b_0) (XC8 := XC8b_0)
    (HCO8 := HCO8b_0) (WCO8 := WCO8b_0) (He8 := He8b_0) (Hchk8 := Hchk8b_0) (HT8 := HT8b_0) (FBC8 := FBC8b_0) (FBT8 := FBT8b_0) (NXC8 := NXC8b_0)
    (NXE8 := NXE8b_0) (ECert8 := ECert8b_0);
    [exact HW | exact HUS | exact HKc | exact RUNDEF |].
  intros rY8 tY8. rewrite HD8b_0.
  revert rY8 tY8. apply (hint_low_etriple 0%nat st nx0 BX D8b D8Lb (F_g9L nx0) WD8Lb_0 DD8Lb_0 NXD8Lb_0 HD8Lb_0 FLOW8b_0
           (fun A0 Kc0 r0 a0 r1 t1 tr1 md1 HJ1 HL1 => F_g9L_hold 0%nat st tmax nx0 Hnx_0 BX A0 Kc0 r0 a0 r1 t1 tr1 md1 HJ1 HL1) A Kc rho a Q). intros rY8 tY8.
  eapply esec_g46 with
    (nW := 0%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (BX := BX) (BXg := BXg) (PX := PXb) (FXP := FXPb) (PX_noband := (PXnbb_0 G2))
    (D8 := D8Lb) (U9 := U9b) (E9f := E9fb) (E9p := E9pb) (CO9p := CO9pb) (E9q := E9qb) (WU9 := WU9b_0) (DU9 := DU9b_0) (NXU9 := NXU9b_0) (HU9 := HU9b_0)
    (Cert9 := Cert9b_0) (SK9 := SK9b_0) (FC9 := FC9b_0) (FX9 := FX9b_0) (FP9 := FP9b_0) (XC9 := XC9b_0) (HCO9 := HCO9b_0) (WCO9 := WCO9b_0) (Cert9q := Cert9qb_0)
    (NXE9 := NXE9b_0) (ECert9 := ECert9b_0) (NXE9q := NXE9qb_0) (ECert9q := ECert9qb_0);
    [exact HW | exact HUS | exact HKc | exact RUNDEF | |].
  - intros rY9 tY9.
    eapply esec_g47 with
    (nW := 0%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (BX := BX) (E := E9fb) (S9a := S9afb) (S9b := S9bfb) (T9 := T9fb) (iM := iMfb)
    (s9 := s9fb) (R9 := R9fb) (HS9a := HS9afb_0) (HS9b := HS9bfb_0) (He9 := He9fb_0) (Hchk9 := Hchk9fb_0) (HT9 := HT9fb_0) (FBC9 := FBC9fb_0) (FBT9 := FBT9fb_0)
    (NXC9 := NXC9fb_0);
      [exact HUS | exact HKc |].
    intros rZ tZ. rewrite HD9fb_0.
    eapply esec_g48_P with
    (nW := 0%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (CST := CST) (XGL := XGL) (HCST := HCST) (HXGL := HXGL) (HCSTM := HCSTM)
    (HCSTS := HCSTS) (BX := BX) (BXok := (BXokb_0 G2)) (blk := 8) (dpx := DUnknown) (NRESe := (SVar V_NRES)) (FXP := FXPb) (Hdpx := (or_introl eq_refl))
    (HPATH := (HPATHb_0 G2)) (partial := false) (F := FFfb) (swc := swcfb) (c1 := c1fb) (c2 := c2fb) (c4 := c4fb) (c5 := c5fb) (mc := mcfb) (xc := xcfb) (tyb := tybfb)
    (SELF := SELFfb_0) (NDF := NDFfb_0) (BNDF := BNDFfb_0) (COVF := COVFfb_0) (XFn := XFnfb_0) (BFb := BFbfb_0) (FPF := FPFfb_0) (FXF := FXFfb_0) (FPAR := FPARfb_0)
    (Hc1 := Hc1fb_0) (Hmc := Hmcfb_0) (Htyb := Htybfb_0) (Hxc := Hxcfb_0) (WCU := WCUfb_0) (SELU := SELUfb_0) (NDU := NDUfb_0) (BNDU := BNDUfb_0) (COVU := COVUfb_0)
    (W9 := W9fb_0) (D9 := D9fb_0) (XB9 := XB9fb_0) (s9 := sFfb) (ENT9 := ENT9fb_0) (SID9 := SID9fb_0) (G110 := G110fb_0) (DF9 := D9fb) (CertF := CertFfb_0)
      (NXEF := NXEFfb_0) (ECertF := ECertFfb_0);
      [exact HPin | exact HW | exact HUS | exact HKc | exact HLw | exact HLl | exact HKEPT | exact HL9 | exact HDB].
  - intros rY9 tY9.
    eapply esec_g47 with
    (nW := 0%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (BX := BX) (E := E9qb) (S9a := S9aqb) (S9b := S9bqb) (T9 := T9qb) (iM := iMqb)
    (s9 := s9qb) (R9 := R9qb) (HS9a := HS9aqb_0) (HS9b := HS9bqb_0) (He9 := He9qb_0) (Hchk9 := Hchk9qb_0) (HT9 := HT9qb_0) (FBC9 := FBC9qb_0) (FBT9 := FBT9qb_0)
    (NXC9 := NXC9qb_0);
      [exact HUS | exact HKc |].
    intros rZ tZ. rewrite HD9qb_0.
    eapply esec_g48_P with
    (nW := 0%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (CST := CST) (XGL := XGL) (HCST := HCST) (HXGL := HXGL) (HCSTM := HCSTM)
    (HCSTS := HCSTS) (BX := BX) (BXok := (BXokb_0 G2)) (blk := 8) (dpx := DUnknown) (NRESe := (SVar V_NRES)) (FXP := FXPb) (Hdpx := (or_introl eq_refl))
    (HPATH := (HPATHb_0 G2)) (partial := true) (F := FFqb) (swc := swcqb) (c1 := c1qb) (c2 := c2qb) (c4 := c4qb) (c5 := c5qb) (mc := mcqb) (xc := xcqb) (tyb := tybqb)
    (SELF := SELFqb_0) (NDF := NDFqb_0) (BNDF := BNDFqb_0) (COVF := COVFqb_0) (XFn := XFnqb_0) (BFb := BFbqb_0) (FPF := FPFqb_0) (FXF := FXFqb_0) (FPAR := FPARqb_0)
    (Hc1 := Hc1qb_0) (Hmc := Hmcqb_0) (Htyb := Htybqb_0) (Hxc := Hxcqb_0) (WCU := WCUqb_0) (SELU := SELUqb_0) (NDU := NDUqb_0) (BNDU := BNDUqb_0) (COVU := COVUqb_0)
    (W9 := W9qb_0) (D9 := D9qb_0) (XB9 := XB9qb_0) (s9 := sFqb) (ENT9 := ENT9qb_0) (SID9 := SID9qb_0) (G110 := G110qb_0) (DF9 := D9qb) (CertF := CertFqb_0)
      (NXEF := NXEFqb_0) (ECertF := ECertFqb_0);
      [exact HPin | exact HW | exact HUS | exact HKc | exact HLw | exact HLl | exact HKEPT | exact HL9 | exact HDB].
Qed.

Theorem esec_tail_0lb : ltac2:(tb__ "0|8|
S11S28S9S9S1bQ40M0A1M1SbG1A1M2S12S33VW;Vst;A2S29R7A1S1S3G1S8R7R1A2S8R8R1A2A3Fi;S1S3SbS1bQ8A1M3A1SaR8R1A2SaR9R1A2A3Fl;S2aVCST;VXGL;RbRbS7R9A1S7R8A1A6S16S1aSfS15S14RcA1A2A1S13RcA1A2SdS0S0A2M4S1eG4R1S31R8A1A3S2fR2ScS0S0S1cG0RbA2M5S32S1cG0S8RcPcA2A2A1M6A4A2F_;Fbn;S0S4S16S26G5A1M7R1A2S19R1S17G7S18G6Z8A2A2A2A2S5S3S10G3A1S7RdS1dG0R2A2A2SeG3A1A3A1F_;Fz;S9G2S1fS2S21S2S34U0Vst;S35S25S11R1LX;RbA2R11R10ReRdA8S38R2R1A5S23S2S20RfRcS2dS27S2eS2A1VCST;VXGL;VW;Vst;R11R10A8A5A3FtX;FrX;F_;F_;F_;F_;F_;F_;F_;F_;FG2;Ftp0;Fa;Frho;Frho0;FKc;FA;").
Proof.
  intros A Kc rho0 rho a tp0 G2. exact (esec_tail_0lb_P A Kc rho0 rho a tp0 G2 (Posts_malloc AE_A (AInvA segsA) CST XGL W st A Kc) (or_intror (or_introl eq_refl))).
Qed.
End INST.
End SpineMallocSec6JEL.

