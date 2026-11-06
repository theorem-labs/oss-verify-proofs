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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ki kn.
From Stdlib Require FunctionalExtensionality.

(* [comment removed for export] *)
Module SpineCallocSec5J.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "sobj"; "obj_range"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "DG"; "aa_geom"; "ag_pab"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3"; "JGs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jq.SpineCallocSec3I"; "nx0"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@Corelib.Init.Datatypes"; "list"; "pair"; "prod"; "fst"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "world"; "assn"; "etriple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "@Stdlib.Lists.List"; "In"; "@Corelib.Init.Logic"; "and"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k5.CDepotCallS"; "AXK"; "dlink"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase"; "stopJ_w"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger"; "sepZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dblocks"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "secmapsize"; "stopJ_stable"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.CSecBump"; "bumpP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ki.SpineCallocSec5I"; "C5ac"; "C5bc"; "X5ac"; "X5bc"; "EXoa"; "EXob"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "kPtrArrayReserve"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineCallocSec4I"; "T4ac"; "T4bc"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jx.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineCallocSec4I.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require il.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CDepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ki.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.SpineCallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SegD_refl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.CSecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.CSecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jq.SpineCallocSec3I OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jx.SpineCallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineCallocSec4I OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.CertCallocSU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k6.SpineCallocSec5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CDepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k5.CDepotCallS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k9.SpineCallocSec6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ki.SpineCallocSec5I.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import CallocBase2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ii.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.CallocPosts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 0. Let st : ustop := UStopLe. Let tmax : Z := 2.
Let GS0 : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3.GS nx0.

Lemma EXZa_0 : ltac2:(tb__ "0|3|
S6S1aS2S10Q40A1M0S2S11G0A1S17S4S0SaS1SdU0Vst;SeS6S2aR1A1LX;R9R8R7R6A8S2dR5R4R3A6S1cS4R3S2fA3S1dS26S14S0S0S5R7R4A2M1A3R3A2S27R3S15S0S0G1A3A2A2S1eS1dS26S32R4A2S27R4S31A2A2S1dS26S9S8RcA1A1M2R4A2S27R4S28G2S33A2A2A2A2F_;F_;F_;Fz;Fo;Fw;Ftp;FrhoE;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a rhoE tp w o z Hw Ho Hz. pose proof (SPA_facts_hold segsA _ rhoE X5ac tp w Hw) as HF. destruct w as [tr [ms md]].
  pose proof (proj2 Hw) as HJ. cbn [w_tr w_cfg cfg_model fst snd] in HJ.
  pose proof (proj1 (Forall_forall _ _) HF _ FXBa_0) as HBR.
  destruct Ho as [<-|[<-|[<-|[]]]].
  - left. exact (ex2_band 0%nat st tmax nx0 Hnx_0 (fun X : AA => bumpP X) A Kc rho a rhoE tp tr md z HJ Hz).
  - left. exact (ex1_band 0%nat st tmax nx0 Hnx_0 (fun X : AA => bumpP X) A Kc rho a rhoE tp tr md z HJ Hz).
  - right. exact (exblk_pab 0%nat st tmax nx0 Hnx_0 (fun X : AA => bumpP X) A Kc rho a rhoE tp tr md z (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) HJ HBR Hz).
Qed.

Theorem depot_call_S_0ha : ltac2:(tb__ "0|6|
S17OF_;S6S1aS2S10Q40M0A1M1S18S21VW;Vst;A2S25VW;Vst;A2S1bR6A1ScS1R9SbR7A1A3S29S1RaSbR8A1A3S7S2S2S11G1A1M2S13S0S0A2M3S1cG3R1S23R5A1A3S22R2S12S0S0SfG0RdA2S24SfG0S3RePcA2A2A1A4A2F_;Fbn;S20R5RdR4A3S16S1R11SaS1SdU0M4Vst;SeS1fS6S2aR1A1LX;M5R6A2R10RfR5RdA8S2bR4R3A5RcA4F_;F_;Ftp';FrhoX;Frho';FG2;S2G2S16S1ReSaS1SdG4Vst;SeG5RdRcRbRaA8S2dR2R1A5R9A4Ftp;FrhoE;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Proof.
  exact (depot_call_S 0%nat st tmax nx0 Hnx_0 NXG_0 (fun X : AA => bumpP X) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl)
           Htmax_0 X5ac C5ac NXEa_0 FBEa_0 F192a_0 FDEPa_0 FUNWa_0 WX5ra_0 DX5ra_0 SPL1a_0 SPL2a_0 SPL3a_0 SPL4a_0
           s4a_i R4a_i T4a_i HERa_0 HT4a_0 XX4a_0 FBX4a_0 Hchk4a_0 NX4a_0 WG10a_0 WG15a_0 WG12a_0 EXoa FAM4a_0 EXZa_0 NEWOa_0 XPosta_0
           FBT4a_0 XT4a_0 RB1a_0 RB2a_0 nobja PERM_nda_0 PERM_lta_0 PERM_cova_0 PERM_lena_0 MRG1a_0 MRG2a_0 MRG3a_0 MRG4a_0 sda_i ENT5a_0 SID5a_0 R4cova_0).
Qed.

Theorem depot_call_SE_0ha : ltac2:(tb__ "0|6|
S6S1aS2S10Q40M0A1M1S17OF_;S21VW;Vst;A2S25VW;Vst;A2S1bR6A1S7S2S2S11G1A1M2S13S0S0A2M3S1cG3R1S23R5A1A3S22R2S12S0S0SfG0RbA2S24SfG0S3RcPcA2A2A1A4A2F_;Fbn;S20R5RbR4A3S19S1SaS1SdU0M4Vst;SeS1fS6S2aR1A1LX;M5R6A2ReRdR5RbA8S2bR4R3A5RaA3F_;F_;Ftp';FrhoX;Frho';FG2;S2G2S19S1SaS1SdG4Vst;SeG5RbRaR9R8A8S2dR2R1A5R7A3Ftp;FrhoE;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;").
Proof.
  exact (depot_call_SE 0%nat st tmax nx0 Hnx_0 NXG_0 (fun X : AA => bumpP X) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl)
           Htmax_0 X5ac C5ac NXEa_0 FBEa_0 F192a_0 FDEPa_0 FUNWa_0 WX5ra_0 DX5ra_0 SPL1a_0 SPL2a_0 SPL3a_0 SPL4a_0
           s4a_i R4a_i T4a_i HERa_0 HT4a_0 XX4a_0 FBX4a_0 Hchk4a_0 NX4a_0 WG10a_0 WG15a_0 WG12a_0 EXoa FAM4a_0 EXZa_0 NEWOa_0 XPosta_0
           FBT4a_0 XT4a_0 RB1a_0 RB2a_0 nobja PERM_nda_0 PERM_lta_0 PERM_cova_0 PERM_lena_0 MRG1a_0 MRG2a_0 MRG3a_0 MRG4a_0 sda_i ENT5a_0 SID5a_0 R4cova_0).
Qed.

Theorem sec_g41_0ha : ltac2:(tb__ "0|6|
S17OF_;S6S1aS2S10Q40M0A1M1S18S21VW;Vst;A2S25VW;Vst;A2S1bR6A1ScS1R9SbR7A1A3S29S1RaSbR8A1A3S7S2S2S11G1A1M2S13S0S0A2M3S1cG3R1S23R5A1A3S22R2S12S0S0SfG0RdA2S24SfG0S3RePcA2A2A1A4A2F_;Fbn;S20R5RdR4A3S16S1R11SaS1SdU0M4Vst;SeS1fS6S2aR1A1LX;M5R6A2R10RfR5RdA8S2bR4R3A5RcA4F_;F_;Ftp';FrhoX;Frho';FG2;S2G2S16S1ReSaS1SdG4Vst;SeG5RdRcRbRaA8S34R2R1A5R9A4FtX;FrX;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Proof.
  exact (sec_g41 0%nat st tmax nx0 Hnx_0 NXG_0 (fun X : AA => bumpP X) T4ac U4ac X5ac C5ac WU4a_0 DU4a_0 NXU4a_0 HU4a_0 Cert5a_0 depot_call_S_0ha).
Qed.

Lemma EXZb_0 : ltac2:(tb__ "0|3|
S6S1aS2S10Q40A1M0S2S11G0A1S17S4S0SaS1SdU0Vst;SeS6R1LX;R9R8R7R6A8S2eR5R4R3A6S1cS4R3S30A3S1dS26S14S0S0S5R7R4A2M1A3R3A2S27R3S15S0S0G1A3A2A2S1eS1dS26S32R4A2S27R4S31A2A2S1dS26S9S8RcA1A1M2R4A2S27R4S28G2S33A2A2A2A2F_;F_;F_;Fz;Fo;Fw;Ftp;FrhoE;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a rhoE tp w o z Hw Ho Hz. pose proof (SPA_facts_hold segsA _ rhoE X5bc tp w Hw) as HF. destruct w as [tr [ms md]].
  pose proof (proj2 Hw) as HJ. cbn [w_tr w_cfg cfg_model fst snd] in HJ.
  pose proof (proj1 (Forall_forall _ _) HF _ FXBb_0) as HBR.
  destruct Ho as [<-|[<-|[<-|[]]]].
  - left. exact (ex2_band 0%nat st tmax nx0 Hnx_0 (fun X : AA => X) A Kc rho a rhoE tp tr md z HJ Hz).
  - left. exact (ex1_band 0%nat st tmax nx0 Hnx_0 (fun X : AA => X) A Kc rho a rhoE tp tr md z HJ Hz).
  - right. exact (exw_pab 0%nat st tmax nx0 Hnx_0 (fun X : AA => X) A Kc rho a rhoE tp tr md z (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) HJ HBR Hz).
Qed.

Theorem depot_call_S_0hb : ltac2:(tb__ "0|6|
S17OF_;S6S1aS2S10Q40M0A1M1S18S21VW;Vst;A2S25VW;Vst;A2S1bR6A1ScS1R9SbR7A1A3S29S1RaSbR8A1A3S7S2S2S11G1A1M2S13S0S0A2M3S1cG3R1S23R5A1A3S22R2S12S0S0SfG0RdA2S24SfG0S3RePcA2A2A1A4A2F_;Fbn;S20R5RdR4A3S16S1R11SaS1SdU0M4Vst;SeS1fS6R1LX;M5R6A2R10RfR5RdA8S2cR4R3A5RcA4F_;F_;Ftp';FrhoX;Frho';FG2;S2G2S16S1ReSaS1SdG4Vst;SeG5RdRcRbRaA8S2eR2R1A5R9A4Ftp;FrhoE;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Proof.
  exact (depot_call_S 0%nat st tmax nx0 Hnx_0 NXG_0 (fun X : AA => X) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl)
           Htmax_0 X5bc C5bc NXEb_0 FBEb_0 F192b_0 FDEPb_0 FUNWb_0 WX5rb_0 DX5rb_0 SPL1b_0 SPL2b_0 SPL3b_0 SPL4b_0
           s4b_i R4b_i T4b_i HERb_0 HT4b_0 XX4b_0 FBX4b_0 Hchk4b_0 NX4b_0 WG10b_0 WG15b_0 WG12b_0 EXob FAM4b_0 EXZb_0 NEWOb_0 XPostb_0
           FBT4b_0 XT4b_0 RB1b_0 RB2b_0 nobjb PERM_ndb_0 PERM_ltb_0 PERM_covb_0 PERM_lenb_0 MRG1b_0 MRG2b_0 MRG3b_0 MRG4b_0 sdb_i ENT5b_0 SID5b_0 R4covb_0).
Qed.

Theorem depot_call_SE_0hb : ltac2:(tb__ "0|6|
S6S1aS2S10Q40M0A1M1S17OF_;S21VW;Vst;A2S25VW;Vst;A2S1bR6A1S7S2S2S11G1A1M2S13S0S0A2M3S1cG3R1S23R5A1A3S22R2S12S0S0SfG0RbA2S24SfG0S3RcPcA2A2A1A4A2F_;Fbn;S20R5RbR4A3S19S1SaS1SdU0M4Vst;SeS1fS6R1LX;M5R6A2ReRdR5RbA8S2cR4R3A5RaA3F_;F_;Ftp';FrhoX;Frho';FG2;S2G2S19S1SaS1SdG4Vst;SeG5RbRaR9R8A8S2eR2R1A5R7A3Ftp;FrhoE;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;").
Proof.
  exact (depot_call_SE 0%nat st tmax nx0 Hnx_0 NXG_0 (fun X : AA => X) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl)
           Htmax_0 X5bc C5bc NXEb_0 FBEb_0 F192b_0 FDEPb_0 FUNWb_0 WX5rb_0 DX5rb_0 SPL1b_0 SPL2b_0 SPL3b_0 SPL4b_0
           s4b_i R4b_i T4b_i HERb_0 HT4b_0 XX4b_0 FBX4b_0 Hchk4b_0 NX4b_0 WG10b_0 WG15b_0 WG12b_0 EXob FAM4b_0 EXZb_0 NEWOb_0 XPostb_0
           FBT4b_0 XT4b_0 RB1b_0 RB2b_0 nobjb PERM_ndb_0 PERM_ltb_0 PERM_covb_0 PERM_lenb_0 MRG1b_0 MRG2b_0 MRG3b_0 MRG4b_0 sdb_i ENT5b_0 SID5b_0 R4covb_0).
Qed.

Theorem sec_g41_0hb : ltac2:(tb__ "0|6|
S17OF_;S6S1aS2S10Q40M0A1M1S18S21VW;Vst;A2S25VW;Vst;A2S1bR6A1ScS1R9SbR7A1A3S29S1RaSbR8A1A3S7S2S2S11G1A1M2S13S0S0A2M3S1cG3R1S23R5A1A3S22R2S12S0S0SfG0RdA2S24SfG0S3RePcA2A2A1A4A2F_;Fbn;S20R5RdR4A3S16S1R11SaS1SdU0M4Vst;SeS1fS6R1LX;M5R6A2R10RfR5RdA8S2cR4R3A5RcA4F_;F_;Ftp';FrhoX;Frho';FG2;S2G2S16S1ReSaS1SdG4Vst;SeG5RdRcRbRaA8S35R2R1A5R9A4FtX;FrX;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Proof.
  exact (sec_g41 0%nat st tmax nx0 Hnx_0 NXG_0 (fun X : AA => X) T4bc U4bc X5bc C5bc WU4b_0 DU4b_0 NXU4b_0 HU4b_0 Cert5b_0 depot_call_S_0hb).
Qed.
End INST.
End SpineCallocSec5J.

(* [comment removed for export] *)
Module SpineCallocSec5JL.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "sobj"; "obj_range"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "DG"; "aa_geom"; "ag_pab"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3"; "JGs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k1.SpineCallocSec3IL"; "nx0"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@Corelib.Init.Datatypes"; "list"; "pair"; "prod"; "fst"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "world"; "assn"; "etriple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "@Stdlib.Lists.List"; "In"; "@Corelib.Init.Logic"; "and"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k5.CDepotCallS"; "AXK"; "dlink"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase"; "stopJ_w"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger"; "sepZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dblocks"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "secmapsize"; "stopJ_stable"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.CSecBump"; "bumpP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ki.SpineCallocSec5IL"; "C5ac"; "C5bc"; "X5ac"; "X5bc"; "EXoa"; "EXob"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "kPtrArrayReserve"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineCallocSec4IL"; "T4ac"; "T4bc"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jx.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineCallocSec4IL.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require il.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CDepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ki.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.SpineCallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SegD_refl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.CSecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.CSecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k1.SpineCallocSec3IL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jx.SpineCallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineCallocSec4IL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.CertCallocSU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k6.SpineCallocSec5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CDepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k5.CDepotCallS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k9.SpineCallocSec6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ki.SpineCallocSec5IL.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import CallocBase2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ii.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.CallocPosts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 0. Let st : ustop := UStopLe. Let tmax : Z := 2.
Let GS0 : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3.GS nx0.

Lemma EXZa_0 : ltac2:(tb__ "0|3|
S6S1aS2S10Q40A1M0S2S11G0A1S17S4S0SaS1SdU0Vst;SeS6S2aR1A1LX;R9R8R7R6A8S2dR5R4R3A6S1cS4R3S2fA3S1dS26S14S0S0S5R7R4A2M1A3R3A2S27R3S15S0S0G1A3A2A2S1eS1dS26S32R4A2S27R4S31A2A2S1dS26S9S8RcA1A1M2R4A2S27R4S28G2S33A2A2A2A2F_;F_;F_;Fz;Fo;Fw;Ftp;FrhoE;Fa;Frho;FKc;FA;").
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
S17OF_;S6S1aS2S10Q40M0A1M1S18S21VW;Vst;A2S25VW;Vst;A2S1bR6A1ScS1R9SbR7A1A3S29S1RaSbR8A1A3S7S2S2S11G1A1M2S13S0S0A2M3S1cG3R1S23R5A1A3S22R2S12S0S0SfG0RdA2S24SfG0S3RePcA2A2A1A4A2F_;Fbn;S20R5RdR4A3S16S1R11SaS1SdU0M4Vst;SeS1fS6S2aR1A1LX;M5R6A2R10RfR5RdA8S2bR4R3A5RcA4F_;F_;Ftp';FrhoX;Frho';FG2;S2G2S16S1ReSaS1SdG4Vst;SeG5RdRcRbRaA8S2dR2R1A5R9A4Ftp;FrhoE;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Proof.
  exact (depot_call_S 0%nat st tmax nx0 Hnx_0 NXG_0 (fun X : AA => bumpP X) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl)
           Htmax_0 X5ac C5ac NXEa_0 FBEa_0 F192a_0 FDEPa_0 FUNWa_0 WX5ra_0 DX5ra_0 SPL1a_0 SPL2a_0 SPL3a_0 SPL4a_0
           s4a_i R4a_i T4a_i HERa_0 HT4a_0 XX4a_0 FBX4a_0 Hchk4a_0 NX4a_0 WG10a_0 WG15a_0 WG12a_0 EXoa FAM4a_0 EXZa_0 NEWOa_0 XPosta_0
           FBT4a_0 XT4a_0 RB1a_0 RB2a_0 nobja PERM_nda_0 PERM_lta_0 PERM_cova_0 PERM_lena_0 MRG1a_0 MRG2a_0 MRG3a_0 MRG4a_0 sda_i ENT5a_0 SID5a_0 R4cova_0).
Qed.

Theorem depot_call_SE_0la : ltac2:(tb__ "0|6|
S6S1aS2S10Q40M0A1M1S17OF_;S21VW;Vst;A2S25VW;Vst;A2S1bR6A1S7S2S2S11G1A1M2S13S0S0A2M3S1cG3R1S23R5A1A3S22R2S12S0S0SfG0RbA2S24SfG0S3RcPcA2A2A1A4A2F_;Fbn;S20R5RbR4A3S19S1SaS1SdU0M4Vst;SeS1fS6S2aR1A1LX;M5R6A2ReRdR5RbA8S2bR4R3A5RaA3F_;F_;Ftp';FrhoX;Frho';FG2;S2G2S19S1SaS1SdG4Vst;SeG5RbRaR9R8A8S2dR2R1A5R7A3Ftp;FrhoE;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;").
Proof.
  exact (depot_call_SE 0%nat st tmax nx0 Hnx_0 NXG_0 (fun X : AA => bumpP X) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl)
           Htmax_0 X5ac C5ac NXEa_0 FBEa_0 F192a_0 FDEPa_0 FUNWa_0 WX5ra_0 DX5ra_0 SPL1a_0 SPL2a_0 SPL3a_0 SPL4a_0
           s4a_i R4a_i T4a_i HERa_0 HT4a_0 XX4a_0 FBX4a_0 Hchk4a_0 NX4a_0 WG10a_0 WG15a_0 WG12a_0 EXoa FAM4a_0 EXZa_0 NEWOa_0 XPosta_0
           FBT4a_0 XT4a_0 RB1a_0 RB2a_0 nobja PERM_nda_0 PERM_lta_0 PERM_cova_0 PERM_lena_0 MRG1a_0 MRG2a_0 MRG3a_0 MRG4a_0 sda_i ENT5a_0 SID5a_0 R4cova_0).
Qed.

Theorem sec_g41_0la : ltac2:(tb__ "0|6|
S17OF_;S6S1aS2S10Q40M0A1M1S18S21VW;Vst;A2S25VW;Vst;A2S1bR6A1ScS1R9SbR7A1A3S29S1RaSbR8A1A3S7S2S2S11G1A1M2S13S0S0A2M3S1cG3R1S23R5A1A3S22R2S12S0S0SfG0RdA2S24SfG0S3RePcA2A2A1A4A2F_;Fbn;S20R5RdR4A3S16S1R11SaS1SdU0M4Vst;SeS1fS6S2aR1A1LX;M5R6A2R10RfR5RdA8S2bR4R3A5RcA4F_;F_;Ftp';FrhoX;Frho';FG2;S2G2S16S1ReSaS1SdG4Vst;SeG5RdRcRbRaA8S34R2R1A5R9A4FtX;FrX;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Proof.
  exact (sec_g41 0%nat st tmax nx0 Hnx_0 NXG_0 (fun X : AA => bumpP X) T4ac U4ac X5ac C5ac WU4a_0 DU4a_0 NXU4a_0 HU4a_0 Cert5a_0 depot_call_S_0la).
Qed.

Lemma EXZb_0 : ltac2:(tb__ "0|3|
S6S1aS2S10Q40A1M0S2S11G0A1S17S4S0SaS1SdU0Vst;SeS6R1LX;R9R8R7R6A8S2eR5R4R3A6S1cS4R3S30A3S1dS26S14S0S0S5R7R4A2M1A3R3A2S27R3S15S0S0G1A3A2A2S1eS1dS26S32R4A2S27R4S31A2A2S1dS26S9S8RcA1A1M2R4A2S27R4S28G2S33A2A2A2A2F_;F_;F_;Fz;Fo;Fw;Ftp;FrhoE;Fa;Frho;FKc;FA;").
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
S17OF_;S6S1aS2S10Q40M0A1M1S18S21VW;Vst;A2S25VW;Vst;A2S1bR6A1ScS1R9SbR7A1A3S29S1RaSbR8A1A3S7S2S2S11G1A1M2S13S0S0A2M3S1cG3R1S23R5A1A3S22R2S12S0S0SfG0RdA2S24SfG0S3RePcA2A2A1A4A2F_;Fbn;S20R5RdR4A3S16S1R11SaS1SdU0M4Vst;SeS1fS6R1LX;M5R6A2R10RfR5RdA8S2cR4R3A5RcA4F_;F_;Ftp';FrhoX;Frho';FG2;S2G2S16S1ReSaS1SdG4Vst;SeG5RdRcRbRaA8S2eR2R1A5R9A4Ftp;FrhoE;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Proof.
  exact (depot_call_S 0%nat st tmax nx0 Hnx_0 NXG_0 (fun X : AA => X) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl)
           Htmax_0 X5bc C5bc NXEb_0 FBEb_0 F192b_0 FDEPb_0 FUNWb_0 WX5rb_0 DX5rb_0 SPL1b_0 SPL2b_0 SPL3b_0 SPL4b_0
           s4b_i R4b_i T4b_i HERb_0 HT4b_0 XX4b_0 FBX4b_0 Hchk4b_0 NX4b_0 WG10b_0 WG15b_0 WG12b_0 EXob FAM4b_0 EXZb_0 NEWOb_0 XPostb_0
           FBT4b_0 XT4b_0 RB1b_0 RB2b_0 nobjb PERM_ndb_0 PERM_ltb_0 PERM_covb_0 PERM_lenb_0 MRG1b_0 MRG2b_0 MRG3b_0 MRG4b_0 sdb_i ENT5b_0 SID5b_0 R4covb_0).
Qed.

Theorem depot_call_SE_0lb : ltac2:(tb__ "0|6|
S6S1aS2S10Q40M0A1M1S17OF_;S21VW;Vst;A2S25VW;Vst;A2S1bR6A1S7S2S2S11G1A1M2S13S0S0A2M3S1cG3R1S23R5A1A3S22R2S12S0S0SfG0RbA2S24SfG0S3RcPcA2A2A1A4A2F_;Fbn;S20R5RbR4A3S19S1SaS1SdU0M4Vst;SeS1fS6R1LX;M5R6A2ReRdR5RbA8S2cR4R3A5RaA3F_;F_;Ftp';FrhoX;Frho';FG2;S2G2S19S1SaS1SdG4Vst;SeG5RbRaR9R8A8S2eR2R1A5R7A3Ftp;FrhoE;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;").
Proof.
  exact (depot_call_SE 0%nat st tmax nx0 Hnx_0 NXG_0 (fun X : AA => X) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl)
           Htmax_0 X5bc C5bc NXEb_0 FBEb_0 F192b_0 FDEPb_0 FUNWb_0 WX5rb_0 DX5rb_0 SPL1b_0 SPL2b_0 SPL3b_0 SPL4b_0
           s4b_i R4b_i T4b_i HERb_0 HT4b_0 XX4b_0 FBX4b_0 Hchk4b_0 NX4b_0 WG10b_0 WG15b_0 WG12b_0 EXob FAM4b_0 EXZb_0 NEWOb_0 XPostb_0
           FBT4b_0 XT4b_0 RB1b_0 RB2b_0 nobjb PERM_ndb_0 PERM_ltb_0 PERM_covb_0 PERM_lenb_0 MRG1b_0 MRG2b_0 MRG3b_0 MRG4b_0 sdb_i ENT5b_0 SID5b_0 R4covb_0).
Qed.

Theorem sec_g41_0lb : ltac2:(tb__ "0|6|
S17OF_;S6S1aS2S10Q40M0A1M1S18S21VW;Vst;A2S25VW;Vst;A2S1bR6A1ScS1R9SbR7A1A3S29S1RaSbR8A1A3S7S2S2S11G1A1M2S13S0S0A2M3S1cG3R1S23R5A1A3S22R2S12S0S0SfG0RdA2S24SfG0S3RePcA2A2A1A4A2F_;Fbn;S20R5RdR4A3S16S1R11SaS1SdU0M4Vst;SeS1fS6R1LX;M5R6A2R10RfR5RdA8S2cR4R3A5RcA4F_;F_;Ftp';FrhoX;Frho';FG2;S2G2S16S1ReSaS1SdG4Vst;SeG5RdRcRbRaA8S35R2R1A5R9A4FtX;FrX;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Proof.
  exact (sec_g41 0%nat st tmax nx0 Hnx_0 NXG_0 (fun X : AA => X) T4bc U4bc X5bc C5bc WU4b_0 DU4b_0 NXU4b_0 HU4b_0 Cert5b_0 depot_call_S_0lb).
Qed.
End INST.
End SpineCallocSec5JL.

(* [comment removed for export] *)
Module SpineCallocSec5JLW1.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "sobj"; "obj_range"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "DG"; "aa_geom"; "ag_pab"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3"; "JGs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k1.SpineCallocSec3ILW1"; "nx0"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@Corelib.Init.Datatypes"; "list"; "pair"; "prod"; "fst"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "world"; "assn"; "etriple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "@Stdlib.Lists.List"; "In"; "@Corelib.Init.Logic"; "and"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k5.CDepotCallS"; "AXK"; "dlink"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase"; "stopJ_w"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger"; "sepZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dblocks"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "secmapsize"; "stopJ_stable"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.CSecBump"; "bumpP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kn.SpineCallocSec5ILW1"; "C5ac"; "C5bc"; "X5ac"; "X5bc"; "EXoa"; "EXob"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "kPtrArrayReserve"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineCallocSec4ILW1"; "T4ac"; "T4bc"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jx.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineCallocSec4ILW1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require il.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CDepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kn.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.SpineCallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SegD_refl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.CSecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.CSecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k1.SpineCallocSec3ILW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jx.SpineCallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineCallocSec4ILW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.CertCallocSU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k6.SpineCallocSec5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CDepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k5.CDepotCallS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k9.SpineCallocSec6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kn.SpineCallocSec5ILW1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import CallocBase2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ii.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.CallocPosts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 1. Let st : ustop := UStopLeOrPc. Let tmax : Z := 3.
Let GS0 : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3.GS nx0.

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

Theorem depot_call_S_1la : ltac2:(tb__ "0|6|
S17OF_;S6S1aS2S10Q40M0A1M1S18S21VW;Vst;A2S25VW;Vst;A2S1bR6A1ScS1R9SbR7A1A3S29S1RaSbR8A1A3S7S2S2S11G1A1M2S13S0S0A2M3S1cG3R1S23R5A1A3S22R2S12S0S0SfG0RdA2S24SfG0S3RePcA2A2A1A4A2F_;Fbn;S20R5RdR4A3S16S1R11SaS1SdU1M4Vst;SeS1fS6S2aR1A1LX;M5R6A2R10RfR5RdA8S2bR4R3A5RcA4F_;F_;Ftp';FrhoX;Frho';FG2;S2G2S16S1ReSaS1SdG4Vst;SeG5RdRcRbRaA8S2dR2R1A5R9A4Ftp;FrhoE;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Proof.
  exact (depot_call_S 1%nat st tmax nx0 Hnx_0 NXG_0 (fun X : AA => bumpP X) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl)
           Htmax_0 X5ac C5ac NXEa_0 FBEa_0 F192a_0 FDEPa_0 FUNWa_0 WX5ra_0 DX5ra_0 SPL1a_0 SPL2a_0 SPL3a_0 SPL4a_0
           s4a_i R4a_i T4a_i HERa_0 HT4a_0 XX4a_0 FBX4a_0 Hchk4a_0 NX4a_0 WG10a_0 WG15a_0 WG12a_0 EXoa FAM4a_0 EXZa_0 NEWOa_0 XPosta_0
           FBT4a_0 XT4a_0 RB1a_0 RB2a_0 nobja PERM_nda_0 PERM_lta_0 PERM_cova_0 PERM_lena_0 MRG1a_0 MRG2a_0 MRG3a_0 MRG4a_0 sda_i ENT5a_0 SID5a_0 R4cova_0).
Qed.

Theorem depot_call_SE_1la : ltac2:(tb__ "0|6|
S6S1aS2S10Q40M0A1M1S17OF_;S21VW;Vst;A2S25VW;Vst;A2S1bR6A1S7S2S2S11G1A1M2S13S0S0A2M3S1cG3R1S23R5A1A3S22R2S12S0S0SfG0RbA2S24SfG0S3RcPcA2A2A1A4A2F_;Fbn;S20R5RbR4A3S19S1SaS1SdU1M4Vst;SeS1fS6S2aR1A1LX;M5R6A2ReRdR5RbA8S2bR4R3A5RaA3F_;F_;Ftp';FrhoX;Frho';FG2;S2G2S19S1SaS1SdG4Vst;SeG5RbRaR9R8A8S2dR2R1A5R7A3Ftp;FrhoE;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;").
Proof.
  exact (depot_call_SE 1%nat st tmax nx0 Hnx_0 NXG_0 (fun X : AA => bumpP X) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl)
           Htmax_0 X5ac C5ac NXEa_0 FBEa_0 F192a_0 FDEPa_0 FUNWa_0 WX5ra_0 DX5ra_0 SPL1a_0 SPL2a_0 SPL3a_0 SPL4a_0
           s4a_i R4a_i T4a_i HERa_0 HT4a_0 XX4a_0 FBX4a_0 Hchk4a_0 NX4a_0 WG10a_0 WG15a_0 WG12a_0 EXoa FAM4a_0 EXZa_0 NEWOa_0 XPosta_0
           FBT4a_0 XT4a_0 RB1a_0 RB2a_0 nobja PERM_nda_0 PERM_lta_0 PERM_cova_0 PERM_lena_0 MRG1a_0 MRG2a_0 MRG3a_0 MRG4a_0 sda_i ENT5a_0 SID5a_0 R4cova_0).
Qed.

Theorem sec_g41_1la : ltac2:(tb__ "0|6|
S17OF_;S6S1aS2S10Q40M0A1M1S18S21VW;Vst;A2S25VW;Vst;A2S1bR6A1ScS1R9SbR7A1A3S29S1RaSbR8A1A3S7S2S2S11G1A1M2S13S0S0A2M3S1cG3R1S23R5A1A3S22R2S12S0S0SfG0RdA2S24SfG0S3RePcA2A2A1A4A2F_;Fbn;S20R5RdR4A3S16S1R11SaS1SdU1M4Vst;SeS1fS6S2aR1A1LX;M5R6A2R10RfR5RdA8S2bR4R3A5RcA4F_;F_;Ftp';FrhoX;Frho';FG2;S2G2S16S1ReSaS1SdG4Vst;SeG5RdRcRbRaA8S34R2R1A5R9A4FtX;FrX;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Proof.
  exact (sec_g41 1%nat st tmax nx0 Hnx_0 NXG_0 (fun X : AA => bumpP X) T4ac U4ac X5ac C5ac WU4a_0 DU4a_0 NXU4a_0 HU4a_0 Cert5a_0 depot_call_S_1la).
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

Theorem depot_call_S_1lb : ltac2:(tb__ "0|6|
S17OF_;S6S1aS2S10Q40M0A1M1S18S21VW;Vst;A2S25VW;Vst;A2S1bR6A1ScS1R9SbR7A1A3S29S1RaSbR8A1A3S7S2S2S11G1A1M2S13S0S0A2M3S1cG3R1S23R5A1A3S22R2S12S0S0SfG0RdA2S24SfG0S3RePcA2A2A1A4A2F_;Fbn;S20R5RdR4A3S16S1R11SaS1SdU1M4Vst;SeS1fS6R1LX;M5R6A2R10RfR5RdA8S2cR4R3A5RcA4F_;F_;Ftp';FrhoX;Frho';FG2;S2G2S16S1ReSaS1SdG4Vst;SeG5RdRcRbRaA8S2eR2R1A5R9A4Ftp;FrhoE;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Proof.
  exact (depot_call_S 1%nat st tmax nx0 Hnx_0 NXG_0 (fun X : AA => X) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl)
           Htmax_0 X5bc C5bc NXEb_0 FBEb_0 F192b_0 FDEPb_0 FUNWb_0 WX5rb_0 DX5rb_0 SPL1b_0 SPL2b_0 SPL3b_0 SPL4b_0
           s4b_i R4b_i T4b_i HERb_0 HT4b_0 XX4b_0 FBX4b_0 Hchk4b_0 NX4b_0 WG10b_0 WG15b_0 WG12b_0 EXob FAM4b_0 EXZb_0 NEWOb_0 XPostb_0
           FBT4b_0 XT4b_0 RB1b_0 RB2b_0 nobjb PERM_ndb_0 PERM_ltb_0 PERM_covb_0 PERM_lenb_0 MRG1b_0 MRG2b_0 MRG3b_0 MRG4b_0 sdb_i ENT5b_0 SID5b_0 R4covb_0).
Qed.

Theorem depot_call_SE_1lb : ltac2:(tb__ "0|6|
S6S1aS2S10Q40M0A1M1S17OF_;S21VW;Vst;A2S25VW;Vst;A2S1bR6A1S7S2S2S11G1A1M2S13S0S0A2M3S1cG3R1S23R5A1A3S22R2S12S0S0SfG0RbA2S24SfG0S3RcPcA2A2A1A4A2F_;Fbn;S20R5RbR4A3S19S1SaS1SdU1M4Vst;SeS1fS6R1LX;M5R6A2ReRdR5RbA8S2cR4R3A5RaA3F_;F_;Ftp';FrhoX;Frho';FG2;S2G2S19S1SaS1SdG4Vst;SeG5RbRaR9R8A8S2eR2R1A5R7A3Ftp;FrhoE;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;").
Proof.
  exact (depot_call_SE 1%nat st tmax nx0 Hnx_0 NXG_0 (fun X : AA => X) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl)
           Htmax_0 X5bc C5bc NXEb_0 FBEb_0 F192b_0 FDEPb_0 FUNWb_0 WX5rb_0 DX5rb_0 SPL1b_0 SPL2b_0 SPL3b_0 SPL4b_0
           s4b_i R4b_i T4b_i HERb_0 HT4b_0 XX4b_0 FBX4b_0 Hchk4b_0 NX4b_0 WG10b_0 WG15b_0 WG12b_0 EXob FAM4b_0 EXZb_0 NEWOb_0 XPostb_0
           FBT4b_0 XT4b_0 RB1b_0 RB2b_0 nobjb PERM_ndb_0 PERM_ltb_0 PERM_covb_0 PERM_lenb_0 MRG1b_0 MRG2b_0 MRG3b_0 MRG4b_0 sdb_i ENT5b_0 SID5b_0 R4covb_0).
Qed.

Theorem sec_g41_1lb : ltac2:(tb__ "0|6|
S17OF_;S6S1aS2S10Q40M0A1M1S18S21VW;Vst;A2S25VW;Vst;A2S1bR6A1ScS1R9SbR7A1A3S29S1RaSbR8A1A3S7S2S2S11G1A1M2S13S0S0A2M3S1cG3R1S23R5A1A3S22R2S12S0S0SfG0RdA2S24SfG0S3RePcA2A2A1A4A2F_;Fbn;S20R5RdR4A3S16S1R11SaS1SdU1M4Vst;SeS1fS6R1LX;M5R6A2R10RfR5RdA8S2cR4R3A5RcA4F_;F_;Ftp';FrhoX;Frho';FG2;S2G2S16S1ReSaS1SdG4Vst;SeG5RdRcRbRaA8S35R2R1A5R9A4FtX;FrX;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Proof.
  exact (sec_g41 1%nat st tmax nx0 Hnx_0 NXG_0 (fun X : AA => X) T4bc U4bc X5bc C5bc WU4b_0 DU4b_0 NXU4b_0 HU4b_0 Cert5b_0 depot_call_S_1lb).
Qed.
End INST.
End SpineCallocSec5JLW1.

(* [comment removed for export] *)
Module SpineCallocSec5JW1.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "sobj"; "obj_range"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "DG"; "aa_geom"; "ag_pab"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3"; "JGs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k1.SpineCallocSec3IW1"; "nx0"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@Corelib.Init.Datatypes"; "list"; "pair"; "prod"; "fst"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "world"; "assn"; "etriple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "@Stdlib.Lists.List"; "In"; "@Corelib.Init.Logic"; "and"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k5.CDepotCallS"; "AXK"; "dlink"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase"; "stopJ_w"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger"; "sepZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dblocks"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "secmapsize"; "stopJ_stable"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.CSecBump"; "bumpP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kn.SpineCallocSec5IW1"; "C5ac"; "C5bc"; "X5ac"; "X5bc"; "EXoa"; "EXob"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "kPtrArrayReserve"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineCallocSec4IW1"; "T4ac"; "T4bc"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jx.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineCallocSec4IW1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require il.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CDepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kn.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.SpineCallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SegD_refl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.CSecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.CSecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k1.SpineCallocSec3IW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jx.SpineCallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineCallocSec4IW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.CertCallocSU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k6.SpineCallocSec5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CDepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k5.CDepotCallS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k9.SpineCallocSec6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kn.SpineCallocSec5IW1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import CallocBase2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ii.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.CallocPosts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 1. Let st : ustop := UStopLeOrPc. Let tmax : Z := 3.
Let GS0 : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3.GS nx0.

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
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "False"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_setS"; "leafA"; "la_state"; "entailsA"; "ax_base"; "mkLeafA"; "xr_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "valuation"; "sv"; "sprop"; "ss_next"; "ss_facts"; "rw"; "cell"; "SLit"; "rm"; "swf"; "sprop_below"; "ss_objs"; "eval"; "holds"; "rl"; "obj_range"; "DUnknown"; "mkObj"; "SPNot"; "SVar"; "odefault"; "ranges_disjoint"; "sstate"; "DZero"; "@Corelib.Init.Datatypes"; "bool"; "true"; "list"; "cons"; "nil"; "prod"; "pair"; "option"; "app"; "nat"; "Some"; "length"; "None"; "andb"; "S"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "LQA"; "jpredA"; "stableA"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_geom"; "ageom"; "aa_sec"; "sec_chunk"; "aa_Km"; "aa_depot"; "DG"; "aa_ptr_committed"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "mem_keptA"; "V_RES"; "base_sv"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "seq"; "@Stdlib.Lists.List"; "In"; "forallb"; "incl"; "existsb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3"; "skel"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "div"; "lt"; "of_nat"; "eqb"; "leb"; "ltb"; "modulo"; "mul"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "secmapsize"; "stopJ_stable"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase"; "stopJ_w"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP"; "MSENT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "Sh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocST"; "O_1"; "carveS"; "O_2"; "Pret_ms"; "BR"; "Pret_mz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.im.CertCallocSV"; "F_A"; "L3"; "CPC"; "F_B"; "O_3"; "O_UBs"; "B3"; "F_par"; "O_3b"; "perm7"; "B4"; "PGST"; "UBs"; "a2e6"; "a2e8"; "osplit"; "BP9"; "F_g7"; "F_g8"; "F_g9"; "L3b"; "O_4z"; "RSF"; "a0e7"; "a2e7"; "fx8"; "ic_c1"; "ic_c2"; "ic_nch"; "ic_nres"; "ic_pg"; "ic_rs"; "mc_cptr"; "mc_idx"; "mc_magic"; "mc_map"; "mc_ms"; "mc_ns"; "mc_size"; "mc_sizehi"; "mc_state"; "mc_type"; "sel7"; "xc_map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger"; "sepZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dblocks"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "LQPA"; "jpostA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.CSecOKInv"; "bumpV"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3"; "SKEL0"; "range_noband"; "JGs"; "GS"; "slink"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ki.SpineCallocSec7"; "idxsF"; "idxsU"; "S2F"; "KUB"; "XF_of"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "ltb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Str_memsetZ"; "Pre_mszA"; "Posts_mszA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "nodupN"; "select"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "wsub"; "wsub_get"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "RsSymJump"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.CallocPosts"; "Lc_ok"; "JLc_ok"; "PFc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CDepotCall"; "isSome"; "omrg"; "oreb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k5.CDepotCallS"; "AXK"; "dlink"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSS"; "nxS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.CertCallocSU"; "DPENT"; "F_g4"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ki.SpineCallocSec6L"; "F_low"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "merge_objs_at"; "rebase_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM"; "IMG_M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jv.SpineCallocSec2"; "IMG_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ko.SpineCallocSecE3.SEC6E"; "slink_refl_of"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildM.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineCallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.SpineCallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineCallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.SpineCallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jd.SpineCallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.RebuildN.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ki.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jb.CInvEnsure OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.CertCallocSU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jx.SpineCallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k6.SpineCallocSec5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.id.DepotKP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k5.CDepotCallS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.im.CertCallocSV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.CRebuildS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ki.SpineCallocSec6L OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ki.SpineCallocSec7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k1.SpineCallocSecE1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k6.SpineCallocSecE2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ki.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k6.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k9.SpineCallocSec6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ki.SpineCallocSec6L OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ki.SpineCallocSec7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k1.SpineCallocSecE1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k6.SpineCallocSecE2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
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
Let GS : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3.GS nx.
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
Let GS : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3.GS nx.
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
Module SpineCallocSec6IL.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_setS"; "leafA"; "ax_X"; "entailsA"; "la_state"; "xr_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "sprop"; "cell"; "ss_next"; "ss_facts"; "ss_objs"; "swf"; "SLit"; "SVar"; "sprop_below"; "DUnknown"; "mkObj"; "SPNot"; "sstate"; "DZero"; "SAlu"; "SPBranch"; "c_off"; "c_val"; "ob_cells"; "sv_eqb"; "@Corelib.Init.Datatypes"; "nil"; "true"; "bool"; "cons"; "list"; "nat"; "prod"; "app"; "option"; "pair"; "Some"; "length"; "false"; "andb"; "S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k1.SpineCallocSec3IL"; "nx0"; "@Stdlib.Lists.List"; "In"; "forallb"; "incl"; "existsb"; "find"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@Corelib.Lists.ListDef"; "map"; "seq"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ki.SpineCallocSec7"; "KEPTF"; "KUB"; "idxsF"; "idxsU"; "S2F"; "XF_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.im.CertCallocSV"; "O_UBs"; "F_par"; "CPC"; "UBs"; "osplit"; "O_3"; "perm7"; "F_A"; "L3"; "O_3b"; "PGST"; "RSF"; "ic_c1"; "ic_c2"; "ic_nch"; "ic_nres"; "ic_pg"; "ic_rs"; "mc_cptr"; "mc_idx"; "mc_magic"; "mc_map"; "mc_ms"; "mc_ns"; "mc_size"; "mc_sizehi"; "mc_state"; "mc_type"; "B3"; "B4"; "BP9"; "F_g7"; "F_g8"; "F_g9"; "L3b"; "O_4z"; "a0e7"; "a2e6"; "a2e7"; "a2e8"; "fx8"; "sel7"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3"; "skel"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA"; "runsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ko.SpineCallocSec6IL.INST"; "FFfa"; "FFfb"; "FFqa"; "FFqb"; "mcfa"; "mcfb"; "mcqa"; "mcqb"; "CT6a"; "CT6b"; "CT7a"; "CT7b"; "CT8a"; "CT8b"; "CO6a"; "CO6b"; "CO8a"; "CO8b"; "swcfa"; "swcfb"; "swcqa"; "swcqb"; "CM7a"; "CM7b"; "D6La"; "D6Lb"; "D7La"; "D7Lb"; "D8La"; "D8Lb"; "E9pa"; "E9pb"; "U7a"; "U7b"; "U8a"; "U8b"; "U9a"; "U9b"; "c1fa"; "c1fb"; "c1qa"; "c1qb"; "FXPa"; "FXPb"; "n7a"; "n7b"; "D6a"; "D6b"; "D7a"; "D7b"; "D8a"; "D8b"; "S9bfa"; "S9bfb"; "S9bqa"; "S9bqb"; "CO7a"; "CO7b"; "CO9pa"; "CO9pb"; "E6a"; "E6b"; "ET7a"; "ET7b"; "ET8a"; "ET8b"; "PXa"; "PXb"; "tybfa"; "tybfb"; "tybqa"; "tybqb"; "C5Aa"; "C5Ab"; "CR7a"; "CR7b"; "CS7a"; "CS7b"; "D9fa"; "D9fb"; "D9qa"; "D9qb"; "R6a"; "R6b"; "R7a"; "R7b"; "R8a"; "R8b"; "T6a"; "T6b"; "T7a"; "T7b"; "T8a"; "T8b"; "perm9fa"; "perm9fb"; "perm9qa"; "perm9qb"; "s6a"; "s6b"; "s7a"; "s7b"; "s8a"; "s8b"; "E9fa"; "E9fb"; "E9qa"; "E9qb"; "S9afa"; "S9afb"; "S9aqa"; "S9aqb"; "Y6Aa"; "Y6Ab"; "iMfa"; "iMfb"; "iMqa"; "iMqb"; "s6Aa"; "s6Ab"; "sFfa"; "sFfb"; "sFqa"; "sFqb"; "c2fa"; "c2fb"; "c2qa"; "c2qb"; "c4fa"; "c4fb"; "c4qa"; "c4qb"; "c5fa"; "c5fb"; "c5qa"; "c5qb"; "run6Aa"; "run6Ab"; "run7a"; "run7b"; "run8a"; "run8b"; "run9a"; "run9b"; "run9qa"; "run9qb"; "runFfa"; "runFfb"; "runFqa"; "runFqb"; "xcfa"; "xcfb"; "xcqa"; "xcqb";
"@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "ltb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "select"; "nodupN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP"; "MSENT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "V_RES"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocST"; "O_1"; "carveS"; "BR"; "O_2"; "Pret_ms"; "Pret_mz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3"; "SKEL0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ki.SpineCallocSec6L"; "F_low"; "F_g7L"; "F_g8L"; "F_g9L"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Str_memsetZ"; "Pre_mszA"; "Posts_mszA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSS"; "V_NRES"; "V_NCH"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CDepotCall"; "isSome"; "omrg"; "oreb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.CallocPosts"; "Lc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1"; "RT_m1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "@Stdlib.ZArith.BinInt.Z"; "eqb"; "leb"; "ltb"; "modulo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ki.SpineCallocSec5IL"; "C5ac"; "C5bc"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_EQ"; "aluop"; "mulop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "merge_objs_at"; "rebase_obj_at"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jx.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineCallocSec4IL.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require il.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CDepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require im.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ki.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.SpineCallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jd.SpineCallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SegD_refl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.CSecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.CSecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k1.SpineCallocSec3IL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jx.SpineCallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineCallocSec4IL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.CertCallocSU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k6.SpineCallocSec5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CDepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k5.CDepotCallS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.im.CertCallocSV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k9.SpineCallocSec6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ki.SpineCallocSec6L OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ki.SpineCallocSec5IL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ki.SpineCallocSec7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import CallocBase2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ii.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.CallocPosts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition tyb_of (mc : list cell) : Z := ltac2:(tb__ "0|4|
S28SdA1S35Lx;S34SdSdS1fS1cR1A1S12Z17f1A1A2Lc;Vmc;A3SdSbS35Lx;S1dR1A1S35R1Lt;S36Z0M0Li;S13bSbSbG0Lb;La;M1Lop;M2G2S13cG1Lop;M3G3S22S37SbG0La;Lw;Lsgn;S36SbS35G0Lk;Li;Ll;Xbx8Lc;G0X28x2").
Definition cells_at (i : nat) (F : axst) : list cell := ltac2:(tb__ "0|0|
S1eS3bSaVi;S10S2VF;A1A1S117S2fA1A4A1").

Section INST.
Let W : list ulink := Wcan 0. Let st : ustop := UStopLe. Let tmax : Z := 2.
Let GS0 : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3.GS nx0.

Definition PXa : list sobj := [O_blk].
Definition FXPa : list sprop := ltac2:(tb__ "0|0|
S23ScS1bS13aS13S129A1S13S128A1A3S20ScA1A3").

Definition C5Aa : axst := Eval vm_compute in (ax_add_facts (F_A nx0) C5ac).
Lemma HC5Aa_0 : ltac2:(tb__ "0|0|
S0S3S6fS4aS2fA1S137A2Sb9A3"). Proof. vm_cast_no_check (@eq_refl _ (C5Aa)). Qed.
Lemma FBAa_0 : ltac2:(tb__ "0|0|
S0S22S31ScS14SeS2S137A1A1A1S4aS2fA1A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FLOWa_0 : ltac2:(tb__ "0|0|
S30ScS11eS2fA1SfS2S137A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Definition run6Aa : option (list leafA) := Eval vm_compute in (runT6 C5Aa).
Lemma run6Aa__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S5A1A1M0A1S70S38Ufa0S23S35S112S20S35A1A3S23S3Sb9S20S3A1A3A4S23G0Sf9S20G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run6Aa]). Qed.
Definition Y6Aa : axst := Eval vm_compute in (leafS 0 run6Aa).
Lemma Cert6Aa_0 : ltac2:(tb__ "0|1|
S0S22S6eS38Ufa0S23S35S112S20S35A1A3VGS0;S23S3Sb9S20S3A1M0A3S23S3Se1G0A3A6S21A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] GS0 [C5Aa] [Y6Aa] [run6Aa]); [exact run6Aa__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition E6a : axst := Eval vm_compute in (rmF (F_A nx0) Y6Aa).
Definition s6Aa : wsub := Eval vm_compute in (infer_sub GS0 (ax_S Y6Aa) (ax_S E6a)).
Lemma E6Aa_0 : ltac2:(tb__ "0|0|
S0S22S7Se1SadSe7A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma I6Aa_0 : ltac2:(tb__ "0|0|
S0S22S12cSe7VGS0;A2S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition CT6a : axst := Eval vm_compute in (rstS E6a ru6 []).
Definition CO6a : axst := Eval vm_compute in (carveS CT6a (O_3 nx0)).
Lemma WC6a_0 : ltac2:(tb__ "0|0|
S0S22S11S2S79A1A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DF6a_0 : ltac2:(tb__ "0|4|
S0S28S26S24S26SbSbA2M0A1M1S24ScA1M2A2M3A1S3cS2SadA1S2S79A1A2S2aG3S29G1G2S23G0S29SbSbS68S2fA1S4bA4S20G0A1A3S20ScA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(a2e6 nx0, L3)], @nil sprop))). Qed.
Lemma NX6a_0 : ltac2:(tb__ "0|0|
S0S36SeS2S79A1A1SeS2SadA1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S E6a))). Qed.
Lemma HC6a_0 : ltac2:(tb__ "0|0|
S0S3S4SadS2S79A1A2S79A3"). Proof. vm_cast_no_check (@eq_refl _ (CT6a)). Qed.
Lemma SK6a_0 : ltac2:(tb__ "0|1|
S0S24S26S26SbSbA2SbA2M0A1S39SaG0S6dS10S2S79A1A1A4S39SaG0S6dS27SaS23SaS11aS2fA1S23SaS117S2fA1S20SaA1A3A3S27SaS11dU0S2fA2Sb3A3A3A4A3"). Proof. vm_cast_no_check (@eq_refl _ (map skel ([O_2 nx0; O_1 nx0] ++ SKEL0 0%nat nx0 ++ PXa))). Qed.
Lemma FC6a_0 : ltac2:(tb__ "0|0|
S32ScS27ScS115VW;Vst;A2S114S113A1A3SfS2S79A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FX6a_0 : ltac2:(tb__ "0|0|
S32ScS9bSfS2S79A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma XC6a_0 : ltac2:(tb__ "0|1|
S0S24S26SbSbA2M0A1S6S79A1S20G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma HCO6a_0 : ltac2:(tb__ "0|0|
S0S3S118S79S16S5fS2fA1S12Z0A1S4bS20SdA1S15A5A2S7fA3"). Proof. vm_cast_no_check (@eq_refl _ (CO6a)). Qed.
Lemma WCO6a_0 : ltac2:(tb__ "0|0|
S0S22S11S2S7fA1A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition s6a : wsub := Eval vm_compute in (callsub CO6a Pre_memsetA).
Definition R6a : list sobj := Eval vm_compute in (callR CO6a Pre_memsetA s6a).
Definition T6a : axst := Eval vm_compute in (callT CO6a Pre_memsetA Pret_ms s6a R6a).
Lemma He6a_0 : ltac2:(tb__ "0|1|
S0S28S24SaA1M0A1S126S7fS10dSd3A3S2aG0Sc3A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some R6a)). Qed.
Lemma Hchk6a_0 : ltac2:(tb__ "0|0|
S0S22S125S7fS10dSd3Sc3S39S5S3S8S10eA4A5S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HT6a_0 : ltac2:(tb__ "0|0|
S0S3S127Sd3S10dS11bS7fSc3A5Sc9A3"). Proof. vm_cast_no_check (@eq_refl _ (T6a)). Qed.
Lemma FBC6a_0 : ltac2:(tb__ "0|1|
S0S22S31ScS14SeS2S7fA1M0A1A1SfG0A1A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT6a_0 : ltac2:(tb__ "0|0|
S0S22S31ScS14SeS2Sc9A1A1A1SfS2S7fA1A1A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXC6a_0 : ltac2:(tb__ "0|0|
S0S22S12aVGS0;SeS2S7fA1A1A2S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition D6a : axst := Eval vm_compute in (ax_with_facts T6a (ss_facts (ax_S CO6a))).
Lemma HD6a_0 : ltac2:(tb__ "0|0|
S0S3S124Sc9SfS2S7fA1A1A2S9fA3"). Proof. vm_cast_no_check (@eq_refl _ (D6a)). Qed.

Definition D6La : axst := Eval vm_compute in (rstS D6a [] (F_g7L nx0)).
Lemma WD6La_0 : ltac2:(tb__ "0|0|
S0S22S11S2S89A1A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DD6La_0 : ltac2:(tb__ "0|4|
S0S28S26S24S26SbSbA2M0A1M1S24ScA1M2A2M3A1S3cS2S9fA1S2S89A1A2S2aG3S29G1G2S20G0A1S11fS2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g7L nx0))). Qed.
Lemma NXD6La_0 : ltac2:(tb__ "0|0|
S0S36SeS2S89A1A1SeS2S9fA1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D6a))). Qed.
Lemma HD6La_0 : ltac2:(tb__ "0|0|
S0S3S4S9fS2S89A1A2S89A3"). Proof. vm_cast_no_check (@eq_refl _ (D6La)). Qed.
Lemma FLOW6a_0 : ltac2:(tb__ "0|0|
S30ScS11eS2fA1SfS2S9fA1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Definition U7a : axst := Eval vm_compute in (U7p nx0 D6La).
Lemma WU7a_0 : ltac2:(tb__ "0|0|
S0S22S11S2S91A1A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DU7a_0 : ltac2:(tb__ "0|4|
S0S28S26S24S26SbSbA2M0A1M1S24ScA1M2A2M3A1S3cS2S89A1S2S91A1A2S2aG3S29G1G2S20G0A1S62S2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g7 nx0))). Qed.
Lemma NXU7a_0 : ltac2:(tb__ "0|0|
S0S36SeS2S91A1A1SeS2S89A1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D6La))). Qed.
Lemma HU7a_0 : ltac2:(tb__ "0|0|
S0S3S4S89S2S91A1A2S91A3"). Proof. vm_cast_no_check (@eq_refl _ (U7a)). Qed.
Definition run7a : option (list leafA) := Eval vm_compute in (runT6 U7a).
Lemma run7a__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S5A1A1M0A1S70S38Ufa0S23S35S112S20S35A1A3S23S3S91S20S3A1A3A4S23G0SfbS20G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run7a]). Qed.
Definition ET7a : axst := Eval vm_compute in (leafS 0 run7a).
Lemma Cert7a_0 : ltac2:(tb__ "0|1|
S0S22S6eS38Ufa0S23S35S112S20S35A1A3VGS0;S23S3S91S20S3A1M0A3S23S3SafG0A3A6S21A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] GS0 [U7a] [ET7a] [run7a]); [exact run7a__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition CT7a : axst := Eval vm_compute in (rstS ET7a (ru7 nx0) []).
Definition CO7a : axst := Eval vm_compute in (carveS CT7a (O_3n nx0)).
Definition CR7a : axst := Eval vm_compute in (CDepotCall.oreb CO7a 1).
Definition n7a : nat := Eval vm_compute in (length (ss_objs (ax_S CR7a))).
Definition CS7a : axst := Eval vm_compute in (sel7 CR7a).
Definition CM7a : axst := Eval vm_compute in (CDepotCall.omrg CS7a 1).
Lemma WC7a_0 : ltac2:(tb__ "0|0|
S0S22S11S2S7bA1A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DF7a_0 : ltac2:(tb__ "0|4|
S0S28S26S24S26SbSbA2M0A1M1S24ScA1M2A2M3A1S3cS2SafA1S2S7bA1A2S2aG3S29G1G2S23G0S29SbSbS67S2fA1S119S2fA1A4S23G0S29SbSbS69S2fA1S65A4S20G0A1A3A3S20ScA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(a0e7 nx0, BR nx0); (a2e7 nx0, L3b)], @nil sprop))). Qed.
Lemma NX7a_0 : ltac2:(tb__ "0|0|
S0S36SeS2S7bA1A1SeS2SafA1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S ET7a))). Qed.
Lemma HC7a_0 : ltac2:(tb__ "0|0|
S0S3S4SafS2S7bA1A2S7bA3"). Proof. vm_cast_no_check (@eq_refl _ (CT7a)). Qed.
Lemma SK7a_0 : ltac2:(tb__ "0|1|
S0S24S26S26SbSbA2SbA2M0A1S39SaG0S6dS10S2S7bA1A1A4S39SaG0S6dS27SaS23SaS48S2fA1S23SaS11aS2fA1S23SaS117S2fA1S20SaA1A3A3A3S27SaS11dU0S2fA2Sb3A3A3A4A3"). Proof. vm_cast_no_check (@eq_refl _ (map skel ([O_3 nx0; O_2 nx0; O_1 nx0] ++ SKEL0 0%nat nx0 ++ PXa))). Qed.
Lemma FC7a_0 : ltac2:(tb__ "0|0|
S32ScS27ScS115VW;Vst;A2S114S113A1A3SfS2S7bA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FX7a_0 : ltac2:(tb__ "0|0|
S32ScS9bSfS2S7bA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma XC7a_0 : ltac2:(tb__ "0|1|
S0S24S26SbSbA2M0A1S6S7bA1S20G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma HCO7a_0 : ltac2:(tb__ "0|0|
S0S3S118S7bS16S119S2fA1S12Z0A1S12Z100A1S20SdA1S15A5A2Sa9A3"). Proof. vm_cast_no_check (@eq_refl _ (CO7a)). Qed.
Lemma WCO7a_0 : ltac2:(tb__ "0|0|
S0S22S11S2Sa9A1A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RB7a_0 : ltac2:(tb__ "0|0|
S0S22S12dS18S13eS2Sa9A1U1A2A2S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HCR7a_0 : ltac2:(tb__ "0|0|
S0S3S12fSa9U1A2SbbA3"). Proof. vm_cast_no_check (@eq_refl _ (CR7a)). Qed.
Lemma LEN7a_0 : ltac2:(tb__ "0|0|
S0S25S2bSaS10S2SbbA1A1A2S9dA3"). Proof. vm_cast_no_check (@eq_refl _ (n7a)). Qed.
Lemma PERM_nd7a_0 : ltac2:(tb__ "0|0|
S0S22S110S49S9dA1A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma PERM_lt7a_0 : ltac2:(tb__ "0|0|
S0S22S31S25S25S10cR1S9dA2Li;S49S9dA1A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma PERM_cov7a_0 : ltac2:(tb__ "0|0|
S0S22S31S25S25S33S25S10bR1A1S49S9dA1A3Li;S3aU0S9dA2A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HCS7a_0 : ltac2:(tb__ "0|0|
S0S3S6cSbbA1SbdA3"). Proof. vm_cast_no_check (@eq_refl _ (CS7a)). Qed.
Lemma MRG7a_0 : ltac2:(tb__ "0|0|
S0S22S12dS18S13dS2SbdA1U1A2A2S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HCM7a_0 : ltac2:(tb__ "0|0|
S0S3S12eSbdU1A2S87A3"). Proof. vm_cast_no_check (@eq_refl _ (CM7a)). Qed.
Definition s7a : wsub := Eval vm_compute in (callsub CM7a Pre_memsetA).
Definition R7a : list sobj := Eval vm_compute in (callR CM7a Pre_memsetA s7a).
Definition T7a : axst := Eval vm_compute in (callT CM7a Pre_memsetA Pret_ms s7a R7a).
Lemma He7a_0 : ltac2:(tb__ "0|1|
S0S28S24SaA1M0A1S126S87S10dSd5A3S2aG0Sc5A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some R7a)). Qed.
Lemma Hchk7a_0 : ltac2:(tb__ "0|0|
S0S22S125S87S10dSd5Sc5S39S5S3S8S10eA4A5S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HT7a_0 : ltac2:(tb__ "0|0|
S0S3S127Sd5S10dS11bS87Sc5A5ScbA3"). Proof. vm_cast_no_check (@eq_refl _ (T7a)). Qed.
Lemma FBC7a_0 : ltac2:(tb__ "0|1|
S0S22S31ScS14SeS2S87A1M0A1A1SfG0A1A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT7a_0 : ltac2:(tb__ "0|0|
S0S22S31ScS14SeS2ScbA1A1A1SfS2S87A1A1A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXC7a_0 : ltac2:(tb__ "0|0|
S0S22S12aVGS0;SeS2S87A1A1A2S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition D7a : axst := Eval vm_compute in (ax_with_facts T7a (ss_facts (ax_S CM7a))).
Lemma HD7a_0 : ltac2:(tb__ "0|0|
S0S3S124ScbSfS2S87A1A1A2Sa1A3"). Proof. vm_cast_no_check (@eq_refl _ (D7a)). Qed.

Definition D7La : axst := Eval vm_compute in (rstS D7a [] (F_g8L nx0)).
Lemma WD7La_0 : ltac2:(tb__ "0|0|
S0S22S11S2S8bA1A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DD7La_0 : ltac2:(tb__ "0|4|
S0S28S26S24S26SbSbA2M0A1M1S24ScA1M2A2M3A1S3cS2Sa1A1S2S8bA1A2S2aG3S29G1G2S20G0A1S120S2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g8L nx0))). Qed.
Lemma NXD7La_0 : ltac2:(tb__ "0|0|
S0S36SeS2S8bA1A1SeS2Sa1A1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D7a))). Qed.
Lemma HD7La_0 : ltac2:(tb__ "0|0|
S0S3S4Sa1S2S8bA1A2S8bA3"). Proof. vm_cast_no_check (@eq_refl _ (D7La)). Qed.
Lemma FLOW7a_0 : ltac2:(tb__ "0|0|
S30ScS11eS2fA1SfS2Sa1A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Definition U8a : axst := Eval vm_compute in (U8p nx0 D7La).
Lemma WU8a_0 : ltac2:(tb__ "0|0|
S0S22S11S2S93A1A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DU8a_0 : ltac2:(tb__ "0|4|
S0S28S26S24S26SbSbA2M0A1M1S24ScA1M2A2M3A1S3cS2S8bA1S2S93A1A2S2aG3S29G1G2S20G0A1S63S2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g8 nx0))). Qed.
Lemma NXU8a_0 : ltac2:(tb__ "0|0|
S0S36SeS2S93A1A1SeS2S8bA1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D7La))). Qed.
Lemma HU8a_0 : ltac2:(tb__ "0|0|
S0S3S4S8bS2S93A1A2S93A3"). Proof. vm_cast_no_check (@eq_refl _ (U8a)). Qed.
Definition run8a : option (list leafA) := Eval vm_compute in (runT6 U8a).
Lemma run8a__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S5A1A1M0A1S70S38Ufa0S23S35S112S20S35A1A3S23S3S93S20S3A1A3A4S23G0SfdS20G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run8a]). Qed.
Definition ET8a : axst := Eval vm_compute in (leafS 0 run8a).
Lemma Cert8a_0 : ltac2:(tb__ "0|1|
S0S22S6eS38Ufa0S23S35S112S20S35A1A3VGS0;S23S3S93S20S3A1M0A3S23S3Sb1G0A3A6S21A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] GS0 [U8a] [ET8a] [run8a]); [exact run8a__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition CT8a : axst := Eval vm_compute in (CT8p nx0 ET8a).
Definition CO8a : axst := Eval vm_compute in (carveS CT8a (O_4 nx0)).
Lemma WC8a_0 : ltac2:(tb__ "0|0|
S0S22S11S2S7dA1A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DF8a_0 : ltac2:(tb__ "0|4|
S0S28S26S24S26SbSbA2M0A1M1S24ScA1M2A2M3A1S3cS2Sb1A1S2S7dA1A2S2aG3S29G1G2S20G0A1S6bS2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), fx8 nx0))). Qed.
Lemma NX8a_0 : ltac2:(tb__ "0|0|
S0S36SeS2S7dA1A1SeS2Sb1A1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S ET8a))). Qed.
Lemma HC8a_0 : ltac2:(tb__ "0|0|
S0S3S4Sb1S2S7dA1A2S7dA3"). Proof. vm_cast_no_check (@eq_refl _ (CT8a)). Qed.
Lemma SK8a_0 : ltac2:(tb__ "0|1|
S0S24S26S26SbSbA2SbA2M0A1S39SaG0S6dS10S2S7dA1A1A4S39SaG0S6dS27SaS23SaS4cS2fA1S23SaS48S2fA1S23SaS117S2fA1S20SaA1A3A3A3S27SaS11dU0S2fA2Sb3A3A3A4A3"). Proof. vm_cast_no_check (@eq_refl _ (map skel ([O_3b nx0; O_3 nx0; O_1 nx0] ++ SKEL0 0%nat nx0 ++ PXa))). Qed.
Lemma FC8a_0 : ltac2:(tb__ "0|0|
S32ScS27ScS115VW;Vst;A2S114S113A1A3SfS2S7dA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FX8a_0 : ltac2:(tb__ "0|0|
S32ScS9bSfS2S7dA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma XC8a_0 : ltac2:(tb__ "0|1|
S0S24S26SbSbA2M0A1S6S7dA1S20G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma HCO8a_0 : ltac2:(tb__ "0|0|
S0S3S118S7dS16S60S2fA1S12Z0A1S6aS2fA1S20SdA1S15A5A2S81A3"). Proof. vm_cast_no_check (@eq_refl _ (CO8a)). Qed.
Lemma WCO8a_0 : ltac2:(tb__ "0|0|
S0S22S11S2S81A1A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition s8a : wsub := Eval vm_compute in (callsub CO8a Pre_mszA).
Definition R8a : list sobj := Eval vm_compute in (callR CO8a Pre_mszA s8a).
Definition T8a : axst := Eval vm_compute in (callT CO8a Pre_mszA Pret_mz s8a R8a).
Lemma He8a_0 : ltac2:(tb__ "0|1|
S0S28S24SaA1M0A1S126S81S122Sd7A3S2aG0Sc7A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some R8a)). Qed.
Lemma Hchk8a_0 : ltac2:(tb__ "0|0|
S0S22S125S81S122Sd7Sc7S39S5S3S8S123A4A5S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HT8a_0 : ltac2:(tb__ "0|0|
S0S3S127Sd7S122S11cS81Sc7A5ScdA3"). Proof. vm_cast_no_check (@eq_refl _ (T8a)). Qed.
Lemma FBC8a_0 : ltac2:(tb__ "0|1|
S0S22S31ScS14SeS2S81A1M0A1A1SfG0A1A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT8a_0 : ltac2:(tb__ "0|0|
S0S22S31ScS14SeS2ScdA1A1A1SfS2S81A1A1A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXC8a_0 : ltac2:(tb__ "0|0|
S0S22S12aVGS0;SeS2S81A1A1A2S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition D8a : axst := Eval vm_compute in (ax_with_facts T8a (ss_facts (ax_S CO8a))).
Lemma HD8a_0 : ltac2:(tb__ "0|0|
S0S3S124ScdSfS2S81A1A1A2Sa3A3"). Proof. vm_cast_no_check (@eq_refl _ (D8a)). Qed.

Definition D8La : axst := Eval vm_compute in (rstS D8a [] (F_g9L nx0)).
Lemma WD8La_0 : ltac2:(tb__ "0|0|
S0S22S11S2S8dA1A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DD8La_0 : ltac2:(tb__ "0|4|
S0S28S26S24S26SbSbA2M0A1M1S24ScA1M2A2M3A1S3cS2Sa3A1S2S8dA1A2S2aG3S29G1G2S20G0A1S121S2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g9L nx0))). Qed.
Lemma NXD8La_0 : ltac2:(tb__ "0|0|
S0S36SeS2S8dA1A1SeS2Sa3A1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D8a))). Qed.
Lemma HD8La_0 : ltac2:(tb__ "0|0|
S0S3S4Sa3S2S8dA1A2S8dA3"). Proof. vm_cast_no_check (@eq_refl _ (D8La)). Qed.
Lemma FLOW8a_0 : ltac2:(tb__ "0|0|
S30ScS11eS2fA1SfS2Sa3A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Definition U9a : axst := Eval vm_compute in (U9p nx0 D8La).
Lemma WU9a_0 : ltac2:(tb__ "0|0|
S0S22S11S2S95A1A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DU9a_0 : ltac2:(tb__ "0|4|
S0S28S26S24S26SbSbA2M0A1M1S24ScA1M2A2M3A1S3cS2S8dA1S2S95A1A2S2aG3S29G1G2S20G0A1S64S2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g9 nx0))). Qed.
Lemma NXU9a_0 : ltac2:(tb__ "0|0|
S0S36SeS2S95A1A1SeS2S8dA1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D8La))). Qed.
Lemma HU9a_0 : ltac2:(tb__ "0|0|
S0S3S4S8dS2S95A1A2S95A3"). Proof. vm_cast_no_check (@eq_refl _ (U9a)). Qed.
Definition run9a : option (list leafA) := Eval vm_compute in (runT9 U9a).
Lemma run9a__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S5A1A1M0A1S70S38Ufa0S23S35S45S23S35S4dS20S35A1A3A3S23S3S95S20S3A1A3A4S23G0SffS20G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run9a]). Qed.
Definition E9fa : axst := Eval vm_compute in (leafS 0 run9a).
Definition E9pa : axst := Eval vm_compute in (leafS 1 run9a).
Lemma Cert9a_0 : ltac2:(tb__ "0|1|
S0S22S6eS38Ufa0S23S35S45S23S35S4dS20S35A1A3A3VGS0;S23S3S95S20S3A1M0A3S23S3Sd9S23S3S8fG0A3A3A6S21A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [CPC; PGST] GS0 [U9a] [E9fa; E9pa] [run9a]); [exact run9a__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma SK9a_0 : ltac2:(tb__ "0|1|
S0S24S26S26SbSbA2SbA2M0A1S39SaG0S6dS10S2S8fA1A1A4S39SaG0S6dS27SaS23SaS66S2fA1S23SaS4cS2fA1S23SaS48S2fA1S23SaS117S2fA1S20SaA1A3A3A3A3S27SaS11dU0S2fA2Sb3A3A3A4A3"). Proof. vm_cast_no_check (@eq_refl _ (map skel ([O_4z nx0; O_3b nx0; O_3 nx0; O_1 nx0] ++ SKEL0 0%nat nx0 ++ PXa))). Qed.
Lemma FC9a_0 : ltac2:(tb__ "0|0|
S32ScS27ScS115VW;Vst;A2S114S113A1A3SfS2S8fA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FX9a_0 : ltac2:(tb__ "0|0|
S32ScS9bSfS2S8fA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FP9a_0 : ltac2:(tb__ "0|0|
S30ScS17S44A1SfS2S8fA1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Lemma XC9a_0 : ltac2:(tb__ "0|1|
S0S24S26SbSbA2M0A1S6S8fA1S20G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Definition CO9pa : axst := Eval vm_compute in (carveS E9pa (mkObj (BP9 nx0) (SLit 0) (SLit 1) [] DUnknown)).
Lemma HCO9a_0 : ltac2:(tb__ "0|0|
S0S3S118S8fS16S61S2fA1S12Z0A1S12Z1A1S20SdA1S15A5A2SabA3"). Proof. vm_cast_no_check (@eq_refl _ (CO9pa)). Qed.
Lemma WCO9a_0 : ltac2:(tb__ "0|0|
S0S22S11S2SabA1A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition run9qa : option (list leafA) := Eval vm_compute in (runT9q CO9pa).
Lemma run9qa__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S5A1A1M0A1S70S38Ufa0S23S35S45S20S35A1A3S23S3SabS20S3A1A3A4S23G0S101S20G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run9qa]). Qed.
Definition E9qa : axst := Eval vm_compute in (leafS 0 run9qa).
Lemma Cert9qa_0 : ltac2:(tb__ "0|1|
S0S22S6eS38Ufa0S23S35S45S20S35A1A3VGS0;S23S3SabS20S3A1M0A3S23S3SdbG0A3A6S21A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [CPC] GS0 [CO9pa] [E9qa] [run9qa]); [exact run9qa__runeq | vm_cast_no_check (eq_refl true)]. Qed.

Definition iMfa : nat := Eval vm_compute in (find_map nx0 (ss_objs (ax_S E9fa)) 0).
Definition S9afa : axst := Eval vm_compute in (osplit E9fa iMfa (SLit 6144)).
Definition S9bfa : axst := Eval vm_compute in (osplit S9afa (S iMfa) (SLit 10240)).
Lemma HS9afa_0 : ltac2:(tb__ "0|0|
S0S3S47Sd9Se3S12Z1800A1A3SddA3"). Proof. vm_cast_no_check (@eq_refl _ (S9afa)). Qed.
Lemma HS9bfa_0 : ltac2:(tb__ "0|0|
S0S3S47SddS2eSe3A1S12Z2800A1A3Sa5A3"). Proof. vm_cast_no_check (@eq_refl _ (S9bfa)). Qed.
Definition perm9fa : list nat := Eval vm_compute in (S iMfa :: seq 0 (S iMfa) ++ seq (S (S iMfa)) (length (ss_objs (ax_S S9bfa)) - S (S iMfa))).
Definition D9fa : axst := Eval vm_compute in (ax_setS S9bfa (set_objs (ax_S S9bfa) (select (ss_objs (ax_S S9bfa)) perm9fa))).
Lemma HD9fa_0 : ltac2:(tb__ "0|1|
S0S3S4Sa5S111S2Sa5A1M0S10fS10G0A1ScfA2A2A2SbfA3"). Proof. vm_cast_no_check (@eq_refl _ (D9fa)). Qed.
Lemma NDpfa_0 : nodupN perm9fa = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDpfa_0 : ltac2:(tb__ "0|0|
S0S22S31S25S25S10cR1S2bSaS10S2Sa5A1A1A2A2Li;ScfA3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVpfa_0 : ltac2:(tb__ "0|0|
S0S22S31S25S25S33S25S10bR1A1ScfA3Li;S3aU0S2bSaS10S2Sa5A1A1A2A2A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition runFfa : option (list leafA) := Eval vm_compute in (runTF D9fa).
Lemma runFfa__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S5A1A1M0A1S70S38Ufa0S20S35A1S23S3SbfS20S3A1A3A4S23G0S103S20G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [runFfa]). Qed.
Definition FFfa : axst := Eval vm_compute in (leafS 0 runFfa).
Lemma CertFfa_0 : ltac2:(tb__ "0|1|
S0S22S6eS38Ufa0S20S35A1VGS0;S23S3SbfS20S3A1M0A3S23S3S71G0A3A6S21A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [] GS0 [D9fa] [FFfa] [runFfa]); [exact runFfa__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition swcfa : list cell := Eval vm_compute in (cells_at 5 FFfa).
Definition c1fa : list cell := Eval vm_compute in (cells_at 38 FFfa).
Definition c2fa : list cell := Eval vm_compute in (cells_at 39 FFfa).
Definition c4fa : list cell := Eval vm_compute in (cells_at 41 FFfa).
Definition c5fa : list cell := Eval vm_compute in (cells_at 45 FFfa).
Definition mcfa : list cell := Eval vm_compute in (cells_at 46 FFfa).
Definition xcfa : list cell := Eval vm_compute in (cells_at 48 FFfa).
Definition tybfa : Z := Eval vm_compute in (tyb_of mcfa).
Lemma SELFfa_0 : ltac2:(tb__ "0|0|
S0S24SaA1S10fS10S2S71A1A1S3fU0S2cA2A2S27SaS3dVW;S83A2S27SaS131S4eS2fS97SedSf1Sf5S75S107Z20000S19S2cAaA3A3A3"). Proof. vm_cast_no_check (@eq_refl _ (KEPTF W swcfa ++ RT_m1 ++ RSF nx0 c1fa c2fa c4fa c5fa mcfa xcfa 131072 DZero false)). Qed.
Lemma NDFfa_0 : ltac2:(tb__ "0|0|
S0S22S110S3fU0S2cA2A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDFfa_0 : ltac2:(tb__ "0|0|
S0S22S31S25S25S10cR1S2bSaS10S2S71A1A1A2A2Li;S3fU0S2cA2A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVFfa_0 : ltac2:(tb__ "0|1|
S0S22S31S25S25S33S25S10bR1A1S3fU0M0S2cA2A3Li;S3aG0S2bSaS10S2S71A1A1A2A2A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XFnfa_0 : ltac2:(tb__ "0|1|
S0S24S26SbSbA2M0A1S6S71A1S20G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma BFbfa_0 : ax_base FFfa = base_sv. Proof. vm_cast_no_check (@eq_refl _ (base_sv)). Qed.
Lemma FPFfa_0 : ltac2:(tb__ "0|0|
S32ScS27ScS115VW;Vst;A2S114S113A1A3SfS2S71A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FXFfa_0 : ltac2:(tb__ "0|0|
S32ScS9bSfS2S71A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FPARfa_0 : ltac2:(tb__ "0|0|
S30ScS22ScL_;S2cS17S44A1S44X22x2SfS2S71A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Lemma Hc1fa_0 : ltac2:(tb__ "0|0|
S1S30SdS53S97A3S1S30SdS4fS97A3S1S30SdS50S97A3S1S30SdS54S97A3S1S30SdS52S1aS139S13S128A1S12Z4000A1A3A1S97A3S30SdS51S97A3A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (ic_pg) c1fa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c1) c1fa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c2) c1fa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_rs) c1fa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_nres (SAlu ALU_ADD (SVar V_NRES) (SLit 16384))) c1fa ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (ic_nch) c1fa ltac:(vm_cast_no_check (eq_refl true)))))))). Qed.
Lemma Hmcfa_0 : ltac2:(tb__ "0|0|
S1S30SdS58S2fA1S75A3S1S30SdS59S75A3S1S30SdS5aS75A3S1S30SdS56S75A3S1S30SdS57S75A3S1S30SdS55S2fA1S75A3S1S30SdS5dS75A3S1S30SdS5eSb5A1S75A3S1S30SdS5cS75A3S30SdS5bS75A3A2A2A2A2A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (mc_map nx0) mcfa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ms) mcfa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ns) mcfa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_idx) mcfa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_magic) mcfa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_cptr nx0) mcfa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_state) mcfa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_type tybfa) mcfa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_sizehi) mcfa ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (mc_size) mcfa ltac:(vm_cast_no_check (eq_refl true)))))))))))). Qed.
Lemma Htybfa_0 : ltac2:(tb__ "0|0|
S0S22S2dS2dS134Z0Sb5A2S135Sb5Z100A2A2S133S136Sb5Z4A2Z1A2A2S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma Hxcfa_0 : In (xc_map nx0) xcfa. Proof. exact (In_of_cellb (xc_map nx0) xcfa ltac:(vm_cast_no_check (eq_refl true))). Qed.
Lemma WCUfa_0 : ltac2:(tb__ "0|0|
S0S22S11S111S2S71A1S27SaS3dVW;S83A2S23SaS43S2fA1S20SaA1A3A3A2A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SELUfa_0 : ltac2:(tb__ "0|0|
S0S24SaA1S10fS27SaS3dVW;S83A2S23SaS43S2fA1S20SaA1A3A3S40U0A1A2S3eVW;S83S2fA3A3"). Proof. vm_cast_no_check (@eq_refl _ (KUB W swcfa nx0)). Qed.
Lemma NDUfa_0 : nodupN (idxsU 0%nat) = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDUfa_0 : ltac2:(tb__ "0|0|
S0S22S31S25S25S10cR1S2bSaS27SaS3dVW;S83A2S23SaS43S2fA1S20SaA1A3A3A2A2Li;S40U0A1A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVUfa_0 : ltac2:(tb__ "0|1|
S0S22S31S25S25S33S25S10bR1A1S40U0M0A1A3Li;S3aG0S2bSaS27SaS3dVW;S83A2S23SaS43S2fA1S20SaA1A3A3A2A2A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W9fa_0 : ltac2:(tb__ "0|0|
S0S22S11S41S71S3eVW;S83S2fA3A2A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D9fa_0 : ltac2:(tb__ "0|5|
S0S28S26S24S26SbSbA2M0A1M1S24ScA1M2A2M3A1S3cS111S2S71A1S3eVW;S83S2fA3M4A2S41S71G4A2A2S2aG3S29G1G2S23G0S29SbSbS12S132A1S13P18A1A4S20G0A1A3S20ScA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(SLit TP_A, SVar 24)], @nil sprop))). Qed.
Lemma XB9fa_0 : ltac2:(tb__ "0|0|
S0S22S9SeS2S71A1A1S29SbSbS46S2fA1S13PcA1A4A2S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sFfa : wsub := Eval vm_compute in (infer_sub NF (S2F FFfa (KUB W swcfa nx0)) (ax_S (Lc_ok W st))).
Lemma ENT9fa_0 : ltac2:(tb__ "0|0|
S0S22S7S42S71S3eVW;S83S2fA3S2fA3S130VW;Vst;A2Se9A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID9fa_0 : wsub_idc sFfa = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma G110fa_0 : ltac2:(tb__ "0|0|
S0SbS12bSe9S116A2S46S2fA1A3"). Proof. vm_cast_no_check (@eq_refl _ (UBs nx0)). Qed.

Definition iMqa : nat := Eval vm_compute in (find_map nx0 (ss_objs (ax_S E9qa)) 0).
Definition S9aqa : axst := Eval vm_compute in (osplit E9qa iMqa (SLit 6144)).
Definition S9bqa : axst := Eval vm_compute in (osplit S9aqa (S iMqa) (SLit 10240)).
Lemma HS9aqa_0 : ltac2:(tb__ "0|0|
S0S3S47SdbSe5S12Z1800A1A3SdfA3"). Proof. vm_cast_no_check (@eq_refl _ (S9aqa)). Qed.
Lemma HS9bqa_0 : ltac2:(tb__ "0|0|
S0S3S47SdfS2eSe5A1S12Z2800A1A3Sa7A3"). Proof. vm_cast_no_check (@eq_refl _ (S9bqa)). Qed.
Definition perm9qa : list nat := Eval vm_compute in (S iMqa :: seq 0 (S iMqa) ++ seq (S (S iMqa)) (length (ss_objs (ax_S S9bqa)) - S (S iMqa))).
Definition D9qa : axst := Eval vm_compute in (ax_setS S9bqa (set_objs (ax_S S9bqa) (select (ss_objs (ax_S S9bqa)) perm9qa))).
Lemma HD9qa_0 : ltac2:(tb__ "0|1|
S0S3S4Sa7S111S2Sa7A1M0S10fS10G0A1Sd1A2A2A2Sc1A3"). Proof. vm_cast_no_check (@eq_refl _ (D9qa)). Qed.
Lemma NDpqa_0 : nodupN perm9qa = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDpqa_0 : ltac2:(tb__ "0|0|
S0S22S31S25S25S10cR1S2bSaS10S2Sa7A1A1A2A2Li;Sd1A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVpqa_0 : ltac2:(tb__ "0|0|
S0S22S31S25S25S33S25S10bR1A1Sd1A3Li;S3aU0S2bSaS10S2Sa7A1A1A2A2A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition runFqa : option (list leafA) := Eval vm_compute in (runTF D9qa).
Lemma runFqa__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S5A1A1M0A1S70S38Ufa0S20S35A1S23S3Sc1S20S3A1A3A4S23G0S105S20G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [runFqa]). Qed.
Definition FFqa : axst := Eval vm_compute in (leafS 0 runFqa).
Lemma CertFqa_0 : ltac2:(tb__ "0|1|
S0S22S6eS38Ufa0S20S35A1VGS0;S23S3Sc1S20S3A1M0A3S23S3S73G0A3A6S21A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [] GS0 [D9qa] [FFqa] [runFqa]); [exact runFqa__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition swcqa : list cell := Eval vm_compute in (cells_at 5 FFqa).
Definition c1qa : list cell := Eval vm_compute in (cells_at 38 FFqa).
Definition c2qa : list cell := Eval vm_compute in (cells_at 39 FFqa).
Definition c4qa : list cell := Eval vm_compute in (cells_at 41 FFqa).
Definition c5qa : list cell := Eval vm_compute in (cells_at 45 FFqa).
Definition mcqa : list cell := Eval vm_compute in (cells_at 46 FFqa).
Definition xcqa : list cell := Eval vm_compute in (cells_at 48 FFqa).
Definition tybqa : Z := Eval vm_compute in (tyb_of mcqa).
Lemma SELFqa_0 : ltac2:(tb__ "0|0|
S0S24SaA1S10fS10S2S73A1A1S3fU0S21A2A2S27SaS3dVW;S85A2S27SaS131S4eS2fS99SefSf3Sf7S77S109Z20000S19S21AaA3A3A3"). Proof. vm_cast_no_check (@eq_refl _ (KEPTF W swcqa ++ RT_m1 ++ RSF nx0 c1qa c2qa c4qa c5qa mcqa xcqa 131072 DZero true)). Qed.
Lemma NDFqa_0 : ltac2:(tb__ "0|0|
S0S22S110S3fU0S21A2A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDFqa_0 : ltac2:(tb__ "0|0|
S0S22S31S25S25S10cR1S2bSaS10S2S73A1A1A2A2Li;S3fU0S21A2A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVFqa_0 : ltac2:(tb__ "0|1|
S0S22S31S25S25S33S25S10bR1A1S3fU0M0S21A2A3Li;S3aG0S2bSaS10S2S73A1A1A2A2A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XFnqa_0 : ltac2:(tb__ "0|1|
S0S24S26SbSbA2M0A1S6S73A1S20G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma BFbqa_0 : ax_base FFqa = base_sv. Proof. vm_cast_no_check (@eq_refl _ (base_sv)). Qed.
Lemma FPFqa_0 : ltac2:(tb__ "0|0|
S32ScS27ScS115VW;Vst;A2S114S113A1A3SfS2S73A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FXFqa_0 : ltac2:(tb__ "0|0|
S32ScS9bSfS2S73A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FPARqa_0 : ltac2:(tb__ "0|0|
S30ScS22ScL_;S21S17S44A1S44X22x2SfS2S73A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Lemma Hc1qa_0 : ltac2:(tb__ "0|0|
S1S30SdS53S99A3S1S30SdS4fS99A3S1S30SdS50S99A3S1S30SdS54S99A3S1S30SdS52S1aS139S13S128A1S12Z4000A1A3A1S99A3S30SdS51S99A3A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (ic_pg) c1qa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c1) c1qa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c2) c1qa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_rs) c1qa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_nres (SAlu ALU_ADD (SVar V_NRES) (SLit 16384))) c1qa ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (ic_nch) c1qa ltac:(vm_cast_no_check (eq_refl true)))))))). Qed.
Lemma Hmcqa_0 : ltac2:(tb__ "0|0|
S1S30SdS58S2fA1S77A3S1S30SdS59S77A3S1S30SdS5aS77A3S1S30SdS56S77A3S1S30SdS57S77A3S1S30SdS55S2fA1S77A3S1S30SdS5dS77A3S1S30SdS5eSb7A1S77A3S1S30SdS5cS77A3S30SdS5bS77A3A2A2A2A2A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (mc_map nx0) mcqa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ms) mcqa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ns) mcqa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_idx) mcqa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_magic) mcqa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_cptr nx0) mcqa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_state) mcqa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_type tybqa) mcqa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_sizehi) mcqa ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (mc_size) mcqa ltac:(vm_cast_no_check (eq_refl true)))))))))))). Qed.
Lemma Htybqa_0 : ltac2:(tb__ "0|0|
S0S22S2dS2dS134Z0Sb7A2S135Sb7Z100A2A2S133S136Sb7Z4A2Z1A2A2S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma Hxcqa_0 : In (xc_map nx0) xcqa. Proof. exact (In_of_cellb (xc_map nx0) xcqa ltac:(vm_cast_no_check (eq_refl true))). Qed.
Lemma WCUqa_0 : ltac2:(tb__ "0|0|
S0S22S11S111S2S73A1S27SaS3dVW;S85A2S23SaS43S2fA1S20SaA1A3A3A2A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SELUqa_0 : ltac2:(tb__ "0|0|
S0S24SaA1S10fS27SaS3dVW;S85A2S23SaS43S2fA1S20SaA1A3A3S40U0A1A2S3eVW;S85S2fA3A3"). Proof. vm_cast_no_check (@eq_refl _ (KUB W swcqa nx0)). Qed.
Lemma NDUqa_0 : nodupN (idxsU 0%nat) = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDUqa_0 : ltac2:(tb__ "0|0|
S0S22S31S25S25S10cR1S2bSaS27SaS3dVW;S85A2S23SaS43S2fA1S20SaA1A3A3A2A2Li;S40U0A1A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVUqa_0 : ltac2:(tb__ "0|1|
S0S22S31S25S25S33S25S10bR1A1S40U0M0A1A3Li;S3aG0S2bSaS27SaS3dVW;S85A2S23SaS43S2fA1S20SaA1A3A3A2A2A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W9qa_0 : ltac2:(tb__ "0|0|
S0S22S11S41S73S3eVW;S85S2fA3A2A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D9qa_0 : ltac2:(tb__ "0|5|
S0S28S26S24S26SbSbA2M0A1M1S24ScA1M2A2M3A1S3cS111S2S73A1S3eVW;S85S2fA3M4A2S41S73G4A2A2S2aG3S29G1G2S23G0S29SbSbS12S132A1S13P18A1A4S20G0A1A3S20ScA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(SLit TP_A, SVar 24)], @nil sprop))). Qed.
Lemma XB9qa_0 : ltac2:(tb__ "0|0|
S0S22S9SeS2S73A1A1S29SbSbS46S2fA1S13PcA1A4A2S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sFqa : wsub := Eval vm_compute in (infer_sub NF (S2F FFqa (KUB W swcqa nx0)) (ax_S (Lc_ok W st))).
Lemma ENT9qa_0 : ltac2:(tb__ "0|0|
S0S22S7S42S73S3eVW;S85S2fA3S2fA3S130VW;Vst;A2SebA3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID9qa_0 : wsub_idc sFqa = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma G110qa_0 : ltac2:(tb__ "0|0|
S0SbS12bSebS116A2S46S2fA1A3"). Proof. vm_cast_no_check (@eq_refl _ (UBs nx0)). Qed.

Definition PXb : list sobj := [O_w].
Definition FXPb : list sprop := ltac2:(tb__ "0|0|
S23ScS17S1bS13aS13S129A1S13S128A1A3A1S20ScA1A3").

Definition C5Ab : axst := Eval vm_compute in (ax_add_facts (F_A nx0) C5bc).
Lemma HC5Ab_0 : ltac2:(tb__ "0|0|
S0S3S6fS4aS2fA1S138A2SbaA3"). Proof. vm_cast_no_check (@eq_refl _ (C5Ab)). Qed.
Lemma FBAb_0 : ltac2:(tb__ "0|0|
S0S22S31ScS14SeS2S138A1A1A1S4aS2fA1A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FLOWb_0 : ltac2:(tb__ "0|0|
S30ScS11eS2fA1SfS2S138A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Definition run6Ab : option (list leafA) := Eval vm_compute in (runT6 C5Ab).
Lemma run6Ab__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S5A1A1M0A1S70S38Ufa0S23S35S112S20S35A1A3S23S3SbaS20S3A1A3A4S23G0SfaS20G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run6Ab]). Qed.
Definition Y6Ab : axst := Eval vm_compute in (leafS 0 run6Ab).
Lemma Cert6Ab_0 : ltac2:(tb__ "0|1|
S0S22S6eS38Ufa0S23S35S112S20S35A1A3VGS0;S23S3SbaS20S3A1M0A3S23S3Se2G0A3A6S21A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] GS0 [C5Ab] [Y6Ab] [run6Ab]); [exact run6Ab__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition E6b : axst := Eval vm_compute in (rmF (F_A nx0) Y6Ab).
Definition s6Ab : wsub := Eval vm_compute in (infer_sub GS0 (ax_S Y6Ab) (ax_S E6b)).
Lemma E6Ab_0 : ltac2:(tb__ "0|0|
S0S22S7Se2SaeSe8A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma I6Ab_0 : ltac2:(tb__ "0|0|
S0S22S12cSe8VGS0;A2S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition CT6b : axst := Eval vm_compute in (rstS E6b ru6 []).
Definition CO6b : axst := Eval vm_compute in (carveS CT6b (O_3 nx0)).
Lemma WC6b_0 : ltac2:(tb__ "0|0|
S0S22S11S2S7aA1A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DF6b_0 : ltac2:(tb__ "0|4|
S0S28S26S24S26SbSbA2M0A1M1S24ScA1M2A2M3A1S3cS2SaeA1S2S7aA1A2S2aG3S29G1G2S23G0S29SbSbS68S2fA1S4bA4S20G0A1A3S20ScA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(a2e6 nx0, L3)], @nil sprop))). Qed.
Lemma NX6b_0 : ltac2:(tb__ "0|0|
S0S36SeS2S7aA1A1SeS2SaeA1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S E6b))). Qed.
Lemma HC6b_0 : ltac2:(tb__ "0|0|
S0S3S4SaeS2S7aA1A2S7aA3"). Proof. vm_cast_no_check (@eq_refl _ (CT6b)). Qed.
Lemma SK6b_0 : ltac2:(tb__ "0|1|
S0S24S26S26SbSbA2SbA2M0A1S39SaG0S6dS10S2S7aA1A1A4S39SaG0S6dS27SaS23SaS11aS2fA1S23SaS117S2fA1S20SaA1A3A3S27SaS11dU0S2fA2Sb4A3A3A4A3"). Proof. vm_cast_no_check (@eq_refl _ (map skel ([O_2 nx0; O_1 nx0] ++ SKEL0 0%nat nx0 ++ PXb))). Qed.
Lemma FC6b_0 : ltac2:(tb__ "0|0|
S32ScS27ScS115VW;Vst;A2S114S113A1A3SfS2S7aA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FX6b_0 : ltac2:(tb__ "0|0|
S32ScS9cSfS2S7aA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma XC6b_0 : ltac2:(tb__ "0|1|
S0S24S26SbSbA2M0A1S6S7aA1S20G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma HCO6b_0 : ltac2:(tb__ "0|0|
S0S3S118S7aS16S5fS2fA1S12Z0A1S4bS20SdA1S15A5A2S80A3"). Proof. vm_cast_no_check (@eq_refl _ (CO6b)). Qed.
Lemma WCO6b_0 : ltac2:(tb__ "0|0|
S0S22S11S2S80A1A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition s6b : wsub := Eval vm_compute in (callsub CO6b Pre_memsetA).
Definition R6b : list sobj := Eval vm_compute in (callR CO6b Pre_memsetA s6b).
Definition T6b : axst := Eval vm_compute in (callT CO6b Pre_memsetA Pret_ms s6b R6b).
Lemma He6b_0 : ltac2:(tb__ "0|1|
S0S28S24SaA1M0A1S126S80S10dSd4A3S2aG0Sc4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some R6b)). Qed.
Lemma Hchk6b_0 : ltac2:(tb__ "0|0|
S0S22S125S80S10dSd4Sc4S39S5S3S8S10eA4A5S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HT6b_0 : ltac2:(tb__ "0|0|
S0S3S127Sd4S10dS11bS80Sc4A5ScaA3"). Proof. vm_cast_no_check (@eq_refl _ (T6b)). Qed.
Lemma FBC6b_0 : ltac2:(tb__ "0|1|
S0S22S31ScS14SeS2S80A1M0A1A1SfG0A1A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT6b_0 : ltac2:(tb__ "0|0|
S0S22S31ScS14SeS2ScaA1A1A1SfS2S80A1A1A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXC6b_0 : ltac2:(tb__ "0|0|
S0S22S12aVGS0;SeS2S80A1A1A2S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition D6b : axst := Eval vm_compute in (ax_with_facts T6b (ss_facts (ax_S CO6b))).
Lemma HD6b_0 : ltac2:(tb__ "0|0|
S0S3S124ScaSfS2S80A1A1A2Sa0A3"). Proof. vm_cast_no_check (@eq_refl _ (D6b)). Qed.

Definition D6Lb : axst := Eval vm_compute in (rstS D6b [] (F_g7L nx0)).
Lemma WD6Lb_0 : ltac2:(tb__ "0|0|
S0S22S11S2S8aA1A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DD6Lb_0 : ltac2:(tb__ "0|4|
S0S28S26S24S26SbSbA2M0A1M1S24ScA1M2A2M3A1S3cS2Sa0A1S2S8aA1A2S2aG3S29G1G2S20G0A1S11fS2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g7L nx0))). Qed.
Lemma NXD6Lb_0 : ltac2:(tb__ "0|0|
S0S36SeS2S8aA1A1SeS2Sa0A1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D6b))). Qed.
Lemma HD6Lb_0 : ltac2:(tb__ "0|0|
S0S3S4Sa0S2S8aA1A2S8aA3"). Proof. vm_cast_no_check (@eq_refl _ (D6Lb)). Qed.
Lemma FLOW6b_0 : ltac2:(tb__ "0|0|
S30ScS11eS2fA1SfS2Sa0A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Definition U7b : axst := Eval vm_compute in (U7p nx0 D6Lb).
Lemma WU7b_0 : ltac2:(tb__ "0|0|
S0S22S11S2S92A1A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DU7b_0 : ltac2:(tb__ "0|4|
S0S28S26S24S26SbSbA2M0A1M1S24ScA1M2A2M3A1S3cS2S8aA1S2S92A1A2S2aG3S29G1G2S20G0A1S62S2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g7 nx0))). Qed.
Lemma NXU7b_0 : ltac2:(tb__ "0|0|
S0S36SeS2S92A1A1SeS2S8aA1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D6Lb))). Qed.
Lemma HU7b_0 : ltac2:(tb__ "0|0|
S0S3S4S8aS2S92A1A2S92A3"). Proof. vm_cast_no_check (@eq_refl _ (U7b)). Qed.
Definition run7b : option (list leafA) := Eval vm_compute in (runT6 U7b).
Lemma run7b__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S5A1A1M0A1S70S38Ufa0S23S35S112S20S35A1A3S23S3S92S20S3A1A3A4S23G0SfcS20G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run7b]). Qed.
Definition ET7b : axst := Eval vm_compute in (leafS 0 run7b).
Lemma Cert7b_0 : ltac2:(tb__ "0|1|
S0S22S6eS38Ufa0S23S35S112S20S35A1A3VGS0;S23S3S92S20S3A1M0A3S23S3Sb0G0A3A6S21A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] GS0 [U7b] [ET7b] [run7b]); [exact run7b__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition CT7b : axst := Eval vm_compute in (rstS ET7b (ru7 nx0) []).
Definition CO7b : axst := Eval vm_compute in (carveS CT7b (O_3n nx0)).
Definition CR7b : axst := Eval vm_compute in (CDepotCall.oreb CO7b 1).
Definition n7b : nat := Eval vm_compute in (length (ss_objs (ax_S CR7b))).
Definition CS7b : axst := Eval vm_compute in (sel7 CR7b).
Definition CM7b : axst := Eval vm_compute in (CDepotCall.omrg CS7b 1).
Lemma WC7b_0 : ltac2:(tb__ "0|0|
S0S22S11S2S7cA1A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DF7b_0 : ltac2:(tb__ "0|4|
S0S28S26S24S26SbSbA2M0A1M1S24ScA1M2A2M3A1S3cS2Sb0A1S2S7cA1A2S2aG3S29G1G2S23G0S29SbSbS67S2fA1S119S2fA1A4S23G0S29SbSbS69S2fA1S65A4S20G0A1A3A3S20ScA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(a0e7 nx0, BR nx0); (a2e7 nx0, L3b)], @nil sprop))). Qed.
Lemma NX7b_0 : ltac2:(tb__ "0|0|
S0S36SeS2S7cA1A1SeS2Sb0A1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S ET7b))). Qed.
Lemma HC7b_0 : ltac2:(tb__ "0|0|
S0S3S4Sb0S2S7cA1A2S7cA3"). Proof. vm_cast_no_check (@eq_refl _ (CT7b)). Qed.
Lemma SK7b_0 : ltac2:(tb__ "0|1|
S0S24S26S26SbSbA2SbA2M0A1S39SaG0S6dS10S2S7cA1A1A4S39SaG0S6dS27SaS23SaS48S2fA1S23SaS11aS2fA1S23SaS117S2fA1S20SaA1A3A3A3S27SaS11dU0S2fA2Sb4A3A3A4A3"). Proof. vm_cast_no_check (@eq_refl _ (map skel ([O_3 nx0; O_2 nx0; O_1 nx0] ++ SKEL0 0%nat nx0 ++ PXb))). Qed.
Lemma FC7b_0 : ltac2:(tb__ "0|0|
S32ScS27ScS115VW;Vst;A2S114S113A1A3SfS2S7cA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FX7b_0 : ltac2:(tb__ "0|0|
S32ScS9cSfS2S7cA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma XC7b_0 : ltac2:(tb__ "0|1|
S0S24S26SbSbA2M0A1S6S7cA1S20G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma HCO7b_0 : ltac2:(tb__ "0|0|
S0S3S118S7cS16S119S2fA1S12Z0A1S12Z100A1S20SdA1S15A5A2SaaA3"). Proof. vm_cast_no_check (@eq_refl _ (CO7b)). Qed.
Lemma WCO7b_0 : ltac2:(tb__ "0|0|
S0S22S11S2SaaA1A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RB7b_0 : ltac2:(tb__ "0|0|
S0S22S12dS18S13eS2SaaA1U1A2A2S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HCR7b_0 : ltac2:(tb__ "0|0|
S0S3S12fSaaU1A2SbcA3"). Proof. vm_cast_no_check (@eq_refl _ (CR7b)). Qed.
Lemma LEN7b_0 : ltac2:(tb__ "0|0|
S0S25S2bSaS10S2SbcA1A1A2S9eA3"). Proof. vm_cast_no_check (@eq_refl _ (n7b)). Qed.
Lemma PERM_nd7b_0 : ltac2:(tb__ "0|0|
S0S22S110S49S9eA1A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma PERM_lt7b_0 : ltac2:(tb__ "0|0|
S0S22S31S25S25S10cR1S9eA2Li;S49S9eA1A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma PERM_cov7b_0 : ltac2:(tb__ "0|0|
S0S22S31S25S25S33S25S10bR1A1S49S9eA1A3Li;S3aU0S9eA2A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HCS7b_0 : ltac2:(tb__ "0|0|
S0S3S6cSbcA1SbeA3"). Proof. vm_cast_no_check (@eq_refl _ (CS7b)). Qed.
Lemma MRG7b_0 : ltac2:(tb__ "0|0|
S0S22S12dS18S13dS2SbeA1U1A2A2S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HCM7b_0 : ltac2:(tb__ "0|0|
S0S3S12eSbeU1A2S88A3"). Proof. vm_cast_no_check (@eq_refl _ (CM7b)). Qed.
Definition s7b : wsub := Eval vm_compute in (callsub CM7b Pre_memsetA).
Definition R7b : list sobj := Eval vm_compute in (callR CM7b Pre_memsetA s7b).
Definition T7b : axst := Eval vm_compute in (callT CM7b Pre_memsetA Pret_ms s7b R7b).
Lemma He7b_0 : ltac2:(tb__ "0|1|
S0S28S24SaA1M0A1S126S88S10dSd6A3S2aG0Sc6A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some R7b)). Qed.
Lemma Hchk7b_0 : ltac2:(tb__ "0|0|
S0S22S125S88S10dSd6Sc6S39S5S3S8S10eA4A5S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HT7b_0 : ltac2:(tb__ "0|0|
S0S3S127Sd6S10dS11bS88Sc6A5SccA3"). Proof. vm_cast_no_check (@eq_refl _ (T7b)). Qed.
Lemma FBC7b_0 : ltac2:(tb__ "0|1|
S0S22S31ScS14SeS2S88A1M0A1A1SfG0A1A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT7b_0 : ltac2:(tb__ "0|0|
S0S22S31ScS14SeS2SccA1A1A1SfS2S88A1A1A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXC7b_0 : ltac2:(tb__ "0|0|
S0S22S12aVGS0;SeS2S88A1A1A2S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition D7b : axst := Eval vm_compute in (ax_with_facts T7b (ss_facts (ax_S CM7b))).
Lemma HD7b_0 : ltac2:(tb__ "0|0|
S0S3S124SccSfS2S88A1A1A2Sa2A3"). Proof. vm_cast_no_check (@eq_refl _ (D7b)). Qed.

Definition D7Lb : axst := Eval vm_compute in (rstS D7b [] (F_g8L nx0)).
Lemma WD7Lb_0 : ltac2:(tb__ "0|0|
S0S22S11S2S8cA1A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DD7Lb_0 : ltac2:(tb__ "0|4|
S0S28S26S24S26SbSbA2M0A1M1S24ScA1M2A2M3A1S3cS2Sa2A1S2S8cA1A2S2aG3S29G1G2S20G0A1S120S2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g8L nx0))). Qed.
Lemma NXD7Lb_0 : ltac2:(tb__ "0|0|
S0S36SeS2S8cA1A1SeS2Sa2A1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D7b))). Qed.
Lemma HD7Lb_0 : ltac2:(tb__ "0|0|
S0S3S4Sa2S2S8cA1A2S8cA3"). Proof. vm_cast_no_check (@eq_refl _ (D7Lb)). Qed.
Lemma FLOW7b_0 : ltac2:(tb__ "0|0|
S30ScS11eS2fA1SfS2Sa2A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Definition U8b : axst := Eval vm_compute in (U8p nx0 D7Lb).
Lemma WU8b_0 : ltac2:(tb__ "0|0|
S0S22S11S2S94A1A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DU8b_0 : ltac2:(tb__ "0|4|
S0S28S26S24S26SbSbA2M0A1M1S24ScA1M2A2M3A1S3cS2S8cA1S2S94A1A2S2aG3S29G1G2S20G0A1S63S2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g8 nx0))). Qed.
Lemma NXU8b_0 : ltac2:(tb__ "0|0|
S0S36SeS2S94A1A1SeS2S8cA1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D7Lb))). Qed.
Lemma HU8b_0 : ltac2:(tb__ "0|0|
S0S3S4S8cS2S94A1A2S94A3"). Proof. vm_cast_no_check (@eq_refl _ (U8b)). Qed.
Definition run8b : option (list leafA) := Eval vm_compute in (runT6 U8b).
Lemma run8b__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S5A1A1M0A1S70S38Ufa0S23S35S112S20S35A1A3S23S3S94S20S3A1A3A4S23G0SfeS20G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run8b]). Qed.
Definition ET8b : axst := Eval vm_compute in (leafS 0 run8b).
Lemma Cert8b_0 : ltac2:(tb__ "0|1|
S0S22S6eS38Ufa0S23S35S112S20S35A1A3VGS0;S23S3S94S20S3A1M0A3S23S3Sb2G0A3A6S21A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] GS0 [U8b] [ET8b] [run8b]); [exact run8b__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition CT8b : axst := Eval vm_compute in (CT8p nx0 ET8b).
Definition CO8b : axst := Eval vm_compute in (carveS CT8b (O_4 nx0)).
Lemma WC8b_0 : ltac2:(tb__ "0|0|
S0S22S11S2S7eA1A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DF8b_0 : ltac2:(tb__ "0|4|
S0S28S26S24S26SbSbA2M0A1M1S24ScA1M2A2M3A1S3cS2Sb2A1S2S7eA1A2S2aG3S29G1G2S20G0A1S6bS2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), fx8 nx0))). Qed.
Lemma NX8b_0 : ltac2:(tb__ "0|0|
S0S36SeS2S7eA1A1SeS2Sb2A1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S ET8b))). Qed.
Lemma HC8b_0 : ltac2:(tb__ "0|0|
S0S3S4Sb2S2S7eA1A2S7eA3"). Proof. vm_cast_no_check (@eq_refl _ (CT8b)). Qed.
Lemma SK8b_0 : ltac2:(tb__ "0|1|
S0S24S26S26SbSbA2SbA2M0A1S39SaG0S6dS10S2S7eA1A1A4S39SaG0S6dS27SaS23SaS4cS2fA1S23SaS48S2fA1S23SaS117S2fA1S20SaA1A3A3A3S27SaS11dU0S2fA2Sb4A3A3A4A3"). Proof. vm_cast_no_check (@eq_refl _ (map skel ([O_3b nx0; O_3 nx0; O_1 nx0] ++ SKEL0 0%nat nx0 ++ PXb))). Qed.
Lemma FC8b_0 : ltac2:(tb__ "0|0|
S32ScS27ScS115VW;Vst;A2S114S113A1A3SfS2S7eA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FX8b_0 : ltac2:(tb__ "0|0|
S32ScS9cSfS2S7eA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma XC8b_0 : ltac2:(tb__ "0|1|
S0S24S26SbSbA2M0A1S6S7eA1S20G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma HCO8b_0 : ltac2:(tb__ "0|0|
S0S3S118S7eS16S60S2fA1S12Z0A1S6aS2fA1S20SdA1S15A5A2S82A3"). Proof. vm_cast_no_check (@eq_refl _ (CO8b)). Qed.
Lemma WCO8b_0 : ltac2:(tb__ "0|0|
S0S22S11S2S82A1A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition s8b : wsub := Eval vm_compute in (callsub CO8b Pre_mszA).
Definition R8b : list sobj := Eval vm_compute in (callR CO8b Pre_mszA s8b).
Definition T8b : axst := Eval vm_compute in (callT CO8b Pre_mszA Pret_mz s8b R8b).
Lemma He8b_0 : ltac2:(tb__ "0|1|
S0S28S24SaA1M0A1S126S82S122Sd8A3S2aG0Sc8A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some R8b)). Qed.
Lemma Hchk8b_0 : ltac2:(tb__ "0|0|
S0S22S125S82S122Sd8Sc8S39S5S3S8S123A4A5S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HT8b_0 : ltac2:(tb__ "0|0|
S0S3S127Sd8S122S11cS82Sc8A5SceA3"). Proof. vm_cast_no_check (@eq_refl _ (T8b)). Qed.
Lemma FBC8b_0 : ltac2:(tb__ "0|1|
S0S22S31ScS14SeS2S82A1M0A1A1SfG0A1A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT8b_0 : ltac2:(tb__ "0|0|
S0S22S31ScS14SeS2SceA1A1A1SfS2S82A1A1A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXC8b_0 : ltac2:(tb__ "0|0|
S0S22S12aVGS0;SeS2S82A1A1A2S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition D8b : axst := Eval vm_compute in (ax_with_facts T8b (ss_facts (ax_S CO8b))).
Lemma HD8b_0 : ltac2:(tb__ "0|0|
S0S3S124SceSfS2S82A1A1A2Sa4A3"). Proof. vm_cast_no_check (@eq_refl _ (D8b)). Qed.

Definition D8Lb : axst := Eval vm_compute in (rstS D8b [] (F_g9L nx0)).
Lemma WD8Lb_0 : ltac2:(tb__ "0|0|
S0S22S11S2S8eA1A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DD8Lb_0 : ltac2:(tb__ "0|4|
S0S28S26S24S26SbSbA2M0A1M1S24ScA1M2A2M3A1S3cS2Sa4A1S2S8eA1A2S2aG3S29G1G2S20G0A1S121S2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g9L nx0))). Qed.
Lemma NXD8Lb_0 : ltac2:(tb__ "0|0|
S0S36SeS2S8eA1A1SeS2Sa4A1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D8b))). Qed.
Lemma HD8Lb_0 : ltac2:(tb__ "0|0|
S0S3S4Sa4S2S8eA1A2S8eA3"). Proof. vm_cast_no_check (@eq_refl _ (D8Lb)). Qed.
Lemma FLOW8b_0 : ltac2:(tb__ "0|0|
S30ScS11eS2fA1SfS2Sa4A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Definition U9b : axst := Eval vm_compute in (U9p nx0 D8Lb).
Lemma WU9b_0 : ltac2:(tb__ "0|0|
S0S22S11S2S96A1A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DU9b_0 : ltac2:(tb__ "0|4|
S0S28S26S24S26SbSbA2M0A1M1S24ScA1M2A2M3A1S3cS2S8eA1S2S96A1A2S2aG3S29G1G2S20G0A1S64S2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g9 nx0))). Qed.
Lemma NXU9b_0 : ltac2:(tb__ "0|0|
S0S36SeS2S96A1A1SeS2S8eA1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D8Lb))). Qed.
Lemma HU9b_0 : ltac2:(tb__ "0|0|
S0S3S4S8eS2S96A1A2S96A3"). Proof. vm_cast_no_check (@eq_refl _ (U9b)). Qed.
Definition run9b : option (list leafA) := Eval vm_compute in (runT9 U9b).
Lemma run9b__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S5A1A1M0A1S70S38Ufa0S23S35S45S23S35S4dS20S35A1A3A3S23S3S96S20S3A1A3A4S23G0S100S20G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run9b]). Qed.
Definition E9fb : axst := Eval vm_compute in (leafS 0 run9b).
Definition E9pb : axst := Eval vm_compute in (leafS 1 run9b).
Lemma Cert9b_0 : ltac2:(tb__ "0|1|
S0S22S6eS38Ufa0S23S35S45S23S35S4dS20S35A1A3A3VGS0;S23S3S96S20S3A1M0A3S23S3SdaS23S3S90G0A3A3A6S21A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [CPC; PGST] GS0 [U9b] [E9fb; E9pb] [run9b]); [exact run9b__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma SK9b_0 : ltac2:(tb__ "0|1|
S0S24S26S26SbSbA2SbA2M0A1S39SaG0S6dS10S2S90A1A1A4S39SaG0S6dS27SaS23SaS66S2fA1S23SaS4cS2fA1S23SaS48S2fA1S23SaS117S2fA1S20SaA1A3A3A3A3S27SaS11dU0S2fA2Sb4A3A3A4A3"). Proof. vm_cast_no_check (@eq_refl _ (map skel ([O_4z nx0; O_3b nx0; O_3 nx0; O_1 nx0] ++ SKEL0 0%nat nx0 ++ PXb))). Qed.
Lemma FC9b_0 : ltac2:(tb__ "0|0|
S32ScS27ScS115VW;Vst;A2S114S113A1A3SfS2S90A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FX9b_0 : ltac2:(tb__ "0|0|
S32ScS9cSfS2S90A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FP9b_0 : ltac2:(tb__ "0|0|
S30ScS17S44A1SfS2S90A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Lemma XC9b_0 : ltac2:(tb__ "0|1|
S0S24S26SbSbA2M0A1S6S90A1S20G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Definition CO9pb : axst := Eval vm_compute in (carveS E9pb (mkObj (BP9 nx0) (SLit 0) (SLit 1) [] DUnknown)).
Lemma HCO9b_0 : ltac2:(tb__ "0|0|
S0S3S118S90S16S61S2fA1S12Z0A1S12Z1A1S20SdA1S15A5A2SacA3"). Proof. vm_cast_no_check (@eq_refl _ (CO9pb)). Qed.
Lemma WCO9b_0 : ltac2:(tb__ "0|0|
S0S22S11S2SacA1A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition run9qb : option (list leafA) := Eval vm_compute in (runT9q CO9pb).
Lemma run9qb__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S5A1A1M0A1S70S38Ufa0S23S35S45S20S35A1A3S23S3SacS20S3A1A3A4S23G0S102S20G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run9qb]). Qed.
Definition E9qb : axst := Eval vm_compute in (leafS 0 run9qb).
Lemma Cert9qb_0 : ltac2:(tb__ "0|1|
S0S22S6eS38Ufa0S23S35S45S20S35A1A3VGS0;S23S3SacS20S3A1M0A3S23S3SdcG0A3A6S21A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [CPC] GS0 [CO9pb] [E9qb] [run9qb]); [exact run9qb__runeq | vm_cast_no_check (eq_refl true)]. Qed.

Definition iMfb : nat := Eval vm_compute in (find_map nx0 (ss_objs (ax_S E9fb)) 0).
Definition S9afb : axst := Eval vm_compute in (osplit E9fb iMfb (SLit 6144)).
Definition S9bfb : axst := Eval vm_compute in (osplit S9afb (S iMfb) (SLit 10240)).
Lemma HS9afb_0 : ltac2:(tb__ "0|0|
S0S3S47SdaSe4S12Z1800A1A3SdeA3"). Proof. vm_cast_no_check (@eq_refl _ (S9afb)). Qed.
Lemma HS9bfb_0 : ltac2:(tb__ "0|0|
S0S3S47SdeS2eSe4A1S12Z2800A1A3Sa6A3"). Proof. vm_cast_no_check (@eq_refl _ (S9bfb)). Qed.
Definition perm9fb : list nat := Eval vm_compute in (S iMfb :: seq 0 (S iMfb) ++ seq (S (S iMfb)) (length (ss_objs (ax_S S9bfb)) - S (S iMfb))).
Definition D9fb : axst := Eval vm_compute in (ax_setS S9bfb (set_objs (ax_S S9bfb) (select (ss_objs (ax_S S9bfb)) perm9fb))).
Lemma HD9fb_0 : ltac2:(tb__ "0|1|
S0S3S4Sa6S111S2Sa6A1M0S10fS10G0A1Sd0A2A2A2Sc0A3"). Proof. vm_cast_no_check (@eq_refl _ (D9fb)). Qed.
Lemma NDpfb_0 : nodupN perm9fb = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDpfb_0 : ltac2:(tb__ "0|0|
S0S22S31S25S25S10cR1S2bSaS10S2Sa6A1A1A2A2Li;Sd0A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVpfb_0 : ltac2:(tb__ "0|0|
S0S22S31S25S25S33S25S10bR1A1Sd0A3Li;S3aU0S2bSaS10S2Sa6A1A1A2A2A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition runFfb : option (list leafA) := Eval vm_compute in (runTF D9fb).
Lemma runFfb__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S5A1A1M0A1S70S38Ufa0S20S35A1S23S3Sc0S20S3A1A3A4S23G0S104S20G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [runFfb]). Qed.
Definition FFfb : axst := Eval vm_compute in (leafS 0 runFfb).
Lemma CertFfb_0 : ltac2:(tb__ "0|1|
S0S22S6eS38Ufa0S20S35A1VGS0;S23S3Sc0S20S3A1M0A3S23S3S72G0A3A6S21A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [] GS0 [D9fb] [FFfb] [runFfb]); [exact runFfb__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition swcfb : list cell := Eval vm_compute in (cells_at 5 FFfb).
Definition c1fb : list cell := Eval vm_compute in (cells_at 38 FFfb).
Definition c2fb : list cell := Eval vm_compute in (cells_at 39 FFfb).
Definition c4fb : list cell := Eval vm_compute in (cells_at 41 FFfb).
Definition c5fb : list cell := Eval vm_compute in (cells_at 45 FFfb).
Definition mcfb : list cell := Eval vm_compute in (cells_at 46 FFfb).
Definition xcfb : list cell := Eval vm_compute in (cells_at 48 FFfb).
Definition tybfb : Z := Eval vm_compute in (tyb_of mcfb).
Lemma SELFfb_0 : ltac2:(tb__ "0|0|
S0S24SaA1S10fS10S2S72A1A1S3fU0S2cA2A2S27SaS3dVW;S84A2S27SaS131S4eS2fS98SeeSf2Sf6S76S108Z8S15S2cAaA3A3A3"). Proof. vm_cast_no_check (@eq_refl _ (KEPTF W swcfb ++ RT_m1 ++ RSF nx0 c1fb c2fb c4fb c5fb mcfb xcfb 8 DUnknown false)). Qed.
Lemma NDFfb_0 : ltac2:(tb__ "0|0|
S0S22S110S3fU0S2cA2A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDFfb_0 : ltac2:(tb__ "0|0|
S0S22S31S25S25S10cR1S2bSaS10S2S72A1A1A2A2Li;S3fU0S2cA2A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVFfb_0 : ltac2:(tb__ "0|1|
S0S22S31S25S25S33S25S10bR1A1S3fU0M0S2cA2A3Li;S3aG0S2bSaS10S2S72A1A1A2A2A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XFnfb_0 : ltac2:(tb__ "0|1|
S0S24S26SbSbA2M0A1S6S72A1S20G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma BFbfb_0 : ax_base FFfb = base_sv. Proof. vm_cast_no_check (@eq_refl _ (base_sv)). Qed.
Lemma FPFfb_0 : ltac2:(tb__ "0|0|
S32ScS27ScS115VW;Vst;A2S114S113A1A3SfS2S72A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FXFfb_0 : ltac2:(tb__ "0|0|
S32ScS9cSfS2S72A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FPARfb_0 : ltac2:(tb__ "0|0|
S30ScS22ScL_;S2cS17S44A1S44X22x2SfS2S72A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Lemma Hc1fb_0 : ltac2:(tb__ "0|0|
S1S30SdS53S98A3S1S30SdS4fS98A3S1S30SdS50S98A3S1S30SdS54S98A3S1S30SdS52S13S128A1A1S98A3S30SdS51S98A3A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (ic_pg) c1fb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c1) c1fb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c2) c1fb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_rs) c1fb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_nres (SVar V_NRES)) c1fb ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (ic_nch) c1fb ltac:(vm_cast_no_check (eq_refl true)))))))). Qed.
Lemma Hmcfb_0 : ltac2:(tb__ "0|0|
S1S30SdS58S2fA1S76A3S1S30SdS59S76A3S1S30SdS5aS76A3S1S30SdS56S76A3S1S30SdS57S76A3S1S30SdS55S2fA1S76A3S1S30SdS5dS76A3S1S30SdS5eSb6A1S76A3S1S30SdS5cS76A3S30SdS5bS76A3A2A2A2A2A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (mc_map nx0) mcfb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ms) mcfb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ns) mcfb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_idx) mcfb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_magic) mcfb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_cptr nx0) mcfb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_state) mcfb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_type tybfb) mcfb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_sizehi) mcfb ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (mc_size) mcfb ltac:(vm_cast_no_check (eq_refl true)))))))))))). Qed.
Lemma Htybfb_0 : ltac2:(tb__ "0|0|
S0S22S2dS2dS134Z0Sb6A2S135Sb6Z100A2A2S133S136Sb6Z4A2Z1A2A2S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma Hxcfb_0 : In (xc_map nx0) xcfb. Proof. exact (In_of_cellb (xc_map nx0) xcfb ltac:(vm_cast_no_check (eq_refl true))). Qed.
Lemma WCUfb_0 : ltac2:(tb__ "0|0|
S0S22S11S111S2S72A1S27SaS3dVW;S84A2S23SaS43S2fA1S20SaA1A3A3A2A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SELUfb_0 : ltac2:(tb__ "0|0|
S0S24SaA1S10fS27SaS3dVW;S84A2S23SaS43S2fA1S20SaA1A3A3S40U0A1A2S3eVW;S84S2fA3A3"). Proof. vm_cast_no_check (@eq_refl _ (KUB W swcfb nx0)). Qed.
Lemma NDUfb_0 : nodupN (idxsU 0%nat) = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDUfb_0 : ltac2:(tb__ "0|0|
S0S22S31S25S25S10cR1S2bSaS27SaS3dVW;S84A2S23SaS43S2fA1S20SaA1A3A3A2A2Li;S40U0A1A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVUfb_0 : ltac2:(tb__ "0|1|
S0S22S31S25S25S33S25S10bR1A1S40U0M0A1A3Li;S3aG0S2bSaS27SaS3dVW;S84A2S23SaS43S2fA1S20SaA1A3A3A2A2A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W9fb_0 : ltac2:(tb__ "0|0|
S0S22S11S41S72S3eVW;S84S2fA3A2A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D9fb_0 : ltac2:(tb__ "0|5|
S0S28S26S24S26SbSbA2M0A1M1S24ScA1M2A2M3A1S3cS111S2S72A1S3eVW;S84S2fA3M4A2S41S72G4A2A2S2aG3S29G1G2S23G0S29SbSbS12S132A1S13P18A1A4S20G0A1A3S20ScA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(SLit TP_A, SVar 24)], @nil sprop))). Qed.
Lemma XB9fb_0 : ltac2:(tb__ "0|0|
S0S22S9SeS2S72A1A1S29SbSbS46S2fA1S13PcA1A4A2S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sFfb : wsub := Eval vm_compute in (infer_sub NF (S2F FFfb (KUB W swcfb nx0)) (ax_S (Lc_ok W st))).
Lemma ENT9fb_0 : ltac2:(tb__ "0|0|
S0S22S7S42S72S3eVW;S84S2fA3S2fA3S130VW;Vst;A2SeaA3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID9fb_0 : wsub_idc sFfb = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma G110fb_0 : ltac2:(tb__ "0|0|
S0SbS12bSeaS116A2S46S2fA1A3"). Proof. vm_cast_no_check (@eq_refl _ (UBs nx0)). Qed.

Definition iMqb : nat := Eval vm_compute in (find_map nx0 (ss_objs (ax_S E9qb)) 0).
Definition S9aqb : axst := Eval vm_compute in (osplit E9qb iMqb (SLit 6144)).
Definition S9bqb : axst := Eval vm_compute in (osplit S9aqb (S iMqb) (SLit 10240)).
Lemma HS9aqb_0 : ltac2:(tb__ "0|0|
S0S3S47SdcSe6S12Z1800A1A3Se0A3"). Proof. vm_cast_no_check (@eq_refl _ (S9aqb)). Qed.
Lemma HS9bqb_0 : ltac2:(tb__ "0|0|
S0S3S47Se0S2eSe6A1S12Z2800A1A3Sa8A3"). Proof. vm_cast_no_check (@eq_refl _ (S9bqb)). Qed.
Definition perm9qb : list nat := Eval vm_compute in (S iMqb :: seq 0 (S iMqb) ++ seq (S (S iMqb)) (length (ss_objs (ax_S S9bqb)) - S (S iMqb))).
Definition D9qb : axst := Eval vm_compute in (ax_setS S9bqb (set_objs (ax_S S9bqb) (select (ss_objs (ax_S S9bqb)) perm9qb))).
Lemma HD9qb_0 : ltac2:(tb__ "0|1|
S0S3S4Sa8S111S2Sa8A1M0S10fS10G0A1Sd2A2A2A2Sc2A3"). Proof. vm_cast_no_check (@eq_refl _ (D9qb)). Qed.
Lemma NDpqb_0 : nodupN perm9qb = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDpqb_0 : ltac2:(tb__ "0|0|
S0S22S31S25S25S10cR1S2bSaS10S2Sa8A1A1A2A2Li;Sd2A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVpqb_0 : ltac2:(tb__ "0|0|
S0S22S31S25S25S33S25S10bR1A1Sd2A3Li;S3aU0S2bSaS10S2Sa8A1A1A2A2A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition runFqb : option (list leafA) := Eval vm_compute in (runTF D9qb).
Lemma runFqb__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S5A1A1M0A1S70S38Ufa0S20S35A1S23S3Sc2S20S3A1A3A4S23G0S106S20G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [runFqb]). Qed.
Definition FFqb : axst := Eval vm_compute in (leafS 0 runFqb).
Lemma CertFqb_0 : ltac2:(tb__ "0|1|
S0S22S6eS38Ufa0S20S35A1VGS0;S23S3Sc2S20S3A1M0A3S23S3S74G0A3A6S21A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [] GS0 [D9qb] [FFqb] [runFqb]); [exact runFqb__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition swcqb : list cell := Eval vm_compute in (cells_at 5 FFqb).
Definition c1qb : list cell := Eval vm_compute in (cells_at 38 FFqb).
Definition c2qb : list cell := Eval vm_compute in (cells_at 39 FFqb).
Definition c4qb : list cell := Eval vm_compute in (cells_at 41 FFqb).
Definition c5qb : list cell := Eval vm_compute in (cells_at 45 FFqb).
Definition mcqb : list cell := Eval vm_compute in (cells_at 46 FFqb).
Definition xcqb : list cell := Eval vm_compute in (cells_at 48 FFqb).
Definition tybqb : Z := Eval vm_compute in (tyb_of mcqb).
Lemma SELFqb_0 : ltac2:(tb__ "0|0|
S0S24SaA1S10fS10S2S74A1A1S3fU0S21A2A2S27SaS3dVW;S86A2S27SaS131S4eS2fS9aSf0Sf4Sf8S78S10aZ8S15S21AaA3A3A3"). Proof. vm_cast_no_check (@eq_refl _ (KEPTF W swcqb ++ RT_m1 ++ RSF nx0 c1qb c2qb c4qb c5qb mcqb xcqb 8 DUnknown true)). Qed.
Lemma NDFqb_0 : ltac2:(tb__ "0|0|
S0S22S110S3fU0S21A2A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDFqb_0 : ltac2:(tb__ "0|0|
S0S22S31S25S25S10cR1S2bSaS10S2S74A1A1A2A2Li;S3fU0S21A2A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVFqb_0 : ltac2:(tb__ "0|1|
S0S22S31S25S25S33S25S10bR1A1S3fU0M0S21A2A3Li;S3aG0S2bSaS10S2S74A1A1A2A2A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XFnqb_0 : ltac2:(tb__ "0|1|
S0S24S26SbSbA2M0A1S6S74A1S20G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma BFbqb_0 : ax_base FFqb = base_sv. Proof. vm_cast_no_check (@eq_refl _ (base_sv)). Qed.
Lemma FPFqb_0 : ltac2:(tb__ "0|0|
S32ScS27ScS115VW;Vst;A2S114S113A1A3SfS2S74A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FXFqb_0 : ltac2:(tb__ "0|0|
S32ScS9cSfS2S74A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FPARqb_0 : ltac2:(tb__ "0|0|
S30ScS22ScL_;S21S17S44A1S44X22x2SfS2S74A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Lemma Hc1qb_0 : ltac2:(tb__ "0|0|
S1S30SdS53S9aA3S1S30SdS4fS9aA3S1S30SdS50S9aA3S1S30SdS54S9aA3S1S30SdS52S13S128A1A1S9aA3S30SdS51S9aA3A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (ic_pg) c1qb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c1) c1qb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c2) c1qb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_rs) c1qb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_nres (SVar V_NRES)) c1qb ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (ic_nch) c1qb ltac:(vm_cast_no_check (eq_refl true)))))))). Qed.
Lemma Hmcqb_0 : ltac2:(tb__ "0|0|
S1S30SdS58S2fA1S78A3S1S30SdS59S78A3S1S30SdS5aS78A3S1S30SdS56S78A3S1S30SdS57S78A3S1S30SdS55S2fA1S78A3S1S30SdS5dS78A3S1S30SdS5eSb8A1S78A3S1S30SdS5cS78A3S30SdS5bS78A3A2A2A2A2A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (mc_map nx0) mcqb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ms) mcqb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ns) mcqb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_idx) mcqb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_magic) mcqb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_cptr nx0) mcqb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_state) mcqb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_type tybqb) mcqb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_sizehi) mcqb ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (mc_size) mcqb ltac:(vm_cast_no_check (eq_refl true)))))))))))). Qed.
Lemma Htybqb_0 : ltac2:(tb__ "0|0|
S0S22S2dS2dS134Z0Sb8A2S135Sb8Z100A2A2S133S136Sb8Z4A2Z1A2A2S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma Hxcqb_0 : In (xc_map nx0) xcqb. Proof. exact (In_of_cellb (xc_map nx0) xcqb ltac:(vm_cast_no_check (eq_refl true))). Qed.
Lemma WCUqb_0 : ltac2:(tb__ "0|0|
S0S22S11S111S2S74A1S27SaS3dVW;S86A2S23SaS43S2fA1S20SaA1A3A3A2A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SELUqb_0 : ltac2:(tb__ "0|0|
S0S24SaA1S10fS27SaS3dVW;S86A2S23SaS43S2fA1S20SaA1A3A3S40U0A1A2S3eVW;S86S2fA3A3"). Proof. vm_cast_no_check (@eq_refl _ (KUB W swcqb nx0)). Qed.
Lemma NDUqb_0 : nodupN (idxsU 0%nat) = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDUqb_0 : ltac2:(tb__ "0|0|
S0S22S31S25S25S10cR1S2bSaS27SaS3dVW;S86A2S23SaS43S2fA1S20SaA1A3A3A2A2Li;S40U0A1A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVUqb_0 : ltac2:(tb__ "0|1|
S0S22S31S25S25S33S25S10bR1A1S40U0M0A1A3Li;S3aG0S2bSaS27SaS3dVW;S86A2S23SaS43S2fA1S20SaA1A3A3A2A2A3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W9qb_0 : ltac2:(tb__ "0|0|
S0S22S11S41S74S3eVW;S86S2fA3A2A1S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D9qb_0 : ltac2:(tb__ "0|5|
S0S28S26S24S26SbSbA2M0A1M1S24ScA1M2A2M3A1S3cS111S2S74A1S3eVW;S86S2fA3M4A2S41S74G4A2A2S2aG3S29G1G2S23G0S29SbSbS12S132A1S13P18A1A4S20G0A1A3S20ScA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(SLit TP_A, SVar 24)], @nil sprop))). Qed.
Lemma XB9qb_0 : ltac2:(tb__ "0|0|
S0S22S9SeS2S74A1A1S29SbSbS46S2fA1S13PcA1A4A2S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sFqb : wsub := Eval vm_compute in (infer_sub NF (S2F FFqb (KUB W swcqb nx0)) (ax_S (Lc_ok W st))).
Lemma ENT9qb_0 : ltac2:(tb__ "0|0|
S0S22S7S42S74S3eVW;S86S2fA3S2fA3S130VW;Vst;A2SecA3S21A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID9qb_0 : wsub_idc sFqb = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma G110qb_0 : ltac2:(tb__ "0|0|
S0SbS12bSecS116A2S46S2fA1A3"). Proof. vm_cast_no_check (@eq_refl _ (UBs nx0)). Qed.
End INST.
End SpineCallocSec6IL.

