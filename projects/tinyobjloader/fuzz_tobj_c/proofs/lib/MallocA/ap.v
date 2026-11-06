(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith List.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase State.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ag SegD_main2.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgEdgesA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.

(* [comment removed for export] *)
Module SegD2.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "ge"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "DG"; "dN"; "@Corelib.Init.Logic"; "and"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rw"; "valuation"; "@Corelib.Init.Datatypes"; "list"; "cons"; "nil"; "pair"; "prod"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states"; "NPRE"; "PostD"; "PreD"; "SZMAX"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "bv_signed"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "alloc_top"; "event"; "m_vmmaps"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "V_DEPTH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_laws2"; "KD_laws2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "DNMAX"; "JD"; "JLD"; "dep_cost"; "droom"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA CompleteA SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import SegD_wf SegD_laws2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_states SegD_main.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ag.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_main2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_main OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ag.SegD_chk OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_main2.
Import ListNotations.
Open Scope Z_scope.

Theorem seg_D_sound2 : ltac2:(tb__ "0|4|
S5S1fF_;S4S22S0R2S13R1A4S2aOF_;S5S20S0R2R5R1A1A3FG;S5S2bS0R3R6R1A1A3FG;S4S7S1Z7fff7f800000R1A2S1R1Z7fffff800000A2A2S5SaSbS18Q40M0A1A1M1SbS1cA1S1aRdR5R4R3R2R1A5S8S4S1bS1dR2A1A1R8A3F_;Fmd;Ftr;Ftp;Frho;FG;S4S7S1Z1M2R1A2S1R1S16A2A2SaG1S5S1S2S6R1A1G2A2S23A2S3ReS2S26R2A1S27R2A1A2A2S7S1RaS2S17G0S9R5PaA2A2S19G0S9R5S21A2A2A2A2S1RaS17G0S9R5PcA2A2A2A2S29S0ReS1eS0S24S0R11R4A3S15R8A1R6R5A5S12S0S13R6R5ScSfS10S11A2M3SeS10S11S14R8A1S25S0R11R4A3A4SdG3A1A3A5A4F_;F_;F_;FG;Ftp;Frho;F_;Fsz;F_;F_;Ftop;F_;F_;Fok;F_;Fhc;FK;").
Proof.
  intros K hc HKD ok HKok HKokp top Htop HKT sz Hsz rho tp G HDN Hhc HT0.
  exact (seg_D_common2 K hc HKD ok HKok HKokp top Htop HKT sz Hsz (chkD_all sz Hsz) rho tp G HDN Hhc HT0).
Qed.

Theorem seg_D_complete2 : ltac2:(tb__ "0|4|
S5S1fF_;S4S22S0R2S13R1A4S4S7S1Z7fff7f800000R1A2S1R1Z7fffff800000A2A2S5SaSbS18Q40M0A1A1M1SbS1cA1S1aRaR5R4R3R2R1A5S8S4S1bS1dR2A1A1R8A3F_;Fmd;Ftr;Ftp;Frho;FG;S4S7S1Z1M2R1A2S1R1S16A2A2SaG1S5S1S2S6R1A1G2A2S23A2S3RbS2S26R2A1S27R2A1A2A2S7S1RaS2S17G0S9R5PaA2A2S19G0S9R5S21A2A2A2A2S1RaS17G0S9R5PcA2A2A2A2S28S0S1eS0S24S0ReR4A3S15R8A1R6R5A5S12S0S13R6R5ScSfS10S11A2M3SeS10S11S14R8A1S25S0ReR4A3A4SdG3A1A3A5A3F_;F_;F_;FG;Ftp;Frho;F_;Fsz;F_;F_;Ftop;F_;Fhc;FK;").
Proof.
  intros K hc HKD top Htop HKT sz Hsz rho tp G HDN Hhc HT0.
  exact (eseg_D_common2 K hc HKD top Htop HKT sz Hsz (chkD_all sz Hsz) rho tp G HDN Hhc HT0).
Qed.
End SegD2.

(* [comment removed for export] *)
Module CertCallocS1c.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "bool"; "cons"; "nil"; "true"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1"; "s1_exits"; "s1_cuts"; "s1_cuts_pcs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLe"; "UStopLeOrPc"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA CFGA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgEdgesA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
Import ListNotations.
Open Scope Z_scope.
Lemma s1_cert_0 : ltac2:(tb__ "0|1|
S5S1S6SbUfa0S2S0Z40a18S3S0A1A3SaS8U0M0ScA2S7G0ScZ2A3A6S4A3").
Proof. exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgEdgesA.check_cfgA_of_ecfgA segsA 4000%nat [0x40a18] GW (map (fun c => mkVNA c 1 (SLit 0)) (s1_cuts 0 UStopLe)) (map (fun e => mkVNA e 0 (SLit 0)) (s1_exits 0 UStopLe 2)) (s1_cuts 0 UStopLe) (s1_exits 0 UStopLe 2) eq_refl eq_refl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertCallocS1e.s1_ecert_0). Qed.
Lemma s1_cert_1 : ltac2:(tb__ "0|1|
S5S1S6SbUfa0S2S0Z40a18S3S0A1A3SaS9U1M0SdA2S7G0SdZ3A3A6S4A3").
Proof. exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgEdgesA.check_cfgA_of_ecfgA segsA 4000%nat [0x40a18] GW (map (fun c => mkVNA c 1 (SLit 0)) (s1_cuts_pcs 1 UStopLeOrPc)) (map (fun e => mkVNA e 0 (SLit 0)) (s1_exits 1 UStopLeOrPc 3)) (s1_cuts_pcs 1 UStopLeOrPc) (s1_exits 1 UStopLeOrPc 3) eq_refl eq_refl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertCallocS1e.s1_ecert_1). Qed.
End CertCallocS1c.

