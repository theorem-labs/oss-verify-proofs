(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "ge"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "DG"; "dN"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "and"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rw"; "valuation"; "@Corelib.Init.Datatypes"; "list"; "cons"; "pair"; "nil"; "prod"; "bool"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states"; "NPRE"; "PostD"; "PreD"; "SZMAX"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "bv_signed"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "jpredA"; "SPA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "JD"; "JLD"; "DNMAX"; "dep_cost"; "droom"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "alloc_top"; "m_vmmaps"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "V_DEPTH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_laws2"; "KD_laws2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_main"; "chkD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_skel2"; "K"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA EntailA CompleteA CFGA GlueA GlueA2 SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import SegD_wf SegD_laws2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_main SegD_skel2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_refl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_main OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_skel2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Local Strategy expand [chkD I3 run_z FindZ NB NBh Jh Js run_n run_nb I4 L2 run2 T1 E1 run1].

Theorem seg_D_commonK : ltac2:(tb__ "0|5|
S4S1cF_;S6S29S0R2S15R1A4S2cOF_;S4S1eS0R2R5R1A1A3FG;S4S2fS0R3R6R1A1A3FG;S6S7S1Z7fff7f800000R1A2S1R1Z7fffff800000A2A2S4SaSbS1aQ40M0A1A1M1SbS25A1S24RdR5R4R3R2R1A5S8S6S26S27R2A1A1R8A3F_;Fmd;Ftr;Ftp;Frho;FG;S6S7S1Z1M2R1A2S1R1S18A2A2S8S10S2aR2A1S11A3SaG1S4S1S2S5R1A1G2A2S21A2S3RfS2S22R2A1S23R2A1A2A2S7S1RbS2S19G0S9R5PaA2A2S1bG0S9R5S28A2A2A2A2S1RbS19G0S9R5PcA2A2A2A2S2eS0RfS1dS0S1fS0S2bR12R4A2M3R4A3S17R9A1R6R5A5S14S0S15R6R5ScSfS12S13A2M4SdS12S13S16R9A1S20S0G3R4A3A4SeG4A1A3A5A4F_;F_;F_;FG0;Ftp0;Frho0;F_;F_;Fsz;F_;F_;Ftop;F_;F_;Fok;F_;Fhc;FK0;").
Proof.
  intros K0 hc HKD ok HKok HKokp top Htop HKT sz Hsz Hc rho0 tp0 G0 HDN0 Hhc HT0.
  lazy beta zeta delta [chkD] in Hc. splitC Hc. convC.
  pose proof (seg_D_main K0 hc HKD ok HKok HKokp sz Hsz rho0 tp0 G0 HDN0 Hhc top Htop HT0 HKT) as T. lazy beta zeta in T.
  eapply T; clear T.
  all: dispC.
Qed.

Theorem eseg_D_commonK : ltac2:(tb__ "0|5|
S4S1cF_;S6S29S0R2S15R1A4S6S7S1Z7fff7f800000R1A2S1R1Z7fffff800000A2A2S4SaSbS1aQ40M0A1A1M1SbS25A1S24RaR5R4R3R2R1A5S8S6S26S27R2A1A1R8A3F_;Fmd;Ftr;Ftp;Frho;FG;S6S7S1Z1M2R1A2S1R1S18A2A2S8S10S2aR2A1S11A3SaG1S4S1S2S5R1A1G2A2S21A2S3RcS2S22R2A1S23R2A1A2A2S7S1RbS2S19G0S9R5PaA2A2S1bG0S9R5S28A2A2A2A2S1RbS19G0S9R5PcA2A2A2A2S2dS0S1dS0S1fS0S2bRfR4A2M3R4A3S17R9A1R6R5A5S14S0S15R6R5ScSfS12S13A2M4SdS12S13S16R9A1S20S0G3R4A3A4SeG4A1A3A5A3F_;F_;F_;FG0;Ftp0;Frho0;F_;F_;Fsz;F_;F_;Ftop;F_;Fhc;FK0;").
Proof.
  intros K0 hc HKD top Htop HKT sz Hsz Hc rho0 tp0 G0 HDN0 Hhc HT0.
  lazy beta zeta delta [chkD] in Hc. splitC Hc. convC.
  pose proof (eseg_D_main K0 hc HKD sz Hsz rho0 tp0 G0 HDN0 Hhc top Htop HT0 HKT) as T. lazy beta zeta in T.
  eapply T; clear T.
  all: dispC.
Qed.

Lemma JD_wrap : ltac2:(tb__ "0|0|
S4S1cF_;S4SaSbS1aQ40A1A1SbS25A1S24S1fS0R6R5R4R3R2R1A7S1fS0S2bR7R6A2R6R5R4R3R2A7F_;Fmd;Ftr;Ftp;Frho;FG0;FK0;").
Proof. intros K0 G0 rho tp tr md [HK HD]. split; [split; [exact HK | lia] | exact HD]. Qed.

Lemma LQPA_unwrap : ltac2:(tb__ "0|2|
S4S1cF_;S4S6SaSbS1aQ40A1A1S2cS14S0S15R3R2ScSfS12S13A2M0SdS12S13S16R4A1S20S0S2bR6R5A2R5A3A4SeG0A1M1A3R1A6S14S0S15R4R3ScG0SdS12S13S16R5A1S20S0R7R6A3A4G1A3R2A6F_;Fw;Ftp0;Frho0;Fsz;FG0;FK0;").
Proof.
  intros K0 G0 sz rho0 tp0 w (L & JL & rho' & tp' & Hin & Hag & Hsm & HJ).
  destruct Hin as [E|[]]. injection E as <- <-.
  exists (PostD sz), (JLD segsA K0 G0), rho', tp'. split; [left; reflexivity|]. split; [exact Hag|]. split; [exact Hsm|].
  destruct HJ as (G' & [HK _] & HD & HP & R1 & R2 & R3 & R4). exists G'.
  split; [exact HK|]. split; [exact HD|]. split; [exact HP|]. split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. exact R4.
Qed.

Theorem seg_D_common2 : ltac2:(tb__ "0|4|
S4S1cF_;S6S29S0R2S15R1A4S2cOF_;S4S1eS0R2R5R1A1A3FG;S4S2fS0R3R6R1A1A3FG;S6S7S1Z7fff7f800000R1A2S1R1Z7fffff800000A2A2S4SaSbS1aQ40M0A1A1M1SbS25A1S24RdR5R4R3R2R1A5S8S6S26S27R2A1A1R8A3F_;Fmd;Ftr;Ftp;Frho;FG;S6S7S1Z1M2R1A2S1R1S18A2A2S8S10S2aR2A1S11A3SaG1S4S1S2S5R1A1G2A2S21A2S3RfS2S22R2A1S23R2A1A2A2S7S1RbS2S19G0S9R5PaA2A2S1bG0S9R5S28A2A2A2A2S1RbS19G0S9R5PcA2A2A2A2S2eS0RfS1dS0S1fS0R12R4A3S17R9A1R6R5A5S14S0S15R6R5ScSfS12S13A2M3SdS12S13S16R9A1S20S0R12R4A3A4SeG3A1A3A5A4F_;F_;F_;FG0;Ftp0;Frho0;F_;F_;Fsz;F_;F_;Ftop;F_;F_;Fok;F_;Fhc;FK0;").
Proof.
  intros K0 hc HKD ok HKok HKokp top Htop HKT sz Hsz Hc rho0 tp0 G0 HDN0 Hhc HT0.
  eapply triple_conseq; [| intros w Hw; exact (LQPA_unwrap K0 G0 sz rho0 tp0 w Hw) | exact (seg_D_commonK K0 hc HKD ok HKok HKokp top Htop HKT sz Hsz Hc rho0 tp0 G0 HDN0 Hhc HT0)].
  intros w [Hsm HJ]. split; [exact Hsm | exact (JD_wrap K0 G0 _ _ _ _ HJ)].
Qed.

Theorem eseg_D_common2 : ltac2:(tb__ "0|4|
S4S1cF_;S6S29S0R2S15R1A4S6S7S1Z7fff7f800000R1A2S1R1Z7fffff800000A2A2S4SaSbS1aQ40M0A1A1M1SbS25A1S24RaR5R4R3R2R1A5S8S6S26S27R2A1A1R8A3F_;Fmd;Ftr;Ftp;Frho;FG;S6S7S1Z1M2R1A2S1R1S18A2A2S8S10S2aR2A1S11A3SaG1S4S1S2S5R1A1G2A2S21A2S3RcS2S22R2A1S23R2A1A2A2S7S1RbS2S19G0S9R5PaA2A2S1bG0S9R5S28A2A2A2A2S1RbS19G0S9R5PcA2A2A2A2S2dS0S1dS0S1fS0RfR4A3S17R9A1R6R5A5S14S0S15R6R5ScSfS12S13A2M3SdS12S13S16R9A1S20S0RfR4A3A4SeG3A1A3A5A3F_;F_;F_;FG0;Ftp0;Frho0;F_;F_;Fsz;F_;F_;Ftop;F_;Fhc;FK0;").
Proof.
  intros K0 hc HKD top Htop HKT sz Hsz Hc rho0 tp0 G0 HDN0 Hhc HT0.
  eapply etriple_conseq; [| intros w Hw; exact (LQPA_unwrap K0 G0 sz rho0 tp0 w Hw) | exact (eseg_D_commonK K0 hc HKD top Htop HKT sz Hsz Hc rho0 tp0 G0 HDN0 Hhc HT0)].
  intros w [Hsm HJ]. split; [exact Hsm | exact (JD_wrap K0 G0 _ _ _ _ HJ)].
Qed.
