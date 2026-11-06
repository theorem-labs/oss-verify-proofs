(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_skel2 SegD_chk.

(* [comment removed for export] *)
Module SegD_main2.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "ge"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "DG"; "dN"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "and"; "eq"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rw"; "valuation"; "@Corelib.Init.Datatypes"; "list"; "cons"; "pair"; "nil"; "prod"; "bool"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states"; "NPRE"; "PostD"; "PreD"; "SZMAX"; "SZMAXT"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "bv_signed"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "jpredA"; "SPA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "JD"; "JLD"; "DNMAX"; "dep_cost"; "droom"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "alloc_top"; "m_vmmaps"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget"; "KMAX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "V_DEPTH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_laws2"; "KD_laws2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_main"; "chkD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_skel2"; "K"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA EntailA CompleteA CFGA GlueA GlueA2 SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import SegD_wf SegD_laws2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_main SegD_skel2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SegD_refl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_main OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_skel2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Local Strategy expand [chkD I3 run_z FindZ NB NBh Jh Js run_n run_nb I4 L2 run2 T1 E1 run1].

Theorem seg_D_commonK : ltac2:(tb__ "0|5|
S4S1eF_;S6S2cS3R2S16R1A4S2fOF_;S4S20S3R2R5R1A1A3FG;S4S32S3R3R6R1A1A3FG;S6S7S0Z7fff7f800000R1A2S0R1Z7fffff800000A2A2S4SbScS1cQ40M0A1A1M1ScS27A1S26RdR5R4R3R2R1A5S8S6S28S29R2A1A1R8A3F_;Fmd;Ftr;Ftp;Frho;FG;S6S7S0Z1M2R1A2S0R1S1aA2A2S8S11S2dR2A1S12A3SbG1S4S9S0R6S19A2S0S5R1A1S1S2aG2A2A2A2S0S1S5R2A1G2A2S23A2S2R10S1S24R3A1S25R3A1A2A2S7S0RcS1S1bG0SaR6PaA2A2S1dG0SaR6S2bA2A2A2A2S0RcS1bG0SaR6PcA2A2A2A2S31S3R10S1fS3S21S3S2eR13R5A2M3R5A3S18RaA1R7R6A5S15S3S16R7R6SdS10S13S14A2M4SeS13S14S17RaA1S22S3G3R5A3A4SfG4A1A3A5A4F_;F_;F_;F_;FG0;Ftp0;Frho0;F_;F_;Fsz;F_;F_;Ftop;F_;F_;Fok;F_;Fhc;FK0;").
Proof.
  intros K0 hc HKD ok HKok HKokp top Htop HKT sz Hsz Hc rho0 tp0 G0 Htol HDN0 Hhc HT0.
  lazy beta zeta delta [chkD] in Hc. splitC Hc. convC.
  pose proof (seg_D_main K0 hc HKD ok HKok HKokp sz Hsz rho0 tp0 G0 Htol HDN0 Hhc top Htop HT0 HKT) as T. lazy beta zeta in T.
  eapply T; clear T.
  all: dispC.
Qed.

Theorem eseg_D_commonK : ltac2:(tb__ "0|5|
S4S1eF_;S6S2cS3R2S16R1A4S6S7S0Z7fff7f800000R1A2S0R1Z7fffff800000A2A2S4SbScS1cQ40M0A1A1M1ScS27A1S26RaR5R4R3R2R1A5S8S6S28S29R2A1A1R8A3F_;Fmd;Ftr;Ftp;Frho;FG;S6S7S0Z1M2R1A2S0R1S1aA2A2S8S11S2dR2A1S12A3SbG1S4S9S0R6S19A2S0S5R1A1S1S2aG2A2A2A2S0S1S5R2A1G2A2S23A2S2RdS1S24R3A1S25R3A1A2A2S7S0RcS1S1bG0SaR6PaA2A2S1dG0SaR6S2bA2A2A2A2S0RcS1bG0SaR6PcA2A2A2A2S30S3S1fS3S21S3S2eR10R5A2M3R5A3S18RaA1R7R6A5S15S3S16R7R6SdS10S13S14A2M4SeS13S14S17RaA1S22S3G3R5A3A4SfG4A1A3A5A3F_;F_;F_;F_;FG0;Ftp0;Frho0;F_;F_;Fsz;F_;F_;Ftop;F_;Fhc;FK0;").
Proof.
  intros K0 hc HKD top Htop HKT sz Hsz Hc rho0 tp0 G0 Htol HDN0 Hhc HT0.
  lazy beta zeta delta [chkD] in Hc. splitC Hc. convC.
  pose proof (eseg_D_main K0 hc HKD sz Hsz rho0 tp0 G0 Htol HDN0 Hhc top Htop HT0 HKT) as T. lazy beta zeta in T.
  eapply T; clear T.
  all: dispC.
Qed.

Lemma JD_wrap : ltac2:(tb__ "0|0|
S4S1eF_;S4SbScS1cQ40A1A1ScS27A1S26S21S3R6R5R4R3R2R1A7S21S3S2eR7R6A2R6R5R4R3R2A7F_;Fmd;Ftr;Ftp;Frho;FG0;FK0;").
Proof. intros K0 G0 rho tp tr md [HK HD]. split; [split; [exact HK | lia] | exact HD]. Qed.

Lemma LQPA_unwrap : ltac2:(tb__ "0|2|
S4S1eF_;S4S6SbScS1cQ40A1A1S2fS15S3S16R3R2SdS10S13S14A2M0SeS13S14S17R4A1S22S3S2eR6R5A2R5A3A4SfG0A1M1A3R1A6S15S3S16R4R3SdG0SeS13S14S17R5A1S22S3R7R6A3A4G1A3R2A6F_;Fw;Ftp0;Frho0;Fsz;FG0;FK0;").
Proof.
  intros K0 G0 sz rho0 tp0 w (L & JL & rho' & tp' & Hin & Hag & Hsm & HJ).
  destruct Hin as [E|[]]. injection E as <- <-.
  exists (PostD sz), (JLD segsA K0 G0), rho', tp'. split; [left; reflexivity|]. split; [exact Hag|]. split; [exact Hsm|].
  destruct HJ as (G' & [HK _] & HD & HP & R1 & R2 & R3 & R4). exists G'.
  split; [exact HK|]. split; [exact HD|]. split; [exact HP|]. split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. exact R4.
Qed.

Theorem seg_D_common2 : ltac2:(tb__ "0|4|
S4S1eF_;S6S2cS3R2S16R1A4S2fOF_;S4S20S3R2R5R1A1A3FG;S4S32S3R3R6R1A1A3FG;S6S7S0Z7fff7f800000R1A2S0R1Z7fffff800000A2A2S4SbScS1cQ40M0A1A1M1ScS27A1S26RdR5R4R3R2R1A5S8S6S28S29R2A1A1R8A3F_;Fmd;Ftr;Ftp;Frho;FG;S6S7S0Z1M2R1A2S0R1S1aA2A2S8S11S2dR2A1S12A3SbG1S4S9S0R6S19A2S0S5R1A1S1S2aG2A2A2A2S0S1S5R2A1G2A2S23A2S2R10S1S24R3A1S25R3A1A2A2S7S0RcS1S1bG0SaR6PaA2A2S1dG0SaR6S2bA2A2A2A2S0RcS1bG0SaR6PcA2A2A2A2S31S3R10S1fS3S21S3R13R5A3S18RaA1R7R6A5S15S3S16R7R6SdS10S13S14A2M3SeS13S14S17RaA1S22S3R13R5A3A4SfG3A1A3A5A4F_;F_;F_;F_;FG0;Ftp0;Frho0;F_;F_;Fsz;F_;F_;Ftop;F_;F_;Fok;F_;Fhc;FK0;").
Proof.
  intros K0 hc HKD ok HKok HKokp top Htop HKT sz Hsz Hc rho0 tp0 G0 Htol HDN0 Hhc HT0.
  eapply triple_conseq; [| intros w Hw; exact (LQPA_unwrap K0 G0 sz rho0 tp0 w Hw) | exact (seg_D_commonK K0 hc HKD ok HKok HKokp top Htop HKT sz Hsz Hc rho0 tp0 G0 Htol HDN0 Hhc HT0)].
  intros w [Hsm HJ]. split; [exact Hsm | exact (JD_wrap K0 G0 _ _ _ _ HJ)].
Qed.

Theorem eseg_D_common2 : ltac2:(tb__ "0|4|
S4S1eF_;S6S2cS3R2S16R1A4S6S7S0Z7fff7f800000R1A2S0R1Z7fffff800000A2A2S4SbScS1cQ40M0A1A1M1ScS27A1S26RaR5R4R3R2R1A5S8S6S28S29R2A1A1R8A3F_;Fmd;Ftr;Ftp;Frho;FG;S6S7S0Z1M2R1A2S0R1S1aA2A2S8S11S2dR2A1S12A3SbG1S4S9S0R6S19A2S0S5R1A1S1S2aG2A2A2A2S0S1S5R2A1G2A2S23A2S2RdS1S24R3A1S25R3A1A2A2S7S0RcS1S1bG0SaR6PaA2A2S1dG0SaR6S2bA2A2A2A2S0RcS1bG0SaR6PcA2A2A2A2S30S3S1fS3S21S3R10R5A3S18RaA1R7R6A5S15S3S16R7R6SdS10S13S14A2M3SeS13S14S17RaA1S22S3R10R5A3A4SfG3A1A3A5A3F_;F_;F_;F_;FG0;Ftp0;Frho0;F_;F_;Fsz;F_;F_;Ftop;F_;Fhc;FK0;").
Proof.
  intros K0 hc HKD top Htop HKT sz Hsz Hc rho0 tp0 G0 Htol HDN0 Hhc HT0.
  eapply etriple_conseq; [| intros w Hw; exact (LQPA_unwrap K0 G0 sz rho0 tp0 w Hw) | exact (eseg_D_commonK K0 hc HKD top Htop HKT sz Hsz Hc rho0 tp0 G0 Htol HDN0 Hhc HT0)].
  intros w [Hsm HJ]. split; [exact Hsm | exact (JD_wrap K0 G0 _ _ _ _ HJ)].
Qed.
End SegD_main2.

(* [comment removed for export] *)
Module SegD2.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "ge"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "DG"; "dN"; "@Corelib.Init.Logic"; "and"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rw"; "valuation"; "@Corelib.Init.Datatypes"; "list"; "cons"; "nil"; "pair"; "prod"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states"; "NPRE"; "PostD"; "PreD"; "SZMAX"; "SZMAXT"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "bv_signed"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "alloc_top"; "event"; "m_vmmaps"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "V_DEPTH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_laws2"; "KD_laws2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "DNMAX"; "JD"; "JLD"; "dep_cost"; "droom"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget"; "KMAX"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA CompleteA SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import SegD_wf SegD_laws2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_states SegD_main SegD_chk.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_main OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_chk OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ik.SegD_main2.
Import ListNotations.
Open Scope Z_scope.

Theorem seg_D_sound2 : ltac2:(tb__ "0|4|
S5S20F_;S4S23S3R2S13R1A4S2bOF_;S5S21S3R2R5R1A1A3FG;S5S2cS3R3R6R1A1A3FG;S4S7S0Z7fff7f800000R1A2S0R1Z7fffff800000A2A2S5SaSbS19Q40M0A1A1M1SbS1dA1S1bRdR5R4R3R2R1A5S8S4S1cS1eR2A1A1R8A3F_;Fmd;Ftr;Ftp;Frho;FG;S4S7S0Z1M2R1A2S0R1S16A2A2SaG1S5S0S1S6R1A1G2A2S24A2S2ReS1S27R2A1S28R2A1A2A2S7S0RaS1S18G0S9R5PaA2A2S1aG0S9R5S22A2A2A2A2S0RaS18G0S9R5PcA2A2A2A2S2aS3ReS1fS3S25S3R11R4A3S15R8A1R6R5A5S12S3S13R6R5ScSfS10S11A2M3SeS10S11S14R8A1S26S3R11R4A3A4SdG3A1A3A5A4F_;F_;F_;FG;Ftp;Frho;F_;Fsz;F_;F_;Ftop;F_;F_;Fok;F_;Fhc;FK;").
Proof.
  intros K hc HKD ok HKok HKokp top Htop HKT sz Hsz rho tp G HDN Hhc HT0.
  assert (HszT : 1 <= sz <= SZMAXT) by (unfold SZMAX, SZMAXT in *; lia).
  exact (seg_D_common2 K hc HKD ok HKok HKokp top Htop HKT sz HszT (chkD_allT sz HszT) rho tp G (or_introl (proj2 Hsz)) HDN Hhc HT0).
Qed.

Theorem seg_D_sound2T : ltac2:(tb__ "0|4|
S5S20F_;S4S23S3R2S13R1A4S2bOF_;S5S21S3R2R5R1A1A3FG;S5S2cS3R3R6R1A1A3FG;S4S7S0Z7fff7f800000R1A2S0R1Z7fffff800000A2A2S5SaSbS19Q40M0A1A1M1SbS1dA1S1bRdR5R4R3R2R1A5S8S4S1cS1eR2A1A1R8A3F_;Fmd;Ftr;Ftp;Frho;FG;S4S7S0Z1M2R1A2S0R1S17A2A2SaG1S5S0S1S6R1A1G2A2S24A2S0S6R2A1S1S2dG2A2A2S2RfS1S27R3A1S28R3A1A2A2S7S0RbS1S18G0S9R6PaA2A2S1aG0S9R6S22A2A2A2A2S0RbS18G0S9R6PcA2A2A2A2S2aS3RfS1fS3S25S3R12R5A3S15R9A1R7R6A5S12S3S13R7R6ScSfS10S11A2M3SeS10S11S14R9A1S26S3R12R5A3A4SdG3A1A3A5A4F_;F_;F_;F_;FG;Ftp;Frho;F_;Fsz;F_;F_;Ftop;F_;F_;Fok;F_;Fhc;FK;").
Proof.
  intros K hc HKD ok HKok HKokp top Htop HKT sz Hsz rho tp G HDN HKM Hhc HT0.
  exact (seg_D_common2 K hc HKD ok HKok HKokp top Htop HKT sz Hsz (chkD_allT sz Hsz) rho tp G (or_intror HKM) HDN Hhc HT0).
Qed.

Theorem seg_D_complete2 : ltac2:(tb__ "0|4|
S5S20F_;S4S23S3R2S13R1A4S4S7S0Z7fff7f800000R1A2S0R1Z7fffff800000A2A2S5SaSbS19Q40M0A1A1M1SbS1dA1S1bRaR5R4R3R2R1A5S8S4S1cS1eR2A1A1R8A3F_;Fmd;Ftr;Ftp;Frho;FG;S4S7S0Z1M2R1A2S0R1S16A2A2SaG1S5S0S1S6R1A1G2A2S24A2S2RbS1S27R2A1S28R2A1A2A2S7S0RaS1S18G0S9R5PaA2A2S1aG0S9R5S22A2A2A2A2S0RaS18G0S9R5PcA2A2A2A2S29S3S1fS3S25S3ReR4A3S15R8A1R6R5A5S12S3S13R6R5ScSfS10S11A2M3SeS10S11S14R8A1S26S3ReR4A3A4SdG3A1A3A5A3F_;F_;F_;FG;Ftp;Frho;F_;Fsz;F_;F_;Ftop;F_;Fhc;FK;").
Proof.
  intros K hc HKD top Htop HKT sz Hsz rho tp G HDN Hhc HT0.
  assert (HszT : 1 <= sz <= SZMAXT) by (unfold SZMAX, SZMAXT in *; lia).
  exact (eseg_D_common2 K hc HKD top Htop HKT sz HszT (chkD_allT sz HszT) rho tp G (or_introl (proj2 Hsz)) HDN Hhc HT0).
Qed.

Theorem seg_D_complete2T : ltac2:(tb__ "0|4|
S5S20F_;S4S23S3R2S13R1A4S4S7S0Z7fff7f800000R1A2S0R1Z7fffff800000A2A2S5SaSbS19Q40M0A1A1M1SbS1dA1S1bRaR5R4R3R2R1A5S8S4S1cS1eR2A1A1R8A3F_;Fmd;Ftr;Ftp;Frho;FG;S4S7S0Z1M2R1A2S0R1S17A2A2SaG1S5S0S1S6R1A1G2A2S24A2S0S6R2A1S1S2dG2A2A2S2RcS1S27R3A1S28R3A1A2A2S7S0RbS1S18G0S9R6PaA2A2S1aG0S9R6S22A2A2A2A2S0RbS18G0S9R6PcA2A2A2A2S29S3S1fS3S25S3RfR5A3S15R9A1R7R6A5S12S3S13R7R6ScSfS10S11A2M3SeS10S11S14R9A1S26S3RfR5A3A4SdG3A1A3A5A3F_;F_;F_;F_;FG;Ftp;Frho;F_;Fsz;F_;F_;Ftop;F_;Fhc;FK;").
Proof.
  intros K hc HKD top Htop HKT sz Hsz rho tp G HDN HKM Hhc HT0.
  exact (eseg_D_common2 K hc HKD top Htop HKT sz Hsz (chkD_allT sz Hsz) rho tp G (or_intror HKM) HDN Hhc HT0).
Qed.
End SegD2.

