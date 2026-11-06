(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Ox.F128_053.   (* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c0 bv.
From Stdlib Require FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c5.

(* [comment removed for export] *)
Module SpineMallocSecOKP.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "rm"; "rl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_sec"; "DG"; "sec_chunk"; "aa_geom"; "aa_Km"; "aa_fs_busy"; "aa_live"; "ageom"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "@Corelib.Init.Datatypes"; "list"; "pair"; "prod"; "None"; "length"; "option"; "nil"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "False"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "jpredA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "Kc_ok"; "ulink"; "UStopLeOrPc"; "mem_keptA"; "ustop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "secmapsize"; "stopJ_stable"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "div"; "of_nat"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger"; "sepZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "dblocks"; "dfp_static"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bp.DepotCallS"; "AXK"; "dlink"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "Sh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SecBump"; "bumpP"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3"; "clsP"; "slink"; "JGs"; "JGsC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineMallocSec4"; "slink4"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec2"; "IMG_S"].
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
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.RebuildN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.MmapSymA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.CertMallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.CertMallocSN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.InvD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.SecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.SecRoom OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineMallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bp.DepotCallS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bw.SecLinks.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c0.SpineMallocSecOK.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section OKP.
Variable nW : nat. Variable st : ustop. Variable nx : positive. Variable hi : bool.
Let W : list ulink := Wcan nW.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTS : ltac2:(tb__ "0|0|
SeS3eVCST;R1A2S3eS48R2A2S1dF_;F_;Fa;").
Hypothesis HCSTD : ltac2:(tb__ "0|0|
SeS3eVCST;R1A2S1cS35R2A1A1F_;Fa;").
Let JGs : ltac2:(tb__ "0|0|
S5S5F_;S5S25S1S11Q40A1S24Fa;Frho;FKc;FA;FAX;") := ltac2:(tb__ "0|0|
S44VnW;Vst;Vnx;A3").
Let JGsC : ltac2:(tb__ "0|0|
S5S5F_;S5S25S1S11Q40A1S24Fa;Frho;FKc;FA;FAX;") := ltac2:(tb__ "0|0|
S45VnW;Vst;Vnx;A3").
Variable Posts : ltac2:(tb__ "0|0|
S5S25S13S15S47S3dA2A1F_;F_;").

Variables (E1 D2 T4a T4b C5a C5b : axst).

Hypothesis HG12 : ltac2:(tb__ "0|5|
S1fOF_;S5S25S1S11Q40M0A1M1S13G1A1M2S20S2cVW;Vst;A2S26R6A1S23S0R9S22R7A1A3S42Vhi;S10G0R6A2S2bS10G0S2R7PcM3A2A2A1A3S1S1G2S43S10G0RaA2S2bS10G0S2RbG3A2A2A1RbR3A4S1eS0RfS21S0VJGs;S5R1LX;M4ReRdR4RbA5VD2;R3R2A5R9A4F_;FtpY;FrhoY;Frho';S1S1eS0RdS21S0VJGsC;G4RcRbRaR9A5VE1;R1R8A5R7A4FrhoX;F_;F_;F_;F_;F_;FQ;Ftp;Fa;Frho;FKc;FA;Fok;").
Hypothesis HG3 : ltac2:(tb__ "0|7|
S1fOF_;S5S25S1S11Q40M0A1M1S20S2cVW;Vst;A2S26R5A1S23S0R8S22R6A1A3S39S0R9S22R7A1A3S2fS2eS31S17S8S6R9A1A2A1Z1A2S32Z2Z14A2A2SeS1bS2dS3aS10G0R8A2A1M2R1A2S2fR1S2eG2S30S2bS10G0S2R9PcM3A2A2A1Z8A2A2A2A2S1cS1aS18S11Q8A1M4A1S3RaS12G0R2A2A2S16G4A1A3A1F_;Fz;S1S1S13G1A1M5S46S9ReA1S10G0RbA2S2bS10G0S2RcG3A2A2A1RcR3A5S1eS0R10S21S0VJGs;S5S3fR1A1LX;RfReR4RcA5VT4a;R3R2A5RbA4F_;FtY;FrY;Frho'';S1G5S1eS0RfS21S0VJGs;S5R1LX;M6ReRdRcRbA5VT4b;R2R1A5RaA4FtY;FrY;S1G5S1eS0R10S21S0VJGs;G6RfReRdRcA5VD2;R2R1A5RbA4FtX;FrX;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Hypothesis HG41a : ltac2:(tb__ "0|5|
S1fOF_;S5S25S1S11Q40M0A1M1S20S1aS2aVst;S28A3S1aS13S27A1VW;S19S27A1A3F_;S2cVW;Vst;A2S26R6A1S23S0R9S22R7A1A3S39S0RaS22R8A1A3S7S1S1S13G1A1M2S15SeSeA2M3S36G3R1S34R5A1A3S33R2S14SeSeS10G0RdA2S2bS10G0S2RePcA2A2A1A4A2F_;Fbn;S38R5RdR4A3S1eS0R11S21S0VJGs;S37S5S3fR1A1LX;M4R6A2R10RfR5RdA5VC5a;R4R3A5RcA4F_;F_;Ftp';FrhoX;Frho';FG2;S1G2S1eS0ReS21S0VJGs;G4RdRcRbRaA5VT4a;R2R1A5R9A4FtX;FrX;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Hypothesis HG41b : ltac2:(tb__ "0|5|
S1fOF_;S5S25S1S11Q40M0A1M1S20S1aS2aVst;S28A3S1aS13S27A1VW;S19S27A1A3F_;S2cVW;Vst;A2S26R6A1S23S0R9S22R7A1A3S39S0RaS22R8A1A3S7S1S1S13G1A1M2S15SeSeA2M3S36G3R1S34R5A1A3S33R2S14SeSeS10G0RdA2S2bS10G0S2RePcA2A2A1A4A2F_;Fbn;S38R5RdR4A3S1eS0R11S21S0VJGs;S37S5R1LX;M4R6A2R10RfR5RdA5VC5b;R4R3A5RcA4F_;F_;Ftp';FrhoX;Frho';FG2;S1G2S1eS0ReS21S0VJGs;G4RdRcRbRaA5VT4b;R2R1A5R9A4FtX;FrX;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Hypothesis HTLa : ltac2:(tb__ "0|8|
S1fOF_;S5S25S1S1S11Q40M0A1M1S13G1A1M2S7S2cVW;Vst;A2S26R7A1S23S0RaS22R8A1A3SfS1aG1S2R8R1A2S2R9R1A2A3Fi;SfS1aS13S11Q8A1M3A1S4R9R1A2S4RaR1A2A3Fl;S29VCST;VXGL;RcRcS3RaA1S3R9A1A6S2dS31S17S8S6RdA1A2A1SaRdA1A2S15SeSeA2M4S36G4R1S34R9A1A3S33R2S14SeSeS10G0RcA2M5S2bS10G0S2RdPcA2A2A1M6A4A2F_;Fbn;SeS1bS2dS3aG5A1M7R1A2S2fR1S2eG7S30G6Z8A2A2A2A2S1cS1aS18G3A1S3ReS12G0R2A2A2S16G3A1A3A1F_;Fz;S1G2S1eS0R13S21S0VJGs;S37S5S3fR1A1LX;RcA2R12R11RfReA5VC5a;R2R1A5S3cS0S3bR10RdVPosts;R12R11A2A5A4FtX;FrX;F_;F_;F_;F_;F_;F_;F_;F_;F_;FG2;Ftp0;Fa;Frho;Frho0;FKc;FA;Fok;").
Hypothesis HTLb : ltac2:(tb__ "0|8|
S1fOF_;S5S25S1S1S11Q40M0A1M1S13G1A1M2S7S2cVW;Vst;A2S26R7A1S23S0RaS22R8A1A3SfS1aG1S2R8R1A2S2R9R1A2A3Fi;SfS1aS13S11Q8A1M3A1S4R9R1A2S4RaR1A2A3Fl;S29VCST;VXGL;RcRcS3RaA1S3R9A1A6S2dS31S17S8S6RdA1A2A1SaRdA1A2S15SeSeA2M4S36G4R1S34R9A1A3S33R2S14SeSeS10G0RcA2M5S2bS10G0S2RdPcA2A2A1M6A4A2F_;Fbn;SeS1bS2dS3aG5A1M7R1A2S2fR1S2eG7S30G6Z8A2A2A2A2S1cS1aS18G3A1S3ReS12G0R2A2A2S16G3A1A3A1F_;Fz;S1G2S1eS0R13S21S0VJGs;S37S5R1LX;RcA2R12R11RfReA5VC5b;R2R1A5S3cS0S3bR10RdVPosts;R12R11A2A5A4FtX;FrX;F_;F_;F_;F_;F_;F_;F_;F_;F_;FG2;Ftp0;Fa;Frho;Frho0;FKc;FA;Fok;").

Lemma c5_pure_P : ltac2:(tb__ "0|7|
S5S5F_;S7S5S25S1S1S1S1S11Q40M0A1M1S1S13G1A1S13S41A1S40S5S1aSdS9ReR1A1A1S9R1A1A3FX;S5S1aS13S8A1S6RfR1A1A1S6R1A1A3FX;S5S1aS13S15SeSeA2M2A1M3ScR10R1A1A1ScR1A1A3FX;S5S1aS13G3A1SbR11R1A1A1SbR1A1A3FX;S10G0R9A2SeS2bS10G0S2RePcM4A2A2A1SeS43R2R1RfReA4S46S9R12A1R3R2RfReA5S38R14RfReA3G2S36G2R1S34R16A1A3S33R2S14SeSeR7R6A4A2F_;Fbn;VJGs;S37R17R16A2R15R14R10RfReRdRcRbA9S1bS29VCST;VXGL;R16R16S3R14A1S3R11A1A6S1bSeS1bS2dS3aR8A1M5R1A2S2fR1S2eG5S30S2bS10G0S2R12G4A2A2A1Z8A2A2A2A2S1cS1aS18S11Q8A1M6A1S3R13S12G0R2A2A2S16G6A1A3A1F_;Fz;S1bSfS1aG1S2R12R1A2S2R15R1A2A3Fi;S1bSfS1aS13G6A1S4R12R1A2S4R15R1A2A3Fl;G2S36G2R1S34R18A1A3S33R2S14SeSeR9S2bS10G0S2R13G4A2A2A1A4A2F_;Fbn;A2A2A2A2F_;F_;F_;F_;F_;TL;Tua;F_;F_;F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho3;Frho2;Frho1;Frho;FKc;FA;FG2;FBX;").
Proof.
  intros BX G2 A Kc rho rho1 rho2 rho3 a r tp tr md BXg BXs BXl BXf ua L SL1 SL4 DL HDB HJ.
  assert (E12 : rw rho3 12%positive = rw rho 12%positive).
  { destruct SL1 as (W1 & _). destruct SL4 as (W2 & _). destruct DL as (W3 & _). rewrite W3, W2. apply W1. }
  unfold JGs, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3.JGs in HJ. rewrite E12 in HJ. fold L in HJ. cbn zeta in HJ.
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

Lemma d2_pure_P : ltac2:(tb__ "0|2|
S5S25S1S11Q40A1M0S1S13G0A1S13S41A1S40VJGs;S5R1LX;R8R7R6R5R4R3R2R1A9S1bS2fS2eS31S17S8S6R9A1A2A1M1Z1A2S32Z2Z14A2A2S2dG1SaR9A1A2A2F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a r tp tr md HJ. unfold JGs, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3.JGs in HJ. cbn zeta in HJ.
  destruct HJ as (_ & _ & HA & _ & _ & _ & _ & _ & _ & HBO).
  set (nv := bv_unsigned (rw rho 12%positive)) in *.
  split.
  - pose proof (AInvA_sec_bound segsA _ r tp md HA) as SB. cbn [aa_sec bumpV] in SB.
    assert (E : large_live (bumpV A nv) = large_live A) by reflexivity. rewrite E in SB.
    pose proof (budget_ok_alloc_room A nv HBO) as RM. unfold sec_room, SEC_SLACK in RM. clear -SB RM. lia.
  - destruct HA as (_ & _ & _ & _ & HM & _). destruct HM as (_ & _ & _ & _ & _ & _ & _ & HLd).
    destruct HLd as (_ & _ & _ & _ & _ & _ & _ & _ & L9 & _). cbn [aa_sec aa_Km bumpV] in L9. exact L9.
Qed.

Theorem sec_ok_chain_P : ltac2:(tb__ "0|2|
S1fOF_;S5S25S1S11Q40M0A1M1S13G1A1S1aS2aVst;S28A3S1aS13S27A1VW;S19S27A1A3F_;S2cVW;Vst;A2S26R6A1S23S0R9S22R7A1A3S39S0RaS22R8A1A3S42Vhi;S10G0R7A2S2bS10G0S2R8PcA2A2A1A3S1S1eS0RdS21S0VJGsC;S5R1LX;RcRbRaR9A5VE1;R1R8A5S3cS0S3bRaR8VPosts;RcRbA2A5A4FrhoX;F_;F_;F_;F_;F_;F_;Ftp;Fa;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho a tp HW HUS HKc Hokl Hokpl HC rhoX.
  set (ua := bv_unsigned a) in *. set (L := secmapsize (bv_unsigned (rw rho 12%positive))) in *.
  apply (HG12 ok A Kc rho a tp _ HUS HKc Hokl HC). intros rho1 rhoY tpY SL1.
  apply (triple_pre_pure segsA ok _ _ (Z.of_nat (length (aa_sec A)) + 1 < 2 ^ 20 /\ Z.of_nat (length (aa_sec A)) <= aa_Km A)).
  { intros [tr [ms md]] Hw. exact (d2_pure_P A Kc rho1 a rhoY tpY tr md (proj2 Hw)). }
  intros [HRM HL9].
  assert (E1r : rw rho1 12%positive = rw rho 12%positive) by (destruct SL1 as (W1 & _); apply W1).
  assert (RD1 : forall z, Sh ua <= z < Sh ua + L / 8 -> rm rho1 (Z_to_bv 64 z) <> None) by (destruct SL1 as (_ & _ & _ & D1); exact D1).
  apply (HG3 ok A Kc rho1 a _ HUS HKc Hokl Hokpl HRM); [rewrite E1r; exact RD1 | |].
  -
    rewrite E1r. fold ua L. intros rho2 rY tY SL4.
    assert (E2r : rw rho2 12%positive = rw rho 12%positive) by (destruct SL4 as (W2 & _); rewrite W2; exact E1r).
    apply (HG41a ok A Kc rho2 a _ HW HUS HKc Hokl Hokpl). rewrite E2r. fold ua L. intros G2 rho3 rhoX3 tp3 HDB DL.
    apply (triple_pre_pure segsA ok _ _ _ (fun w Hw => c5_pure_P (fun X : AA => bumpP X) G2 A Kc rho rho1 rho2 rho3 a rhoX3 tp3 (w_tr w) (cfg_model (w_cfg w))
             (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) SL1 SL4 DL HDB (proj2 Hw))).
    intros (HK & RD & HWr & HLr & HDB3).
    exact (HTLa ok A Kc rho rho3 a tp G2 HUS HKc Hokl HWr HLr HK HL9 HDB3 RD rhoX3 tp3).
  -
    intros rY tY.
    apply (HG41b ok A Kc rho1 a _ HW HUS HKc Hokl Hokpl). rewrite E1r. fold ua L. intros G2 rho3 rhoX3 tp3 HDB DL.
    apply (triple_pre_pure segsA ok _ _ _ (fun w Hw => c5_pure_P (fun X : AA => X) G2 A Kc rho rho1 rho1 rho3 a rhoX3 tp3 (w_tr w) (cfg_model (w_cfg w))
             (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) SL1 (slink4_refl (aa_geom A) ua L rho1 RD1) DL HDB (proj2 Hw))).
    intros (HK & RD & HWr & HLr & HDB3).
    exact (HTLb ok A Kc rho rho3 a tp G2 HUS HKc Hokl HWr HLr HK HL9 HDB3 RD rhoX3 tp3).
Qed.
End OKP.
End SpineMallocSecOKP.

(* [comment removed for export] *)
Module CDepotCallM.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Specif"; "sig"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c4.CDepotCallM.INST"; "T4_i"; "nobj_i"; "@Corelib.Init.Datatypes"; "prod"; "list"; "nil"; "option"; "pair"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bv.CDepotCallW"; "T40"; "T4a"; "T4b"; "T4c"; "T4d"; "T4m1"; "T4m2"; "T4m3"; "X4"; "X4a"; "X4b"; "X4c"; "X4r"; "@Stdlib.ZArith.BinInt.Z"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states"; "PreD"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocSP SegD_wf SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CDepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bv.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_refl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aq.SpineCallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.SpineCallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bk.SpineCallocE OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CDepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bv.CDepotCallW.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a8.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a8.CallocMemoSP.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let st : ustop := UStopLe. Let tmax : Z := 2.

Lemma by_casesN : ltac2:(tb__ "0|2|
SbOF_;R1Z1M0A1R2Z2M1A1SbS2S1cG0R1A2S1cR1G1A2A2R5R2A1F_;Fsz;F_;F_;FP;").
Proof. intros P H1 H2 sz Hsz. assert (E : sz = 1 \/ sz = 2) by lia. destruct E as [-> | ->]; assumption. Qed.
Ltac memo_rw t M := lazymatch goal with |- context [t] => pattern t; refine (@eq_ind_r _ (proj1_sig M) _ _ t (proj2_sig M)); cbv beta | _ => fail "memo_rw: stage term not found" t end.
Ltac vmc := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.
Definition mE : {x | E4d (Wcan 0) st tmax = x} := exist _ m_E4d m_E4d_eq.
Definition mC5 : {x | C5 (Wcan 0) st tmax = x} := exist _ m_C5 m_C5_eq.
Lemma mXr_1 : ltac2:(tb__ "0|0|
S3S0S0S1S0S1bU0Vst;Vtmax;Z1A4R1A3Lx;A2"). Proof. eexists. unfold X4r, X4f. memo_rw (E4d (Wcan 0) st tmax) mE. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mXa_1 : ltac2:(tb__ "0|0|
S3S0S0S1S0S18U0Vst;Vtmax;Z1A4R1A3Lx;A2"). Proof. eexists. unfold X4a. memo_rw (X4r 0%nat st tmax 1) mXr_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mXb_1 : ltac2:(tb__ "0|0|
S3S0S0S1S0S19U0Vst;Vtmax;Z1A4R1A3Lx;A2"). Proof. eexists. unfold X4b. memo_rw (X4a 0%nat st tmax 1) mXa_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mXc_1 : ltac2:(tb__ "0|0|
S3S0S0S1S0S1aU0Vst;Vtmax;Z1A4R1A3Lx;A2"). Proof. eexists. unfold X4c. memo_rw (X4b 0%nat st tmax 1) mXb_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mX_1 : ltac2:(tb__ "0|0|
S3S0S0S1S0S17U0Vst;Vtmax;Z1A4R1A3Lx;A2"). Proof. eexists. unfold X4. memo_rw (X4c 0%nat st tmax 1) mXc_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mXr_2 : ltac2:(tb__ "0|0|
S3S0S0S1S0S1bU0Vst;Vtmax;Z2A4R1A3Lx;A2"). Proof. eexists. unfold X4r, X4f. memo_rw (E4d (Wcan 0) st tmax) mE. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mXa_2 : ltac2:(tb__ "0|0|
S3S0S0S1S0S18U0Vst;Vtmax;Z2A4R1A3Lx;A2"). Proof. eexists. unfold X4a. memo_rw (X4r 0%nat st tmax 2) mXr_2. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mXb_2 : ltac2:(tb__ "0|0|
S3S0S0S1S0S19U0Vst;Vtmax;Z2A4R1A3Lx;A2"). Proof. eexists. unfold X4b. memo_rw (X4a 0%nat st tmax 2) mXa_2. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mXc_2 : ltac2:(tb__ "0|0|
S3S0S0S1S0S1aU0Vst;Vtmax;Z2A4R1A3Lx;A2"). Proof. eexists. unfold X4c. memo_rw (X4b 0%nat st tmax 2) mXb_2. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mX_2 : ltac2:(tb__ "0|0|
S3S0S0S1S0S17U0Vst;Vtmax;Z2A4R1A3Lx;A2"). Proof. eexists. unfold X4. memo_rw (X4c 0%nat st tmax 2) mXc_2. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.

Definition gP (o : option (wsub * list sobj * axst)) : wsub * list sobj * axst := ltac2:(tb__ "0|4|
S9S6S6S1dS7SdA1M0A2S0A2M1A1G1Lo;Vo;G1R1Lx;SaS6S7S6ScSeA2M2A1M3G0A2S0SaG3G0S8G2A1S8SdA1A4S1eZ0A1A4X9x2").
Definition CP1 : wsub * list sobj * axst := Eval vm_compute in (gP (call_pack (proj1_sig mX_1) 1)).
Definition CP2 : wsub * list sobj * axst := Eval vm_compute in (gP (call_pack (proj1_sig mX_2) 2)).
Definition CP (sz : Z) : wsub * list sobj * axst := if sz =? 1 then CP1 else CP2.
Definition s4_i (sz : Z) : wsub := fst (fst (CP sz)).
Definition R4_i (sz : Z) : list sobj := snd (fst (CP sz)).
Definition T4_i (sz : Z) : axst := snd (CP sz).
Definition nobj_i : nat := 48%nat.
Lemma mT0_1 : ltac2:(tb__ "0|0|
S3S0S0S1S0SfU0Vst;Vtmax;S4Z1A5R1A3Lx;A2"). Proof. eexists. unfold T40. memo_rw (X4 0%nat st tmax 1) mX_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mTa_1 : ltac2:(tb__ "0|0|
S3S0S0S1S0S10U0Vst;Vtmax;S4Z1A5R1A3Lx;A2"). Proof. eexists. unfold T4a. memo_rw (T40 0%nat st tmax T4_i 1) mT0_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mTb_1 : ltac2:(tb__ "0|0|
S3S0S0S1S0S11U0Vst;Vtmax;S4Z1A5R1A3Lx;A2"). Proof. eexists. unfold T4b. memo_rw (T4a 0%nat st tmax T4_i 1) mTa_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mTc_1 : ltac2:(tb__ "0|0|
S3S0S0S1S0S12U0Vst;Vtmax;S4S5Z1A6R1A3Lx;A2"). Proof. eexists. unfold T4c. memo_rw (T4b 0%nat st tmax T4_i 1) mTb_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mT1_1 : ltac2:(tb__ "0|0|
S3S0S0S1S0S14U0Vst;Vtmax;S4S5Z1A6R1A3Lx;A2"). Proof. eexists. unfold T4m1. memo_rw (T4c 0%nat st tmax T4_i nobj_i 1) mTc_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mT2_1 : ltac2:(tb__ "0|0|
S3S0S0S1S0S15U0Vst;Vtmax;S4S5Z1A6R1A3Lx;A2"). Proof. eexists. unfold T4m2. memo_rw (T4m1 0%nat st tmax T4_i nobj_i 1) mT1_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mT3_1 : ltac2:(tb__ "0|0|
S3S0S0S1S0S16U0Vst;Vtmax;S4S5Z1A6R1A3Lx;A2"). Proof. eexists. unfold T4m3. memo_rw (T4m2 0%nat st tmax T4_i nobj_i 1) mT2_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mTd_1 : ltac2:(tb__ "0|0|
S3S0S0S1S0S13U0Vst;Vtmax;S4S5Z1A6R1A3Lx;A2"). Proof. eexists. unfold T4d. memo_rw (T4m3 0%nat st tmax T4_i nobj_i 1) mT3_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mT0_2 : ltac2:(tb__ "0|0|
S3S0S0S1S0SfU0Vst;Vtmax;S4Z2A5R1A3Lx;A2"). Proof. eexists. unfold T40. memo_rw (X4 0%nat st tmax 2) mX_2. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mTa_2 : ltac2:(tb__ "0|0|
S3S0S0S1S0S10U0Vst;Vtmax;S4Z2A5R1A3Lx;A2"). Proof. eexists. unfold T4a. memo_rw (T40 0%nat st tmax T4_i 2) mT0_2. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mTb_2 : ltac2:(tb__ "0|0|
S3S0S0S1S0S11U0Vst;Vtmax;S4Z2A5R1A3Lx;A2"). Proof. eexists. unfold T4b. memo_rw (T4a 0%nat st tmax T4_i 2) mTa_2. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mTc_2 : ltac2:(tb__ "0|0|
S3S0S0S1S0S12U0Vst;Vtmax;S4S5Z2A6R1A3Lx;A2"). Proof. eexists. unfold T4c. memo_rw (T4b 0%nat st tmax T4_i 2) mTb_2. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mT1_2 : ltac2:(tb__ "0|0|
S3S0S0S1S0S14U0Vst;Vtmax;S4S5Z2A6R1A3Lx;A2"). Proof. eexists. unfold T4m1. memo_rw (T4c 0%nat st tmax T4_i nobj_i 2) mTc_2. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mT2_2 : ltac2:(tb__ "0|0|
S3S0S0S1S0S15U0Vst;Vtmax;S4S5Z2A6R1A3Lx;A2"). Proof. eexists. unfold T4m2. memo_rw (T4m1 0%nat st tmax T4_i nobj_i 2) mT1_2. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mT3_2 : ltac2:(tb__ "0|0|
S3S0S0S1S0S16U0Vst;Vtmax;S4S5Z2A6R1A3Lx;A2"). Proof. eexists. unfold T4m3. memo_rw (T4m2 0%nat st tmax T4_i nobj_i 2) mT2_2. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma mTd_2 : ltac2:(tb__ "0|0|
S3S0S0S1S0S13U0Vst;Vtmax;S4S5Z2A6R1A3Lx;A2"). Proof. eexists. unfold T4d. memo_rw (T4m3 0%nat st tmax T4_i nobj_i 2) mT3_2. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Definition sd_1 : wsub := Eval vm_compute in (infer_sub GW (ax_S (proj1_sig mTd_1)) (ax_S (proj1_sig mC5))).
Definition sd_2 : wsub := Eval vm_compute in (infer_sub GW (ax_S (proj1_sig mTd_2)) (ax_S (proj1_sig mC5))).
Definition sd_i (sz : Z) : wsub := if sz =? 1 then sd_1 else sd_2.

End INST.
End CDepotCallM.

(* [comment removed for export] *)
Module SpineMallocSec6L.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "@Corelib.Init.Datatypes"; "list"; "bool"; "true"; "nil"; "cons"; "prod"; "option"; "Some"; "app"; "pair"; "None"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_setS"; "entailsA"; "la_state"; "leafA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "valuation"; "holds"; "sobj"; "sv"; "ss_next"; "ss_facts"; "SLit"; "SPBranch"; "sprop_below"; "swf"; "SVar"; "rw"; "DUnknown"; "SAlu"; "SPUle"; "cell"; "eval"; "mkObj"; "obj_range"; "rm"; "ss_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_geom"; "ageom"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "ulink"; "Kc_ok"; "UStopLeOrPc"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "ustop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c4.SpineMallocSec6L.SEC6L"; "F_low"; "F_g7L"; "F_g8L"; "F_g9L"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_GEU"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3"; "skel"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "div"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.CertMallocSV"; "F_A"; "L3"; "B3"; "END8"; "RUE"; "UE9"; "a2e6"; "@Stdlib.Lists.List"; "forallb"; "In"; "incl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "secmapsize"; "stopJ_stable"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "check_cfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP"; "MSENT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.CertMallocSS"; "V_MS"; "nxS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocST"; "O_1"; "O_2"; "Pret_ms"; "carveS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "Sh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3"; "JGs"; "SKEL0"; "range_noband"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA EntailA CFGA GlueA GlueA2 SummaryA SysCallA MmapA MmapFixedA LedgerA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocS4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RebuildM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require MmapSymA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ae.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocSec SpineMallocSec2 SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bt.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require EnsureMapA DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SecLog2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require q0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bw.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SpineMallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.RebuildN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.MmapSymA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.CertMallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.CertMallocSN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.SegD_cost OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.LedgerLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.InvD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.DepotK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.SecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SecReveal OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvReveal OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.EnsureMapA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SecLog2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.InvEnsure OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.CertMallocSU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineMallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bw.SpineMallocSec5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.DepotKP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bp.DepotCallS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.CertMallocSV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c0.SpineMallocSec6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section SEC6L.
Variable nW : nat. Variable st : ustop. Variable tmax : Z.
Let W : list ulink := Wcan nW.
Let segs : list Segment := segsA.
Variable nx : positive.
Hypothesis Hnx : ltac2:(tb__ "0|0|
S0S44S69VW;Vst;Vtmax;A3Vnx;A3").
Hypothesis NXG : ltac2:(tb__ "0|0|
S0S4S5fS6eVnx;A2S5A3").
Let GS : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3.GS nx.
Let JG (BX : AA -> AA) : AA -> KcA -> valuation -> word -> jpredA := ltac2:(tb__ "0|0|
S71VnW;Vst;Vnx;VBX;A4").

Definition F_low : sprop := ltac2:(tb__ "0|0|
S23S22S46S1fVnx;A1S1fS68A1A3S1bZ7fff7000A1A2").

Lemma low_FA : ltac2:(tb__ "0|1|
S2aS2aFx;S2aS30S15S2dQ40A1M0S15S3G0A1S3S3fA1S3eS2aS0S2cS2bRaR1A1A1S2bR1A1A3FX;VJG;RaR9R8R7R6R5R4R3R2A9S16R6S38A2S3cS14S16R7A1S52Vnx;A1A3F_;F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FBX;").
Proof.
  intros BX A Kc rho a r tp tr md BXg HJ HL.
  pose proof (JGs_rigidS nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (_ & Enx & _ & E142 & _ & _ & E155 & _).
  pose proof (JGs_nums nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (HN & SMB & _ & _ & IMG & HTOP & _). cbn zeta in *.
  destruct HJ as (_ & _ & HA & HP & _).
  pose proof (proj1 HA) as HG. rewrite BXg in HG. cbn [aa_geom bumpV] in HG.
  pose proof (geom_nums _ HG) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S1 & S2 & _). rewrite kSpaceSize_val in S2. unfold HIGH_SHADOW_END in S1.
  pose proof (urange a) as Ra. unfold IMG_HI in IMG.
  set (ua := bv_unsigned a) in *. set (L := secmapsize (bv_unsigned (rw rho 12%positive))) in *. set (SB := ag_spacebeg (aa_geom A)) in *.
  pose proof (topG_range (aa_geom A)) as TG.
  assert (RSB : 0 <= SB < 2 ^ 64) by (clear -S1 S2 TG; lia).
  assert (RL : 0 <= L < 2 ^ 64) by (clear -SMB HN; lia).
  unfold F_low in HL. cbn [holds eval] in HL. rewrite Enx, E142, add_val in HL. fold ua L in HL.
  rewrite (u64_lit L RL) in HL. rewrite Z.mod_small in HL by (clear -IMG HTOP SMB; lia). rewrite u64_lit in HL by (clear; lia).
  unfold F_A. apply Forall_cons; [|apply Forall_nil]. cbn [holds eval]. rewrite Enx, E142, E155, add_val. fold ua L SB.
  rewrite (u64_lit L RL), (u64_lit SB RSB). rewrite Z.mod_small by (clear -IMG HTOP SMB; lia). clear -HL S1. lia.
Qed.

Definition F_g7L : list sprop := ltac2:(tb__ "0|0|
S7S14S1cS45S1bZ7fff7fffA1S56Vnx;A1A3S6S14A1A3").
Definition F_g8L : list sprop := ltac2:(tb__ "0|0|
S7S14S1cS45S1bZ7fff7fffA1S55Vnx;A1A3S6S14A1A3").
Definition F_g9L : list sprop := ltac2:(tb__ "0|0|
S7S14S1cS45S1bZ7fff7fffA1S57Vnx;A1A3S6S14A1A3").

Lemma low_end : ltac2:(tb__ "0|2|
S2aS2aF_;S2aS30S15S2dQ40M0A1M1S15S3G1A1S3S3fA1S3eVJG;R9R8R7R6R5R4R3R2R1A9S16R5S38A2S4bS4cS2eG0R7A2S5dS2eG0S20R8PcA2A2A1A2Z7fff7000A2F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FBX;").
Proof.
  intros BX A Kc rho a r tp tr md HJ HL.
  pose proof (JGs_rigidS nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (_ & Enx & _ & E142 & _).
  pose proof (JGs_nums nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (HN & SMB & _ & _ & IMG & HTOP & _). cbn zeta in *.
  pose proof (urange a) as Ra. unfold IMG_HI in IMG.
  set (ua := bv_unsigned a) in *. set (L := secmapsize (bv_unsigned (rw rho 12%positive))) in *.
  assert (RL : 0 <= L < 2 ^ 64) by (clear -SMB HN; lia).
  unfold F_low in HL. cbn [holds eval] in HL. rewrite Enx, E142, add_val in HL. fold ua L in HL.
  rewrite (u64_lit L RL) in HL. rewrite Z.mod_small in HL by (clear -IMG HTOP SMB; lia). rewrite u64_lit in HL by (clear; lia). exact HL.
Qed.

Lemma geu_intro : ltac2:(tb__ "0|0|
S15S43S18S1S4bZ0R2A2S4dR2S4fZ2Z40A2A2A2S4bS2eQ40S25R4R2A2A2R3A2S16R5S1cS45S1bR4A1R3A3A2F_;F_;Fe;Fc;Fr;").
Proof.
  intros r c e Hc H. cbn [holds eval branch_taken]. apply Bool.negb_true_iff. unfold bv_ltu. apply Z.ltb_ge. rewrite u64_lit by exact Hc. exact H.
Qed.

Lemma F_g7L_hold : ltac2:(tb__ "0|1|
S2aS2aF_;S2aS30S15S2dQ40A1M0S15S3G0A1S3S3fA1S3eVJG;R9R8R7R6R5R4R3R2R1A9S16R5S38A2S3cS14S16R6A1S39A3F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FBX;").
Proof.
  intros BX A Kc rho a r tp tr md HJ HL. pose proof (low_end BX A Kc rho a r tp tr md HJ HL) as LE.
  pose proof (JGs_rigidS nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (E12 & Enx & _).
  pose proof (JGs_nums nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (HN & SMB & _ & AL & IMG & HTOP & ENS & EMS & R8M & R8B). cbn zeta in *.
  pose proof (urange a) as Ra. set (ua := bv_unsigned a) in *. set (nv := bv_unsigned (rw rho 12%positive)) in *. unfold IMG_HI in IMG.
  assert (LB : nv + 6151 <= secmapsize nv).
  { rewrite EMS, ENS. pose proof (round_up_ge' (round_up nv 8 + 4096) PG ltac:(unfold PG; lia)). unfold PG in *. lia. }
  unfold F_g7L. apply Forall_cons; [|apply Forall_nil]. apply geu_intro; [clear; lia|]. unfold RUE. cbn [eval].
  rewrite and_val, !add_val, Enx, E12, !u64_lit by lia. fold ua nv.
  rewrite (Z.mod_small (ua + 6144)) by (clear -Ra HTOP SMB; lia). rewrite (Z.mod_small (ua + 6144 + nv)) by (clear -Ra HTOP LB HN SMB; lia).
  rewrite (Z.mod_small (ua + 6144 + nv + 7)) by (clear -Ra HTOP LB HN SMB; lia).
  rewrite (land_m8E nW st tmax nx Hnx) by (clear -Ra HTOP LB HN SMB; lia). pose proof (Z.mod_pos_bound (ua + 6144 + nv + 7) 8 ltac:(lia)) as MB. clear -MB LE LB. lia.
Qed.

Lemma F_g8L_hold : ltac2:(tb__ "0|1|
S2aS2aF_;S2aS30S15S2dQ40A1M0S15S3G0A1S3S3fA1S3eVJG;R9R8R7R6R5R4R3R2R1A9S16R5S38A2S3cS14S16R6A1S3aA3F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FBX;").
Proof.
  intros BX A Kc rho a r tp tr md HJ HL. pose proof (low_end BX A Kc rho a r tp tr md HJ HL) as LE.
  destruct (site8_vals nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (_ & _ & _ & EE). cbn zeta in EE.
  pose proof (JGs_nums nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (HN & SMB & _ & _ & IMG & TOP & ENS & EMS & _). cbn zeta in *.
  set (nv := bv_unsigned (rw rho 12%positive)) in *. set (ua := bv_unsigned a) in *.
  assert (LB : nv + 6151 <= secmapsize nv).
  { rewrite EMS, ENS. pose proof (round_up_ge' (round_up nv 8 + 4096) PG ltac:(unfold PG; lia)). pose proof (round_up_ge' nv 8 ltac:(lia)). unfold PG in *. lia. }
  pose proof (Z.mod_pos_bound nv 8 ltac:(lia)) as MN.
  unfold F_g8L. apply Forall_cons; [|apply Forall_nil]. apply geu_intro; [clear; lia|]. rewrite EE. clear -LE LB MN. lia.
Qed.

Lemma F_g9L_hold : ltac2:(tb__ "0|1|
S2aS2aF_;S2aS30S15S2dQ40A1M0S15S3G0A1S3S3fA1S3eVJG;R9R8R7R6R5R4R3R2R1A9S16R5S38A2S3cS14S16R6A1S3bA3F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FBX;").
Proof.
  intros BX A Kc rho a r tp tr md HJ HL. pose proof (low_end BX A Kc rho a r tp tr md HJ HL) as LE.
  destruct (site9_vals nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (EU & _). cbn zeta in EU.
  pose proof (JGs_nums nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (HN & SMB & _ & _ & IMG & TOP & ENS & EMS & _). cbn zeta in *.
  set (nv := bv_unsigned (rw rho 12%positive)) in *. set (ua := bv_unsigned a) in *.
  assert (LB : nv + 6151 <= secmapsize nv).
  { rewrite EMS, ENS. pose proof (round_up_ge' (round_up nv 8 + 4096) PG ltac:(unfold PG; lia)). pose proof (round_up_ge' nv 8 ltac:(lia)). unfold PG in *. lia. }
  pose proof (Z.mod_pos_bound nv 8 ltac:(lia)) as MN.
  unfold F_g9L. apply Forall_cons; [|apply Forall_nil]. apply geu_intro; [clear; lia|]. rewrite EU. clear -LE LB MN. lia.
Qed.

Section HINT.
Variable BX : AA -> AA.
Variables (D D' : axst) (F : list sprop).
Hypothesis WD : ltac2:(tb__ "0|0|
S0S4S1eSeVD';A1A1S5A3").
Hypothesis DD : ltac2:(tb__ "0|4|
S0S9S8S3S8S18S18A2M0A1M1S3S14A1M2A2M3A1S5cSeVD;A1SeVD';A1A2SaG3ScG1G2S6G0A1VF;A4A2A3").
Hypothesis NXD : ltac2:(tb__ "0|0|
S0S44S19SeVD';A1A1S19SeVD;A1A1A3").
Hypothesis HD : ltac2:(tb__ "0|0|
S0SfS10VD;SeVD';A1A2VD';A3").
Hypothesis FLOW : ltac2:(tb__ "0|0|
S5aS14S38S1aSeVD;A1A1A3").
Hypothesis FH : ltac2:(tb__ "0|1|
S2aS30S15S2dQ40A1M0S15S3G0A1S3S3fA1S3eVJG;VBX;R8R7R6R5R4R3R2R1A9S16R5S38A2S3cS14S16R6A1VF;A3F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;").

Lemma hint_low : ltac2:(tb__ "0|1|
S2aS30S15S2dQ40A1M0S15S3G0A1S48S40Vsegs;VJG;VBX;R7R6R5R4A5VD;R3R2R1A6S40Vsegs;VJG;VBX;R8R7R6R5A5VD';R4R3R2A6F_;Fw;Ftp;FrhoX;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a rhoX tp w Hw.
  pose proof (proj1 (Forall_forall _ _) (SPA_facts_hold segsA _ rhoX D tp w Hw) _ FLOW) as HL.
  destruct w as [tr [ms md]]. rewrite <- HD.
  eapply SPA_restate; [exact WD | exact DD | exact NXD | constructor | | exact Hw].
  exact (FH A Kc rho a rhoX tp tr md (proj2 Hw) HL).
Qed.

Lemma hint_low_triple : ltac2:(tb__ "0|2|
S48OF_;S2aS30S15S2dQ40A1M0S49S15S3G0A1M1S47Vsegs;R8S40Vsegs;VJG;VBX;R7R6R5R4A5VD';R2R1A5R3A4FtY;FrY;S15G1S47Vsegs;R9S40Vsegs;VJG;VBX;R8R7R6R5A5VD;R2R1A5R4A4FtX;FrX;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho a Q HC rX tX.
  eapply triple_conseq; [intros w Hw; exact (hint_low A Kc rho a rX tX w Hw) | intros w Hw; exact Hw | exact (HC rX tX)].
Qed.
End HINT.

Section G43L.
Variable BX : AA -> AA.
Hypothesis BXg : ltac2:(tb__ "0|0|
S2aS0S2cS2bVBX;R1A1A1S2bR1A1A3FX;").
Variable PX : list sobj.
Variable FXP : list sprop.
Hypothesis PX_noband : ltac2:(tb__ "0|2|
S2aS30S15S2dQ40A1M0S15S3G0A1S3S3fA1S3eVJG;VBX;R8R7R6R5R4R3R2R1A9S3cS14S16R5A1VFXP;A3S3S17A1S0S3S8S8S18S18A2S18A2M1A1S3dS17G1S4aR1A4S3dS17G1S4aVPX;A4A3S3cS17S17S73S27R9R1A2A1Lo;R2A3F_;Fl;F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;").
Variables (C5 C5A Y6A E6 CT6 CO6 T6 : axst) (sA s6 : wsub) (R6 : list sobj).
Let D6 : axst := ltac2:(tb__ "0|0|
S63VT6;S1aSeVCO6;A1A1A2").
Hypothesis FLOW : ltac2:(tb__ "0|0|
S5aS14S38S1aSeVC5;A1A1A3").
Hypothesis HC5A : ltac2:(tb__ "0|0|
S0SfS61S52Vnx;A1VC5;A2VC5A;A3").
Hypothesis FBA : ltac2:(tb__ "0|0|
S0S4S59S14S1dS19SeVC5;A1A1A1S52Vnx;A1A3S5A3").
Hypothesis Cert6A : ltac2:(tb__ "0|1|
S0S4S62S70Ufa0S7S43S67S6S43A1A3VGS;S7SfVC5A;S6SfA1M0A3S7SfVY6A;G0A3A6S5A3").
Hypothesis E6A : ltac2:(tb__ "0|0|
S0S4S11VY6A;VE6;VsA;A3S5A3").
Hypothesis I6A : ltac2:(tb__ "0|0|
S0S4S60VsA;VGS;A2S5A3").
Hypothesis WC6 : ltac2:(tb__ "0|0|
S0S4S1eSeVCT6;A1A1S5A3").
Hypothesis DF6 : ltac2:(tb__ "0|4|
S0S9S8S3S8S18S18A2M0A1M1S3S14A1M2A2M3A1S5cSeVE6;A1SeVCT6;A1A2SaG3ScG1G2S7G0ScS18S18S58Vnx;A1S53A4S6G0A1A3S6S14A1A4A2A3").
Hypothesis NX6 : ltac2:(tb__ "0|0|
S0S44S19SeVCT6;A1A1S19SeVE6;A1A1A3").
Hypothesis HC6 : ltac2:(tb__ "0|0|
S0SfS10VE6;SeVCT6;A1A2VCT6;A3").
Hypothesis SK6 : ltac2:(tb__ "0|1|
S0S3S8S8S18S18A2S18A2M0A1S3dS17G0S4aS29SeVCT6;A1A1A4S3dS17G0S4aSbS17S7S17S6bVnx;A1S7S17S6aVnx;A1S6S17A1A3A3SbS17S72VnW;Vnx;A2VPX;A3A3A4A3").
Hypothesis FC6 : ltac2:(tb__ "0|0|
S5bS14SbS14S36VW;Vst;A2S35S34A1A3S1aSeVCT6;A1A1A3").
Hypothesis FX6 : ltac2:(tb__ "0|0|
S5bS14VFXP;S1aSeVCT6;A1A1A3").
Hypothesis XC6 : ax_X CT6 = [].
Hypothesis HCO6 : ltac2:(tb__ "0|0|
S0SfS6dVCT6;S26S54Vnx;A1S1bZ0A1S53S6S24A1S21A5A2VCO6;A3").
Hypothesis WCO6 : ltac2:(tb__ "0|0|
S0S4S1eSeVCO6;A1A1S5A3").
Hypothesis He6 : ltac2:(tb__ "0|1|
S0S9S3S17A1M0A1S65VCO6;S50Vs6;A3SaG0VR6;A2A3").
Hypothesis Hchk6 : ltac2:(tb__ "0|0|
S0S4S64VCO6;S50Vs6;VR6;S3dS13SfS12S51A4A5S5A3").
Hypothesis HT6 : ltac2:(tb__ "0|0|
S0SfS66Vs6;S50S6cVCO6;VR6;A5VT6;A3").
Hypothesis FBC6 : ltac2:(tb__ "0|1|
S0S4S59S14S1dS19SeVCO6;A1M0A1A1S1aG0A1A3S5A3").
Hypothesis FBT6 : ltac2:(tb__ "0|0|
S0S4S59S14S1dS19SeVT6;A1A1A1S1aSeVCO6;A1A1A3S5A3").
Hypothesis NXC6 : ltac2:(tb__ "0|0|
S0S4S5fVGS;S19SeVCO6;A1A1A2S5A3").

Theorem sec_g43_low : ltac2:(tb__ "0|5|
S48OF_;S2aS30S15S2dQ40M0A1M1S49S0S37Vst;S33A3S0S3S31A1VW;S6S31A1A3F_;S5eVW;Vst;A2S32R6A1S42Vsegs;R9S41R7A1A3S43S1S4bS6fS2eG0R7A2A1M2R1A2S4dR1S4cG2S4eS5dS2eG0S20R8PcA2A2A1Z8A2A2A2A2S2S0S9S2dQ8A1M3A1S28R9S2fG0R2A2A2SdG3A1A3A1F_;Fz;S15S3G1A1M4S47Vsegs;RdS40Vsegs;VJG;VBX;RcRbRaR9A5VD6;R2R1A5R8A4FtpY;FrhoY;S15G4S47Vsegs;ReS40Vsegs;VJG;VBX;RdRcRbRaA5VC5;R2R1A5R9A4FtX;FrX;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho a Q HW HUS HKc Hokl RUNDEF HCONT rX tX.
  pose proof (JG_okf nW st nx BX ok A Kc rho a Hokl) as Hokf. pose proof (JG_stable nW st tmax nx Hnx NXG BX A Kc rho a HUS HKc) as HST.
  assert (SL : slink (bv_unsigned a) (secmapsize (bv_unsigned (rw rho 12%positive))) rho rho).
  { split; [intros i; reflexivity|]. split; [intros l; reflexivity|]. split; [intros x; left; reflexivity | exact RUNDEF]. }
  assert (TAIL : forall rE tE, triple segs ok (SPA segs (JG BX A Kc rho a) E6 rE tE) Q).
  { intros rE tE.
    apply (ms_step nW st tmax nx Hnx NXG BX BXg E6 CT6 CO6 T6 (B3 nx) L3 [O_2 nx; O_1 nx] PX Pre_memsetA Pret_ms Posts_memsetA s6 R6 eq_refl
             (fun ok0 Jx r0 t0 Ho Hs => memset_sumA ok0 Jx r0 t0 Ho Hs) eq_refl
             (RS6 nW st tmax nx Hnx BX E6 CT6 WC6 DF6 NX6 HC6) (HBL6 nW st tmax nx Hnx BX PX FXP PX_noband E6 CT6 NX6 FX6)
             SK6 FC6 XC6 HCO6 WCO6 He6 Hchk6 HT6 FBC6 FBT6 NXC6
             ok A Kc rho rho a tE Q HW HUS HKc Hokl SL).
    intros rhoY tpY. exact (HCONT rhoY tpY). }
  apply (triple_conseq (P:=SPA segs (JG BX A Kc rho a) C5A rX tX) (SPA segs (JG BX A Kc rho a) C5 rX tX) (Q:=Q)); [intros w Hw | intros w Hw; exact Hw |].
  { pose proof (proj1 (Forall_forall _ _) (SPA_facts_hold segsA _ rX C5 tX w Hw) _ FLOW) as HL.
    destruct w as [tr [ms md]]. rewrite <- HC5A.
    split; [|exact (proj2 Hw)]. exact (smatchA_add_facts segs rX tX (F_A nx) _ _ (proj1 Hw) (low_FA BX A Kc rho a rX tX tr md BXg (proj2 Hw) HL) FBA). }
  apply (cfg_soundA segs 4000%nat [MSENT] GS [C5A] [Y6A] (JG BX A Kc rho a) ok Q tX Hokf HST Cert6A); [|left; reflexivity].
  intros E rE HinE. destruct HinE as [<-|[]].
  eapply triple_conseq; [intros w Hw; exact (join4 nW st tmax nx Hnx NXG BX A Kc rho a Y6A E6 sA rE tX w HUS HKc E6A I6A Hw) | intros w Hw; right; exact Hw |].
  apply TAIL.
Qed.
End G43L.
End SEC6L.
End SpineMallocSec6L.

(* [comment removed for export] *)
Module SpineMallocSec7.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "False"; "or"; "@Corelib.Init.Datatypes"; "nat"; "list"; "cons"; "bool"; "nil"; "app"; "true"; "length"; "pair"; "prod"; "andb"; "Some"; "option"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "rw"; "valuation"; "cell"; "sprop"; "sv"; "SVar"; "rl"; "rm"; "ss_facts"; "eval"; "holds"; "ss_objs"; "SLit"; "SPBranch"; "SPNot"; "odefault"; "ss_next"; "swf"; "DUnknown"; "DZero"; "SAlu"; "mkSS"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_pc"; "ss_regs"; "ss_resv"; "sstate"; "@Stdlib.Lists.List"; "In"; "forallb"; "existsb"; "incl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_sec"; "sec_chunk"; "aa_Km"; "aa_geom"; "aa_ptr_committed"; "aa_depot"; "ageom"; "aa_Kf"; "aa_V"; "aa_cache_inited"; "aa_cls"; "aa_fs_busy"; "aa_fs_hint"; "aa_internal_inited"; "aa_live"; "aa_q_global"; "aa_q_thread"; "class_state"; "qbatch"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "@Stdlib.ZArith.BinInt.Z"; "le"; "of_nat"; "add"; "div"; "mul"; "eqb"; "leb"; "ltb"; "modulo"; "@Corelib.Init.Nat"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "entailsA"; "mkAX"; "xr_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "ulink"; "KcA"; "AE_A"; "Kc_ok"; "UStopLeOrPc"; "mem_keptA"; "ustop"; "L_malloc_ok"; "A_globals"; "JL_malloc_ok"; "Posts_malloc"; "unwind_objs"; "V_RES"; "base_sv"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.SecOKInv"; "bumpV"; "@Corelib.Lists.ListDef"; "seq"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "setregs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.CertMallocSV"; "O_UBs"; "UBs"; "F_par"; "RSF"; "ic_c1"; "ic_c2"; "ic_nch"; "ic_nres"; "ic_pg"; "ic_rs"; "mc_cptr"; "mc_idx"; "mc_magic"; "mc_map"; "mc_ms"; "mc_ns"; "mc_size"; "mc_sizehi"; "mc_state"; "mc_type"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger"; "sepZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "dblocks"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "secmapsize"; "stopJ_stable"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c4.SpineMallocSec7.SEC7.FIN"; "idxsU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c4.SpineMallocSec7"; "idxsF"; "S2F"; "KUB"; "XF_of"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_EQ"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "nodupN"; "select"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.CertMallocSS"; "V_NCH"; "V_NRES"; "nxS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS9"; "sw9";
"@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "ltb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "kPtrArrayCommit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM"; "IMG_M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec2"; "IMG_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3"; "GS"; "JGs"; "@Stdlib.PArith.BinPos.Pos"; "leb"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocS4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocS9 RebuildM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require MmapSymA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ae.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocSec SpineMallocSec2 SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bt.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require EnsureMapA DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SecLog2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require q0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bw.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require br.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SpineMallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.RebuildN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.MmapSymA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.CertMallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.CertMallocSN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.SegD_cost OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.LedgerLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.InvD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.DepotK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.SecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SecReveal OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvReveal OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.EnsureMapA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SecLog2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.InvEnsure OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.CertMallocSU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineMallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bw.SpineMallocSec5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.DepotKP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bp.DepotCallS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.CertMallocSV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.br.RebuildS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c0.SpineMallocSec6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition idxsF (nW : nat) (partial : bool) : list nat := ltac2:(tb__ "0|3|
S9S4S6S4U5S9S4S6dU6M0VnW;A2S6S4S55G0VnW;A2S6S4S55U7VnW;A2S8S4A1M1A3A3A3A3S9S4S6dS55U8M2VnW;A2U1eA2S9S4S6S4U0S6S4U1S6S4U2S6S4U3S6S4U4G1A3A3A3A3A3S9S4S6dS55U26VnW;A2G2A2S9S4S6S4S55U2eVnW;A2S6S4S55U2fVnW;A2S6S4S55U30VnW;A2G1A3A3A3S7S5S4A1Lpartial;Vpartial;S6S4S55U31VnW;A2G1A3G1X7x2A3A3A3A3A3").
Definition KEPTF (W : list ulink) (swc : list cell) : list sobj := ltac2:(tb__ "0|0|
S6S13Sa0Vswc;A1S9S13S66VW;A1S63A3A3").

Definition KUB (W : list ulink) (swc : list cell) (nx : positive) : list sobj := ltac2:(tb__ "0|0|
S9S13S6S13Sa0Vswc;A1S66VW;A1A3S9S13S6S13S71Vnx;A1S8S13A1A3S63A3A3").
Definition S2F (F : axst) (K : list sobj) : sstate := ltac2:(tb__ "0|1|
S56VF;A1S30S29S2dR1A1S70S2eR1A1S6SdS4S18A2M0ScS4S18U4S19P18A1A4S8G0A1A3A2S2bR1A1S2aR1A1S2fR1A1VK;S1cR1A1S24R1A1S2cR1A1A9TS;").
Definition XF_of (F : axst) (K : list sobj) (nx : positive) : axst := ltac2:(tb__ "0|1|
S59S93VF;VK;A2S6SdS18S18A2M0ScS18S18S72Vnx;A1S19PcA1A4S8G0A1A3S68A3").

Definition bx_ok (BX : AA -> AA) : Prop := ltac2:(tb__ "0|3|
S35S1S0S3cS39VBX;R1A1M0A1S39R1A1A3S1S0S5S47A1S40G0A1S40R1A1A3S1S0S7S3fG0A1S3fR1A1A3S1S0S5S37A1S36G0A1S36R1A1A3S1S0S5SdS11S11A2A1M1S44G0A1S44R1A1A3S1S0S5S48A1M2S46G0A1S46R1A1A3S1S0G2S45G0A1S45R1A1A3S1S0S5S11A1S42G0A1S42R1A1A3S1S0S5G1A1S41G0A1S41R1A1A3S1S0S7S43G0A1S43R1A1A3S1S0S11S3eG0A1S3eR1A1A3S1S0S11S38G0A1S4eS38R1A1Z1A2A3S0S11S3dG0A1S3dR1A1A3A2A2A2A2A2A2A2A2A2A2A2A2FX;").

Section SEC7.
Variable nW : nat. Variable st : ustop. Variable tmax : Z.
Let W : list ulink := Wcan nW.
Let segs : list Segment := segsA.
Variable nx : positive.
Hypothesis Hnx : ltac2:(tb__ "0|0|
S0S12S9fVW;Vst;Vtmax;A3Vnx;A3").
Hypothesis NXG : ltac2:(tb__ "0|0|
S0S7SafSa7Vnx;A2SaA3").
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTM : ltac2:(tb__ "0|0|
S11S8dVCST;R1A2S8dSabR2A2S2F_;F_;Fa;").
Hypothesis HCSTS : ltac2:(tb__ "0|0|
S11S8dVCST;R1A2S8dSacR2A2S2F_;F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let JG (BX : AA -> AA) : AA -> KcA -> valuation -> word -> jpredA := ltac2:(tb__ "0|0|
SaeVnW;Vst;Vnx;VBX;A4").

Section FIN.
Variable BX : AA -> AA.
Hypothesis BXok : bx_ok BX.
Variables (blk : Z) (dpx : odefault) (NRESe : sv) (FXP : list sprop).
Hypothesis Hdpx : ltac2:(tb__ "0|0|
S3S0S23Vdpx;S26A3S0S23Vdpx;S27A3A2").

Hypothesis HPATH : ltac2:(tb__ "0|4|
S35S5cS15S4aQ40M0A1M1S15S5G1A1S5S97A1S96VJG;VBX;R8R7R6R5R4R3R2R1A9S6eS17S1eR5A1VFXP;A3VBX;S6cRaS49G0S14R8PcA2A2A2A1S35S1S1S4cZ8M2Vblk;A2S4cVblk;Z20000A2A2S1S4cS4eS50G2S4dSbS37S36RbA1A2A1A2Vblk;A2S3aR1A1M3A2S0G1S1dR7VNRESe;A2S4bG0S4fG3G2A2A2A3A2A2TAs;F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;").
Variable partial : bool.
Variable F : axst.
Variables swc c1 c2 c4 c5 mc xc : list cell.
Variable tyb : Z.
Let K : list sobj := KEPTF W swc.
Let RS : list sobj := ltac2:(tb__ "0|0|
S74Vnx;Vc1;Vc2;Vc4;Vc5;Vmc;Vxc;Vblk;Vdpx;Vpartial;Aa").
Let R : list sobj := RT_m1 ++ RS.
Hypothesis SELF : ltac2:(tb__ "0|0|
S0S5S13A1S9bS1fS56VF;A1A1S92VnW;Vpartial;A2A2S9S13VK;VR;A3A3").
Hypothesis NDF : ltac2:(tb__ "0|0|
S0S7S9aS92VnW;Vpartial;A2A1SaA3").
Hypothesis BNDF : ltac2:(tb__ "0|0|
S0S7S32S4S4Sa2R1SbS13S1fS56VF;A1A1A2A2Li;S92VnW;Vpartial;A2A3SaA3").
Hypothesis COVF : ltac2:(tb__ "0|0|
S0S7S32S4S4S33S4Sa1R1A1S92VnW;Vpartial;A2A3Li;S6dU0SbS13S1fS56VF;A1A1A2A2A3SaA3").
Hypothesis XFn : ax_X F = [].
Hypothesis BFb : ax_base F = base_sv.
Hypothesis FPF : ltac2:(tb__ "0|0|
S34S17S9S17S6bVW;Vst;A2S6aS69A1A3S1cS56VF;A1A1A3").
Hypothesis FXF : ltac2:(tb__ "0|0|
S34S17VFXP;S1cS56VF;A1A1A3").
Hypothesis FPAR : ltac2:(tb__ "0|0|
S31S17S7S17Lpartial;Vpartial;S22S73A1S73X7x2S1cS56VF;A1A1A3").

Hypothesis Hc1 : ltac2:(tb__ "0|0|
S1S31S16S79Vc1;A3S1S31S16S75Vc1;A3S1S31S16S76Vc1;A3S1S31S16S7aVc1;A3S1S31S16S78VNRESe;A1Vc1;A3S31S16S77Vc1;A3A2A2A2A2A2").
Hypothesis Hmc : ltac2:(tb__ "0|0|
S1S31S16S7eVnx;A1Vmc;A3S1S31S16S7fVmc;A3S1S31S16S80Vmc;A3S1S31S16S7cVmc;A3S1S31S16S7dVmc;A3S1S31S16S7bVnx;A1Vmc;A3S1S31S16S83Vmc;A3S1S31S16S84Vtyb;A1Vmc;A3S1S31S16S82Vmc;A3S31S16S81Vmc;A3A2A2A2A2A2A2A2A2A2").
Hypothesis Htyb : ltac2:(tb__ "0|0|
S0S7SeSeS52Z0Vtyb;A2S53Vtyb;Z100A2A2S51S54Vtyb;Z4A2Z1A2A2SaA3").
Hypothesis Hxc : In (xc_map nx) xc.

Let KU : list sobj := ltac2:(tb__ "0|0|
S94VW;Vswc;Vnx;A3").
Definition idxsU (n : nat) : list nat := ltac2:(tb__ "0|2|
S9S4S6S4U0S6dU1M0Vn;A2A3S9S4S6S4S55Vn;U3A2S8S4A1M1A3S6S4S55Vn;G0A2S6S4S55Vn;U2A2G1A3A3A3A3").
Hypothesis WCU : ltac2:(tb__ "0|0|
S0S7S25S9cS56VF;A1S9S13VK;S6S13S71Vnx;A1S8S13A1A3A3A2A1SaA3").
Hypothesis SELU : ltac2:(tb__ "0|0|
S0S5S13A1S9bS9S13VK;S6S13S71Vnx;A1S8S13A1A3A3S91VnW;A1A2VKU;A3").
Hypothesis NDU : ltac2:(tb__ "0|0|
S0S7S9aS91VnW;A1A1SaA3").
Hypothesis BNDU : ltac2:(tb__ "0|0|
S0S7S32S4S4Sa2R1SbS13S9S13VK;S6S13S71Vnx;A1S8S13A1A3A3A2A2Li;S91VnW;A1A3SaA3").
Hypothesis COVU : ltac2:(tb__ "0|0|
S0S7S32S4S4S33S4Sa1R1A1S91VnW;A1A3Li;S6dU0SbS13S9S13VK;S6S13S71Vnx;A1S8S13A1A3A3A2A2A3SaA3").
Hypothesis W9 : ltac2:(tb__ "0|0|
S0S7S25S93VF;VKU;A2A1SaA3").
Hypothesis D9 : ltac2:(tb__ "0|4|
S0S10SdS5SdS18S18A2M0A1M1S5S17A1M2A2M3A1Sa3S9cS56VF;A1VKU;A2S93VF;VKU;A2A2SfG3ScG1G2S6G0ScS18S18S20Sa8A1S19P18A1A4S8G0A1A3S8S17A1A4A2A3").
Hypothesis XB9 : ltac2:(tb__ "0|0|
S0S7S5aS24S56VF;A1A1ScS18S18S72Vnx;A1S19PcA1A4A2SaA3").
Variable s9 : wsub.
Hypothesis ENT9 : ltac2:(tb__ "0|0|
S0S7S58S95VF;VKU;Vnx;A3S62S5dVW;Vst;A3Vs9;A3SaA3").
Hypothesis SID9 : ltac2:(tb__ "0|0|
S0S7Sa5Vs9;S6fA2SaA3").
Hypothesis G110 : ltac2:(tb__ "0|0|
S0S18Sa4Vs9;S67A2S72Vnx;A1A3").

Theorem sec_finish_P : ltac2:(tb__ "0|6|
S35S5cS15S15S4aQ40M0A1M1S15S5G1A1M2G2S85S5SdS57S8bA2M3A1S31G3ScS57S8bS62S5dVW;Vst;A3S64VAInv;VCST;VXGL;RaR9A5A4R1A3S0S61Vst;S5fA3S0S5S5bA1VW;S8S5bA1A3F_;S5eRbA1S12S0G1S14RbR1A2S14RcR1A2A3Fi;S12S0S5S4aQ8A1A1S1aRcR1A2S1aRdR1A2A3Fl;S60VCST;VXGL;RfRfS1bRdA1S1bRcA1A6S4cS4dSbS37S36R10A1A2A1S38R10A1A2SdS11S11A2M4S31G4R1S8eS3bVBX;S6cR12S49G0S14RfPcM5A2A2A2A1A1A1A3S8cR2ScS11S11S49G0RfA2S8fS49G0S14R10G5A2A2A1A4A2F_;Fbn;S87Vsegs;VJG;VBX;R12R11RfReA5VF;RdRbRaA6S8aVsegs;S6fR11RdRaRbA6F_;F_;F_;F_;F_;F_;F_;F_;F_;FPosts;Fw;Ftp;Ftp0;FrhoE;Fa;Frho;Frho0;FKc;FA;").
Proof.
  intros A Kc rho0 rho a rhoE tp0 tp w Posts HPin HW HKc HLw HLl HKEPT0 HL9 HDB H.
  destruct w as [tr [ms md]].
  pose proof H as [HsmA HJ]. cbn [w_tr w_cfg cfg_model fst snd] in HJ.
  pose proof (SPA_facts_hold segs _ rhoE F tp _ H) as HFacts.
  pose proof (JGs_rigidS nW st tmax nx Hnx BX A Kc rho a rhoE tp tr md HJ) as (E12 & Enx & E141 & E142 & E151 & E152 & E155 & E145 & E146 & E147 & Erm & Erl).
  pose proof (JGs_nums nW st tmax nx Hnx BX A Kc rho a rhoE tp tr md HJ) as (HN & SMB & SMM & AL & IMG & TOP & ENS & EMS & R8M & R8B).
  assert (HFX : Forall (holds rhoE) FXP) by (apply Forall_forall; intros p Hp; exact (proj1 (Forall_forall _ _) HFacts p (FXF p Hp))).
  pose proof (HPATH A Kc rho a rhoE tp tr md HJ HFX) as (Hblk & HROOM & ENRES).
  pose proof (msx_val nW st tmax nx Hnx BX A Kc rho a rhoE tp tr md HJ) as EMSX.
  cbn zeta in *.
  set (nv := bv_unsigned (rw rho 12%positive)) in *. set (ua := bv_unsigned a) in *. set (L := secmapsize nv) in *.
  set (As := BX (bumpV A nv)) in *.
  destruct (BXok (bumpV A nv)) as (Bg & Bc & Bci & Bs & Bl & Bqt & Bqg & Bfh & Bfb & Bii & BV & BKm & BKf). fold As in Bg, Bc, Bci, Bs, Bl, Bqt, Bqg, Bfh, Bfb, Bii, BV, BKm, BKf.
  cbn [aa_geom aa_cls aa_cache_inited aa_sec aa_live aa_q_thread aa_q_global aa_fs_hint aa_fs_busy aa_internal_inited aa_V aa_Km aa_Kf bumpV] in Bg, Bc, Bci, Bs, Bl, Bqt, Bqg, Bfh, Bfb, Bii, BV, BKm, BKf.
  pose proof HJ as ((Hagw & Hagl & Hagm) & Ha & HA & HP & HK & Htp & HU & _ & Htop & HBud). fold nv As in HA. fold nv ua L in HP.
  set (G := aa_geom A) in *. set (T := ag_thread G). set (idx := Z.of_nat (length (aa_sec A))) in *. set (ub := ua + 6144). set (pw := ag_pab G + 8 * idx).
  assert (E153 : rw rhoE 153%positive = Z_to_bv 64 (ag_stack_top G)). { rewrite <- (Hagw 153%positive) by (unfold GW; lia). reflexivity. }
  assert (E154 : rw rhoE 154%positive = Z_to_bv 64 (ag_stack_bottom G)). { rewrite <- (Hagw 154%positive) by (unfold GW; lia). reflexivity. }
  assert (E156 : rw rhoE 156%positive = Z_to_bv 64 (ag_spacebeg G + kSpaceSize)). { rewrite <- (Hagw 156%positive) by (unfold GW; lia). reflexivity. }
  assert (ErmF : rm rhoE = rm rho). { apply functional_extensionality. intros x. exact (Erm x). }
  pose proof HA as (HG & HR & HFs & HRest & HM & HI3 & HBt). rewrite Bg in HG. fold G in HG.
  pose proof (geom_numsS _ HG) as (G1 & G2 & G3 & G4 & G5 & G6 & _). fold T in G4, G5. pose proof (topG_range G) as ACV.
  pose proof (urange a) as Ra. fold ua in Ra. unfold IMG_HI in IMG. unfold PG in AL, SMM.

  set (KJ := (fun (_ : valuation) (_ : list word) (t : list event) (m : Model) => Kc t m) : jpredA).
  assert (HaK : SPA segs KJ F rhoE tp (tr, {| cfg_ms := ms; cfg_model := md |})) by (split; [exact HsmA | exact HK]).
  pose proof (SPA_select segs KJ rhoE F (idxsF nW partial) tp _ HaK NDF
                ltac:(intros i Hi; apply Nat.ltb_lt; exact (proj1 (forallb_forall _ _) BNDF i Hi))
                ltac:(intros i Hi; pose proof (proj1 (forallb_forall _ _) COVF i ltac:(apply in_seq; lia)) as X;
                      apply existsb_exists in X as (i' & Hi' & E); apply Nat.eqb_eq in E; subst i'; exact Hi')) as Hsel.
  rewrite SELF in Hsel. clear HaK.

  pose proof (SPA_unobj segs KJ rhoE (ax_setS F (set_objs (ax_S F) (K ++ R))) K R tp tr ms md eq_refl Hsel (fun k => k)) as Hb.
  cbn zeta in Hb. set (rho3 := rho_absorb rhoE R (vms md tp ms)) in *.
  pose proof (proj1 (proj1 Hsel)) as Hsm1. unfold virt in Hsm1. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S ax_setS] in Hsm1.
  set (v3 := view segs (rm rho3)). set (vE := view segs (rm rhoE)).
  assert (AO : forall o, In o R -> _) by (intros o Ho; exact (absorb_obj rhoE _ tr (vms md tp ms) (vmd md) K R o Hsm1 eq_refl Ho)).
  assert (INRS : forall o, In o RS -> In o R) by (intros o Ho; unfold R; apply in_or_app; right; exact Ho).

  assert (AOC : forall o c bZ offZ V, In o RS -> In c (ob_cells o) ->
            bv_unsigned (eval rhoE (ob_base o)) = bZ -> soff rhoE (c_off c) = offZ -> eval rhoE (SymState.c_val c) = Z_to_bv 64 V ->
            0 <= bZ + offZ -> bZ + offZ + c_width c <= 2 ^ 64 ->
            cell_ok v3 (mkACell (bZ + offZ) (Z.to_nat (c_width c)) V)).
  { intros o c bZ offZ V Ho Hc Eb Eo Ev B1 B2. destruct (AO o (INRS o Ho)) as (_ & CO & _). destruct (CO c Hc) as (_ & _ & CJ).
    rewrite Eb, Eo, Ev in CJ. intros k Hk. cbn [c_addr c_w RtCells.c_val] in *. unfold v3. rewrite view_in by (clear -B1 B2 Hk; lia). exact (CJ k Hk). }
  assert (AOP : forall o z, In o RS -> (ob_dflt o = DUnknown \/ ob_dflt o = DZero) -> fst (obj_range rhoE o) <= z < snd (obj_range rhoE o) -> exists bb, v3 z = Some bb).
  { intros o z Ho DD Hz. destruct (AO o (INRS o Ho)) as (Bo & _ & Po & _). unfold obj_range in Hz. cbn [fst snd] in Hz.
    unfold v3. rewrite view_in by (clear -Bo Hz; unfold obj_lo_of, obj_hi_of in *; lia).
    replace z with (bv_unsigned (eval rhoE (ob_base o)) + (z - bv_unsigned (eval rhoE (ob_base o)))) by (clear; lia).
    apply Po; [exact DD | clear -Hz; unfold obj_lo_of, obj_hi_of in *; lia]. }

  assert (EVnx : bv_unsigned (eval rhoE (SVar nx)) = ua) by (cbn [eval]; rewrite Enx; reflexivity).
  assert (UAB : 6578176 <= ua /\ ua + L <= 140737479966720 /\ 73728 <= L) by (clear -IMG TOP SMB; lia).
  assert (LB : nv + 8192 <= L).
  { rewrite EMS, ENS. pose proof (round_up_ge' (round_up nv 8 + 4096) PG ltac:(unfold PG; lia)). pose proof (round_up_ge' nv 8 ltac:(lia)). unfold PG in *. lia. }
  assert (WZ : forall w : word, w = Z_to_bv 64 (bv_unsigned w)) by (intros w0; symmetry; apply Z_to_bv_bv_unsigned).

  assert (IN_Mlo : In (O_Mlo nx mc) RS) by (unfold RS, RSF; cbn [app In]; repeat (first [left; reflexivity | right])).
  assert (IN_seci : In (O_seciF c1) RS) by (unfold RS, RSF; cbn [app In]; repeat (first [left; reflexivity | right])).
  assert (IN_secm : In O_secmF RS) by (unfold RS, RSF; cbn [app In]; repeat (first [left; reflexivity | right])).
  assert (IN_px : In (O_pxF blk dpx xc) RS) by (unfold RS, RSF; cbn [app In]; repeat (first [left; reflexivity | right])).
  assert (IN_4z : In (O_4z nx) RS) by (unfold RS, RSF; cbn [app In]; repeat (first [left; reflexivity | right])).
  destruct Hmc as (M0 & M8 & M16 & M24 & M4096 & M4104 & M6128 & M6129 & M6130 & M6132).
  destruct Hc1 as (I0 & I8 & I16 & I24 & I48 & I56).
  assert (SOL : forall z, 0 <= z < 2 ^ 62 -> soff rhoE (SLit z) = z) by (intros z Hz; apply soff_lit_small; lia).

  assert (C0 : cell_ok v3 (mkACell ua 8 ua)).
  { replace ua with (ua + 0) at 1 by (clear; lia). apply (AOC (O_Mlo nx mc) (mc_map nx) ua 0 ua IN_Mlo M0 EVnx (SOL 0 ltac:(clear; lia))); [cbn [SymState.c_val mc_map eval]; rewrite Enx; apply WZ | clear -UAB; lia | cbn [c_width mc_map]; clear -UAB; lia]. }
  assert (C8 : cell_ok v3 (mkACell (ua + 8) 8 L)).
  { apply (AOC (O_Mlo nx mc) mc_ms ua 8 L IN_Mlo M8 EVnx (SOL 8 ltac:(clear; lia))); [cbn [SymState.c_val mc_ms]; rewrite (WZ (eval rhoE msx)), EMSX; reflexivity | clear -UAB; lia | cbn [c_width mc_ms]; clear -UAB; lia]. }
  assert (C16 : cell_ok v3 (mkACell (ua + 16) 8 (secneeded nv))).
  { apply (AOC (O_Mlo nx mc) mc_ns ua 16 (secneeded nv) IN_Mlo M16 EVnx (SOL 16 ltac:(clear; lia))); [cbn [SymState.c_val mc_ns eval]; exact E141 | clear -UAB; lia | cbn [c_width mc_ns]; clear -UAB; lia]. }
  assert (C24 : cell_ok v3 (mkACell (ua + 24) 8 idx)).
  { apply (AOC (O_Mlo nx mc) mc_idx ua 24 idx IN_Mlo M24 EVnx (SOL 24 ltac:(clear; lia))); [cbn [SymState.c_val mc_idx eval]; exact E147 | clear -UAB; lia | cbn [c_width mc_idx]; clear -UAB; lia]. }
  assert (VMG0 : cell_ok v3 (mkACell (ua + 4096) 8 kAllocBegMagic)).
  { apply (AOC (O_Mlo nx mc) mc_magic ua 4096 kAllocBegMagic IN_Mlo M4096 EVnx (SOL 4096 ltac:(clear; lia))); [reflexivity | clear -UAB; lia | cbn [c_width mc_magic]; clear -UAB; lia]. }
  assert (VMG8 : cell_ok v3 (mkACell (ua + 4104) 8 (ub - 16))).
  { apply (AOC (O_Mlo nx mc) (mc_cptr nx) ua 4104 (ub - 16) IN_Mlo M4104 EVnx (SOL 4104 ltac:(clear; lia))); [| clear -UAB; lia | cbn [c_width mc_cptr]; clear -UAB; lia].
    cbn [SymState.c_val mc_cptr]. apply bv_eq. cbn [eval]. rewrite Enx, add_val, !u64_lit by (unfold ub; clear -UAB; lia). fold ua. rewrite Z.mod_small by (clear -UAB; lia). unfold ub. clear. lia. }

  assert (EN12 : eval rhoE (SVar 12) = Z_to_bv 64 nv) by (cbn [eval]; rewrite E12; apply WZ).
  assert (B1E : forall z, 0 <= z < 256 -> nth 0 (enc_bytes 1 (Z_to_bv 64 z)) (Z_to_bv 8 0) = Z_to_bv 8 z).
  { intros z Hz. rewrite (ReprGlue.nth_enc_bytes 1 0 z ltac:(clear; lia) ltac:(clear; lia)). apply f_equal. unfold MallocInv.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
    rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite !Z.mod_small by (clear -Hz; lia). reflexivity. }
  assert (VH2 : v3 (ub - 16) = Some (Z_to_bv 8 2)).
  { pose proof (AOC (O_Mlo nx mc) mc_state ua 6128 2 IN_Mlo M6128 EVnx (SOL 6128 ltac:(clear; lia)) eq_refl ltac:(clear -UAB; lia) ltac:(cbn [c_width mc_state]; clear -UAB; lia)) as X.
    specialize (X 0%nat ltac:(cbn; clear; lia)). cbn [c_addr c_w RtCells.c_val c_width mc_state Z.of_nat] in X. rewrite Z.add_0_r in X.
    replace (ub - 16) with (ua + 6128) by (unfold ub; clear; lia). rewrite X. apply f_equal. exact (B1E 2 ltac:(clear; lia)). }
  assert (VH1 : exists t, v3 (ub - 15) = Some t /\ bv_unsigned t mod 4 = 1).
  { apply andb_prop in Htyb as [Ht1 Ht2]. apply andb_prop in Ht1 as [Ht0 Ht1]. apply Z.leb_le in Ht0. apply Z.ltb_lt in Ht1. apply Z.eqb_eq in Ht2.
    pose proof (AOC (O_Mlo nx mc) (mc_type tyb) ua 6129 tyb IN_Mlo M6129 EVnx (SOL 6129 ltac:(clear; lia)) eq_refl ltac:(clear -UAB; lia) ltac:(cbn [c_width mc_type]; clear -UAB; lia)) as X.
    specialize (X 0%nat ltac:(cbn; clear; lia)). cbn [c_addr c_w RtCells.c_val c_width mc_type Z.of_nat] in X. rewrite Z.add_0_r in X.
    exists (Z_to_bv 8 tyb). split.
    - replace (ub - 15) with (ua + 6129) by (unfold ub; clear; lia). rewrite X. apply f_equal. exact (B1E tyb (conj Ht0 Ht1)).
    - rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. rewrite (Z.mod_small tyb 256) by (clear -Ht0 Ht1; lia). exact Ht2. }
  assert (VHN : cell_ok v3 (mkACell (ub - 12) 4 (nv mod 2 ^ 32))).
  { pose proof (AOC (O_Mlo nx mc) mc_size ua 6132 nv IN_Mlo M6132 EVnx (SOL 6132 ltac:(clear; lia)) EN12 ltac:(clear -UAB; lia) ltac:(cbn [c_width mc_size]; clear -UAB; lia)) as X.
    intros k Hk. specialize (X k Hk). cbn [c_addr c_w RtCells.c_val c_width mc_size] in X, Hk |- *. change (Z.to_nat 4) with 4%nat in X, Hk.
    replace (ub - 12 + Z.of_nat k) with (ua + 6132 + Z.of_nat k) by (unfold ub; clear; lia). rewrite X. apply f_equal.
    rewrite !(ReprGlue.nth_enc_bytes 4 k) by (first [exact Hk | clear; lia]). apply f_equal. unfold MallocInv.le_byte. change (8 * Z.of_nat 4) with 32. rewrite Z.mod_mod by (clear; lia). reflexivity. }
  assert (VH0 : cell_ok v3 (mkACell (ub - 14) 2 (nv / 2 ^ 32))).
  { assert (EV : eval rhoE (SAlu ALU_SRL (SVar 12) (SLit 32)) = Z_to_bv 64 (nv / 2 ^ 32)).
    { apply bv_eq. cbn [eval]. rewrite E12, srl_val. fold nv. change (32 mod 64) with 32. rewrite Z.shiftr_div_pow2 by (clear; lia).
      symmetry. apply u64_lit. pose proof (Z.div_pos nv (2 ^ 32) ltac:(clear -HN; lia) ltac:(clear; lia)). pose proof (Z.div_lt_upper_bound nv (2 ^ 32) (2 ^ 7) ltac:(clear; lia) ltac:(clear -HN; lia)). lia. }
    pose proof (AOC (O_Mlo nx mc) mc_sizehi ua 6130 (nv / 2 ^ 32) IN_Mlo M6130 EVnx (SOL 6130 ltac:(clear; lia)) EV ltac:(clear -UAB; lia) ltac:(cbn [c_width mc_sizehi]; clear -UAB; lia)) as X.
    replace (ub - 14) with (ua + 6130) by (unfold ub; clear; lia). exact X. }

  assert (EV0 : bv_unsigned (eval rhoE (SLit 0)) = 0) by reflexivity.
  assert (SECB : 0 <= SEC_INST /\ 0xee044 <= 2 ^ 62) by (unfold SEC_INST; clear; lia).
  assert (CI0 : cell_ok v3 (mkACell SEC_INST 8 PG)).
  { pose proof (AOC (O_seciF c1) ic_pg 0 SEC_INST PG IN_seci I0 EV0 (SOL SEC_INST ltac:(unfold SEC_INST; clear; lia)) eq_refl ltac:(unfold SEC_INST; clear; lia) ltac:(unfold SEC_INST; cbn; clear; lia)) as X. exact X. }
  assert (CI8 : cell_ok v3 (mkACell (SEC_INST + 8) 8 (ag_pab G))).
  { pose proof (AOC (O_seciF c1) ic_c1 0 (SEC_INST + 8) (ag_pab G) IN_seci I8 EV0 (SOL (SEC_INST + 8) ltac:(unfold SEC_INST; clear; lia)) ltac:(cbn [SymState.c_val ic_c1 eval]; exact E145) ltac:(unfold SEC_INST; clear; lia) ltac:(unfold SEC_INST; cbn; clear; lia)) as X. exact X. }
  assert (CI16 : cell_ok v3 (mkACell (SEC_INST + 16) 8 (ag_pab G))).
  { pose proof (AOC (O_seciF c1) ic_c2 0 (SEC_INST + 16) (ag_pab G) IN_seci I16 EV0 (SOL (SEC_INST + 16) ltac:(unfold SEC_INST; clear; lia)) ltac:(cbn [SymState.c_val ic_c2 eval]; exact E145) ltac:(unfold SEC_INST; clear; lia) ltac:(unfold SEC_INST; cbn; clear; lia)) as X. exact X. }
  assert (CI24 : cell_ok v3 (mkACell (SEC_INST + 24) 8 kPtrArrayReserve)).
  { pose proof (AOC (O_seciF c1) ic_rs 0 (SEC_INST + 24) kPtrArrayReserve IN_seci I24 EV0 (SOL (SEC_INST + 24) ltac:(unfold SEC_INST; clear; lia)) eq_refl ltac:(unfold SEC_INST; clear; lia) ltac:(unfold SEC_INST; cbn; clear; lia)) as X. exact X. }
  assert (C48 : cell_ok v3 (mkACell (SEC_INST + 48) 8 (aa_ptr_committed As / 8))).
  { pose proof (AOC (O_seciF c1) (ic_nres NRESe) 0 (SEC_INST + 48) (aa_ptr_committed As / 8) IN_seci I48 EV0 (SOL (SEC_INST + 48) ltac:(unfold SEC_INST; clear; lia)) ENRES ltac:(unfold SEC_INST; clear; lia) ltac:(unfold SEC_INST; cbn; clear; lia)) as X. exact X. }
  pose proof (Zle_0_nat (length (aa_sec A))) as IDX0. fold idx in IDX0.
  pose proof HRest as (_ & _ & _ & HSRs & _). pose proof (pab_facts _ As HSRs) as (P1 & P2 & P3 & P4 & P5). rewrite Bg in P1, P2, P3. rewrite Bs in P4. fold G in P1, P2, P3. fold idx in P4.
  unfold IMG_HI in P1. unfold kPtrArrayReserve in P2, P4.
  assert (C56 : cell_ok v3 (mkACell (SEC_INST + 56) 8 (idx + 1))).
  { assert (EV : eval rhoE (SAlu ALU_ADD (SVar V_NCH) (SLit 1)) = Z_to_bv 64 (idx + 1)).
    { apply bv_eq. cbn [eval]. rewrite E147, add_val, !u64_lit by (clear -IDX0 P4; lia). fold idx. apply Z.mod_small. clear -IDX0 P4. lia. }
    pose proof (AOC (O_seciF c1) ic_nch 0 (SEC_INST + 56) (idx + 1) IN_seci I56 EV0 (SOL (SEC_INST + 56) ltac:(unfold SEC_INST; clear; lia)) EV ltac:(unfold SEC_INST; clear; lia) ltac:(unfold SEC_INST; cbn; clear; lia)) as X. exact X. }
  assert (CMU : cell_ok v3 (mkACell 0xee040 4 0)).
  { pose proof (AOC O_secmF (mkCell (SLit 0xee040) 1 (SLit 0)) 0 0xee040 0 IN_secm ltac:(cbn; left; reflexivity) EV0 (SOL 0xee040 ltac:(clear; lia)) eq_refl ltac:(clear; lia) ltac:(cbn; clear; lia)) as X1.
    pose proof (AOC O_secmF (mkCell (SLit 0xee041) 3 (SLit 0)) 0 0xee041 0 IN_secm ltac:(cbn; right; left; reflexivity) EV0 (SOL 0xee041 ltac:(clear; lia)) eq_refl ltac:(clear; lia) ltac:(cbn; clear; lia)) as X3.
    assert (ZB : forall w k, (k < w)%nat -> (w <= 8)%nat -> nth k (enc_bytes w (Z_to_bv 64 0)) (Z_to_bv 8 0) = Z_to_bv 8 0).
    { intros w0 k0 H1 H2. rewrite (ReprGlue.nth_enc_bytes w0 k0 0 H1 H2). apply f_equal. unfold MallocInv.le_byte. rewrite Z.mod_0_l by (apply Z.pow_nonzero; lia). rewrite Z.shiftr_0_l. reflexivity. }
    intros k Hk. cbn [c_addr c_w RtCells.c_val] in Hk |- *. rewrite (ZB 4%nat k Hk ltac:(clear; lia)).
    destruct k as [|k].
    - specialize (X1 0%nat ltac:(cbn; clear; lia)). cbn [c_addr c_w RtCells.c_val c_width] in X1. change (Z.to_nat 1) with 1%nat in X1. rewrite (ZB 1%nat 0%nat ltac:(clear; lia) ltac:(clear; lia)) in X1.
      replace (0xee040 + Z.of_nat 0) with (0 + 0xee040 + Z.of_nat 0) by (clear; lia). exact X1.
    - specialize (X3 k ltac:(cbn; clear -Hk; lia)). cbn [c_addr c_w RtCells.c_val c_width] in X3. change (Z.to_nat 3) with 3%nat in X3. rewrite (ZB 3%nat k ltac:(clear -Hk; lia) ltac:(clear; lia)) in X3.
      replace (0xee040 + Z.of_nat (S k)) with (0 + 0xee041 + Z.of_nat k) by (clear; lia). exact X3. }

  assert (EBw : bv_unsigned (eval rhoE Bw) = pw).
  { unfold Bw, pw. cbn [eval]. rewrite E145, E147, add_val, sll_val. fold G idx. rewrite !u64_lit by (clear -P1 P2 P4 IDX0 ACV; lia).
    change (3 mod 64) with 3. rewrite Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 3) with 8.
    rewrite (Z.mod_small (idx * 8)) by (clear -IDX0 P4; lia). rewrite Z.mod_small by (clear -P1 P2 P4 IDX0 ACV; lia). clear. lia. }
  assert (PWB : ag_pab G <= pw /\ pw + blk <= ag_pab G + 8388608) by (unfold pw; clear -IDX0 HROOM P4; lia).
  assert (CPW : cell_ok v3 (mkACell pw 8 ua)).
  { pose proof (AOC (O_pxF blk dpx xc) (xc_map nx) pw 0 ua IN_px Hxc EBw (SOL 0 ltac:(clear; lia)) ltac:(cbn [SymState.c_val xc_map eval]; rewrite Enx; apply WZ)
                  ltac:(clear -PWB P1; lia) ltac:(cbn [c_width xc_map]; clear -PWB P2 ACV Hblk; lia)) as X.
    rewrite Z.add_0_r in X. exact X. }

  destruct (site8_vals nW st tmax nx Hnx BX A Kc rho a rhoE tp tr md HJ) as (EB4 & EL4 & _). cbn zeta in EB4, EL4. fold nv ua in EB4, EL4.
  assert (ESHub : Sh ub = Sh ua + 768).
  { unfold Sh, ub. replace (ua + 6144) with (ua + 768 * 8) by (clear; lia). rewrite Z.div_add by (clear; lia). clear. lia. }
  pose proof (Z.div_pos nv 8 ltac:(clear -HN; lia) ltac:(clear; lia)) as NP. pose proof (Z.div_lt_upper_bound nv 8 (2 ^ 36) ltac:(clear; lia) ltac:(clear -HN; lia)) as NU.
  assert (SHB : 2147450880 <= Sh ua /\ Sh ua + L / 8 <= 17594333495296).
  { unfold Sh, SHADOW_OFF. pose proof (Z.div_pos ua 8 ltac:(clear -UAB; lia) ltac:(clear; lia)) as D0.
    pose proof (Z.div_le_mono (ua + L) 140737479966720 8 ltac:(clear; lia) ltac:(clear -UAB; lia)) as D1. change (140737479966720 / 8) with 17592184995840 in D1.
    assert (DS : ua / 8 + L / 8 <= (ua + L) / 8) by (apply Z.div_le_lower_bound; [clear; lia|]; pose proof (Z.mul_div_le ua 8 ltac:(clear; lia)); pose proof (Z.mul_div_le L 8 ltac:(clear; lia)); lia).
    clear -D0 D1 DS. lia. }
  assert (L8B : nv / 8 + 1024 <= L / 8).
  { pose proof (Z.div_le_mono (nv + 8192) L 8 ltac:(clear; lia) LB) as D. replace (nv + 8192) with (nv + 1024 * 8) in D by (clear; lia). rewrite Z.div_add in D by (clear; lia). exact D. }
  assert (VZ : forall g, 0 <= g < nv / 8 -> v3 (Sh ub + g) = Some (Z_to_bv 8 0)).
  { intros g Hg. destruct (AO _ (INRS _ IN_4z)) as (_ & _ & _ & ZO). cbn [ob_base ob_cells ob_lo ob_hi ob_dflt O_4z] in ZO. specialize (ZO eq_refl g).
    unfold obj_lo_of, obj_hi_of in ZO. cbn [ob_lo ob_hi ob_cells ob_base O_4z] in ZO. rewrite soff_lit_small in ZO by (clear; lia).
    rewrite (soff_of_val rhoE (a2e8 nx) (nv / 8) EL4) in ZO by (clear -NP NU; lia). rewrite EB4 in ZO.
    unfold v3. rewrite view_in by (rewrite ESHub; clear -SHB Hg L8B; lia). rewrite ESHub.
    apply ZO; [exact Hg|]. intros HC. unfold covered in HC. apply Exists_exists in HC as (cc & Hcc & _). exact Hcc. }
  pose proof (nmod8_of_par nW st tmax nx Hnx BX A Kc rho a rhoE tp tr md HJ) as (PAR0 & PAR1). fold nv in PAR0, PAR1.
  pose proof (proj1 (Forall_forall _ _) HFacts _ FPAR) as HPARF.
  destruct (site9_vals nW st tmax nx Hnx BX A Kc rho a rhoE tp tr md HJ) as (_ & EBP9). cbn zeta in EBP9. fold nv ua in EBP9.
  assert (VP : nv mod 8 <> 0 -> v3 (Sh ub + nv / 8) = Some (Z_to_bv 8 (nv mod 8))).
  { intros Hm. destruct partial eqn:EP; [|exfalso; exact (Hm (PAR0 HPARF))].
    assert (IN_P : In (O_Pf9 nx) RS) by (unfold RS, RSF; try rewrite EP; cbn [app In]; repeat (first [left; reflexivity | right])).
    assert (EV : eval rhoE (SAlu ALU_AND (SVar 12) (SLit 7)) = Z_to_bv 64 (nv mod 8)).
    { apply bv_eq. cbn [eval]. rewrite E12, and_val. fold nv. rewrite (u64_lit 7) by (clear; lia). rewrite land_7 by (clear -HN; lia). symmetry. apply u64_lit. pose proof (Z.mod_pos_bound nv 8 ltac:(clear; lia)). lia. }
    pose proof (AOC (O_Pf9 nx) (mkCell (SLit 0) 1 (SAlu ALU_AND (SVar 12) (SLit 7))) (Sh ua + 768 + nv / 8) 0 (nv mod 8) IN_P ltac:(cbn; left; reflexivity) EBP9 (SOL 0 ltac:(clear; lia)) EV
                  ltac:(clear -SHB NP; lia) ltac:(cbn [c_width]; clear -SHB L8B; lia)) as X.
    specialize (X 0%nat ltac:(cbn; clear; lia)). cbn [c_addr c_w RtCells.c_val c_width Z.of_nat] in X. rewrite !Z.add_0_r in X.
    rewrite ESHub. rewrite X. apply f_equal. apply B1E. pose proof (Z.mod_pos_bound nv 8 ltac:(clear; lia)). lia. }

  destruct (site7_vals nW st tmax nx Hnx BX A Kc rho a rhoE tp tr md HJ) as (_ & _ & EBR & EL3b & V512 & VM). cbn zeta in EBR, EL3b, V512, VM. fold nv ua L in EBR, EL3b, V512, VM.
  destruct (site3_vals nW st tmax nx Hnx BX A Kc rho a rhoE tp tr md HJ) as (EB3 & _ & EL3). fold ua in EB3.
  destruct (site1_bounds nW st tmax nx Hnx BX A Kc rho a rhoE tp tr md HJ) as (EB1 & EL1 & _). fold ua in EB1.
  assert (EUB : bv_unsigned (eval rhoE (UBs nx)) = ub).
  { unfold UBs. cbn [eval]. rewrite Enx, add_val, !u64_lit by (clear; lia). fold ua. rewrite Z.mod_small by (clear -UAB; lia). reflexivity. }
  assert (EVT : bv_unsigned (eval rhoE vT) = T) by (unfold vT; cbn [eval]; rewrite E151; apply u64_lit; fold G T; clear -G4 G5 ACV; lia).
  assert (RG_Mlo : obj_range rhoE (O_Mlo nx mc) = (ua, ua + 6144)) by (unfold O_Mlo; rewrite obj_range_mk by (clear; lia); rewrite EVnx; f_equal; clear; lia).
  assert (RG_fill : obj_range rhoE (O_fill nx) = (ub, ub + 4096)) by (unfold O_fill; rewrite obj_range_mk by (clear; lia); rewrite EUB; f_equal; clear; lia).
  assert (RG_Mhi : obj_range rhoE (O_Mhi nx) = (ua + 10240, ua + L)).
  { unfold O_Mhi, obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite soff_lit_small by (clear; lia).
    rewrite (soff_of_val rhoE (SVar V_MS) L) by (first [cbn [eval]; rewrite E142; apply u64_lit; clear -UAB; lia | clear -UAB; lia]). rewrite EVnx. reflexivity. }
  assert (RG_1 : obj_range rhoE (O_1 nx) = (Sh ua, Sh ua + 512)) by (unfold O_1, L1; rewrite obj_range_mk by (clear; lia); rewrite EB1; f_equal; clear; lia).
  assert (RG_3 : obj_range rhoE (O_3 nx) = (Sh ua + 512, Sh ua + 768)) by (unfold O_3, L3; rewrite obj_range_mk by (clear; lia); rewrite EB3; f_equal; clear; lia).
  assert (RG_4z : obj_range rhoE (O_4z nx) = (Sh ua + 768, Sh ua + 768 + nv / 8)).
  { unfold O_4z, obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite soff_lit_small by (clear; lia).
    rewrite (soff_of_val rhoE (a2e8 nx) (nv / 8) EL4) by (clear -NP NU; lia). rewrite EB4. f_equal. clear. lia. }
  set (v8 := secneeded nv / 8) in *.
  assert (RG_3b : obj_range rhoE (O_3b nx) = (Sh ua + v8 + 256, Sh ua + L / 8)).
  { unfold O_3b, obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite soff_lit_small by (clear; lia).
    rewrite (soff_of_val rhoE L3b (L / 8 - v8 - 256) EL3b) by (clear -V512 VM SHB; lia). rewrite EBR. f_equal; clear; lia. }
  assert (RG_P : obj_range rhoE (O_Pf9 nx) = (Sh ua + 768 + nv / 8, Sh ua + 768 + nv / 8 + 1)) by (unfold O_Pf9; rewrite obj_range_mk by (clear; lia); rewrite EBP9; f_equal; clear; lia).
  assert (RG_px : obj_range rhoE (O_pxF blk dpx xc) = (pw, pw + blk)) by (unfold O_pxF; rewrite obj_range_mk by (clear -Hblk; lia); rewrite EBw; f_equal; clear; lia).
  assert (RG_st : obj_range rhoE (O_stF c5) = (T + 2768, T + 3168)) by (unfold O_stF; rewrite obj_range_mk by (clear; lia); rewrite EVT; reflexivity).
  assert (RG_seci : obj_range rhoE (O_seciF c1) = (SEC_INST, SEC_INST + 64)) by (unfold O_seciF; rewrite obj_range_mk by (unfold SEC_INST; clear; lia); reflexivity).
  assert (RG_secs : obj_range rhoE (O_secsF c2) = (SEC_INST + 64, 0xee040)) by (unfold O_secsF; rewrite obj_range_mk by (unfold SEC_INST; clear; lia); reflexivity).
  assert (RG_secm : obj_range rhoE O_secmF = (0xee040, 0xee044)) by (unfold O_secmF; rewrite obj_range_mk by (clear; lia); reflexivity).
  assert (RG_secg : obj_range rhoE (O_secgF c4) = (0xee048, 0xee070)) by (unfold O_secgF; rewrite obj_range_mk by (clear; lia); reflexivity).
  assert (RG_san : obj_range rhoE O_san = (0xe9b28, 0xe9b30)).
  { change O_san with (mkObj (SLit 0) (SLit 0xe9b28) (SLit 0xe9b30) (ob_cells O_san) DUnknown). rewrite obj_range_mk by (clear; lia). reflexivity. }
  assert (RG_oom : obj_range rhoE O_oom = (0x173660, 0x173662)).
  { change O_oom with (mkObj (SLit 0) (SLit 0x173660) (SLit 0x173662) (ob_cells O_oom) DUnknown). rewrite obj_range_mk by (clear; lia). reflexivity. }
  assert (RG_errno : obj_range rhoE O_errno = (ERRNO_A, ERRNO_A + 4)).
  { change O_errno with (mkObj (SLit 0) (SLit ERRNO_A) (SLit (ERRNO_A + 4)) (ob_cells O_errno) DUnknown). rewrite obj_range_mk by (unfold ERRNO_A; clear; lia). reflexivity. }

  assert (PARB : if partial then nv mod 8 <> 0 else nv mod 8 = 0) by (destruct partial; [exact (PAR1 HPARF) | exact (PAR0 HPARF)]).
  assert (EV8 : v8 = 768 - 256 + nv / 8 + (if partial then 1 else 0)).
  { unfold v8. rewrite ENS. replace (round_up nv 8 + 4096) with (round_up nv 8 + 512 * 8) by (clear; lia). rewrite Z.div_add by (clear; lia).
    unfold round_up. rewrite Z.div_mul by (clear; lia). pose proof (Z.div_mod nv 8 ltac:(clear; lia)) as DN. pose proof (Z.mod_pos_bound nv 8 ltac:(clear; lia)) as MN.
    destruct partial.
    - replace ((nv + 8 - 1) / 8) with (nv / 8 + 1) by (apply Z.div_unique with (nv mod 8 - 1); clear -DN MN PARB; lia). clear. lia.
    - replace ((nv + 8 - 1) / 8) with (nv / 8) by (apply Z.div_unique with 7; clear -DN MN PARB; lia). clear. lia. }

  assert (DUK : forall o, In o RS -> ob_dflt o = DUnknown \/ ob_dflt o = DZero).
  { intros o Ho. unfold RS, RSF in Ho. apply in_app_or in Ho as [Ho|Ho]; [|apply in_app_or in Ho as [Ho|Ho]; [|apply in_app_or in Ho as [Ho|Ho]]].
    - cbn [In] in Ho. destruct Ho as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [ob_dflt O_fill O_4z O_3b O_3 O_1]; first [left; reflexivity | right; reflexivity].
    - cbn [In] in Ho. destruct Ho as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]; left; reflexivity.
    - cbn [In] in Ho. destruct Ho as [<-|[<-|[<-|[]]]]; cbn [ob_dflt O_Mlo O_Mhi O_pxF]; [right; reflexivity | right; reflexivity | exact Hdpx].
    - destruct partial; cbn [In] in Ho; [destruct Ho as [<-|[]]; left; reflexivity | destruct Ho]. }
  assert (INL : forall o, In o ([O_fill nx; O_4z nx; O_3b nx; O_3 nx; O_1 nx] ++ [O_seciF c1; O_secsF c2; O_secmF; O_secgF c4; O_san; O_oom; O_errno; O_stF c5] ++ [O_Mlo nx mc; O_Mhi nx; O_pxF blk dpx xc]) -> In o RS).
  { intros o Ho. unfold RS, RSF. apply in_app_or in Ho as [Ho|Ho]; [apply in_or_app; left; exact Ho|].
    apply in_app_or in Ho as [Ho|Ho]; apply in_or_app; right; apply in_or_app; [left; exact Ho | right; apply in_or_app; left; exact Ho]. }
  assert (PRESo : forall o z, In o RS -> fst (obj_range rhoE o) <= z < snd (obj_range rhoE o) -> exists bb, v3 z = Some bb) by (intros o z Ho Hz; exact (AOP o z Ho (DUK o Ho) Hz)).
  assert (PRES : forall z, chg_s G ua L pw blk z -> exists b, v3 z = Some b).
  { intros z [X|[X|[[X|X]|X]]].
    - unfold zimg in X. destruct X as [X|[X|[X|X]]].
      + destruct (Z_lt_dec z (SEC_INST + 64)) as [L1|L1]; [|destruct (Z_lt_dec z 0xee040) as [L2|L2]].
        * apply (PRESo (O_seciF c1) z); [apply INL; cbn [app In]; repeat (first [left; reflexivity | right]) | rewrite RG_seci; cbn [fst snd]; clear -X L1; lia].
        * apply (PRESo (O_secsF c2) z); [apply INL; cbn [app In]; repeat (first [left; reflexivity | right]) | rewrite RG_secs; cbn [fst snd]; clear -X L1 L2; lia].
        * apply (PRESo O_secmF z); [apply INL; cbn [app In]; repeat (first [left; reflexivity | right]) | rewrite RG_secm; cbn [fst snd]; clear -X L2; lia].
      + apply (PRESo (O_secgF c4) z); [apply INL; cbn [app In]; repeat (first [left; reflexivity | right]) | rewrite RG_secg; cbn [fst snd]; exact X].
      + apply (PRESo O_oom z); [apply INL; cbn [app In]; repeat (first [left; reflexivity | right]) | rewrite RG_oom; cbn [fst snd]; clear -X; lia].
      + apply (PRESo O_errno z); [apply INL; cbn [app In]; repeat (first [left; reflexivity | right]) | rewrite RG_errno; cbn [fst snd]; exact X].
    - apply (PRESo (O_stF c5) z); [apply INL; cbn [app In]; repeat (first [left; reflexivity | right]) | rewrite RG_st; cbn [fst snd]; exact X].
    - destruct (Z_lt_dec z (ua + 6144)) as [L1|L1]; [|destruct (Z_lt_dec z (ua + 10240)) as [L2|L2]].
      + apply (PRESo (O_Mlo nx mc) z); [apply INL; cbn [app In]; repeat (first [left; reflexivity | right]) | rewrite RG_Mlo; cbn [fst snd]; clear -X L1; lia].
      + apply (PRESo (O_fill nx) z); [apply INL; cbn [app In]; repeat (first [left; reflexivity | right]) | rewrite RG_fill; cbn [fst snd]; unfold ub; clear -L1 L2; lia].
      + apply (PRESo (O_Mhi nx) z); [apply INL; cbn [app In]; repeat (first [left; reflexivity | right]) | rewrite RG_Mhi; cbn [fst snd]; clear -X L2; lia].
    - destruct (Z_lt_dec z (Sh ua + 512)) as [L1|L1]; [|destruct (Z_lt_dec z (Sh ua + 768)) as [L2|L2]; [|destruct (Z_lt_dec z (Sh ua + 768 + nv / 8)) as [L3|L3]]].
      + apply (PRESo (O_1 nx) z); [apply INL; cbn [app In]; repeat (first [left; reflexivity | right]) | rewrite RG_1; cbn [fst snd]; clear -X L1; lia].
      + apply (PRESo (O_3 nx) z); [apply INL; cbn [app In]; repeat (first [left; reflexivity | right]) | rewrite RG_3; cbn [fst snd]; clear -L1 L2; lia].
      + apply (PRESo (O_4z nx) z); [apply INL; cbn [app In]; repeat (first [left; reflexivity | right]) | rewrite RG_4z; cbn [fst snd]; clear -L2 L3; lia].
      + destruct (Z_lt_dec z (Sh ua + v8 + 256)) as [L4|L4].
        *
          destruct partial eqn:EP; [|exfalso; clear -L3 L4 EV8; lia].
          apply (PRESo (O_Pf9 nx) z); [unfold RS, RSF; apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; left; reflexivity | rewrite RG_P; cbn [fst snd]; clear -L3 L4 EV8; lia].
        * apply (PRESo (O_3b nx) z); [apply INL; cbn [app In]; repeat (first [left; reflexivity | right]) | rewrite RG_3b; cbn [fst snd]; clear -X L4; lia].
    - apply (PRESo (O_pxF blk dpx xc) z); [apply INL; cbn [app In]; repeat (first [left; reflexivity | right]) | rewrite RG_px; cbn [fst snd]; exact X]. }

  set (K_san := ((SLit 0, 0xe9b28, 0xe9b30, [(0xe9b28, 8%nat, SLit 0x1a36f)]) : carve_spec)).
  assert (ESAN : carve_obj K_san = O_san) by reflexivity.
  assert (SM_san : spec_small K_san) by (unfold K_san, spec_small; split; [lia|]; split; [lia|]; split; [lia|]; unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia).
  assert (INR : forall x : word, in_ranges rhoE R x ->
            (exists k, In k (N_m1 ++ [K_san]) /\ fst (spec_range rhoE k) <= bv_unsigned x < snd (spec_range rhoE k))
            \/ chg_s G ua L pw blk (bv_unsigned x) \/ bv_unsigned x = 0x173661).
  { intros x (o & HoR & Hr). unfold R in HoR. apply in_app_or in HoR as [HoR|HoR].
    - left. rewrite <- N_m1_ok in HoR. apply in_map_iff in HoR as (k & <- & Hk). exists k. split; [apply in_or_app; left; exact Hk|].
      rewrite (carve_range rhoE k (proj1 (Forall_forall _ _) N_m1_small k Hk)) in Hr. exact Hr.
    - set (z := bv_unsigned x) in *.
      assert (RUNZ : Sh ua <= z < Sh ua + L / 8 -> chg_s G ua L pw blk z) by (intros X; right; right; left; right; exact X).
      assert (MAPZ : ua <= z < ua + L -> chg_s G ua L pw blk z) by (intros X; right; right; left; left; exact X).
      assert (IMGZ : zimg z -> chg_s G ua L pw blk z) by (intros X; left; exact X).
      unfold RS, RSF in HoR. apply in_app_or in HoR as [HoR|HoR]; [|apply in_app_or in HoR as [HoR|HoR]; [|apply in_app_or in HoR as [HoR|HoR]]].
      + cbn [In] in HoR. destruct HoR as [<-|[<-|[<-|[<-|[<-|[]]]]]]; right; left.
        * rewrite RG_fill in Hr. cbn [fst snd] in Hr. apply MAPZ. unfold ub in Hr. clear -Hr LB HN. lia.
        * rewrite RG_4z in Hr. cbn [fst snd] in Hr. apply RUNZ. clear -Hr L8B. lia.
        * rewrite RG_3b in Hr. cbn [fst snd] in Hr. apply RUNZ. clear -Hr V512. lia.
        * rewrite RG_3 in Hr. cbn [fst snd] in Hr. apply RUNZ. clear -Hr L8B NP. lia.
        * rewrite RG_1 in Hr. cbn [fst snd] in Hr. apply RUNZ. clear -Hr L8B NP. lia.
      + cbn [In] in HoR. destruct HoR as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]].
        * right; left. apply IMGZ. rewrite RG_seci in Hr. cbn [fst snd] in Hr. unfold zimg, SEC_INST in *. clear -Hr. lia.
        * right; left. apply IMGZ. rewrite RG_secs in Hr. cbn [fst snd] in Hr. unfold zimg, SEC_INST in *. clear -Hr. lia.
        * right; left. apply IMGZ. rewrite RG_secm in Hr. cbn [fst snd] in Hr. unfold zimg, SEC_INST in *. clear -Hr. lia.
        * right; left. apply IMGZ. rewrite RG_secg in Hr. cbn [fst snd] in Hr. unfold zimg in *. clear -Hr. lia.
        * left. exists K_san. split; [apply in_or_app; right; left; reflexivity|]. rewrite <- (carve_range rhoE K_san SM_san), ESAN. exact Hr.
        * rewrite RG_oom in Hr. cbn [fst snd] in Hr. destruct (Z.eq_dec z 0x173660) as [E0|NE0]; [right; left; apply IMGZ; unfold zimg; clear -E0; lia | right; right; clear -Hr NE0; lia].
        * right; left. apply IMGZ. rewrite RG_errno in Hr. cbn [fst snd] in Hr. unfold zimg. clear -Hr. lia.
        * right; left. right; left. rewrite RG_st in Hr. exact Hr.
      + cbn [In] in HoR. destruct HoR as [<-|[<-|[<-|[]]]]; right; left.
        * rewrite RG_Mlo in Hr. cbn [fst snd] in Hr. apply MAPZ. clear -Hr UAB. lia.
        * rewrite RG_Mhi in Hr. cbn [fst snd] in Hr. apply MAPZ. clear -Hr. lia.
        * rewrite RG_px in Hr. right; right; right. exact Hr.
      + destruct partial; cbn [In] in HoR; [|destruct HoR]. destruct HoR as [<-|[]]. right; left. rewrite RG_P in Hr. cbn [fst snd] in Hr. apply RUNZ. clear -Hr L8B NP. lia. }

  pose proof HRest as (Hsep & _ & _ & _ & _ & _ & _ & _ & HMIs).
  assert (HAg : AInv As rhoE tp md) by exact HA.
  assert (NK : forall k, In k (N_m1 ++ [K_san]) -> In (carve_obj k) R /\ spec_small k /\ spec_covered k
            /\ cells_in_view rhoE (rd_of segs (rm rhoE)) (fst (spec_range rhoE k) - (let '(_, lo, _, _) := k in lo)) (let '(_, _, _, cs) := k in cs)).
  { intros k Hk. apply in_app_or in Hk as [Hk|Hk].
    - split; [unfold R; apply in_or_app; left; rewrite <- N_m1_ok; apply in_map; exact Hk|].
      split; [exact (proj1 (Forall_forall _ _) N_m1_small k Hk)|].
      split; [apply coverb_sound; exact (proj1 (forallb_forall _ _) N_m1_coverb k Hk)|].
      pose proof (proj1 (Forall_forall _ _) (N_m1_civ AInvA_die As rhoE tp md HAg ltac:(rewrite Bg; exact E151) ltac:(rewrite Bg; exact E152) ltac:(rewrite Bg; exact E153) ltac:(rewrite Bg; exact E154)
                                               ltac:(rewrite Bg; exact E155) ltac:(rewrite Bg; exact E156)) k Hk) as CV. cbn beta in CV.
      destruct k as [[[base lo] hi] cs]. cbn [spec_range fst]. replace (bv_unsigned (eval rhoE base) + lo - lo) with (bv_unsigned (eval rhoE base)) by (clear; lia). exact CV.
    - destruct Hk as [<-|[]].
      split; [unfold R; apply in_or_app; right; rewrite ESAN; apply INL; cbn [app In]; repeat (first [left; reflexivity | right])|].
      split; [exact SM_san|].
      split; [apply coverb_sound; reflexivity|].
      destruct HMIs as (HMIc & _ & _). pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail HMIc))))) as HSAN.
      assert (CSAN : cell_ok (view segs (rm rhoE)) (mkACell (0 + 0xe9b28) 8 0x1a36f)).
      { intros j Hj. specialize (HSAN j Hj). cbn [c_addr c_w RtCells.c_val] in HSAN, Hj |- *. rewrite Bg in HSAN. fold G in HSAN.
        rewrite maskv_out in HSAN by (apply (fs_footb_img G _ HG); clear -Hj; lia). exact HSAN. }
      cbn [spec_range fst K_san]. replace (bv_unsigned (eval rhoE (SLit 0)) + 0xe9b28 - 0xe9b28) with 0 by (cbn [eval]; rewrite u64_lit by (clear; lia); clear; lia).
      unfold cells_in_view. apply Forall_cons; [|apply Forall_nil].
      exact (civ_cell rhoE (rm rhoE) 0 0xe9b28 8 0x1a36f (SLit 0x1a36f) CSAN eq_refl ltac:(clear; lia) ltac:(cbn; clear; lia)). }
  assert (VO : forall z, ~ chg_s G ua L pw blk z -> v3 z = vE z).
  { intros z Hz. unfold v3, vE. destruct (Z_le_dec 0 z) as [l|n]; [destruct (Z_lt_dec z (2 ^ 64)) as [l0|n]|].
    2,3: rewrite !view_out by (clear -n; lia) || rewrite !view_out by (clear -n l; lia); reflexivity.
    rewrite !view_in by (clear -l l0; lia).
    destruct (in_ranges_dec rhoE R (Z_to_bv 64 z)) as [Hin|Hout].
    - destruct (INR _ Hin) as [(k & Hk & Hr)|[Hc|E1]]; rewrite ?u64_lit in * by (clear -l l0; lia).
      + unfold rho3. exact (absorb_specs_view rhoE _ tr (vms md tp ms) (vmd md) K R (N_m1 ++ [K_san]) (rd_of segs (rm rhoE)) Hsm1 eq_refl NK z k Hk Hr).
      + exfalso. exact (Hz Hc).
      +
        assert (IN_oom : In O_oom R) by (apply INRS; apply INL; cbn [app In]; repeat (first [left; reflexivity | right])).
        destruct (AO _ IN_oom) as (_ & CE & _ & _). change (ob_cells O_oom) with [mkCell (SLit 0x173661) 1 (SLit 1)] in CE.
        destruct (CE _ (or_introl eq_refl)) as (_ & _ & CEj). pose proof (CEj 0%nat ltac:(cbn; clear; lia)) as X. clear CEj.
        change (ob_base O_oom) with (SLit 0) in X. cbn [c_off c_width SymState.c_val eval] in X. change (Z.to_nat 1) with 1%nat in X. change (Z.of_nat 0) with 0 in X.
        rewrite soff_lit_small, (u64_lit 0), Z.add_0_r in X by (clear; lia). rewrite Z.add_0_l in X. rewrite E1. unfold rho3.
        transitivity (Some (nth 0 (enc_bytes 1 (Z_to_bv 64 1)) (Z_to_bv 8 0))); [exact X|]. symmetry.
        destruct HMIs as (HMIc & _ & _). pose proof (Forall_inv HMIc) as C9. specialize (C9 0%nat ltac:(cbn; clear; lia)).
        cbn [c_addr c_w RtCells.c_val Z.of_nat] in C9. rewrite Z.add_0_r in C9. rewrite Bg in C9. fold G in C9.
        rewrite maskv_out in C9 by (apply (fs_footb_img G _ HG); clear; lia). rewrite view_in in C9 by (clear; lia). exact C9.
    - unfold rho3, rd_of. rewrite rm_absorb_out by exact Hout. reflexivity. }
  assert (RMO : forall x, 0 <= x < 2 ^ 64 -> ~ rt_zoneM G x -> ~ chg_s G ua L pw blk x -> ~ in_rangesZ IMG_S x -> rm rho3 (Z_to_bv 64 x) = rm rhoE (Z_to_bv 64 x)).
  { intros x Bx Hz1 Hz2 Hz4. unfold rho3. apply rm_absorb_out. intros Hin.
    destruct (INR _ Hin) as [(k & Hk & Hr)|[Hc|E1]]; rewrite ?u64_lit in * by exact Bx.
    - apply in_app_or in Hk as [Hk|Hk].
      + apply Hz1. exact (N_m1_zone G rhoE k x HG E151 E152 Hk Hr).
      + destruct Hk as [<-|[]]. apply Hz4. cbn [spec_range fst snd K_san eval] in Hr. rewrite (u64_lit 0) in Hr by (clear; lia).
        unfold IMG_S, in_rangesZ. exists 0xe9b28, 8. split; [right; right; left; reflexivity | clear -Hr; lia].
    - exact (Hz2 Hc).
    - apply Hz4. unfold IMG_S, in_rangesZ. exists 0x173660, 2. split; [right; right; right; left; reflexivity | clear -E1; lia]. }
  assert (RWR : Forall (fun o => dflt_writable (ob_dflt o) = true) R).
  { unfold R. apply Forall_app. split.
    - pose proof (R9_writable [] [] []) as X. unfold R9 in X. apply Forall_app in X. exact (proj1 X).
    - apply Forall_forall. intros o Ho. destruct (DUK o Ho) as [E|E]; rewrite E; reflexivity. }
  assert (DEFM : forall x, IMG_HI <= x < 2 ^ 64 -> rm rhoE (Z_to_bv 64 x) <> None -> rm rho3 (Z_to_bv 64 x) <> None).
  { intros x Bx Hd. destruct (in_ranges_dec rhoE R (Z_to_bv 64 x)) as [Hin|Hout].
    - unfold rho3. apply (absorb_defined rhoE _ tr (vms md tp ms) (vmd md) K R (Z_to_bv 64 x) Hsm1 eq_refl RWR Hin). rewrite u64_lit by (unfold IMG_HI in Bx; clear -Bx; lia). exact (proj1 Bx).
    - unfold rho3. rewrite rm_absorb_out by exact Hout. exact Hd. }
  assert (DEFB : forall x, SHADOW_BAND_LO <= x < SHADOW_BAND_HI -> rm rhoE (Z_to_bv 64 x) <> None -> rm rho3 (Z_to_bv 64 x) <> None).
  { intros x Bx. apply DEFM. unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END, IMG_HI in *. clear -Bx. lia. }

  assert (HPDs : pendS As ua L md).
  { destruct HP as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12). unfold pendS. rewrite Bg, Bs. fold G.
    split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|]. split; [exact Q5|]. split; [exact Q6|]. split; [exact Q7|]. split; [exact Q8|].
    split; [exact Q9|]. split; [exact Q10|]. split; [exact Q11|]. exact HDB. }
  assert (HKMs : idx + 1 <= aa_Km As) by (rewrite BKm; unfold idx; clear -HL9; lia).
  pose proof (sec_rebuild As rhoE rho3 tp md nv ua blk HA HN) as RB. cbn zeta in RB. rewrite Bg, Bs in RB. fold G idx L ub pw v3 vE in RB.
  specialize (RB HPDs (proj1 Hblk) HROOM HKMs C0 C8 C16 C24 CPW CI0 CI8 CI16 CI24 C48 C56 CMU VH2 VHN VH0 VH1 VMG0 VMG8 VZ VP PRES VO DEFB).
  pose proof (sec_kept CST XGL HCST HXGL HCSTM HCSTS As rhoE rho3 tp md nv ua blk HA HN) as KP. cbn zeta in KP. rewrite Bg, Bs in KP. fold G idx L pw in KP.
  specialize (KP HPDs (proj1 Hblk) HROOM RMO DEFB).

  set (A1 := ax_setS (ax_setS F (set_objs (ax_S F) (K ++ R))) (set_objs (ax_S (ax_setS F (set_objs (ax_S F) (K ++ R)))) K)) in Hb.
  assert (EV3 : forall e, eval rho3 e = eval rhoE e) by (intros e; unfold rho3; apply eval_absorb).
  assert (OR3 : forall o, obj_range rho3 o = obj_range rhoE o) by (intros o; unfold obj_range, obj_lo_of, obj_hi_of, soff; rewrite !EV3; reflexivity).
  assert (HFXP : forall p, In p (unwind_factsS W st ++ pre_facts malloc_depth) -> holds rhoE p) by (intros p Hp; exact (proj1 (Forall_forall _ _) HFacts p (FPF p Hp))).
  assert (Hhigh : holds rhoE F_sp_high) by (apply HFXP; apply in_or_app; right; unfold pre_facts; cbn [app In]; right; left; reflexivity).
  destruct (sw_range_gen segs rhoE (set_objs (ax_S F) (K ++ R)) _ (sw9 swc) Hsm1 ltac:(cbn; left; reflexivity) eq_refl Hhigh) as (SW1 & SW2 & SW3).
  assert (SW0 : topG G <= fst (obj_range rhoE (sw9 swc))) by (rewrite (sw_lo_gen rhoE (sw9 swc) eq_refl); exact Htop).
  assert (LNK : Forall (fun o => topG G + 16 <= bv_unsigned (eval rhoE (ob_base o)) <= 2 ^ 47 /\ ob_lo o = SLit (-16) /\ ob_hi o = SLit 0) (unwind_objs W)).
  { apply (unwind_objs_above _ _ (topG G)); [|clear -SW0 SW2 SW3; lia|clear -ACV; lia]. apply Forall_forall. intros p Hp. apply HFXP. apply in_or_app. left. exact (chain_pre_factsS W st p HW Hp). }
  pose proof HP as (_ & _ & _ & PDI & _). destruct PDI as (_ & _ & PDT & _ & PDB). fold G in PDT. unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in PDB.

  assert (KDISJ : forall lo hi, 6578176 <= lo -> hi <= topG G -> Forall (fun o' => ranges_disjoint (obj_range rhoE o') (lo, hi)) K).
  { intros lo hi Hlo Hhi. unfold K, KEPTF. constructor.
    - unfold ranges_disjoint. right; right; right. cbn [fst snd]. clear -SW0 Hhi. lia.
    - apply Forall_app. split.
      + eapply Forall_impl; [|exact LNK]. intros [ob olo ohi ocs od] (B1 & L1 & H1). cbn [ob_base ob_lo ob_hi] in B1, L1, H1. subst olo ohi.
        unfold ranges_disjoint. rewrite obj_range_mk by (clear; lia). cbn [fst snd]. right; right; right. clear -B1 Hhi. lia.
      + unfold A_globals, O_got, O_rtc, GOT_LO, GOT_HI, RTC_LO, RTC_HI. repeat apply Forall_cons; try apply Forall_nil;
          unfold ranges_disjoint; rewrite obj_range_mk by (clear; lia); cbn [fst snd eval]; rewrite u64_lit by (clear; lia); right; right; left; clear -Hlo; lia. }
  assert (RM3 : forall z, ua <= z < ua + L \/ Sh ua <= z < Sh ua + L / 8 -> rm rho3 (Z_to_bv 64 z) <> None).
  { intros z Hz. assert (CZ : chg_s G ua L pw blk z) by (right; right; left; exact Hz). destruct (PRES z CZ) as [bb Hbb].
    assert (BZ : 0x646000 <= z < 2 ^ 64) by (destruct Hz as [Hz|Hz]; [clear -Hz UAB; lia | clear -Hz SHB; lia]).
    unfold v3 in Hbb. rewrite view_in in Hbb by (clear -BZ; lia). rewrite (rd_off_image _ _ _ BZ Hbb). discriminate. }
  assert (Hcv : SPA segs KJ (ax_setS A1 (set_objs (ax_S F) (K ++ [O_UBs nx]))) rho3 tp (tr, {| cfg_ms := ms; cfg_model := md |})).
  { pose proof (SPA_carve_unk segs KJ rho3 A1 tp _ (UBs nx) (SLit 0) (SVar 12) (ss_next (ax_S A1)) Hb) as CV. cbn zeta in CV.
    rewrite !EV3 in CV. unfold soff in CV. rewrite !EV3 in CV. fold (soff rhoE (SLit 0)) (soff rhoE (SVar 12)) in CV.
    rewrite (SOL 0 ltac:(clear; lia)), EUB in CV. rewrite (soff_of_val rhoE (SVar 12) nv) in CV by (first [rewrite EN12; apply u64_lit; clear -HN; lia | clear -HN; lia]).
    apply CV; clear CV.
    - exact WCU.
    - apply Pos.le_refl.
    - clear -HN. lia.
    - clear -HN. lia.
    - unfold ub. clear -UAB. lia.
    - unfold ub. clear -UAB LB. lia.
    - change (ss_objs (ax_S A1)) with K. eapply Forall_impl; [|exact (KDISJ (ub + 0) (ub + nv) ltac:(unfold ub; clear -UAB; lia) ltac:(unfold ub; clear -LB PDT; lia))].
      intros o Ho. rewrite OR3. exact Ho.
    - intros z Hz. pose proof (RM3 z ltac:(left; unfold ub in Hz; clear -Hz LB; lia)) as D.
      unfold wok_of, rd_of. destruct (rm rho3 (Z_to_bv 64 z)) as [x|]; [|exfalso; exact (D eq_refl)]. split; [reflexivity | exists x; reflexivity].
    - intros rr y j Hin. change (ax_X A1) with (ax_X F) in Hin. rewrite XFn in Hin. destruct Hin. }

  pose proof (SPA_select segs KJ rho3 _ (idxsU nW) tp _ Hcv NDU
                ltac:(intros i Hi; apply Nat.ltb_lt; exact (proj1 (forallb_forall _ _) BNDU i Hi))
                ltac:(intros i Hi; pose proof (proj1 (forallb_forall _ _) COVU i ltac:(apply in_seq; exact (conj (Nat.le_0_l i) Hi))) as X;
                      apply existsb_exists in X as (i' & Hi' & E); apply Nat.eqb_eq in E; subst i'; exact Hi')) as Hsu.
  cbn [ax_S ax_setS ss_objs set_objs] in Hsu. rewrite SELU in Hsu. clear Hcv.

  match type of Hsu with SPA _ _ ?AU _ _ _ => set (A2 := AU) in Hsu end.
  assert (Hc : SPA segs KJ (ax_setS A2 (S2F F KU)) rho3 tp (tr, {| cfg_ms := ms; cfg_model := md |})).
  { eapply SPA_restate; [exact W9 | exact D9 | reflexivity | | constructor | exact Hsu].
    constructor; [|constructor]. cbn [fst snd eval]. unfold tp_ok in Htp. apply bv_eq. rewrite u64_lit by (unfold TP_A; clear; lia).
    unfold rho3. cbn [rho_absorb rw]. rewrite Htp. pose proof (geom_old _ HG) as HGt. destruct HGt as (_ & _ & _ & G4' & _). unfold G in G4'. rewrite G4'. reflexivity. }
  clear Hsu.

  assert (EUB3 : bv_unsigned (eval rho3 (UBs nx)) = ub) by (rewrite EV3; exact EUB).
  assert (E12_3 : bv_unsigned (eval rho3 (SVar 12)) = nv) by (rewrite EV3, EN12; apply u64_lit; clear -HN; lia).
  assert (RGUB : obj_range rhoE (O_UBs nx) = (ub, ub + nv)).
  { unfold O_UBs, obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite soff_lit_small by (clear; lia).
    rewrite (soff_of_val rhoE (SVar 12) nv) by (first [rewrite EN12; apply u64_lit; clear -HN; lia | clear -HN; lia]). rewrite EUB. f_equal. clear. lia. }
  assert (OUTK : forall z, SHADOW_OFF <= z < 17594333495296 -> outside_all rho3 KU (Z_to_bv 64 z)).
  { intros z Hz. unfold SHADOW_OFF in Hz. unfold KU, KUB, outside_all. rewrite u64_lit by (clear -Hz; lia). apply Forall_app. split; [constructor|apply Forall_app; split].
    - cbn zeta. rewrite OR3. clear -SW0 SW3 Hz ACV. lia.
    - eapply Forall_impl; [|exact LNK]. intros [ob olo ohi ocs od] (B1 & L1 & H1). cbn [ob_base ob_lo ob_hi] in B1, L1, H1. subst olo ohi.
      cbn zeta. rewrite OR3, obj_range_mk by (clear; lia). cbn [fst snd]. clear -B1 Hz ACV. lia.
    - constructor; [|constructor]. cbn zeta. rewrite OR3, RGUB. cbn [fst snd]. unfold ub. clear -Hz PDB LB UAB. lia.
    - unfold A_globals, O_got, O_rtc, GOT_LO, GOT_HI, RTC_LO, RTC_HI. repeat apply Forall_cons; try apply Forall_nil; cbn zeta;
        rewrite obj_range_mk by (clear; lia); cbn [fst snd eval]; rewrite u64_lit by (clear; lia); clear -Hz; lia. }
  assert (UA8 : exists q, ua = 4096 * q) by (exists (ua / 4096); pose proof (Z.div_mod ua 4096 ltac:(clear; lia)) as X; rewrite AL, Z.add_0_r in X; exact X).
  destruct UA8 as [qu Hqu].
  assert (L8q : exists q, L = 4096 * q) by (exists (L / 4096); pose proof (Z.div_mod L 4096 ltac:(clear; lia)) as X; rewrite SMM, Z.add_0_r in X; exact X).
  destruct L8q as [ql Hql].
  assert (ESHua : Sh ua = 512 * qu + SHADOW_OFF) by (unfold Sh; rewrite Hqu; replace (4096 * qu) with (512 * qu * 8) by (clear; lia); rewrite Z.div_mul by (clear; lia); reflexivity).
  assert (EL8 : L / 8 = 512 * ql) by (rewrite Hql; replace (4096 * ql) with (512 * ql * 8) by (clear; lia); apply Z.div_mul; clear; lia).
  assert (Hd : SPA segs KJ (ax_setX (ax_setS A2 (S2F F KU)) ((UBs nx, SVar 12) :: ax_X (ax_setS A2 (S2F F KU)))) rho3 tp (tr, {| cfg_ms := ms; cfg_model := md |})).
  { apply SPA_x_publish; [exact XB9 | | exact Hc].
    change (ax_base (ax_setS A2 (S2F F KU))) with (ax_base F). rewrite BFb. change (ss_objs (ax_S (ax_setS A2 (S2F F KU)))) with KU.
    unfold xr_ok. cbn [fst snd]. rewrite EUB3, E12_3. unfold base_sv. cbn [eval]. rewrite u64_lit by (unfold SHADOW_OFF; clear; lia).
    split; [unfold ub; rewrite Hqu; apply Z.mod_divide; [clear; lia|]; exists (512 * qu + 768); clear; lia|].
    split; [unfold ub; clear -UAB LB; lia|].
    intros x Hx.
    pose proof (Z.div_mod x 8 ltac:(clear; lia)) as DMa. pose proof (Z.mod_pos_bound x 8 ltac:(clear; lia)) as MBa.
    pose proof (Z.div_mod nv 8 ltac:(clear; lia)) as DMn. pose proof (Z.mod_pos_bound nv 8 ltac:(clear; lia)) as MBn.
    set (pa := x / 8) in *.
    assert (PA : 512 * qu + 768 <= pa /\ 8 * pa <= x /\ pa <= 512 * qu + 768 + nv / 8 /\ (pa = 512 * qu + 768 + nv / 8 -> nv mod 8 <> 0)).
    { unfold ub in Hx. rewrite Hqu in Hx. clear -Hx DMa MBa DMn MBn. lia. }
    assert (SHA : SHADOW_OFF + pa = Sh ub + (pa - 512 * qu - 768)) by (rewrite ESHub, ESHua; clear; lia).
    assert (INRUN : Sh ua <= SHADOW_OFF + pa < Sh ua + L / 8) by (rewrite ESHua; clear -PA L8B; lia).
    split; [clear -INRUN SHB; lia|].
    split; [unfold shadow_addr; fold pa; apply OUTK; clear -INRUN SHB; unfold SHADOW_OFF in *; lia|].
    split.
    { intros j Hj. unfold word_byte.
      assert (WIN : Sh ua <= (SHADOW_OFF + pa) / 8 * 8 + j < Sh ua + L / 8).
      { pose proof (Z.div_mod (SHADOW_OFF + pa) 8 ltac:(clear; lia)) as DMs. pose proof (Z.mod_pos_bound (SHADOW_OFF + pa) 8 ltac:(clear; lia)) as MBs.
        rewrite ESHua, EL8 in INRUN |- *. unfold SHADOW_OFF in *.
        assert (Q1 : 64 * qu + 268431360 <= (2147450880 + pa) / 8) by (apply Z.div_le_lower_bound; [clear; lia | clear -INRUN; lia]).
        assert (Q2 : (2147450880 + pa) / 8 < 64 * qu + 268431360 + 64 * ql) by (apply Z.div_lt_upper_bound; [clear; lia | clear -INRUN; lia]).
        clear -Q1 Q2 Hj. lia. }
      split; [apply OUTK; clear -WIN SHB; unfold SHADOW_OFF in *; lia | apply RM3; right; exact WIN]. }
    destruct (Z_lt_dec (pa - 512 * qu - 768) (nv / 8)) as [LT|GE].
    - exists (Z_to_bv 8 0). split; [|left; reflexivity].
      unfold shadow_addr. fold pa. rewrite SHA. pose proof (VZ (pa - 512 * qu - 768) ltac:(clear -LT PA; lia)) as X. unfold v3 in X.
      rewrite view_in in X by (rewrite <- SHA; clear -INRUN SHB; lia).
      refine (rd_off_image _ _ _ _ X). rewrite <- SHA. clear -INRUN SHB. lia.
    - assert (EQ : pa - 512 * qu - 768 = nv / 8 /\ nv mod 8 <> 0) by (split; [clear -GE PA; lia | apply (proj2 (proj2 (proj2 PA))); clear -GE PA; lia]).
      destruct EQ as [EQ NZ]. exists (Z_to_bv 8 (nv mod 8)). split.
      + unfold shadow_addr. fold pa. rewrite SHA, EQ. pose proof (VP NZ) as X. unfold v3 in X.
        rewrite view_in in X by (rewrite <- EQ, <- SHA; clear -INRUN SHB; lia).
        refine (rd_off_image _ _ _ _ X). rewrite <- EQ, <- SHA. clear -INRUN SHB. lia.
      + right. split.
        * rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. rewrite (Z.mod_small (nv mod 8) 256) by (clear -MBn; lia).
          unfold ub. rewrite Hqu. replace (4096 * qu + 6144 + nv) with (nv + (512 * qu + 768) * 8) by (clear; lia). rewrite Z_mod_plus_full. reflexivity.
        * fold pa. unfold ub. rewrite Hqu. replace (4096 * qu + 6144 + nv) with (nv + (512 * qu + 768) * 8) by (clear; lia). rewrite Z.div_add by (clear; lia). clear -EQ. lia. }
  clear Hc.

  change (ax_setX (ax_setS A2 (S2F F KU)) ((UBs nx, SVar 12) :: ax_X (ax_setS A2 (S2F F KU))))
    with (mkAX (S2F F KU) ((UBs nx, SVar 12) :: ax_X F) (ax_base F)) in Hd.
  rewrite XFn, BFb in Hd. change (mkAX (S2F F KU) [(UBs nx, SVar 12)] base_sv) with (XF_of F KU nx) in Hd.
  pose proof (smatchA_entails segs (XF_of F KU nx) (L_malloc_ok AE_A W st) s9 rho3 tp _ ENT9 (proj1 Hd)) as Hsm4.
  set (rho4 := rho_sub rho3 s9) in Hsm4.
  assert (Hlow : forall k, (k < NF)%positive -> rw rho4 k = rw rhoE k).
  { intros k Hk. unfold rho4. cbn [rho_sub rw]. rewrite (wsub_get_id _ _ _ SID9 Hk). cbn [eval]. unfold rho3. cbn [rho_absorb rw]. reflexivity. }
  assert (E110 : bv_unsigned (rw rho4 V_RES) = ub). { unfold rho4. cbn [rho_sub rw]. rewrite G110. exact EUB3. }
  assert (Erm4 : rm rho4 = rm rho3) by exact (rm_rho_sub' rho3 s9).
  pose proof (rhoM_agree A rho) as (RMw & RMl & RMm).
  assert (LOWE : forall k, (k < NF)%positive -> rw rhoE k = rw rho0 k).
  { intros k Hk. rewrite <- (Hagw k) by (unfold GW, NF in *; clear -Hk; lia). rewrite <- (RMw k Hk). exact (HLw k). }

  assert (CLE : forall x, client_addrA CST As x <-> client_addrA CST A x).
  { intros x. unfold client_addrA, client_mut_addrA, aa_frames, frame_flag. rewrite Bl, Bfb, Bg. cbn [aa_live aa_fs_busy aa_geom bumpV]. split; intros X; exact X. }
  assert (CLE' : forall x, client_addrA CST A x -> client_addrA CST (secA As ua nv) x).
  { intros x Hx. apply (proj2 (CLE x)) in Hx. unfold client_addrA, client_mut_addrA, aa_frames, frame_flag in Hx |- *. cbn [aa_live aa_fs_busy aa_geom secA].
    destruct Hx as [[X|[X|[X|X]]]|X]; [left; left; exact X | left; right; left | left; right; right; left; exact X | left; right; right; right; exact X | right; exact X].
    destruct X as (b & n & Hbn & Hb0). exists b, n. split; [right; exact Hbn | exact Hb0]. }
  apply (LQPA_intro segs NF rho0 tp0 _ (L_malloc_ok AE_A W st) (JL_malloc_ok AInv CST XGL A Kc) rho4 tp _ KJ).
  - exact HPin.
  - split; [exact Hsm4 | exact HK].
  - split.
    + intros i Hi. rewrite (Hlow i Hi), (LOWE i Hi). reflexivity.
    + intros l. unfold rho4. cbn [rho_sub rl]. unfold rho3. cbn [rho_absorb rl]. rewrite (Erl l). symmetry. exact (HLl l).
  - intros _. unfold JL_malloc_ok. cbn [w_tr w_cfg cfg_model].
    exists (secA As ua nv), [], (aa_live A). cbn [app].
    assert (E12_0 : bv_unsigned (rw rho0 12%positive) = nv) by (rewrite <- (HLw 12%positive); reflexivity).
    split; [unfold AInv, AInvA in RB |- *; rewrite Erm4; exact RB|].
    split; [cbn [aa_live secA]; rewrite Bl, E110, E12_0; reflexivity|].
    split; [reflexivity|].
    split; [unfold aa_frames; cbn [aa_fs_busy secA]; rewrite Bfb; reflexivity|].
    split; [cbn [aa_V secA]; rewrite BV, E12_0; reflexivity|].
    split; [cbn [aa_Km secA]; rewrite BKm; reflexivity|]. split; [cbn [aa_Kf secA]; rewrite BKf; reflexivity|]. split; [cbn [aa_geom secA]; exact Bg|].
    split.
    {
      destruct HKEPT0 as [K01 K02]. destruct KP as [KP1 KP2]. rewrite Erm4. split.
      - intros x Bx Hcl.
        assert (EQ0 : rm rho (Z_to_bv 64 x) = rm rho0 (Z_to_bv 64 x)).
        { apply (K01 x Bx). destruct Hcl as [(X & _ & NE)|(X & _ & DEF)]; [left; exact (conj X (conj X NE)) | right; exact (conj X (conj X DEF))]. }
        assert (Hcl' : (client_addrA CST As x /\ client_addrA CST (secA As ua nv) x /\ ~ errno_addrA x)
                       \/ (client_shadowA CST XGL As x /\ client_shadowA CST XGL (secA As ua nv) x /\ rm rhoE (Z_to_bv 64 x) <> None)).
        { destruct Hcl as [(X & Y & NE)|(X & Y & DEF)].
          - left. split; [apply (proj2 (CLE x)); exact X | exact (conj Y NE)].
          - right. split; [|split; [exact Y | rewrite ErmF, EQ0; exact DEF]].
            destruct X as [(y & Y1 & Y2)|Y']; [left; exists y; split; [apply (proj2 (CLE y)); exact Y1 | exact Y2] | right; exact Y']. }
        rewrite (KP1 x Bx Hcl'). rewrite ErmF. exact EQ0.
      - intros xx jj Hx Hj Hdef. apply (KP2 xx jj); [| exact Hj |].
        + destruct Hx as [[X Y]|X]; [left; split; [apply (proj2 (CLE xx)); exact X | exact Y] | right; exact X].
        + rewrite ErmF. apply (K02 xx jj); [| exact Hj | exact Hdef].
          destruct Hx as [[X Y]|X]; [left; exact (conj X X) | right; exact X]. }
    split; [exact HK|].

    intros c0 Hc0 Hor Hfr. unfold class_fresh in Hfr |- *. cbn [aa_cls secA]. rewrite Bc. exact Hfr.
Qed.

Theorem sec_finish : ltac2:(tb__ "0|5|
S35S5cS15S15S4aQ40M0A1M1S15S5G1A1M2G2S85S0S61Vst;S5fA3S0S5S5bA1VW;S8S5bA1A3F_;S5eR9A1S12S0G1S14R9R1A2S14RaR1A2A3Fi;S12S0S5S4aQ8A1A1S1aRaR1A2S1aRbR1A2A3Fl;S60VCST;VXGL;RdRdS1bRbA1S1bRaA1A6S4cS4dSbS37S36ReA1A2A1S38ReA1A2SdS11S11A2M3S31G3R1S8eS3bVBX;S6cR10S49G0S14RdPcM4A2A2A2A1A1A1A3S8cR2ScS11S11S49G0RdA2S8fS49G0S14ReG4A2A2A1A4A2F_;Fbn;S87Vsegs;VJG;VBX;R10RfRdRcA5VF;RbR9R8A6S8aVsegs;S6fRfRbS65S5dVAInv;VCST;VXGL;VW;Vst;R11R10A8R9A6F_;F_;F_;F_;F_;F_;F_;F_;Fw;Ftp;Ftp0;FrhoE;Fa;Frho;Frho0;FKc;FA;").
Proof.
  intros A Kc rho0 rho a rhoE tp0 tp w. apply sec_finish_P. unfold Posts_malloc. right. left. reflexivity.
Qed.

Variable DF9 : axst.
Hypothesis CertF : ltac2:(tb__ "0|1|
S0S7Sa6SaaUfa0S8S11A1SadVnx;A1S6S57VDF9;S8S57A1M0A3S6S57VF;G0A3A6SaA3").
Theorem sec_g48_P : ltac2:(tb__ "0|6|
S85OF_;S35S5cS15S15S4aQ40M0A1M1S5G1A1M2S5SdS57S8bA2M3A1S31G3ScS57S8bS62S5dVW;Vst;A3S64VAInv;VCST;VXGL;R7R6A5A4R1A3S0S61Vst;S5fA3S0S5S5bA1VW;S8S5bA1A3F_;S90VW;Vst;A2S5eR9A1S89Vsegs;RcS88RaA1A3S12S0G1S14RaR1A2S14RbR1A2A3Fi;S12S0S5S4aQ8A1A1S1aRbR1A2S1aRcR1A2A3Fl;S60VCST;VXGL;ReReS1bRcA1S1bRbA1A6S4cS4dSbS37S36RfA1A2A1S38RfA1A2SdS11S11A2M4S31G4R1S8eS3bVBX;S6cR11S49G0S14RePcM5A2A2A2A1A1A1A3S8cR2ScS11S11S49G0ReA2S8fS49G0S14RfG5A2A2A1A4A2F_;Fbn;S15G2S86Vsegs;R14S87Vsegs;VJG;VBX;R13R12R10RfA5VDF9;R2R1A5S8aVsegs;S6fR11ReRdA5A4FtpX;FrhoX;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FPosts;Ftp0;Fa;Frho;Frho0;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho0 rho a tp0 Posts HPin HW HUS HKc Hokl HLw HLl HKEPT0 HL9 HDB rhoX tpX.
  pose proof (JG_okf nW st nx BX ok A Kc rho a Hokl) as Hokf. pose proof (JG_stable nW st tmax nx Hnx NXG BX A Kc rho a HUS HKc) as HST.
  apply (cfg_soundA segs 4000%nat [] (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3.GS nx) [DF9] [F] (JG BX A Kc rho a) ok _ tpX Hokf HST CertF); [|left; reflexivity].
  intros E rE HinE. destruct HinE as [<-|[]].
  eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw |].
  eapply triple_conseq; [intros w Hw; exact Hw | | apply triple_refl].
  intros w Hw. exact (sec_finish_P A Kc rho0 rho a rE tp0 tpX w Posts HPin HW HKc HLw HLl HKEPT0 HL9 HDB Hw).
Qed.
Theorem sec_g48 : ltac2:(tb__ "0|5|
S85OF_;S35S5cS15S15S4aQ40M0A1M1S5G1A1M2S0S61Vst;S5fA3S0S5S5bA1VW;S8S5bA1A3F_;S90VW;Vst;A2S5eR7A1S89Vsegs;RaS88R8A1A3S12S0G1S14R8R1A2S14R9R1A2A3Fi;S12S0S5S4aQ8A1A1S1aR9R1A2S1aRaR1A2A3Fl;S60VCST;VXGL;RcRcS1bRaA1S1bR9A1A6S4cS4dSbS37S36RdA1A2A1S38RdA1A2SdS11S11A2M3S31G3R1S8eS3bVBX;S6cRfS49G0S14RcPcM4A2A2A2A1A1A1A3S8cR2ScS11S11S49G0RcA2S8fS49G0S14RdG4A2A2A1A4A2F_;Fbn;S15G2S86Vsegs;R12S87Vsegs;VJG;VBX;R11R10ReRdA5VDF9;R2R1A5S8aVsegs;S6fRfRcS65S5dVAInv;VCST;VXGL;VW;Vst;R11R10A8A5A4FtpX;FrhoX;F_;F_;F_;F_;F_;F_;F_;F_;F_;Ftp0;Fa;Frho;Frho0;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho0 rho a tp0. apply sec_g48_P. unfold Posts_malloc. right. left. reflexivity.
Qed.
End FIN.

Lemma hpath_a : ltac2:(tb__ "0|6|
S35S35Fx;S35S5cS15S4aQ40M0A1M1S15S5G1A1S5S97A1S96S35S0S3cS39RaR1A1A1S39R1A1A3FX;S35S0S5S37A1S36RbR1A1A1S36R1A1A3FX;S35S0S11S3aRcR1A1A1S4eS3aR1A1M2Sa9A2A3FX;VJG;RcRbRaR9R8R7R6R5R4A9S6eS17S1eR8A1S6S17S21S98S19S9dA1S19S9eA1M3A3S8S17A1A3A3ReS6cRdS49G0S14RbPcA2A2A2A1S35S1S1S4cZ8M4Z20000M5A2S4cG5G5A2A2S1S4cS4eS50G4S4dSbS37S36ReA1A2A1A2G5A2G2A2S0G1S1dRaS28S99G3S20Z4000A1A3A2S4bG0S4fG2G4A2A2A3A2A2TAs;F_;F_;F_;F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FBX;").
Proof.
  intros BX A Kc rho a r tp tr md BXg BXs BXp HJ HF. apply Forall_inv in HF. cbn zeta.
  pose proof (JGs_rigidS nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (_ & _ & _ & _ & _ & _ & _ & E145 & E146 & E147 & _).
  destruct HJ as (_ & _ & HA & _). pose proof (AInvA_pab _ _ _ _ HA) as X. rewrite BXg, BXs, BXp in X. cbn [aa_geom aa_sec aa_ptr_committed bumpV] in X. cbn zeta in X.
  destruct X as (P1 & P2 & P3 & P4 & P5 & P6 & _).
  rewrite BXp. cbn [aa_ptr_committed bumpV].
  set (G := aa_geom A) in *. set (c := aa_ptr_committed A) in *.
  pose proof (topG_range G) as TG. pose proof (Zle_0_nat (length (aa_sec A))) as NN.
  assert (EDV : (c + kPtrArrayCommit) / 8 = c / 8 + 16384) by (change kPtrArrayCommit with (16384 * 8); apply Z.div_add; lia).
  unfold kPtrArrayReserve, kPtrArrayCommit, PG, IMG_HI in *.
  assert (C17 : c mod 2 ^ 17 = 0).
  { pose proof (Z.mod_add c 1 (2 ^ 17) ltac:(lia)) as MA. rewrite <- MA. rewrite <- P6. f_equal. }
  pose proof (Z.div_mod c (2 ^ 17) ltac:(lia)) as X. rewrite C17, Z.add_0_r in X.
  pose proof (Z.div_mod c 8 ltac:(lia)) as X8.
  assert (C8 : c mod 8 = 0) by (rewrite X; replace (2 ^ 17 * (c / 2 ^ 17)) with ((2 ^ 14 * (c / 2 ^ 17)) * 8) by lia; apply Z_mod_mult).
  rewrite C8, Z.add_0_r in X8.
  cbn [holds eval] in HF. rewrite E147, E146 in HF. fold c in HF.
  assert (C0 : 0 <= c).
  { destruct (Z_lt_le_dec c 0) as [Hneg|]; [exfalso | assumption].
    assert (Ec : c = - 2 ^ 17) by (clear -X Hneg P5 NN; lia).
    assert (En : Z.of_nat (length (aa_sec A)) = 0) by (clear -Ec P5 NN; lia).
    rewrite En, Ec in HF. vm_compute in HF. discriminate HF. }
  pose proof (Z.div_pos c 8 ltac:(lia) ltac:(lia)) as DP. pose proof (Z.div_le_mono c (2 ^ 23) 8 ltac:(clear -P5; lia) ltac:(clear -P5; lia)) as DM. cbn in DM.
  rewrite bt_eq_lit in HF by (clear -DP DM NN P5; lia). apply Z.eqb_eq in HF.
  assert (HcN : 8 * Z.of_nat (length (aa_sec A)) = c) by (rewrite HF; clear -X8; lia).
  split; [lia|]. split; [clear -HcN; lia|].
  apply bv_eq. cbn [eval]. rewrite E146. fold c. rewrite add_val, !u64_lit by (clear -DP DM; lia). rewrite Z.mod_small by (clear -DP DM; lia).
  rewrite EDV. reflexivity.
Qed.

Lemma hpath_b : ltac2:(tb__ "0|5|
S35S35Fx;S35S5cS15S4aQ40M0A1M1S15S5G1A1S5S97A1S96S35S0S3cS39RaR1A1A1S39R1A1A3FX;S35S0S5S37A1S36RbR1A1A1S36R1A1A3FX;S35S0S11S3aRcR1A1A1S3aR1A1M2A3FX;VJG;RcRbRaR9R8R7R6R5R4A9S6eS17S1eR8A1S6S17S22S21S98S19S9dA1S19S9eA1M3A3A1S8S17A1A3A3ReS6cRdS49G0S14RbPcA2A2A2A1S35S1S1S4cZ8M4G4A2S4cG4Z20000A2A2S1S4cS4eS50G4S4dSbS37S36ReA1A2A1A2G4A2G2A2S0G1S1dRaG3A2S4bG0S4fG2G4A2A2A3A2A2TAs;F_;F_;F_;F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FBX;").
Proof.
  intros BX A Kc rho a r tp tr md BXg BXs BXp HJ HF. apply Forall_inv in HF. cbn zeta.
  pose proof (JGs_rigidS nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (_ & _ & _ & _ & _ & _ & _ & E145 & E146 & E147 & _).
  pose proof (site_b nW st tmax nx Hnx Pret_ms Pret_ms Pret_ms Pret_ms eq_refl eq_refl BX A Kc rho a r tp tr md BXg BXs BXp HJ HF) as (_ & B1 & B2 & _). cbn zeta in B1, B2.
  rewrite BXp. cbn [aa_ptr_committed bumpV].
  split; [lia|]. split; [clear -B2; lia|]. cbn [eval]. exact E146.
Qed.
End SEC7.
End SpineMallocSec7.

(* [comment removed for export] *)
Module CSecLinks.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Logic"; "and"; "eq"; "not"; "False"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rm"; "rl"; "rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "div"; "pow"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "@Corelib.Init.Datatypes"; "None"; "list"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "Sh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "ageom"; "AA"; "aa_depot"; "aa_geom"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c5.SpineCallocSec4"; "slink4"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c5.CDepotCallS"; "dlink"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.CSecOKInv"; "pendS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "mem_keptA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "dfp_static"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bx.SpineCallocSec2"; "IMG_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineCallocSec3"; "slink"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "secmapsize"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundR SymSummary SymFrame Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import BackingAlgebra LedgerA Virt StepA SoundA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SMGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineCallocS4 RebuildM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require al.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bx.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require q0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CDepotCall.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineCallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.RebuildN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.CSecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.CSecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.SegD_cost OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b3.CInvEnsure OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.LiveGeom OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bx.SpineCallocSec2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineCallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c5.SpineCallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.InvD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CDepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c5.CDepotCallS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.CRebuildS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section Links.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTS : ltac2:(tb__ "0|0|
S0SaVCST;R1A2SaS22R2A2S5F_;F_;Fa;").
Hypothesis HCSTD : ltac2:(tb__ "0|0|
S0SaVCST;R1A2S4S21R2A1A1F_;Fa;").

Lemma slink4_refl : ltac2:(tb__ "0|2|
S16S0S0S6S0S2SbS15R4A1M0R1A2ScR1SdG0SeR3Z8A2A2A2A2S4S3S14S10Q8A1M1A1S7R3S11Q40R2A2A2S12G1A1A3A1F_;Fz;S1aR5R4R3R2R2A5F_;Fr;FL;Fua;FG;").
Proof. intros G ua L r RD. split; [reflexivity|]. split; [reflexivity|]. split; [intros a; left; reflexivity | exact RD]. Qed.

Theorem links_kept : ltac2:(tb__ "0|4|
S17S6S13S10Q40M0A1M1A1S1bS0S0S6S6S6S6S20S1cRaR9R8R7A5S2SbZfc01R7A2ScR7SfZ2Z27A2A2A2S19RcA1S16S24R9A1S0S1eReR9R1RbA4S23RaR2R9R8A4S1aR4RbR3R9R8A5S1dS18R11A1R9R8A3S2S1fVCST;VXGL;R12R12S7RcA1S7R9A1A6S2S0S2SbS15ReA1M2R1A2ScR1SdG2SeR6Z8A2A2A2A2S4S3S14S10Q8A1M3A1S7RbS11G0R2A2A2S12G3A1A3A1F_;Fz;S2S1S3G1S9RaR1A2S9RdR1A2A3Fi;S1S3S13G3A1S8RaR1A2S8RdR1A2A3Fl;A2A2A2F_;F_;F_;F_;TL;TG;F_;F_;Frho3;Frho2;Frho1;Frho0;Fua;Fnv;Fmd;Ftp;Fr;FAs;").
Proof.
  intros A r tp md nv ua rho0 rho1 rho2 rho3 HA Hnv. cbn zeta. intros HPD (W1 & L1 & M1 & D1) (W2 & L2 & M2 & D2) (W3 & L3 & M3).
  pose proof HA as (HG & HR & HF & HRest & HM & HI3 & HB).
  destruct HRest as (Hsep & Hlive & HPR & HSR & HQR & HDW & HIA & HTH & HMI).
  set (G := aa_geom A) in *. set (T := ag_thread G) in *. set (L := secmapsize nv) in *.
  pose proof (geom_numsS _ HG) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & ACV). fold T in G4, G5, G10, G13, G14.
  pose proof (geom_bands _ HG) as (FB & TB & CB & DB & TI & CI & DI). fold G T in TB, TI. fold G in FB, CB, DB, CI, DI.
  unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END, IMG_LO, IMG_HI in FB, TB, CB, DB, TI, CI, DI. rewrite FS_total_val in FB.
  destruct HPD as (PM & PAL & PL0 & PDI & ST & SC & SD & SF & SS & SP & SX & SDB). fold G L in PM, PL0, PDI, ST, SC, SD, SF, SS, SP, SX, SDB. fold T in ST.
  pose proof (secmapsize_bounds nv ltac:(clear -Hnv; lia)) as [SMB SMM]. fold L in SMB, SMM. unfold PG in SMM, PAL.
  pose proof (dyn_in_big _ _ _ PDI ltac:(clear -SMB; lia)) as UI. destruct PDI as (_ & _ & PDT & _ & PDB).
  pose proof (pab_facts _ A HSR) as (P1 & P2 & P3 & P4 & P5). fold G in P1, P2, P3.
  assert (U8 : ua mod 8 = 0).
  { pose proof (Z.div_mod ua 4096 ltac:(clear; lia)) as X. rewrite PAL, Z.add_0_r in X. rewrite X. replace (4096 * (ua / 4096)) with ((512 * (ua / 4096)) * 8) by (clear; lia). apply Z_mod_mult. }
  assert (L8 : L mod 8 = 0).
  { pose proof (Z.div_mod L 4096 ltac:(clear; lia)) as X. rewrite SMM, Z.add_0_r in X. rewrite X. replace (4096 * (L / 4096)) with ((512 * (L / 4096)) * 8) by (clear; lia). apply Z_mod_mult. }
  assert (UT : ua + L <= 140737479966720) by (clear -PDT ACV; lia).
  unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in PDB.
  pose proof (live_foot_new ua L U8 L8 PL0 UI UT ltac:(unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END; exact PDB) A _ HG Hsep HI3 HPR HSR SS SX) as LFN.
  unfold sepZ in SF, ST. cbn [fst snd] in SF, ST. rewrite FS_total_val in SF.
  assert (ESHL : Sh (ua + L) = Sh ua + L / 8).
  { unfold Sh. pose proof (Z.div_mod L 8 ltac:(clear; lia)) as DL. rewrite L8, Z.add_0_r in DL. rewrite DL at 1. rewrite Z.mul_comm, Z.div_add by (clear; lia). clear. lia. }

  assert (RUNB : forall z, Sh ua <= z < Sh ua + L / 8 -> 2147446784 <= z < 17594333495296).
  { intros z Hz. rewrite <- ESHL in Hz.
    pose proof (sh_run_band2 ua (ua + L) z ltac:(unfold IMG_HI in UI; clear -UI; lia) ltac:(clear -UT PL0; lia) Hz) as BY.
    unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in BY. exact BY. }
  idtac "lk:0".

  assert (NOC : forall a, client_addrA CST A a -> ~ rtint G a /\ ~ (ua <= a < ua + L)).
  { intros a Hcl.
    destruct (client_addr_cases CST A a _ HF Hcl) as [S|[Lv|[FR|[C|FL]]]].
    - fold G in S. split; [|clear -S PDT; lia].
      intros [X|X]; [unfold SEC_INST in X; clear -X S ACV; lia | clear -X S P2; lia].
    - destruct Lv as (b & n & Hbn & Hx). destruct (Hsep b n Hbn) as (S1 & S2 & _). unfold IMG_HI in S2.
      pose proof (rz_bound n) as RZ.
      pose proof (LFN b n a Hbn ltac:(left; clear -Hx RZ; lia)) as NZ.
      pose proof (live_foot _ A HG Hsep HI3 HPR HSR b n a Hbn ltac:(left; clear -Hx RZ; lia)) as (X1 & X2 & _).
      pose proof (live_foot_pab _ A HG Hsep HI3 HPR HSR b n a Hbn ltac:(left; clear -Hx RZ; lia)) as X3. fold G T in X2, X3.
      split; [|intros X; apply NZ; left; exact X].
      intros [X|X]; [unfold SEC_INST, IMG_HI in *; clear -X X1; lia | exact (X3 X)].
    - destruct FR as (c & p & Hcp & Hp & _ & Hx). pose proof (fs_geom_nums G c p HG Hcp Hp) as M. cbn zeta in M.
      rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M. unfold IMG_HI in M. fold G in Hx.
      destruct HI3 as ((_ & _ & _ & _ & _ & PF & _) & _). fold G in PF. rewrite FS_total_val in PF. unfold kPtrArrayReserve in *.
      split; [|clear -Hx M SF; lia].
      intros [X|X]; [unfold SEC_INST in X; clear -X Hx M; lia | unfold kPtrArrayReserve in X; clear -X Hx M PF; lia].
    - destruct (HCST _ C) as [X0 _]. unfold IMG_LO, IMG_HI in X0.
      split; [|unfold IMG_HI in UI; clear -X0 UI; lia].
      intros [X|X].
      + apply (HCSTS a C). unfold IMG_S, in_rangesZ. unfold SEC_INST in *.
        exists 0xeddd8, (0xee044 - 0xeddd8). split; [left; reflexivity | clear -X; lia].
      + unfold IMG_HI in P1. clear -X X0 P1. lia.
    - destruct FL as (c & p & Hcp & Hp & _ & Ea). pose proof (fs_geom_nums G c p HG Hcp Hp) as M. cbn zeta in M.
      rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M. fold G in Ea. unfold fs_flags in M, Ea. rewrite FS_kFlagsOffset_val in M, Ea. unfold IMG_HI in M.
      destruct HI3 as ((_ & _ & _ & _ & _ & PF & _) & _). fold G in PF. rewrite FS_total_val in PF. unfold kPtrArrayReserve in *.
      split; [|clear -M Ea SF; lia].
      intros [X|X]; [unfold SEC_INST in X; clear -X M Ea; lia | unfold kPtrArrayReserve in X; clear -X M Ea PF; lia]. }
  idtac "lk:1".

  destruct (AInvA_X A r tp md HA) as (HXd & _ & _).
  assert (NOD : forall a, KEEPD CST XGL A a -> ~ DFP (aa_depot A) a).
  { intros a HK. exact (keep_not_DFP UStopLe CST XGL HCST HXGL HCSTD A r tp md a HXd HK). }
  assert (BAND : forall a, 2147446784 <= a < 17594333495296 -> ~ DFP (aa_depot A) a).
  { intros a HB' HD.
    assert (HSEC : forall i ch, nth_error (aa_sec A) i = Some ch -> dyn_in (topG (aa_geom A)) (sc_map_beg ch) (sc_map_size ch)).
    { intros i ch Hi. destruct HSR as [X1 _]. destruct (X1 i ch Hi) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & D10 & _). exact D10. }
    assert (HPAB : dyn_ok (topG (aa_geom A)) (ag_pab (aa_geom A)) kPtrArrayReserve) by (destruct HSR as (_ & _ & _ & _ & X4' & _); exact X4').
    pose proof (zones_not_DFPw A a HG HI3 HSEC HPAB) as ZN. cbn zeta in ZN.
    destruct (DFP_split _ _ HD) as [Hs|Hws]; [pose proof (dstat_range a Hs) as DR; unfold MAP1, MAP1N, STORE in DR; clear -HB' DR; lia | ].
    apply ZN; [do 8 right; left; unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END; exact HB' | exact Hws]. }

  assert (BRT : forall a, 2147446784 <= a < 17594333495296 -> ~ rtint G a).
  { intros a HB' [X|X]; [unfold SEC_INST in X; clear -X HB'; lia |].
    unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in P3. clear -X HB' P3. lia. }
  idtac "lk:2".

  assert (NOS : forall a, client_shadowA CST XGL A a -> 2147446784 <= a < 17594333495296 /\ ~ (Sh ua <= a < Sh ua + L / 8)).
  { intros a C1. pose proof (client_shadow_bounds CST XGL HCST HXGL A a _ HG HF Hsep C1) as B0. unfold SHADOW_OFF, HIGH_SHADOW_END in B0.
    split; [clear -B0; lia|]. intros X.
    assert (XIN : forall x, a = Sh x -> 0 <= x -> ua <= x < ua + L).
    { intros x -> Hx0. unfold Sh in X. pose proof (Z.div_mod L 8 ltac:(clear; lia)) as DL. rewrite L8, Z.add_0_r in DL.
      pose proof (Z.div_mod ua 8 ltac:(clear; lia)) as DU. rewrite U8, Z.add_0_r in DU.
      pose proof (Z.div_mod x 8 ltac:(clear; lia)) as DX. pose proof (Z.mod_pos_bound x 8 ltac:(clear; lia)) as MX. clear -X DL DU DX MX. lia. }
    destruct C1 as [(y & Cy & Ey)|(y & Gy & Ey)].
    - destruct (client_addr_bounds CST HCST A y _ HG HF Hsep Cy) as [By _]. pose proof (XIN y Ey ltac:(clear -By; lia)) as YIN.
      exact (proj2 (NOC y Cy) YIN).
    - destruct (HXGL y Gy) as [Y1 Y2]. pose proof (XIN y Ey ltac:(clear -Y1; unfold IMG_LO in *; lia)) as YIN. clear -YIN Y2 UI. lia. }
  idtac "lk:3".

  assert (DEFB : forall z, 2147446784 <= z < 17594333495296 -> rm rho0 (Z_to_bv 64 z) <> None -> rm rho3 (Z_to_bv 64 z) <> None).
  { intros z Hz Hd.
    assert (EZ : bv_unsigned (Z_to_bv 64 z) = z) by (rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with 18446744073709551616; apply Z.mod_small; clear -Hz; lia).
    assert (H1 : rm rho1 (Z_to_bv 64 z) <> None).
    { destruct (M1 (Z_to_bv 64 z)) as [E|[(N & _)|(_ & N)]]; [rewrite E; exact Hd | exact (False_ind _ (Hd N)) | exact N]. }
    assert (H2 : rm rho2 (Z_to_bv 64 z) <> None).
    { destruct (M2 (Z_to_bv 64 z)) as [E|[(N & _)|[(_ & N)|N]]]; [rewrite E; exact H1 | exact (False_ind _ (H1 N)) | exact N |].
      rewrite EZ in N. exact (False_ind _ (BRT z Hz N)). }
    rewrite (M3 (Z_to_bv 64 z)); [exact H2|]. rewrite EZ. exact (BAND z Hz). }
  idtac "lk:4".
  split; [|split; [|split]].
  - split.
    + intros a Ba Hcl.
      assert (EZ : bv_unsigned (Z_to_bv 64 a) = a) by (rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with 18446744073709551616; apply Z.mod_small; clear -Ba; lia).
      assert (KD : KEEPD CST XGL A a) by (destruct Hcl as [(C1 & _)|(C1 & _)]; [left; exact C1 | right; exact C1]).
      rewrite (M3 (Z_to_bv 64 a)) by (rewrite EZ; exact (NOD a KD)).
      destruct Hcl as [(C1 & _ & NE)|(C1 & _ & Hd)].
      * destruct (NOC a C1) as (N1 & N2).
        destruct (client_addr_bounds CST HCST A a _ HG HF Hsep C1) as [_ NB].
        assert (NRUN : ~ (Sh ua <= a < Sh ua + L / 8)) by (intros X; pose proof (RUNB a X) as Y; clear -Y NB; lia).
        assert (E1 : rm rho1 (Z_to_bv 64 a) = rm rho0 (Z_to_bv 64 a)).
        { destruct (M1 (Z_to_bv 64 a)) as [E|[(_ & _ & N)|(N & _)]]; [exact E | | ]; rewrite EZ in N; exfalso;
            [unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in N; clear -N NB; lia | exact (NRUN N)]. }
        rewrite <- E1.
        destruct (M2 (Z_to_bv 64 a)) as [E|[(_ & _ & N)|[(N & _)|N]]]; [exact E | | | ]; rewrite EZ in N; exfalso;
          [unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in N; clear -N NB; lia | exact (NRUN N) | exact (N1 N)].
      * destruct (NOS a C1) as (B0 & NRUN).
        assert (E1 : rm rho1 (Z_to_bv 64 a) = rm rho0 (Z_to_bv 64 a)).
        { destruct (M1 (Z_to_bv 64 a)) as [E|[(N & _)|(N & _)]]; [exact E | exact (False_ind _ (Hd N)) | rewrite EZ in N; exact (False_ind _ (NRUN N))]. }
        rewrite <- E1. rewrite <- E1 in Hd.
        destruct (M2 (Z_to_bv 64 a)) as [E|[(N & _)|[(N & _)|N]]]; [exact E | exact (False_ind _ (Hd N)) | rewrite EZ in N; exact (False_ind _ (NRUN N)) |].
        rewrite EZ in N. exact (False_ind _ (BRT a B0 N)).
    + intros x j Hx Hj Hdef.
      assert (Bx : SHADOW_OFF <= Sh x < HIGH_SHADOW_END).
      { destruct Hx as [[C1 C2]|GX].
        - destruct (client_addr_bounds CST HCST A x _ HG HF Hsep C1) as [B _]. unfold Sh, SHADOW_OFF, HIGH_SHADOW_END. clear -B. lia.
        - destruct (HXGL x GX) as [X0 X1]. unfold IMG_LO, IMG_HI, Sh, SHADOW_OFF, HIGH_SHADOW_END in *. clear -X0 X1. lia. }
      unfold SHADOW_OFF, HIGH_SHADOW_END in Bx.
      destruct (word_byte_range (Sh x) j ltac:(clear -Bx; lia) Hj) as (W1' & W2' & W3').
      unfold word_byte in *. apply DEFB; [|exact Hdef]. clear -W3' Bx Hj. lia.
  - intros z Hz. pose proof (RUNB z Hz) as Bz.
    assert (EZ : bv_unsigned (Z_to_bv 64 z) = z) by (rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with 18446744073709551616; apply Z.mod_small; clear -Bz; lia).
    rewrite (M3 (Z_to_bv 64 z)); [exact (D2 z Hz)|]. rewrite EZ. exact (BAND z Bz).
  - intros i. rewrite W3, W2. apply W1.
  - intros l. rewrite L3, L2. apply L1.
Qed.
End Links.
End CSecLinks.

(* [comment removed for export] *)
Module SpineCallocSec5.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_setS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@Corelib.Init.Datatypes"; "list"; "bool"; "cons"; "nil"; "true"; "prod"; "Some"; "option"; "pair"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sprop"; "ss_next"; "sv"; "holds"; "swf"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bd.CertCallocSU"; "F_g4"; "DPENT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "@stdpp.bitvector.definitions"; "bv"; "@Corelib.Lists.ListDef"; "Forall"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSS"; "nxS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineCallocSec3"; "JGs"; "@Stdlib.PArith.BinPos.Pos"; "leb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA EntailA CFGA GlueA GlueA2 SummaryA SysCallA MmapA MmapFixedA LedgerA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
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
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.SpineCallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineCallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.SpineCallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineCallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.RebuildN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.MmapSymA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.CertCallocSN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineCallocSec OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bx.SpineCallocSec2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.SegD_cost OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.LedgerLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.InvD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.DepotK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.CSecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SecReveal OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvReveal OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineCallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.EnsureMapA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CDepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.CSecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SecLog2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b3.CInvEnsure OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bd.CertCallocSU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c5.SpineCallocSec4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section SEC5.
Variable nW : nat. Variable st : ustop. Variable tmax : Z. Variable hi : bool.
Let W : list ulink := Wcan nW.
Let segs : list Segment := segsA.
Variable nx : positive.
Hypothesis Hnx : ltac2:(tb__ "0|0|
S0S15S21VW;Vst;Vtmax;A3Vnx;A3").
Hypothesis NXG : ltac2:(tb__ "0|0|
S0S6S25S22Vnx;A2S9A3").
Let GS : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineCallocSec3.GS nx.
Let JG (BX : AA -> AA) : AA -> KcA -> valuation -> word -> jpredA := ltac2:(tb__ "0|0|
S24VnW;Vst;Vnx;VBX;A4").

Lemma F_g4_hold : ltac2:(tb__ "0|1|
S4S4F_;S4S19SeS1aQ40A1M0SeS5G0A1S5S1dA1S1cVJG;R9R8R7R6R5R4R3R2R1A9S1bSfS12R5A1S17Vnx;A1A3F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;FBX;").
Proof.
  intros BX A Kc rho a r tp tr md HJ.
  pose proof (JGs_rigidS nW st tmax nx Hnx BX A Kc rho a r tp tr md HJ) as (E12 & Enx & ENS & _).
  destruct HJ as (_ & _ & _ & HP & _ & _ & _ & Hnv & _). cbn zeta in Hnv.
  set (nv := bv_unsigned (rw rho 12%positive)) in *.
  destruct HP as (_ & _ & _ & (D1 & D2 & D3 & _) & _). pose proof (topG_range (aa_geom A)) as TG.
  pose proof (secmapsize_bounds nv ltac:(lia)) as (MB1 & MB2).
  assert (NSV : secneeded nv = (nv + 8 - 1) / 8 * 8 + 4096) by reflexivity.
  pose proof (Z.div_mod (nv + 8 - 1) 8 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound (nv + 8 - 1) 8 ltac:(lia)) as MBd.
  pose proof (urange a) as Ra.
  unfold F_g4. apply Forall_cons; [|apply Forall_nil]. cbn [holds eval branch_taken]. intros H. unfold bv_ltu in H. apply Z.ltb_lt in H.
  rewrite !add_val, ENS, Enx, E12, !u64_lit in H by lia. fold nv in H.
  rewrite (Z.mod_small (bv_unsigned a + 4096)) in H by lia. rewrite (Z.mod_small (bv_unsigned a + 6144)) in H by lia.
  rewrite !Z.mod_small in H by lia. lia.
Qed.

Section G41.
Variables (T4 U4 X5 : axst).
Hypothesis WU4 : ltac2:(tb__ "0|0|
S0S6S13S1VU4;A1A1S9A3").
Hypothesis DU4 : ltac2:(tb__ "0|4|
S0ScSaS5SaS11S11A2M0A1M1S5SfA1M2A2M3A1S1fS1VT4;A1S1VU4;A1A2SbG3SdG1G2S8G0A1S17Vnx;A1A4A2A3").
Hypothesis NXU4 : ltac2:(tb__ "0|0|
S0S15S10S1VU4;A1A1S10S1VT4;A1A1A3").
Hypothesis HU4 : ltac2:(tb__ "0|0|
S0S2S3VT4;S1VU4;A1A2VU4;A3").
Hypothesis Cert5 : ltac2:(tb__ "0|1|
S0S6S20S23Ufa0S7S14S18S8S14A1A3VGS;S7S2VU4;S8S2A1M0A3S7S2VX5;G0A3A6S9A3").

Lemma RSU4 : ltac2:(tb__ "0|1|
S4S4F_;S4S19SeS1aQ40A1M0SeS5G0A1S1eS16Vsegs;VJG;R8R7R6R5R4A5VT4;R3R2R1A6S16Vsegs;VJG;R9R8R7R6R5A5VU4;R4R3R2A6F_;Fw;Ftp;FrhoX;Fa;Frho;FKc;FA;FBX;").
Proof.
  intros BX A Kc rho a rhoX tp w Hw. destruct w as [tr [ms md]]. rewrite <- HU4.
  eapply SPA_restate; [exact WU4 | exact DU4 | exact NXU4 | constructor | | exact Hw].
  exact (F_g4_hold BX A Kc rho a rhoX tp tr md (proj2 Hw)).
Qed.
End G41.
End SEC5.
End SpineCallocSec5.

