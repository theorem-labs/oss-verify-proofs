(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k8 k2.
From Stdlib Require FunctionalExtensionality.

(* [comment removed for export] *)
Module SpineMallocSecOK0S.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSecI"; "st0"; "W0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "liftKA"; "SPA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "AE_A"; "JL_malloc_ok"; "L_malloc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@Corelib.Init.Datatypes"; "list"; "prod"; "false"; "pair"; "true"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@Corelib.Init.Logic"; "False"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.CertMallocSS"; "ES1g"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "secmapsize"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3"; "JGsC"; "clsP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1"; "E_s1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.IfaceS"; "alloc_roomA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM"; "IMG_M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dfp_static"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1"; "JG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocSec2"; "IMG_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jm.SpineMallocSec3I"; "nx0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jm.SpineMallocSec3IL"; "nx0"; "@Stdlib.Lists.List"; "In"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.RebuildN.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import MmapSymA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require id.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocSec SpineMallocSec2 SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ii.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jl.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require js.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jm.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocSec4I.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jz.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jw.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocSec4IL.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.CertMallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.id.CertMallocSN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocSec OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocSec2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.InvD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.SecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.SecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SecRoom OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineMallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jn.DepotCallS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jq.SecLinks OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.js.SpineMallocSecOK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSecI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jm.SpineMallocSec3I OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocSec4I OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jz.SpineMallocSec5I OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jw.SpineMallocSec5J OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k8.SpineMallocSec6J OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jm.SpineMallocSec3IL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocSec4IL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jz.SpineMallocSec5IL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k4.SpineMallocSec5JL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k8.SpineMallocSec6JL.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require IfaceS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ji.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jo.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.IfaceS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ji.SpineMallocSec2S OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jo.SpineMallocSecOKP.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section OK0.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTM : ltac2:(tb__ "0|0|
S16SeVCST;R1A2SeS27R2A2S1eF_;F_;Fa;").
Hypothesis HCSTS : ltac2:(tb__ "0|0|
S16SeVCST;R1A2SeS2aR2A2S1eF_;F_;Fa;").
Hypothesis HCSTD : ltac2:(tb__ "0|0|
S16SeVCST;R1A2S1fS28R2A1A1F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Variable PF : ltac2:(tb__ "0|0|
S1S9S11S12S1aS1cA2A1F_;F_;").
Hypothesis HPF : ltac2:(tb__ "0|0|
S1S9S2dS12S1aS1cA2S14S1aS1cSdSbS3S2A3ScS26S0A1VCST;VXGL;R2R1A5A4VPF;R2R1A2A3FKc;FA;").

Theorem sec_ok_0h_S : ltac2:(tb__ "0|2|
S18OF_;S1S9S4S10Q40M0A1M1S11G1A1SaR4A1S8S0R7S6R5A1A3S1dS0R8S6R6A1A3S23S15SfG0R5A2S21SfG0S5R6PcA2A2A1A3S4S17S0RbS7S0S22U0S2S2bS1R1LX;RaR9R8R7A8S20S3S2Z2A3R1R6A5S1bS0S19R8R6VPF;RaR9A2A5A4FrhoX;F_;F_;F_;F_;Ftp;Fa;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho a tp HKc Hokl Hokpl HC rhoX.
  exact (sec_ok_chain_P 0%nat st0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jm.SpineMallocSec3I.nx0 true CST XGL HCST HXGL HCSTS HCSTD PF (ES1g W0 st0 2)
           OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jm.SpineMallocSec3I.D2c SpineMallocSec4I.T4ac SpineMallocSec4I.T4bc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jz.SpineMallocSec5I.C5ac OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jz.SpineMallocSec5I.C5bc
           sec_g12_0h sec_g3_0h sec_g41_0ha sec_g41_0hb (fun ok' A' Kc' rho0' rho' a' tp0' G2' => sec_tail_0ha_P CST XGL HCST HXGL HCSTM HCSTS ok' A' Kc' rho0' rho' a' tp0' G2' (PF A' Kc') (HPF A' Kc')) (fun ok' A' Kc' rho0' rho' a' tp0' G2' => sec_tail_0hb_P CST XGL HCST HXGL HCSTM HCSTS ok' A' Kc' rho0' rho' a' tp0' G2' (PF A' Kc') (HPF A' Kc'))
           ok A Kc rho a tp ltac:(intros E; discriminate E) (stopJ_stable_le _) HKc Hokl Hokpl HC rhoX).
Qed.

Theorem sec_ok_0l_S : ltac2:(tb__ "0|2|
S18OF_;S1S9S4S10Q40M0A1M1S11G1A1SaR4A1S8S0R7S6R5A1A3S1dS0R8S6R6A1A3S23S13SfG0R5A2S21SfG0S5R6PcA2A2A1A3S4S17S0RbS7S0S22U0S2S2cS1R1LX;RaR9R8R7A8S20S3S2Z2A3R1R6A5S1bS0S19R8R6VPF;RaR9A2A5A4FrhoX;F_;F_;F_;F_;Ftp;Fa;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho a tp HKc Hokl Hokpl HC rhoX.
  exact (sec_ok_chain_P 0%nat st0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jm.SpineMallocSec3IL.nx0 false CST XGL HCST HXGL HCSTS HCSTD PF (ES1g W0 st0 2)
           OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jm.SpineMallocSec3IL.D2c SpineMallocSec4IL.T4ac SpineMallocSec4IL.T4bc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jz.SpineMallocSec5IL.C5ac OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jz.SpineMallocSec5IL.C5bc
           sec_g12_0l sec_g3_0l sec_g41_0la sec_g41_0lb (fun ok' A' Kc' rho0' rho' a' tp0' G2' => sec_tail_0la_P CST XGL HCST HXGL HCSTM HCSTS ok' A' Kc' rho0' rho' a' tp0' G2' (PF A' Kc') (HPF A' Kc')) (fun ok' A' Kc' rho0' rho' a' tp0' G2' => sec_tail_0lb_P CST XGL HCST HXGL HCSTM HCSTS ok' A' Kc' rho0' rho' a' tp0' G2' (PF A' Kc') (HPF A' Kc'))
           ok A Kc rho a tp ltac:(intros E; discriminate E) (stopJ_stable_le _) HKc Hokl Hokpl HC rhoX).
Qed.

Theorem malloc_sec_ok_0_S : ltac2:(tb__ "0|1|
S18OF_;S1S9S4S11S10Q40M0A1A1SaR3A1S8Vsegs;R6S6R4A1A3S1dVsegs;R7S6R5A1A3S25R7SfG0S5R5PcA2A2A2S4S17Vsegs;RaS7Vsegs;S29S3S2R9R8R7A5S24S3S2Z2Z8A4R1R6A5S1bVsegs;S19R7R6VPF;R9R8A2A5A4FrhoE;F_;F_;F_;F_;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp HKc Hokl Hokpl HROOM rhoE.
  apply (sec_spine_S 0%nat st0 2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSecI.SWa_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSecI.SDa_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSecI.SWb_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSecI.SFB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSecI.CertS1_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSecI.WC1_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSecI.DC1_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSecI.NXC1_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSecI.IC1_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSecI.R17_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSecI.R11_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSecI.R10_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSecI.R12_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSecI.R13_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSecI.R14_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSecI.R15_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSecI.NX1_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSecI.XC1_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSecI.SK1_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSecI.FC1_0 ok A Kc
           (fun a => OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3.JGsC 0%nat st0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jm.SpineMallocSec3I.nx0 (fun X : AA => X) A Kc rho a) rho tp _ ltac:(intros E; discriminate E) (stopJ_stable_le _) HKc Hokl Hokpl HROOM).
  - intros rhoX tr ms md a Hsp HJG Hpl. pose proof OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSecI.NX1_0 as NX1'. unfold W0, st0 in NX1'. unfold W0, st0 in *. rewrite NX1'.
    exact (grant_Jo 0%nat st0 2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jm.SpineMallocSec3I.nx0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jm.SpineMallocSec3I.Hnx_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jm.SpineMallocSec3I.NXG_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSecI.R11_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSecI.FC1_0 A Kc rho rhoX tp tr ms md a (stopJ_stable_le _) HKc Hsp HJG Hpl).
  - intros rhoX a. unfold W0, st0 in *. rewrite OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jm.SpineMallocSec3I.Hnx_0.
    apply (cls_split 0%nat st0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jm.SpineMallocSec3I.nx0 ok A Kc rho a (ES1g W0 st0 2) _ tp).
    + intros HC. exact (sec_ok_0h_S ok A Kc rho a tp HKc Hokl Hokpl HC _).
    + intros HC. exact (sec_ok_0l_S ok A Kc rho a tp HKc Hokl Hokpl HC _).
Qed.
End OK0.
End SpineMallocSecOK0S.

(* [comment removed for export] *)
Module SpineMallocRu0.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "ss_objs"; "valuation"; "rw"; "swf"; "ss_facts"; "ss_lenient"; "ss_next"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "la_state"; "ax_S"; "axst"; "leafA"; "sym_runA"; "ax_X"; "@Corelib.Init.Datatypes"; "bool"; "true"; "list"; "nil"; "cons"; "prod"; "app"; "false"; "Some"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ka.SpineMallocRu0"; "r_u1_0"; "r_u2_0"; "e3u"; "cellsf_u"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jt.SpineMallocRi0"; "W0"; "e3r"; "FUEL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jw.SpineMallocU1"; "cU0"; "cU1"; "kU1"; "kU2"; "cU2"; "perm_okb"; "O_arrF"; "O_pcmZ"; "eU"; "idx1"; "idx2"; "sU1"; "@Corelib.Lists.ListDef"; "map"; "firstn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR"; "nobj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "KcA"; "Kc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3"; "skel"; "inclb"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP"; "O_st"; "O_pcc0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_cache_inited"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SpineMallocR2"; "BASEF"; "BASEO"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1"; "JG"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ja.RebuildI"; "initA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillTR"; "TRok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "cst_ok"; "xgl_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "cnt_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jq.SpineMallocR5"; "posts_conv"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillTR RefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require io.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ja.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jw.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jt.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocR1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SpineMallocR2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jq.SpineMallocR5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ja.RebuildI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jw.SpineMallocU1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k2.SpineMallocU2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jt.SpineMallocRi0.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition R_u1__R : option (list leafA) := ltac2:(tb__ "0|0|
SeS20S23S14S1eZ41358S13S1eA1A3S24S22A1S11A5").
Local Strategy expand [R_u1__R].
Definition r_u1 := Eval vm_compute in ((fun ro1__ : option (list leafA) => (match ro1__ with Some l => l | None => [] end)) R_u1__R).
Definition r_u1_0 := Eval vm_compute in (nth 0 r_u1 (mkLeafA (cU0 e3r) RsCut)).
Definition cu1 := Eval vm_compute in (cU1 (la_state r_u1_0)).
Definition r_u2 := Eval vm_compute in (match sym_runA segsA FUEL [0x413f4] cu1 true with Some l => l | None => [] end).
Definition r_u2_0 := Eval vm_compute in (nth 0 r_u2 (mkLeafA cu1 RsCut)).
Definition cellsf_u := Eval vm_compute in (ob_cells (last (ss_objs (ax_S (la_state r_u2_0))) O_pcc0)).
Definition e3u := Eval vm_compute in (eU (la_state r_u2_0)).
Lemma E3u_eq : ltac2:(tb__ "0|0|
S0ScS2cSaS1bA1A1S1cA3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma WU0 : ltac2:(tb__ "0|0|
S0S10S6SbS24S22A1A1A1S11A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_u1 : ltac2:(tb__ "0|1|
S0S19S12SdA1M0A1SeS20S23S14S1eZ41358S13S1eA1A3S24S22A1S11A5S18G0S14SdS1aS13SdA1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_u1__R <: R_u1__R = Some [r_u1_0]). Qed.
Lemma LN_u1 : ltac2:(tb__ "0|0|
S0S10S8SbS24S22A1A1A1S17A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_u1 : ltac2:(tb__ "0|0|
S0S10S45PdcS9SbS24S22A1A1A1A2S11A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma PERM1 : ltac2:(tb__ "0|1|
S0S10S29S32SaS1aA1M0A1S2dG0A1A2S11A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma OB_s1 : ltac2:(tb__ "0|2|
S0S12S1A1S3SbS2fSaS1aA1M0A1A1A1M1S16S1S31S1S38S32G0A1U2A2G1A3S14S1S3fS14S1S2bS13S1A1A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma SK_k1 : ltac2:(tb__ "0|1|
S0S12S15S15S2S2A2S2A2M0A1S30S1G0S36S3SbS26SaS1aA1A1A1A1A4S30S1G0S36S16S1S43S21A1S14S1S3eS13S1A1A3A3A4A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_k1b : ltac2:(tb__ "0|0|
S0S10S37S42S21S33A2S7SbS26SaS1aA1A1A1A1A2S11A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XX_k1 : ltac2:(tb__ "0|1|
S0S12S15S2S2A2M0A1SfS26SaS1aA1A1A1S13G0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma W_c1 : ltac2:(tb__ "0|0|
S0S10S6SbS25SaS1aA1A1A1A1S11A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_u2 : ltac2:(tb__ "0|1|
S0S19S12SdA1M0A1SeS20S23S14S1eZ413f4S13S1eA1A3S25SaS1aA1A1S11A5S18G0S14SdS1bS13SdA1A3A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma LN_u2 : ltac2:(tb__ "0|0|
S0S10S8SbS25SaS1aA1A1A1A1S17A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_u2 : ltac2:(tb__ "0|0|
S0S10S45PdcS9SbS25SaS1aA1A1A1A1A2S11A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma OB_u2 : ltac2:(tb__ "0|2|
S0S12S1A1S3SbSaS1bA1M0A1A1M1S16S1S31S1S38S32G0A1U1A2G1A3S14S1S2aS1dA1S13S1A1A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma ARR_ok : arr_okb cellsf_u = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SK_k2 : ltac2:(tb__ "0|1|
S0S12S15S15S2S2A2S2A2M0A1S30S1G0S36S3SbS27SaS1bA1A1A1A1A4S30S1G0S36S16S1S43S21A1S14S1S3eS13S1A1A3A3A4A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_k2b : ltac2:(tb__ "0|0|
S0S10S37S42S21S33A2S7SbS27SaS1bA1A1A1A1A2S11A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XX_k2 : ltac2:(tb__ "0|1|
S0S12S15S2S2A2M0A1SfS27SaS1bA1A1A1S13G0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma W_c2 : ltac2:(tb__ "0|0|
S0S10S6SbS28SaS1bA1A1A1A1S11A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma PERM2 : ltac2:(tb__ "0|1|
S0S10S29S32S28SaS1bA1A1M0A1S2eG0A1A2S11A3").
Proof. vm_cast_no_check (eq_refl true). Qed.

Theorem refill_uninit_i : ltac2:(tb__ "0|4|
S12S15S1eS1eA2A1M0G0S48R2A1S49R2A1S40S34S12S15ScS3dA2A1F_;F_;S4bR5R4R1A3ScScS0ScR2S22A3S0ScR2S1cA3S40S34S4S12S4cQ40M1A1M2A1S39S39OF_;F_;S47R4R1A2S35R5A1S0S10S41R7A1S17A3S0S1eS4aR8S4dG1S5R6PcA2A2A2Z0A3S4S4S0S1fG2F_;S5R2A1S5R9A1A3R8S3bS20S44S21S33S46RcA1M3RbR3A5RfR2R9A5S3cS20S3aR3R9R12G3RbA2A5A2F_;FrX;Frho1;S4R7S3bS20S44S21S33RbRaR9A5RfR1R8A5S3cS20S3aR9R8R11RbRaA2A5A2FrhoE;F_;F_;F_;FHKc;FKIT;FTR;Ftp;Frho;FKc;FA;F_;F_;FE3U;FE3;FHPF;FPFam;FHXGL;FHCST;FXGL;FCST;").
Proof.
  intros CST XGL HCST HXGL PFam HPF E3 E3U -> ->. rewrite <- E3u_eq.
  intros A Kc rho tp TR KIT HKc Hini Hcnt HCONT.
  exact (refill_uninit CST XGL HCST HXGL PFam HPF 0 UStopLe FUEL e3r r_u1_0 r_u2_0 cellsf_u SK3 XX3 (inclb_incl _ _ XF3b) WU0 R_u1 LN_u1 NX_u1 PERM1 OB_s1 SK_k1 (inclb_incl _ _ XF_k1b) XX_k1 W_c1
           R_u2 LN_u2 NX_u2 OB_u2 ARR_ok SK_k2 (inclb_incl _ _ XF_k2b) XX_k2 W_c2 PERM2 A Kc rho tp TR KIT HKc HW0 Hini Hcnt HCONT).
Qed.
End SpineMallocRu0.

(* [comment removed for export] *)
Module SpineCallocR15.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "rm"; "sv"; "eval"; "sprop"; "SAlu"; "SLit"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CRefillJ"; "JR"; "phase"; "entryR"; "gh_new"; "ph0"; "frozen"; "ghosts"; "mlink"; "FAb"; "committed"; "ph_f"; "ph_u"; "releasedp"; "rlink"; "@Corelib.Init.Datatypes"; "list"; "bool"; "length"; "true"; "prod"; "nil"; "option"; "pair"; "None"; "Some"; "cons"; "nat"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "or"; "iff"; "@Stdlib.ZArith.BinInt.Z"; "add"; "mul"; "of_nat"; "le"; "lt"; "ge"; "ltb"; "modulo"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "cs_free_array"; "cs_mapped_free_array"; "class_state"; "aa_cache_inited"; "aa_geom"; "ag_spacebeg"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "mem_keptA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillTR"; "TRok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j9.SpineCallocR7"; "popfacts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "cst_of"; "cls_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.im.CRefillJP"; "ph_quiet"; "pbase"; "ph_set"; "PF"; "PU"; "ph_get"; "pord"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jw.SpineCallocR13"; "phL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k2.SpineCallocR14"; "e16P"; "e32P"; "e48P"; "e_srcP"; "e24M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jr.SpineCallocR6"; "backT"; "exitT"; "popT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSR"; "vMFA"; "beg1"; "beg2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel"; "kchunks"; "refillA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ka.SpineCallocR15.ASMP"; "pieceT"; "fillT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ka.SpineCallocR15"; "phFin"; "phUF3"; "phU3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1"; "JG"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "headroom"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "bview"; "view"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jt.SpineCallocR12"; "rup_e"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.je.SpineCallocR3"; "phK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jj.SpineCallocR4"; "ph_setcnt"; "ph_setri"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundV SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv InvLaws PrimCredit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillModel RefillModelP RefillBits.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillTR CRefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require im.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require je.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require js.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jt.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jw.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineCallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModelP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillBits OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CRefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.im.CRefillJP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineCallocR1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.SpineCallocR2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.je.SpineCallocR3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jj.SpineCallocR4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jo.SpineCallocR5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jr.SpineCallocR6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j9.SpineCallocR7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.js.SpineCallocR11 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jt.SpineCallocR12 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jw.SpineCallocR13 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k2.SpineCallocR14.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation segs := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree.segsA.

Section FAMAP.
Variables (A : AA) (Kc : KcA) (rb : valuation) (tp0 : list word) (md0 : Model).
Variable TR : assn -> assn -> Prop.
Hypothesis KIT : TRok Kc TR.
Hypothesis HKc : Kc_ok Kc.
Variables (W : list ulink) (st : ustop) (rho : valuation).
Hypothesis HE : ltac2:(tb__ "0|0|
SfVA;Vrb;Vtp0;Vmd0;VW;Vst;Vrho;A7").
Hypothesis PF : popfacts A rb.
Notation JRp := (JR A Kc rb tp0 md0).
Let cs : class_state := ltac2:(tb__ "0|0|
S45VA;S3eQ40S1Vrb;PcA2A2A2").
Variable LFm : axst.
Let CFM : axst := cFm LFm.
Hypothesis W_fm : ltac2:(tb__ "0|0|
S27S1cS8S48VCFM;A1A1S1eA3").
Hypothesis D_fm : ltac2:(tb__ "0|4|
S27S21S1fS1bS1fS3S3A2M0A1M1S1bS5A1M2A2M3A1S69S48VLFm;A1S48VCFM;A1A2S24G3S22G1G2S25G0S22S3S3S6dS6S68S5cS7Z40000A1A3A4S20G0A1A3S20S5A1A4A2A3").

Lemma famap_restate : ltac2:(tb__ "0|0|
SeS0S1bS3dQ40A1A1SaS30S38Vcs;A1S2dZ4S2cS2eS1dSbS37Vcs;A1A2A1S10VA;Vrb;A2A2A2A2VTR;ScS9SdVA;VKc;Vrb;Vtp0;Vmd0;R5A6VCFM;R4R3A5R2A2VTR;ScS9SdVA;VKc;Vrb;Vtp0;Vmd0;R6A6VLFm;R5R4A5R3A2F_;F_;FQ;Ftp;Fr;Fph;").
Proof.
  intros ph r tp Q HLT HT. pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF.
  apply (jr_restate A Kc rb tp0 md0 TR KIT LFm (ax_S CFM) _ _ ph r tp Q W_fm D_fm ltac:(apply Pos.eqb_refl)); [|exact HT].
  intros tr md (HFz & HGh & _) _. split; [|constructor]. unfold diffs_ok. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
  exact (rup_val A rb r CF PF HGh HLT).
Qed.
End FAMAP.

Definition phU3 : phase := ph_set PU 3 ph0.
Definition phUF3 : phase := ph_set PF 3 phU3.
Definition phFin (ph : phase) (new k : Z) : phase := ltac2:(tb__ "0|0|
S70S6fS6eS53Vph;Vnew;A2Vk;A2A1A1").

Section ASMP.
Variables CST XGL : list (Z * Z).
Variable PFam : ltac2:(tb__ "0|0|
S36S40S1bS1fS47S4bA2A1F_;F_;").
Variables (W : list ulink) (st : ustop).

Variables (LP CP2C RU LF0 LFm CFM RF LF1 : axst) (LJP XLP LZP LJM XLM LZM E3P : axst).
Notation AInvS := (AInvA segs).
Hypothesis HWs : stopJ_w W st.

Definition headT : Prop := ltac2:(tb__ "0|1|
S36S40S0S1bS3dQ40A1A1M0S34SaSaOF_;F_;S43R5R1A2S41R6A1S0S0G0SaSfRcRaR9R8VW;Vst;R4A7S44RdRbA2S0RaScS9SdRfReRdRcRbS11A6VCP2C;R1R5A5R4A2Fr';F_;R9ScS9SdReRdRcRbRaS11A6VLP;R5R4A5R3A2F_;F_;FQ;Ftp;Fr;Frho;FHKc;FKIT;FTR;Fmd0;Ftp0;Frb;FKc;FA;").
Definition pieceT (p : piece) (eb : sv) (C0 RX : axst) : Prop := ltac2:(tb__ "0|6|
S36S40S0S1bS3dQ40M0A1A1M1S34SaSaOF_;F_;S43R5R1A2S41R6A1S0SfR9R7R6R5VW;Vst;R1A7SeS27S26S51Vp;R1A2U0A3S52Vp;R2A2S4cR3A1S0S12RdR1A2S13R10ReR2A3S27SbS3eG0S4R3Veb;A2A2S4dR11RfVp;A3A3F_;F_;Fr;S28S2fS2cS3cS3bRfA1A1M2Z100000000A2S4dRfRdVp;A3M3A2S28S2fS2cG3Z40000M4A2S2cG2Z2000000000A2A2S27SbS33G3Z10000A2Z0A3A2A2G1S34S14R12R10RfReR8R2R1A7S31S6aR2R3A2M5G4A2F_;Fmd;Ftp;G1S34S14R13R11R10RfS4eVp;U1R9A3R2R1A7S31G5Z8000A2F_;Fmd;Ftp;S0G1SaS0G1R12ScS9SdR17R16R15R14R13S4eVp;U3RdA3A6VRX;R2R1A5R3A2Ftp';Fr';R11ScS9SdR16R15R14R13R12RcA6VC0;R4R3A5R2A2F_;FQ;Ftp;Fr;F_;F_;F_;F_;F_;F_;F_;Fph;FHE;Frho;FHKc;FKIT;FTR;Fmd0;Ftp0;Frb;FKc;FA;").
Definition midT : Prop := ltac2:(tb__ "0|4|
S36S40S0S1bS3dQ40M0A1A1M1S34SaSaOF_;F_;S43R5R1A2S41R6A1S0SfR9R7R6R5VW;Vst;R1A7S44RaR8A2SeS0G1SaS45RfS3eG0S1RdPcA2A2A2S39S29S30S38R1A1S2dZ4M2S2cS2eS1dSbS37R1A1A2A1S10R10ReA2A2A2A2A1S0RdScS9SdR12R11R10RfReR7A6M3VLF0;R1R5A5R4A2Fr';F_;S30S38R2A1S2dG2S2cS2eS1dSbS37R2A1A2A1S10R11RfA2A2A2A2S0ReScS9SdR13R12R11R10RfR8A6VLFm;R1R6A5R5A2Fr';F_;RdScS9G3VRU;R6R5A5R4A2F_;F_;Tcs;FQ;Ftp;Fr;Fph;FPF;FHE;Frho;FHKc;FKIT;FTR;Fmd0;Ftp0;Frb;FKc;FA;").
Definition fmT : Prop := ltac2:(tb__ "0|2|
S36S40S0S1bS3dQ40M0A1A1M1S34SaSaOF_;F_;S43R5R1A2S41R6A1S0SfR9R7R6R5VW;Vst;R1A7S44RaR8A2SeS0G1SaS45RfS3eG0S1RdPcA2A2A2S39S30S38R1A1S2dZ4S2cS2eS1dSbS37R1A1A2A1S10R10ReA2A2A2A2RcScS9SdR11R10RfReRdR6A6VCFM;R5R4A5R3A2RdScS9SdR12R11R10RfReR7A6VLFm;R6R5A5R4A2F_;F_;Tcs;FQ;Ftp;Fr;Fph;FPF;FHE;Frho;FHKc;FKIT;FTR;Fmd0;Ftp0;Frb;FKc;FA;").
Definition runT (C L : axst) : Prop := ltac2:(tb__ "0|2|
S36S40S0S1bS3dQ40A1A1M0S34SaSaOF_;F_;S43R5R1A2S41R6A1SeS0G0SaS0R8ScS9SdRdRcRbRaR9R5A6M1VL;R1R3A5R2A2Fr';R8ScS9G1VC;R4R3A5R2A2F_;FQ;Ftp;Fr;Fph;FHKc;FKIT;FTR;Fmd0;Ftp0;Frb;FKc;FA;").
Definition fillT (LH LJ : axst) : Prop := ltac2:(tb__ "0|7|
S36S40S0S1bS3dQ40M0A1A1M1S34SaSaOF_;F_;S43R5R1A2S41R6A1S0SfR9R7R6R5VW;Vst;R1A7S44RaR8A2SeS4cR1A1SbS6bS28S2fZ0R2A2S2fR2S10RfRdA2A2A2S1aR10ReS53R5R3A2S6cS9S2ReA1A2R2A5SbS28S2fS2cS15R12R10A2M2S2dZ4M3S2eS1dSbS37S45R12S3eG0S1R10PcA2A2A2A1A2A1M4A2A2R1A2S30R1S2cG2S2dG3S2cG4S10R12R10A2M5A2A2A2A2A2S29S27S21S3dQ8A1M6A1R5R2A1S23G6A1A3A1F_;Fz;F_;F_;Fm;Fi;S0G1SaS0RdScS9SdR12R11R10RfReS53R7G5A2A6VLJ;R1R3A5R2A2Fr';RdScS9SdR12R11R10RfReR7A6VLH;R4R3A5R2A2F_;FQ;Ftp;Fr;F_;F_;Fph;FPF;FHE;Frho;FHKc;FKIT;FTR;Fmd0;Ftp0;Frb;FKc;FA;").

Hypothesis H_head : headT.
Hypothesis H_pu : ltac2:(tb__ "0|0|
S62S50S5dVCP2C;VRU;A4").
Hypothesis H_mid : midT.
Hypothesis H_fm : fmT.
Hypothesis H_pf : ltac2:(tb__ "0|0|
S62S4fS5eVCFM;VRF;A4").
Hypothesis H_run : runT RF LF1.
Hypothesis H_fillP : fillT LF0 LJP.
Hypothesis H_fillM : fillT LF1 LJM.
Hypothesis H_popP : ltac2:(tb__ "0|0|
S5bVW;Vst;VLJP;VXLP;S57A5").
Hypothesis H_popM : ltac2:(tb__ "0|0|
S5bVW;Vst;VLJM;VXLM;S57A5").
Hypothesis H_exitP : ltac2:(tb__ "0|0|
S5aVW;Vst;VXLP;VLZP;S54S5cS55S56A8").
Hypothesis H_exitM : ltac2:(tb__ "0|0|
S5aVW;Vst;VXLM;VLZM;S54S58S55S56A8").
Hypothesis H_backP : ltac2:(tb__ "0|0|
S59VCST;VXGL;VPFam;VW;Vst;VE3P;VLZP;A7").
Hypothesis H_backM : ltac2:(tb__ "0|0|
S59VCST;VXGL;VPFam;VW;Vst;VE3P;VLZM;A7").

Lemma pop_tail : ltac2:(tb__ "0|5|
S47S47S47S47S3S63R5R4A2S5bVW;Vst;R5R4S57A5S5aVW;Vst;R5R4S54R3S55S56A8S59VCST;VXGL;VPFam;VW;Vst;VE3P;R5A7S36S40S0S1bS3dQ40M0A1M1A1M2S34SaSaOF_;F_;S43R5R1A2S41R6A1S0SfR9R7R6R5VW;Vst;R1A7S44RaR8A2SeS27S1cS3aRcA1S1eA3S4cR2A1S27S1cS16S18R3A1A1S1eA3S3eG0S1RdPcA2A2SbS46R1A1SbS45R11R2A2S39S2eS1dSbS37R1A1A2A1SbS10R13R11A2SbS38R3A1SbS2aS27S1cS19S17RaA1A1S1eA3S2fS2dZ4M3S2cR3R2A2A2R1A2A2S0S12R15R1A2S13R18R16R2A3S27G1S4R3R1eA2S3fG0S1cSbL_;S32R5S2dG3S2cR7R6A2A2A2S2cR5Z40000A2R5X1cx2A2A3F_;F_;Fr;S0G2S1bS35A1S34SdR1bR1aR19R18R17S64R10R8S60RbA1A3R4R3R2R1AaS28S5fS9S61R1cRcA2M4R5R4R2A5S42VCST;VXGL;R1cG4S2R1aA1S2R5A1A6A2F_;Fmd;Ftr;Ftp';Fr;S36S0G2S0R17ScS9S67VW;Vst;R4R1bR3A5VE3P;R1R2A5S4aS9S49R3R2VPFam;R4R1bA2A5A2FrX;Ftp';Frho';FA';S0G2R16ScS9SdR1bR1aR19R18R17R10A6R24R2R1A5S4aS9S49R13R18VPFam;R1bR1aA2A5A2Ftp;Fr;F_;F_;F_;F_;Tmfa;Tnew;Tnf;Tcs;Tc;Tnv;F_;F_;F_;FphX;FPF;FHE;Frho;FHKc;FKIT;FTR;Fmd0;Ftp0;Frb;FKc;FA;F_;F_;F_;F_;Fe24;FLZ;FXL;FLJ;FLH;").
Proof.
  intros LH LJ XL LZ e24 HFI HPO HEX HBA A Kc rb tp0 md0 TR KIT HKc rho HE PF phX Hini PQ PCU nv c cs nf new mfa HARM HE24 HREB HPOP r tp.
  pose proof (P_csR A rb tp0 md0 W st rho HE PF) as (X1 & X2 & X3 & X5 & X6 & X7 & LP' & HIDS). cbn zeta in X1, X2, X3, X5, X6, X7, LP', HIDS. fold nv c cs nf new in X1, X2, X3, X5, X6, X7, LP', HIDS.
  destruct (pop_geo A rb tp0 md0 W st rho HE PF) as (C1 & S1 & AU0 & MU1 & N4 & K1 & KN & NF0 & MF1 & MF2 & MF0 & _). fold nv c cs nf new mfa in C1, S1, AU0, MU1, N4, K1, KN, NF0, MF1, MF2, MF0.
  set (k := kchunks c) in *. set (fP := faP c cs) in *.

  apply (HFI A Kc rb tp0 md0 TR KIT HKc rho HE PF phX PQ).
  { intros i m Hi HR z Hz. apply (P_HDEF A rb tp0 md0 W st rho HE PF (phL phX i) m); [exact HARM | exact HR | exact Hz]. }
  intros r1.

  apply (HPO A Kc rb tp0 md0 TR KIT HKc rho HE (phL phX new) (conj eq_refl (conj eq_refl eq_refl)) fP).
  - intros i m Hi HR idx Hidx. apply (P_HSRC A rb tp0 md0 W st rho HE PF (phK (phL phX new) i) m); [reflexivity | cbn [ph_pop phK]; fold nv c k in Hi; clear -Hi K1; lia | exact HR | exact Hidx].
  - fold nv c k. rewrite LP'. clear -KN NF0. lia.
  - rewrite LP'. clear -MF1 MF2 N4. lia.
  - intros _. unfold gh_nf. fold nv c cs nf new. rewrite LP'. cbn [ph_fill phL]. clear -NF0 N4. lia.
  - exact HIDS.
  - fold nv c cs k. rewrite LP'. exact X1.
  - fold nv c k. exact (P_HSRCP A rb tp0 md0 W st rho HE PF).
  - intros r2.

    apply (HEX A Kc rb tp0 md0 TR KIT HKc rho HE (phK (phL phX new) k) (conj eq_refl (conj eq_refl eq_refl))).
    + intros _. unfold gh_nf. fold nv c cs nf new. cbn [ph_fill phK phL]. clear -NF0 N4 MF1 MF2. lia.
    + exact Hini.
    + intros r' HFz HGh. exact (P_HRIv A rb tp0 md0 W st rho HE PF e24 r' HFz HGh (HE24 r' HFz HGh)).
    + fold nv c cs k. exact X2.
    + fold nv c cs. intros x Hx. rewrite X1 in Hx. apply HIDS. rewrite <- (firstn_skipn (Z.to_nat (nf + new - k)) fP). apply in_or_app. right. exact Hx.
    + intros r3.

      apply (HBA A Kc rb tp0 md0 TR KIT rho HE (phFin phX new k)).
      * intros r' t tr md HJ. exact (proj1 (HREB r' t tr md HJ)).
      * intros r' t tr md HJ. exact (proj2 (HREB r' t tr md HJ)).
      * fold nv c cs k. exact X2.
      * exact (HPOP (refillA A c)).
Qed.

Theorem refill_populate : ltac2:(tb__ "0|3|
S36S40S0S1bS3dQ40M0A1A1M1SaSaOF_;F_;S43R4R1A2S41R5A1S27S1cS3aR7A1S1eA3S4aS9S49R6R5VPFam;R8R7A2A5SaS0S34SfRbR2R8R1VW;Vst;R9A7S44RcR3A2SeS2aS27SeR1S66A3S27SeR1S65A3A2S3eG0S1R6PcA2A2SbS46R1A1SbS45R11R2A2S39S2bS27SeR5S65A3S30S38R1A1S2dZ4S2cS2eS1dSbS37R1A1A2A1S10R12R9A2A2A2A2A2S0G1S1bS35A1S34SdR17R16ReR14RdS64RaS10R17ReA2S60R7A1A3R4R3R2R1AaS28S5fS9S61R18R8A2M2R5R4R2A5S42VCST;VXGL;R18G2S2RfA1S2R5A1A6A2F_;Fmd;Ftr;Ftp';Fr;F_;Tcs;Tc;Tnv;F_;FphX;FPF;FHE;Fmd0;Frb;S36S0G1S0RaScS9S67VW;Vst;R4RdR3A5VE3P;R1R2A5S4aS9S49R3R2VPFam;R4RdA2A5A2FrX;Ftp';Frho';FA';S0S34S0SfReR3RbR2VW;Vst;RcA7RbScS9SdRfReR4RcR3S11A6VLP;R2RcA5R7A2F_;Fr';Fmd0;Frb;F_;F_;TQ;F_;FHKc;FKIT;FTR;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp TR KIT HKc Hini Q HREB HPOP rb md0 r0 HE.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF.
  apply (H_head A Kc rb tp md0 TR KIT HKc rho r0 tp Q HE). intros PF r1.
  set (nv := bv_unsigned (rw rb 12%positive)) in *. set (c := cls_of nv) in *. set (cs := cst_of A nv) in *.
  destruct (pop_geo A rb tp md0 W st rho HE PF) as (C1 & S1 & AU0 & MU1 & N4 & K1 & KN & NF0 & MF1 & MF2 & MF0 & G13 & G14 & FAr & _).
  fold nv c cs in C1, S1, AU0, MU1, N4, K1, KN, NF0, MF1, MF2, MF0, FAr.
  destruct (pop_credit A rb tp md0 W st rho HE PF) as (CR & _). fold nv c cs in CR.
  assert (G12 : ag_spacebeg (aa_geom A) mod 65536 = 0) by (unfold cfacts in CF; cbn zeta in CF; destruct CF as (_ & _ & _ & _ & _ & (X & _) & _); exact X).
  assert (MU18 : cs_mapped_user cs mod 262144 = 0) by (unfold cfacts in CF; cbn zeta in CF; fold nv c cs in CF; destruct CF as (_ & _ & (X & _) & _); exact X).

  apply (H_pu A Kc rb tp md0 TR KIT HKc rho HE ph0 eq_refl eq_refl (conj eq_refl (conj eq_refl (conj eq_refl eq_refl)))).
  - intros r HFz HGh. exact (beg1_val A rb r CF (entry_rigids _ _ _ _ _ _ _ _ HE HFz) HGh).
  - cbn [pbase]. unfold U0, region_beg, kRegionSize. fold nv c cs. split; [clear -C1 AU0; lia|]. split; [clear -C1 MU1; lia|].
    rewrite Z.add_mod, (Z.add_mod (ag_spacebeg (aa_geom A))), G12 by (clear; lia).
    destruct (proj1 (Z.mod_divide (cs_mapped_user cs) 262144 ltac:(clear; lia)) MU18) as [q Hq]. rewrite Hq.
    replace (c * 2 ^ 32) with (c * 65536 * 65536) by (clear; lia). replace (q * 262144) with (q * 4 * 65536) by (clear; lia). rewrite !Z_mod_mult. reflexivity.
  - intros t md HM. pose proof (pop_headroom A rb tp md0 W st rho HE PF ph0 t md HM) as X. cbn [ph0 ph_u ph_f committed revealedp Nat.leb] in X.
    destruct (cs_mapped_free_array cs <? _); clear -X CR; lia.
  - intros t md HM. pose proof (pop_headroom A rb tp md0 W st rho HE PF (ph_set PU 1 ph0) t md HM) as X. cbn [ph_set ph0 ph_u ph_f committed revealedp Nat.leb] in X.
    destruct (cs_mapped_free_array cs <? _); clear -X CR; lia.
  - intros r2 tp2. fold phU3.
    apply (H_mid A Kc rb tp md0 TR KIT HKc rho HE PF phU3 r2 tp2 Q); cbn zeta; fold nv c cs.
    +
      intros NLT r3.
      apply (pop_tail LF0 LJP XLP LZP vMFA H_fillP H_popP H_exitP H_backP A Kc rb tp md0 TR KIT HKc rho HE PF phU3 Hini (conj eq_refl (conj eq_refl (conj eq_refl eq_refl))) eq_refl).
      * right. fold nv c cs. clear -NLT. lia.
      * intros r HFz HGh. fold nv c cs. replace (cs_mapped_free_array cs <? _) with false by (symmetry; apply Z.ltb_ge; clear -NLT; lia).
        destruct HGh as (_ & _ & Q222 & _). fold nv c cs in Q222. exact Q222.
      * fold nv c. apply (HREB rb md0 HE PF phU3 (or_introl eq_refl)). cbn zeta. fold nv c cs. split; [intros X; discriminate X | intros X; contradiction].
      * exact HPOP.
    +
      intros LT r3.
      apply (H_fm A Kc rb tp md0 TR KIT HKc rho HE PF phU3 r3 tp2 Q LT).
      pose proof (P_newZ A rb) as ENZ. fold nv c cs in ENZ.
      destruct (RefillModelP.P_famap c cs _ C1 (proj1 (entry_pure A rb tp md0 W st rho HE PF)) (proj2 (proj2 (proj2 (entry_pure A rb tp md0 W st rho HE PF))))
                  ltac:(rewrite ENZ; exact LT)) as (_ & FCM).
      pose proof (facap_room c C1) as FRM.
      apply (H_pf A Kc rb tp md0 TR KIT HKc rho HE phU3 eq_refl I (conj eq_refl (conj eq_refl (conj eq_refl eq_refl)))).
      * intros r HFz HGh. exact (beg2_val A rb r CF (entry_rigids _ _ _ _ _ _ _ _ HE HFz) HGh).
      * cbn [pbase]. unfold F0, free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize. fold nv c cs.
        split; [clear -C1 NF0 MF1; lia|]. split; [clear -C1 FCM FRM; lia|].
        rewrite Z.add_mod, (Z.add_mod (ag_spacebeg (aa_geom A) + c * 2 ^ 32)), (Z.add_mod (ag_spacebeg (aa_geom A))), G12 by (clear; lia).
        destruct (proj1 (Z.mod_divide (cs_mapped_free_array cs) 262144 ltac:(clear; lia)) MF0) as [q Hq]. rewrite Hq.
        replace (c * 2 ^ 32) with (c * 65536 * 65536) by (clear; lia). replace (q * 262144) with (q * 4 * 65536) by (clear; lia). rewrite !Z_mod_mult. reflexivity.
      * intros t md HM. pose proof (pop_headroom A rb tp md0 W st rho HE PF phU3 t md HM) as X. cbn [phU3 ph_set ph0 ph_u ph_f committed revealedp Nat.leb] in X.
        fold nv c cs in CR. replace (cs_mapped_free_array cs <? _) with true in CR by (symmetry; apply Z.ltb_lt; exact LT). clear -X CR. lia.
      * intros t md HM. pose proof (pop_headroom A rb tp md0 W st rho HE PF (ph_set OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.im.CRefillJP.PF 1 phU3) t md HM) as X. cbn [phU3 ph_set ph0 ph_u ph_f committed revealedp Nat.leb] in X.
        fold nv c cs in CR. replace (cs_mapped_free_array cs <? _) with true in CR by (symmetry; apply Z.ltb_lt; exact LT). clear -X CR. lia.
      * intros r4 tp4. fold phUF3.
        apply (H_run A Kc rb tp md0 TR KIT HKc phUF3 r4 tp4 Q). intros r5.
        apply (pop_tail LF1 LJM XLM LZM e24M H_fillM H_popM H_exitM H_backM A Kc rb tp md0 TR KIT HKc rho HE PF phUF3 Hini (conj eq_refl (conj eq_refl (conj eq_refl eq_refl))) eq_refl).
        -- left. reflexivity.
        -- intros r HFz HGh. fold nv c cs. replace (cs_mapped_free_array cs <? _) with true by (symmetry; apply Z.ltb_lt; exact LT).
           destruct HGh as (_ & _ & Q222 & _). fold nv c cs in Q222. unfold e24M, vMFA. cbn [eval]. rewrite Q222. apply bv_eq.
           rewrite add_val, !u64_lit by (clear -NF0 MF1 MF2; lia). rewrite Z.mod_small by (clear -NF0 MF1 MF2; lia). reflexivity.
        -- fold nv c. apply (HREB rb md0 HE PF phUF3 (or_intror eq_refl)). cbn zeta. fold nv c cs. split; [intros _; exact LT | intros _; reflexivity].
        -- exact HPOP.
Qed.
End ASMP.
End SpineCallocR15.

