(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "list"; "pair"; "cons"; "nil"; "prod"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "J_alloc_pre"; "Pre_malloc"; "JL_malloc_ok"; "KcA"; "Kc_ok"; "L_malloc_ok"; "malloc_shape"; "ulink"; "ustop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "SVar"; "rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_Kf"; "aa_Km"; "aa_V"; "@Stdlib.ZArith.BinInt.Z"; "le"; "pow"; "add"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@Corelib.Init.Logic"; "and"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.IfaceS"; "alloc_roomA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundR SymSummary ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model RtCells Iface.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition alloc_roomA (A : AA) (n : Z) : Prop := ltac2:(tb__ "0|1|
S21S1cS1bVA;A1S1dZ2M0Z24A2A2S21S1cVn;S1dG0Z1aA2A2S1cS1eS1aVA;A1S19VA;A1A2Z800A2A2A2").

Section WithSegs.
Variable segs : list Segment.
Section Contracts.
Variable E : aentry.
Variable AInvA : ltac2:(tb__ "0|0|
S18S15S0S1fQ40A1A1S23OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).

Definition malloc_contractA_strong : Prop := ltac2:(tb__ "0|5|
S0S13A1S14S28OF_;S18SfS15S0S1fQ40M0A1A1S12R7R6A2S10R4A1S8Vsegs;R7S7R5A1A3S29Vsegs;R8S7R6A1A3S0S22A1M1S5S6Vsegs;ScVAInvA;RdRcRaR9S16PcM2A1M3A6SdVE;RdRcA3R8R7S1G1S5R2R1A4A6S25RbS20G0S17R9G2A2A2A2F_;Fmd;Ftr;S27Vsegs;RaS6Vsegs;ScVAInvA;RcRbR9R8G3A6SdVE;RcRbA3R7R6A5SbVsegs;S24R7R6S2S4S9SaA2M4S1S9SaS11VE;RcRbA3SeVAInvA;VCST;VXGL;R9R8A5A4S3G4A1A3A5A4F_;F_;F_;F_;F_;Ftp;Frho;FKc;FA;Fok;Fst;FW;").

Definition malloc_contractA_strong_ex : Prop := ltac2:(tb__ "0|5|
S0S13A1S14S18SfS15S0S1fQ40M0A1A1S12R6R5A2S10R4A1S0S22A1M1S5S6Vsegs;ScVAInvA;RaR9R8R7S16PcM2A1M3A6SdVE;RaR9A3R6R5S1G1S5R2R1A4A6S25R9S20G0S17R7G2A2A2A2F_;Fmd;Ftr;S26Vsegs;S6Vsegs;ScVAInvA;R9R8R7R6G3A6SdVE;R9R8A3R5R4A5SbVsegs;S24R5R4S2S4S9SaA2M4S1S9SaS11VE;R9R8A3SeVAInvA;VCST;VXGL;R7R6A5A4S3G4A1A3A5A3F_;F_;F_;Ftp;Frho;FKc;FA;Fst;FW;").
End Contracts.
End WithSegs.
