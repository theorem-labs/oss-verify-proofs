(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "prod"; "list"; "cons"; "nat"; "bool"; "nil"; "pair"; "fst"; "None"; "app"; "false"; "snd"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "A_globals"; "mkA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "valuation"; "SVar"; "FcsrFrm0"; "SLit"; "mkSS"; "rm"; "rw"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "PTrue"; "JA_pre"; "JLA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_fuzz_iface2"; "P0_fz"; "P_fz"; "NPOST_FZ"; "PD_fz"; "fcallee_saved"; "post_fregs_fz"; "@Corelib.Init.Logic"; "and"; "eq"; "@Corelib.Lists.ListDef"; "map"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "post_regs"; "setregs"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@Corelib.Init.Nat"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nk.Lib_fuzz_iface"; "Pre_fz"; "nd_fz0"; "O_F_fz"; "O_W_fz"; "O_pay"; "P0_fz"; "X_fz"; "fz_facts"; "nd_fz1"; "vDAT"; "vLEN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_fuzz_iface2.Stmt"; "Posts_fz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "BXok_d"; "bxt"; "uval"; "@Stdlib.PArith.BinPos.Pos"; "of_nat"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nk.Lib_fuzz_iface.FZAddr"; "fz_ret"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "pclMA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "ccount"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol"; "HB"; "PRES"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CFGA GlueA SummaryA SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nk.
Export OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nk.Lib_fuzz_iface.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import FZAddr.

Definition fcallee_saved (r : nat) : bool :=
  match r with 8 | 9 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 => true | _ => false end%nat.
Definition post_fregs_fz : list sv := ltac2:(tb__ "0|0|
S29S4S14S4S5S14L_;S25R1A1S16S43S30U3cR1A2A1A1S16S43S30U8cR1A2A1A1X5x2Lr;S2aU0U20A2A4").
Definition NPOST_FZ : positive := 172%positive.
Definition P_fz : axst := ltac2:(tb__ "0|1|
S10S19S45S2dS2cS2bA1S3S1S4S14A2M0S7S4S14UaS18Z0A1A4S6G0A1A3A2S26S17S9S14A1SaS13S3S13S33S3S13S34S3S13S35S6S13A1A3A3A3SfA3S38S23SbA9S37A2").
Definition PD_fz : list (axst * ndesc) := ltac2:(tb__ "0|1|
S3S1S11S1dA2M0S7S11S1dS22S39A4S6G0A1A3").
Lemma P_fz_swf : ltac2:(tb__ "0|0|
S28S5S1cS12S22A1A1SdA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition P0_fz (CST : list (Z * Z)) (FB : list (Z * Z)) (FF : list (Z * Z * Z)) (r : valuation) : Prop := ltac2:(tb__ "0|2|
S27S0S27S4eS42Vr;S3aA2M0R1A2S4fR1S4dG0S42Vr;S3bA2A2A2A2S48VCST;Vr;VFB;VFF;R2A5F_;Fa;S27S0S28S4S49R1S29S1S1S0S0A2M1S0A2G1S8G1S0A2VFF;A4A2U0A3Fc;S4bSeS1aVr;A1S2fQ40S1bVr;PaA2A2S4aVr;A1A4A2A2").
Lemma P0_fz_old : ltac2:(tb__ "0|2|
S2S1S0S0A2M0A1M1G1S2S1G0S0A2A1S15S21R4R3R2R1A4S36R5R4R3R2A4F_;Fr;FFF;FFB;FCST;").
Proof. intros CST FB FF r (H1 & H2 & _). split; assumption. Qed.

Section Stmt.
Variable AInv : ltac2:(tb__ "0|0|
S4cS15S2S2eQ40A1A1S44OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Variable Kc : KcA.
Definition Posts_fz (FB : list (Z * Z)) (FF : list (Z * Z * Z)) (BX : bxt) : list (axst * jpostA) := ltac2:(tb__ "0|1|
S29S1S11S1dA2M0S1S11S3fA2G0S7S11S3fS8S11S1dR1A3S20VAInv;VCST;VXGL;VKc;S21VCST;VFB;VFF;A3VFB;VFF;VBX;S1eScS11S1dR1A3AaA4Ld;S24A4").
Definition fuzz_one_sumT (ok : world -> Prop) : Prop := ltac2:(tb__ "0|1|
S2S1S0S0A2M0A1S2S1G0S0A2A1S41S15S2S2eQ40A1A1S40Z8R3A2S47SeVok;S3dSeS1fVAInv;VCST;VXGL;VKc;S21VCST;R6R5A3R6R5R4S1eS32AaS31R3R2A5S3eSeS2bR3R2S3cR6R5R4A3A5A4F_;Ftp0;Frho0;FBX;FFF;FFB;").
Definition fuzz_one_sumE : Prop := ltac2:(tb__ "0|1|
S2S1S0S0A2M0A1S2S1G0S0A2A1S41S15S2S2eQ40A1A1S40Z8R3A2S46SeS3dSeS1fVAInv;VCST;VXGL;VKc;S21VCST;R6R5A3R6R5R4S1eS32AaS31R3R2A5S3eSeS2bR3R2S3cR6R5R4A3A5A3F_;Ftp0;Frho0;FBX;FFF;FFB;").
End Stmt.
