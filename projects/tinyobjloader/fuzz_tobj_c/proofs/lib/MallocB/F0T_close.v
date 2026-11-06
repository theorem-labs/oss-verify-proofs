(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "cst_ok"; "xgl_ok"; "@Corelib.Init.Logic"; "not"; "and"; "False"; "or"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "@Corelib.Init.Datatypes"; "list"; "prod"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild"; "IMG_F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "IA_BEG"; "IA_END"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvQ8"; "QRD_img"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dfp_static"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0T_close"; "geomT_B"; "segD_TE_B"; "segD_T_B"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "AE_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m6.F0T_top"; "free_tol_contract_B"; "free_tol_contract_ex_B"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol"; "free_tol_contract"; "free_tol_contract_ex"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ik.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ix.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require km.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ke.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m6.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.UnwT_node OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.km.F0T_depotG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0T_asm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m6.F0T_top.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma segD_T_B : segD_T_stmt. Proof. exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ik.SegD2.seg_D_sound2T. Qed.
Lemma segD_TE_B : segD_TE_stmt. Proof. exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ik.SegD2.seg_D_complete2T. Qed.
Lemma geomT_B : geomT_stmt.
Proof.
  intros A rho tp md HA. pose proof HA as (HG & _). split; [|exact (Inv.geom_stop_hb _ HG)].
  destruct HG as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ST & _). clear - ST. lia.
Qed.

Definition free_tol_contract_closed : ltac2:(tb__ "0|2|
SaSbS0S0A2A1M0G0S2R2A1S3R2A1S0S1R5R1A2S7S1SdR2A2S5S8SeR2A2S9R2SfA2A2M1A2S6F_;F_;Fa;S0S1R6R1A2S4S12R2A1A1F_;Fa;S0S1R7R1A2S4S11R2A1A1F_;Fa;S0S1R8R1A2S5S4G1A1S4S5S8Z17db48R2A2S9R2Z17db4cA2A2A1A2F_;Fa;S19ScS16S10ScA1R8R7A5FHCST2;FHCSTQ;FHCSTD;FHCSTF;FHXGL;FHCST;FXGL;FCST;") := ltac2:(tb__ "0|2|
SaSbS0S0A2A1M0G0S2R2A1S3R2A1S0S1R5R1A2S7S1SdR2A2S5S8SeR2A2S9R2SfA2A2M1A2S6F_;F_;Fa;S0S1R6R1A2S4S12R2A1A1F_;Fa;S0S1R7R1A2S4S11R2A1A1F_;Fa;S0S1R8R1A2S5S4G1A1S4S5S8Z17db48R2A2S9R2Z17db4cA2A2A1A2F_;Fa;S17R8R7R6R5R4R3R2R1S15S13AaLHCST2;LHCSTQ;LHCSTD;LHCSTF;LHXGL;LHCST;LXGL;LCST;").
Definition free_tol_contract_ex_closed : ltac2:(tb__ "0|2|
SaSbS0S0A2A1M0G0S2R2A1S3R2A1S0S1R5R1A2S7S1SdR2A2S5S8SeR2A2S9R2SfA2A2M1A2S6F_;F_;Fa;S0S1R6R1A2S4S12R2A1A1F_;Fa;S0S1R7R1A2S4S11R2A1A1F_;Fa;S0S1R8R1A2S5S4G1A1S4S5S8Z17db48R2A2S9R2Z17db4cA2A2A1A2F_;Fa;S1aScS16S10ScA1R8R7A5FHCST2;FHCSTQ;FHCSTD;FHCSTF;FHXGL;FHCST;FXGL;FCST;") := ltac2:(tb__ "0|2|
SaSbS0S0A2A1M0G0S2R2A1S3R2A1S0S1R5R1A2S7S1SdR2A2S5S8SeR2A2S9R2SfA2A2M1A2S6F_;F_;Fa;S0S1R6R1A2S4S12R2A1A1F_;Fa;S0S1R7R1A2S4S11R2A1A1F_;Fa;S0S1R8R1A2S5S4G1A1S4S5S8Z17db48R2A2S9R2Z17db4cA2A2A1A2F_;Fa;S18R8R7R6R5R4R3R2R1S14S13AaLHCST2;LHCSTQ;LHCSTD;LHCSTF;LHXGL;LHCST;LXGL;LCST;").
