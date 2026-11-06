(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLe"; "AE_A"; "KcA"; "Kc_ok"; "J_free_preT"; "Pre_freeI"; "Wcan"; "client_addrA"; "client_shadowA"; "JL_free"; "L_free"; "free_contractA"; "free_contractA_ex"; "ulink"; "ustop"; "@Corelib.Init.Datatypes"; "list"; "false"; "true"; "prod"; "pair"; "bool"; "nil"; "cons"; "length"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_live"; "aa_internal_inited"; "qbatch"; "aa_cache_inited"; "aa_q_thread"; "qb_items"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "AInvA"; "IA_BEG"; "IA_END"; "@Corelib.Init.Logic"; "eq"; "or"; "and"; "not"; "False"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_top"; "QFT"; "CQ1C"; "wholeE_stmt"; "whole_stmt"; "qcondC"; "contFn"; "econtFn"; "top_pure"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok"; "qcond"; "rhoF_of"; "j_min"; "junkF"; "cache24"; "lastq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skeln"; "HBIGNE_stmt"; "HBIGN_stmt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "of_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls"; "blk_cls"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_cLN0"; "Erc_LN0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_cLN1"; "Erc_LN1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_cLN2"; "Erc_LN2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_cN0"; "Erc_N0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_cN1"; "Erc_N1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_cN2"; "Erc_N2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.F0A_depot"; "tjv_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel"; "JF"; "depot_onlyKf"; "rigF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states"; "QA"; "QBe"; "QBf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "kQuarantineMax"; "kQuarantineMin"; "kQuarantineBatchCount"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5"; "hd_link"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_rebuild"; "IMG_F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvQ8"; "QRD_img"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "dfp_static"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_wf DepotCall TopGlueA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.TopGlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require af.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_instok F0A_rebuild.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require InvQ8 F0A_drain.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c9.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_laws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_rebuild OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cp.F0A_asm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvQ8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_drain OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.F0A_mstates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.F0A_minit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c9.F0A_masm.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require af.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ar.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require dh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require dg.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require au.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ae.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require dz.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require dd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aw.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require dk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require dl.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ax.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require dy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ah.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ag.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require df.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require di.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ay.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_mL2Bf.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_c0A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ar.F0A_i0A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dh.F0A_a0A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dg.F0A_m0A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.au.F0A_b0A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.F0A_cL0A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dz.F0A_iL0A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dd.F0A_aL0A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.F0A_mL0A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aw.F0A_bL0A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_c0Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ar.F0A_i0Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dh.F0A_a0Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dk.F0A_m0Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.au.F0A_b0Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.F0A_cL0Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dz.F0A_iL0Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dd.F0A_aL0Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.F0A_mL0Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aw.F0A_bL0Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_c0Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ar.F0A_i0Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dh.F0A_a0Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dl.F0A_m0Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.au.F0A_b0Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.F0A_cL0Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dz.F0A_iL0Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dd.F0A_aL0Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dg.F0A_mL0Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aw.F0A_bL0Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_c1A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ar.F0A_i1A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dh.F0A_a1A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dk.F0A_m1A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aw.F0A_b1A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.F0A_cL1A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dz.F0A_iL1A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dd.F0A_aL1A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dg.F0A_mL1A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ax.F0A_bL1A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_c1Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dy.F0A_i1Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dh.F0A_a1Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dl.F0A_m1Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aw.F0A_b1Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ah.F0A_cL1Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dz.F0A_iL1Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dd.F0A_aL1Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dg.F0A_mL1Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ax.F0A_bL1Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ag.F0A_c1Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dy.F0A_i1Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dh.F0A_a1Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dl.F0A_m1Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aw.F0A_b1Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ah.F0A_cL1Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dz.F0A_iL1Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.df.F0A_aL1Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dg.F0A_mL1Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ax.F0A_bL1Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ag.F0A_c2A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dy.F0A_i2A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.di.F0A_a2A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dl.F0A_m2A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ax.F0A_b2A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ah.F0A_cL2A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.au.F0A_iL2A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.df.F0A_aL2A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dk.F0A_mL2A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ay.F0A_bL2A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ag.F0A_c2Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dy.F0A_i2Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.di.F0A_a2Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dl.F0A_m2Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ax.F0A_b2Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ah.F0A_cL2Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.au.F0A_iL2Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.df.F0A_aL2Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dk.F0A_mL2Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ay.F0A_bL2Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ag.F0A_c2Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dy.F0A_i2Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dd.F0A_a2Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dk.F0A_m2Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ay.F0A_b2Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ah.F0A_cL2Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.au.F0A_iL2Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.di.F0A_aL2Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_mL2Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ay.F0A_bL2Bf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_instG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ar.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_skeln F0A_cN0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_cLN0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_cN1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_cLN1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_cN2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require q1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_cLN2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b6.F0A_instokC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ar.F0A_bigno OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skeln OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_cN0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cs.F0A_aN0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_cLN0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cs.F0A_aLN0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_cN1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cs.F0A_aN1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_cLN1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cs.F0A_aLN1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_cN2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q1.F0A_aN2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_cLN2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q1.F0A_aLN2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require dj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require dr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require dp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ds.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require du.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dj.F0A_asmC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dr.F0A_aCe0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dp.F0A_aLCe0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dp.F0A_aCf0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dp.F0A_aLCf0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ds.F0A_aCe1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dr.F0A_aLCe1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dr.F0A_aCf1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ds.F0A_aLCf1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.du.F0A_aCe2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.du.F0A_aLCe2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ds.F0A_aCf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.du.F0A_aLCf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require dw.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition QFT (CST XGL : list (Z * Z)) (nW : nat) (A : AA) (Kc : KcA) (rho : valuation) (tp : list word) : assn := ltac2:(tb__ "0|1|
S4cS0S5fVrho;Vtp;S18S14S4aS4bA2M0S15S4aS4bScS3S8VnW;A1S2A3SbS25S0A1VCST;VXGL;VA;VKc;A5A4S17G0A1A3A5").

Definition contFn (nW : nat) (keep : Z -> Prop) (ok : world -> Prop) (A : AA) (Kc : KcA) (rho1 : valuation) (E : axst) (Q : assn) : Prop := ltac2:(tb__ "0|0|
S1cS1aS1aS11S23Q40A1A1S55VA;R4A2S5dVkeep;Vrho1;R4A3S40S0Vok;S2dS0S54VnW;S2S12R6VKc;R5A6VE;R4R3A5VQ;A4F_;F_;FtpE;FrhoE;Frho1';FA';").
Definition econtFn (nW : nat) (keep : Z -> Prop) (A : AA) (Kc : KcA) (rho1 : valuation) (E : axst) (Q : world -> Prop) : Prop := ltac2:(tb__ "0|0|
S1cS1aS1aS11S23Q40A1A1S55VA;R4A2S5dVkeep;Vrho1;R4A3S3fS0S2dS0S54VnW;S2S12R6VKc;R5A6VE;R4R3A5VQ;A3F_;F_;FtpE;FrhoE;Frho1';FA';").

Definition qcondC (A : AA) : Prop := ltac2:(tb__ "0|0|
S2aS29S28S11S1fA1S21VA;A1S17S1fA1A3S28S1S47S19S14S1S1A2S22S3dVA;A1A1A2A1S5cA3A2S29S28S16S20VA;A1S12A3S28S11S1A1S3cVA;A1S17S1A1A3A2A2").

Definition HBIG_stmt (CST XGL : list (Z * Z)) (nW : nat) (q : qvar) (E : axst) : Prop := ltac2:(tb__ "0|1|
S3eOF_;S1cS4S1aS11S23Q40M0A1A1S1S1S1S3bS1OF_;S5R8A1S2fS0RbS2eR9A1A3S43S0RcS2eRaA1A3S28S1S24G0S1bRaPcA2A2R8A3S28S1S24G0S1bRbPdA2A2R8A3S49S14S1S1A2S15S1S1RaR9A4S1dReA1A3S48RbRaA2S28S16S1eR10A1S13A3S38Vq;R11A2S53R12R10ReRdRcRbA6S56R11S39R13R11RfReRdRcA6A2S28S1S3aRdA1S5bA3S1S29S9VCST;R16R1A3SaVCST;VXGL;R16R1A4A2RfR2A1F_;Fa;S35VnW;ReR17R16R15S39R16R14R12R11R10RfA6VE;S30VCST;VXGL;VnW;R16R15R14R13A7A8F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fkeep;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;Fok;").
Definition HBIGE_stmt (CST XGL : list (Z * Z)) (nW : nat) (q : qvar) (E : axst) : Prop := ltac2:(tb__ "0|1|
S1cS4S1aS11S23Q40M0A1A1S1S1S1S3bS1OF_;S5R8A1S28S1S24G0S1bR8PcA2A2R6A3S28S1S24G0S1bR9PdA2A2R6A3S49S14S1S1A2S15S1S1R8R7A4S1dRcA1A3S48R9R8A2S28S16S1eReA1S13A3S38Vq;RfA2S53R10ReRcRbRaR9A6S56RfS39R11RfRdRcRbRaA6A2S28S1S3aRbA1S5bA3S1S29S9VCST;R14R1A3SaVCST;VXGL;R14R1A4A2RdR2A1F_;Fa;S36VnW;RcR14R13S39R14R12R10RfReRdA6VE;S30VCST;VXGL;VnW;R14R13R12R11A7A7F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fkeep;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;").

Definition whole_stmt (CST XGL : list (Z * Z)) (nW : nat) (C : AA -> Prop) : Prop := ltac2:(tb__ "0|2|
S3eOF_;S1cS4S1aS11S23Q40M0A1A1S5R3A1S2fS0R6S2eR4A1A3S43S0R7S2eR5A1A3VC;R7A1S45S24G0S1bR6PdA2A2S5aA2S40S0RaS2dS0S6S25S0A1S8VnW;A1M1S2R9R8A5S7S3G1S2A3R7R6A5S30VCST;VXGL;VnW;R9R8R7R6A7A4F_;F_;F_;F_;F_;Ftp;Frho;FKc;FA;Fok;").
Definition wholeE_stmt (CST XGL : list (Z * Z)) (nW : nat) (C : AA -> Prop) : Prop := ltac2:(tb__ "0|2|
S1cS4S1aS11S23Q40M0A1A1S5R3A1VC;R5A1S45S24G0S1bR4PdA2A2S5aA2S3fS0S2dS0S6S25S0A1S8VnW;A1M1S2R7R6A5S7S3G1S2A3R5R4A5S30VCST;VXGL;VnW;R7R6R5R4A7A3F_;F_;F_;Ftp;Frho;FKc;FA;").
Definition CQ1C (A : AA) : Prop := qcondC A.

Definition top_pure (A : AA) (rho : valuation) : Prop := ltac2:(tb__ "0|1|
S24Q40M0S1bVrho;PcA2A2S1S24G0S1bVrho;PdA2A2S1S2aS49S14S1S1A2S15S1S1R2R1A4S1dVA;A1A3S2aS48R2R1A2S29S38S57VA;A2S29S38S58VA;A2S29S38S59VA;A2S34VA;A1A2A2A2A2A2Tn;Tp;").
Lemma qcond_cases : ltac2:(tb__ "0|0|
S1cS1aS11S23Q40A1A1S5eS1S1S25S0R6R5R4R3A5S49S14S1S1A2S15S1S1R3R2A4S1dR7A1A3S48R4R3A2S29S38S57R9A2S29S38S58R9A2S29S38S59R9A2S34R9A1A2A2A2F_;F_;F_;Fn;Fp;Fmd;Ftp;Frho;FA;").
Proof.
  intros A rho tp md p n HA HL HC. pose proof (qF A rho tp md p n HA HL) as QF. cbn zeta in QF. destruct QF as (_ & _ & _ & _ & _ & QL).
  assert (DC : (aa_cache_inited A = true /\ cache24 A <> []) \/ (aa_cache_inited A = false \/ cache24 A = [])).
  { destruct (aa_cache_inited A); [|right; left; reflexivity]. destruct (cache24 A) eqn:EC; [right; right; reflexivity | left; split; [reflexivity | discriminate]]. }
  destruct (aa_q_thread A) as [|b0 l0] eqn:EQ.
  - destruct DC as [[D1 D2]|D].
    + right; left. unfold qcond. split; [exact EQ|]. split; [exact D1 | exact D2].
    + right; right; right. unfold qcondC. split; [left; exact EQ | exact D].
  - assert (HNE : aa_q_thread A <> []) by (rewrite EQ; discriminate).
    destruct (QL ltac:(discriminate)) as (_ & _ & _ & _ & _ & LE & _).
    assert (LQ : lastq A = last (b0 :: l0) qb_dflt) by (unfold lastq; rewrite EQ; reflexivity).
    rewrite <- LQ in LE.
    destruct (Z_lt_le_dec (Z.of_nat (length (qb_items (lastq A)))) kQuarantineBatchCount) as [LT|GE].
    + left. unfold qcond. split; [exact HNE | exact LT].
    + assert (EK : Z.of_nat (length (qb_items (lastq A))) = kQuarantineBatchCount) by (clear -LE GE; lia).
      destruct DC as [[D1 D2]|D].
      * right; right; left. unfold qcond. split; [exact HNE|]. split; [exact EK|]. split; [exact D1 | exact D2].
      * right; right; right. unfold qcondC. split; [right; exact EK | exact D].
Qed.
Lemma top_pure_of : ltac2:(tb__ "0|0|
S11SfA1S10S1cS4S1aS11S23Q40A1A1S3eS2dS0S6S25S0A1R7R6R5R4A5S7S3R7R6A3R3R2R1A6S37R6R4A2F_;Fw;Ftp;Frho;FKc;FA;Fst;FW;").
Proof.
  intros W st A Kc rho tp w [_ HJ]. destruct HJ as (HA & _ & HL & _). unfold top_pure. cbn zeta.
  assert (HC : blk_cls (bv_unsigned (rw rho 12%positive)) (bv_unsigned (rw rho 13%positive))).
  { pose proof HA as (_ & _ & _ & HRest & _). destruct HRest as (Hsep & _). destruct (Hsep _ _ HL) as (_ & _ & _ & _ & _ & _ & _ & S8). exact S8. }
  split; [exact HL|]. split; [exact HC|]. exact (qcond_cases A rho tp _ _ _ HA HL HC).
Qed.

Section FTop.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTF : ltac2:(tb__ "0|0|
S1S44VCST;R1A2S29S44S60R2A2S2aS45S26R2A2S46R2S27A2A2A2S2cF_;F_;Fa;").
Hypothesis HCSTD : ltac2:(tb__ "0|0|
S1S44VCST;R1A2S2bS62R2A1A1F_;Fa;").
Hypothesis HCSTQ : ltac2:(tb__ "0|0|
S1S44VCST;R1A2S2bS61R2A1A1F_;Fa;").
Hypothesis HCST2 : ltac2:(tb__ "0|0|
S1S44VCST;R1A2S2aS2bS2aS45S26R2A2S46R2S27A2A2A1S2bS2aS45Z180e88R2A2S46R2Z180e8cA2A2A1A2F_;Fa;").

Hypothesis HBIGN_N0 : ltac2:(tb__ "0|0|
S42VCST;VXGL;S13U0S50A5").   Hypothesis HBIGNE_N0 : ltac2:(tb__ "0|0|
S41VCST;VXGL;S13U0S50A5").
Hypothesis HBIGN_N1 : ltac2:(tb__ "0|0|
S42VCST;VXGL;S13U1S51A5").   Hypothesis HBIGNE_N1 : ltac2:(tb__ "0|0|
S41VCST;VXGL;S13U1S51A5").
Hypothesis HBIGN_N2 : ltac2:(tb__ "0|0|
S42VCST;VXGL;S13U2S52A5").   Hypothesis HBIGNE_N2 : ltac2:(tb__ "0|0|
S41VCST;VXGL;S13U2S52A5").
Hypothesis HBIGN_LN0 : ltac2:(tb__ "0|0|
S42VCST;VXGL;S12U0S4dA5").   Hypothesis HBIGNE_LN0 : ltac2:(tb__ "0|0|
S41VCST;VXGL;S12U0S4dA5").
Hypothesis HBIGN_LN1 : ltac2:(tb__ "0|0|
S42VCST;VXGL;S12U1S4eA5").   Hypothesis HBIGNE_LN1 : ltac2:(tb__ "0|0|
S41VCST;VXGL;S12U1S4eA5").
Hypothesis HBIGN_LN2 : ltac2:(tb__ "0|0|
S42VCST;VXGL;S12U2S4fA5").   Hypothesis HBIGNE_LN2 : ltac2:(tb__ "0|0|
S41VCST;VXGL;S12U2S4fA5").

Lemma HQ1C_0 : ltac2:(tb__ "0|0|
S33VCST;VXGL;U0S31A4").
Proof.
  intros ok A Kc rho tp HK HF HP QC Hn.
  apply (triple_pre_pure segsA ok _ _ (top_pure A rho /\ exists tp0 md0, AInvA segsA A rho tp0 md0)).
  { intros w Hw. split; [exact (top_pure_of _ _ A Kc rho tp w Hw)|]. destruct Hw as [_ HJ]. destruct HJ as (HA & _). exists tp, (cfg_model (w_cfg w)). exact HA. }
  intros ((HL & HC & _) & tp0 & md0 & HA0).
  destruct (qcondC_split A rho tp0 md0 HA0 QC) as [QCx|QCx]; destruct (aa_internal_inited A) eqn:Hii; destruct HC as [HLO|HHI].
  - exact (free_lo_Ce_0 CST XGL HCST HXGL HCSTF HCSTD HCSTQ ok A Kc rho tp HK HF HP HLO Hii QCx Hn (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sum_all ok Kc HK HF HP)).
  - exact (free_hi_Ce_0 CST XGL HCST HXGL HCSTF HCSTD HCSTQ ok A Kc rho tp HK HF HP HHI Hii QCx Hn (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sum_all ok Kc HK HF HP)).
  - exact (free_lo_ia0_Ce_0 CST XGL HCST HXGL HCSTF HCSTD HCSTQ HCST2 ok A Kc rho tp HK HF HP HLO Hii QCx Hn (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sum_all ok Kc HK HF HP)).
  - exact (free_hi_ia0_Ce_0 CST XGL HCST HXGL HCSTF HCSTD HCSTQ HCST2 ok A Kc rho tp HK HF HP HHI Hii QCx Hn (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sum_all ok Kc HK HF HP)).
  - exact (free_lo_Cf_0 CST XGL HCST HXGL HCSTF HCSTD HCSTQ ok A Kc rho tp HK HF HP HLO Hii QCx Hn (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sum_all ok Kc HK HF HP)).
  - exact (free_hi_Cf_0 CST XGL HCST HXGL HCSTF HCSTD HCSTQ ok A Kc rho tp HK HF HP HHI Hii QCx Hn (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sum_all ok Kc HK HF HP)).
  - exact (free_lo_ia0_Cf_0 CST XGL HCST HXGL HCSTF HCSTD HCSTQ HCST2 ok A Kc rho tp HK HF HP HLO Hii QCx Hn (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sum_all ok Kc HK HF HP)).
  - exact (free_hi_ia0_Cf_0 CST XGL HCST HXGL HCSTF HCSTD HCSTQ HCST2 ok A Kc rho tp HK HF HP HHI Hii QCx Hn (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sum_all ok Kc HK HF HP)).
Qed.
Lemma HQ1CE_0 : ltac2:(tb__ "0|0|
S32VCST;VXGL;U0S31A4").
Proof.
  intros A Kc rho tp HK QC Hn.
  apply (etriple_pre_pure segsA _ _ (top_pure A rho /\ exists tp0 md0, AInvA segsA A rho tp0 md0)).
  { intros w Hw. split; [exact (top_pure_of _ _ A Kc rho tp w Hw)|]. destruct Hw as [_ HJ]. destruct HJ as (HA & _). exists tp, (cfg_model (w_cfg w)). exact HA. }
  intros ((HL & HC & _) & tp0 & md0 & HA0).
  destruct (qcondC_split A rho tp0 md0 HA0 QC) as [QCx|QCx]; destruct (aa_internal_inited A) eqn:Hii; destruct HC as [HLO|HHI].
  - exact (efree_lo_Ce_0 CST XGL HCST HXGL HCSTF HCSTD HCSTQ A Kc rho tp HK HLO Hii QCx Hn (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sumE_all Kc HK)).
  - exact (efree_hi_Ce_0 CST XGL HCST HXGL HCSTF HCSTD HCSTQ A Kc rho tp HK HHI Hii QCx Hn (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sumE_all Kc HK)).
  - exact (efree_lo_ia0_Ce_0 CST XGL HCST HXGL HCSTF HCSTD HCSTQ HCST2 A Kc rho tp HK HLO Hii QCx Hn (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sumE_all Kc HK)).
  - exact (efree_hi_ia0_Ce_0 CST XGL HCST HXGL HCSTF HCSTD HCSTQ HCST2 A Kc rho tp HK HHI Hii QCx Hn (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sumE_all Kc HK)).
  - exact (efree_lo_Cf_0 CST XGL HCST HXGL HCSTF HCSTD HCSTQ A Kc rho tp HK HLO Hii QCx Hn (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sumE_all Kc HK)).
  - exact (efree_hi_Cf_0 CST XGL HCST HXGL HCSTF HCSTD HCSTQ A Kc rho tp HK HHI Hii QCx Hn (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sumE_all Kc HK)).
  - exact (efree_lo_ia0_Cf_0 CST XGL HCST HXGL HCSTF HCSTD HCSTQ HCST2 A Kc rho tp HK HLO Hii QCx Hn (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sumE_all Kc HK)).
  - exact (efree_hi_ia0_Cf_0 CST XGL HCST HXGL HCSTF HCSTD HCSTQ HCST2 A Kc rho tp HK HHI Hii QCx Hn (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sumE_all Kc HK)).
Qed.
Lemma HQ1C_1 : ltac2:(tb__ "0|0|
S33VCST;VXGL;U1S31A4").
Proof.
  intros ok A Kc rho tp HK HF HP QC Hn.
  apply (triple_pre_pure segsA ok _ _ (top_pure A rho /\ exists tp0 md0, AInvA segsA A rho tp0 md0)).
  { intros w Hw. split; [exact (top_pure_of _ _ A Kc rho tp w Hw)|]. destruct Hw as [_ HJ]. destruct HJ as (HA & _). exists tp, (cfg_model (w_cfg w)). exact HA. }
  intros ((HL & HC & _) & tp0 & md0 & HA0).
  destruct (qcondC_split A rho tp0 md0 HA0 QC) as [QCx|QCx]; destruct (aa_internal_inited A) eqn:Hii; destruct HC as [HLO|HHI].
  - exact (free_lo_Ce_1 CST XGL HCST HXGL HCSTF HCSTD HCSTQ ok A Kc rho tp HK HF HP HLO Hii QCx Hn (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sum_all ok Kc HK HF HP)).
  - exact (free_hi_Ce_1 CST XGL HCST HXGL HCSTF HCSTD HCSTQ ok A Kc rho tp HK HF HP HHI Hii QCx Hn (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sum_all ok Kc HK HF HP)).
  - exact (free_lo_ia0_Ce_1 CST XGL HCST HXGL HCSTF HCSTD HCSTQ HCST2 ok A Kc rho tp HK HF HP HLO Hii QCx Hn (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sum_all ok Kc HK HF HP)).
  - exact (free_hi_ia0_Ce_1 CST XGL HCST HXGL HCSTF HCSTD HCSTQ HCST2 ok A Kc rho tp HK HF HP HHI Hii QCx Hn (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sum_all ok Kc HK HF HP)).
  - exact (free_lo_Cf_1 CST XGL HCST HXGL HCSTF HCSTD HCSTQ ok A Kc rho tp HK HF HP HLO Hii QCx Hn (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sum_all ok Kc HK HF HP)).
  - exact (free_hi_Cf_1 CST XGL HCST HXGL HCSTF HCSTD HCSTQ ok A Kc rho tp HK HF HP HHI Hii QCx Hn (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sum_all ok Kc HK HF HP)).
  - exact (free_lo_ia0_Cf_1 CST XGL HCST HXGL HCSTF HCSTD HCSTQ HCST2 ok A Kc rho tp HK HF HP HLO Hii QCx Hn (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sum_all ok Kc HK HF HP)).
  - exact (free_hi_ia0_Cf_1 CST XGL HCST HXGL HCSTF HCSTD HCSTQ HCST2 ok A Kc rho tp HK HF HP HHI Hii QCx Hn (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sum_all ok Kc HK HF HP)).
Qed.
Lemma HQ1CE_1 : ltac2:(tb__ "0|0|
S32VCST;VXGL;U1S31A4").
Proof.
  intros A Kc rho tp HK QC Hn.
  apply (etriple_pre_pure segsA _ _ (top_pure A rho /\ exists tp0 md0, AInvA segsA A rho tp0 md0)).
  { intros w Hw. split; [exact (top_pure_of _ _ A Kc rho tp w Hw)|]. destruct Hw as [_ HJ]. destruct HJ as (HA & _). exists tp, (cfg_model (w_cfg w)). exact HA. }
  intros ((HL & HC & _) & tp0 & md0 & HA0).
  destruct (qcondC_split A rho tp0 md0 HA0 QC) as [QCx|QCx]; destruct (aa_internal_inited A) eqn:Hii; destruct HC as [HLO|HHI].
  - exact (efree_lo_Ce_1 CST XGL HCST HXGL HCSTF HCSTD HCSTQ A Kc rho tp HK HLO Hii QCx Hn (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sumE_all Kc HK)).
  - exact (efree_hi_Ce_1 CST XGL HCST HXGL HCSTF HCSTD HCSTQ A Kc rho tp HK HHI Hii QCx Hn (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sumE_all Kc HK)).
  - exact (efree_lo_ia0_Ce_1 CST XGL HCST HXGL HCSTF HCSTD HCSTQ HCST2 A Kc rho tp HK HLO Hii QCx Hn (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sumE_all Kc HK)).
  - exact (efree_hi_ia0_Ce_1 CST XGL HCST HXGL HCSTF HCSTD HCSTQ HCST2 A Kc rho tp HK HHI Hii QCx Hn (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sumE_all Kc HK)).
  - exact (efree_lo_Cf_1 CST XGL HCST HXGL HCSTF HCSTD HCSTQ A Kc rho tp HK HLO Hii QCx Hn (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sumE_all Kc HK)).
  - exact (efree_hi_Cf_1 CST XGL HCST HXGL HCSTF HCSTD HCSTQ A Kc rho tp HK HHI Hii QCx Hn (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sumE_all Kc HK)).
  - exact (efree_lo_ia0_Cf_1 CST XGL HCST HXGL HCSTF HCSTD HCSTQ HCST2 A Kc rho tp HK HLO Hii QCx Hn (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sumE_all Kc HK)).
  - exact (efree_hi_ia0_Cf_1 CST XGL HCST HXGL HCSTF HCSTD HCSTQ HCST2 A Kc rho tp HK HHI Hii QCx Hn (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sumE_all Kc HK)).
Qed.
Lemma HQ1C_2 : ltac2:(tb__ "0|0|
S33VCST;VXGL;U2S31A4").
Proof.
  intros ok A Kc rho tp HK HF HP QC Hn.
  apply (triple_pre_pure segsA ok _ _ (top_pure A rho /\ exists tp0 md0, AInvA segsA A rho tp0 md0)).
  { intros w Hw. split; [exact (top_pure_of _ _ A Kc rho tp w Hw)|]. destruct Hw as [_ HJ]. destruct HJ as (HA & _). exists tp, (cfg_model (w_cfg w)). exact HA. }
  intros ((HL & HC & _) & tp0 & md0 & HA0).
  destruct (qcondC_split A rho tp0 md0 HA0 QC) as [QCx|QCx]; destruct (aa_internal_inited A) eqn:Hii; destruct HC as [HLO|HHI].
  - exact (free_lo_Ce_2 CST XGL HCST HXGL HCSTF HCSTD HCSTQ ok A Kc rho tp HK HF HP HLO Hii QCx Hn (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sum_all ok Kc HK HF HP)).
  - exact (free_hi_Ce_2 CST XGL HCST HXGL HCSTF HCSTD HCSTQ ok A Kc rho tp HK HF HP HHI Hii QCx Hn (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sum_all ok Kc HK HF HP)).
  - exact (free_lo_ia0_Ce_2 CST XGL HCST HXGL HCSTF HCSTD HCSTQ HCST2 ok A Kc rho tp HK HF HP HLO Hii QCx Hn (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sum_all ok Kc HK HF HP)).
  - exact (free_hi_ia0_Ce_2 CST XGL HCST HXGL HCSTF HCSTD HCSTQ HCST2 ok A Kc rho tp HK HF HP HHI Hii QCx Hn (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sum_all ok Kc HK HF HP)).
  - exact (free_lo_Cf_2 CST XGL HCST HXGL HCSTF HCSTD HCSTQ ok A Kc rho tp HK HF HP HLO Hii QCx Hn (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sum_all ok Kc HK HF HP)).
  - exact (free_hi_Cf_2 CST XGL HCST HXGL HCSTF HCSTD HCSTQ ok A Kc rho tp HK HF HP HHI Hii QCx Hn (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sum_all ok Kc HK HF HP)).
  - exact (free_lo_ia0_Cf_2 CST XGL HCST HXGL HCSTF HCSTD HCSTQ HCST2 ok A Kc rho tp HK HF HP HLO Hii QCx Hn (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sum_all ok Kc HK HF HP)).
  - exact (free_hi_ia0_Cf_2 CST XGL HCST HXGL HCSTF HCSTD HCSTQ HCST2 ok A Kc rho tp HK HF HP HHI Hii QCx Hn (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sum_all ok Kc HK HF HP)).
Qed.
Lemma HQ1CE_2 : ltac2:(tb__ "0|0|
S32VCST;VXGL;U2S31A4").
Proof.
  intros A Kc rho tp HK QC Hn.
  apply (etriple_pre_pure segsA _ _ (top_pure A rho /\ exists tp0 md0, AInvA segsA A rho tp0 md0)).
  { intros w Hw. split; [exact (top_pure_of _ _ A Kc rho tp w Hw)|]. destruct Hw as [_ HJ]. destruct HJ as (HA & _). exists tp, (cfg_model (w_cfg w)). exact HA. }
  intros ((HL & HC & _) & tp0 & md0 & HA0).
  destruct (qcondC_split A rho tp0 md0 HA0 QC) as [QCx|QCx]; destruct (aa_internal_inited A) eqn:Hii; destruct HC as [HLO|HHI].
  - exact (efree_lo_Ce_2 CST XGL HCST HXGL HCSTF HCSTD HCSTQ A Kc rho tp HK HLO Hii QCx Hn (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sumE_all Kc HK)).
  - exact (efree_hi_Ce_2 CST XGL HCST HXGL HCSTF HCSTD HCSTQ A Kc rho tp HK HHI Hii QCx Hn (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sumE_all Kc HK)).
  - exact (efree_lo_ia0_Ce_2 CST XGL HCST HXGL HCSTF HCSTD HCSTQ HCST2 A Kc rho tp HK HLO Hii QCx Hn (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sumE_all Kc HK)).
  - exact (efree_hi_ia0_Ce_2 CST XGL HCST HXGL HCSTF HCSTD HCSTQ HCST2 A Kc rho tp HK HHI Hii QCx Hn (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sumE_all Kc HK)).
  - exact (efree_lo_Cf_2 CST XGL HCST HXGL HCSTF HCSTD HCSTQ A Kc rho tp HK HLO Hii QCx Hn (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sumE_all Kc HK)).
  - exact (efree_hi_Cf_2 CST XGL HCST HXGL HCSTF HCSTD HCSTQ A Kc rho tp HK HHI Hii QCx Hn (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sumE_all Kc HK)).
  - exact (efree_lo_ia0_Cf_2 CST XGL HCST HXGL HCSTF HCSTD HCSTQ HCST2 A Kc rho tp HK HLO Hii QCx Hn (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sumE_all Kc HK)).
  - exact (efree_hi_ia0_Cf_2 CST XGL HCST HXGL HCSTF HCSTD HCSTQ HCST2 A Kc rho tp HK HHI Hii QCx Hn (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sumE_all Kc HK)).
Qed.

Lemma free_top_0 : ltac2:(tb__ "0|2|
S3eOF_;S1cS4S1aS11S23Q40A1A1S5R3A1S2fS0R6S2eR4A1A3S43S0R7S2eR5A1A3S40S0R8S2dS0S6S25S0A1S8U0M0A1M1S2R7R6A5S7S3G1S2A3R5R4A5S30VCST;VXGL;G0R7R6R5R4A7A4F_;F_;F_;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp HK HF HP.
  apply (triple_pre_pure segsA ok _ _ (top_pure A rho)); [intros w Hw; exact (top_pure_of _ _ A Kc rho tp w Hw)|].
  intros (HL & HC & QCs).
  destruct (Z_le_gt_dec (bv_unsigned (rw rho 13%positive)) kQuarantineMax) as [Hn|Hbig]; [destruct QCs as [QC|[QC|[QC|QC]]] | clear QCs; apply Z.gt_lt in Hbig].
  - destruct (aa_internal_inited A) eqn:Hii; destruct HC as [HLO|HHI].
    * exact (free_lo_0A CST XGL HCST HXGL HCSTF HCSTD HCSTQ ok A Kc rho tp HK HF HP HLO Hii QC (fun t jv HTJ HJM HR => contF_small 0 UStopLe false _ ok A Kc rho _ Ebg_L0A _ big_fact_L0A HR Hn) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sum_all ok Kc HK HF HP)).
    * exact (free_hi_0A CST XGL HCST HXGL HCSTF HCSTD HCSTQ ok A Kc rho tp HK HF HP HHI Hii QC (fun t jv HTJ HJM HR => contF_small 0 UStopLe false _ ok A Kc rho _ Ebg_0A _ big_fact_0A HR Hn) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sum_all ok Kc HK HF HP)).
    * exact (free_lo_ia0_0A CST XGL HCST HXGL HCSTF HCSTD HCSTQ HCST2 ok A Kc rho tp HK HF HP HLO Hii QC (fun rho2 t jv ML HTJ HJM HR => contF_small 0 UStopLe false _ ok (set_inited A) Kc rho2 _ Ebg_L0A _ big_fact_L0A HR (eq_ind_r (fun z => z <= kQuarantineMax) Hn (proj2 (mid_link_pn A rho rho2 _ _ t jv ML)))) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sum_all ok Kc HK HF HP)).
    * exact (free_hi_ia0_0A CST XGL HCST HXGL HCSTF HCSTD HCSTQ HCST2 ok A Kc rho tp HK HF HP HHI Hii QC (fun rho2 t jv ML HTJ HJM HR => contF_small 0 UStopLe false _ ok (set_inited A) Kc rho2 _ Ebg_0A _ big_fact_0A HR (eq_ind_r (fun z => z <= kQuarantineMax) Hn (proj2 (mid_link_pn A rho rho2 _ _ t jv ML)))) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sum_all ok Kc HK HF HP)).
  - destruct (aa_internal_inited A) eqn:Hii; destruct HC as [HLO|HHI].
    * exact (free_lo_0Be CST XGL HCST HXGL HCSTF HCSTD HCSTQ ok A Kc rho tp HK HF HP HLO Hii QC (fun t jv HTJ HJM HR => contF_small 0 UStopLe false _ ok A Kc rho _ Ebg_L0Be _ big_fact_L0Be HR Hn) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sum_all ok Kc HK HF HP)).
    * exact (free_hi_0Be CST XGL HCST HXGL HCSTF HCSTD HCSTQ ok A Kc rho tp HK HF HP HHI Hii QC (fun t jv HTJ HJM HR => contF_small 0 UStopLe false _ ok A Kc rho _ Ebg_0Be _ big_fact_0Be HR Hn) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sum_all ok Kc HK HF HP)).
    * exact (free_lo_ia0_0Be CST XGL HCST HXGL HCSTF HCSTD HCSTQ HCST2 ok A Kc rho tp HK HF HP HLO Hii QC (fun rho2 t jv ML HTJ HJM HR => contF_small 0 UStopLe false _ ok (set_inited A) Kc rho2 _ Ebg_L0Be _ big_fact_L0Be HR (eq_ind_r (fun z => z <= kQuarantineMax) Hn (proj2 (mid_link_pn A rho rho2 _ _ t jv ML)))) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sum_all ok Kc HK HF HP)).
    * exact (free_hi_ia0_0Be CST XGL HCST HXGL HCSTF HCSTD HCSTQ HCST2 ok A Kc rho tp HK HF HP HHI Hii QC (fun rho2 t jv ML HTJ HJM HR => contF_small 0 UStopLe false _ ok (set_inited A) Kc rho2 _ Ebg_0Be _ big_fact_0Be HR (eq_ind_r (fun z => z <= kQuarantineMax) Hn (proj2 (mid_link_pn A rho rho2 _ _ t jv ML)))) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sum_all ok Kc HK HF HP)).
  - destruct (aa_internal_inited A) eqn:Hii; destruct HC as [HLO|HHI].
    * exact (free_lo_0Bf CST XGL HCST HXGL HCSTF HCSTD HCSTQ ok A Kc rho tp HK HF HP HLO Hii QC (fun t jv HTJ HJM HR => contF_small 0 UStopLe false _ ok A Kc rho _ Ebg_L0Bf _ big_fact_L0Bf HR Hn) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sum_all ok Kc HK HF HP)).
    * exact (free_hi_0Bf CST XGL HCST HXGL HCSTF HCSTD HCSTQ ok A Kc rho tp HK HF HP HHI Hii QC (fun t jv HTJ HJM HR => contF_small 0 UStopLe false _ ok A Kc rho _ Ebg_0Bf _ big_fact_0Bf HR Hn) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sum_all ok Kc HK HF HP)).
    * exact (free_lo_ia0_0Bf CST XGL HCST HXGL HCSTF HCSTD HCSTQ HCST2 ok A Kc rho tp HK HF HP HLO Hii QC (fun rho2 t jv ML HTJ HJM HR => contF_small 0 UStopLe false _ ok (set_inited A) Kc rho2 _ Ebg_L0Bf _ big_fact_L0Bf HR (eq_ind_r (fun z => z <= kQuarantineMax) Hn (proj2 (mid_link_pn A rho rho2 _ _ t jv ML)))) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sum_all ok Kc HK HF HP)).
    * exact (free_hi_ia0_0Bf CST XGL HCST HXGL HCSTF HCSTD HCSTQ HCST2 ok A Kc rho tp HK HF HP HHI Hii QC (fun rho2 t jv ML HTJ HJM HR => contF_small 0 UStopLe false _ ok (set_inited A) Kc rho2 _ Ebg_0Bf _ big_fact_0Bf HR (eq_ind_r (fun z => z <= kQuarantineMax) Hn (proj2 (mid_link_pn A rho rho2 _ _ t jv ML)))) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sum_all ok Kc HK HF HP)).
  - exact (HQ1C_0 ok A Kc rho tp HK HF HP QC Hn).
  - destruct (aa_internal_inited A) eqn:Hii; destruct HC as [HLO|HHI].
    + exact (free_lo_N_0 CST XGL HCST HXGL HCSTD ok A Kc rho tp HK HF HP HLO Hii Hbig (fun t jv HTJ HJM HR => HBIGN_LN0 ok A Kc rho tp _ _ t jv _ HK HF HP eq_refl eq_refl HL HLO Hii Hbig HTJ HR HJM (fun a H => H))).
    + exact (free_hi_N_0 CST XGL HCST HXGL HCSTD ok A Kc rho tp HK HF HP HHI Hii Hbig (fun t jv HTJ HJM HR => HBIGN_N0 ok A Kc rho tp _ _ t jv _ HK HF HP eq_refl eq_refl HL HHI Hii Hbig HTJ HR HJM (fun a H => H))).
    + exact (free_lo_ia0_N_0 CST XGL HCST HXGL HCSTD HCST2 ok A Kc rho tp HK HF HP HLO Hii Hbig (fun rho2 t jv ML HTJ HJM HR => HBIGN_LN0 ok (set_inited A) Kc rho2 tp _ _ t jv _ HK HF HP (proj1 (mid_link_pn A rho rho2 _ _ t jv ML)) (proj2 (mid_link_pn A rho rho2 _ _ t jv ML)) HL HLO eq_refl Hbig HTJ HR HJM (fun a H => H))).
    + exact (free_hi_ia0_N_0 CST XGL HCST HXGL HCSTD HCST2 ok A Kc rho tp HK HF HP HHI Hii Hbig (fun rho2 t jv ML HTJ HJM HR => HBIGN_N0 ok (set_inited A) Kc rho2 tp _ _ t jv _ HK HF HP (proj1 (mid_link_pn A rho rho2 _ _ t jv ML)) (proj2 (mid_link_pn A rho rho2 _ _ t jv ML)) HL HHI eq_refl Hbig HTJ HR HJM (fun a H => H))).
Qed.

Lemma efree_top_0 : ltac2:(tb__ "0|2|
S1cS4S1aS11S23Q40A1A1S5R3A1S3fS0S2dS0S6S25S0A1S8U0M0A1M1S2R5R4A5S7S3G1S2A3R3R2A5S30VCST;VXGL;G0R5R4R3R2A7A3F_;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp HK.
  apply (etriple_pre_pure segsA _ _ (top_pure A rho)); [intros w Hw; exact (top_pure_of _ _ A Kc rho tp w Hw)|].
  intros (HL & HC & QCs).
  destruct (Z_le_gt_dec (bv_unsigned (rw rho 13%positive)) kQuarantineMax) as [Hn|Hbig]; [destruct QCs as [QC|[QC|[QC|QC]]] | clear QCs; apply Z.gt_lt in Hbig].
  - destruct (aa_internal_inited A) eqn:Hii; destruct HC as [HLO|HHI].
    * exact (efree_lo_0A CST XGL HCST HXGL HCSTF HCSTD HCSTQ A Kc rho tp HK HLO Hii QC (fun t jv HTJ HJM HR => econtF_small 0 UStopLe false _ A Kc rho _ Ebg_L0A _ big_fact_L0A HR Hn) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sumE_all Kc HK)).
    * exact (efree_hi_0A CST XGL HCST HXGL HCSTF HCSTD HCSTQ A Kc rho tp HK HHI Hii QC (fun t jv HTJ HJM HR => econtF_small 0 UStopLe false _ A Kc rho _ Ebg_0A _ big_fact_0A HR Hn) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sumE_all Kc HK)).
    * exact (efree_lo_ia0_0A CST XGL HCST HXGL HCSTF HCSTD HCSTQ HCST2 A Kc rho tp HK HLO Hii QC (fun rho2 t jv ML HTJ HJM HR => econtF_small 0 UStopLe false _ (set_inited A) Kc rho2 _ Ebg_L0A _ big_fact_L0A HR (eq_ind_r (fun z => z <= kQuarantineMax) Hn (proj2 (mid_link_pn A rho rho2 _ _ t jv ML)))) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sumE_all Kc HK)).
    * exact (efree_hi_ia0_0A CST XGL HCST HXGL HCSTF HCSTD HCSTQ HCST2 A Kc rho tp HK HHI Hii QC (fun rho2 t jv ML HTJ HJM HR => econtF_small 0 UStopLe false _ (set_inited A) Kc rho2 _ Ebg_0A _ big_fact_0A HR (eq_ind_r (fun z => z <= kQuarantineMax) Hn (proj2 (mid_link_pn A rho rho2 _ _ t jv ML)))) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sumE_all Kc HK)).
  - destruct (aa_internal_inited A) eqn:Hii; destruct HC as [HLO|HHI].
    * exact (efree_lo_0Be CST XGL HCST HXGL HCSTF HCSTD HCSTQ A Kc rho tp HK HLO Hii QC (fun t jv HTJ HJM HR => econtF_small 0 UStopLe false _ A Kc rho _ Ebg_L0Be _ big_fact_L0Be HR Hn) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sumE_all Kc HK)).
    * exact (efree_hi_0Be CST XGL HCST HXGL HCSTF HCSTD HCSTQ A Kc rho tp HK HHI Hii QC (fun t jv HTJ HJM HR => econtF_small 0 UStopLe false _ A Kc rho _ Ebg_0Be _ big_fact_0Be HR Hn) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sumE_all Kc HK)).
    * exact (efree_lo_ia0_0Be CST XGL HCST HXGL HCSTF HCSTD HCSTQ HCST2 A Kc rho tp HK HLO Hii QC (fun rho2 t jv ML HTJ HJM HR => econtF_small 0 UStopLe false _ (set_inited A) Kc rho2 _ Ebg_L0Be _ big_fact_L0Be HR (eq_ind_r (fun z => z <= kQuarantineMax) Hn (proj2 (mid_link_pn A rho rho2 _ _ t jv ML)))) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sumE_all Kc HK)).
    * exact (efree_hi_ia0_0Be CST XGL HCST HXGL HCSTF HCSTD HCSTQ HCST2 A Kc rho tp HK HHI Hii QC (fun rho2 t jv ML HTJ HJM HR => econtF_small 0 UStopLe false _ (set_inited A) Kc rho2 _ Ebg_0Be _ big_fact_0Be HR (eq_ind_r (fun z => z <= kQuarantineMax) Hn (proj2 (mid_link_pn A rho rho2 _ _ t jv ML)))) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sumE_all Kc HK)).
  - destruct (aa_internal_inited A) eqn:Hii; destruct HC as [HLO|HHI].
    * exact (efree_lo_0Bf CST XGL HCST HXGL HCSTF HCSTD HCSTQ A Kc rho tp HK HLO Hii QC (fun t jv HTJ HJM HR => econtF_small 0 UStopLe false _ A Kc rho _ Ebg_L0Bf _ big_fact_L0Bf HR Hn) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sumE_all Kc HK)).
    * exact (efree_hi_0Bf CST XGL HCST HXGL HCSTF HCSTD HCSTQ A Kc rho tp HK HHI Hii QC (fun t jv HTJ HJM HR => econtF_small 0 UStopLe false _ A Kc rho _ Ebg_0Bf _ big_fact_0Bf HR Hn) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sumE_all Kc HK)).
    * exact (efree_lo_ia0_0Bf CST XGL HCST HXGL HCSTF HCSTD HCSTQ HCST2 A Kc rho tp HK HLO Hii QC (fun rho2 t jv ML HTJ HJM HR => econtF_small 0 UStopLe false _ (set_inited A) Kc rho2 _ Ebg_L0Bf _ big_fact_L0Bf HR (eq_ind_r (fun z => z <= kQuarantineMax) Hn (proj2 (mid_link_pn A rho rho2 _ _ t jv ML)))) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sumE_all Kc HK)).
    * exact (efree_hi_ia0_0Bf CST XGL HCST HXGL HCSTF HCSTD HCSTQ HCST2 A Kc rho tp HK HHI Hii QC (fun rho2 t jv ML HTJ HJM HR => econtF_small 0 UStopLe false _ (set_inited A) Kc rho2 _ Ebg_0Bf _ big_fact_0Bf HR (eq_ind_r (fun z => z <= kQuarantineMax) Hn (proj2 (mid_link_pn A rho rho2 _ _ t jv ML)))) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sumE_all Kc HK)).
  - exact (HQ1CE_0 A Kc rho tp HK QC Hn).
  - destruct (aa_internal_inited A) eqn:Hii; destruct HC as [HLO|HHI].
    + exact (efree_lo_N_0 CST XGL HCST HXGL HCSTD A Kc rho tp HK HLO Hii Hbig (fun t jv HTJ HJM HR => HBIGNE_LN0 A Kc rho tp _ _ t jv _ HK eq_refl eq_refl HL HLO Hii Hbig HTJ HR HJM (fun a H => H))).
    + exact (efree_hi_N_0 CST XGL HCST HXGL HCSTD A Kc rho tp HK HHI Hii Hbig (fun t jv HTJ HJM HR => HBIGNE_N0 A Kc rho tp _ _ t jv _ HK eq_refl eq_refl HL HHI Hii Hbig HTJ HR HJM (fun a H => H))).
    + exact (efree_lo_ia0_N_0 CST XGL HCST HXGL HCSTD HCST2 A Kc rho tp HK HLO Hii Hbig (fun rho2 t jv ML HTJ HJM HR => HBIGNE_LN0 (set_inited A) Kc rho2 tp _ _ t jv _ HK (proj1 (mid_link_pn A rho rho2 _ _ t jv ML)) (proj2 (mid_link_pn A rho rho2 _ _ t jv ML)) HL HLO eq_refl Hbig HTJ HR HJM (fun a H => H))).
    + exact (efree_hi_ia0_N_0 CST XGL HCST HXGL HCSTD HCST2 A Kc rho tp HK HHI Hii Hbig (fun rho2 t jv ML HTJ HJM HR => HBIGNE_N0 (set_inited A) Kc rho2 tp _ _ t jv _ HK (proj1 (mid_link_pn A rho rho2 _ _ t jv ML)) (proj2 (mid_link_pn A rho rho2 _ _ t jv ML)) HL HHI eq_refl Hbig HTJ HR HJM (fun a H => H))).
Qed.

Lemma free_top_1 : ltac2:(tb__ "0|2|
S3eOF_;S1cS4S1aS11S23Q40A1A1S5R3A1S2fS0R6S2eR4A1A3S43S0R7S2eR5A1A3S40S0R8S2dS0S6S25S0A1S8U1M0A1M1S2R7R6A5S7S3G1S2A3R5R4A5S30VCST;VXGL;G0R7R6R5R4A7A4F_;F_;F_;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp HK HF HP.
  apply (triple_pre_pure segsA ok _ _ (top_pure A rho)); [intros w Hw; exact (top_pure_of _ _ A Kc rho tp w Hw)|].
  intros (HL & HC & QCs).
  destruct (Z_le_gt_dec (bv_unsigned (rw rho 13%positive)) kQuarantineMax) as [Hn|Hbig]; [destruct QCs as [QC|[QC|[QC|QC]]] | clear QCs; apply Z.gt_lt in Hbig].
  - destruct (aa_internal_inited A) eqn:Hii; destruct HC as [HLO|HHI].
    * exact (free_lo_1A CST XGL HCST HXGL HCSTF HCSTD HCSTQ ok A Kc rho tp HK HF HP HLO Hii QC (fun t jv HTJ HJM HR => contF_small 1 UStopLe false _ ok A Kc rho _ Ebg_L1A _ big_fact_L1A HR Hn) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sum_all ok Kc HK HF HP)).
    * exact (free_hi_1A CST XGL HCST HXGL HCSTF HCSTD HCSTQ ok A Kc rho tp HK HF HP HHI Hii QC (fun t jv HTJ HJM HR => contF_small 1 UStopLe false _ ok A Kc rho _ Ebg_1A _ big_fact_1A HR Hn) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sum_all ok Kc HK HF HP)).
    * exact (free_lo_ia0_1A CST XGL HCST HXGL HCSTF HCSTD HCSTQ HCST2 ok A Kc rho tp HK HF HP HLO Hii QC (fun rho2 t jv ML HTJ HJM HR => contF_small 1 UStopLe false _ ok (set_inited A) Kc rho2 _ Ebg_L1A _ big_fact_L1A HR (eq_ind_r (fun z => z <= kQuarantineMax) Hn (proj2 (mid_link_pn A rho rho2 _ _ t jv ML)))) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sum_all ok Kc HK HF HP)).
    * exact (free_hi_ia0_1A CST XGL HCST HXGL HCSTF HCSTD HCSTQ HCST2 ok A Kc rho tp HK HF HP HHI Hii QC (fun rho2 t jv ML HTJ HJM HR => contF_small 1 UStopLe false _ ok (set_inited A) Kc rho2 _ Ebg_1A _ big_fact_1A HR (eq_ind_r (fun z => z <= kQuarantineMax) Hn (proj2 (mid_link_pn A rho rho2 _ _ t jv ML)))) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sum_all ok Kc HK HF HP)).
  - destruct (aa_internal_inited A) eqn:Hii; destruct HC as [HLO|HHI].
    * exact (free_lo_1Be CST XGL HCST HXGL HCSTF HCSTD HCSTQ ok A Kc rho tp HK HF HP HLO Hii QC (fun t jv HTJ HJM HR => contF_small 1 UStopLe false _ ok A Kc rho _ Ebg_L1Be _ big_fact_L1Be HR Hn) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sum_all ok Kc HK HF HP)).
    * exact (free_hi_1Be CST XGL HCST HXGL HCSTF HCSTD HCSTQ ok A Kc rho tp HK HF HP HHI Hii QC (fun t jv HTJ HJM HR => contF_small 1 UStopLe false _ ok A Kc rho _ Ebg_1Be _ big_fact_1Be HR Hn) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sum_all ok Kc HK HF HP)).
    * exact (free_lo_ia0_1Be CST XGL HCST HXGL HCSTF HCSTD HCSTQ HCST2 ok A Kc rho tp HK HF HP HLO Hii QC (fun rho2 t jv ML HTJ HJM HR => contF_small 1 UStopLe false _ ok (set_inited A) Kc rho2 _ Ebg_L1Be _ big_fact_L1Be HR (eq_ind_r (fun z => z <= kQuarantineMax) Hn (proj2 (mid_link_pn A rho rho2 _ _ t jv ML)))) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sum_all ok Kc HK HF HP)).
    * exact (free_hi_ia0_1Be CST XGL HCST HXGL HCSTF HCSTD HCSTQ HCST2 ok A Kc rho tp HK HF HP HHI Hii QC (fun rho2 t jv ML HTJ HJM HR => contF_small 1 UStopLe false _ ok (set_inited A) Kc rho2 _ Ebg_1Be _ big_fact_1Be HR (eq_ind_r (fun z => z <= kQuarantineMax) Hn (proj2 (mid_link_pn A rho rho2 _ _ t jv ML)))) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sum_all ok Kc HK HF HP)).
  - destruct (aa_internal_inited A) eqn:Hii; destruct HC as [HLO|HHI].
    * exact (free_lo_1Bf CST XGL HCST HXGL HCSTF HCSTD HCSTQ ok A Kc rho tp HK HF HP HLO Hii QC (fun t jv HTJ HJM HR => contF_small 1 UStopLe false _ ok A Kc rho _ Ebg_L1Bf _ big_fact_L1Bf HR Hn) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sum_all ok Kc HK HF HP)).
    * exact (free_hi_1Bf CST XGL HCST HXGL HCSTF HCSTD HCSTQ ok A Kc rho tp HK HF HP HHI Hii QC (fun t jv HTJ HJM HR => contF_small 1 UStopLe false _ ok A Kc rho _ Ebg_1Bf _ big_fact_1Bf HR Hn) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sum_all ok Kc HK HF HP)).
    * exact (free_lo_ia0_1Bf CST XGL HCST HXGL HCSTF HCSTD HCSTQ HCST2 ok A Kc rho tp HK HF HP HLO Hii QC (fun rho2 t jv ML HTJ HJM HR => contF_small 1 UStopLe false _ ok (set_inited A) Kc rho2 _ Ebg_L1Bf _ big_fact_L1Bf HR (eq_ind_r (fun z => z <= kQuarantineMax) Hn (proj2 (mid_link_pn A rho rho2 _ _ t jv ML)))) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sum_all ok Kc HK HF HP)).
    * exact (free_hi_ia0_1Bf CST XGL HCST HXGL HCSTF HCSTD HCSTQ HCST2 ok A Kc rho tp HK HF HP HHI Hii QC (fun rho2 t jv ML HTJ HJM HR => contF_small 1 UStopLe false _ ok (set_inited A) Kc rho2 _ Ebg_1Bf _ big_fact_1Bf HR (eq_ind_r (fun z => z <= kQuarantineMax) Hn (proj2 (mid_link_pn A rho rho2 _ _ t jv ML)))) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sum_all ok Kc HK HF HP)).
  - exact (HQ1C_1 ok A Kc rho tp HK HF HP QC Hn).
  - destruct (aa_internal_inited A) eqn:Hii; destruct HC as [HLO|HHI].
    + exact (free_lo_N_1 CST XGL HCST HXGL HCSTD ok A Kc rho tp HK HF HP HLO Hii Hbig (fun t jv HTJ HJM HR => HBIGN_LN1 ok A Kc rho tp _ _ t jv _ HK HF HP eq_refl eq_refl HL HLO Hii Hbig HTJ HR HJM (fun a H => H))).
    + exact (free_hi_N_1 CST XGL HCST HXGL HCSTD ok A Kc rho tp HK HF HP HHI Hii Hbig (fun t jv HTJ HJM HR => HBIGN_N1 ok A Kc rho tp _ _ t jv _ HK HF HP eq_refl eq_refl HL HHI Hii Hbig HTJ HR HJM (fun a H => H))).
    + exact (free_lo_ia0_N_1 CST XGL HCST HXGL HCSTD HCST2 ok A Kc rho tp HK HF HP HLO Hii Hbig (fun rho2 t jv ML HTJ HJM HR => HBIGN_LN1 ok (set_inited A) Kc rho2 tp _ _ t jv _ HK HF HP (proj1 (mid_link_pn A rho rho2 _ _ t jv ML)) (proj2 (mid_link_pn A rho rho2 _ _ t jv ML)) HL HLO eq_refl Hbig HTJ HR HJM (fun a H => H))).
    + exact (free_hi_ia0_N_1 CST XGL HCST HXGL HCSTD HCST2 ok A Kc rho tp HK HF HP HHI Hii Hbig (fun rho2 t jv ML HTJ HJM HR => HBIGN_N1 ok (set_inited A) Kc rho2 tp _ _ t jv _ HK HF HP (proj1 (mid_link_pn A rho rho2 _ _ t jv ML)) (proj2 (mid_link_pn A rho rho2 _ _ t jv ML)) HL HHI eq_refl Hbig HTJ HR HJM (fun a H => H))).
Qed.

Lemma efree_top_1 : ltac2:(tb__ "0|2|
S1cS4S1aS11S23Q40A1A1S5R3A1S3fS0S2dS0S6S25S0A1S8U1M0A1M1S2R5R4A5S7S3G1S2A3R3R2A5S30VCST;VXGL;G0R5R4R3R2A7A3F_;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp HK.
  apply (etriple_pre_pure segsA _ _ (top_pure A rho)); [intros w Hw; exact (top_pure_of _ _ A Kc rho tp w Hw)|].
  intros (HL & HC & QCs).
  destruct (Z_le_gt_dec (bv_unsigned (rw rho 13%positive)) kQuarantineMax) as [Hn|Hbig]; [destruct QCs as [QC|[QC|[QC|QC]]] | clear QCs; apply Z.gt_lt in Hbig].
  - destruct (aa_internal_inited A) eqn:Hii; destruct HC as [HLO|HHI].
    * exact (efree_lo_1A CST XGL HCST HXGL HCSTF HCSTD HCSTQ A Kc rho tp HK HLO Hii QC (fun t jv HTJ HJM HR => econtF_small 1 UStopLe false _ A Kc rho _ Ebg_L1A _ big_fact_L1A HR Hn) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sumE_all Kc HK)).
    * exact (efree_hi_1A CST XGL HCST HXGL HCSTF HCSTD HCSTQ A Kc rho tp HK HHI Hii QC (fun t jv HTJ HJM HR => econtF_small 1 UStopLe false _ A Kc rho _ Ebg_1A _ big_fact_1A HR Hn) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sumE_all Kc HK)).
    * exact (efree_lo_ia0_1A CST XGL HCST HXGL HCSTF HCSTD HCSTQ HCST2 A Kc rho tp HK HLO Hii QC (fun rho2 t jv ML HTJ HJM HR => econtF_small 1 UStopLe false _ (set_inited A) Kc rho2 _ Ebg_L1A _ big_fact_L1A HR (eq_ind_r (fun z => z <= kQuarantineMax) Hn (proj2 (mid_link_pn A rho rho2 _ _ t jv ML)))) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sumE_all Kc HK)).
    * exact (efree_hi_ia0_1A CST XGL HCST HXGL HCSTF HCSTD HCSTQ HCST2 A Kc rho tp HK HHI Hii QC (fun rho2 t jv ML HTJ HJM HR => econtF_small 1 UStopLe false _ (set_inited A) Kc rho2 _ Ebg_1A _ big_fact_1A HR (eq_ind_r (fun z => z <= kQuarantineMax) Hn (proj2 (mid_link_pn A rho rho2 _ _ t jv ML)))) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sumE_all Kc HK)).
  - destruct (aa_internal_inited A) eqn:Hii; destruct HC as [HLO|HHI].
    * exact (efree_lo_1Be CST XGL HCST HXGL HCSTF HCSTD HCSTQ A Kc rho tp HK HLO Hii QC (fun t jv HTJ HJM HR => econtF_small 1 UStopLe false _ A Kc rho _ Ebg_L1Be _ big_fact_L1Be HR Hn) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sumE_all Kc HK)).
    * exact (efree_hi_1Be CST XGL HCST HXGL HCSTF HCSTD HCSTQ A Kc rho tp HK HHI Hii QC (fun t jv HTJ HJM HR => econtF_small 1 UStopLe false _ A Kc rho _ Ebg_1Be _ big_fact_1Be HR Hn) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sumE_all Kc HK)).
    * exact (efree_lo_ia0_1Be CST XGL HCST HXGL HCSTF HCSTD HCSTQ HCST2 A Kc rho tp HK HLO Hii QC (fun rho2 t jv ML HTJ HJM HR => econtF_small 1 UStopLe false _ (set_inited A) Kc rho2 _ Ebg_L1Be _ big_fact_L1Be HR (eq_ind_r (fun z => z <= kQuarantineMax) Hn (proj2 (mid_link_pn A rho rho2 _ _ t jv ML)))) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sumE_all Kc HK)).
    * exact (efree_hi_ia0_1Be CST XGL HCST HXGL HCSTF HCSTD HCSTQ HCST2 A Kc rho tp HK HHI Hii QC (fun rho2 t jv ML HTJ HJM HR => econtF_small 1 UStopLe false _ (set_inited A) Kc rho2 _ Ebg_1Be _ big_fact_1Be HR (eq_ind_r (fun z => z <= kQuarantineMax) Hn (proj2 (mid_link_pn A rho rho2 _ _ t jv ML)))) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sumE_all Kc HK)).
  - destruct (aa_internal_inited A) eqn:Hii; destruct HC as [HLO|HHI].
    * exact (efree_lo_1Bf CST XGL HCST HXGL HCSTF HCSTD HCSTQ A Kc rho tp HK HLO Hii QC (fun t jv HTJ HJM HR => econtF_small 1 UStopLe false _ A Kc rho _ Ebg_L1Bf _ big_fact_L1Bf HR Hn) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sumE_all Kc HK)).
    * exact (efree_hi_1Bf CST XGL HCST HXGL HCSTF HCSTD HCSTQ A Kc rho tp HK HHI Hii QC (fun t jv HTJ HJM HR => econtF_small 1 UStopLe false _ A Kc rho _ Ebg_1Bf _ big_fact_1Bf HR Hn) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sumE_all Kc HK)).
    * exact (efree_lo_ia0_1Bf CST XGL HCST HXGL HCSTF HCSTD HCSTQ HCST2 A Kc rho tp HK HLO Hii QC (fun rho2 t jv ML HTJ HJM HR => econtF_small 1 UStopLe false _ (set_inited A) Kc rho2 _ Ebg_L1Bf _ big_fact_L1Bf HR (eq_ind_r (fun z => z <= kQuarantineMax) Hn (proj2 (mid_link_pn A rho rho2 _ _ t jv ML)))) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sumE_all Kc HK)).
    * exact (efree_hi_ia0_1Bf CST XGL HCST HXGL HCSTF HCSTD HCSTQ HCST2 A Kc rho tp HK HHI Hii QC (fun rho2 t jv ML HTJ HJM HR => econtF_small 1 UStopLe false _ (set_inited A) Kc rho2 _ Ebg_1Bf _ big_fact_1Bf HR (eq_ind_r (fun z => z <= kQuarantineMax) Hn (proj2 (mid_link_pn A rho rho2 _ _ t jv ML)))) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sumE_all Kc HK)).
  - exact (HQ1CE_1 A Kc rho tp HK QC Hn).
  - destruct (aa_internal_inited A) eqn:Hii; destruct HC as [HLO|HHI].
    + exact (efree_lo_N_1 CST XGL HCST HXGL HCSTD A Kc rho tp HK HLO Hii Hbig (fun t jv HTJ HJM HR => HBIGNE_LN1 A Kc rho tp _ _ t jv _ HK eq_refl eq_refl HL HLO Hii Hbig HTJ HR HJM (fun a H => H))).
    + exact (efree_hi_N_1 CST XGL HCST HXGL HCSTD A Kc rho tp HK HHI Hii Hbig (fun t jv HTJ HJM HR => HBIGNE_N1 A Kc rho tp _ _ t jv _ HK eq_refl eq_refl HL HHI Hii Hbig HTJ HR HJM (fun a H => H))).
    + exact (efree_lo_ia0_N_1 CST XGL HCST HXGL HCSTD HCST2 A Kc rho tp HK HLO Hii Hbig (fun rho2 t jv ML HTJ HJM HR => HBIGNE_LN1 (set_inited A) Kc rho2 tp _ _ t jv _ HK (proj1 (mid_link_pn A rho rho2 _ _ t jv ML)) (proj2 (mid_link_pn A rho rho2 _ _ t jv ML)) HL HLO eq_refl Hbig HTJ HR HJM (fun a H => H))).
    + exact (efree_hi_ia0_N_1 CST XGL HCST HXGL HCSTD HCST2 A Kc rho tp HK HHI Hii Hbig (fun rho2 t jv ML HTJ HJM HR => HBIGNE_N1 (set_inited A) Kc rho2 tp _ _ t jv _ HK (proj1 (mid_link_pn A rho rho2 _ _ t jv ML)) (proj2 (mid_link_pn A rho rho2 _ _ t jv ML)) HL HHI eq_refl Hbig HTJ HR HJM (fun a H => H))).
Qed.

Lemma free_top_2 : ltac2:(tb__ "0|2|
S3eOF_;S1cS4S1aS11S23Q40A1A1S5R3A1S2fS0R6S2eR4A1A3S43S0R7S2eR5A1A3S40S0R8S2dS0S6S25S0A1S8U2M0A1M1S2R7R6A5S7S3G1S2A3R5R4A5S30VCST;VXGL;G0R7R6R5R4A7A4F_;F_;F_;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp HK HF HP.
  apply (triple_pre_pure segsA ok _ _ (top_pure A rho)); [intros w Hw; exact (top_pure_of _ _ A Kc rho tp w Hw)|].
  intros (HL & HC & QCs).
  destruct (Z_le_gt_dec (bv_unsigned (rw rho 13%positive)) kQuarantineMax) as [Hn|Hbig]; [destruct QCs as [QC|[QC|[QC|QC]]] | clear QCs; apply Z.gt_lt in Hbig].
  - destruct (aa_internal_inited A) eqn:Hii; destruct HC as [HLO|HHI].
    * exact (free_lo_2A CST XGL HCST HXGL HCSTF HCSTD HCSTQ ok A Kc rho tp HK HF HP HLO Hii QC (fun t jv HTJ HJM HR => contF_small 2 UStopLe false _ ok A Kc rho _ Ebg_L2A _ big_fact_L2A HR Hn) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sum_all ok Kc HK HF HP)).
    * exact (free_hi_2A CST XGL HCST HXGL HCSTF HCSTD HCSTQ ok A Kc rho tp HK HF HP HHI Hii QC (fun t jv HTJ HJM HR => contF_small 2 UStopLe false _ ok A Kc rho _ Ebg_2A _ big_fact_2A HR Hn) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sum_all ok Kc HK HF HP)).
    * exact (free_lo_ia0_2A CST XGL HCST HXGL HCSTF HCSTD HCSTQ HCST2 ok A Kc rho tp HK HF HP HLO Hii QC (fun rho2 t jv ML HTJ HJM HR => contF_small 2 UStopLe false _ ok (set_inited A) Kc rho2 _ Ebg_L2A _ big_fact_L2A HR (eq_ind_r (fun z => z <= kQuarantineMax) Hn (proj2 (mid_link_pn A rho rho2 _ _ t jv ML)))) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sum_all ok Kc HK HF HP)).
    * exact (free_hi_ia0_2A CST XGL HCST HXGL HCSTF HCSTD HCSTQ HCST2 ok A Kc rho tp HK HF HP HHI Hii QC (fun rho2 t jv ML HTJ HJM HR => contF_small 2 UStopLe false _ ok (set_inited A) Kc rho2 _ Ebg_2A _ big_fact_2A HR (eq_ind_r (fun z => z <= kQuarantineMax) Hn (proj2 (mid_link_pn A rho rho2 _ _ t jv ML)))) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sum_all ok Kc HK HF HP)).
  - destruct (aa_internal_inited A) eqn:Hii; destruct HC as [HLO|HHI].
    * exact (free_lo_2Be CST XGL HCST HXGL HCSTF HCSTD HCSTQ ok A Kc rho tp HK HF HP HLO Hii QC (fun t jv HTJ HJM HR => contF_small 2 UStopLe false _ ok A Kc rho _ Ebg_L2Be _ big_fact_L2Be HR Hn) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sum_all ok Kc HK HF HP)).
    * exact (free_hi_2Be CST XGL HCST HXGL HCSTF HCSTD HCSTQ ok A Kc rho tp HK HF HP HHI Hii QC (fun t jv HTJ HJM HR => contF_small 2 UStopLe false _ ok A Kc rho _ Ebg_2Be _ big_fact_2Be HR Hn) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sum_all ok Kc HK HF HP)).
    * exact (free_lo_ia0_2Be CST XGL HCST HXGL HCSTF HCSTD HCSTQ HCST2 ok A Kc rho tp HK HF HP HLO Hii QC (fun rho2 t jv ML HTJ HJM HR => contF_small 2 UStopLe false _ ok (set_inited A) Kc rho2 _ Ebg_L2Be _ big_fact_L2Be HR (eq_ind_r (fun z => z <= kQuarantineMax) Hn (proj2 (mid_link_pn A rho rho2 _ _ t jv ML)))) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sum_all ok Kc HK HF HP)).
    * exact (free_hi_ia0_2Be CST XGL HCST HXGL HCSTF HCSTD HCSTQ HCST2 ok A Kc rho tp HK HF HP HHI Hii QC (fun rho2 t jv ML HTJ HJM HR => contF_small 2 UStopLe false _ ok (set_inited A) Kc rho2 _ Ebg_2Be _ big_fact_2Be HR (eq_ind_r (fun z => z <= kQuarantineMax) Hn (proj2 (mid_link_pn A rho rho2 _ _ t jv ML)))) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sum_all ok Kc HK HF HP)).
  - destruct (aa_internal_inited A) eqn:Hii; destruct HC as [HLO|HHI].
    * exact (free_lo_2Bf CST XGL HCST HXGL HCSTF HCSTD HCSTQ ok A Kc rho tp HK HF HP HLO Hii QC (fun t jv HTJ HJM HR => contF_small 2 UStopLe false _ ok A Kc rho _ Ebg_L2Bf _ big_fact_L2Bf HR Hn) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sum_all ok Kc HK HF HP)).
    * exact (free_hi_2Bf CST XGL HCST HXGL HCSTF HCSTD HCSTQ ok A Kc rho tp HK HF HP HHI Hii QC (fun t jv HTJ HJM HR => contF_small 2 UStopLe false _ ok A Kc rho _ Ebg_2Bf _ big_fact_2Bf HR Hn) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sum_all ok Kc HK HF HP)).
    * exact (free_lo_ia0_2Bf CST XGL HCST HXGL HCSTF HCSTD HCSTQ HCST2 ok A Kc rho tp HK HF HP HLO Hii QC (fun rho2 t jv ML HTJ HJM HR => contF_small 2 UStopLe false _ ok (set_inited A) Kc rho2 _ Ebg_L2Bf _ big_fact_L2Bf HR (eq_ind_r (fun z => z <= kQuarantineMax) Hn (proj2 (mid_link_pn A rho rho2 _ _ t jv ML)))) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sum_all ok Kc HK HF HP)).
    * exact (free_hi_ia0_2Bf CST XGL HCST HXGL HCSTF HCSTD HCSTQ HCST2 ok A Kc rho tp HK HF HP HHI Hii QC (fun rho2 t jv ML HTJ HJM HR => contF_small 2 UStopLe false _ ok (set_inited A) Kc rho2 _ Ebg_2Bf _ big_fact_2Bf HR (eq_ind_r (fun z => z <= kQuarantineMax) Hn (proj2 (mid_link_pn A rho rho2 _ _ t jv ML)))) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sum_all ok Kc HK HF HP)).
  - exact (HQ1C_2 ok A Kc rho tp HK HF HP QC Hn).
  - destruct (aa_internal_inited A) eqn:Hii; destruct HC as [HLO|HHI].
    + exact (free_lo_N_2 CST XGL HCST HXGL HCSTD ok A Kc rho tp HK HF HP HLO Hii Hbig (fun t jv HTJ HJM HR => HBIGN_LN2 ok A Kc rho tp _ _ t jv _ HK HF HP eq_refl eq_refl HL HLO Hii Hbig HTJ HR HJM (fun a H => H))).
    + exact (free_hi_N_2 CST XGL HCST HXGL HCSTD ok A Kc rho tp HK HF HP HHI Hii Hbig (fun t jv HTJ HJM HR => HBIGN_N2 ok A Kc rho tp _ _ t jv _ HK HF HP eq_refl eq_refl HL HHI Hii Hbig HTJ HR HJM (fun a H => H))).
    + exact (free_lo_ia0_N_2 CST XGL HCST HXGL HCSTD HCST2 ok A Kc rho tp HK HF HP HLO Hii Hbig (fun rho2 t jv ML HTJ HJM HR => HBIGN_LN2 ok (set_inited A) Kc rho2 tp _ _ t jv _ HK HF HP (proj1 (mid_link_pn A rho rho2 _ _ t jv ML)) (proj2 (mid_link_pn A rho rho2 _ _ t jv ML)) HL HLO eq_refl Hbig HTJ HR HJM (fun a H => H))).
    + exact (free_hi_ia0_N_2 CST XGL HCST HXGL HCSTD HCST2 ok A Kc rho tp HK HF HP HHI Hii Hbig (fun rho2 t jv ML HTJ HJM HR => HBIGN_N2 ok (set_inited A) Kc rho2 tp _ _ t jv _ HK HF HP (proj1 (mid_link_pn A rho rho2 _ _ t jv ML)) (proj2 (mid_link_pn A rho rho2 _ _ t jv ML)) HL HHI eq_refl Hbig HTJ HR HJM (fun a H => H))).
Qed.

Lemma efree_top_2 : ltac2:(tb__ "0|2|
S1cS4S1aS11S23Q40A1A1S5R3A1S3fS0S2dS0S6S25S0A1S8U2M0A1M1S2R5R4A5S7S3G1S2A3R3R2A5S30VCST;VXGL;G0R5R4R3R2A7A3F_;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp HK.
  apply (etriple_pre_pure segsA _ _ (top_pure A rho)); [intros w Hw; exact (top_pure_of _ _ A Kc rho tp w Hw)|].
  intros (HL & HC & QCs).
  destruct (Z_le_gt_dec (bv_unsigned (rw rho 13%positive)) kQuarantineMax) as [Hn|Hbig]; [destruct QCs as [QC|[QC|[QC|QC]]] | clear QCs; apply Z.gt_lt in Hbig].
  - destruct (aa_internal_inited A) eqn:Hii; destruct HC as [HLO|HHI].
    * exact (efree_lo_2A CST XGL HCST HXGL HCSTF HCSTD HCSTQ A Kc rho tp HK HLO Hii QC (fun t jv HTJ HJM HR => econtF_small 2 UStopLe false _ A Kc rho _ Ebg_L2A _ big_fact_L2A HR Hn) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sumE_all Kc HK)).
    * exact (efree_hi_2A CST XGL HCST HXGL HCSTF HCSTD HCSTQ A Kc rho tp HK HHI Hii QC (fun t jv HTJ HJM HR => econtF_small 2 UStopLe false _ A Kc rho _ Ebg_2A _ big_fact_2A HR Hn) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sumE_all Kc HK)).
    * exact (efree_lo_ia0_2A CST XGL HCST HXGL HCSTF HCSTD HCSTQ HCST2 A Kc rho tp HK HLO Hii QC (fun rho2 t jv ML HTJ HJM HR => econtF_small 2 UStopLe false _ (set_inited A) Kc rho2 _ Ebg_L2A _ big_fact_L2A HR (eq_ind_r (fun z => z <= kQuarantineMax) Hn (proj2 (mid_link_pn A rho rho2 _ _ t jv ML)))) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sumE_all Kc HK)).
    * exact (efree_hi_ia0_2A CST XGL HCST HXGL HCSTF HCSTD HCSTQ HCST2 A Kc rho tp HK HHI Hii QC (fun rho2 t jv ML HTJ HJM HR => econtF_small 2 UStopLe false _ (set_inited A) Kc rho2 _ Ebg_2A _ big_fact_2A HR (eq_ind_r (fun z => z <= kQuarantineMax) Hn (proj2 (mid_link_pn A rho rho2 _ _ t jv ML)))) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sumE_all Kc HK)).
  - destruct (aa_internal_inited A) eqn:Hii; destruct HC as [HLO|HHI].
    * exact (efree_lo_2Be CST XGL HCST HXGL HCSTF HCSTD HCSTQ A Kc rho tp HK HLO Hii QC (fun t jv HTJ HJM HR => econtF_small 2 UStopLe false _ A Kc rho _ Ebg_L2Be _ big_fact_L2Be HR Hn) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sumE_all Kc HK)).
    * exact (efree_hi_2Be CST XGL HCST HXGL HCSTF HCSTD HCSTQ A Kc rho tp HK HHI Hii QC (fun t jv HTJ HJM HR => econtF_small 2 UStopLe false _ A Kc rho _ Ebg_2Be _ big_fact_2Be HR Hn) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sumE_all Kc HK)).
    * exact (efree_lo_ia0_2Be CST XGL HCST HXGL HCSTF HCSTD HCSTQ HCST2 A Kc rho tp HK HLO Hii QC (fun rho2 t jv ML HTJ HJM HR => econtF_small 2 UStopLe false _ (set_inited A) Kc rho2 _ Ebg_L2Be _ big_fact_L2Be HR (eq_ind_r (fun z => z <= kQuarantineMax) Hn (proj2 (mid_link_pn A rho rho2 _ _ t jv ML)))) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sumE_all Kc HK)).
    * exact (efree_hi_ia0_2Be CST XGL HCST HXGL HCSTF HCSTD HCSTQ HCST2 A Kc rho tp HK HHI Hii QC (fun rho2 t jv ML HTJ HJM HR => econtF_small 2 UStopLe false _ (set_inited A) Kc rho2 _ Ebg_2Be _ big_fact_2Be HR (eq_ind_r (fun z => z <= kQuarantineMax) Hn (proj2 (mid_link_pn A rho rho2 _ _ t jv ML)))) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sumE_all Kc HK)).
  - destruct (aa_internal_inited A) eqn:Hii; destruct HC as [HLO|HHI].
    * exact (efree_lo_2Bf CST XGL HCST HXGL HCSTF HCSTD HCSTQ A Kc rho tp HK HLO Hii QC (fun t jv HTJ HJM HR => econtF_small 2 UStopLe false _ A Kc rho _ Ebg_L2Bf _ big_fact_L2Bf HR Hn) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sumE_all Kc HK)).
    * exact (efree_hi_2Bf CST XGL HCST HXGL HCSTF HCSTD HCSTQ A Kc rho tp HK HHI Hii QC (fun t jv HTJ HJM HR => econtF_small 2 UStopLe false _ A Kc rho _ Ebg_2Bf _ big_fact_2Bf HR Hn) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sumE_all Kc HK)).
    * exact (efree_lo_ia0_2Bf CST XGL HCST HXGL HCSTF HCSTD HCSTQ HCST2 A Kc rho tp HK HLO Hii QC (fun rho2 t jv ML HTJ HJM HR => econtF_small 2 UStopLe false _ (set_inited A) Kc rho2 _ Ebg_L2Bf _ big_fact_L2Bf HR (eq_ind_r (fun z => z <= kQuarantineMax) Hn (proj2 (mid_link_pn A rho rho2 _ _ t jv ML)))) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sumE_all Kc HK)).
    * exact (efree_hi_ia0_2Bf CST XGL HCST HXGL HCSTF HCSTD HCSTQ HCST2 A Kc rho tp HK HHI Hii QC (fun rho2 t jv ML HTJ HJM HR => econtF_small 2 UStopLe false _ (set_inited A) Kc rho2 _ Ebg_2Bf _ big_fact_2Bf HR (eq_ind_r (fun z => z <= kQuarantineMax) Hn (proj2 (mid_link_pn A rho rho2 _ _ t jv ML)))) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dw.SegQ3_close.drain_sumE_all Kc HK)).
  - exact (HQ1CE_2 A Kc rho tp HK QC Hn).
  - destruct (aa_internal_inited A) eqn:Hii; destruct HC as [HLO|HHI].
    + exact (efree_lo_N_2 CST XGL HCST HXGL HCSTD A Kc rho tp HK HLO Hii Hbig (fun t jv HTJ HJM HR => HBIGNE_LN2 A Kc rho tp _ _ t jv _ HK eq_refl eq_refl HL HLO Hii Hbig HTJ HR HJM (fun a H => H))).
    + exact (efree_hi_N_2 CST XGL HCST HXGL HCSTD A Kc rho tp HK HHI Hii Hbig (fun t jv HTJ HJM HR => HBIGNE_N2 A Kc rho tp _ _ t jv _ HK eq_refl eq_refl HL HHI Hii Hbig HTJ HR HJM (fun a H => H))).
    + exact (efree_lo_ia0_N_2 CST XGL HCST HXGL HCSTD HCST2 A Kc rho tp HK HLO Hii Hbig (fun rho2 t jv ML HTJ HJM HR => HBIGNE_LN2 (set_inited A) Kc rho2 tp _ _ t jv _ HK (proj1 (mid_link_pn A rho rho2 _ _ t jv ML)) (proj2 (mid_link_pn A rho rho2 _ _ t jv ML)) HL HLO eq_refl Hbig HTJ HR HJM (fun a H => H))).
    + exact (efree_hi_ia0_N_2 CST XGL HCST HXGL HCSTD HCST2 A Kc rho tp HK HHI Hii Hbig (fun rho2 t jv ML HTJ HJM HR => HBIGNE_N2 (set_inited A) Kc rho2 tp _ _ t jv _ HK (proj1 (mid_link_pn A rho rho2 _ _ t jv ML)) (proj2 (mid_link_pn A rho rho2 _ _ t jv ML)) HL HHI eq_refl Hbig HTJ HR HJM (fun a H => H))).
Qed.

Theorem free_contractA_A : ltac2:(tb__ "0|0|
SdS0S3S25S0A1VCST;VXGL;A5").
Proof.
  apply free_contractA_of_T. intros W st ok A Kc rho tp HS HK HF HP.
  destruct HS as [E|[E|[E|[]]]]; injection E as <- <-; [exact (free_top_0 ok A Kc rho tp HK HF HP) | exact (free_top_1 ok A Kc rho tp HK HF HP) | exact (free_top_2 ok A Kc rho tp HK HF HP)].
Qed.
Theorem free_contractA_ex_A : ltac2:(tb__ "0|0|
SeS0S3S25S0A1VCST;VXGL;A5").
Proof.
  apply free_contractA_ex_of_T. intros W st A Kc rho tp HS HK.
  destruct HS as [E|[E|[E|[]]]]; injection E as <- <-; [exact (efree_top_0 A Kc rho tp HK) | exact (efree_top_1 A Kc rho tp HK) | exact (efree_top_2 A Kc rho tp HK)].
Qed.
End FTop.
