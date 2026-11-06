(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "or"; "ex"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "mul"; "of_nat"; "pow"; "div"; "to_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs"; "it_cls"; "it_ab"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2"; "cls_of"; "QFP"; "@Corelib.Init.Datatypes"; "bool"; "list"; "cons"; "true"; "length"; "prod"; "nat"; "nil"; "pair"; "None"; "app"; "fst"; "option"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rm"; "ss_next"; "rw"; "obj_range"; "sobj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_geom"; "qbatch"; "aa_cache_inited"; "ag_spacebeg"; "cs_cache"; "aa_q_global"; "aa_q_thread"; "budget_bound"; "class_state"; "cs_mapped_free_array"; "mkQB"; "aa_cls"; "ag_thread"; "ageom"; "cs_free_array"; "topG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "view"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "smatchA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel"; "kchunks"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.SegQ3D_inv"; "JRI"; "QP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DrainModel"; "drain_grows"; "drainA"; "drain_cs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.DrainS"; "drain_zone"; "JLD"; "JD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQIF_env"; "qienvF"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "rho_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "call_linkP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "SHADOW_BAND_HI"; "kQuarantineMin"; "max_count"; "SHADOW_BAND_LO"; "free_array"; "kFreeArraySize"; "HIGH_SHADOW_END"; "Sh"; "kFreeArrayMapSize"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.InvQ"; "K0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iq.SegQ3D_qi_arith"; "vb_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kw.SegQIF_glue"; "ENVM"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQIF_mdefs"; "PostD"; "PreD"; "m_C1"; "m_RF"; "m_T1f"; "m_sF"; "mcert"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "J_ofPA"; "LQPA"; "import_okPA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget"; "LIMIT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jo.SegQF_lib"; "DZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQIF_cont"; "DZM"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQtr"; "TR"; "TRP"; "@Corelib.Init.Peano"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m0.SegQIF_call"; "FLM"; "fr_okG"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundL SymSoundV SymSoundM SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3 SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocInv Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Inv Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ_defs SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ie.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQtr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ3R_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require il.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require im.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require id.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require io.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iu.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.SegQ3_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.SegQ3D_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.SegQ3G_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQtr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.SegQ3R_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ3R_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.SegQ3DM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.SegQ3D_inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.im.SegQ3D_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.SegQI_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.id.SegQI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQI_side OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.SegQC_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SegQ3D_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SegQ3D_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SegQ3D_qi_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iq.SegQ3D_qi_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iq.SegQ3D_qc_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m9.SegQ3D_qc_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.SegQ3D_qc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import F0A_zones.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require je.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ3M_glue SegQ_wf4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQS_glue SegQS_scan SegQS_lib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jt.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillModel DrainModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_drain DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ls.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQIF_env SegQIF_mdefs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lz.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kw.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SegQ_wf3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.SegQ3D_qip OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.je.SegQ3D_qiq OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ3M_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.SegQS_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQS_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQS_scan OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQS_lib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jk.SegQS_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jj.SegQS_k OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jt.SegQS_tail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jc.InvQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jd.InvQ4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jd.InvQ6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jb.InvQ9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DrainModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.DrainS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.DrainSG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jo.SegQF_lib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.InvQ7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_drain OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ls.SegQCF_call OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i9.SegQIP_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iq.SegQIF_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQIF_env OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQIF_mdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lz.SegQIF_zones OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kw.SegQIF_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m0.SegQIF_call.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition DZM (A : AA) (c z : Z) : Prop := ltac2:(tb__ "0|3|
S34S28VA;A1M0A1S0S2bG0A1S0S4S2S6S7S7R2Zd0A2S9Z50Vc;A2A2M1Vz;A2S8Vz;S7G1Z4A2A2A2S4S2S6S54R1Vc;A2M2Vz;A2S8Vz;S7S7R1SbZ2Z25A2A2Z1000A2A2A2S2S6S57G2A1Vz;A2S8Vz;S50A2A2A2A2TSB;TT;").

Section GeoM.
Variables (A : AA) (it : Z * Z) (r : valuation) (t st : Z).
Hypothesis QE : ltac2:(tb__ "0|0|
S49VA;Vit;Vr;Vt;Vst;A5").

Lemma geoM_nums : ltac2:(tb__ "0|8|
S2bS28VA;A1M0A1S0SeVit;A1S0S2S2S6Z1R1A2S6R1Z1eA2A2S2S1S0S54R2R1A2M1S7S7R2S9R1SbZ2M2Z20A2A2A2M3Ze0000000A2A3S2S6S56R2A2S2S6S7S7R2SbG2Z25A2A2Z1000A2S37G0A1M4A2S2S6G4Z7fffff800000A2S2S6S7S1eS0S0Vit;A3M5S9ScS7S20S0S0Vit;A3Z7A2Z8M6A2G6A2A2G1A2S2S6G3SfVit;A1M7A2S6G7G5A2A2A2A2A2A2A2A2Tc;TSB;").
Proof.
  intros SB c. pose proof QE as [HG HSEP3 HRTC HRIG HGEO HV HCV HIM HSTAT Ht Hst HNF HQP HAU HIN HPR HMU]. unfold qgeo in HGEO.
  pose proof (qf_nums A it r t st QE) as (T0 & T1 & C0 & C1' & S14 & TG & K16).
  destruct HGEO as (C1 & Z1 & Z2 & RZ & RZ16 & EU & N1 & R1 & M1 & U1 & A16 & UN & TOP & S1 & S2 & S3 & N8a & N8b).
  assert (FAv : free_array SB c = SB + c * 2 ^ 32 + 3758096384) by (unfold free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize; lia).
  fold SB c in R1, U1, UN, S2, S14, HMU |- *. unfold kUserSpaceSize, kRegionSize, kFreeArraySize in HMU. unfold HIGH_SHADOW_END.
  split; [exact C1|]. split; [exact FAv|]. rewrite FAv. clear - R1 U1 UN S2 S14 HMU TG EU RZ. repeat split; lia.
Qed.

Lemma dzone_M : ltac2:(tb__ "0|1|
S0S46S28VA;A1SeVit;A1M0S11VA;G0A2R1A4S6dVA;G0R2A3F_;Fz;").
Proof.
  intros z HZ. destruct geoM_nums as (C1 & FAv & S1 & S14 & TG & _). cbv zeta in FAv, S1, S14.
  pose proof (cv_fa_bounds _ _ _ _ _ (qf_hcv A it r t st QE)) as (_ & FB2 & FB3).
  destruct (kchunks_facts _ C1) as (KC & _).
  pose proof (Zle_0_nat (length (cs_free_array (cls_of A (it_cls it))))) as NF0.
  unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.DrainS.drain_zone in HZ. cbv zeta in HZ. unfold DZM. cbv zeta.
  set (SB := ag_spacebeg (aa_geom A)) in *. set (c := it_cls it) in *. set (cs := cls_of A c) in *. set (fa := free_array SB c) in *.
  unfold region_info, kRegionInfoStride, kFreeArraySize, kFreeArrayMapSize, HIGH_SHADOW_END in *. rewrite kSpaceSize_val in HZ.
  destruct HZ as [H|[H|[H|(_ & [H|H])]]].
  - left. lia.
  - right; left. lia.
  - right; left. lia.
  - right; left. lia.
  - right; right. unfold SHADOW_BAND_HI, HIGH_SHADOW_END, Sh, SHADOW_OFF in *.
    pose proof (Z.div_le_mono fa (fa + cs_mapped_free_array cs) 8 ltac:(lia) ltac:(lia)) as D0.
    pose proof (Z.div_le_upper_bound (fa + cs_mapped_free_array cs) 8 (2 ^ 44 - 32768) ltac:(lia) ltac:(lia)) as D1. lia.
Qed.

Lemma floc_outM : ltac2:(tb__ "0|0|
S0S72VA;Vit;R1A3S3S6dVA;SeVit;A1R2A3A1F_;Fz;").
Proof.
  intros z HF HZ. destruct geoM_nums as (C1 & FAv & S1 & S14 & TG & UF & R1 & ABU). cbv zeta in FAv, S1, S14, UF, R1.
  pose proof (qf_nums A it r t st QE) as (T0 & T1 & C0 & C1' & _ & _ & _). pose proof (qf_Sh A it r t st QE) as (SH0 & SH1 & L0 & L1).
  pose proof (qf_wins A it r t st QE) as (WTI & WCI & WTB & WCB & WTC & WTS & WCS).
  unfold FLM in HF. unfold DZM in HZ. cbv zeta in HZ.
  set (SB := ag_spacebeg (aa_geom A)) in *. set (c := it_cls it) in *. set (fa := free_array SB c) in *. set (T := ag_thread (aa_geom A)) in *. set (CTX := ag_ctx (aa_geom A)) in *.
  assert (SHF : Sh (fst it) + (snd it + 7) / 8 <= Sh fa).
  { unfold Sh. pose proof (Z.div_le_mono (fst it + (snd it + 7) / 8 * 8) fa 8 ltac:(lia) UF) as D0. rewrite Z.div_add in D0 by lia. lia. }
  assert (SHL : 0x7fff8000 <= Sh fa) by (unfold Sh, SHADOW_OFF; pose proof (Z.div_pos fa 8 ltac:(unfold HIGH_SHADOW_END in S1; lia) ltac:(lia)); lia).
  rewrite <- L1 in SHF. unfold IMG_LO, IMG_HI, SHADOW_BAND_HI, HIGH_SHADOW_END in *.
  clear - HF HZ C1 FAv S1 S14 TG UF R1 ABU T0 T1 C0 C1' SH0 SH1 L0 WTI WCI WTB WCB WTC WTS WCS SHF SHL. lia.
Qed.
End GeoM.

Lemma fr_okG_loc : ltac2:(tb__ "0|1|
S0OF_;S27S21S26S73R4R3R2R1A4S0S2S6S1eS0S0S25R4R3A2M0A3R1A2S8R1S20S0S0G0A3A2A2R7R2A1F_;Fz;F_;Fo;Frho;FA;FFL;").
Proof.
  intros FL A rho o [(b & lo & hi & cs & -> & L1 & L2 & L3 & CI & B1 & B2 & LOC & _)|(_ & _ & _ & HU)] z Hz.
  - unfold carved in Hz. rewrite obj_range_mk in Hz by lia. cbn [fst snd] in Hz. exact (LOC z Hz).
  - exact (proj1 (HU z Hz)).
Qed.

Section ContM.
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variables (A0 : AA) (rho0 : valuation).
Variables (n : Z) (g vb : bool) (D : mdata).
Hypothesis HC : ltac2:(tb__ "0|0|
S62Vn;Vg;Vvb;VD;A4").

Lemma qif_post_ok : ltac2:(tb__ "0|c|
S27S0S0S19S18S0S0A2M0S14G0A1S14S29A1M1G1S21S14S3bQ40M2A1M3A1M4S14S4bA1M5S63S4aS0S0S21G4G5S4aS1S13S2aR13A1S16A3S1S0S40SeR10A1A1Vn;A3S1S0SaS17S0S2cS11R15SeR11A1M6A2A1A2A1S52G6A1A3S1S13S43SeR12A1M7S11R16G7A2A2Vg;A3S1S13Vvb;S5aR13A1A3S5bVn;R18SeR14A1R10A4S49R19R15R11RcRbA5S1G3S24R12Pd0A2S3cG2S51A2A3S3eS10R13R12S5eVD;A1M8S1bG5S64R11S65R10RfA2A4A5S41S59VKc;A1VA0;Vrho0;R1cR1bR1aR19S15G0R18R17A3R16R15R14R13R12R10AeS4eS23S39S5dVn;Vg;A2M9A1A1S4dS4cR15S5fVD;A1MaS3fR11R14R12A3A3S61VD;A1MbA2ReA3S47R1eVKc;SeR1aA1S4dS4cR16GaS3fR12R15R13A3A3GbA2R15RfReRdRcA9S69R17S3fR13R16R14A3GaGbG9S5cVn;Vg;A2G8R10A8F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd';Ftr';FtpL;FrhoL;Fst;Ft;Fmd;Fms;Ftr;Ftp;Frho;Frest;Ftmp';Fits;Fit;Fnd;Fn0;Fa;FA;").
Proof.
  intros A a n0 nd it its tmp' rest rho tp tr ms md t st rhoL tpL tr' md' HCI Hn HFULL HGR EVB (E200 & E201 & E221 & E222 & E223 & E224 & E225 & ECH) QE E208 Hsm (HK & _) Hag (HKL & HRM & _).
  pose proof (sF_get n g vb D HC 155%positive _ ltac:(unfold SFREF; cbn; tauto)) as W155. pose proof (sF_get n g vb D HC 158%positive _ ltac:(unfold SFREF; cbn; tauto)) as W158.
  pose proof (sF_get n g vb D HC 221%positive _ ltac:(unfold SFREF; cbn; tauto)) as W221.
  destruct (c_XF0 n g vb D HC) as (XP & XC & _ & NXP & _).
  pose proof (C1_pre_holds n g vb D HC rho tp _ Hsm) as HFp.
  pose proof (fr_allM Kc A it rho tp tr md t st HKc HK HCI HFp QE E208 n g vb D HC EVB) as FRA.
  destruct (frame_viewG (FLM A it) A (m_C1 D) _ (m_RF D) rho tp tr ms md Hsm (c_C1objs n g vb D HC) FRA) as (_ & _ & _ & FR4).
  split; [split|split].
  - intros a0 Hin. apply HRM. intros HZ. exact (floc_outM A it rho t st QE _ (proj1 (FR4 a0 Hin)) (dzone_M A it rho t st QE _ HZ)).
  - intros o' oR Ho' HoR. rewrite (c_new n g vb D HC) in Ho'. destruct g; [|destruct Ho']. destruct Ho' as [<-|[]].
    destruct (geoM_nums A it rho t st QE) as (C1 & FAv & S1 & S14 & TG & _). cbv zeta in FAv, S1, S14.
    pose proof (cv_fa_bounds _ _ _ _ _ (qf_hcv A it rho t st QE)) as (_ & FB2 & FB3).
    destruct (qf_hrig A it rho t st QE) as (_ & _ & E155 & _).
    destruct (kchunks_facts _ C1) as (KC & _). rewrite Hn in KC.
    set (SB := ag_spacebeg (aa_geom A)) in *. set (c := it_cls it) in *. set (nf := Z.of_nat (length (cs_free_array (cls_of A c)))) in *. assert (NF0 : 0 <= nf) by (unfold nf; lia).
    assert (EL : forall v, (v < 240)%positive -> rw rhoL v = eval rho (wsub_get (m_sF D) v)).
    { intros v Hv. rewrite <- (proj1 Hag v ltac:(rewrite NXP; exact Hv)). cbn [rw rho_sub]. apply eval_absorb. }
    assert (E155L : rw rhoL 155%positive = Z_to_bv 64 SB) by (rewrite (EL 155%positive eq_refl), W155; exact E155).
    assert (E158L : rw rhoL 158%positive = Z_to_bv 64 c) by (rewrite (EL 158%positive eq_refl), W158; exact E200).
    assert (E221L : rw rhoL 221%positive = Z_to_bv 64 nf) by (rewrite (EL 221%positive eq_refl), W221; exact E221).
    unfold HIGH_SHADOW_END, kFreeArraySize in *.
    assert (Edst : bv_unsigned (eval (rho_sub rhoL []) dst_e) = free_array SB c + 4 * nf).
    { unfold dst_e, fa_e. rewrite U_add, U_add, U_add, !U_sll_lit. unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1.vSB, vNF. cbn [eval rw rho_sub wsub_get]. change V_CLS with 158%positive. rewrite E158L, E155L, E221L, !u64_lit by lia.
      change (32 mod 64) with 32. change (2 mod 64) with 2. unfold M64v. rewrite (Z.mod_small (c * 2 ^ 32)) by lia. rewrite (Z.mod_small (c * 2 ^ 32 + 3758096384)) by lia.
      rewrite (Z.mod_small (SB + (c * 2 ^ 32 + 3758096384))) by lia. rewrite (Z.mod_small (nf * 2 ^ 2)) by lia. rewrite Z.mod_small by lia. rewrite FAv. lia. }
    rewrite obj_range_subst. unfold O_dstD. rewrite obj_range_mk by lia. rewrite Edst.
    apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ls.SegQCF_call.rd_pointwise _ _ _ _ (FLM A it) (fr_okG_loc _ A rho oR (proj1 (Forall_forall _ _) FRA oR HoR))).
    intros z Hz HF. apply (floc_outM A it rho t st QE z HF). unfold DZM. cbv zeta. right; left. fold SB c. rewrite FAv in Hz |- *. lia.
  - intros r0 a0 j oR Hr. rewrite XP in Hr. destruct Hr.
  - intros r0 a0 j Hr. rewrite XC in Hr. destruct Hr.
Qed.

Lemma drainA_clsM : ltac2:(tb__ "0|0|
S27S0S70SdR1A1S17S30S33R2A1A2A2S1S30S11S44R3R2A2R2A2S45R2S11R3R2A2A2A3F_;Fc;FA;").
Proof. intros A c HL. unfold cls_of, nthZ, drainA. cbn [aa_cls]. apply nth_list_upd_same. exact HL. Qed.

Lemma dzone_DZM : ltac2:(tb__ "0|2|
S27S0S0S6Z0M0S2bS28R3A1A1A2S6G0S31S11R4R3A2A1A2S6Z1S40R4A1A2S6S9Z4S7SaS17S0S36S11R6R5A2A1A2A1S40R5A1A2A2S55A2S1S13S43R6S11R7R6A2A2S16A3S6S7S31S11R8R7A2M1A1S58A2S55A2F_;S46S28R8A1R7G1R6A4S6cR9R8R7A3F_;F_;F_;F_;F_;F_;Fz;Fc;FA;").
Proof.
  intros A c z HSB HM0 HKC HN HGRW HZ. unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.DrainS.drain_zone in HZ. cbv zeta in HZ. unfold DZ. cbv zeta.
  pose proof (Zle_0_nat (length (cs_free_array (cls_of A c)))) as NF0.
  unfold kRegionInfoStride, kFreeArraySize, kFreeArrayMapSize in *.
  destruct HZ as [H|[H|[H|(HGW & [H|H])]]].
  - left. lia.
  - right; right; left. lia.
  - right; left. lia.
  - specialize (HGRW HGW). right; right; left. lia.
  - specialize (HGRW HGW). right; right; right. unfold Sh in *. set (fa := free_array (ag_spacebeg (aa_geom A)) c) in *. set (mfa := cs_mapped_free_array (cls_of A c)) in *.
    pose proof (Z.div_le_mono fa (fa + mfa) 8 ltac:(lia) ltac:(lia)) as D0.
    pose proof (Z.div_le_mono (fa + mfa + 32768 * 8) (fa + 536870912) 8 ltac:(lia) ltac:(lia)) as D1. rewrite Z.div_add in D1 by lia. lia.
Qed.
Lemma DZ_QFPM : ltac2:(tb__ "0|0|
S27S27S0S0S2S6Z1R2A2S6R2Z1eA2A2S1S35S28R5A1S28R4A1A3S6cR6R4R3A3S12R6R4A2F_;F_;F_;Fz;Fc;FA0';FA;").
Proof.
  intros A A0' c z Hc EG HZ. unfold DZ in HZ. cbv zeta in HZ. rewrite EG in HZ. unfold QFP. destruct HZ as [H|[H|[H|H]]].
  - right; left. lia.
  - right; right; left. exists c. split; [exact Hc|]. left. exact H.
  - right; right; left. exists c. split; [exact Hc|]. right; left. exact H.
  - right; right; left. exists c. split; [exact Hc|]. right; right. exact H.
Qed.

Lemma qif_exit_core : ltac2:(tb__ "0|14|
S27S0S0S0S19S18S0S0A2M0S14G0A1S14S29A1M1G1S21S14S3bQ40M2A1M3A1M4S14S4bA1M5S63S4aS0S0S21G4S1G1S2eR12A1S1aS29A1A3S1S13S2aR13A1S16A3S42VA0;R14A2S1G1S2dR15A1S15S29S32R14S15G0R10RfA3R13A3S1dS29ReRdA3A3A3S1S0S40SeR11A1A1Vn;A3S1S0SaS17S0S2cS11R17SeR12A1M6A2A1A2A1S52G6A1A3S1S13S43SeR13A1M7S11R18G7A2A2Vg;A3S1S13Vvb;S5aR14A1A3S5bVn;R1aSeR15A1R11A4S49R1bR16R12RdRcA5S1G3S24R13Pd0A2S3cG2S51A2A3S3eS10R14R13S5eVD;A1M8S1bG5S64R12S65R11R10A2A4A5S41S59VKc;A1M9VA0;Vrho0;R1eR1dR1bR1aS15G0R19R18A3R17R16R15R14R13R11AeS21S71S4fR18S3fR14R17R15A3S5fVD;A1MaS61VD;A1MbS39S5dVn;Vg;A2McA1S39G8A1MdS39S5cVn;Vg;A2MeA1R2R11A9S3dS10S67S47R22VKc;SeR1dA1A3S4dS4cR19GaS3fR15R18R16A3A3GbA2R18R12R11A5S6aGbGcGeG8GaA5R3R11R2A6S5S21S21S2S3dS10S41G9VA0;Vrho0;S44R24SeR1fA1A2R23R21R20S15G0R1fR1eA3R1dR1cAaS60VD;A1R1R13R4A6S2S4eS23GdA1R1bR1A3S2S0S3S46S28R25A1SeR20A1MfS11R25GfA2R1A4A1S1S1fS3bQ8A1M10A1M11S38S10S22R3A1R2A3S38S10S22R1dA1R2A3M12A3F_;Fz;S0S2S6S53R1A2S8R1S50A2A2S3S1G11G12S1cG10A1M13A3A1S3S1G11S38S10S22R4A1R3A3G13A3A1F_;F_;Fz;A2A2A2Lrho5;A2F_;F_;Fw';Frho';F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FtpL;FrhoL;Fst;Ft;Fmd;Fms;Ftr;Ftp;Frho;Frest;Ftmp';Fits;Fit;Fnd;Fn0;Fs;Fa;FA;").
Proof.
  intros A a s n0 nd it its tmp' rest rho tp tr ms md t st rhoL tpL HTH HCI HQP HGL Hn HFULL HGR EVB HENV QE E208 Hsm0 HJ0 rho' w' HLK [Hsm' HJ'].
  pose proof HJ0 as (HK & HCB & HRMM & HFRM).
  destruct (c_XF0 n g vb D HC) as (XP & XC & XT & NXP & NXC).
  assert (EG : aa_geom A = aa_geom A0) by (destruct HQP as (ESB & _); unfold same_but_qcs in ESB; rewrite ESB; reflexivity).
  pose proof (smatch_facts_hold _ _ _ _ (proj1 Hsm0)) as HFa.
  pose proof (C1_pre_holds n g vb D HC rho tp _ Hsm0) as HFp.
  pose proof (fr_allM Kc A it rho tp tr md t st HKc HK HCI HFp QE E208 n g vb D HC EVB) as FRA.
  destruct (frame_viewG (FLM A it) A (m_C1 D) _ (m_RF D) rho tp tr ms md Hsm0 (c_C1objs n g vb D HC) FRA) as (_ & _ & _ & FR4). set (r3 := rho_absorb rho (m_RF D) (vms md tp ms)) in *.
  destruct (entails_frA_sound segsA (m_C1 D) (PreD n g) (m_sF D) (m_RF D) rho tp tr ms md (c_He n g vb D HC) Hsm0) as (_ & _ & _ & HwfR & HinR).
  destruct w' as [tr2 [ms2 md2]]. cbn [w_tr w_cfg cfg_model fst snd] in HJ'.
  pose proof HJ' as HJc. unfold J_ofPA in HJ'. destruct HJ' as (HK3 & HRM & HDEF & HRL3).
  pose proof HLK as (Hag' & Hrm' & HagL' & Hlink').
  set (c := it_cls it) in *.
  assert (HF4 : Forall (holds rho') (ss_facts (ax_S (m_C1 D)))).
  { apply Forall_forall. intros f Hf. exact (proj1 (holds_agree_vals _ rho rho' f Hag' (proj1 (forallb_forall _ _) (c_FBC1 n g vb D HC) f Hf)) (proj1 (Forall_forall _ _) HFa f Hf)). }
  assert (HT40 : SPA segsA (J_ofPA (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.DrainS.JLD A Kc c) (rho_sub r3 (m_sF D)) tp rhoL tpL) (m_T1f D) rho' tpL (tr2, mkCfg ms2 md2)).
  { rewrite <- (c_T1f n g vb D HC). unfold T1f_of. apply (SPA_refacts segsA); [exact (conj Hsm' HJc) | exact (c_FBT1 n g vb D HC) | intros _; exact HF4]. }
  assert (RNG : forall o, In o (m_RF D) -> obj_range rho' o = obj_range rho o).
  { intros o Ho. apply (obj_range_agree_vals (ss_next (ax_S (m_C1 D)))); [exact Hag' | exact (proj1 (forallb_forall _ _) HwfR o Ho)]. }
  set (rho5 := rho_absorb rho' (m_RF D) (ms_with_mem ms2 (rm rho))).
  assert (RM5 : forall x, rm rho5 x = if in_ranges_dec rho' (m_RF D) x then rm rho x else rm rhoL x).
  { intros x. unfold rho5, rho_absorb, ms_with_mem. cbn [rm ms_mem]. rewrite Hrm'. reflexivity. }
  assert (IRE : forall x, in_ranges rho' (m_RF D) x <-> in_ranges rho (m_RF D) x).
  { intros x. split; intros (o & Ho & Hox); exists o; [rewrite <- (RNG o Ho) | rewrite (RNG o Ho)]; exact (conj Ho Hox). }
  assert (KEPT : forall x, in_ranges rho (m_RF D) x -> rm rhoL x = rm r3 x).
  { intros x Hin. apply (HRM x). intros HZ. exact (floc_outM A it rho t st QE _ (proj1 (FR4 x Hin)) (dzone_M A it rho t st QE _ HZ)). }
  assert (KEY : forall x : word, ~ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.DrainS.drain_zone (aa_geom A) c (cls_of A c) (bv_unsigned x) -> rm rho5 x = rm rho x).
  { intros x Hx. rewrite RM5. destruct (in_ranges_dec rho' (m_RF D) x) as [Hi|Hn']; [reflexivity|]. rewrite (HRM x Hx). cbn [rm rho_sub]. apply rm_absorb_out. intros Hi. exact (Hn' (proj2 (IRE x) Hi)). }
  assert (DEF5 : forall x : word, SHADOW_BAND_LO <= bv_unsigned x < SHADOW_BAND_HI -> rm rho x <> None -> rm rho5 x <> None).
  { intros x HBx Hd. rewrite RM5. destruct (in_ranges_dec rho' (m_RF D) x) as [Hi|Hn']; [exact Hd|].
    apply (HDEF x HBx). cbn [rm rho_sub]. unfold r3. rewrite (rm_absorb_out _ _ _ _ (fun Hi => Hn' (proj2 (IRE x) Hi))). exact Hd. }

  set (A1 := drainA A c).
  pose proof HK3 as (HAQ3 & HKc3 & _).
  destruct (AInvQ_parts' A1 rhoL tpL md2 HAQ3) as (HG3 & HI33 & HQP3 & HAU3 & HSR3).
  assert (QWT : forall z, QW A z -> z < topG (aa_geom A)).
  { intros z HQ. exact (QRD_lt_top A1 HG3 HI33 HQP3 HAU3 _ HSR3 z (QRD_QFP A1 z (or_introl HQ))). }
  assert (V5IN : forall z, 0 <= z < 2 ^ 64 -> in_ranges rho' (m_RF D) (Z_to_bv 64 z) -> view segsA (rm rho5) z = view segsA (rm rho) z).
  { intros z Hr Hi. apply view_agree. intros _. rewrite RM5. destruct (in_ranges_dec rho' (m_RF D) (Z_to_bv 64 z)) as [|Hn']; [reflexivity | exfalso; exact (Hn' Hi)]. }
  assert (V5OUT : forall z, ~ in_ranges rho' (m_RF D) (Z_to_bv 64 z) -> view segsA (rm rho5) z = view segsA (rm rhoL) z).
  { intros z Hn'. apply view_agree. intros _. rewrite RM5. destruct (in_ranges_dec rho' (m_RF D) (Z_to_bv 64 z)) as [Hi|]; [exfalso; exact (Hn' Hi) | reflexivity]. }
  assert (VL3 : forall z, 0 <= z < 2 ^ 64 -> in_ranges rho (m_RF D) (Z_to_bv 64 z) -> view segsA (rm rhoL) z = view segsA (rm r3) z).
  { intros z Hr Hi. apply view_agree. intros _. exact (KEPT _ Hi). }
  set (r5 := set_rm rhoL (rm rho5)).
  assert (HK5' : K0 Kc A1 r5 tpL tr2 md2).
  { apply (K0_blind Kc A1 rhoL r5 tpL tr2 md2); [intros i; reflexivity | intros l; reflexivity | | | exact HK3].
    - intros z Hz NQ. unfold r5. cbn [rm set_rm]. destruct (Z_le_dec 0 z) as [Z0|Z0]; [destruct (Z_lt_dec z (2 ^ 64)) as [Z1|Z1]|].
      2, 3: unfold view; replace ((0 <=? z) && (z <? 2 ^ 64))%bool with false; [reflexivity | symmetry; apply andb_false_iff; first [right; apply Z.ltb_ge; lia | left; apply Z.leb_gt; lia]].
      destruct (in_ranges_dec rho' (m_RF D) (Z_to_bv 64 z)) as [Hi|Hn']; [|exact (V5OUT z Hn')].
      pose proof (proj1 (IRE _) Hi) as Hi'. rewrite (V5IN z ltac:(lia) Hi). rewrite (VL3 z ltac:(lia) Hi').
      destruct (FR4 _ Hi') as (_ & ALT). rewrite u64_lit in ALT by lia. destruct ALT as [ALT|[ALT|ALT]].
      + exfalso. change (aa_geom A1) with (aa_geom A) in Hz. lia.
      + exfalso. exact (NQ (proj1 ALT)).
      + symmetry. exact ALT.
    - intros z HQ Hd. unfold r5. cbn [rm set_rm]. pose proof (view_range _ _ Hd) as Hr.
      destruct (in_ranges_dec rho' (m_RF D) (Z_to_bv 64 z)) as [Hi|Hn']; [|rewrite (V5OUT z Hn'); exact Hd].
      pose proof (proj1 (IRE _) Hi) as Hi'. rewrite (V5IN z Hr Hi). rewrite (VL3 z Hr Hi') in Hd.
      destruct (FR4 _ Hi') as (_ & ALT). rewrite u64_lit in ALT by lia. destruct ALT as [ALT|[ALT|ALT]].
      + exfalso. pose proof (QWT z HQ). lia.
      + exact (proj2 ALT).
      + rewrite <- ALT. exact Hd. }
  destruct HK5' as (HA5 & HKc5 & _).
  pose proof HK as (_ & _ & Htp & Htop & HRG).
  assert (RW5 : forall i, (i < NXM)%positive -> rw rho5 i = rw rho i).
  { intros i Hi. unfold rho5. cbn [rw rho_absorb]. symmetry. apply (proj1 Hag'). rewrite NXC. exact Hi. }
  assert (HK5 : K0 Kc A1 rho5 tpL tr2 md2).
  { split; [exact HA5|]. split; [exact HKc5|]. split; [|split].
    - unfold tp_ok in *. rewrite (RW5 24%positive eq_refl). exact Htp.
    - unfold top_high, V_DEPTH in *. rewrite (RW5 10%positive eq_refl), (RW5 15%positive eq_refl). exact Htop.
    - unfold rigidQ in *. rewrite (RW5 151%positive eq_refl), (RW5 152%positive eq_refl), (RW5 155%positive eq_refl), (RW5 156%positive eq_refl). exact HRG. }

  pose proof (K0_laws Kc HKc) as HL.
  destruct (kq_facts segsA (K0 Kc) HL A rho tp _ _ HK) as [HG _ _ _ _ HLEN HCLS _ _ _ _ _ _].
  destruct (kq_facts segsA (K0 Kc) HL A1 rhoL tpL _ _ HK3) as [_ _ _ _ _ _ HCLS3 _ _ _ _ _ _].
  destruct (geoM_nums A it rho t st QE) as (C1 & FAv & S1 & _). cbv zeta in FAv, S1. fold c in C1, FAv. unfold HIGH_SHADOW_END in S1.
  destruct (kchunks_facts _ C1) as (KC & KMX & _). rewrite Hn in KC, KMX.
  pose proof (HCLS HCI c C1) as CV. pose proof (cv_fa_bounds _ _ _ _ _ CV) as (FB1 & FB2 & FB3).
  pose proof (HCLS3 HCI c C1) as CV3. pose proof (cv_fa_bounds _ _ _ _ _ CV3) as (_ & FC2 & FC3).
  unfold A1 in FC2, FC3. rewrite (drainA_clsM A c ltac:(rewrite HLEN; lia)) in FC2, FC3. unfold drain_cs in FC2, FC3. cbn [cs_free_array cs_mapped_free_array] in FC2, FC3.
  rewrite length_app, length_skipn in FC2. unfold drain_keep in FC2. rewrite Hn in FC2.
  assert (DZI : forall z, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.DrainS.drain_zone (aa_geom A) c (cls_of A c) z -> DZ A c z).
  { intros z HZ. apply (dzone_DZM A c z); [lia | lia | rewrite Hn; lia | | | exact HZ].
    - rewrite Hn. clear - FC2 FC3 HFULL KC KMX. destruct (drain_grows c (cls_of A c)); lia.
    - intros EGW. rewrite EGW in FC3. exact FC3. }
  assert (VOUTP : forall z, ~ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.DrainS.drain_zone (aa_geom A) c (cls_of A c) z -> view segsA (rm rho5) z = view segsA (rm rho) z).
  { intros z Hz. apply view_agree. intros Hr. apply KEY. rewrite u64_lit by exact Hr. exact Hz. }
  assert (VOUT : forall z, ~ DZ A c z -> view segsA (rm rho5) z = view segsA (rm rho) z).
  { intros z Hz. apply VOUTP. intros HZ. exact (Hz (DZI z HZ)). }
  assert (VBAND : forall z, SHADOW_BAND_LO <= z < SHADOW_BAND_HI -> view segsA (rm rho) z <> None -> view segsA (rm rho5) z <> None).
  { intros z HB Hd. pose proof (view_range _ _ Hd) as Hr. rewrite view_in in Hd |- * by exact Hr.
    destruct (rd_of segsA (rm rho) (Z_to_bv 64 z)) as [x|] eqn:E; [|exfalso; exact (Hd eq_refl)].
    pose proof (rd_off_image (rm rho) z x ltac:(unfold SHADOW_BAND_LO, LOW_SHADOW_BEG in HB; lia) E) as E'.
    pose proof (DEF5 (Z_to_bv 64 z) ltac:(rewrite u64_lit by exact Hr; exact HB) ltac:(rewrite E'; discriminate)) as D5.
    unfold rd_of. destruct (rm rho5 (Z_to_bv 64 z)); [discriminate | exfalso; exact (D5 eq_refl)]. }
  destruct (CR_drain (K0 Kc) HL (K0_secband Kc) A a s (it :: its) tmp' rest c HTH HCI HGL C1 rho tp tr md (view segsA (rm rho)) (view segsA (rm rho5)) n0 nd HK VOUT VBAND HCB HRMM) as (HCB5 & HRM5).
  destruct HFRM as ((F1 & F1') & F2 & F3 & F4).
  assert (HFRM5 : FRM A0 rho0 rho5).
  { split; [split|split; [|split]].
    - intros i Hi. rewrite (F1 i Hi). symmetry. apply RW5. unfold NPRE in Hi. unfold NXM. lia.
    - intros l. rewrite (F1' l). unfold rho5. cbn [rl rho_absorb]. exact (proj2 Hag' l).
    - intros x Hx. rewrite KEY; [exact (F2 x Hx)|]. intros HZ. apply Hx. apply QRD_QFP. exact (DZ_QFPM A A0 c _ C1 EG (DZI _ HZ)).
    - intros z Hz. rewrite VOUT; [exact (F3 z Hz)|]. intros HZ. exact (Hz (DZ_QFPM A A0 c _ C1 EG HZ)).
    - intros x HBx Hd. exact (DEF5 x HBx (F4 x HBx Hd)). }
  exists rho5. split; [|split; [|split; [exact VOUTP | exact VBAND]]].
  - pose proof (proj1 (proj1 HT40)) as HsmT. pose proof (smatch_facts_hold _ _ _ _ HsmT) as HfT.
    unfold rho5. apply (SPA_absorb_any segsA (J_ofPA (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.DrainS.JLD A Kc c) (rho_sub r3 (m_sF D)) tp rhoL tpL)); [exact XT | | exact HT40 | ].
    + intros o x Ho Hx. exact (coveredb_sound _ _ _ rho' o x HfT (c_RFcov n g vb D HC) Ho Hx).
    + cbn [w_tr w_cfg cfg_model fst snd]. fold rho5. split; [exact HK5|]. split; [exact HCB5|]. split; [exact HRM5 | exact HFRM5].
  - split; [intros i Hi; symmetry; apply RW5; rewrite NXC in Hi; exact Hi | intros l; unfold rho5; cbn [rl rho_absorb]; exact (proj2 Hag' l)].
Qed.
End ContM.

Section CallT.
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variables (A0 : AA) (rho0 : valuation).
Context {Q : assn} (X : trk Q).
Variables (n : Z) (g vb : bool) (D : mdata).
Hypothesis HC : ltac2:(tb__ "0|0|
S62Vn;Vg;Vvb;VD;A4").

Hypothesis HDC : ltac2:(tb__ "0|2|
S27S0S21S14S3bQ40A1A1S1S13Vg;S16A3S6S2fR5A1S6bA2F_;S6fVQ;VX;S3dS10S48Vn;Vg;R5VKc;R4A5S5dVn;Vg;A2M0R3R2A5S68S10S23S39G0A1A1R3R2S15S18S3aS66A2M1S1bS3aS66S5cVn;Vg;A2S47R5VKc;R4A3A4S1aG1A1A3A5A4F_;Ftp1;Frho1;Fc;FA;").

Lemma qif_call : ltac2:(tb__ "0|d|
S27S0S0S0S19S18S0S0A2M0S14G0A1S14S29A1M1G1S21S14S3bQ40M2A1M3A1M4S0S0S1G1S2eRdA1S1aS29A1A3S1S13S2aReA1S16A3S42VA0;RfA2S1G1S2dR10A1S15S29S32RfS15G0RbRaA3ReA3S1dS29R9R8A3A3A3S1S0S40SeRcA1A1Vn;A3S1S0SaS17S0S2cS11R12SeRdA1M5A2A1A2A1S52G5A1A3S1S13S43SeReA1M6S11R13G6A2A2Vg;A3S1S13Vvb;S5aRfA1A3S1S13Vg;S16A3S6S2fR16A1S6bA2F_;S5bVn;R16SeR11A1RdA4S49R17R12ReRcRbA5S1G3S24RfPd0A2S3cG2S51A2A3S21G4S4eS23S39S5eVD;A1M7A1A1R12R2A3S0S3S46S28R1dA1SeR18A1M8S11R1dG8A2R1A4A1S1S1fS3bQ8A1M9A1MaS38S10S22R5A1R2A3S38S10S22R15A1R2A3A3F_;Fz;S0S2S6S53R1A2S8R1S50A2A2S3S1GaS38S10S22R16A1R2A3S1cG9A1MbA3A1S3S1GaS38S10S22R7A1R3A3GbA3A1F_;F_;Fz;S6eVQ;VX;S3dS10S41S59VKc;A1McVA0;Vrho0;S44R1eSeR19A1A2R1dR1bR1aS15G0R19R18A3R17R16AaS60VD;A1R5R4A5A3F_;F_;F_;FtpL;Frho5;S6eVQ;VX;S3dS10S41GcVA0;Vrho0;R1aR19R17R16S15G0R15R14A3R13R12AaG7R11R10A5A3F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fst;Ft;Ftp;Frho;Frest;Ftmp';Fits;Fit;Fnd;Fn0;Fs;Fa;FA;").
Proof.
  intros A a s n0 nd it its tmp' rest rho tp t st HTH HCI HQP HGL Hn HFULL HGR EVB HB HENV QE E208 HCt.
  apply (tr_callP X (JRI (K0 Kc) A0 rho0 A a n0 nd (it :: its) tmp' rest) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.DrainS.JD n g A Kc (it_cls it)) (m_C1 D) (PreD n g) (m_sF D) (m_RF D) [(PostD n g, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.DrainS.JLD A Kc (it_cls it))] rho tp
           (c_He n g vb D HC) (c_Hchk n g vb D HC)).
  - intros rho1 tp1. exact (HDC A (it_cls it) rho1 tp1 HB).
  - intros tr ms md Hsm HJ. exact (qif_JP Kc HKc A0 rho0 n g vb D HC A a n0 nd it its tmp' rest rho tp tr ms md t st HCI Hn HFULL HGR EVB HENV QE E208 Hsm HJ).
  - intros L JL tr ms md rhoL tpL tr' ms' md' Hin Hsm HJ Hag HsmL HJL. destruct Hin as [E|[]]. injection E as <- <-. split.
    + exact (qif_post_ok Kc HKc A0 rho0 n g vb D HC A a n0 nd it its tmp' rest rho tp tr ms md t st rhoL tpL tr' md' HCI Hn HFULL HGR EVB HENV QE E208 Hsm HJ Hag HJL).
    + intros rho' HLK.
      apply (tr_glue X _ (JRI (K0 Kc) A0 rho0 (drainA A (it_cls it)) a n0 nd (it :: its) tmp' rest) (m_T1f D) tpL
               (fun r => agree_vals (ss_next (ax_S (m_C1 D))) rho r
                         /\ (forall z, ~ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.DrainS.drain_zone (aa_geom A) (it_cls it) (cls_of A (it_cls it)) z -> view segsA (rm r) z = view segsA (rm rho) z)
                         /\ (forall z, SHADOW_BAND_LO <= z < SHADOW_BAND_HI -> view segsA (rm rho) z <> None -> view segsA (rm r) z <> None)));
        [|intros r (Hr1 & Hr2 & Hr3); exact (HCt r tpL Hr1 Hr2 Hr3)].
      intros w' Hw'. exact (qif_exit_core Kc HKc A0 rho0 n g vb D HC A a s n0 nd it its tmp' rest rho tp tr ms md t st rhoL tpL HTH HCI HQP HGL Hn HFULL HGR EVB HENV QE E208 Hsm HJ rho' w' HLK Hw').
Qed.
End CallT.
