(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require q1.
From Stdlib Require NArith PArith.
From LinuxProcessSemantics.Riscv Require Decode DecodeC.

(* [comment removed for export] *)
Module SegQCF_exit.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "sobj"; "ss_objs"; "valuation"; "rw"; "SAlu"; "SVar"; "sprop"; "eval"; "sv_eqb"; "ob_hi"; "ob_lo"; "SExt"; "ob_base"; "sprop_eqb"; "ss_facts"; "@Corelib.Init.Datatypes"; "pair"; "prod"; "cons"; "nat"; "bool"; "nil"; "list"; "app"; "true"; "false"; "andb"; "fst"; "Some"; "length"; "option"; "S"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_spec"; "carve_obj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_setS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "qbatch"; "aa_geom"; "AA"; "aa_cache_inited"; "mkQB"; "aa_q_global"; "aa_q_thread"; "ageom"; "cs_cache"; "ag_ctx"; "ag_thread"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXRebase"; "AXSelect"; "apply_axforms"; "AXMerge"; "AXUnbase"; "@Corelib.Lists.ListDef"; "map"; "firstn"; "seq"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dq.SegQCF_exit"; "Lx"; "Ly"; "Lz"; "Lm"; "T_x"; "ref3"; "DSX"; "K24"; "K27"; "N_D2b"; "REFALL"; "findi"; "is3"; "N_2a"; "REF1"; "REF2a"; "REFK"; "XM1"; "dstS"; "fri"; "isfr"; "p1"; "p2"; "riS"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "aluop"; "mulop"; "ALU_SUB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.d9.SegQCF_states"; "pcbF"; "L2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DrainModel"; "drainA"; "drain_grows"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ"; "K0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bd.SegQ3D_inv"; "JRD"; "JRI"; "QP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.SegQ3D_states"; "clsB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2"; "cls_of"; "QW"; "push_cache"; "set_q"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR"; "vMFA"; "vRI"; "vAU"; "vMU"; "vNF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc"; "vT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "Size"; "PG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b3.SegQ3D_qc_defs"; "RCr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3M_glue"; "dspec"; "forallb2"; "dobj"; "keepN"; "same_rng"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3R_loop"; "HVX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dg.SegQCF_glue"; "dstF"; "@Stdlib.ZArith.BinInt.Z"; "eqb"; "of_nat"; "add"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "pre_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3DM"; "MC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b2.SegQ3D_qcs"; "cptrC";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SegQ3D_qip"; "DQI0"; "N_rti"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states"; "DEPTH_R"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q1.SegQCF_call"; "ENVC"; "gmaxS"; "mtxS"; "szS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQS_glue"; "ZD_fixS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQS_lib"; "mkST"; "ro_cond"; "s_C"; "s_Cd"; "s_k"; "s_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bz.SegQS_tail"; "sbS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs"; "qb_id"; "@Stdlib.Lists.List"; "existsb"; "forallb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundL SymSoundV SymSoundM SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3 SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocInv Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Inv Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ_defs SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ae.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQtr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ak.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ3R_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require be.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ba.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_zones.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ3M_glue SegQ_wf4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQS_glue SegQS_scan SegQS_lib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bw.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bz.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require az.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillModel DrainModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require d9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require dg.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_drain DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require q1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b6.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.SegQ3_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.SegQ3D_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a8.SegQ3G_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQtr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3R_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3R_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3DM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bd.SegQ3D_inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.SegQ3D_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.SegQI_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.SegQI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SegQI_side OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.SegQC_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_qi_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.be.SegQ3D_qi_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b3.SegQ3D_qc_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SegQ3D_qc_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SegQ3D_qc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_zones OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQ_wf3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SegQ3D_qip OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SegQ3D_qiq OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3M_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SegQS_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQS_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQS_scan OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQS_lib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bw.SegQS_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bv.SegQS_k OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bz.SegQS_tail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.InvQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.InvQ4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.InvQ6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.InvQ9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DrainModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.DrainS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.DrainSG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.d9.SegQCF_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bb.SegQF_lib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dg.SegQCF_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SegQ3D_qiq OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b2.InvQ7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_drain OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q1.SegQCF_call OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b6.SegQF_ri OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b2.SegQ3D_qcs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SMGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ba.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Fixpoint findi (f : sobj -> bool) (l : list sobj) (k : nat) : nat := match l with [] => k | o :: t => if f o then k else findi f t (S k) end.
Definition isfr (o : sobj) : bool := ltac2:(tb__ "0|a|
S0S15Lx;M0ScVo;A1S21G0SbVo;A1S21S1bS81R2N30A2S81R1Z0A2A2Lb;S22S1aLi;M1S5eS0S0S1aLb;M2La0;M3Lop;M4G4S5fG3Lop;M5G5S15S23S0S1aLa0;Lw;Lsgn;S22S0S21S1aLk;Li;Ll;M6X0x8La;G1S5eS0G2La;M7Lop;M8G8S5fG7Lop;M9G9S15S23S0S1aLa;Lw;Lsgn;G6X0x8").
Definition fri (g : bool) : nat := ltac2:(tb__ "0|0|
S4eS57S3S29S62Vg;A1A1A1U0A3").
Definition p1 (g : bool) : list nat := ltac2:(tb__ "0|2|
S13S14U0S13S14S56Vg;A1M0S18S14S3fU1M1S6fG0G1A2A2S3fS20G0A1S6fU1dG0A2A2A3A3A3").
Definition XM1 (g : bool) : list axform := ltac2:(tb__ "0|1|
S13S37S39S58Vg;A1A1S13S37S38U0M0A1S13S37S38U1A1S13S37S3bG0A1S13S37S3cG0Nc0A2S16S37A1A3A3A3A3A3").
Definition optA (d : axst) (o : option axst) : axst := match o with Some Y => Y | None => d end.
Definition Lm_f : axst := Eval vm_compute in (optA (L2 false) (apply_axforms (L2 false) (XM1 false))).
Definition Lm_g : axst := Eval vm_compute in (optA (L2 true) (apply_axforms (L2 true) (XM1 true))).
Definition Lm (g : bool) : axst := if g then Lm_g else Lm_f.
Lemma Lm_eq : ltac2:(tb__ "0|0|
S15S24S1fS2aA1S3aS62R1A1S54R1A1A2S1dS2aS46R1A1A2A3Fg;"). Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition is3 (b lo hi : sv) (o : sobj) : bool := ltac2:(tb__ "0|0|
S1bS1bSaSeVo;A1Vb;A2SaScVo;A1Vlo;A2A2SaSbVo;A1Vhi;A2A2").
Definition ref3 (k : carve_spec) : sv * sv * sv := ltac2:(tb__ "0|5|
S12S12S12S0S21A2M0S21A2M1S17S12S12S21S14A2S0A2A1M2A2S12S12S0S0A2M3S0A2M4Lk;Vk;G1G2G1G4Lp;R2G0S21G0G4Lp0;R2S0S21S11G3S0S11S0S0R2S1R1A1A4S1R3A1A4Llo;Lb;X12x1Lhi;Lp0;X12x1Ll;Lp;X12x1").
Definition REFK : list (sv * sv * sv) := ltac2:(tb__ "0|6|
S13S12S12S0S0A2M0S0A2M1S11G0S0S11S0S0S6S5dS7PaA1M2S1Nc0A1M3A3S6S5dS7PfA1S1Zc0A1A3A4S1Z0A1M4A4S13G1S11G0S0S11S0S0G2G3A4S1Nb8A1M5A4S13G1S11G0S0S11S0S0S6S5dG2G5A3G4A4S1Z10A1A4S13G1S11G0S0S11S0S0G2S1Na8A1A4G4A4S13G1S48S8fA1S13G1S48S8eA1S13G1S11G0S0S11S0S0G4S1Ze7bd8A1A4S1Ze8978A1A4S13G1S11G0S0S11S0S0G4S1Zf13f8A1A4S1Zf1404A1A4S16G1A1A3A3A3A3A3A3A3A3").
Definition N_D2b : list carve_spec := ltac2:(tb__ "0|d|
S18S27S8bS13S12S12S12S0S21A2M0S21A2M1S17S12S12S21S14A2M2S0A2M3A1M4A2M5S11G1G4S11G0S21S11S0S21S1Z0A1M6Z180ea0M7A4Z180ea8A4S13G3S11G2S0S11S21S14G7U8M8A4S1S78A1A4S16G3A1M9A3A4S13G5S11G1G4S11G0S21S11S0S21G6Z18302cMaA4Z18302dA4S13G3S11G2S0S11S21S14GaU1A4G6A4G9A3A4S13G5S11G1G4S11G0S21S11S0S21G6Z182fb8MbA4Z182fc0A4S13G3S11G2S0S11S21S14GbG8A4G6A4G9A3A4S13G5S11G1G4S11G0S21S11S0S21S61Z4McA4Z8A4S13G3S11G2S0S11S21S14GcU4A4S1Z2A1A4G9A3A4S13S27S90S16S27A1A3A3A3A3A3A3").
Definition REF2a : list (sv * sv * sv) := ltac2:(tb__ "0|2|
S13S12S12S0S0A2M0S0A2M1S11G0S0S11S0S0S61S1Z0A1A4S1Z4A1A4S13G1S11G0S0S11S0S0S61S1Z14A1A4S1Z18A1A4S13G1S11G0S0S11S0S0S76S1Zad0A1A4S1Zc60A1A4S16G1A1A3A3A3").
Definition REF1 : list (sv * sv * sv) := ltac2:(tb__ "0|3|
S13S12S12S0S0A2M0S0A2M1S11G0S0S11S0S0S72S1Z0A1M2A4S1Z80A1A4S13G1S11G0S0S11S0S0S80G2A4S1Z4A1A4S16G1A1A3A3").
Definition REFALL : list (sv * sv * sv) := ltac2:(tb__ "0|1|
S18S12S12S0S0A2S0A2M0S53S18G0S3dS27G0S48S4cA4S18G0S52S51A3A3A3").
Definition p2 (g : bool) : list nat := ltac2:(tb__ "0|2|
S3dS12S12S0S0A2M0S0A2M1S14G1G1S14Lr;R1G0S0G0S14Lp;R2S0S0S4eS4fR2R1R3A3S3S29S46Vg;A1A1A1U0A3Llo;Lb;X12x1Lhi;Lp;X12x1Lr;S4dA4").
Definition Lx_f : axst := Eval vm_compute in (optA Lm_f (apply_axforms Lm_f [AXSelect (p2 false)])).
Definition Lx_g : axst := Eval vm_compute in (optA Lm_g (apply_axforms Lm_g [AXSelect (p2 true)])).
Definition Lx (g : bool) : axst := if g then Lx_g else Lx_f.
Lemma Lx_eq : ltac2:(tb__ "0|0|
S15S24S1fS2aA1S3aS46R1A1S13S37S39S59R1A1A1S16S37A1A3A2S1dS2aS43R1A1A2A3Fg;"). Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Lx_shape : ltac2:(tb__ "0|2|
S15S24S15S7bS2S12S12S0S0A2M0S0A2M1S2G1G1S15Lr;R1G0S0G0S15Lp;R2S0S0S4fR2R1R3R6A4Llo;Lb;X12x1Lhi;Lp;X12x1Lr;Lo;S3S29S43R1A1A1A1S4dA5S19A3Fg;"). Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition riS (g : bool) : carve_spec := ltac2:(tb__ "0|6|
S11S12S12S0S21A2M0S21A2S17S12S12S21S14A2M1S0A2M2A1S11G0S21S11S0S21S72Z0M3A4Z80A4S13G2S11G1S0S11S21S14G3U8M4A4S1G3A1M5A4S13G2S11G1S0S11S21S14Z10G4A4S6S5dS75S1Z1A1A3A4S13G2S11G1S0S11S21S14Z18G4A4S15S0Lg;Vg;S6S5dS71S1Z40000A1A3S71X15x2A4S13G2S11G1S0S11S21S14Z20G4A4S73A4S13G2S11G1S0S11S21S14Z28G4A4G5A4S13G2S11G1S0S11S21S14Z30G4A4S74A4S13G2S11G1S0S11S21S14Z38G4A4G5A4S13G2S11G1S0S11S21S14Z44U1A4G5A4S16G2A1A3A3A3A3A3A3A3A3A4").
Definition dstS : carve_spec := ltac2:(tb__ "0|4|
S11S12S12S0S21A2M0S21A2S17S12S12S21S14A2M1S0A2M2A1S11G0S21S11S0S21S80Z0M3A4Z4A4S13G2S11G1S0S11S21S14G3U4A4SdS19Q20S7Pe7A1A3A4S16G2A1A3A4").
Definition K27 (g : bool) : list sobj := ltac2:(tb__ "0|0|
S3eS2U1bS3S29S43Vg;A1A1A1A3").
Lemma Lx_objs1 : ltac2:(tb__ "0|0|
S15S24S17S2A1S3S29S43R1A1A1A1S18S2S4bR1A1S3dS27S2S28S13S27S5aR1A1S13S27S55S16S27A1A3A3A4A3A3Fg;"). Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition Ly (g : bool) : axst := ltac2:(tb__ "0|1|
S2bS43Vg;A1M0S70S29G0A1S4bVg;A1A2A2").

Section ExitF.
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variables (A0 : AA) (rho0 : valuation).

Lemma qcf_x1 : ltac2:(tb__ "0|5|
S15S2eS21S21S21S14S17S2cA1M0G0S4S17S5cQ40A1M1A1S66S24G0S32RaA1S16S2cA1A3S24S15S2fRbA1S19A3S69VA0;RcA2S24G0S31RdA1S13S2cS30RcS16S12S21S21A2A1M2RbA3S18S2cR8R7A3A3A3S24S21S82S1eS21S34S6bReZ18M3A2A1A2A1Z2A3S24S15S64G3S6bRfG3A2A2R10A3S8dR10R9A2S41S42S68S65VKc;A1M4VA0;Vrho0;S63R11G3A2R10ReRdG2RcRbAaS43R12A1RaR9R8A6S26S4S4S25S41S42S68G4VA0;Vrho0;S63R13G3A2R12R10RfG2ReRdAaS44R14A1R1RbRaA6S22S24G1S5R2R1A2S5RdR1A2A3Fi;A2Lrho3;A2F_;F_;F_;F_;F_;F_;F_;F_;Fw;Ftp;Frho;Frest;Ftmp';Fnd;Fn0;Fs;Fa;FA;Fg;").
Proof.
  intros g A a s n0 nd tmp' rest rho tp [tr [ms md]] HTH HCI HQP HGL HFULL HGR (EC & E201 & E208 & E221 & E222 & E223 & E224 & E225 & E231) H.
  destruct (proj2 H) as (HK & HCB & HRM & HFRM). cbn [w_tr w_cfg cfg_model fst snd] in HK, HCB, HRM, HFRM.
  pose proof (proj1 (proj1 H)) as Hsm. unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model] in Hsm.
  set (A1 := drainA A 24) in *.
  assert (EG : aa_geom A = aa_geom A0) by (destruct HQP as (ESB & _); unfold same_but_qcs in ESB; rewrite ESB; reflexivity).
  pose proof (K0_laws Kc HKc) as HL.
  destruct (kq_facts segsA (K0 Kc) HL A1 rho tp _ _ HK) as [HG HRIG _ _ _ HLEN HCLS _ _ _ _ _ _]. change (aa_geom A1) with (aa_geom A) in HG, HRIG.
  destruct HRIG as (E151 & E152 & E155 & E156).
  assert (HLA : (24 < length (aa_cls A))%nat) by (unfold A1, drainA in HLEN; cbn [aa_cls] in HLEN; rewrite length_list_upd in HLEN; lia).
  pose proof (HCLS HCI 24 ltac:(lia)) as CV1. change (aa_geom A1) with (aa_geom A) in CV1. unfold A1 in CV1. rewrite (drainA_cls A HLA) in CV1.
  set (cs := SegQ_wf2.cls_of A 24) in *. set (SB := ag_spacebeg (aa_geom A)) in *. set (nf := Z.of_nat (length (cs_free_array cs))) in *.
  pose proof (cv_fa_bounds _ _ _ _ _ CV1) as (FC1 & FC2 & FC3). unfold drain_cs in FC1, FC2, FC3. cbn [cs_free_array cs_mapped_free_array] in FC1, FC2, FC3. fold cs in HGR. rewrite HGR in FC1, FC2, FC3. unfold kFreeArrayMapSize in FC1, FC2, FC3.
  rewrite length_app, length_skipn in FC2. unfold drain_keep in FC2. change (Z.to_nat (kchunks 24)) with 1%nat in FC2.
  assert (NF0 : 0 <= nf) by (unfold nf; lia). assert (HFL : length (cs_cache cs) = 2%nat) by lia. rewrite HFL in FC2. change (Z.of_nat (length (cs_free_array cs) + (2 - (2 - 1)))) with (Z.of_nat (length (cs_free_array cs) + 1)) in FC2.
  rewrite Nat2Z.inj_add in FC2. fold nf in FC2. change (Z.of_nat 1) with 1 in FC2.
  destruct (geo_nums Kc A1 rho tp tr md HKc HK) as (S1 & S2 & _). cbv zeta in S1, S2. change (aa_geom A1) with (aa_geom A) in S1, S2. fold SB in S1, S2.
  pose proof (topG_range (aa_geom A)) as TG. unfold HIGH_SHADOW_END, kFreeArraySize in *. rewrite kSpaceSize_val in S2.
  assert (RIv : region_info SB 24 = SB + 2 ^ 37 + 3072) by (unfold region_info, kRegionInfoStride; rewrite kSpaceSize_val; lia).
  assert (FAv : free_array SB 24 = SB + 24 * 2 ^ 32 + 3758096384) by (unfold free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize; lia).
  assert (ERI : bv_unsigned (eval rho vRI) = SB + 2 ^ 37 + 3072) by (unfold vRI; cbn [eval]; rewrite E225; fold SB; rewrite RIv, u64_lit by lia; reflexivity).
  assert (Edst : bv_unsigned (eval rho dstF) = SB + 24 * 2 ^ 32 + 3758096384 + 4 * nf).
  { unfold dstF. rewrite U_add, U_add, U_add, !U_sll_lit. unfold vSB, vNF. cbn [eval]. rewrite EC, E155, E221. fold SB nf. rewrite !u64_lit by lia. change (32 mod 64) with 32. change (2 mod 64) with 2.
    unfold M64v. rewrite (Z.mod_small (24 * 2 ^ 32)) by lia. rewrite (Z.mod_small (24 * 2 ^ 32 + 3758096384)) by lia. rewrite (Z.mod_small (SB + (24 * 2 ^ 32 + 3758096384))) by lia.
    rewrite (Z.mod_small (nf * 2 ^ 2)) by lia. rewrite Z.mod_small by lia. lia. }

  set (x1 := nth 1 (cs_cache cs) 0) in *.
  assert (ECA : cs_cache cs = [nth 0 (cs_cache cs) 0; x1]) by (unfold x1; destruct (cs_cache cs) as [|y0 [|y1 [|y2 l]]]; cbn in HFL; try lia; reflexivity).
  assert (EFA1 : cs_free_array (drain_cs 24 cs) = cs_free_array cs ++ [x1]).
  { unfold drain_cs, drain_keep. cbn [cs_free_array]. change (Z.to_nat (kchunks 24)) with 1%nat. rewrite HFL. rewrite ECA. reflexivity. }
  assert (EMF1 : cs_mapped_free_array (drain_cs 24 cs) = if g then cs_mapped_free_array cs + 262144 else cs_mapped_free_array cs).
  { unfold drain_cs. cbn [cs_mapped_free_array]. fold cs. rewrite HGR. unfold kFreeArrayMapSize. destruct g; reflexivity. }
  assert (HX1 : 0 <= x1 < 2 ^ 28).
  { apply (K0_id24_bound Kc A1 rho tp tr md x1 HKc HCI HK). unfold A1. rewrite (drainA_cls A HLA). fold cs. rewrite EFA1. apply in_or_app. left. apply in_or_app. right. left. reflexivity. }
  pose proof (cv_ri_au _ _ _ _ _ CV1) as K_au. pose proof (cv_ri_mu _ _ _ _ _ CV1) as K_mu. pose proof (cv_bounds _ _ _ _ _ CV1) as (_ & BAU & BMU & _).
  pose proof (cv_fa_cells _ _ _ _ _ CV1 (length (cs_free_array cs)) x1 ltac:(rewrite EFA1; rewrite nth_error_app2 by lia; rewrite Nat.sub_diag; reflexivity)) as K_dst.
  fold SB in K_dst, K_au, K_mu. fold nf in K_dst. rewrite FAv in K_dst. cbn [cs_allocated_user cs_mapped_user drain_cs] in BAU, BMU. unfold kUserSpaceSize, kRegionSize, kFreeArraySize, kUserMapSize in BMU.

  set (R := map carve_obj [riS g; dstS]). set (rho3 := rho_absorb rho R (vms md tp ms)). set (v3 := view segsA (rm rho3)). set (v := view segsA (rm rho)) in *.
  destruct (absorb_view_cells segsA rho _ tr (vms md tp ms) (vmd md) (K27 g) R vRI 0 128 _ Hsm (Lx_objs1 g) ltac:(left; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia) ltac:(rewrite ERI; lia) ltac:(rewrite ERI; lia)) as [AV1 PR1].
  destruct (absorb_view_cells segsA rho _ tr (vms md tp ms) (vmd md) (K27 g) R dstF 0 4 _ Hsm (Lx_objs1 g) ltac:(right; left; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia) ltac:(rewrite Edst; lia) ltac:(rewrite Edst; lia)) as [AV2 PR2].
  fold rho3 v3 in AV1, PR1, AV2, PR2. rewrite ERI in AV1, PR1. rewrite Edst in AV2, PR2.
  set (ri := SB + 2 ^ 37 + 3072) in *. set (da := SB + 24 * 2 ^ 32 + 3758096384 + 4 * nf) in *.
  assert (Enf1 : eval rho (SAlu ALU_ADD vNF (SLit 1)) = Z_to_bv 64 (nf + 1)) by (apply (ev_add_lit rho vNF nf 1); [unfold vNF; cbn [eval]; exact E221 | lia | lia | lia]).
  assert (Emf1 : eval rho (if g then SAlu ALU_ADD vMFA (SLit 262144) else vMFA) = Z_to_bv 64 (if g then cs_mapped_free_array cs + 262144 else cs_mapped_free_array cs)).
  { destruct g; [apply (ev_add_lit rho vMFA (cs_mapped_free_array cs) 262144); [unfold vMFA; cbn [eval]; exact E222 | clear -FC1 FC2 FC3 NF0; lia | lia | clear -FC1 FC2 FC3 NF0; lia] | unfold vMFA; cbn [eval]; exact E222]. }
  assert (Edv : eval rho (SExt true 32 (SVar 231)) = Z_to_bv 64 x1) by (cbn [eval]; rewrite E231; apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineMallocR3.sext32_small; lia).
  assert (C0 : cell_ok v3 (mkACell (ri + 0) 8 0)) by exact (av_cell v3 ri 0 8 _ _ rho (fun j => AV1 _ _ _ j (or_introl eq_refl)) eq_refl).
  assert (C16 : cell_ok v3 (mkACell (ri + 16) 8 (nf + 1))) by exact (av_cell v3 ri 16 8 _ _ rho (fun j => AV1 _ _ _ j (or_intror (or_introl eq_refl))) Enf1).
  assert (C24 : cell_ok v3 (mkACell (ri + 24) 8 (if g then cs_mapped_free_array cs + 262144 else cs_mapped_free_array cs))) by exact (av_cell v3 ri 24 8 _ _ rho (fun j => AV1 _ _ _ j (or_intror (or_intror (or_introl eq_refl)))) Emf1).
  assert (C32 : cell_ok v3 (mkACell (ri + 32) 8 (cs_allocated_user cs))) by exact (av_cell v3 ri 32 8 _ _ rho (fun j => AV1 _ _ _ j (or_intror (or_intror (or_intror (or_introl eq_refl))))) E223).
  assert (C40 : cell_ok v3 (mkACell (ri + 40) 8 0)) by exact (av_cell v3 ri 40 8 _ _ rho (fun j => AV1 _ _ _ j (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl)))))) eq_refl).
  assert (C48 : cell_ok v3 (mkACell (ri + 48) 8 (cs_mapped_user cs))) by exact (av_cell v3 ri 48 8 _ _ rho (fun j => AV1 _ _ _ j (or_intror (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl))))))) E224).
  assert (C56 : cell_ok v3 (mkACell (ri + 56) 8 0)) by exact (av_cell v3 ri 56 8 _ _ rho (fun j => AV1 _ _ _ j (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl)))))))) eq_refl).
  assert (C68 : cell_ok v3 (mkACell (ri + 68) 1 0)) by exact (av_cell v3 ri 68 1 _ _ rho (fun j => AV1 _ _ _ j (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl))))))))) eq_refl).
  assert (Cd3 : cell_ok v3 (mkACell (da + 0) 4 x1)) by exact (av_cell v3 da 0 4 _ _ rho (fun j => AV2 _ _ _ j (or_introl eq_refl)) Edv).
  set (P := fun z : Z => (ri <= z < ri + 128) \/ (da <= z < da + 4)).
  assert (PD : forall z, P z \/ ~ P z) by (intros z; unfold P; lia).
  assert (INRG : forall x, in_ranges rho R x -> P (bv_unsigned x)).
  { intros x (o & Ho & Hz). unfold P. destruct Ho as [<-|[<-|[]]]; unfold carve_obj, riS, dstS, carved in Hz; rewrite obj_range_mk in Hz by lia; cbn [fst snd] in Hz; rewrite ?ERI, ?Edst in Hz; fold ri da in Hz; lia. }
  destruct (absorb_out rho R (vms md tp ms) P INRG) as [FR FRrm]. fold rho3 v3 v in FR, FRrm.
  assert (VD : forall z, da <= z < da + 4 -> v3 z = v z).
  { intros z Hz. replace da with (da + 0) in Hz by lia. unfold da in K_dst. fold da in K_dst. replace (da) with (da + 0) in K_dst by lia.
    apply (cell_ok_same v v3 _ K_dst Cd3). cbn [c_addr c_w]. lia. }
  assert (VO : forall z, ~ (ri <= z < ri + 128) -> v3 z = v z).
  { intros z Hz. destruct (Z_le_dec da z) as [L1|L1]; [destruct (Z_lt_dec z (da + 4)) as [L2|L2]; [exact (VD z (conj L1 L2))|]|]; apply FR; unfold P; lia. }
  assert (HK3 : K0 Kc A1 rho3 tp tr md).
  { apply (K0_ri_blind Kc A1 rho rho3 tp tr md 24 HKc ltac:(lia) HCI); try (intros; reflexivity); try exact HK.
    all: change (ag_spacebeg (aa_geom A1)) with SB; rewrite ?RIv; fold ri; fold v3 v.
    all: unfold A1; rewrite ?(drainA_cls A HLA); fold cs; rewrite ?EFA1, ?EMF1, ?length_app; cbn [length cs_allocated_user cs_mapped_user drain_cs]; rewrite ?Nat2Z.inj_add; fold nf; change (Z.of_nat 1) with 1.
    all: unfold RI_mutex, RI_num_freed, RI_mapped_free_array, RI_allocated_user, RI_allocated_meta, RI_mapped_user, RI_mapped_meta, RI_exhausted.
    - exact VO.
    - intros z Hz. exact (PR1 z ltac:(lia)).
    - intros a0 Ha0. apply FRrm. unfold P, ri, da. rewrite u64_lit by (unfold IMG_LO, IMG_HI in Ha0; lia). unfold IMG_LO, IMG_HI in Ha0. lia.
    - exact C0.
    - exact C16.
    - exact C24.
    - exact C32.
    - exact C40.
    - exact C48.
    - exact C56.
    - exact C68. }
  assert (PDZ : forall z, P z -> DZ A1 24 z).
  { intros z Hz. unfold DZ. cbv zeta. change (aa_geom A1) with (aa_geom A). fold SB. rewrite RIv, FAv. unfold kRegionInfoStride, kFreeArraySize. unfold P, ri, da in Hz.
    destruct Hz as [Hz|Hz]; [right; left; lia | right; right; left; clear -Hz FC2 FC3 NF0; destruct g; lia]. }
  destruct (CR_drain (K0 Kc) HL (K0_secband Kc) A1 a s [] tmp' rest 24 HTH HCI HGL ltac:(lia) rho tp tr md v v3 n0 nd HK) as (HCB3 & HRM3); [ | | exact HCB | exact HRM | ].
  { intros z Hz. apply FR. intros HP. exact (Hz (PDZ z HP)). }
  { intros z HB Hd. rewrite FR; [exact Hd|]. unfold P, ri, da. unfold bandz, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in HB. lia. }
  assert (HF3 : FRM A0 rho0 rho3).
  { apply (FRM_absorb_QFP A0 rho0 rho rho3 P PD ltac:(intros i; reflexivity) ltac:(intros l; reflexivity)); [| exact FR | exact FRrm | exact HFRM].
    intros z Hz. split; [exact (DZ_QFP A1 A0 z EG (PDZ z Hz))|]. unfold P, ri, da in Hz. unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END. lia. }
  set (TJ := (fun (_ : valuation) (_ : list word) (_ : list event) (_ : Model) => True) : jpredA).
  assert (HT : SPA segsA TJ (Lx g) rho tp (tr, mkCfg ms md)) by (split; [exact (proj1 H) | exact I]).
  pose proof (SPA_unobj segsA TJ rho (Lx g) (K27 g) R tp tr ms md (Lx_objs1 g) HT (fun x => x)) as HU. cbn zeta in HU. fold rho3 in HU.
  exists rho3. split; [|intros i; reflexivity].
  split; [exact (proj1 HU)|]. cbn [w_tr w_cfg cfg_model fst snd]. split; [exact HK3|]. split; [exact HCB3|]. split; [exact HRM3 | exact HF3].
Qed.
End ExitF.

Definition N_2a : list carve_spec := ltac2:(tb__ "0|a|
S13S12S12S12S0S21A2M0S21A2M1S17S12S12S21S14A2M2S0A2M3A1M4A2M5S11G1G4S11G0S21S11S0S21S61Z0M6A4Z4A4S13G3S11G2S0S11S21S14G6U4M7A4S1Z2A1A4S16G3A1M8A3A4S13G5S11G1G4S11G0S21S11S0S21S61Z14M9A4Z18A4S13G3S11G2S0S11S21S14G9G7A4S89A4G8A3A4S13G5S11G1G4S11G0S21S11S0S21S76Zad0A4Zc60A4S13G3S11G2S0S11S21S14Zae0U8A4S87S7Pd1A1S6S60S1G6A1S7Pc9A1A3A2A4G8A3A4S16G5A1A3A3A3").
Definition K24 (g : bool) : list sobj := ltac2:(tb__ "0|0|
S3eS2U18S3S29S44Vg;A1A1A1A3").
Lemma Ly_objs2 : ltac2:(tb__ "0|0|
S15S24S17S2A1S3S29S44R1A1A1A1S18S2S4aR1A1S3dS27S2S28S50A4A3A3Fg;"). Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition Lz (g : bool) : axst := ltac2:(tb__ "0|1|
S2bS44Vg;A1M0S70S29G0A1S4aVg;A1A2A2").

Section ExitG.
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variables (A0 : AA) (rho0 : valuation).

Lemma qcf_x2a : ltac2:(tb__ "0|7|
S15S2eS21S21S21S14S17S2cA1M0G0S4S17S5cQ40M1A1M2A1S66S24G0S32RaA1S16S2cA1M3A3S24S15S2fRbA1S19A3S69VA0;RcA2S24G0S31RdA1S13S2cS30RcS16S12S21S21A2A1M4RbA3S18S2cR8R7A3A3A3S24S21S82S1eS21S34S6bReZ18M5A2A1A2A1Z2A3S41S42S68S65VKc;A1M6VA0;Vrho0;S63RfG5A2ReRcRbG4RaR9AaS44R10A1R8R7R6A6S24G2S5R9Pa6A2S5bG1RfA2A3S26S4S4S25S41S42S67G6VA0;Vrho0;S6dS6eS63R12G5A2G3S18S2cRdRcA3A3G5S99S2dR12A1S30R11G4R10A3A2A3RdRcA6S45R13A1R1RaR9A6S25S22S24G2S5R2R1A2S5RcR1A2A3Fi;S24G2S9R1S6aA2S5bG1G5A2A3A2A2Lrho3;A2F_;F_;F_;F_;F_;F_;F_;Fw;Ftp;Frho;Frest;Ftmp';Fnd;Fn0;Fs;Fa;FA;Fg;").
Proof.
  intros g A a s n0 nd tmp' rest rho tp [tr [ms md]] HTH HCI HQP0 HGL HFULL H E166.
  destruct (proj2 H) as (HK & HCB & HRM & HFRM). cbn [w_tr w_cfg cfg_model fst snd] in HK, HCB, HRM, HFRM.
  pose proof (proj1 (proj1 H)) as Hsm. unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model] in Hsm.
  set (A1 := drainA A 24) in *. pose proof (K0_laws Kc HKc) as HL.
  assert (HTH1 : aa_q_thread A1 = []) by exact HTH. assert (HGL1 : aa_q_global A1 = mkQB a [] s :: tmp' ++ rest) by exact HGL. assert (HCI1 : aa_cache_inited A1 = true) by exact HCI.
  destruct (kq_facts segsA (K0 Kc) HL A1 rho tp _ _ HK) as [HG HRIG HRTC HMIN HST HLEN HCLS HQPU HIDS HSEP HSEP3 HKTOP HKSECQ].
  change (aa_geom A1) with (aa_geom A) in HG, HRIG, HST, HSEP.
  destruct HRIG as (E151 & E152 & E155 & E156).
  assert (HLA : (24 < length (aa_cls A))%nat) by (unfold A1, drainA in HLEN; cbn [aa_cls] in HLEN; rewrite length_list_upd in HLEN; lia).
  assert (HK1 : Z.of_nat (length (cs_cache (SegQ_wf2.cls_of A1 24))) = 1).
  { unfold A1. rewrite (drainA_cls A HLA). unfold drain_cs, drain_keep. cbn [cs_cache]. change (Z.to_nat (kchunks 24)) with 1%nat. rewrite length_firstn. lia. }
  set (T := ag_thread (aa_geom A)) in *.
  pose proof (geom_old _ HG) as HG'. destruct HG' as (_ & _ & _ & _ & G5 & G6 & G7 & _). fold T in G5, G6, G7.
  pose proof (geom_bands _ HG) as (_ & TBD & _ & _ & TI & _). unfold IMG_LO, IMG_HI in TI. fold T in TI, TBD. pose proof (topG_range (aa_geom A)) as TG.
  pose proof (benv_of_K (K0 Kc) HL A1 HCI1 rho tp tr md HK) as BE. destruct BE as [_ _ HQP HAU _ _ _].
  destruct (batch_slot A1 HQP HAU HG (mkQB a [] s) ltac:(rewrite (qall_A1 A1 HTH1), HGL1; left; reflexivity)) as (y & Ey & Y0 & _ & Y1 & _). cbn [qb_addr] in Ey. rewrite kUserSpaceSize_val in Y1.
  change (aa_geom A1) with (aa_geom A) in Ey.
  pose proof (SB_facts A HG) as (_ & SBF1 & SBF2). unfold HIGH_SHADOW_END in SBF1. rewrite kSpaceSize_val in SBF2.
  assert (EC : eval rho clsB = Z_to_bv 64 24) by (apply (clsB_val rho (ag_spacebeg (aa_geom A)) a y); try lia; assumption).
  assert (ECP : eval rho cptrC = Z_to_bv 64 y) by (apply (cptrC_val rho (ag_spacebeg (aa_geom A)) a y); try lia; assumption).
  rewrite (qb_id_val (aa_geom A) a [] s y Ey).
  assert (EcbC : eval rho cbC = Z_to_bv 64 (T + 208)) by (unfold cbC; apply ev_add_lit; [unfold vT; cbn [eval]; exact E151 | lia | lia | lia]).
  assert (Epcb : bv_unsigned (eval rho pcbF) = T + 2128).
  { unfold pcbF, add. rewrite U_add, U_mul. fold (add vT (SLit 208)). fold cbC. rewrite EcbC, EC. change (eval rho (SLit 80)) with (Z_to_bv 64 80). rewrite !u64_lit by lia. unfold M64v.
    rewrite (Z.mod_small (24 * 80)) by lia. rewrite Z.mod_small by lia. lia. }
  assert (EvT : bv_unsigned (eval rho vT) = T) by (unfold vT; cbn [eval]; rewrite E151, u64_lit by lia; reflexivity).
  set (R := map carve_obj N_2a).
  set (rho3 := rho_absorb rho R (vms md tp ms)). set (v3 := view segsA (rm rho3)). set (v := view segsA (rm rho)) in *.
  destruct (absorb_view_cells segsA rho _ tr (vms md tp ms) (vmd md) (K24 g) R pcbF 0 4 _ Hsm (Ly_objs2 g) ltac:(left; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia) ltac:(rewrite Epcb; lia) ltac:(rewrite Epcb; lia)) as [AV1 PR1].
  destruct (absorb_view_cells segsA rho _ tr (vms md tp ms) (vmd md) (K24 g) R pcbF 20 24 _ Hsm (Ly_objs2 g) ltac:(right; left; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia) ltac:(rewrite Epcb; lia) ltac:(rewrite Epcb; lia)) as [AV2 PR2].
  destruct (absorb_view_cells segsA rho _ tr (vms md tp ms) (vmd md) (K24 g) R vT 2768 3168 _ Hsm (Ly_objs2 g) ltac:(right; right; left; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia) ltac:(rewrite EvT; lia) ltac:(rewrite EvT; lia)) as [_ PR3].
  fold rho3 v3 in AV1, PR1, AV2, PR2, PR3. rewrite Epcb in AV1, PR1, AV2, PR2. rewrite EvT in PR3.
  assert (C_cnt3 : cell_ok v3 (mkACell (T + 2128 + 0) 4 2)) by exact (av_cell v3 (T + 2128) 0 4 _ _ rho (fun j => AV1 _ _ _ j (or_introl eq_refl)) eq_refl).
  assert (C_slot3 : cell_ok v3 (mkACell (T + 2128 + 20) 4 y)) by exact (av_cell v3 (T + 2128) 20 4 _ _ rho (fun j => AV2 _ _ _ j (or_introl eq_refl)) ECP).
  clear AV1 AV2.
  set (P := fun z : Z => (T + 2128 <= z < T + 2132) \/ (T + 2148 <= z < T + 2152) \/ (T + 2768 <= z < T + 3168)).
  assert (PD : forall z, P z \/ ~ P z) by (intros z; unfold P; lia).
  assert (PT : forall z, P z -> T + 2128 <= z < T + 3168) by (intros z Hz; unfold P in Hz; lia).
  assert (INRG : forall x, in_ranges rho R x -> P (bv_unsigned x)).
  { intros x (o & Ho & Hz). unfold P. destruct Ho as [<-|[<-|[<-|[]]]]; unfold carve_obj, carved in Hz; rewrite obj_range_mk in Hz by lia; cbn [fst snd] in Hz;
      rewrite ?Epcb, ?EvT in Hz; lia. }
  destruct (absorb_out rho R (vms md tp ms) P INRG) as [FR FRrm]. fold rho3 v3 v in FR, FRrm.
  assert (PPR : forall z, P z -> v3 z <> None).
  { intros z Hz. destruct Hz as [Hz|[Hz|Hz]]; [destruct (PR1 z ltac:(lia)) as [x Hx] | destruct (PR2 z ltac:(lia)) as [x Hx] | destruct (PR3 z ltac:(lia)) as [x Hx]]; rewrite Hx; discriminate. }

  assert (HK3 : K0 Kc (push_cache (set_q A1 [] (tmp' ++ rest)) 24 y) rho3 tp tr md).
  { rewrite <- (qb_id_val (aa_geom A) a [] s y Ey). change (aa_geom A) with (aa_geom A1).
    apply (kq_push_batch segsA (K0 Kc) HL A1 rho rho3 tp tr md [] (tmp' ++ rest) (mkQB a [] s) HTH1 HGL1 eq_refl HCI1 ltac:(rewrite HK1; reflexivity)); [intros i; reflexivity | intros l; reflexivity | | | | | exact HK].
    - intros z NQ NPZ. fold v3 v. destruct (PD z) as [Hp|Np]; [|exact (FR z Np)]. exfalso. unfold push_zone, pc_entry in NPZ. change (aa_geom A1) with (aa_geom A) in NPZ. fold T in NPZ. rewrite HK1 in NPZ.
      destruct Hp as [Hp|[Hp|Hp]]; [apply NPZ; left; lia | apply NPZ; right; lia | apply NQ; right; right; unfold qstat_zone; change (aa_geom A1) with (aa_geom A); fold T; lia].
    - intros z _ Hd. fold v3. fold v in Hd. destruct (PD z) as [Hp|Np]; [exact (PPR z Hp) | rewrite (FR z Np); exact Hd].
    - fold v3. unfold pc_entry. change (aa_geom A1) with (aa_geom A). fold T. rewrite HK1. replace (T + 0xd0 + 80 * 24) with (T + 2128 + 0) by lia. exact C_cnt3.
    - fold v3. unfold pc_entry. change (aa_geom A1) with (aa_geom A). fold T. rewrite HK1. change (aa_geom A1) with (aa_geom A). rewrite (qb_id_val (aa_geom A) a [] s y Ey).
      replace (T + 0xd0 + 80 * 24 + 16 + 4 * 1) with (T + 2128 + 20) by lia. exact C_slot3. }

  assert (QF_OUT : forall z, q_foot A1 z -> ~ P z) by (intros z QF HP; pose proof (HSEP z QF) as NT; fold T in NT; pose proof (PT z HP); lia).
  assert (HR3 : RMEM2 v3 (aa_geom A1) tmp' rest).
  { destruct HRM as (HBM & HLT & HLR & HTHD & HGH). change Inv.QG with QG in *. change (aa_geom A1) with (aa_geom A) in *.
    assert (INQ : forall b, In b (tmp' ++ rest) -> In b (qall A1)) by (intros b Hb; rewrite (qall_A1 A1 HTH1), HGL1; right; exact Hb).
    split; [|split; [|split; [|split]]].
    - apply Forall_forall. intros b Hb.
      apply (batch_mem_frame A1 v v3 b (proj1 (Forall_forall _ _) (proj1 HQP) b (INQ b Hb))); [|exact (proj1 (Forall_forall _ _) HBM b Hb)].
      intros z Hz. apply FR. apply QF_OUT. unfold q_foot. fold (qall A1). apply Exists_exists. exists b. split; [exact (INQ b Hb)|]. unfold bfoot in Hz.
      destruct Hz as [Hz|Hz]; [left; unfold kQuarantineBatchSize in *; lia | right]. apply Exists_exists in Hz as (it & Hit & Hz). apply Exists_exists. exists it.
      split; [exact Hit|]. unfold ifoot, it_ab in Hz. exact Hz.
    - apply qlinks_to_0. apply (qlinks_to_frame v v3 tmp' 0); [|apply qlinks_to_0; exact HLT].
      intros b z Hb Hz. apply FR. apply QF_OUT. unfold q_foot. fold (qall A1). apply Exists_exists. exists b. split; [apply INQ; apply in_or_app; left; exact Hb|]. left. unfold kQuarantineBatchSize. lia.
    - apply qlinks_to_0. apply (qlinks_to_frame v v3 rest 0); [|apply qlinks_to_0; exact HLR].
      intros b z Hb Hz. apply FR. apply QF_OUT. unfold q_foot. fold (qall A1). apply Exists_exists. exists b. split; [apply INQ; apply in_or_app; right; exact Hb|]. left. unfold kQuarantineBatchSize. lia.
    - destruct HTHD as (Q1 & Q2 & Q3 & Q4). unfold qhdr_repr. fold T in Q1, Q2, Q3, Q4 |- *.
      assert (TOUT : forall z, T + 0x50 <= z < T + 0x70 -> v3 z = v z) by (intros z Hz; apply FR; intros HP; pose proof (PT z HP); lia).
      split; [eapply cell_ok_frame1; [|exact Q1]; cbn; intros z Hz; apply TOUT; lia|]. split; [intros X; exfalso; exact (X eq_refl)|].
      split; [eapply present_frame; [|exact Q3]; intros z Hz; apply TOUT; lia | eapply cell_ok_frame1; [|exact Q4]; cbn; intros z Hz; apply TOUT; lia].
    - destruct HGH as (Q1 & Q2 & Q3 & Q4). unfold qhdr_repr.
      assert (GOUT : forall z, QG + 160 <= z < QG + 192 -> v3 z = v z) by (intros z Hz; apply FR; intros HP; pose proof (PT z HP); unfold QG in *; lia).
      split; [eapply cell_ok_frame1; [|exact Q1]; cbn; intros z Hz; apply GOUT; lia|].
      split; [intros NE; destruct (Q2 NE) as [Qa Qb]; split; (eapply cell_ok_frame1; [|eassumption]); cbn; intros z Hz; apply GOUT; lia|].
      split; [eapply present_frame; [|exact Q3]; intros z Hz; apply GOUT; lia | eapply cell_ok_frame1; [|exact Q4]; cbn; intros z Hz; apply GOUT; lia]. }
  assert (HF3 : FRM A0 rho0 rho3).
  { apply (FRM_absorb_QFP A0 rho0 rho rho3 P PD ltac:(intros i; reflexivity) ltac:(intros l; reflexivity)); [| exact FR | exact FRrm | exact HFRM].
    intros z Hz. pose proof (PT z Hz) as PTz. split; [|unfold SHADOW_BAND_LO, SHADOW_BAND_HI in *; lia].
    destruct HQP0 as (ESB & _). assert (EG : aa_geom A = aa_geom A0) by (unfold same_but_qcs in ESB; rewrite ESB; reflexivity).
    destruct (Z_lt_dec z (T + 2768)) as [|]; [right; left; rewrite <- EG; fold T; lia | left; right; right; unfold qstat_zone; rewrite <- EG; fold T; lia]. }
  set (TJ := (fun (_ : valuation) (_ : list word) (_ : list event) (_ : Model) => True) : jpredA).
  assert (HT : SPA segsA TJ (Ly g) rho tp (tr, mkCfg ms md)) by (split; [exact (proj1 H) | exact I]).
  pose proof (SPA_unobj segsA TJ rho (Ly g) (K24 g) R tp tr ms md (Ly_objs2 g) HT (fun x => x)) as HU. cbn zeta in HU. fold rho3 in HU.
  exists rho3. split; [|split; [intros i; reflexivity | unfold rho3; rewrite eval_absorb; exact EC]].
  split; [exact (proj1 HU)|]. cbn [w_tr w_cfg cfg_model fst snd]. split; [exact HK3|]. split; [exact HR3 | exact HF3].
Qed.
End ExitG.

Definition T_x (g : bool) : strans := ltac2:(tb__ "0|2|
S92S45Vg;A1U10S13S27S98S16S27A1A3S16S22A1S16S8A1S79S88S91S13S12S12S14S21A2M0S21A2M1S11G0S21S11S14S21U0Zeddb8A4Zeddc0A4S16G1A1A3A9").
Lemma T_x_ok : ltac2:(tb__ "0|0|
S15S24S15S97S47R1A1A1S19A3Fg;"). Proof. intros [|]; vm_cast_no_check (eq_refl true). Qed.
Definition DSX (ctx pcb : Z) : list dspec := ltac2:(tb__ "0|4|
S3dS27S12S27S21A2S27S11S27S21R1S0S21Lx;S1cS0S21S1cS12S0S21A2M0S21S1cS12G0S21A2S17S12S12S21S14A2S0A2A1R1A3A3A3S21Z0Lz;S22Vctx;Li;S5eS0S0Vpcb;Lb;La;M1Lop;M2G2S5fG1Lop;M3G3S15S23S0Vpcb;La;Lw;Lsgn;S22S0S21Vpcb;Lk0;Li;Ll;X0x8A4Lk;S4cA4").
Lemma Lz_objs : ltac2:(tb__ "0|2|
S15S21S21S24S17S2A1S3S29S94S47R3A1M0A1M1A1A1S18S2S7dG1S96G0A1A2S3dS7aS2S7cS49R2R1A2A4A3A3Fpcb;Fctx;Fg;").
Proof. intros g ctx pcb. change (map dobj (DSX ctx pcb)) with (map carve_obj N_D2b). revert g. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Lz_ref : ltac2:(tb__ "0|0|
S15S24S15S7bS2S2S7eS3S29S95S47R1A1A1A1A1S3S29S8aA1A1A5S19A3Fg;"). Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Lz_pre : ltac2:(tb__ "0|0|
S15S24S15S9bS8S8S9aS8SfR1A1S10S29S45R2A1A1A1A3Lf;S86S8cA1A3S19A3Fg;"). Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Ltac rtc_cellx HR := first [ exact (cells_ok_nth _ _ 0%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 1%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 2%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 3%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 4%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 5%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 6%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 7%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 8%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 9%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 10%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 11%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 12%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 13%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 14%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 15%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 16%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 17%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 18%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 19%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 20%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 21%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 22%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 23%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 24%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 25%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 26%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 27%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 28%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 29%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 30%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 31%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 32%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 33%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 34%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 35%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 36%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 37%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 38%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 39%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 40%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 41%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 42%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 43%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 44%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 45%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 46%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 47%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 48%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 49%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 50%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 51%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 52%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 53%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 54%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 55%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 56%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 57%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 58%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 59%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 60%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 61%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 62%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 63%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 64%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 65%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 66%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 67%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 68%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 69%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 70%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 71%nat _ HR eq_refl) ].

Section ExitH.
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variables (A0 : AA) (rho0 : valuation).

Lemma ro_allX : ltac2:(tb__ "0|4|
S2eS4S17S5cQ40M0A1M1A1S17S85A1S84S65VKc;R5R4R3R2R1A6S24S15S2fR6A1S19A3S24S33S2dR7A1S2dVA0;A1A3S24G1S9R7S6aA2S5bG0Z18M2A2A3S24G1S5R8Pc9A2S5bG0S77G2A1A2A3S40S7aS93VA0;R9A2S49S35S2dRaA1M3A1S83S36G3A1Z850A2A2A3F_;F_;F_;F_;F_;Fmd;Ftr;Ftp;Fr;FA';").
Proof.
  intros A' r tp tr md HK HCI EG EC E201. pose proof (K0_laws Kc HKc) as HL.
  destruct (kq_facts segsA (K0 Kc) HL A' r tp _ _ HK) as [HG HRIG HRTC _ _ _ HCLS _ _ _ _ _ _].
  destruct HRIG as (E151 & E152 & E155 & E156).
  assert (HR : cells_ok (view segsA (rm r)) (rtc_cells RTC_A (aa_geom A'))) by exact HRTC.
  pose proof (HCLS HCI 24 ltac:(lia)) as CV. pose proof (cv_max _ _ _ _ _ CV) as C_max. pose proof (cv_size _ _ _ _ _ CV) as C_sz. unfold pc_entry in C_max, C_sz.
  change (max_count 24) with 2 in C_max. change (Size 24) with 8192 in *.
  pose proof (geom_nums _ HG) as (_ & _ & _ & T0 & T1 & _ & C0 & C1' & _ & _ & _ & _ & _ & TG).
  pose proof (geom_bands _ HG) as (_ & _ & _ & _ & _ & CI & _). unfold IMG_LO, IMG_HI in CI.
  assert (CB : ag_ctx (aa_geom A') + 0x1000 <= SHADOW_BAND_LO \/ SHADOW_BAND_HI <= ag_ctx (aa_geom A')) by (destruct HG as (_ & _ & _ & (_ & _ & _ & _ & X0) & _); exact X0).
  assert (TB : ag_thread (aa_geom A') + 0x1000 <= SHADOW_BAND_LO \/ SHADOW_BAND_HI <= ag_thread (aa_geom A')) by (destruct HG as (_ & _ & (_ & _ & _ & _ & _ & X0) & _); exact X0).
  unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in CB, TB.
  set (T := ag_thread (aa_geom A')) in *. set (CTX := ag_ctx (aa_geom A')) in *.
  assert (EcbC : eval r cbC = Z_to_bv 64 (T + 208)) by (unfold cbC; apply ev_add_lit; [unfold vT; cbn [eval]; exact E151 | lia | lia | lia]).
  assert (Epcb : eval r pcbF = Z_to_bv 64 (T + 2128)).
  { apply bv_eq. unfold pcbF, add. rewrite U_add, U_mul. fold (add vT (SLit 208)). fold cbC. rewrite EcbC, EC. change (eval r (SLit 80)) with (Z_to_bv 64 80). rewrite !u64_lit by lia. unfold M64v.
    rewrite (Z.mod_small (24 * 80)) by lia. rewrite Z.mod_small by lia. lia. }
  unfold DSX, N_D2b, N_rti, szS, vCTX. cbn [map app fst].
  repeat apply Forall_cons; try apply Forall_nil; apply (ro_cond_intro A0 (mkSC 0 0 0));
    try (unfold PG; lia); try reflexivity;
    try (cbn [eval]; exact E152); try exact Epcb;
    try (unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia).
  all: try (intros z Hz; cbv [pcbF add] in Hz; split; [|unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *; lia];
            first [ right; left; unfold qrtc_zone; rewrite <- EG; fold CTX; unfold Inv.QG; lia
                  | right; right; unfold qrtc2_zone; lia
                  | left; right; left; rewrite <- EG; fold T; lia ]).
  all: repeat apply Forall_cons; try apply Forall_nil.
  all: cbv beta iota; eexists; (split; [first [reflexivity | exact E155 | exact E156 | exact E152 | exact E151 | exact E201]|]);
       cbv [pcbF add]; first [ rtc_cellx HR | (replace (T + 2128 + 4) with (T + 208 + 80 * 24 + 4) by lia; exact C_max) | (replace (T + 2128 + 8) with (T + 208 + 80 * 24 + 8) by lia; exact C_sz) ].
Qed.

Lemma qcf_x2b : ltac2:(tb__ "0|5|
S15S2eS17S2cA1M0G0S4S17S5cQ40M1A1M2A1S66S21S6cR7R1A2S6cVA0;R2A2F_;Fz;S24S15S2fR7A1S19A3S24S33S2dR8A1S2dVA0;A1A3S41S42S67S65VKc;A1M3VA0;Vrho0;R9R8R7A6S45RaA1R6R5R4A6S24G2S9R7S6aA2S5bG1Z18M4A2A3S24G2S5R8Pc9A2S5bG1S77G4A1A2A3S7fR9RbA2S26S4S4S25S41S42S67G3VA0;Vrho0;ReRdRcA6S79R1RaR9A6S7fR1RdA2A2Lrho5;A2F_;F_;F_;F_;F_;F_;F_;Fw;Ftp;Frho;Frest;Ftmp';FA';Fg;").
Proof.
  intros g A' tmp' rest rho tp [tr [ms md]] HQW HCI EG H EC E201 HVx.
  destruct (proj2 H) as (HK & HRM & HFRM). cbn [w_tr w_cfg cfg_model fst snd] in HK, HRM, HFRM.
  pose proof (K0_laws Kc HKc) as HL.
  pose proof (smatch_facts_hold _ _ _ _ (proj1 (proj1 H))) as HFa.
  assert (HFp : Forall (holds rho) (pre_facts DEPTH_R)).
  { apply Forall_forall. intros f Hf. pose proof (proj1 (forallb_forall _ _) (Lz_pre g) f Hf) as X0. apply existsb_exists in X0 as (f' & Hf' & E). apply sprop_eqb_sound in E. subst f'.
    exact (proj1 (Forall_forall _ _) HFa f Hf'). }
  pose proof HK as (_ & _ & _ & HTOP & _).
  set (TJ := (fun (_ : valuation) (_ : list word) (_ : list event) (_ : Model) => True) : jpredA).
  assert (HT : SPA segsA TJ (s_C (T_x g)) rho tp (tr, mkCfg ms md)) by (split; [exact (proj1 H) | exact I]).
  destruct (s_step (K0 Kc) HL A0 rho0 (zbF A') zloS zhiF ZUF (zsepF Kc A' rho tp tr md HKc HK) (T_x g) (JRD (K0 Kc) A0 rho0 A' tmp' rest)
              (DSX (ag_ctx (aa_geom A')) (ag_thread (aa_geom A') + 2128)) [] A' rho tp tr ms md (T_x_ok g)
              (JRD_stable (K0 Kc) HL A0 rho0 A' tmp' rest) HQW (Lz_objs g _ _) eq_refl HT HK HFRM (ro_allX A' rho tp tr md HK HCI EG EC E201))
    as (rho5 & H5 & V5 & RM5 & AG5 & EV).
  { intros HK3 HF3 EV3. set (rho3 := rho_absorb rho (map dobj (DSX (ag_ctx (aa_geom A')) (ag_thread (aa_geom A') + 2128))) (vms md tp ms)) in *. cbn [T_x s_bs combine rho_sets].
    split; [split; [exact HK3 | split; [rewrite EV3; exact HRM | exact HF3]]|].
    destruct (kq_facts segsA (K0 Kc) HL A' rho3 tp _ _ HK3) as [_ HRIG3 HRTC3 _ _ _ _ _ _ _ _ _ _].
    split; [|split; [|split; [|intros _; apply Forall_nil]]].
    - unfold T_x. cbn [s_N]. apply Forall_cons; [|apply Forall_nil].
      unfold sbS, carve_okq. cbn [eval]. rewrite u64_lit by lia.
      split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
      split; [unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia|].
      split; [intros off Hoff; split; [apply wok_of_imageA; lia | apply rd_of_imageA; lia]|].
      unfold cells_in_view. repeat apply Forall_cons; try apply Forall_nil.
      assert (HSB : cell_ok (view segsA (rm rho3)) (mkACell 0xeddb8 8 (ag_spacebeg (aa_geom A')))) by (unfold rtc_inv, rtc_cells in HRTC3; exact (cells_ok_nth _ _ 3 _ HRTC3 eq_refl)).
      eapply (civ_cell rho3 (rm rho3) 0 0xeddb8); [exact HSB | unfold vSB; cbn [eval]; exact (proj1 (proj2 (proj2 HRIG3))) | lia | lia].
    - unfold T_x. cbn [s_N s_ZDn map]. constructor; [|constructor].
      unfold in_zone, sbS, carve_obj, carved. rewrite obj_range_mk by lia. cbn [eval fst snd]. rewrite u64_lit by lia.
      split; [unfold ZUF; cbn; tauto|]. unfold zloS, zhiF, zbF. split; [lia|]. split; [lia|]. right. lia.
    - unfold T_x at 2. cbn [s_ZDo].
      apply (in_zone_same rho3 _ _ _ _ _ (ss_objs (ax_S DQI0)) ZD_fixS (Lz_ref g)).
      apply (in_zone_ext_list rho3 (zbS (ag_thread (aa_geom A')) (ag_ctx (aa_geom A')) (topG (aa_geom A')) 0) zloS (zhiS 0) ZUS).
      + apply (inz_fixS A' (0, 0) 0%nat (mkSC 0 0 0) rho3); [unfold top_high in *; exact HTOP|].
        apply Forall_forall. intros f0 Hf0. apply (holds_agree_vals NPRE rho rho3 f0); [split; [intros v0 _; reflexivity | intros l0; reflexivity] | exact (proj1 (forallb_forall _ _) pre_facts_below f0 Hf0) | exact (proj1 (Forall_forall _ _) HFp f0 Hf0)].
      + unfold ZD_fixS. repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; (split; [unfold ZUF; cbn; tauto | split; [reflexivity | split; reflexivity]]). }
  cbn [T_x s_bs combine rho_sets] in V5, AG5.
  assert (VV : forall v0, In v0 [166; 184; 185; 186; 187; 208]%positive -> rw rho5 v0 = rw rho v0).
  { intros v0 Hv. rewrite (V5 v0 (SVar v0)); [reflexivity|]. unfold T_x. cbn [s_M]. unfold MC, idm. apply in_map_iff. exists v0. split; [reflexivity | exact Hv]. }
  exists rho5. split; [exact H5|]. destruct HVx as (E184 & E185 & E186 & E187 & E208). unfold HVX. rewrite !VV by (cbn; tauto). tauto.
Qed.
End ExitH.
End SegQCF_exit.

(* [comment removed for export] *)
Module MallocHit2E.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "SVar"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "AE_A"; "KcA"; "Kc_ok"; "Pre_mallocI"; "JL_malloc_ok"; "J_alloc_preT"; "L_malloc_ok"; "Posts_malloc"; "@Corelib.Init.Datatypes"; "list"; "pair"; "prod"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@Corelib.Init.Logic"; "eq"; "False"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1"; "E_s1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP"; "E3r"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "cnt_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1"; "JG"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM"; "IMG_M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "dfp_static"; "@Stdlib.Lists.List"; "In"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fi.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RebuildM SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ao.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocS4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require be.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ba.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocS9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bg.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require br.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require q1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bi.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bx.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_wf DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require df.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require dl.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a8.CertMallocSPc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.CertMallocSPd OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ao.SpineMallocS3iW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SpineMallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.be.SpineMallocS7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineMallocS8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SpineMallocS5iW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bg.SpineMallocS6iW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bg.SpineMallocS7iW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bh.SpineMallocS8iW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bh.SpineMallocS9iW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.br.SpineMallocS9jW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q1.MallocHit2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineMallocE OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bx.SpineMallocEiW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.df.DepotCallHW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SpineMallocEc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SpineMallocS5t OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dl.MallocHitTail2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q1.MallocHitTail2E.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a8.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a8.CertMallocSPeW2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SpineMallocS12iW2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section HIT0E.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTM : ltac2:(tb__ "0|0|
S6S12VCST;R1A2S12S21R2A2S14F_;F_;Fa;").
Hypothesis HCSTD : ltac2:(tb__ "0|0|
S6S12VCST;R1A2S15S22R2A1A1F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let J (W : list ulink) (st : ustop) (A : AA) (Kc : KcA) : jpredA := ltac2:(tb__ "0|0|
ScVAInv;VW;Vst;VA;VKc;S4PcA1A6").
Let law_die : forall A rho tp md, AInv A rho tp md -> cell_ok (view segs (rm rho)) (mkACell 0x182f1c 4 0) := AInvA_die.
Let law_inv3 : forall A rho tp md, AInv A rho tp md -> inv3 A := AInvA_inv3.
Let W0 : list ulink := Wcan 2.
Let st0 : ustop := UStopLe.

Theorem emalloc_hit_2_P : ltac2:(tb__ "0|4|
S1cS8S2SfS1fQ40M0A1A1SfS11S17S19A2M1A1S18Vsegs;S16R3R2R1A5S1S23G1S10S17S19SdS7VW0;Vst0;A3SbVAInv;VCST;VXGL;R6R5A5A4R2A3S9R6A1S13S6S1dR8S20G0S3R6PcA2A2A2Z0A3S2S0Vsegs;S5Vsegs;S1eVW0;Vst0;RaR9R8A5M2S1bVW0;Vst0;Z4M3A3R1R7A5R5A3FrhoE;F_;S2S0Vsegs;S5Vsegs;G2S1aVW0;Vst0;G3Z8A4R1R7A5R5A3FrhoE;S0Vsegs;S5Vsegs;VJ;VW0;Vst0;RaR9A4SaS7VW0;Vst0;A3R8R7A5R5A3F_;F_;F_;F_;TQ;FPosts;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp Posts Q HPin HKc HREF HSEC.
  assert (HUS : stopJ_stable W0 st0) by (apply stopJ_stable_le).
  assert (HW : st0 = UStopLeOrPc -> W0 = []) by (intros E; discriminate E).
  apply (espine_s1 2%nat st0 4 law_die WC1_2 DC1_2 NXhi_0 NXlo_0 ECert1_0 A Kc rho tp Q HW HUS HKc Wa_0 Da_0 Wb_0 Fbh_0 Fbl_0); [|exact HSEC].
  intros rhoE1.
  apply (espine_s2c 2%nat st0 4 OVa_2 OVb_2 TABa_2 TABb_2 Wa'_2 Wb'_0 Da'_2 Db'_0 NXa_2 NXb_0 Fa_0 Fb_0 Ga_0 Gb_0 SKa_0 SKb_0 XXa_0 XXb_0 XFa_0 XFb_0
           W1a_0 W1ba_0 W1ca_0 W2a_0 W1ra_0 W2ra_0 W1b_0 W1bb_0 W1cb_0 W2b_0 W1rb_0 W2rb_0 sa_0 sra_0 sb_0 srb_0 ENTa_0 ENTra_0 ENTb_0 ENTrb_0
           SIDa_0 SIDra_0 SIDb_0 SIDrb_0 FB_0 FBr_0 NXC1g_0 s2_ecert_2 A Kc rho tp Q HW HUS HKc).
  2: { intros Hz0 rhoE2. apply (espine_s3r 2%nat st0 4 NXC2r_0 s3r_ecert_2 A Kc rho tp Q HUS HKc). exact (HREF Hz0). }
  intros rhoE2.

  apply (espine_s3p_cert 2%nat st0 4 NXC2p_0 s3p_ecert_2 A Kc rho tp Q HUS HKc).
  exact (emalloc_hit_tail_2_P CST XGL HCST HXGL HCSTM HCSTD A Kc rho tp Posts HPin HKc).
Qed.

Theorem emalloc_hit_2 : ltac2:(tb__ "0|3|
S1cS8S2SfS1fQ40M0A1A1S18Vsegs;S16R2R1SeS7VAInv;VCST;VXGL;VW0;Vst0;R4R3A8A5S1S9R4A1S13S6S1dR6S20G0S3R4PcA2A2A2Z0A3S2S0Vsegs;S5Vsegs;S1eVW0;Vst0;R8R7R6A5M1S1bVW0;Vst0;Z4M2A3R1R5A5R4A3FrhoE;F_;S2S0Vsegs;S5Vsegs;G1S1aVW0;Vst0;G2Z8A4R1R5A5R4A3FrhoE;S0Vsegs;S5Vsegs;VJ;VW0;Vst0;R8R7A4SaS7VW0;Vst0;A3R6R5A5R4A3F_;F_;F_;TQ;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp. exact (emalloc_hit_2_P A Kc rho tp (Posts_malloc AE_A AInv CST XGL W0 st0 A Kc) (or_intror (or_introl eq_refl))).
Qed.
End HIT0E.
End MallocHit2E.

