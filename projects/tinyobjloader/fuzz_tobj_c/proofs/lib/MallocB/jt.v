(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require PaidMunmap.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap Madvise.
From Stdlib Require NArith PArith.
From LinuxProcessSemantics.Riscv Require Decode DecodeC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require js.

(* [comment removed for export] *)
Module SegQS_tail.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@Corelib.Init.Logic"; "eq"; "and"; "or"; "not"; "ex"; "@Corelib.Init.Datatypes"; "bool"; "nat"; "cons"; "list"; "prod"; "pair"; "nil"; "true"; "option"; "Some"; "app"; "false"; "length"; "fst"; "snd"; "None"; "S"; "negb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "valuation"; "sv"; "SLit"; "SAlu"; "rw"; "cell"; "ss_objs"; "eval"; "rl"; "mkCell"; "reg_sv"; "DUnknown"; "mkObj"; "rm"; "sprop"; "ss_next"; "ob_dflt"; "obj_range"; "odefault"; "ss_pc"; "SPBranch"; "agree_below"; "dflt_writable"; "holds"; "ranges_disjoint"; "sprop_eqb"; "ss_facts"; "swf"; "tfact"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "modulo"; "of_nat"; "pow"; "sub"; "div"; "mul"; "opp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "sec_chunk"; "aa_geom"; "aa_sec"; "qbatch"; "ag_pab"; "sc_map_beg"; "ag_spacebeg"; "ag_thread"; "mkQB"; "topG"; "AA"; "aa_q_global"; "ag_ctx"; "ageom"; "sc_map_size"; "sc_size"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_setS"; "ax_X"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_spec"; "carve_obj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.SegQS_states"; "vH"; "vMS"; "EUd"; "EMd"; "VSX"; "C5"; "EUx"; "E5"; "EMx"; "LR"; "vLAST"; "vNCH"; "vPAB"; "EM"; "EU"; "LENS"; "vIDX"; "AM"; "AU"; "EUs"; "O_cidx"; "O_clast"; "O_csh"; "O_hh"; "O_hidx"; "O_ihdr"; "O_lidx"; "O_secg"; "O_secm"; "O_secn"; "O_secs"; "O_stS"; "SX"; "VS0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jt.SegQS_tail"; "KEEPX"; "DUo"; "EBEG"; "offzoneb"; "A2OLD"; "DUp"; "EEND"; "MB"; "ME"; "REFX"; "ZDX"; "zfind"; "ELEN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "ok_frameA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_zones"; "zdesc"; "in_zone"; "@Stdlib.Lists.List"; "nth_error"; "In"; "forallb"; "Forall2"; "existsb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "view"; "cell_ok"; "mkACell"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQtr"; "TR"; "JOK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jt.SegQS_tail.Tail"; "TENV"; "CHF"; "JPU"; "T_fin"; "DSR"; "DUZ"; "HVQ"; "NUMS"; "CLZ"; "NROS"; "itS"; "sbS"; "@Corelib.Init.Nat"; "sub"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SRL"; "instr"; "ALU_SLL"; "ALU_AND"; "Ecall"; "ALU_SUB"; "BC_GEU"; "aluop"; "mulop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "Sh"; "IMG_HI"; "HIGH_SHADOW_END"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "kPtrArrayReserve"; "HIGH_SHADOW_BEG"; "LOW_SHADOW_BEG"; "PG"; "SHADOW_GAP_BEG"; "is_primary"; "round_up"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "NPRE"; "add"; "vSB"; "@Corelib.Lists.ListDef"; "nth"; "Forall"; "map"; "skipn"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.im.SegQ3D_skel"; "HVS"; "HVI";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQS_glue"; "N_sec1"; "fam_ok"; "ZD_fixS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2"; "QW"; "sec_foot"; "QFP"; "QRD"; "qstat_zone"; "set_q"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.SegQ3D_inv"; "QP"; "JRI"; "CURB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ3M_glue"; "forallb2"; "same_rng"; "dspec"; "dobj"; "keepN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jk.SegQS_loop"; "REF1"; "XVALS"; "NX"; "UX"; "ZDNX"; "ZDU"; "ZD_ref"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "lt"; "eqb"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "instr_at"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "A_after"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.SegQ3D_states"; "RI"; "vIT"; "vS7"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ3R_loop"; "HVX"; "RMEM2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQS_lib"; "ro_cond"; "mkST"; "s_C"; "s_Cd"; "s_k"; "s_ok"; "uobj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf4"; "chunk_sh_zone"; "chunk_zone"; "sec_junk_zone"; "sec_tbl_zone"; "unmap_sec"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "obj_vars_all"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "cells_inside"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "pre_facts"; "top_high"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "SEC_INST"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SMGlue"; "coverb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.SegQ3DM"; "MI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.SegQ3D_qip"; "DQI0"; "N_rti"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQ3RM"; "idm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.SegQ3R_skel"; "FRM"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQ3_states"; "DEPTH_R"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jj.SegQS_k"; "band"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs"; "qall"; "qitems"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQpieceM"; "keepsM"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"].
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
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SegQ_wf3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.SegQ3D_qip OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.je.SegQ3D_qiq OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ3M_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.SegQS_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQS_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQS_scan OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQS_lib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jk.SegQS_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jj.SegQS_k.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import PaidMunmap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Madvise.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import SysCallA MmapA MmapFixedA MmapFixedA2 MmapNodesA MunmapSymA MadviseSpecA MadviseA.

Definition A2OLD : sv := ltac2:(tb__ "0|1|
S1eSacS1eSa6S1eSa7S1eSa6S1eSa6S5bS5cA3S1dN8A1A3S1dZ3A1M0A3S1dZ1A1A3S1eSa7S5bG0A3A3").
Definition EBEG : sv := ltac2:(tb__ "0|0|
S1eSaaS1eSa6S1eSa7S5bS1dZ3A1A3S1dZ7fff8fffA1A3S1dZfffffffffffff000A1A3").
Definition EEND : sv := ltac2:(tb__ "0|0|
S1eSaaS1eSa6S1eSa7S1eSa6S5cS5bA3S1dZ3A1A3S1dZ7fff8000A1A3S1dZfffffffffffff000A1A3").
Definition ELEN : sv := SAlu ALU_SUB EEND EBEG.
Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.

Lemma C5_swf : ltac2:(tb__ "0|0|
S9S8S3S8S36S53S60R2R1A2A1A1SfA3Fl;Ff;"). Proof. fam6; vmr. Qed.
Lemma C5_diff : ltac2:(tb__ "0|4|
S9S8S3S10ScSbScS1cS1cA2M0A1M1SbS29A1M2A2M3A1Sf8S53S62R2R1A2A1S53S60R2R1A2A1A2S11G3SdG1G2SaG0SdS1cS1cS81S6aS5cA1A4SeG0A1A3SeS29A1A4A2A3Fl;Ff;"). Proof. fam6; vmr. Qed.
Lemma C5_set : ltac2:(tb__ "0|1|
S9S8S3S54S55S62R2R1A2S53S60R2R1A2M0A1A2G0A3Fl;Ff;"). Proof. fam6; vmr. Qed.
Lemma C5_next : ltac2:(tb__ "0|0|
S9S8S3S1S2aS53S60R2R1A2A1A1S2aS53S62R2R1A2A1A1A3Fl;Ff;"). Proof. fam6; vmr. Qed.

Lemma EUs_fact : ltac2:(tb__ "0|0|
S9S8S3S8S93S29S34S2fSadS7fS83A3A1S35S53S6eR2R1A2A1A1A3SfA3Fl;Ff;"). Proof. fam6; vmr. Qed.

Lemma EMx_objs : ltac2:(tb__ "0|0|
S9S8S3SbS1aA1S21S53S63R2R1A2A1A1S12S1aS21S53S5eR2R1A2A1A1SaS1aS71S5bS5cA2SeS1aA1A3A3A3Fl;Ff;"). Proof. fam6; vmr. Qed.
Lemma EMd_set : ltac2:(tb__ "0|2|
S9S8S3S54S55S63R2R1A2M0Se5S53G0A1S21S53S5eR2R1A2M1A1A1A2A2G1A3Fl;Ff;"). Proof. fam6; vmr. Qed.
Lemma EMd_node : ltac2:(tb__ "0|3|
S9S8S4S3S10Sa8A1Se4S52S2eS53S5eR2R1A2M0A1M1A1A2S11Sa8SabA2A3S4S3S1cS25G1Z11A2S1dZe9A1A3S4S3S1cS25G1ZaA2S7fA3S4S3S1cS25G1ZbA2S89A3S4S3S1cS25G1ZcA2S1dZ4A1A3S4S3SbScS1cS1cA2M2A1S56G0A1SeG2A1A3S3S8Se0SbcS2aG1A1A2SfA3A2A2A2A2A2A2Fl;Ff;").
Proof. fam6; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma AM_eq : ltac2:(tb__ "0|0|
S9S8S3S54Se6S5eR2R1A2S1dZ0A1A2S6cR2R1A2A3Fl;Ff;"). Proof. fam6; vmr. Qed.

Definition DUo (l : bool) : list sobj := ltac2:(tb__ "0|1|
Sc2S1aSa5S14S1aS21S53S61U1Vl;A2A1A1M0A2S8S9Ll;Vl;U9UbX8x2A2G0A3").
Lemma EUx_objs : ltac2:(tb__ "0|0|
S9S8S3SbS1aA1S21S53S61R2R1A2A1A1S12S1aS21S53S5dR2R1A2A1A1S7eR1A1A3A3Fl;Ff;"). Proof. fam6; vmr. Qed.
Lemma EUd_set : ltac2:(tb__ "0|2|
S9S8S3S54S55S61R2R1A2M0Se5S53G0A1S21S53S5dR2R1A2M1A1A1A2A2G1A3Fl;Ff;"). Proof. fam6; vmr. Qed.
Lemma EUd_node : ltac2:(tb__ "0|3|
S9S8S4S3S10Sa8A1Se4S52S2eS53S5dR2R1A2M0A1M1A1A2S11Sa8SabA2A3S4S3S1cS25G1Z11A2S1dZd7A1A3S4S3S1cS25G1ZaA2S5bA3S4S3S1cS25G1ZbA2S5cA3S4S3SbScS1cS1cA2M2A1S56G0A1SeG2A1A3S3S8Se0SbcS2aG1A1A2SfA3A2A2A2A2A2Fl;Ff;").
Proof. fam6; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma AU_eq : ltac2:(tb__ "0|0|
S9S8S3S54Se6S5dR2R1A2S1dZ0A1A2S6dR2R1A2A3Fl;Ff;"). Proof. fam6; vmr. Qed.

Definition DUp (l : bool) : list sobj := ltac2:(tb__ "0|3|
S12S1aSaS1aS78SaS1aS79SaS1aS77SaS1aS76SaS1aS7aSaS1aS74SaS1aS72S5bS5cA2SaS1aS73S5bS1dZ0A1M0A2SeS1aA1M1A3A3A3A3A3A3A3A3S8SbS1aA1Ll;Vl;SaS1aS70G0A1M2G1A3SaS1aS6fG0A1SaS1aG2SaS1aS75G1A3A3A3X8x2A3").
Lemma DUo_rng : ltac2:(tb__ "0|0|
S8S3S8Sd4S1aS1aSd5S7eR1A1S82R1A1A5SfA3Fl;"). Proof. intros [|]; vmr. Qed.
Lemma DUo_unk : ltac2:(tb__ "0|1|
S8S3S8S91S1aS1aS2dS8Lx;S2bR1A1SfS13S13S1S13Ll0;M0G0S0S1cSbScS0S0A2A1SbS37A1S13Ltmpl;Lflds;Lcnt;Lesz;X2dx6Lo;S7eR1A1A3SfA3Fl;"). Proof. intros [|]; vmr. Qed.

Definition KEEPX (l : bool) (rS r : valuation) : Prop := ltac2:(tb__ "0|0|
S4S1S5Se1R1SbcA2S90S1R1S5fVl;A1A3A2S3S57Q40A1S1fVr;R2A2S1fVrS;R2A2A3F_;Fv;S1S3SbS57Q8A1A1S23Vr;R1A2S23VrS;R1A2A3Fll;A2").
Lemma KEEPX_refl : ltac2:(tb__ "0|0|
S8S1bS7dR2R1R1A3Fr;Fl;"). Proof. intros l r. split; [intros v _; reflexivity | intros ll; reflexivity]. Qed.
Lemma KEEPX_trans : ltac2:(tb__ "0|0|
S8S1bS1bS1bS7dR4R3R2A3S7dR5R3R2A3S7dR6R5R3A3F_;F_;Fr3;Fr2;Fr1;Fl;").
Proof. intros l r1 r2 r3 (A1 & L1) (A2 & L2). split; [intros v Hv; rewrite (A2 v Hv); exact (A1 v Hv) | intros ll; rewrite L2; apply L1]. Qed.
Lemma KEEPX_keepsM : ltac2:(tb__ "0|0|
S8S1bS1bS109S103S5fR3A1A1R2R1A3S7dR4R3R2A3F_;Fr';Fr;Fl;").
Proof.
  intros l r r' [HA HM]. split.
  - intros v [Hv|Hv]; [symmetry; exact (proj1 HA v Hv)|]. rewrite (HM v (SVar v)); [reflexivity|]. unfold idm. apply in_map_iff. exists v. split; [reflexivity | exact Hv].
  - intros ll. symmetry. exact (proj1 (proj2 HA) ll).
Qed.
Lemma VSX_lt : ltac2:(tb__ "0|0|
S8S1S90S1R1S5fR2A1A3Se1R2Pd6A2F_;Fv;Fl;").
Proof. intros [|] v Hv; unfold VSX, VS0 in Hv; cbn [app In] in Hv; repeat (destruct Hv as [<-|Hv]; [reflexivity|]); destruct Hv. Qed.
Lemma KEEPX_agree : ltac2:(tb__ "0|0|
S8S1S1bS1bS30R3R2R1A3Se3Pd6R4A2S7dR6R4R3A3F_;F_;Fr';Fr;Fn;Fl;").
Proof.
  intros l n r r' (HA & HL & _) Hn. split; [|intros ll; symmetry; apply HL].
  intros v [Hv|Hv]; symmetry; apply HA; [unfold NPRE in Hv; lia | pose proof (VSX_lt l v Hv); lia].
Qed.
Lemma KEEPX_same : ltac2:(tb__ "0|0|
S8S1bS1bS1S3S57Q40A1S1fR2R1A2S1fR3R1A2A3Fv;S1S3SbS57Q8A1A1S23R3R1A2S23R4R1A2A3Fll;S7dR5R4R3A3F_;F_;Fr';Fr;Fl;").
Proof. intros l r r' H1 H2. split; [intros v _; apply H1 | exact H2]. Qed.
Lemma VS0_VSX : ltac2:(tb__ "0|0|
S8S1S90S1R1S7cA3S90S1R2S5fR3A1A3F_;Fv;Fl;"). Proof. intros l v Hv. unfold VSX. apply in_or_app. left. exact Hv. Qed.

Fixpoint zfind (refs : list sobj) (ds : list zdesc) (o : sobj) : option zdesc :=
  match refs, ds with
  | r :: refs', d :: ds' => if same_rng o r then Some d else zfind refs' ds' o
  | _, _ => None
  end.
Lemma zfind_sound : ltac2:(tb__ "0|1|
S1bS9S0F_;M0G0G0SbS9A1SbS1aA1SbS8dA1S1aS8dS92S1aS8dS8eR9R8R7R6R5A5R4R3A5S3S10S8dA1S88R5R4R3A3S11S8dR2A2A3S8eRbRaR9R8R7R4R3A7F_;F_;Fd;Fo;Fds;Frefs;FZU;Fzhi;Fzlo;Fzb;Frho;").
Proof.
  intros rho zb zlo zhi ZU refs ds o d HF. induction HF as [|r d0 refs' ds' Hr HF IH]; intros HZ; cbn [zfind] in HZ; [discriminate|].
  destruct (same_rng o r) eqn:E; [|exact (IH HZ)]. injection HZ as <-.
  destruct d0 as [[z lo] hi]. unfold in_zone in *. rewrite (same_rng_range rho o r E). exact Hr.
Qed.

Definition offzoneb (refs : list sobj) (ds : list zdesc) (z0 : nat) (objs : list sobj) : bool := ltac2:(tb__ "0|0|
S91S1aS1aS10S8dA1S8Lx;S88Vrefs;Vds;R1A3S8dS19S10aS15S9S0S15ScS9S0A2S0R1A3A3Vz0;A2A1Ld;S13X10x2Lo;Vobjs;A3").
Lemma offzone_sound : ltac2:(tb__ "0|4|
S1bS9S0Fx;M0G0G0SbS9A1SbS1aA1M1SbS8dA1S9G1S0S0S9S9S90S9R2R9A3S90S9R2RaA3S6S3S9R4R3A3A1S5S38S39RfR5A1M2RdR5A1A2S39RfR4A1M3ReR4A1A2A2S38S39G3RdR4A1A2S39G2ReR5A1A2A2A2F_;F_;F_;Fz';Fz;S92S1aS8dS8eRcRbRaR9R8A5R7R6A5S3S8S80R8R7R6R5A4SfA3S90S9R7RaA3S38S39ReR8A1RdR8A1A2R6A2S38R6S39RfR9A1RdR9A1A2A2S1aS90S1aR1RaA3S33S2cR13R2A2SdS0S0RaR9A4A2F_;Fo;F_;F_;F_;F_;F_;F_;Fhi;Flo;Fobjs;Fz0;Fds;Frefs;FZU;Fzhi;Fzlo;Fzb;Frho;").
Proof.
  intros rho zb zlo zhi ZU refs ds z0 objs lo hi Hsep HF HB HZ0 L1 L2 o Ho.
  pose proof (proj1 (forallb_forall _ _) HB o Ho) as X. cbv beta in X. destruct (zfind refs ds o) as [d|] eqn:EZ; [|discriminate X].
  pose proof (zfind_sound rho zb zlo zhi ZU refs ds o d HF EZ) as IZ. destruct d as [[z dlo] dhi]. cbn [fst] in X.
  apply negb_true_iff in X. apply Nat.eqb_neq in X. destruct IZ as (U & Z1 & Z2 & R). unfold SymState.ranges_disjoint.
  destruct (obj_range rho o) as [x y]. cbn [fst snd] in *.
  destruct R as [R|[R1 R2]]; [left; exact R|]. destruct (Hsep z z0 U HZ0 X) as [S|S]; lia.
Qed.

Definition REFX (l : bool) : list sobj := ltac2:(tb__ "0|0|
S12S1aSd9S12S1aSaS1aSf2SdcS5bA1A1SeS1aA1A3Sc1S59S1aS5aSdbVl;S5bA2A4A3A3").
Definition ZDX (l : bool) : list zdesc := ltac2:(tb__ "0|0|
S12S8dSdfS12S8dSaS8dSdeSeS8dA1A3SddVl;A1A3A3").
Lemma REF1_refl : ltac2:(tb__ "0|0|
S3S8Sd4S1aS1aSd5Sd9Sd9A5SfA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma EMd_off4 : ltac2:(tb__ "0|0|
S9S8S3S8S80S86R1A1S87R1A1U4S21S53S5eR2R1A2A1A1A4SfA3Fl;Ff;"). Proof. fam6; vmr. Qed.
Lemma EUd_off5 : ltac2:(tb__ "0|0|
S9S8S3S8S80S86R1A1S87R1A1U5S21S53S5dR2R1A2A1A1A4SfA3Fl;Ff;"). Proof. fam6; vmr. Qed.
Lemma C5_next214 : ltac2:(tb__ "0|0|
S9S8S3S8Se0Pd6S2aS53S60R2R1A2A1A1A2SfA3Fl;Ff;"). Proof. fam6; vmr. Qed.

Lemma eval_A2OLD : ltac2:(tb__ "0|6|
S1bS0S0S3S57Q40M0A1M1S22R3S5bA2S58G0R2A2M2A3S3G1S22R4S5cA2G2A3S38Z0M3R4A2S38Z8M4R4A2S3aS39R6R5A2S3dZ2Z2fA2A2S3S0S3bR7G4A2G3A3M5G5S3G1S22RaS81A2S22RaS6aS5cA1A2A3F_;F_;F_;F_;F_;F_;F_;Fmx;Fhx;Frho;").
Proof.
  intros rho hx mx Eh Em H0 H8 HT Hh Hm. unfold A2OLD.
  destruct (proj1 (Z.mod_divide hx 8 ltac:(lia)) Hh) as [kh Ekh]. destruct (proj1 (Z.mod_divide mx 8 ltac:(lia)) Hm) as [km Ekm].
  assert (E1 : eval rho (SAlu ALU_ADD (SAlu ALU_ADD vH vMS) (SLit (-8))) = Z_to_bv 64 (hx + mx - 8)).
  { replace (hx + mx - 8) with (hx + mx + -8) by lia. apply ev_add_lit; [apply (eval_add_z rho vH vMS hx mx Eh Em); lia | lia | lia | lia]. }
  assert (E2 : eval rho (SAlu ALU_SRL (SAlu ALU_ADD (SAlu ALU_ADD vH vMS) (SLit (-8))) (SLit 3)) = Z_to_bv 64 (kh + km - 1)).
  { rewrite (eval_srl3 rho _ (hx + mx - 8) E1 ltac:(lia)). f_equal. subst hx mx. replace (kh * 8 + km * 8 - 8) with ((kh + km - 1) * 8) by lia. apply Z.div_mul. lia. }
  assert (E3 : eval rho (SAlu ALU_ADD (SAlu ALU_SRL (SAlu ALU_ADD (SAlu ALU_ADD vH vMS) (SLit (-8))) (SLit 3)) (SLit 1)) = Z_to_bv 64 (kh + km)).
  { replace (kh + km) with (kh + km - 1 + 1) by lia. apply ev_add_lit; [exact E2 | lia | lia | lia]. }
  assert (E4 : eval rho (SAlu ALU_SRL vH (SLit 3)) = Z_to_bv 64 kh) by (rewrite (eval_srl3 rho vH hx Eh ltac:(lia)); f_equal; subst hx; apply Z.div_mul; lia).
  assert (E5 : eval rho (LENS vMS) = Z_to_bv 64 km) by (unfold LENS; rewrite (eval_srl3 rho vMS mx Em ltac:(lia)); f_equal; subst mx; apply Z.div_mul; lia).
  rewrite E5. apply bv_eq. rewrite (U_sub rho _ _ (kh + km) kh E3 E4 ltac:(lia) ltac:(lia)). rewrite u64_lit by lia. rewrite Z.mod_small by lia. lia.
Qed.

Definition MB (hx : Z) : Z := ltac2:(tb__ "0|1|
S3eS39S3fVhx;Z8A2Z7fff8fffA2M0S3bG0Z1000A2A2").
Definition ME (hx mx : Z) : Z := ltac2:(tb__ "0|1|
S3eS39S3fS39Vmx;Vhx;A2Z8A2Z7fff8000A2M0S3bG0Z1000A2A2").
Lemma mrange_facts : ltac2:(tb__ "0|5|
S0S0S38Z0M0R2A2S3S0S3bR3Z1000M1A2G0A3M2G2S38Z12000R4A2S4S3S0S3bS84R6A1M3G1A2G0A3S4S38Sb0R6A1G3A2S4S3aG3S85R6R5A2M4A2S4S38G4Sb0S39R6R5A2A1A2S3S0S3bS3eG4G3A2G1A2G0A3A2A2A2A2F_;F_;F_;F_;Fmx;Fhx;").
Proof.
  intros hx mx H0 Hh Hm HM. unfold MB, ME, Sh, SHADOW_OFF.
  destruct (proj1 (Z.mod_divide hx 4096 ltac:(lia)) Hh) as [kh Ekh]. destruct (proj1 (Z.mod_divide mx 4096 ltac:(lia)) Hm) as [km Ekm].
  assert (D1 : hx / 8 = kh * 512) by (subst hx; replace (kh * 4096) with (kh * 512 * 8) by lia; apply Z.div_mul; lia).
  assert (D2 : (mx + hx) / 8 = (km + kh) * 512) by (subst hx mx; replace (km * 4096 + kh * 4096) with ((km + kh) * 512 * 8) by lia; apply Z.div_mul; lia).
  assert (D3 : (hx + mx) / 8 = (km + kh) * 512) by (rewrite <- D2; f_equal; lia).
  rewrite D1, D2, D3.
  pose proof (Z.div_mod (kh * 512 + 2147454975) 4096 ltac:(lia)) as X1. pose proof (Z.mod_pos_bound (kh * 512 + 2147454975) 4096 ltac:(lia)) as X2.
  pose proof (Z.div_mod ((km + kh) * 512 + 2147450880) 4096 ltac:(lia)) as Y1. pose proof (Z.mod_pos_bound ((km + kh) * 512 + 2147450880) 4096 ltac:(lia)) as Y2.
  set (q1 := (kh * 512 + 2147454975) / 4096) in *. set (r1 := (kh * 512 + 2147454975) mod 4096) in *.
  set (q2 := ((km + kh) * 512 + 2147450880) / 4096) in *. set (r2 := ((km + kh) * 512 + 2147450880) mod 4096) in *.
  replace (kh * 512 + 2147454975 - r1) with (q1 * 4096) by lia. replace ((km + kh) * 512 + 2147450880 - r2) with (q2 * 4096) by lia.
  split; [apply Z.mod_mul; lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  replace (q2 * 4096 - q1 * 4096) with ((q2 - q1) * 4096) by lia. apply Z.mod_mul. lia.
Qed.
Lemma hmask4096 : and_hmask 18446744073709547520 = Some 4096. Proof. reflexivity. Qed.
Lemma eval_EBEG : ltac2:(tb__ "0|2|
S1bS0S3S57Q40M0A1M1S22R2S5bA2S58G0R1A2A3S4S38Z0R2A2S3aR2S3dZ2Z2fA2A2A2S3G1S22R4S7fA2S58G0S84R3A1A2A3F_;F_;Fhx;Frho;").
Proof.
  intros rho hx Eh Hx. unfold EBEG, MB. pose proof (Z.div_pos hx 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound hx 8 (2 ^ 44) ltac:(lia) ltac:(lia)).
  assert (E1 : eval rho (SAlu ALU_ADD (SAlu ALU_SRL vH (SLit 3)) (SLit 2147454975)) = Z_to_bv 64 (hx / 8 + 2147454975))
    by (apply (ev_add_lit rho _ (hx / 8) 2147454975 (eval_srl3 rho vH hx Eh ltac:(lia))); lia).
  pose proof (Z.mod_pos_bound (hx / 8 + 2147454975) 4096 ltac:(lia)).
  apply bv_eq. rewrite (U_and_hmask rho _ _ 4096 hmask4096), E1, !u64_lit by lia. reflexivity.
Qed.
Lemma eval_EEND : ltac2:(tb__ "0|4|
S1bS0S0S3S57Q40M0A1M1S22R3S5bA2S58G0R2A2M2A3S3G1S22R4S5cA2G2A3S38Z0R4A2M3G3S3aS39R6R5A2S3dZ2Z2fA2A2S3G1S22R8S83A2S58G0S85R7R6A2A2A3F_;F_;F_;F_;F_;Fmx;Fhx;Frho;").
Proof.
  intros rho hx mx Eh Em H0 H1 HT. unfold EEND, ME. pose proof (Z.div_pos (mx + hx) 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound (mx + hx) 8 (2 ^ 44) ltac:(lia) ltac:(lia)).
  assert (E0 : eval rho (SAlu ALU_ADD vMS vH) = Z_to_bv 64 (mx + hx)) by (apply (eval_add_z rho vMS vH mx hx Em Eh); lia).
  assert (E1 : eval rho (SAlu ALU_ADD (SAlu ALU_SRL (SAlu ALU_ADD vMS vH) (SLit 3)) (SLit 2147450880)) = Z_to_bv 64 ((mx + hx) / 8 + 2147450880))
    by (apply (ev_add_lit rho _ ((mx + hx) / 8) 2147450880 (eval_srl3 rho _ (mx + hx) E0 ltac:(lia))); lia).
  pose proof (Z.mod_pos_bound ((mx + hx) / 8 + 2147450880) 4096 ltac:(lia)).
  apply bv_eq. rewrite (U_and_hmask rho _ _ 4096 hmask4096), E1, !u64_lit by lia. reflexivity.
Qed.

Section Tail.
Variable K : AA -> jpredA.
Hypothesis HL : KQ_laws segsA K.
Hypothesis HKS : KQ_sec segsA K.
Variables (A0 : AA) (rho0 : valuation).
Variables (A : AA) (it : Z * Z) (i : nat) (ch : sec_chunk).
Variables (a s n0 : Z) (nd : nat) (its : list (Z * Z)) (tmp' rest : list qbatch).
Hypothesis HQW : ltac2:(tb__ "0|0|
S0ScbVA;R1A2ScbVA0;R2A2F_;Fz;").
Hypothesis HSF : ltac2:(tb__ "0|0|
S0SccVA;R1A2SccVA0;R2A2F_;Fz;").
Hypothesis HTH : aa_q_thread A = [].
Hypothesis HCI : aa_cache_inited A = true.
Hypothesis HGL : ltac2:(tb__ "0|0|
S3SbS45A1S4dVA;A1SaS45S4aVa;SaScS0S0A2Vit;Vits;A3Vs;A3S12S45Vtmp';Vrest;A3A3A3").
Hypothesis HPR : ltac2:(tb__ "0|0|
S3S8SbaS16S0S0Vit;A3A1S13A3").
Hypothesis HI : ltac2:(tb__ "0|0|
S3S10S42A1S8fS42S44VA;A1Vi;A3S11S42Vch;A2A3").
Hypothesis HU : ltac2:(tb__ "0|0|
S3S0S15S0S0Vit;A3S39S39S47Vch;A1Sb8A2Z800A2A3").
Hypothesis HSZ : ltac2:(tb__ "0|0|
S3S0S51Vch;A1S39SbbS16S0S0Vit;A3Z8A2Z1000A2A3").
Let J : jpredA := ltac2:(tb__ "0|0|
Sd2VK;VA0;Vrho0;VA;Va;Vn0;Vnd;SaScS0S0A2Vit;Vits;A3Vtmp';Vrest;Aa").
Let h : Z := sc_map_beg ch.
Let msz : Z := sc_map_size ch.

Definition HVQ (r : valuation) : Prop := ltac2:(tb__ "0|4|
S4S3S57Q40M0A1M1S1fVr;Pa5A2S58G0S3eS15S0S0Vit;A3Z10A2A2A3S4S3G1S1fVr;Pc8A2S58G0S46S43VA;A1A1A2A3S4S3G1S1fVr;Pc9A2S58G0S3cS14S42S44VA;A1A2A1A2A3S4S3G1S1fVr;PcfA2S58G0S3fS16S0S0Vit;A3M2S3dZ2Z20A2M3A2A2A3S3G1S1fVr;Pd1A2S58G0S3bG2G3A2A2A3A2A2A2A2").
Definition TENV (l : bool) (lst : sec_chunk) (r : valuation) : Prop := ltac2:(tb__ "0|0|
S4S9fVr;A1S4SfdVA;Vr;A2S4Sc0S29S32Vr;A1SfcS105A1A3S4SdaVA;Vi;Vch;Vl;Vlst;Vr;S5bA7S4SeaVr;Vtmp';A2Sc7Vr;Va;Vn0;Vnd;Vit;A5A2A2A2A2A2").
Lemma inVSX : ltac2:(tb__ "0|0|
S8S1S3S8S93S1Se2R1A1S5fR2A1A3SfA3S90S1R2S5fR3A1A3F_;Fv;Fl;").
Proof. intros l v H. apply existsb_exists in H as (x & Hx & E). apply Pos.eqb_eq in E. subst x. exact Hx. Qed.
Lemma TENV_keep : ltac2:(tb__ "0|0|
S8S42S1bS1bS99R4R3R2A3S7dR5R3R2A3S99R6R5R3A3F_;F_;Fr;FrS;Flst;Fl;").
Proof.
  intros l lst rS r (HV & HT & HF & XV & HX & HI') (KV & KL).
  assert (E : forall v, existsb (Pos.eqb v) (VSX l) = true -> rw r v = rw rS v) by (intros v Hv; apply KV; right; exact (inVSX l v Hv)).
  split; [|split; [|split; [|split; [|split]]]].
  - unfold HVQ in *. rewrite !E by (destruct l; reflexivity). exact HV.
  - unfold top_high in *. rewrite !KV by (left; unfold NPRE, V_DEPTH; reflexivity). exact HT.
  - apply Forall_forall. intros g Hg.
    apply (holds_agree_vals NPRE rS r g); [split; [intros v Hv; symmetry; exact (KV v (or_introl Hv)) | intros ll; symmetry; apply KL] | exact (proj1 (forallb_forall _ _) pre_facts_below g Hg) | exact (proj1 (Forall_forall _ _) HF g Hg)].
  - destruct XV as (X1 & X2 & X3 & X4). unfold XVALS, vH in *. cbn [eval] in *. rewrite !E by (destruct l; reflexivity).
    split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. intros ->. rewrite !E by reflexivity. exact (X4 eq_refl).
  - unfold HVX in *. rewrite !E by (destruct l; reflexivity). exact HX.
  - unfold HVI in *. rewrite !E by (destruct l; reflexivity). exact HI'.
Qed.

Definition CHF : Prop := ltac2:(tb__ "0|3|
S4S3S0S3bVh;Z1000M0A2Z0M1A3S4S3S0S3bVmsz;G0A2G1A3S4S38Z12000Vmsz;A2S4S38Sb1Vh;A2S4S3aS39Vh;Vmsz;A2M2S3dZ2Z2fA2A2S5S38G2Sb4A2S38Sb3Vh;A2A2A2A2A2A2A2").
Lemma chf_of_K : ltac2:(tb__ "0|0|
S1bSbS57Q40A1A1SbSc4A1Sc3VK;VA;R4R3R2R1A5S9aF_;Fmd;Ftr;Ftp;Fr;").
Proof.
  intros r tp tr md HK. destruct (chk_facts K HKS A r tp tr md i ch HK HI) as (C1 & C2 & C3 & C4 & C5 & C6 & _). cbv zeta in C1, C2, C3, C4, C5, C6.
  fold h msz in C1, C2, C3, C4, C5, C6. unfold PG in C1, C2. pose proof (topG_range (aa_geom A)) as TG.
  destruct (proj1 (Z.mod_divide msz 4096 ltac:(lia)) C2) as [km Ekm].
  unfold CHF. split; [exact C1|]. split; [exact C2|]. split; [lia|]. split; [exact C4|]. split; [lia | exact C6].
Qed.
Lemma chf_of_J : ltac2:(tb__ "0|0|
S54S1bSbS57Q40A1A1Sc5S8aS52VJ;R4R3R2R1A6S9aF_;Fw;Ftp;Fr;FSt;").
Proof. intros St r tp [tr [ms md]] Hw. destruct (proj2 Hw) as (HK & _). exact (chf_of_K r tp tr md HK). Qed.

Context {Q : assn} (X : trk Q).
Hypothesis HJX : JOK X J.

Lemma tail_B : ltac2:(tb__ "0|0|
S9S8S42S1bSbS57Q40A1A1S99R4R3R2A3S1bS7dR6R4R1A3S97VQ;VX;S8aS52VJ;S68R8R7A2R2R4A5A3F_;Fr;S97VQ;VX;S8aS52VJ;S7bR7R6A2R4R3A5A3F_;F_;Ftp;FrS;Flst;Fl;Ff;").
Proof.
  intros f l lst rS tp TE HC.
  apply (tr_pure X _ CHF); [intros w Hw; exact (chf_of_J _ _ _ _ Hw)|]. intros (CH1 & CH2 & CH3 & CH4 & CH5 & CH6). unfold IMG_HI in CH4.
  apply (seg_PB X f l J rS tp HJX). intros T M r1 HIN HKp. cbn [TsPB In] in HIN. destruct HIN as [E|[]]. injection E as <- <-.
  pose proof (KEEPX_keepsM l rS r1 HKp) as KV1. pose proof (TENV_keep l lst rS r1 TE KV1) as (_ & _ & _ & XV1 & _). destruct XV1 as (EH1 & EM1 & _). fold h msz in EH1, EM1.
  apply (tr_conseq X _ (SPA segsA J (C5 f l) r1 tp)).
  { intros w Hw. rewrite <- (C5_set f l). apply (SPA_restate segsA J r1 (E5 f l) (ax_S (C5 f l)) tp w _ _ (C5_swf f l) (C5_diff f l) (C5_next f l)); [|constructor|exact Hw].
    constructor; [|constructor]. cbn [fst snd].
    apply (eval_A2OLD r1 h msz EH1 ltac:(unfold vMS; cbn [eval]; exact EM1)); lia. }
  apply (qs_memset X f l J r1 tp HJX). intros r2 Hag.
  pose proof (KEEPX_agree l _ r1 r2 Hag ltac:(apply Pos.leb_le; exact (C5_next214 f l))) as KV2.
  apply (seg_PC X f l J r2 tp HJX). intros T M r3 HIN HKp3. cbn [TsPC In] in HIN. destruct HIN as [E|[E|[]]]; injection E as <- <-.
  -
    apply (tr_pure X _ False); [|intros []]. intros w Hw.
    pose proof (KEEPX_trans l _ _ _ (KEEPX_trans l _ _ _ KV1 KV2) (KEEPX_keepsM l r2 r3 HKp3)) as KV3.
    pose proof (TENV_keep l lst rS r3 TE KV3) as (_ & _ & _ & XV3 & _). destruct XV3 as (EH3 & EM3 & _). fold h msz in EH3, EM3.
    pose proof (SPA_facts_hold segsA _ r3 (EUs f l) tp w Hw) as HFa.
    pose proof (EUs_fact f l) as X0. apply existsb_exists in X0 as (g & Hg & E). apply sprop_eqb_sound in E. subst g.
    pose proof (proj1 (Forall_forall _ _) HFa _ Hg) as HB. cbn [holds branch_taken] in HB. apply negb_true_iff in HB. unfold bv_ltu in HB. apply Z.ltb_ge in HB.
    rewrite (eval_EBEG r3 h EH3 ltac:(lia)), (eval_EEND r3 h msz EH3 ltac:(unfold vMS; cbn [eval]; exact EM3) ltac:(lia) ltac:(lia) ltac:(lia)) in HB.
    destruct (mrange_facts h msz ltac:(lia) CH1 CH2 CH3) as (M1 & M2 & M3 & M4 & M5).
    assert (SHB : 0 <= Sh h /\ Sh (h + msz) < 2 ^ 63).
    { unfold Sh, SHADOW_OFF. pose proof (Z.div_pos h 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound (h + msz) 8 (2 ^ 44) ltac:(lia) ltac:(lia)). lia. }
    rewrite !u64_lit in HB by lia. lia.
  - apply HC. exact (KEEPX_trans l _ _ _ (KEEPX_trans l _ _ _ KV1 KV2) (KEEPX_keepsM l r2 r3 HKp3)).
Qed.

Lemma shz_band : ltac2:(tb__ "0|0|
S9aS0Sf3Vch;R1A2S106R2A1F_;Fz;F_;").
Proof.
  intros (C1 & C2 & C3 & C4 & C5 & C6) z Hz. unfold chunk_sh_zone in Hz. fold h msz in Hz. unfold IMG_HI in C4.
  pose proof (Sh_in_band h ltac:(lia)) as B1. pose proof (Z.div_le_upper_bound (h + msz) 8 (2 ^ 44) ltac:(lia) ltac:(lia)) as B2.
  unfold band, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END, Sh, SHADOW_OFF in *. lia.
Qed.
Lemma it_in_q : ltac2:(tb__ "0|0|
S90ScS0S0A2Vit;S108S107VA;A1A1A3").
Proof. rewrite (qitems_split A it a s its tmp' rest HTH HGL). left. reflexivity. Qed.
Lemma ch_foot : ltac2:(tb__ "0|0|
S0S5Sf3Vch;R1A2Sf4Vch;R1A2A2ScdVA0;R2A2F_;Fz;").
Proof.
  intros z Hz. right. right. right. apply HSF. right. right. right. apply Exists_exists. exists ch. split; [exact (nth_error_In _ _ HI)|].
  split; [exists it; split; [exact it_in_q | split; [exact HPR | exact HU]]|]. unfold chunk_sh_zone, chunk_zone in Hz. tauto.
Qed.
Lemma Sh_h_msz : ltac2:(tb__ "0|0|
S9aS3S0Sb0S39Vh;Vmsz;A2A1S39Sb0Vh;A1S3fVmsz;Z8A2A2A3F_;").
Proof.
  intros (C1 & C2 & _). apply Sh_add8.
  - destruct (proj1 (Z.mod_divide h 4096 ltac:(lia)) C1) as [k ->]. replace (k * 4096) with (k * 512 * 8) by lia. apply Z.mod_mul. lia.
  - destruct (proj1 (Z.mod_divide msz 4096 ltac:(lia)) C2) as [k ->]. replace (k * 4096) with (k * 512 * 8) by lia. apply Z.mod_mul. lia.
Qed.

Lemma shadow_dissolve : ltac2:(tb__ "0|2|
S9S8S1bSbS57Q40M0A1M1A1Sc5S3G1S22R3S5bA2S58G0Vh;A2A3S3G1S1fR4PcbA2S58G0Vmsz;A2A3S8aS52VJ;S63R7R6A2R5R4R3A6S7S1bS1bS4S8aS52VJ;S5eR9R8A2R1R6R5A6S4S1S3G1S1fR2R1A2S1fR8R1A2A3Fv;S1S3SbS57Q8A1A1S23R2R1A2S23R8R1A2A3Fll;A2A2Lr2;A2F_;F_;F_;Fw;Ftp;Fr;Fl;Ff;").
Proof.
  intros f l r tp [tr [ms md]] EH EMs H.
  destruct (proj2 H) as (HK & HCB & HRM & HFRM). cbn [w_tr w_cfg cfg_model fst snd] in HK, HCB, HRM, HFRM.
  pose proof (chf_of_K r tp tr md HK) as CH. pose proof CH as (C1 & C2 & C3 & C4 & C5 & C6). unfold IMG_HI in C4.
  pose proof (proj1 (proj1 H)) as Hsm. unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model] in Hsm.
  set (R := [O_csh vH vMS]). set (r2 := rho_absorb r R (vms md tp ms)). set (v := view segsA (rm r)). set (v2 := view segsA (rm r2)).
  pose proof (Sh_in_band h ltac:(lia)) as SB1. pose proof (Sh_h_msz CH) as SHE.
  pose proof (Z.div_pos msz 8 ltac:(lia) ltac:(lia)) as MD0. pose proof (Z.div_lt_upper_bound msz 8 (2 ^ 44) ltac:(lia) ltac:(lia)) as MD1.
  assert (RG : obj_range r (O_csh vH vMS) = (Sh h, Sh h + msz / 8)).
  { unfold O_csh, obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite (eval_BSHS r vH h EH ltac:(lia)), (soff_LENS r vMS msz ltac:(unfold vMS; cbn [eval]; exact EMs) ltac:(lia)).
    rewrite soff_lit_small by lia. unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in SB1. rewrite u64_lit by lia. f_equal. lia. }
  assert (IRZ : forall x, in_ranges r R x -> chunk_sh_zone ch (bv_unsigned x)).
  { intros x (o & Ho & Hz). destruct Ho as [<-|[]]. rewrite RG in Hz. cbn [fst snd] in Hz. unfold chunk_sh_zone. fold h msz. rewrite SHE. exact Hz. }
  assert (PRS : forall z, v z <> None -> v2 z <> None).
  { intros z Hd. destruct (IRdec r R z) as [[Hz Hin]|NI]; [|unfold v2, r2; rewrite (proj2 (absorb_io r R (vms md tp ms)) z NI); exact Hd].
    destruct Hin as (o & Ho & Hr). rewrite u64_lit in Hr by lia.
    destruct (SpineMallocS9.absorb_obj r _ tr (vms md tp ms) (vmd md) (ss_objs (ax_S (EMd f l))) R o Hsm (EMx_objs f l) Ho) as (_ & _ & X3 & _). cbn zeta in X3.
    assert (Do : ob_dflt o = DUnknown) by (destruct Ho as [<-|[]]; reflexivity).
    unfold obj_range in Hr. cbn [fst snd] in Hr.
    destruct (X3 (or_introl Do) (z - bv_unsigned (eval r (ob_base o))) ltac:(lia)) as [x Hx].
    unfold v2, r2. rewrite view_in by lia.
    replace (Z_to_bv 64 z) with (Z_to_bv 64 (bv_unsigned (eval r (ob_base o)) + (z - bv_unsigned (eval r (ob_base o))))) by (f_equal; lia).
    rewrite Hx. discriminate. }
  assert (EQF : forall z, ~ chunk_sh_zone ch z -> v2 z = v z).
  { intros z NC. apply (proj2 (absorb_io r R (vms md tp ms)) z). intros [Hz Hin]. apply NC. pose proof (IRZ _ Hin) as X0. rewrite u64_lit in X0 by lia. exact X0. }
  assert (HK2 : K A r2 tp tr md).
  { apply (kq_secshadow segsA K HKS A r r2 tp tr md it i ch it_in_q HPR HI HU); [intros i0; reflexivity | intros l0; reflexivity | | | exact HK].
    - intros z _ NC. exact (EQF z NC).
    - intros z _ Hd. exact (PRS z Hd). }
  destruct (CR_band K HL HKS A it i ch a s its tmp' rest HTH HCI HGL HI HU r tp tr md v v2 n0 nd HK) as [HCB2 HRM2]; try assumption.
  { intros z NB. apply EQF. intros HZ. exact (NB (shz_band CH z HZ)). }
  assert (HF2 : FRM A0 rho0 r2).
  { apply (FRM_absorb_gen A0 rho0 r r2 (fun z => 0 <= z < 2 ^ 64 /\ in_ranges r R (Z_to_bv 64 z)) (IRdec r R) ltac:(intros i0; reflexivity) ltac:(intros l0; reflexivity));
      [| | exact (proj2 (absorb_io r R (vms md tp ms))) | | exact HFRM].
    - intros z [Hz Hin]. left. apply ch_foot. left. pose proof (IRZ _ Hin) as X0. rewrite u64_lit in X0 by lia. exact X0.
    - intros x [_ Hin] HBx. rewrite Z_to_bv_bv_unsigned in Hin.
      apply (SpineMallocS9.absorb_defined r _ tr (vms md tp ms) (vmd md) (ss_objs (ax_S (EMd f l))) R x Hsm (EMx_objs f l)); [| exact Hin | unfold SHADOW_BAND_LO, LOW_SHADOW_BEG in HBx; unfold IMG_HI; lia].
      repeat constructor.
    - intros x NP. apply (proj1 (absorb_io r R (vms md tp ms))). intros Hin. apply NP. split; [apply urange|]. rewrite Z_to_bv_bv_unsigned. exact Hin. }
  set (TJ := (fun (_ : valuation) (_ : list word) (_ : list event) (_ : Model) => True) : jpredA).
  assert (HT : SPA segsA TJ (EMx f l) r tp (tr, mkCfg ms md)) by (split; [exact (proj1 H) | exact I]).
  pose proof (SPA_unobj segsA TJ r (EMx f l) (ss_objs (ax_S (EMd f l))) R tp tr ms md (EMx_objs f l) HT (fun x => x)) as HU2. cbn zeta in HU2. fold r2 in HU2. rewrite EMd_set in HU2.
  exists r2. split; [|split; [intros v0; reflexivity | intros ll; reflexivity]].
  split; [exact (proj1 HU2)|]. cbn [w_tr w_cfg cfg_model fst snd]. split; [exact HK2|]. split; [exact HCB2|]. split; [exact HRM2 | exact HF2].
Qed.

Lemma fam_shadow : ltac2:(tb__ "0|3|
S9S9aSc9R2S48S43VA;A1A1M0Vh;Vmsz;A4S38Sb2G0A2S5S4S38Sb7Sb0Vh;A1M1A2S38Sb0S39Vh;Vmsz;A2A1M2Sb9A2A2S4S38Sb6G1A2S38G2Sb2A2A2A2F_;F_;F_;Ff;").
Proof.
  intros f (C1 & C2 & C3 & C4 & C5 & C6) HFAM HSB. unfold IMG_HI in C4.
  unfold Sh, SHADOW_OFF, LOW_SHADOW_BEG, SHADOW_GAP_BEG, HIGH_SHADOW_BEG, HIGH_SHADOW_END in *.
  pose proof (Z.div_pos h 8 ltac:(lia) ltac:(lia)) as D0. pose proof (Z.div_le_upper_bound (h + msz) 8 (2 ^ 44) ltac:(lia) ltac:(lia)) as D1.
  destruct f as [|[|f]]; cbn [fam_ok] in HFAM.
  - left. pose proof (Z.div_le_upper_bound (h + msz) 8 268430848 ltac:(lia) ltac:(lia)). lia.
  - right. pose proof (Z.div_le_lower_bound h 8 2199291686912 ltac:(lia) ltac:(lia)). lia.
  - right. pose proof (Z.div_le_lower_bound h 8 2199291686912 ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma tail_M : ltac2:(tb__ "0|1|
S9S8S42S1bSbS57Q40A1A1S99R4R3R2A3S3S10S42A1S8fS42S44VA;A1M0Sa5S14S42G0A2U1A2A3S11S42R4A2A3Sc9R7S48S43VA;A1A1Vh;Vmsz;A4S1bS7dR8R6R1A3S97VQ;VX;S8aS52VJ;S69RaR9A2R2R6A5A3F_;Fr;S1bS7dR9R7R1A3S97VQ;VX;S8aS52VJ;S68RbRaA2R2R7A5A3F_;Fr;F_;F_;F_;F_;Ftp;FrS;Flst;Fl;Ff;").
Proof.
  intros f l lst rS tp TE Hl HFAM HC r KV.
  pose proof (TENV_keep l lst rS r TE KV) as (_ & _ & _ & XVr & _). destruct XVr as (EH & EMs & _). fold h msz in EH, EMs.
  apply (tr_conseq X _ (SPA segsA J (EMx f l) r tp)); [intros w Hw; exact (SPA_axforms segsA J _ r _ _ tp w (EMx_eq f l) Hw)|].
  apply (tr_glue X _ J (EMd f l) tp (fun r2 => KEEPX l rS r2)).
  { intros w Hw. destruct (shadow_dissolve f l r tp w EH EMs Hw) as (r2 & H2 & RW & RL). exists r2. split; [exact H2|]. exact (KEEPX_trans l _ _ _ KV (KEEPX_same l r r2 RW RL)). }
  intros r2 KV2. pose proof (TENV_keep l lst rS r2 TE KV2) as (HV2 & HT2 & HF2 & XV2 & _). pose proof XV2 as (EH2 & EM2 & _ & XF2). fold h msz in EH2, EM2.
  apply (tr_pure X _ CHF); [intros w Hw; exact (chf_of_J _ _ _ _ Hw)|]. intros CH. pose proof CH as (CH1 & CH2 & CH3 & CH4 & CH5 & CH6). unfold IMG_HI in CH4.
  destruct (mrange_facts h msz ltac:(lia) CH1 CH2 CH3) as (M1 & M2 & M3 & M4 & M5). set (nlit := ME h msz - MB h) in *.
  pose proof (Sh_in_band h ltac:(lia)) as SB1. pose proof (Sh_h_msz CH) as SHE.
  pose proof (Z.div_pos msz 8 ltac:(lia) ltac:(lia)) as MD0. pose proof (Z.div_lt_upper_bound msz 8 (2 ^ 44) ltac:(lia) ltac:(lia)) as MD1.
  unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in SB1.
  assert (EB : eval r2 EBEG = Z_to_bv 64 (MB h)) by (apply eval_EBEG; [exact EH2 | lia]).
  assert (EE : eval r2 EEND = Z_to_bv 64 (ME h msz)) by (apply eval_EEND; [exact EH2 | unfold vMS; cbn [eval]; exact EM2 | lia | lia | lia]).
  pose proof (EMd_node f l) as (N1 & N2 & N3 & N4 & N5 & N6 & N7). apply Pos.leb_le in N7.
  apply (tr_madvise X J J (EMd f l) r2 tp (fun _ => true) EBEG ELEN nlit HJX N7 N1 N2 N3 N4).
  - unfold ELEN. rewrite (U_sub r2 _ _ (ME h msz) (MB h) EE EB ltac:(lia) ltac:(lia)). unfold nlit. apply Z.mod_small. lia.
  - exact M5.
  - unfold nlit. lia.
  - exact N5.
  -
    unfold madvise_pre. intros tr ms md Hsp HJ. cbv zeta.
    destruct (pending_argsA segsA r2 tp (EMd f l) tr ms md Hsp) as (G0 & _). rewrite N3, EB in G0. rewrite G0. rewrite (u64_lit (MB h)) by lia.
    rewrite tp_dontneed_keep.
    destruct HJ as (HK & HCB & HRM & HFRM).
    pose proof (qsenv_intro K HL HKS A it i ch a s its tmp' rest HTH HCI HGL HI HU HSZ r2 tp tr md n0 nd HK HCB HV2) as QS.
    destruct (exit_carve K A it i ch HKS r2 tp tr md l lst vH REF1 HK QS HT2 HF2 Hl XV2 REF1_refl) as (_ & _ & Z1 & Z2 & Z3).
    assert (ZALL : Forall2 (in_zone r2 (zbE A i ch lst) zloS (zhiX (sc_map_size ch)) (ZUXl l)) (REFX l) (ZDX l)).
    { unfold REFX, ZDX. apply Forall2_app; [exact Z3|]. cbn [app]. constructor; [exact Z1 | exact Z2]. }
    assert (HLF : l = false -> (i < length (aa_sec A) - 1)%nat) by (intros E; exact (proj1 (XF2 E))).
    pose proof (zsepE K A it i ch HKS r2 tp tr md l lst HK QS Hl HLF) as HSEPZ.
    destruct (kq_facts segsA K HL A r2 tp _ _ HK) as [HG _ _ _ _ _ _ _ _ _ _ _ _].
    pose proof (geom_old _ HG) as GO. destruct GO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSB & _).
    pose proof (fam_shadow f CH HFAM HSB) as FSH. rewrite SHE in FSH.
    destruct (ks_madvise_ok segsA K HKS A r2 tp tr md HK (Z_to_bv 64 (MB h)) nlit) as [GATE LAZY].
    { rewrite u64_lit by lia. unfold PG. exact M1. } { unfold PG. exact M5. } { unfold nlit. lia. }
    { rewrite u64_lit by lia. unfold nlit. unfold LOW_SHADOW_BEG, SHADOW_GAP_BEG, HIGH_SHADOW_BEG, HIGH_SHADOW_END in *. lia. }
    rewrite (u64_lit (MB h)) in LAZY by lia.
    assert (DISJ : forall o, In o (ss_objs (ax_S (EMd f l))) -> SymState.ranges_disjoint (obj_range r2 o) (MB h, MB h + nlit)).
    { apply (offzone_sound r2 (zbE A i ch lst) zloS (zhiX (sc_map_size ch)) (ZUXl l) (REFX l) (ZDX l) 4%nat _ (MB h) (MB h + nlit) HSEPZ ZALL (EMd_off4 f l)).
      - destruct l; cbn; tauto.
      - unfold zbE, zbX, zloS, LOW_SHADOW_BEG. lia.
      - unfold zbE, zbX, zhiX, nlit. unfold LOW_SHADOW_BEG, SHADOW_GAP_BEG, HIGH_SHADOW_BEG, HIGH_SHADOW_END in *. lia. }
    split; [unfold page_size; exact M1|]. split; [unfold nlit; lia|]. split; [exact GATE|]. split; [exact LAZY|]. split; [exact DISJ|].
    split; [intros rr y Hin; rewrite N6 in Hin; destruct Hin|].

    set (aw := Z_to_bv 64 (MB h)). set (nw := Z_to_bv 64 nlit).
    set (r4 := set_rm r2 (splice (rm r2) (rereserve_bytes tp) aw nw)). set (v2 := view segsA (rm r2)). set (v4 := view segsA (rm r4)).
    assert (INR : forall z, 0 <= z < 2 ^ 64 -> SysStep.in_range aw nw (Z_to_bv 64 z) = true <-> MB h <= z < MB h + nlit).
    { intros z Hz. rewrite SysStep.in_range_spec. unfold aw, nw. rewrite !u64_lit by (unfold nlit; lia). tauto. }
    assert (PAID : forall z, MB h <= z < MB h + nlit -> rm r2 (Z_to_bv 64 z) <> None -> page_mem (page_base (Z_to_bv 64 z)) tp = true).
    { intros z Hz Hd. destruct (smatch_pendingA_mem segsA r2 tp (EMd f l) tr ms md Hsp) as (_ & _ & HMF).
      assert (OUT : outside_all r2 (ss_objs (ax_S (EMd f l))) (Z_to_bv 64 z)).
      { apply Forall_forall. intros o Ho. pose proof (DISJ o Ho) as D. unfold SymState.ranges_disjoint in D. cbn [fst snd] in D. cbv zeta. rewrite u64_lit by lia. lia. }
      pose proof (HMF _ OUT) as E. rewrite vms_mem in E. pose proof (LAZY (Z_to_bv 64 z) ltac:(rewrite u64_lit by lia; exact Hz)) as LZ.
      unfold hid in E. rewrite LZ in E. cbn [andb] in E. destruct (page_mem (page_base (Z_to_bv 64 z)) tp); [reflexivity|]. cbn [negb] in E. exfalso. apply Hd. rewrite <- E. reflexivity. }
    pose proof (ks_repr segsA K HKS A r2 tp tr md HK) as (SC1 & _). destruct (SC1 i ch HI) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PSH). fold h msz in PSH. rewrite SHE in PSH.
    assert (V4IN : forall z, MB h <= z < MB h + nlit -> v4 z = Some (Z_to_bv 8 0)).
    { intros z Hz. assert (Hz' : 0 <= z < 2 ^ 64) by (unfold nlit in Hz; lia). destruct (PSH z ltac:(unfold nlit in Hz; lia)) as [b Hb]. unfold v2 in Hb. rewrite view_in in Hb by lia.
      pose proof (rd_off_image (rm r2) z b ltac:(lia) Hb) as Hm.
      unfold v4, r4. rewrite view_in by lia. unfold rd_of. cbn [rm set_rm]. unfold splice. rewrite (proj2 (INR z Hz') Hz). unfold rereserve_bytes.
      rewrite (PAID z Hz ltac:(rewrite Hm; discriminate)). reflexivity. }
    assert (V4OUT : forall z, ~ (MB h <= z < MB h + nlit) -> v4 z = v2 z).
    { intros z NZ. unfold v4, v2. apply view_agree. intros Hz. unfold r4. cbn [rm set_rm]. unfold splice.
      destruct (SysStep.in_range aw nw (Z_to_bv 64 z)) eqn:EI; [exfalso; exact (NZ (proj1 (INR z Hz) EI)) | reflexivity]. }
    assert (RM4OUT : forall x : word, ~ (MB h <= bv_unsigned x < MB h + nlit) -> rm r4 x = rm r2 x).
    { intros x NZ. unfold r4. cbn [rm set_rm]. unfold splice. destruct (SysStep.in_range aw nw x) eqn:EI; [|reflexivity].
      exfalso. apply NZ. apply SysStep.in_range_spec in EI. unfold aw, nw in EI. rewrite !u64_lit in EI by (unfold nlit; lia). exact EI. }
    assert (INSH : forall z, MB h <= z < MB h + nlit -> chunk_sh_zone ch z) by (intros z Hz; unfold chunk_sh_zone; fold h msz; rewrite SHE; unfold nlit in Hz; lia).
    assert (PRS4 : forall z, v2 z <> None -> v4 z <> None).
    { intros z Hd. destruct (Z_le_dec (MB h) z) as [L1|L1]; [destruct (Z_lt_dec z (MB h + nlit)) as [L2|L2]|]; [rewrite (V4IN z (conj L1 L2)); discriminate | rewrite V4OUT by lia; exact Hd | rewrite V4OUT by lia; exact Hd]. }
    pose proof (smatch_pendingA_MI segsA _ _ _ _ _ _ Hsp) as HMI.
    assert (HKm : K A r2 tp tr (madvise_dontneed_next md aw nw)).
    { apply (kq_stable segsA K HL A r2 r2 tp tr md (madvise_dontneed_next md aw nw)); [split; [intros v0 _; reflexivity | split; [intros l0; reflexivity | intros x; reflexivity]] | | exact HK].
      apply (mat_equiv_dontneed segsA md tp aw nw HMI). intros x Hx. apply LAZY. unfold aw, nw in Hx. rewrite !u64_lit in Hx by (unfold nlit; lia). exact Hx. }
    split; [|split; [|split]].
    + apply (kq_secshadow segsA K HKS A r2 r4 tp tr _ it i ch it_in_q HPR HI HU); [intros i0; reflexivity | intros l0; reflexivity | | | exact HKm].
      * intros z _ NC. apply V4OUT. intros Hz. exact (NC (INSH z Hz)).
      * intros z _ Hd. exact (PRS4 z Hd).
    + apply (CR_band K HL HKS A it i ch a s its tmp' rest HTH HCI HGL HI HU r2 tp tr md v2 v4 n0 nd HK); [| exact PRS4 | exact HCB | exact HRM].
      intros z NB. apply V4OUT. intros Hz. exact (NB (shz_band CH z (INSH z Hz))).
    + apply (CR_band K HL HKS A it i ch a s its tmp' rest HTH HCI HGL HI HU r2 tp tr md v2 v4 n0 nd HK); [| exact PRS4 | exact HCB | exact HRM].
      intros z NB. apply V4OUT. intros Hz. exact (NB (shz_band CH z (INSH z Hz))).
    + apply (FRM_absorb_gen A0 rho0 r2 r4 (fun z => MB h <= z < MB h + nlit)); [intros z; lia | intros i0; reflexivity | intros l0; reflexivity | | | exact V4OUT | exact RM4OUT | exact HFRM].
      * intros z Hz. left. apply ch_foot. left. exact (INSH z Hz).
      * intros x Hx _. pose proof (V4IN _ Hx) as E. unfold v4 in E. rewrite view_in in E by apply urange. rewrite Z_to_bv_bv_unsigned in E.
        pose proof (rd_off_image (rm r4) (bv_unsigned x) _ ltac:(pose proof (urange x); lia) ltac:(rewrite Z_to_bv_bv_unsigned; exact E)) as Hm. rewrite Z_to_bv_bv_unsigned in Hm. rewrite Hm. discriminate.
  -
    unfold madvise_post. rewrite tp_dontneed_keep, AM_eq. set (r4 := set_rm r2 _).
    apply (seg_PD X f l J r4 tp HJX). intros T M r5 HIN HKp. cbn [TsPD In] in HIN. destruct HIN as [E|[]]. injection E as <- <-.
    apply HC. apply (KEEPX_trans l _ r4 _); [|exact (KEEPX_keepsM l r4 r5 HKp)].
    apply (KEEPX_trans l _ r2 _ KV2). apply KEEPX_same; intros; reflexivity.
Qed.

Definition DUZ (z : Z) : Prop := ltac2:(tb__ "0|0|
S5Sf4Vch;Vz;A2S5Sf5Vz;A1S5Sf6VA;Vi;Vz;A3ScfS43VA;A1Vz;A2A2A2A2").

Definition JPU (l : bool) (lst : sec_chunk) (rp : valuation) : jpredA := ltac2:(tb__ "0|f|
S1bSbS57Q40A1A1SbSc4A1Sc3S4VK;VA;Vrp;R3R2R1A5S4Sd3S94S52S28Vrp;A1M0A2M1Va;Vn0;Vnd;SaScS0S0A2Vit;Vits;A3A5S4SebG1S43VA;A1M2Vtmp';Vrest;A4S4Sf9SbcVrp;R4A3S4S0S6S9eR1A1A1S3S10S57Q8A1M3A1M4S94S52S28R6A1R2A3M5S94S52G0R2A3M6A3F_;Fz;S4S0S6S3G4S94S52G0R1A3S17G3A1M7A3A1S6S3G4G5G7A3A1F_;Fz;S4S95S94S52S28R4A1A2M8S96S39SfeZ38A2U8M9S3eS3cS14S42S44VA;A1A2A1Z1A2A3A2S4S95G8S96Zead00U4Z0A3A2S4S3S8Vl;S13A3S4S95S94S52S28R5A1A2MaS96S39S46G2A1S40Z8MbS3cVi;A1McA2A2MdG9S47Vlst;A1MeA3A2S95GaS96S39GeZ18A2G9GcA3A2A2F_;S4S3S8Vl;SfA3S0S4S38GdR1A2S3aR1S39GdGbA2A2A2S3G4S94S52S28R7A1R2A3G6A3F_;Fz;F_;S104VA0;Vrho0;R4A3A2A2A2A2A2A2A2A2A2A2Lmd;Ltr;Ltp;Lr;").
Lemma JPU_stable : ltac2:(tb__ "0|0|
S8S42S1bS8cS52SbcS9bR3R2R1A3A3Frp;Flst;Fl;").
Proof.
  intros l lst rp r r' tp tr md md' Hag Hme (HK & HCB & HRM & HAV & HD & HP & C1 & C2 & C3 & C4 & HF).
  assert (Erm : rm r' = rm r) by (apply functional_extensionality; intros x; symmetry; apply (proj2 (proj2 Hag))).
  split; [apply (kq_stable segsA K HL A rp rp tp tr md md'); [split; [intros v0 _; reflexivity | split; [intros l0; reflexivity | intros x; reflexivity]] | exact Hme | exact HK]|].
  split; [exact HCB|]. split; [exact HRM|].
  split; [split; [intros v0 Hv; rewrite (proj1 HAV v0 Hv); exact (proj1 Hag v0 Hv) | intros l0; rewrite (proj2 HAV l0); exact (proj1 (proj2 Hag) l0)]|].
  rewrite Erm. repeat (split; [assumption|]). exact (FRM_stable A0 rho0 r r' Hag HF).
Qed.
Lemma JPU_okf : ltac2:(tb__ "0|0|
Sc5OF_;S8S42S1bS4cS8bS52R5VK;R1A1A3FA';S8bS52R5S9bR4R3R2A3A3F_;Frp;Flst;Fl;Fok;").
Proof. intros ok l lst rp HOK r tp tr ms md msv' (HK & _). exact (HOK A rp tp tr ms md msv' HK). Qed.

Definition NUMS (lst : sec_chunk) : Prop := ltac2:(tb__ "0|6|
S43VA;A1S4fS3cS14S42S44VA;A1A2A1S0S4S38Z1000M0S49R2A1M1A2S4S38S39G1G0A2S4bR2A1M2A2S4S38Sb1S46R2A1M3A2S4S38S39G3Sb5A2G2A2S4S38Z1R1A2S4S38S40Z8R1A2Sb5A2S4S3aS3cVi;A1R1A2S4S38Sb1S47Vlst;A1M4A2S4S38S39G4S50Vlst;A1M5A2G2A2S38Z12000G5A2A2A2A2A2A2A2A2A2A2Tn;TG;").
Lemma nums_of_K : ltac2:(tb__ "0|1|
S1bSbS57Q40A1A1SbSc4A1Sc3S42VK;VA;R5R4R3R2A5S3S10S42A1S8fS42S44VA;A1M0Sa5S14S42G0A2U1A2A3S11S42R2A2A3Sa0R3A1F_;F_;Flst;Fmd;Ftr;Ftp;Fr;").
Proof.
  intros r tp tr md lst HK Hl. unfold NUMS. cbv zeta.
  destruct (kq_facts segsA K HL A r tp _ _ HK) as [HG _ _ _ _ _ _ _ _ _ _ _ _].
  pose proof (geom_old _ HG) as GO. destruct GO as (_ & _ & _ & _ & T0 & T1 & _).
  destruct (tbl_facts K HL HKS A r tp tr md HK) as (P1 & P2 & _).
  pose proof (ks_repr segsA K HKS A r tp tr md HK) as (_ & _ & _ & _ & DY & _). destruct DY as (_ & _ & _ & DY3 & _).
  pose proof (proj1 (nth_error_Some (aa_sec A) i) ltac:(rewrite HI; discriminate)) as LTi.
  destruct (chk_facts K HKS A r tp tr md _ lst HK Hl) as (L1 & L2 & L3 & L4 & L5 & _). cbv zeta in L1, L2, L3, L4, L5. unfold PG in L2.
  repeat split; try assumption; lia.
Qed.

Lemma DUo_secn : ltac2:(tb__ "0|1|
S8S3S10S1aA1S8fS1aS7eR1A1U0A3S11S1aS27S1dZ0A1S1dZeaad0A1M0S1dZeaad8A1SaS20S24G0Z8SbdS66S1dN1A1A2A3SeS20A1A3S26A5A2A3Fl;").
Proof. intros [|]; vmr. Qed.
Lemma DUo_secm : ltac2:(tb__ "0|2|
S8S3S10S1aA1S8fS1aS7eR1A1U2A3S11S1aS27S1dZ0A1M0S1dZead00A1M1S1dZead04A1SaS20S24G1Z1G0A3SaS20S24S1dZead01A1Z3G0A3SeS20A1A3A3S26A5A2A3Fl;").
Proof. intros [|]; vmr. Qed.
Lemma DUo_clast_t : ltac2:(tb__ "0|0|
S3S10S1aA1S8fS1aS7eSfA1U8A3S11S1aS27SbdS1eSa9S66S1dZ3A1A3S67A2S1dN8A1S1dZ0A1SaS20S24S1dZfffffffffffffff8A1Z8S5bA3SeS20A1A3S26A5A2A3").
Proof. vmr. Qed.
Lemma DUo_cidx : ltac2:(tb__ "0|2|
S3S10S1aA1S8fS1aS7eS13A1U8A3S11S1aS27SbdS67S1eSa9S6bS1dZ3A1A3A2S1dZ0A1M0S1dZ8M1A1SaS20S24G0G1S65A3SeS20A1A3S26A5A2A3").
Proof. vmr. Qed.
Lemma DUo_clast_f : ltac2:(tb__ "0|1|
S3S10S1aA1S8fS1aS7eS13A1U9A3S11S1aS27SbdS1eSa9S66S1dZ3A1A3S67A2S1dN8A1M0S1dZ0A1SaS20S24G0Z8S65A3SeS20A1A3S26A5A2A3").
Proof. vmr. Qed.
Lemma DUo_lidx : ltac2:(tb__ "0|1|
S3S10S1aA1S8fS1aS7eS13A1UaA3S11S1aS27S65S1dZ18A1M0S1dZ20A1SaS20S24G0Z8S6bA3SeS20A1A3S26A5A2A3").
Proof. vmr. Qed.
Lemma DUo_wr : ltac2:(tb__ "0|0|
S8S3S8S91S1aS1aS31S2bR1A1A1Lo;S7eR1A1A3SfA3Fl;"). Proof. intros [|]; vmr. Qed.
Lemma forallb2_In_l : forall {X0 Y0 : Type} (g : X0 -> Y0 -> bool) l1 l2 x, forallb2 g l1 l2 = true -> In x l1 -> exists y, In y l2 /\ g x y = true.
Proof.
  intros X0 Y0 g l1. induction l1 as [|x1 r1 IH]; intros l2 x HB Hin; [destruct Hin|]. destruct l2 as [|y2 r2]; cbn [forallb2] in HB; [discriminate|].
  apply andb_prop in HB as [H1 H2]. destruct Hin as [<-|Hin]; [exists y2; split; [left; reflexivity | exact H1]|].
  destruct (IH r2 x H2 Hin) as (y & Hy & E). exists y. split; [right; exact Hy | exact E].
Qed.

Definition CLZ (z : Z) : Prop := ltac2:(tb__ "0|3|
S4S38S39S46S43VA;A1A1M0S40Z8M1S3eS3cS14S42S44VA;A1A2A1M2Z1A2A2A2Vz;A2S3aVz;S39G0S40G1G2A2A2A2A2").

Lemma DUp_ranges : ltac2:(tb__ "0|3|
S8S42S1bS1aS9aSa0R4A1S3S10S42A1S8fS42S44VA;A1M0Sa5S14S42G0A2U1A2A3S11S42R5A2A3S3S57Q40M1A1S1fR5P97A2S58G1S49S43VA;A1A1A2A3S9fR6A1SdaVA;Vi;Vch;R9R8R7S5bA7S90S1aR7S82RaA1A3S0S4S38S15S0S0S2cRaR9A2M2A3R1A2S3aR1S16S0S0G2A3A2A2S5S9eR2A1S4S3S8RdS13A3Sa1R2A1A2A2F_;Fz;F_;F_;F_;F_;F_;F_;F_;Fp;Fr;Flst;Fl;").
Proof.
  intros l lst r p (C1 & C2 & C3 & C4 & C5 & C6) NM Hl E151 (E165 & E200 & E201 & _) (EH & E203 & XT & XF) Hin z Hz.
  unfold NUMS in NM. cbv zeta in NM. destruct NM as (T0 & T1 & P0 & P1 & N1 & N8 & LTi & L0 & L1 & L2).
  pose proof (topG_range (aa_geom A)) as TG. unfold IMG_HI, kPtrArrayReserve, PG in *. fold h msz in EH, E203.
  set (T := ag_thread (aa_geom A)) in *. set (PAB := ag_pab (aa_geom A)) in *. set (n := Z.of_nat (length (aa_sec A))) in *.
  assert (EvT : bv_unsigned (eval r vT) = T) by (unfold vT; cbn [eval]; rewrite E151, u64_lit by lia; reflexivity).
  assert (EvIT : bv_unsigned (eval r vIT) = fst it - 16) by (unfold vIT; cbn [eval]; rewrite E165, u64_lit by lia; reflexivity).
  assert (EvH : bv_unsigned (eval r vH) = h) by (rewrite EH, u64_lit by lia; reflexivity).
  assert (EPb : eval r vPAB = Z_to_bv 64 PAB) by (unfold vPAB; cbn [eval]; exact E200).
  assert (ENc : eval r vNCH = Z_to_bv 64 n) by (unfold vNCH; cbn [eval]; exact E201).
  assert (EvCL : bv_unsigned (eval r (add (SAlu ALU_SLL vNCH (SLit 3)) vPAB)) = 8 * n + PAB).
  { rewrite (eval_add_z r _ vPAB (8 * n) PAB (eval_sll3 r vNCH n ENc ltac:(lia)) EPb) by lia. rewrite u64_lit by lia. reflexivity. }
  unfold DUZ, CLZ, chunk_zone, sec_junk_zone, sec_tbl_zone, qstat_zone, SEC_INST. fold h msz T PAB n.
  destruct l; cbn [DUp app In] in Hin.
  - pose proof (XT eq_refl) as EI.
    repeat (destruct Hin as [<-|Hin]); [| | | | | | | | | destruct Hin];
      unfold O_secn, O_secs, O_secm, O_secg, O_stS, O_ihdr, O_hh, O_hidx, O_clast, carved, SEC_INST in Hz; rewrite obj_range_mk in Hz by lia; rewrite ?EvT, ?EvIT, ?EvH, ?EvCL in Hz; cbn [fst snd eval] in Hz; rewrite ?u64_lit in Hz by lia; unfold SEC_INST in Hz.
    + left. right. right. left. left. lia.
    + left. right. left. left. lia.
    + left. right. right. left. right. left. lia.
    + left. right. left. right. lia.
    + left. right. right. right. lia.
    + left. left. lia.
    + left. left. lia.
    + left. left. lia.
    + left. right. right. left. right. right. left. lia.
  - destruct (XF eq_refl) as (XLT & E204 & E205 & _).
    assert (EvCI : bv_unsigned (eval r (add vPAB (SAlu ALU_SLL vIDX (SLit 3)))) = PAB + 8 * Z.of_nat i).
    { rewrite (eval_add_z r vPAB _ PAB (8 * Z.of_nat i) EPb (eval_sll3 r vIDX (Z.of_nat i) ltac:(unfold vIDX; cbn [eval]; exact E204) ltac:(lia))) by lia. rewrite u64_lit by lia. reflexivity. }
    assert (EvL : bv_unsigned (eval r vLAST) = sc_map_beg lst) by (unfold vLAST; cbn [eval]; rewrite E205, u64_lit by lia; reflexivity).
    repeat (destruct Hin as [<-|Hin]); [| | | | | | | | | | | destruct Hin];
      unfold O_secn, O_secs, O_secm, O_secg, O_stS, O_ihdr, O_hh, O_hidx, O_cidx, O_clast, O_lidx, carved, SEC_INST in Hz; rewrite obj_range_mk in Hz by lia; rewrite ?EvT, ?EvIT, ?EvH, ?EvCL, ?EvCI, ?EvL in Hz; cbn [fst snd eval] in Hz; rewrite ?u64_lit in Hz by lia; unfold SEC_INST in Hz.
    + left. right. right. left. left. lia.
    + left. right. left. left. lia.
    + left. right. right. left. right. left. lia.
    + left. right. left. right. lia.
    + left. right. right. right. lia.
    + left. left. lia.
    + left. left. lia.
    + left. left. lia.
    + left. right. right. left. right. right. left. lia.
    + right. split; [reflexivity | lia].
    + left. right. right. left. right. right. right. exists lst. split; [exact Hl | lia].
Qed.

Lemma du_dissolve : ltac2:(tb__ "0|2|
S9S8S42S1bSbS57Q40A1M0A1Sc5S99R5R4R3A3S3S10S42A1S8fS42S44VA;A1M1Sa5S14S42G1A2U1A2A3S11S42R5A2A3S8aS52VJ;S61R8R7A2R5R4R3A6S7S1bS1bS4S8aS52S9bR9R8R7A3S5dRaR9A2R1R6R5A6S4S1S3G0S1fR2R1A2S1fR8R1A2A3Fv;S4S1S3SbS57Q8A1A1S23R2R1A2S23R8R1A2A3Fll;Sc6R1Va;Vnd;Vit;A4A2A2A2Lr2;A2F_;F_;F_;Fw;Ftp;Frp;Flst;Fl;Ff;").
Proof.
  intros f l lst rp tp [tr [ms md]] (HVp & HTp & HFp & XVp & _) Hl H.
  destruct (proj2 H) as (HK & HCB & HRM & HFRM). cbn [w_tr w_cfg cfg_model fst snd] in HK, HCB, HRM, HFRM.
  pose proof (chf_of_K rp tp tr md HK) as CH. pose proof (nums_of_K rp tp tr md lst HK Hl) as NM.
  destruct (kq_facts segsA K HL A rp tp _ _ HK) as [_ HRIG _ _ _ _ _ _ _ _ _ _ _]. destruct HRIG as (E151 & _).
  pose proof (proj1 (proj1 H)) as Hsm. unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model] in Hsm.
  set (R := DUo l). set (r2 := rho_absorb rp R (vms md tp ms)). set (v := view segsA (rm rp)). set (v2 := view segsA (rm r2)).
  assert (IRZ : forall x, in_ranges rp R x -> DUZ (bv_unsigned x) \/ (l = false /\ CLZ (bv_unsigned x))).
  { intros x (o & Ho & Hz). destruct (forallb2_In_l same_rng _ _ o (DUo_rng l) Ho) as (p & Hp & E). rewrite (same_rng_range rp o p E) in Hz.
    exact (DUp_ranges l lst rp p CH NM Hl E151 HVp XVp Hp _ Hz). }
  assert (PRS : forall z, v z <> None -> v2 z <> None).
  { intros z Hd. destruct (IRdec rp R z) as [[Hz Hin]|NI]; [|unfold v2, r2; rewrite (proj2 (absorb_io rp R (vms md tp ms)) z NI); exact Hd].
    destruct Hin as (o & Ho & Hr). rewrite u64_lit in Hr by lia.
    destruct (SpineMallocS9.absorb_obj rp _ tr (vms md tp ms) (vmd md) (ss_objs (ax_S (EUd f l))) R o Hsm (EUx_objs f l) Ho) as (_ & _ & X3 & _). cbn zeta in X3.
    assert (Do : ob_dflt o = DUnknown).
    { pose proof (proj1 (forallb_forall _ _) (DUo_unk l) o Ho) as Y. cbv beta in Y. destruct (ob_dflt o); first [reflexivity | discriminate Y]. }
    unfold obj_range in Hr. cbn [fst snd] in Hr.
    destruct (X3 (or_introl Do) (z - bv_unsigned (eval rp (ob_base o))) ltac:(lia)) as [x Hx].
    unfold v2, r2. rewrite view_in by lia.
    replace (Z_to_bv 64 z) with (Z_to_bv 64 (bv_unsigned (eval rp (ob_base o)) + (z - bv_unsigned (eval rp (ob_base o))))) by (f_equal; lia).
    rewrite Hx. discriminate. }
  assert (CELL : forall o c bz off k val, In o R -> In c (ob_cells o) -> bv_unsigned (eval rp (ob_base o)) = bz -> soff rp (c_off c) = off ->
            c_width c = Z.of_nat k -> eval rp (SymState.c_val c) = Z_to_bv 64 val -> 0 <= bz + off -> bz + off + Z.of_nat k <= 2 ^ 64 -> cell_ok v2 (mkACell (bz + off) k val)).
  { intros o c bz off k val Ho Hc Eb Eo W Ev B1 B2 j Hj. cbn [c_addr c_w RtCells.c_val] in *.
    destruct (SpineMallocS9.absorb_obj rp _ tr (vms md tp ms) (vmd md) (ss_objs (ax_S (EUd f l))) R o Hsm (EUx_objs f l) Ho) as (_ & X2 & _). cbn zeta in X2.
    destruct (X2 c Hc) as (_ & _ & Xc). specialize (Xc j ltac:(rewrite W, Nat2Z.id; exact Hj)). rewrite Eb, Eo, W, Nat2Z.id, Ev in Xc.
    unfold v2, r2. rewrite view_in by lia. exact Xc. }
  pose proof CH as (C1 & C2 & C3 & C4 & C5 & C6). unfold NUMS in NM. cbv zeta in NM. destruct NM as (T0 & T1 & P0 & P1 & N1 & N8 & LTi & L0 & L1 & L2).
  pose proof (topG_range (aa_geom A)) as TG. unfold IMG_HI, kPtrArrayReserve in *.
  destruct HVp as (E165 & E200 & E201 & _). pose proof XVp as (EH & E203 & XT & XF).
  assert (EPb : eval rp vPAB = Z_to_bv 64 (ag_pab (aa_geom A))) by (unfold vPAB; cbn [eval]; exact E200).
  assert (ENc : eval rp vNCH = Z_to_bv 64 (Z.of_nat (length (aa_sec A)))) by (unfold vNCH; cbn [eval]; exact E201).
  assert (EvCL : bv_unsigned (eval rp (add (SAlu ALU_SLL vNCH (SLit 3)) vPAB)) = 8 * Z.of_nat (length (aa_sec A)) + ag_pab (aa_geom A)).
  { rewrite (eval_add_z rp _ vPAB _ _ (eval_sll3 rp vNCH _ ENc ltac:(lia)) EPb) by lia. rewrite u64_lit by lia. reflexivity. }

  assert (CN : cell_ok v2 (mkACell (SEC_INST + 56) 8 (Z.of_nat (length (aa_sec A)) - 1))).
  { apply (CELL _ (mkCell (SLit 961232) 8 (add vNCH (SLit (-1)))) 0 961232 8%nat _ (nth_error_In _ _ (DUo_secn l))); [left; reflexivity | reflexivity | apply soff_lit_small; lia | reflexivity | | lia | lia].
    cbn [SymState.c_val]. replace (Z.of_nat (length (aa_sec A)) - 1) with (Z.of_nat (length (aa_sec A)) + -1) by lia. apply ev_add_lit; [exact ENc | lia | lia | lia]. }
  assert (CM : cell_ok v2 (mkACell 0xead00 4 0)).
  { pose proof (CELL _ (mkCell (SLit 961792) 1 (SLit 0)) 0 961792 1%nat 0 (nth_error_In _ _ (DUo_secm l)) ltac:(left; reflexivity) eq_refl ltac:(apply soff_lit_small; lia) eq_refl eq_refl ltac:(lia) ltac:(lia)) as M0.
    pose proof (CELL _ (mkCell (SLit 961793) 3 (SLit 0)) 0 961793 3%nat 0 (nth_error_In _ _ (DUo_secm l)) ltac:(right; left; reflexivity) eq_refl ltac:(apply soff_lit_small; lia) eq_refl eq_refl ltac:(lia) ltac:(lia)) as M1.
    unfold cell_ok in M0, M1. cbn [c_addr c_w RtCells.c_val] in M0, M1.
    intros k Hk. cbn [c_addr c_w RtCells.c_val] in *. destruct k as [|[|[|[|k]]]]; [| | | | lia].
    - replace (961792 + Z.of_nat 0) with (0 + 961792 + Z.of_nat 0) by lia. rewrite (M0 0%nat ltac:(lia)). reflexivity.
    - replace (961792 + Z.of_nat 1) with (0 + 961793 + Z.of_nat 0) by lia. rewrite (M1 0%nat ltac:(lia)). reflexivity.
    - replace (961792 + Z.of_nat 2) with (0 + 961793 + Z.of_nat 1) by lia. rewrite (M1 1%nat ltac:(lia)). reflexivity.
    - replace (961792 + Z.of_nat 3) with (0 + 961793 + Z.of_nat 2) by lia. rewrite (M1 2%nat ltac:(lia)). reflexivity. }
  pose proof (ks_repr segsA K HKS A rp tp tr md HK) as (SC1 & _).
  assert (CF : l = false -> cell_ok v2 (mkACell (ag_pab (aa_geom A) + 8 * Z.of_nat i) 8 (sc_map_beg lst)) /\ cell_ok v2 (mkACell (sc_map_beg lst + 24) 8 (Z.of_nat i))
                            /\ (forall z, CLZ z -> v2 z = v z)).
  { intros ->. destruct (XF eq_refl) as (XLT & E204 & E205 & _).
    assert (EvCI : bv_unsigned (eval rp (add vPAB (SAlu ALU_SLL vIDX (SLit 3)))) = ag_pab (aa_geom A) + 8 * Z.of_nat i).
    { rewrite (eval_add_z rp vPAB _ _ (8 * Z.of_nat i) EPb (eval_sll3 rp vIDX (Z.of_nat i) ltac:(unfold vIDX; cbn [eval]; exact E204) ltac:(lia))) by lia. rewrite u64_lit by lia. reflexivity. }
    assert (EvL : bv_unsigned (eval rp vLAST) = sc_map_beg lst) by (unfold vLAST; cbn [eval]; rewrite E205, u64_lit by lia; reflexivity).
    split; [|split].
    - replace (ag_pab (aa_geom A) + 8 * Z.of_nat i) with (ag_pab (aa_geom A) + 8 * Z.of_nat i + 0) by lia.
      apply (CELL _ (mkCell (SLit 0) 8 vLAST) _ 0 8%nat _ (nth_error_In _ _ DUo_cidx)); [left; reflexivity | exact EvCI | apply soff_lit_small; lia | reflexivity | unfold vLAST; cbn [SymState.c_val eval]; exact E205 | lia | lia].
    - apply (CELL _ (mkCell (SLit 24) 8 vIDX) _ 24 8%nat _ (nth_error_In _ _ DUo_lidx)); [left; reflexivity | exact EvL | apply soff_lit_small; lia | reflexivity | unfold vIDX; cbn [SymState.c_val eval]; exact E204 | lia | lia].
    - pose proof (CELL _ (mkCell (SLit (-8)) 8 vLAST) _ (-8) 8%nat _ (nth_error_In _ _ DUo_clast_f) ltac:(left; reflexivity) EvCL ltac:(apply soff_lit_small; lia) eq_refl ltac:(unfold vLAST; cbn [SymState.c_val eval]; exact E205) ltac:(lia) ltac:(lia)) as CL2.
      destruct (SC1 _ lst Hl) as (_ & _ & _ & _ & CLv & _). fold v in CLv.
      intros z Hz. unfold CLZ in Hz. apply (cell_ok_same v v2 _ CLv); [|cbn [c_addr c_w]; rewrite Nat2Z.inj_sub by lia; cbn [Z.of_nat]; lia].
      replace (ag_pab (aa_geom A) + 8 * Z.of_nat (length (aa_sec A) - 1)) with (8 * Z.of_nat (length (aa_sec A)) + ag_pab (aa_geom A) + -8) by (rewrite Nat2Z.inj_sub by lia; cbn [Z.of_nat]; lia). exact CL2. }
  assert (CT : l = true -> forall z, ag_pab (aa_geom A) + 8 * Z.of_nat i <= z < ag_pab (aa_geom A) + 8 * Z.of_nat i + 8 -> v2 z = v z).
  { intros ->. pose proof (XT eq_refl) as EI.
    pose proof (CELL _ (mkCell (SLit 18446744073709551608) 8 vH) _ (-8) 8%nat h (nth_error_In _ _ DUo_clast_t) ltac:(left; reflexivity) EvCL ltac:(reflexivity) eq_refl ltac:(cbn [SymState.c_val]; exact EH) ltac:(lia) ltac:(lia)) as CL2.
    destruct (SC1 i ch HI) as (_ & _ & _ & _ & CPv & _). fold v h in CPv.
    intros z Hz. apply (cell_ok_same v v2 _ CPv); [|cbn [c_addr c_w]; lia].
    replace (ag_pab (aa_geom A) + 8 * Z.of_nat i) with (8 * Z.of_nat (length (aa_sec A)) + ag_pab (aa_geom A) + -8) by lia. exact CL2. }
  assert (EQF : forall z, ~ DUZ z -> v2 z = v z).
  { intros z ND. destruct (IRdec rp R z) as [[Hz Hin]|NI]; [|exact (proj2 (absorb_io rp R (vms md tp ms)) z NI)].
    pose proof (IRZ _ Hin) as X0. rewrite u64_lit in X0 by lia. destruct X0 as [X0|[El X0]]; [exfalso; exact (ND X0)|]. exact (proj2 (proj2 (CF El)) z X0). }
  assert (HF2 : FRM A0 rho0 r2).
  { apply (FRM_absorb_gen A0 rho0 rp r2 (fun z => 0 <= z < 2 ^ 64 /\ in_ranges rp R (Z_to_bv 64 z)) (IRdec rp R) ltac:(intros i0; reflexivity) ltac:(intros l0; reflexivity));
      [| | exact (proj2 (absorb_io rp R (vms md tp ms))) | | exact HFRM].
    - intros z [Hz Hin]. pose proof (IRZ _ Hin) as X0. rewrite u64_lit in X0 by lia. left.
      destruct X0 as [[X0|[X0|[X0|X0]]]|[El X0]].
      + apply ch_foot. right. exact X0.
      + right. right. right. left. unfold sec_junk_zone, SEC_INST in *. lia.
      + unfold sec_tbl_zone in X0. destruct X0 as [X0|[X0|[X0|(lst' & Hl' & X0)]]].
        * right. right. right. left. unfold SEC_INST in *. lia.
        * right. right. right. left. unfold SEC_INST in *. lia.
        * right. right. right. apply HSF. right. left. unfold kPtrArrayReserve. lia.
        * right. right. right. apply HSF. right. right. left. apply Exists_exists. exists lst'. split; [exact (nth_error_In _ _ Hl') | lia].
      + left. apply HQW. right. right. exact X0.
      + right. right. right. apply HSF. right. left. unfold CLZ in X0. unfold kPtrArrayReserve. lia.
    - intros x [_ Hin] HBx. rewrite Z_to_bv_bv_unsigned in Hin.
      apply (SpineMallocS9.absorb_defined rp _ tr (vms md tp ms) (vmd md) (ss_objs (ax_S (EUd f l))) R x Hsm (EUx_objs f l)); [| exact Hin | unfold SHADOW_BAND_LO, LOW_SHADOW_BEG in HBx; unfold IMG_HI; lia].
      apply Forall_forall. intros o Ho. exact (proj1 (forallb_forall _ _) (DUo_wr l) o Ho).
    - intros x NP. apply (proj1 (absorb_io rp R (vms md tp ms))). intros Hin. apply NP. split; [apply urange|]. rewrite Z_to_bv_bv_unsigned. exact Hin. }
  set (TJ := (fun (_ : valuation) (_ : list word) (_ : list event) (_ : Model) => True) : jpredA).
  assert (HT : SPA segsA TJ (EUx f l) rp tp (tr, mkCfg ms md)) by (split; [exact (proj1 H) | exact I]).
  pose proof (SPA_unobj segsA TJ rp (EUx f l) (ss_objs (ax_S (EUd f l))) R tp tr ms md (EUx_objs f l) HT (fun x => x)) as HU2. cbn zeta in HU2. fold r2 in HU2. rewrite EUd_set in HU2.
  assert (HVS2 : HVS r2 a nd it).
  { unfold HVS. fold v2. pose proof HCB as (_ & HN0 & HN1 & _ & Q5). destruct (Q5 0%nat it eq_refl) as [Cs _]. unfold kQuarantineBatchCount in HN1. cbn [length] in HN0.
    replace (a + 24 + 8 * (Z.of_nat nd + Z.of_nat 0)) with (a + 24 + 8 * Z.of_nat nd) in Cs by lia.
    apply (cell_ok_frame1 v v2 _ _ _); [|exact Cs]. intros z Hz. cbn [Z.of_nat] in Hz. apply EQF. intros HD.
    apply (proj2 (batch_where K HL HKS A i ch HTH HCI HI rp tp tr md (mkQB a (it :: its) s) HK ltac:(rewrite HGL; left; reflexivity)) z); [cbn [qb_addr]; lia|].
    unfold ZQ, DUZ in *. tauto. }
  exists r2. split; [|split; [intros v0; reflexivity | split; [intros ll; reflexivity | exact HVS2]]].
  split; [exact (proj1 HU2)|]. cbn [w_tr w_cfg cfg_model fst snd]. unfold JPU.
  split; [exact HK|]. split; [exact HCB|]. split; [exact HRM|]. split; [split; [intros v0 _; reflexivity | intros l0; reflexivity]|].
  split; [exact EQF|]. split; [exact PRS|]. split; [exact CN|]. split; [exact CM|].
  split; [intros El; destruct (CF El) as (X1 & X2 & _); split; [exact X1 | exact X2]|]. split; [exact CT | exact HF2].
Qed.

Lemma EUd_vars : ltac2:(tb__ "0|0|
S9S8S3S8S91S1aSfaS1SfL_;A1S21S53S5dR2R1A2A1A1A3SfA3Fl;Ff;"). Proof. fam6; vmr. Qed.

Let A' : AA := ltac2:(tb__ "0|0|
Sf7Sd0VA;SeS45A1SaS45S4aVa;Vits;Vs;A3S12S45Vtmp';Vrest;A3A3A3Vi;A2").
Let J' : jpredA := ltac2:(tb__ "0|0|
Sd2VK;VA0;Vrho0;VA';Va;Vn0;S18Vnd;A1Vits;Vtmp';Vrest;Aa").
Hypothesis HJX' : JOK X J'.
Hypothesis HJP : ltac2:(tb__ "0|0|
S8S42S1bS98VQ;VX;S9bR3R2R1A3A3Frp;Flst;Fl;").

Lemma tail_U : ltac2:(tb__ "0|2|
S9S8S42S1bSbS57Q40A1A1M0S99R4R3R2A3S3S10S42A1S8fS42S44VA;A1M1Sa5S14S42G1A2U1A2A3S11S42R4A2A3S1bG0S7dR8R6R2A3Sc6R3Va;Vnd;Vit;A4S97VQ;VX;S8aS52VJ';S64RbRaA2R4R3A5A3F_;F_;Ftp';Fr;S1bS7dR8R6R1A3S97VQ;VX;S8aS52VJ;S69RaR9A2R2R6A5A3F_;Fr;F_;F_;F_;Ftp;FrS;Flst;Fl;Ff;").
Proof.
  intros f l lst rS tp TE Hl HC r KV.
  pose proof (TENV_keep l lst rS r TE KV) as TEr.
  apply (tr_conseq X _ (SPA segsA J (EUx f l) r tp)); [intros w Hw; exact (SPA_axforms segsA J _ r _ _ tp w (EUx_eq f l) Hw)|].
  apply (tr_glue X _ (JPU l lst r) (EUd f l) tp (fun r2 => KEEPX l rS r2 /\ (forall v, rw r2 v = rw r v) /\ (forall ll, rl r2 ll = rl r ll) /\ HVS r2 a nd it)).
  { intros w Hw. destruct (du_dissolve f l lst r tp w TEr Hl Hw) as (r2 & H2 & RW & RL & HS2). exists r2. split; [exact H2|].
    split; [exact (KEEPX_trans l _ _ _ KV (KEEPX_same l r r2 RW RL)) | split; [exact RW | split; [exact RL | exact HS2]]]. }
  intros r2 (KV2 & RW2 & RL2 & HS2). destruct TEr as (HVr & HTr & HFr & XVr & _). pose proof XVr as (EH & EMs & XT & XF). fold h msz in EH, EMs.
  apply (tr_pure X _ (CHF /\ NUMS lst /\ Z.of_nat nd <= 1020 /\ (forall z, a <= z < a + 8192 -> ~ chunk_zone ch z))).
  { intros [tr [ms md]] Hw. destruct (proj2 Hw) as (HK & HCB & _). cbn [w_tr w_cfg cfg_model fst snd] in HK, HCB. split; [exact (chf_of_K r tp tr md HK) | split; [exact (nums_of_K r tp tr md lst HK Hl)|]].
    split; [destruct HCB as (_ & HN0 & HN1 & _); unfold kQuarantineBatchCount in HN1; cbn [length] in HN0; lia|].
    intros z Hz HZ. apply (proj2 (batch_where K HL HKS A i ch HTH HCI HI r tp tr md (mkQB a (it :: its) s) HK ltac:(rewrite HGL; left; reflexivity)) z); [cbn [qb_addr]; exact Hz | right; left; exact HZ]. }
  intros (CH & NM & NDB & BOFF). pose proof CH as (CH1 & CH2 & CH3 & CH4 & CH5 & CH6). unfold IMG_HI in CH4.
  assert (EH2 : eval r2 vH = Z_to_bv 64 h) by (unfold vH in *; cbn [eval] in *; rewrite RW2; exact EH).
  assert (EM2 : eval r2 vMS = Z_to_bv 64 msz) by (unfold vMS; cbn [eval]; rewrite RW2; exact EMs).
  pose proof (EUd_node f l) as (N1 & N2 & N3 & N4 & N6 & N7). apply Pos.leb_le in N7.
  apply (tr_munmap X (JPU l lst r) J' (EUd f l) r2 tp vH vMS msz (HJP l lst r) N7 N1 N2 N3 N4 EM2 CH2 ltac:(lia)).
  -
    intros tr ms md Hsp HJ. cbv zeta.
    destruct (pending_argsA segsA r2 tp (EUd f l) tr ms md Hsp) as (G0 & _). rewrite N3, EH2 in G0. rewrite G0. rewrite (u64_lit h) by lia.
    destruct HJ as (HK & HCB & HRM & HAV & HD & HP & C1 & C2 & C3 & C4 & HF).
    pose proof (qsenv_intro K HL HKS A it i ch a s its tmp' rest HTH HCI HGL HI HU HSZ r tp tr md n0 nd HK HCB HVr) as QS.
    destruct (exit_carve K A it i ch HKS r tp tr md l lst vH REF1 HK QS HTr HFr Hl XVr REF1_refl) as (_ & _ & Z1 & Z2 & Z3).
    assert (ZALL : Forall2 (in_zone r (zbE A i ch lst) zloS (zhiX (sc_map_size ch)) (ZUXl l)) (REFX l) (ZDX l)).
    { unfold REFX, ZDX. apply Forall2_app; [exact Z3|]. cbn [app]. constructor; [exact Z1 | exact Z2]. }
    assert (HLF : l = false -> (i < length (aa_sec A) - 1)%nat) by (intros E; exact (proj1 (XF E))).
    pose proof (zsepE K A it i ch HKS r tp tr md l lst HK QS Hl HLF) as HSEPZ.
    destruct (ks_munmap_ok segsA K HKS A r tp tr md HK ch (nth_error_In _ _ HI)) as (MU1 & MU2 & MU3). fold h msz in MU1, MU2, MU3.
    assert (DISJ : forall o, In o (ss_objs (ax_S (EUd f l))) -> SymState.ranges_disjoint (obj_range r2 o) (h, h + msz)).
    { intros o Ho. rewrite (obj_range_agree_vars (fun _ => true) r r2 o ltac:(intros v0 _; symmetry; apply RW2) ltac:(intros l0; symmetry; apply RL2) (proj1 (forallb_forall _ _) (EUd_vars f l) o Ho)).
      apply (offzone_sound r (zbE A i ch lst) zloS (zhiX (sc_map_size ch)) (ZUXl l) (REFX l) (ZDX l) 5%nat _ h (h + msz) HSEPZ ZALL (EUd_off5 f l)); [destruct l; cbn; tauto | | | exact Ho]; unfold zbE, zbX, zloS, zhiX; fold h msz; lia. }
    split; [unfold page_size; exact CH1|]. split; [unfold TASK_SIZE; lia|]. split; [exact MU1|]. split; [exact MU2|]. split; [exact MU3|]. split; [exact DISJ|].
    split; [intros rr y Hin; rewrite N6 in Hin; destruct Hin|].

    set (aw := Z_to_bv 64 h). set (nw := Z_to_bv 64 msz).
    set (r4 := set_rm r2 (unmap_range (rm r2) aw nw)). set (v := view segsA (rm r)). set (v2 := view segsA (rm r2)). set (v4 := view segsA (rm r4)). fold v in HCB, HRM. fold v v2 in HD, HP, C4. fold v2 in C1, C2, C3.
    assert (INR : forall x : word, SysStep.in_range aw nw x = true <-> chunk_zone ch (bv_unsigned x)).
    { intros x. rewrite SysStep.in_range_spec. unfold aw, nw, chunk_zone. fold h msz. rewrite !u64_lit by lia. tauto. }
    assert (V4OUT : forall z, ~ chunk_zone ch z -> v4 z = v2 z).
    { intros z NZ. unfold v4, v2. apply view_agree. intros Hz. unfold r4. cbn [rm set_rm]. rewrite unmap_range_at.
      destruct (SysStep.in_range aw nw (Z_to_bv 64 z)) eqn:EI; [|reflexivity]. exfalso. apply NZ. pose proof (proj1 (INR _) EI) as X0. rewrite u64_lit in X0 by lia. exact X0. }
    assert (RM4OUT : forall x : word, ~ chunk_zone ch (bv_unsigned x) -> rm r4 x = rm r2 x).
    { intros x NZ. unfold r4. cbn [rm set_rm]. rewrite unmap_range_at. destruct (SysStep.in_range aw nw x) eqn:EI; [|reflexivity]. exfalso. exact (NZ (proj1 (INR x) EI)). }
    pose proof (qw_off_chunk K HL HKS A it i ch HTH HCI HI HU r tp tr md HK) as QOC.
    assert (CELL4 : forall c, cell_ok v2 c -> (forall z, c_addr c <= z < c_addr c + Z.of_nat (c_w c) -> ~ chunk_zone ch z) -> cell_ok v4 c).
    { intros [ca cw cv] Hc Hz. apply (cell_ok_frame1 v2 v4 ca cw cv); [|exact Hc]. intros z Hzz. apply V4OUT. apply Hz. cbn [c_addr c_w]. exact Hzz. }
    unfold NUMS in NM. cbv zeta in NM. destruct NM as (T0 & T1 & P0 & P1 & NN1 & NN8 & LTi & L0 & L1 & L2). unfold IMG_HI, kPtrArrayReserve in *.
    destruct (chk_facts K HKS A r tp tr md i ch HK HI) as (_ & _ & _ & _ & _ & _ & _ & _ & K9 & K10). cbv zeta in K9, K10. fold h msz in K9, K10. unfold kPtrArrayReserve in K9.
    split; [|split; [|split]].
    +
      unfold A'. apply (kq_unmap segsA K HKS A r r4 tp tr md [] (tmp' ++ rest) a it its s s i ch HTH HGL HPR HI HU); [intros i0; exact (RW2 i0) | intros l0; exact (RL2 l0) | | | | | | exact (paid_munmap_leZ segsA md tp h msz ltac:(lia) ltac:(lia) (smatch_pendingA_MI segsA _ _ _ _ _ _ Hsp) MU3) | exact HK].
      * intros z N1' N2' N3' N4' _. fold v4 v. rewrite (V4OUT z N4'). apply HD. unfold DUZ. intros [X0|[X0|[X0|X0]]]; [exact (N4' X0) | exact (N2' X0) | exact (N3' X0) | apply N1'; right; right; exact X0].
      * intros z HZ Hd. fold v4. rewrite (V4OUT z (QOC z HZ)). exact (HP z Hd).
      * fold v4. apply (CELL4 _ C1). intros z Hz. cbn [c_addr c_w] in Hz. unfold chunk_zone, SEC_INST in *. fold h msz. lia.
      * fold v4. apply (CELL4 _ C2). intros z Hz. cbn [c_addr c_w] in Hz. unfold chunk_zone. fold h msz. lia.
      * intros lst0 Hl0. rewrite Hl in Hl0. injection Hl0 as <-. split.
        -- intros Hlt. destruct l; [pose proof (XT eq_refl) as EI; exfalso; lia|]. destruct (C3 eq_refl) as [C3a C3b]. fold v4. split.
           ++ apply (CELL4 _ C3a). intros z Hz. cbn [c_addr c_w] in Hz. unfold chunk_zone. fold h msz. lia.
           ++ apply (CELL4 _ C3b). intros z Hz. cbn [c_addr c_w] in Hz. unfold chunk_zone. fold h msz.
              pose proof (K10 _ lst Hl ltac:(pose proof (HLF eq_refl); lia)) as X0. lia.
        -- intros Heq z Hz. destruct l; [|pose proof (HLF eq_refl); exfalso; lia]. fold v4 v. rewrite V4OUT by (unfold chunk_zone; fold h msz; lia). exact (C4 eq_refl z Hz).
    + apply (CR_unmap K HL HKS A it i ch a s its tmp' rest HTH HCI HGL HPR HI HU r tp tr md v v4 n0 nd HK); [| | exact HCB | exact HRM].
      * intros z NZ. rewrite V4OUT by (intros X0; apply NZ; right; left; exact X0). apply HD. unfold DUZ, ZQ in *. tauto.
      * intros z NZ Hd. rewrite (V4OUT z NZ). exact (HP z Hd).
    + change (aa_geom A') with (aa_geom A). apply (CR_unmap K HL HKS A it i ch a s its tmp' rest HTH HCI HGL HPR HI HU r tp tr md v v4 n0 nd HK); [| | exact HCB | exact HRM].
      * intros z NZ. rewrite V4OUT by (intros X0; apply NZ; right; left; exact X0). apply HD. unfold DUZ, ZQ in *. tauto.
      * intros z NZ Hd. rewrite (V4OUT z NZ). exact (HP z Hd).
    + apply (FRM_absorb_gen A0 rho0 r2 r4 (chunk_zone ch)); [intros z; unfold chunk_zone; lia | intros i0; reflexivity | intros l0; reflexivity | | | exact V4OUT | exact RM4OUT | exact HF].
      * intros z Hz. left. apply ch_foot. right. exact Hz.
      * intros x Hx HB. exfalso. unfold chunk_zone in Hx. fold h msz in Hx. lia.
  -
    rewrite AU_eq. set (r4 := set_rm r2 _). set (tp4 := tp_forget _ _ tp).
    apply (seg_PE X f l J' r4 tp4 HJX'). intros T M r5 HIN HKp. cbn [TsPE In] in HIN. destruct HIN as [E|[]]. injection E as <- <-.
    apply HC.
    + apply (KEEPX_trans l _ r4 _); [|exact (KEEPX_keepsM l r4 r5 HKp)].
      apply (KEEPX_trans l _ r2 _ KV2). apply KEEPX_same; intros; reflexivity.
    +
      assert (ERM : rm r5 = rm r4) by (apply functional_extensionality; intros x; symmetry; apply (proj2 (proj2 (proj1 HKp)))).
      unfold HVS in *. rewrite ERM. pose proof (proj1 (proj2 NM)) as T1'. unfold NUMS in NM. cbv zeta in NM.
      apply (cell_ok_frame1 (view segsA (rm r2)) _ _ _ _); [|exact HS2]. intros z Hz. cbn [Z.of_nat] in Hz.
      apply view_agree. intros Hz64. unfold r4. cbn [rm set_rm]. rewrite unmap_range_at, EH2.
      destruct (SysStep.in_range (Z_to_bv 64 h) (Z_to_bv 64 msz) (Z_to_bv 64 z)) eqn:EI; [|reflexivity]. exfalso.
      apply SysStep.in_range_spec in EI. rewrite !u64_lit in EI by lia.
      apply (BOFF z); [lia | unfold chunk_zone; fold h msz; exact EI].
Qed.

Lemma In_list_upd : forall {T0 : Type} (l0 : list T0) k x y, In y (list_upd l0 k x) -> In y l0 \/ y = x.
Proof.
  intros T0 l0. induction l0 as [|h0 t0 IH]; intros k x y Hy; [destruct k; cbn in Hy; destruct Hy|].
  destruct k as [|k]; cbn [list_upd] in Hy; destruct Hy as [<-|Hy]; [right; reflexivity | left; right; exact Hy | left; left; reflexivity|].
  destruct (IH k x y Hy) as [X0|X0]; [left; right; exact X0 | right; exact X0].
Qed.
Lemma In_removelast : forall {T0 : Type} (l0 : list T0) y, In y (removelast l0) -> In y l0.
Proof.
  intros T0 l0. induction l0 as [|h0 t0 IH]; intros y Hy; [destruct Hy|]. cbn [removelast] in Hy. destruct t0 as [|h1 t1]; [destruct Hy|].
  destruct Hy as [<-|Hy]; [left; reflexivity | right; exact (IH y Hy)].
Qed.
Lemma swap_remove_incl : forall {T0 : Type} (l0 : list T0) k, incl (swap_remove l0 k) l0.
Proof.
  intros T0 l0 k y Hy. unfold swap_remove in Hy. destruct (nth_error l0 (length l0 - 1)) as [x|] eqn:E; [|exact Hy].
  destruct (Nat.eqb k (length l0 - 1)); [exact (In_removelast l0 y Hy)|].
  destruct (In_list_upd _ _ _ _ Hy) as [X0| ->]; [exact (In_removelast l0 y X0) | exact (nth_error_In _ _ E)].
Qed.
Lemma QW_unmap : ltac2:(tb__ "0|0|
S0ScbVA';R1A2ScbVA;R2A2F_;Fz;").
Proof.
  intros z [H|H]; [left | right; exact H].
  unfold qzone, qall in *. cbn [A' aa_q_thread aa_q_global unmap_sec set_sec set_q app] in H. rewrite HTH, HGL. cbn [app].
  apply Exists_cons in H as [H|H]; [apply Exists_cons_hd | apply Exists_cons_tl; exact H].
  cbn [qb_addr qb_items] in *. destruct H as [H|H]; [left; exact H | right]. apply Exists_cons_tl. exact H.
Qed.
Lemma SF_unmap : ltac2:(tb__ "0|0|
S0SccVA';R1A2SccVA;R2A2F_;Fz;").
Proof.
  intros z. apply sec_foot_mono; [reflexivity | unfold A'; cbn [aa_sec unmap_sec set_sec set_q]; apply swap_remove_incl |].
  unfold qall. cbn [A' aa_q_thread aa_q_global unmap_sec set_sec set_q app]. rewrite HTH, HGL. cbn [app]. unfold qitems. cbn [flat_map qb_items].
  intros y Hy. apply in_app_or in Hy as [Hy|Hy]; apply in_or_app; [left; right; exact Hy | right; exact Hy].
Qed.
Lemma QP_unmap : ltac2:(tb__ "0|0|
Sd1VA0;VA;A2Sd1VA0;VA';A2F_;").
Proof.
  intros (E & EL & EF). split; [|split; [exact EL | exact EF]]. unfold same_but_qcs in *. unfold A', unmap_sec, set_sec, set_q. rewrite E. reflexivity.
Qed.

Lemma ro_cond_intro : ltac2:(tb__ "0|a|
S1bS1cS0S0SbScScS0S9A2M0S1cA2M1A1M2S0S3S57Q40M3A1M4S22R6R5A2S58G3R1A2M5A3S4S38Z0M6R2A2S3aR2S3dZ2Z3eA2M7A2A2S38S41G7A1R6A2S38R7R6A2S38R7G7A2S38G6S39R6R9A2A2SfbRaR9R8A3S0S4S38S39R9RcA2R1A2S3aR1S39R9RbA2A2A2S4SceVA0;R2A2S6S4S38Sb4R2A2S3aR2Sb3A2A2A1A2F_;Fz;S3S8SffSdScScS1cS0A2M8S0A2M9G2SdG8S0SdS1cS0RdRcA4RbA4RaA4A1SfA3Sc0G1G1G1OLc;R1G0S1cG0OLp;R2S0S9S7S0S0S4S3G4S22R15R4A2G5A3S95S94S52S28R15A1A2S96S39R10R3A2R2R1A3A2A2Lval;A2Lk;Loff;Xcx1Le;Lp;Xcx1Lc;RbA3SecVA0;R10SdScG9G2A2S0SdG9G2SdG8S0SdS1cS0RfReA4RdA4RcA4RbA4A3F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fa0;Fcs;Fhi;Flo;Fb;Frho;").
Proof.
  intros rho b lo hi cs a0 Eb H1 H2 H3 H4 H5 CI HZ HC HF. unfold ro_cond. split; [exact Eb|]. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|]. split; [exact CI|]. split; [exact HZ|].
  intros z Hz. destruct (SMGlue.coverb_sound _ HC (z - a0) ltac:(lia)) as (o & n & e & Hin & Ho).
  pose proof (proj1 (Forall_forall _ _) HF _ Hin) as X0. cbv beta iota in X0. destruct X0 as (val & Ev & Cv).
  exists o, n, e, val. split; [exact Hin|]. split; [lia|]. split; [exact Ev | exact Cv].
Qed.

Definition NROS : list carve_spec := ltac2:(tb__ "0|4|
S12S59S102SaS59SbfS59U0Sc8SdScScS1cS0A2M0S0A2SbScScS0S9A2S1cA2M1A1SdG0S0SdS1cS0S1dZ0M2A1G2A4G2A4SeG1A1A4M3A4SaS59SbfS59U5Sc8G3A4SaS59SbfS59U6Sc8G3A4SaS59SbfS59U7Sc8G3A4SeS59A1A3A3A3A3A3").
Definition DSR (ctx : Z) : list dspec := ltac2:(tb__ "0|4|
Sc1S59ScS59S0A2S59SdS59S0R1S1cS0Lx;S15S1cS0S15ScS1cS0A2M0S0S15ScG0S0A2SbScScS0S9A2S1cA2A1R1A3A3A3S0Z0Lz;S1Vctx;Li0;SaeS1cS1cVctx;Lb;La0;M1Lop;M2G2SafG1Lop;M3G3S8S2S1cVctx;La0;Lw;Lsgn;S1S1cS0Vctx;Lk0;Li0;Ll;X1cx8A4Lk;Sa2A4").
Definition sbS : carve_spec := ltac2:(tb__ "0|4|
SdScScS1cS0A2M0S0A2SbScScS0S9A2M1S1cA2M2A1SdG0S0SdS1cS0S1dZ0A1Zeaa78M3A4Zeaa80A4SaG2SdG1S1cSdS0S9G3U8A4SbeA4SeG2A1A3A4").
Definition itS : carve_spec := ltac2:(tb__ "0|4|
SdScScS1cS0A2M0S0A2SbScScS0S9A2M1S1cA2M2A1SdG0S0SdS1cS0Se9N80M3A4N78A4SaG2SdG1S1cSdS0S9G3U8A4Se8A4SeG2A1A3A4").
Definition T_fin (f : nat) (l : bool) : strans := ltac2:(tb__ "0|2|
SedS64Vf;Vl;A2UfSaS59Sa4SaS59Sa3SeS59A1A3A3SeS1A1SeS29A1Se7S100ScaSaScScS9S0A2M0S0A2M1SdG0S0SdS9S0U0Zeaa78A4Zeaa80A4SaG1SdG0S0SdS9S0UaZ0A4Z2000A4SeG1A1A3A3A9").
Lemma T_fin_ok : ltac2:(tb__ "0|0|
S9S8S3S8Sf1S9cR2R1A2A1SfA3Fl;Ff;"). Proof. fam6; vmr. Qed.
Lemma LR_objs : ltac2:(tb__ "0|2|
S9S8S0S3SbS1aA1S21S53SeeS9cR3R2A2M0A1M1A1A1S12S1aSd8G1Sf0G0A1A2Sc1Sd6S1aSd7S9dR1A1A4A3A3Fctx;Fl;Ff;").
Proof. intros f l ctx. change (map dobj (DSR ctx)) with (map carve_obj NROS). revert f l. fam6; vmr. Qed.
Lemma LR_ref : ltac2:(tb__ "0|0|
S9S8S3S8Sd4S1aS1aSd5S21S53SefS9cR2R1A2A1A1A1S21S53S101A1A1A5SfA3Fl;Ff;"). Proof. fam6; vmr. Qed.

Ltac rtc_cell HR := first [ exact (cells_ok_nth _ _ 0%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 1%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 2%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 3%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 4%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 5%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 6%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 7%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 8%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 9%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 10%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 11%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 12%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 13%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 14%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 15%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 16%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 17%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 18%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 19%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 20%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 21%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 22%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 23%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 24%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 25%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 26%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 27%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 28%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 29%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 30%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 31%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 32%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 33%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 34%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 35%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 36%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 37%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 38%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 39%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 40%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 41%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 42%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 43%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 44%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 45%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 46%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 47%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 48%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 49%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 50%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 51%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 52%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 53%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 54%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 55%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 56%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 57%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 58%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 59%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 60%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 61%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 62%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 63%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 64%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 65%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 66%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 67%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 68%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 69%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 70%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 71%nat _ HR eq_refl) ].
Lemma ro_all : ltac2:(tb__ "0|3|
S1bSbS57Q40M0A1M1A1SbSc4A1Sc3VK;VA';R4R3R2R1A5S3G1S1fR5Pc8A2S58G0S46S43VA;A1M2A1A2A3Sd1VA0;VA;A2Sc0Sd6SecVA0;R7A2S9dS4eG2A1A1A3F_;F_;F_;Fmd;Ftr;Ftp;Fr;").
Proof.
  intros r tp tr md HK E200 (ESB & _). assert (EG : aa_geom A = aa_geom A0) by (unfold same_but_qcs in ESB; rewrite ESB; reflexivity).
  destruct (kq_facts segsA K HL A' r tp _ _ HK) as [HG HRIG HRTC _ _ _ _ _ _ _ _ _ _]. change (aa_geom A') with (aa_geom A) in HG, HRIG, HRTC.
  destruct HRIG as (E151 & E152 & E155 & E156).
  assert (HR : cells_ok (view segsA (rm r)) (rtc_cells RTC_A (aa_geom A))) by exact HRTC.
  pose proof (ks_repr segsA K HKS A' r tp tr md HK) as (_ & _ & _ & _ & _ & HS0 & HS8 & _). change (aa_geom A') with (aa_geom A) in HS8.
  pose proof (geom_old _ HG) as GO. destruct GO as (_ & _ & _ & _ & _ & _ & _ & C0 & C1 & _).
  pose proof (geom_bands _ HG) as (_ & _ & _ & _ & _ & CI & _). pose proof (topG_range (aa_geom A)) as TG. unfold IMG_LO, IMG_HI in CI.
  assert (CB : ag_ctx (aa_geom A) + 0x1000 <= SHADOW_BAND_LO \/ SHADOW_BAND_HI <= ag_ctx (aa_geom A)) by (destruct HG as (_ & _ & _ & (_ & _ & _ & _ & X0) & _); exact X0).
  unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in CB.
  unfold DSR, NROS, N_rti, N_sec1, vCTX. cbn [map app nth fst].
  repeat apply Forall_cons; try apply Forall_nil; apply ro_cond_intro;
    try (unfold SEC_INST, PG; lia); try reflexivity;
    try (cbn [eval]; exact E152);
    try (unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; unfold SEC_INST; lia).
  all: try (intros z Hz; split; [|unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END, SEC_INST in *; lia];
            first [ right; left; unfold qrtc_zone; rewrite <- EG; unfold Inv.QG; lia
                  | left; right; right; right; left; unfold SEC_INST in *; lia
                  | right; right; unfold qrtc2_zone; lia ]).
  all: repeat apply Forall_cons; try apply Forall_nil.
  all: cbv beta iota; eexists; (split; [first [reflexivity | exact E155 | exact E156 | exact E152 | exact E151 | exact E200]|]);
       first [ exact HS0 | exact HS8 | rtc_cell HR ].
Qed.

Hypothesis HQP : QP A0 A.
Definition zbR (z : nat) : Z := ltac2:(tb__ "0|0|
S9S0Lz;Vz;Z0S9S9S0Ln;R1Va;S9S9S0Ln1;R1Va;S9S9S0Ln2;R1S4bS43VA;A1A1S9Va;Ln3;X9x2Ln2;X9x2Ln1;X9x2Ln;X9x2").
Definition zhiR (z : nat) : Z := match z with 0%nat => 0x643000 | 3%nat => 2 ^ 64 | _ => 8192 end.
Definition ZUR : list nat := ltac2:(tb__ "0|0|
SaS9U0SaS9U3SaS9UaSeS9A1A3A3A3").

Lemma tail_R : ltac2:(tb__ "0|0|
S9S8S42S1bSbS57Q40A1A1S99R4R3R2A3S1bSeaR1Vtmp';A2Sc7R2Va;Vn0;Vnd;Vit;A5Sc6R3Va;Vnd;Vit;A4S97VQ;VX;S8aS52VJ';Se7R4R6A5A3F_;F_;F_;Fr';S1bS7dR7R5R1A3Sc6R2Va;Vnd;Vit;A4S97VQ;VX;S8aS52VJ';S64RaR9A2R3R6A5A3F_;F_;Fr;F_;F_;Ftp1;FrS;Flst;Fl;Ff;").
Proof.
  intros f l lst rS tp1 TE HCq r KV HSr.
  pose proof (TENV_keep l lst rS r TE KV) as ((E165 & E200 & _) & HTr & HFr & _ & HXr & HIr).
  apply (tr_glue X _ J' RI tp1 (fun r' => HVX r' tmp' /\ HVI r' a n0 nd it /\ HVS r' a nd it)); [|intros r' (H1 & H2 & H3); exact (HCq r' H1 H2 H3)].
  intros [tr [ms md]] Hw. destruct (proj2 Hw) as (HK & HCB & HRM & HFRM). cbn [w_tr w_cfg cfg_model fst snd] in HK, HCB, HRM, HFRM.
  assert (HTH' : aa_q_thread A' = []) by reflexivity. assert (HCI' : aa_cache_inited A' = true) by exact HCI.
  pose proof (benv_of_K K HL A' HCI' r tp1 tr md HK) as BE.
  destruct (batch_addr_facts A' HTH' r (mkQB a its s) BE ltac:(left; reflexivity)) as (BA1 & BA2 & BA3 & _). cbn [qb_addr] in BA1, BA2, BA3. change (aa_geom A') with (aa_geom A) in BA2.
  pose proof HCB as (_ & HN0 & HN1 & _). unfold kQuarantineBatchCount in HN1.
  assert (HSEPR : forall z z', In z ZUR -> In z' ZUR -> z <> z' -> zbR z + zhiR z <= zbR z' + zloS z' \/ zbR z' + zhiR z' <= zbR z + zloS z).
  { pose proof (topG_range (aa_geom A)) as TG. intros z z' Hz Hz' NE. unfold ZUR in *. cbn [In] in Hz, Hz'.
    destruct Hz as [<-|[<-|[<-|[]]]]; destruct Hz' as [<-|[<-|[<-|[]]]]; try (exfalso; apply NE; reflexivity); unfold zbR, zhiR, zloS; lia. }
  set (TJ := (fun (_ : valuation) (_ : list word) (_ : list event) (_ : Model) => True) : jpredA).
  assert (HT : SPA segsA TJ (s_C (T_fin f l)) r tp1 (tr, mkCfg ms md)) by (split; [exact (proj1 Hw) | exact I]).
  destruct (s_step K HL A0 rho0 zbR zloS zhiR ZUR HSEPR (T_fin f l) J' (DSR (ag_ctx (aa_geom A))) [] A' r tp1 tr ms md (T_fin_ok f l)
              (JRI_stable K HL A0 rho0 A' a n0 (S nd) its tmp' rest) (fun z Hz => HQW z (QW_unmap z Hz)) (LR_objs f l _) eq_refl HT HK HFRM (ro_all r tp1 tr md HK E200 HQP))
    as (rho5 & H5 & V5 & RM5 & AG5 & EV).
  { intros HK3 HF3 EV3. set (rho3 := rho_absorb r (map dobj (DSR (ag_ctx (aa_geom A)))) (vms md tp1 ms)) in *. cbn [T_fin s_bs combine rho_sets].
    assert (HS3 : HVS rho3 a nd it) by (unfold HVS; rewrite EV3; exact HSr).
    split; [split; [exact HK3 | split; [rewrite EV3; exact HCB | split; [rewrite EV3; exact HRM | exact HF3]]]|].
    destruct (kq_facts segsA K HL A' rho3 tp1 _ _ HK3) as [_ HRIG3 HRTC3 _ _ _ _ _ _ _ _ _ _]. change (aa_geom A') with (aa_geom A) in HRIG3, HRTC3.
    assert (E163 : bv_unsigned (eval rho3 vS7) = a + 152 + 8 * Z.of_nat nd) by (destruct HIr as (_ & X0 & _); unfold rho3; rewrite eval_absorb; unfold vS7; cbn [eval]; rewrite X0, u64_lit by lia; reflexivity).
    split; [|split; [|split; [|intros _; apply Forall_nil]]].
    -
      unfold T_fin. cbn [s_N]. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      + unfold sbS, carve_okq. cbn [eval]. rewrite u64_lit by lia.
        split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
        split; [unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia|].
        split; [intros off Hoff; split; [apply wok_of_imageA; lia | apply rd_of_imageA; lia]|].
        unfold cells_in_view. repeat apply Forall_cons; try apply Forall_nil.
        assert (HSB : cell_ok (view segsA (rm rho3)) (mkACell 0xeaa78 8 (ag_spacebeg (aa_geom A)))) by (unfold rtc_inv, rtc_cells in HRTC3; exact (cells_ok_nth _ _ 3 _ HRTC3 eq_refl)).
        eapply (civ_cell rho3 (rm rho3) 0 0xeaa78); [exact HSB | unfold vSB; cbn [eval]; exact (proj1 (proj2 (proj2 HRIG3))) | lia | lia].
      + unfold itS, carve_okq. rewrite E163.
        split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
        split; [unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia|].
        split.
        * intros off Hoff. replace (a + 152 + 8 * Z.of_nat nd + off) with (a + 24 + 8 * Z.of_nat nd + (off + 128)) by lia.
          eapply (cell_wok_rd _ _ _ _ _ HS3); cbn [Z.of_nat]; lia.
        * unfold cells_in_view. repeat apply Forall_cons; try apply Forall_nil.
          eapply (civ_cell rho3 (rm rho3) (a + 152 + 8 * Z.of_nat nd) (-128)); [replace (a + 152 + 8 * Z.of_nat nd + -128) with (a + 24 + 8 * Z.of_nat nd) by lia; exact HS3 | unfold vIT; cbn [eval]; exact E165 | lia | lia].
    -
      unfold T_fin. cbn [s_N s_ZDn map]. constructor; [|constructor; [|constructor]].
      + unfold in_zone, sbS, carve_obj, carved. rewrite obj_range_mk by lia. cbn [eval fst snd]. rewrite u64_lit by lia.
        split; [unfold ZUR; cbn; tauto|]. unfold zloS, zhiR, zbR. split; [lia|]. split; [lia|]. right. lia.
      + unfold in_zone, itS, carve_obj, carved. rewrite obj_range_mk by lia. rewrite E163. cbn [fst snd].
        split; [unfold ZUR; cbn; tauto|]. unfold zloS, zhiR, zbR. split; [lia|]. split; [lia|]. right. lia.
    -
      unfold T_fin at 2. cbn [s_ZDo].
      apply (in_zone_same rho3 _ _ _ _ _ (ss_objs (ax_S DQI0)) ZD_fixS (LR_ref f l)).
      apply (in_zone_ext_list rho3 (zbS (ag_thread (aa_geom A)) (ag_ctx (aa_geom A)) (topG (aa_geom A)) h) zloS (zhiS msz) ZUS).
      + apply (inz_fixS A it i ch rho3); [unfold top_high in *; exact HTr|].
        apply Forall_forall. intros g Hg. apply (holds_agree_vals NPRE r rho3 g); [split; [intros v0 _; reflexivity | intros l0; reflexivity] | exact (proj1 (forallb_forall _ _) pre_facts_below g Hg) | exact (proj1 (Forall_forall _ _) HFr g Hg)].
      + unfold ZD_fixS. repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; (split; [unfold ZUR; cbn; tauto | split; [reflexivity | split; reflexivity]]). }
  cbn [T_fin s_bs combine rho_sets] in V5, AG5.
  assert (VV : forall v0, In v0 [160; 161; 162; 163; 164; 165; 166; 184; 185; 186; 187; 208]%positive -> rw rho5 v0 = rw r v0).
  { intros v0 Hv. rewrite (V5 v0 (SVar v0)); [reflexivity|]. unfold T_fin. cbn [s_M]. unfold MI, idm. apply in_map_iff. exists v0. split; [reflexivity | exact Hv]. }
  exists rho5. split; [exact H5|].
  destruct HXr as (E184 & E185 & E186 & E187 & E208). destruct HIr as (E162 & E163' & E164 & E165' & E166).
  split; [unfold HVX; rewrite !VV by (cbn; tauto); tauto|]. split; [unfold HVI; rewrite !VV by (cbn; tauto); tauto|].
  unfold HVS. rewrite RM5, EV. exact HSr.
Qed.
End Tail.
End SegQS_tail.

(* [comment removed for export] *)
Module SpineMallocR14.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "and"; "eq"; "or"; "not"; "@Corelib.Numbers.BinNums"; "Z"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "mul"; "of_nat"; "lt"; "ltb"; "sub"; "to_nat"; "ge"; "modulo"; "pow"; "@Corelib.Init.Datatypes"; "bool"; "length"; "list"; "None"; "app"; "nil"; "option"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SAlu"; "eval"; "valuation"; "rm"; "SLit"; "SMd"; "SVar"; "sv"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCredit"; "prim_credit"; "MUCAP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillJ"; "FAb"; "phase"; "committed"; "frozen"; "ghosts"; "ph_f"; "ph_fill"; "ph_pop"; "revealedp"; "rlink"; "entryR"; "mlink"; "ph_u"; "releasedp"; "zoneR"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SUB"; "ALU_SLL"; "M_MUL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget"; "LIMIT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR"; "vNEW"; "vK"; "vNF"; "vAU"; "vFA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "m_vmmaps"; "vm_limit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "paid"; "headroom"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "aa_geom"; "class_state"; "cs_allocated_user"; "cs_cache"; "cs_free_array"; "cs_mapped_free_array"; "cs_mapped_user"; "AA"; "ag_spacebeg"; "ag_thread"; "budget_bound"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel"; "refill_cs"; "cls_pure"; "refillA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "bview"; "view"; "cell_ok"; "mkACell"; "@Corelib.Lists.ListDef"; "nth"; "skipn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP"; "V_SIZE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "kUserMapSize"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "live_ids"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModelP"; "newZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs"; "q_ids"; "qall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jt.SpineMallocR14.ARMP"; "e16P"; "e32P"; "e48P"; "e_srcP"; "@Stdlib.Lists.List"; "In"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require PrimCredit PrimCreditLaws Inv InvLaws.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.SegD_cost OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCredit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCreditLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillModel RefillModelP RefillBits.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillTR RefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ii.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require io.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require js.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jj.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModelP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillBits OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.RefillJP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j9.RebuildRP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocR1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SpineMallocR2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jc.SpineMallocR3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.js.SpineMallocR6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineMallocR7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jk.SpineMallocR12 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jj.SpineMallocR13.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation segs := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree.segsA.

Lemma AInvA_credit : ltac2:(tb__ "0|0|
S4aS1aS12S21Q40A1A1S3eS59S3dR4R3R2R1A5S0S5S6S41R2R3A2S22R5A1A2S4dR5A1A2S1S4S40S3fR2A1A1S37A3A2F_;Fmd;Ftp;Frho;FA;").
Proof.
  intros A rho tp md (HG & HR & HF & HRest & HM & HI3 & HB).
  destruct HRest as (_ & _ & _ & _ & _ & HD & _). unfold depot_wf in HD.
  destruct HM as (_ & PB & VL & V0 & K0 & F0 & _ & _ & _ & _ & _ & _ & DN & PC & _).
  split; [|exact VL]. eapply Z.le_trans; [exact PB|].
  apply budgetD_le_budget; [| |exact DN|exact PC|exact K0|exact F0].
  - exact (dep_cost_bound_mem _ _ HD).
  - exact (dm_F_NFBLK _ _ HD).
Qed.

Section ARMP.
Variables (A : AA) (rb : valuation) (tp0 : list word) (md0 : Model) (W : list ulink) (st : ustop) (rho : valuation).
Hypothesis HE : ltac2:(tb__ "0|0|
S2eVA;Vrb;Vtp0;Vmd0;VW;Vst;Vrho;A7").
Hypothesis PF : popfacts A rb.
Let nv : Z := bv_unsigned (rw rb 12%positive).
Let c : Z := cls_of nv.
Let cs : class_state := cst_of A nv.
Let k : Z := kchunks c.
Let S : Z := Size c.
Let nf : Z := Z.of_nat (length (cs_free_array cs)).
Let au : Z := cs_allocated_user cs.
Let mu : Z := cs_mapped_user cs.
Let mfa : Z := cs_mapped_free_array cs.
Let new : Z := gh_new A rb.
Let out : list Z := ltac2:(tb__ "0|1|
S14S4S5aS43VA;A1M0VA;Vc;A3S5cG0S5dVA;A1Vc;A3A3").
Let fP : list Z := faP c cs.

Lemma P_c : 1 <= c <= 30.
Proof. pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. unfold cfacts in CF. cbn zeta in CF. destruct CF as ((_ & C1 & _) & _). exact C1. Qed.

Lemma entry_pure : ltac2:(tb__ "0|0|
S0S4fVc;Vcs;Vout;A3S0S1S12S4A1S46Vcs;A1S15S4A1A3S0S9Vnf;Vk;A2S5S6Vmu;S58A2S23Vc;A1A2A2A2A2").
Proof.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. unfold cfacts in CF. cbn zeta in CF. fold nv c cs in CF.
  destruct CF as (_ & _ & _ & _ & (_ & _ & Hc0) & _).
  destruct HE as (_ & HA & _). pose proof HA as (HG & _ & _ & HRest & _). destruct HRest as (_ & _ & Hprim & _ & Hq & _). destruct Hprim as (_ & _ & _ & PC).
  destruct PF as (NP & RM & _). fold nv c cs in NP, RM.
  split; [exact (entry_cls_pure _ A c P_c HG (PC c P_c) Hq)|]. split; [exact Hc0|]. split; [exact NP | unfold kUserMapSize; exact RM].
Qed.

Lemma P_newZ : ltac2:(tb__ "0|0|
S1S4S5bVc;Vcs;A2Vnew;A3").
Proof. unfold newZ, new, gh_new. fold nv c cs. reflexivity. Qed.

Lemma P_csR : ltac2:(tb__ "0|4|
S4eVc;Vcs;A2S44S0S1S12S4A1S46R1A1M0S56S4ScSbS6Vnf;Vnew;A2M1Vk;A2M2A1VfP;A3A3S0S1S4S8S11S4G0A2A1Vk;A3S0S1S4S8S11S4S47R1A1A2A1G2A3S0S1S4S45R1A1S6Vau;S7Vnew;VS;A2A2A3S0S1S4S49R1A1S6Vmu;Z40000M3A2A3S0S1S4S48R1A1S10S4L_;SaVmfa;S7Z4G1A2A2S6Vmfa;G3A2Vmfa;X10x2A3S0S1S4S8S11S4VfP;A2A1G1A3S4S62S4R1VfP;A3S0S5Z0R2A2S9R2SfZ2Z1cA2A2A2F_;Fx;A2A2A2A2A2A2A2TcsR;").
Proof.
  destruct entry_pure as (HP & Hc0 & NP & RM).
  pose proof (P_fields c cs out P_c HP NP RM) as X. cbn zeta in X. rewrite P_newZ in X. fold nf au mu mfa S k fP in X.
  pose proof (P_faP_len c cs out P_c HP RM) as LP. rewrite P_newZ in LP. fold nf fP in LP.
  destruct X as (X1 & X2 & X3 & _ & X5 & X6 & X7). rewrite LP in X1.
  cbn zeta. split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split; [exact X5|]. split; [exact X6|]. split; [exact X7|]. split; [exact LP|].
  exact (P_ids c cs out P_c HP RM).
Qed.

Lemma pop_credit_eq : ltac2:(tb__ "0|1|
S1S4S6S6S22S50VA;Vc;A2A1Z48000M0A2S10S4L_;SaVmfa;S7Z4S6Vnf;Vnew;A2A2A2G0Z0X10x2A2S22VA;A1A3").
Proof.
  destruct entry_pure as (HP & Hc0 & NP & RM). pose proof P_csR as (_ & _ & _ & _ & EMU & EMF & _). cbn zeta in EMU, EMF.
  destruct (refill_pure c cs out P_c HP Hc0 ltac:(intros _; exact RM)) as (HPR & _). cbn zeta in HPR.
  destruct HPR as (R1 & _ & _ & R4 & _ & _ & _ & _ & _ & _ & R10 & R11). destruct HP as (P1 & _ & _ & P4 & _ & _ & _ & _ & _ & _ & _ & _).
  pose proof HE as (_ & HA & _).
  pose proof HA as (_ & _ & _ & HRest & _). destruct HRest as (_ & _ & (PL & _) & _).
  assert (Hlen : (Z.to_nat c < length (aa_cls A))%nat) by (rewrite PL; pose proof P_c as C1; clear -C1; lia).
  pose proof (prim_credit_populate A (refillA A c) c P_c) as PP. cbn zeta in PP.
  assert (E1 : nth (Z.to_nat c) (aa_cls (refillA A c)) cs_empty = refill_cs c cs).
  { unfold refillA. cbn [aa_cls]. rewrite nth_list_upd_same by exact Hlen. reflexivity. }
  assert (E0 : nth (Z.to_nat c) (aa_cls A) cs_empty = cs) by reflexivity.
  rewrite E1, E0 in PP. fold mu mfa in PP, P1, P4. rewrite EMU in PP, R1, R10. rewrite EMF in PP, R4, R11.
  assert (M8 : mu mod 8 = 0).
  { unfold kUserMapSize in P1. destruct (proj1 (Z.mod_divide mu (2 ^ 18) ltac:(clear; lia)) P1) as [q Hq]. rewrite Hq. replace (q * 2 ^ 18) with (q * 32768 * 8) by (clear; lia). apply Z_mod_mult. }
  assert (F8 : mfa mod 8 = 0).
  { unfold kFreeArrayMapSize in P4. destruct (proj1 (Z.mod_divide mfa (2 ^ 18) ltac:(clear; lia)) P4) as [q Hq]. rewrite Hq. replace (q * 2 ^ 18) with (q * 32768 * 8) by (clear; lia). apply Z_mod_mult. }
  specialize (PP ltac:(intros c' Hc' Hne; unfold refillA; cbn [aa_cls]; apply nth_list_upd_other; pose proof P_c as C1; clear -C1 Hc' Hne; lia) M8).
  destruct (mfa <? 4 * (nf + new)) eqn:E.
  - specialize (PP ltac:(rewrite Z.add_mod, M8 by (clear; lia); reflexivity) ltac:(clear -R10; lia) F8 ltac:(rewrite Z.add_mod, F8 by (clear; lia); reflexivity) ltac:(clear -R11; lia)).
    replace (mu + 262144 - mu) with 262144 in PP by (clear; lia). replace (mfa + 262144 - mfa) with 262144 in PP by (clear; lia). change (262144 / 8) with 32768 in PP. clear -PP. lia.
  - specialize (PP ltac:(rewrite Z.add_mod, M8 by (clear; lia); reflexivity) ltac:(clear -R10; lia) F8 F8 ltac:(clear -R11; lia)).
    replace (mu + 262144 - mu) with 262144 in PP by (clear; lia). replace (mfa - mfa) with 0 in PP by (clear; lia). change (262144 / 8) with 32768 in PP. change (0 / 8) with 0 in PP. clear -PP. lia.
Qed.

Lemma pop_credit : ltac2:(tb__ "0|2|
S0S5S6Z48000M0S10S4L_;SaVmfa;S7Z4S6Vnf;Vnew;A2A2A2G0Z0X10x2A2S22VA;A1M1A2S0S5S6S41Vmd0;Vtp0;A2G1A2S37A2S1S4S40S3fVmd0;A1A1S37A3A2A2").
Proof.
  pose proof pop_credit_eq as EQ. pose proof (prim_credit_nonneg (refillA A c)) as NN.
  pose proof HE as (_ & HA & _ & _ & HBud & Hnv & _). fold nv in HBud.
  destruct (AInvA_credit A rb tp0 md0 HA) as (CR & VL).
  unfold budget_ok_alloc, limit_ok_alloc in HBud. destruct HBud as (LO & _). unfold budget_bound in CR.
  pose proof (acost_mono (aa_V A) (aa_V A + nv) ltac:(clear -Hnv; lia)) as AM. unfold BETA_M in *.
  pose proof HA as (_ & _ & _ & _ & HMI & _). destruct HMI as (_ & _ & _ & _ & K0 & _).
  split; [clear -EQ NN; lia|]. split; [clear -CR LO AM K0; lia | exact VL].
Qed.

Lemma pop_headroom : ltac2:(tb__ "0|6|
S25S12S21Q40A1A1S3eS2fVA;Vrb;Vtp0;Vmd0;R3R2R1A7SdS42R2R3A2SbS22VA;A1S6S6S10S4L_;M0S26S30R4A1M1A1Z40000M2Z0M3X10x2G0S26S29R4A1M4A1G2G3X10x2A2S7Z1000S6G0S2cG1A1Z8M5G3X10x2G0S2cG4A1G5G3X10x2A2A2A2A2A2F_;Fmd;Ftp;Fph;").
Proof.
  intros ph tp md HM. destruct pop_credit as (_ & CR & VL).
  unfold mlink in HM. cbn zeta in HM. destruct HM as (_ & _ & M3 & _ & _ & _ & tp1 & _ & _ & _ & M10).
  unfold headroom. rewrite M3, VL. unfold kUserMapSize, kFreeArrayMapSize in M10.
  destruct (committed (ph_u ph)), (committed (ph_f ph)), (revealedp (ph_u ph)), (revealedp (ph_f ph)); clear -CR M10; lia.
Qed.

Lemma pop_geo : ltac2:(tb__ "0|9|
S0S0S5Z1M0Vc;A2S5Vc;Z1eA2A2S0S0S5Z20VS;A2S5VS;Z10000A2A2S0S0S5Z0M1Vau;A2S5Vau;Vmu;A2A2S0S5Vmu;Zdffc0000A2S0S0S5Z4M2Vnew;A2S5Vnew;Z2001A2A2S0S0S5G0Vk;A2S5Vk;Z8A2A2S0S5Vk;Vnew;A2S0S5G1Vnf;A2S0S5S7G2Vnf;A2Vmfa;A2S0S5Vmfa;Z1ffc0000A2S0S1S4SeVmfa;Z40000A2G1A3S0S5Z100080000000S4bS43VA;A1M3A1M4A2S0S5S6S6G4Z2000000000A2Z1000M5A2M6Z7fffff800000A2S0S1S4S24VA;Vrb;A2S6S6G4S7Vc;Z100000000A2A2Ze0000000A2A3S0S5G5S4cG3A1M7A2S0S2S5S6G7G5A2M8G4A2S5G6G7A2A2S2S5G8Z7fff7000A2S5Z10007fff8000G7A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF.
  destruct (new_nums A rb CF PF) as (N1 & N2 & N3 & N4 & N5 & _ & _ & N8 & N9 & N10 & N11 & _). cbn zeta in N1, N2, N3, N4, N5, N8, N9, N10, N11.
  unfold cfacts in CF. cbn zeta in CF. fold nv c in CF. destruct CF as ((_ & C1 & _) & (K1 & _) & _ & _ & _ & (G12 & G13 & G14 & TG) & (T1 & T2 & TI & PS1) & TB).
  assert (FAr : FAb A rb = ag_spacebeg (aa_geom A) + c * 4294967296 + 3758096384).
  { unfold FAb, free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize. fold nv c. clear; lia. }
  repeat (split; [first [assumption | exact K1 | clear -G14 TG; lia]|]). exact TB.
Qed.

Lemma old_cell_off : ltac2:(tb__ "0|1|
S25S4S5S2aR2A1Vnew;A2S5S2bR3A1Z10A2S0S5S24VA;Vrb;A2M0R3A2S9R3S6G0S7Z4Vnf;A2A2A2A2S3S32VA;Vrb;R5R4A4A1F_;F_;F_;Fz;Fph;").
Proof.
  intros ph z HFL HPO Hz HZ.
  destruct pop_geo as (C1 & S1 & AU0 & MU1 & N4 & K1 & KN & NF0 & MF1 & MF2 & MF0 & G13 & G14 & FAr & T1 & PS1 & TB).
  unfold zoneR in HZ. unfold gh_nf in HZ. fold nv c cs nf new in HZ.
  unfold U0, F0, free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize, kUserMapSize, kFreeArrayMapSize, region_info, kRegionInfoStride, PCE in HZ. fold nv c cs mu mfa in HZ.
  rewrite kSpaceSize_val in HZ. rewrite FAr in Hz, HZ.
  assert (SHB : forall x, 0 <= x <= 140737479966720 -> 2147450880 <= Sh x /\ Sh x + 32768 <= 17594333495296 + 32768) by (intros x Hx; unfold Sh, SHADOW_OFF; clear -Hx; lia).
  pose proof (SHB (ag_spacebeg (aa_geom A) + c * 2 ^ 32 + mu) ltac:(clear -C1 G13 G14 AU0 MU1; lia)) as B1.
  pose proof (SHB (ag_spacebeg (aa_geom A) + c * 2 ^ 32 + (2 ^ 32 - 2 ^ 29) + mfa) ltac:(clear -C1 G13 G14 NF0 MF1 MF2; lia)) as B2.
  assert (B1' : Sh (ag_spacebeg (aa_geom A) + c * 2 ^ 32 + mu) + 32768 <= 17594333495296).
  { unfold Sh, SHADOW_OFF. clear -C1 G13 G14 AU0 MU1. lia. }
  assert (B2' : Sh (ag_spacebeg (aa_geom A) + c * 2 ^ 32 + (2 ^ 32 - 2 ^ 29) + mfa) + 32768 <= 17594333495296).
  { unfold Sh, SHADOW_OFF. clear -C1 G13 G14 NF0 MF1 MF2. lia. }
  destruct HZ as [[_ X]|[[_ X]|[[_ X]|[[_ X]|[[X _]|[X|[[_ X]|[_ X]]]]]]]]; clear -X Hz C1 AU0 MU1 NF0 MF1 MF2 G13 G14 T1 PS1 TB B1' B2' HFL HPO N4; lia.
Qed.

Lemma P_HSRC : ltac2:(tb__ "0|1|
S25S51S1S4S2aR2A1Vnew;A3S5S2bR3A1Z10A2S2dVA;Vrb;R4S52S3dS1bVrb;A1A2R3A5S4S0S5Z0M0R1A2S9R1S8S11S4VfP;A2A1A2A2S53R6S54S6S24VA;Vrb;A2S7Z4R2A2A2U4S55S4ScR2A1VfP;G0A4A3A2F_;Fidx;F_;F_;F_;Fm;Fph;").
Proof.
  intros ph m HFL HPO (L1 & _ & L3 & _) idx Hidx.
  destruct entry_pure as (HP & Hc0 & NP & RM). pose proof P_csR as (_ & _ & _ & _ & _ & _ & LP & _). cbn zeta in LP. rewrite LP in Hidx.
  destruct pop_geo as (C1 & S1 & AU0 & MU1 & N4 & K1 & KN & NF0 & _).
  destruct (Z_lt_dec idx nf) as [OLD|NEW].
  - unfold fP. rewrite (P_nth_old c cs (Z.to_nat idx)) by (fold nf in OLD; unfold nf in OLD; clear -OLD Hidx; lia).
    eapply cell_ok_agree_range; [|exact (proj1 (entry_fa _ _ _ _ _ _ _ HE) idx ltac:(fold nv c cs nf; clear -OLD Hidx; lia))].
    cbn [c_addr c_w]. change (Z.of_nat 4) with 4. intros z Hz. apply L1. apply (old_cell_off ph z ltac:(rewrite HFL; clear; lia) HPO). clear -Hz OLD Hidx. lia.
  - set (j := nf + new - 1 - idx). assert (Hj : 0 <= j < new) by (unfold j; clear -NEW Hidx; lia).
    pose proof (L3 j ltac:(rewrite HFL; exact Hj)) as CE. unfold gh_nf in CE. fold nv c cs nf new au S in CE.
    replace (nf + new - 1 - j) with idx in CE by (unfold j; clear; lia).
    unfold fP. replace (Z.to_nat idx) with (Z.to_nat (Z.of_nat (length (cs_free_array cs)) + newZ c cs - 1 - j)) by (rewrite P_newZ; fold nf; unfold j; clear -Hidx; lia).
    rewrite (P_nth_new c cs j ltac:(rewrite P_newZ; exact Hj)). fold au S. exact CE.
Qed.

Lemma P_HDEF : ltac2:(tb__ "0|4|
S25S51S2S1S10S31S29R2A1A1S17A3S5S7Z4M0S6Vnf;Vnew;A2A2M1Vmfa;A2A2S2dVA;Vrb;R3S52S3dS1bVrb;A1A2R2A5S4S0S5S6S24VA;Vrb;A2M2S7G0Vnf;A2A2R1A2S9R1S6G2G1A2A2A2S3S1S16S21Q8A1M3A1R5R2A1S13G3A1A3A1F_;Fz;F_;F_;Fm;Fph;").
Proof.
  intros ph m HARM (L1 & L2 & _) z Hz.
  destruct pop_geo as (C1 & S1 & AU0 & MU1 & N4 & K1 & KN & NF0 & MF1 & MF2 & MF0 & G13 & G14 & FAr & _).
  assert (ZD : zoneR A rb ph z \/ ~ zoneR A rb ph z).
  { unfold zoneR. destruct (revealedp (ph_u ph)), (releasedp (ph_u ph)), (revealedp (ph_f ph)), (releasedp (ph_f ph)), (ph_cnt ph), (ph_ri ph); clear; lia. }
  destruct ZD as [ZI|ZO]; [exact (L2 z ZI)|]. rewrite (L1 z ZO).

  assert (LT : z < FAb A rb + mfa).
  { destruct (Z_lt_dec z (FAb A rb + mfa)) as [X|X]; [exact X|]. exfalso. destruct HARM as [REL|FIT]; [|clear -Hz X FIT; lia].
    apply ZO. unfold zoneR. right; right; right; left. split; [exact REL|]. unfold F0, kFreeArrayMapSize. fold nv c cs mfa. unfold FAb in Hz, X. fold nv c in Hz, X. clear -Hz X N4 MF1. lia. }
  destruct HE as (_ & HA & _). pose proof HA as (HG & _ & _ & HRest & _). destruct HRest as (_ & _ & Hprim & _). destruct Hprim as (_ & _ & _ & P4). specialize (P4 c C1).
  unfold class_repr in P4. change (nthZ (aa_cls A) c cs_empty) with cs in P4.
  destruct P4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PR & _).
  destruct (PR z ltac:(unfold FAb in Hz, LT; fold nv c in Hz, LT; fold nf mfa; clear -Hz LT; lia)) as [b Hb].
  rewrite maskv_out in Hb; [change (view segs (rm rb) z = Some b) in Hb; rewrite Hb; discriminate|].
  apply fs_footb_space; [exact HG|]. rewrite kSpaceSize_val. rewrite FAr in Hz. clear -Hz C1 NF0 N4 MF1 MF2 G13 G14. lia.
Qed.

Definition e_srcP : sv := ltac2:(tb__ "0|0|
S18S33S3cS18S35S18S34S18S33S3aS38A3S39A3S1cZ2A1A3A3").
Definition e16P : sv := ltac2:(tb__ "0|0|
S18S34S18S33S3aS38A3S39A3").
Definition e32P : sv := ltac2:(tb__ "0|0|
S18S33S3bS1dS36S38S1eS57A1A3A3").
Definition e48P : sv := SAlu ALU_ADD vMU (SLit 262144).
Definition e24M : sv := SAlu ALU_ADD vMFA (SLit 262144).

Lemma P_HSRCP : ltac2:(tb__ "0|1|
S1aS27Vrb;R1A2S28VA;Vrb;R2A3S1S21Q40M0A1S19R3S61A2S20G0S6S24VA;Vrb;A2S7Z4SbS8S11S4VfP;A2A1Vk;A2A2A2A2A3F_;F_;Fr;").
Proof.
  intros r HFz HGh. pose proof P_csR as (_ & _ & _ & _ & _ & _ & LP & _). cbn zeta in LP. rewrite LP.
  destruct pop_geo as (C1 & S1 & AU0 & MU1 & N4 & K1 & KN & NF0 & MF1 & MF2 & MF0 & G13 & G14 & FAr & _).
  destruct HGh as (_ & Q221 & _ & _ & _ & _ & Q226 & Q227 & Q228 & _). unfold gh_nf in Q221. fold nv c cs nf in Q221. fold nv c k in Q227. fold new in Q228.
  unfold e_srcP, vFA, vNF, vNEW, vK. cbn [eval]. rewrite Q221, Q226, Q227, Q228. apply bv_eq.
  rewrite add_val, sll_val, sub_val, add_val. rewrite !u64_lit by (rewrite ?FAr; clear -C1 G13 G14 NF0 MF1 MF2 N4 K1; lia).
  change (2 mod 64) with 2. rewrite (Z.mod_small (nf + new)) by (clear -NF0 MF1 MF2 N4; lia).
  rewrite (Z.mod_small (nf + new - k)) by (clear -NF0 MF1 MF2 N4 KN K1; lia).
  rewrite Z.shiftl_mul_pow2 by (clear; lia). rewrite (Z.mod_small (_ * 2 ^ 2)) by (clear -NF0 MF1 MF2 N4 KN K1; lia).
  rewrite Z.mod_small by (rewrite FAr; clear -C1 G13 G14 NF0 MF1 MF2 N4 KN K1; lia). clear; lia.
Qed.

Lemma P_HRIv : ltac2:(tb__ "0|2|
S1fS1aS27Vrb;R1A2S28VA;Vrb;R2A3S1S21Q40M0A1M1S19R3R4A2S20G0S10S4L_;SaVmfa;S7Z4S6Vnf;Vnew;A2A2A2S6Vmfa;Z40000A2Vmfa;X10x2A2A3S4eVc;Vcs;A2S44S0S1G1S19R5S5eA2S20G0S8S11S4S47R1A1A2A1A2A3S0S1G1S19R5R6A2S20G0S48R1A1A2A3S0S1G1S19R5S5fA2S20G0S45R1A1A2A3S1G1S19R5S60A2S20G0S49R1A1A2A3A2A2A2TcsR;F_;F_;F_;Fr;Fe24;").
Proof.
  intros e24 r HFz HGh E24 csR. pose proof P_csR as (_ & _ & X3 & X5 & X6 & X7 & _). cbn zeta in X3, X5, X6, X7. fold csR in X3, X5, X6, X7.
  destruct pop_geo as (C1 & S1 & AU0 & MU1 & N4 & K1 & KN & NF0 & MF1 & MF2 & MF0 & G13 & G14 & FAr & _).
  pose proof (entry_rigids _ _ _ _ _ _ _ _ HE HFz) as RG. destruct RG as (_ & E148 & _). fold nv c S in E148.
  destruct HGh as (_ & Q221 & _ & Q223 & Q224 & _ & _ & Q227 & Q228 & _). unfold gh_nf in Q221. fold nv c cs nf in Q221. fold nv c cs au in Q223. fold nv c cs mu in Q224. fold nv c k in Q227. fold new in Q228.
  assert (NS : 0 <= new * S <= 3758096384) by (pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF; destruct (new_nums A rb CF PF) as (_ & _ & _ & _ & _ & M6 & _); cbn zeta in M6; fold nv c cs in M6; fold S au mu new in M6; clear -M6 AU0 MU1 N4 S1; nia).
  rewrite X3, X5, X6, X7. split; [|split; [exact E24|split]].
  - unfold e16P, vNF, vNEW, vK. cbn [eval]. rewrite Q221, Q227, Q228. apply bv_eq. rewrite sub_val, add_val, !u64_lit by (clear -NF0 MF1 MF2 N4 K1 KN; lia).
    rewrite (Z.mod_small (nf + new)) by (clear -NF0 MF1 MF2 N4; lia). rewrite Z.mod_small by (clear -NF0 MF1 MF2 N4 KN K1; lia). reflexivity.
  - unfold e32P, vAU, vNEW, V_SIZE. cbn [eval]. rewrite Q223, Q228, E148. apply bv_eq. rewrite add_val, mul_val, !u64_lit by (clear -AU0 MU1 N4 S1 NS; lia).
    rewrite (Z.mod_small (new * S)) by (clear -NS; lia). rewrite Z.mod_small by (clear -NS AU0 MU1; lia). reflexivity.
  - unfold e48P, vMU. cbn [eval]. rewrite Q224. apply bv_eq. rewrite add_val, !u64_lit by (clear -AU0 MU1; lia). rewrite Z.mod_small by (clear -AU0 MU1; lia). reflexivity.
Qed.
End ARMP.
End SpineMallocR14.

(* [comment removed for export] *)
Module SpineMallocRi0.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "cons"; "true"; "bool"; "nil"; "list"; "prod"; "app"; "Some"; "option"; "false"; "pair"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "sprop"; "ss_next"; "ss_facts"; "valuation"; "ss_objs"; "ss_lenient"; "swf"; "SAlu"; "SLit"; "SVar"; "rw"; "SPBranch"; "SPNot"; "rm"; "sprop_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "la_state"; "leafA"; "sym_runA"; "axst"; "ax_X"; "entailsA"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jt.SpineMallocRi0"; "e3r"; "icc"; "r_9N_0"; "W0"; "FUEL"; "ct0N"; "r_1_0"; "r_2_1"; "r_t1N_0"; "s_bkN"; "s_inN"; "xlN"; "e3p"; "nob"; "r_t1N_1"; "cellsfN"; "r_2_0"; "r_t0N_0"; "r_zN_0"; "s_xN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR"; "cE1"; "cE2"; "GR"; "cR1"; "factsR"; "PV4"; "cR0"; "cT1"; "PV6"; "cE3"; "vK"; "O_pcm"; "cE3b"; "k_e"; "F_r0"; "F_r1"; "F_x"; "O_pccK"; "O_ri"; "PNX"; "cE3a"; "cR0a"; "fa_e"; "keepn"; "nobj"; "ri_e"; "ri_has"; "vAU"; "vFA"; "vMFA"; "vMU"; "vNF"; "vRI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "KcA"; "ulink"; "A_globals"; "Kc_ok"; "UStopLeOrPc"; "malloc_depth"; "mem_keptA"; "pre_facts"; "unwind_factsS"; "unwind_objs"; "ustop"; "@Corelib.Lists.ListDef"; "map"; "firstn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3"; "inclb"; "skel"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "eqb"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_NE"; "BC_LTU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub_id_below"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP"; "O_pcc0"; "O_st"; "E3p"; "E3r"; "F_gen"; "pc_base"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_cache_inited"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "cls_of"; "cnt_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillJ"; "JR"; "entryR"; "gh_nf"; "ph0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel"; "kchunks"; "refillA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SpineMallocR2"; "BASEF"; "BASEO"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jc.SpineMallocR3"; "O_dstc"; "O_srcc"; "e_end"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1"; "JG"; "@Stdlib.Lists.List"; "forallb"; "nth_error"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1"; "RT_m1"; "sw_s1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillTR";
"TRok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jn.SpineMallocR4"; "O_rif"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jq.SpineMallocR5"; "posts_conv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.js.SpineMallocR6"; "e16N"; "e_srcN"; "phFN"; "@Stdlib.ZArith.BinInt.Z"; "le"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillTR RefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require io.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require js.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocR1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SpineMallocR2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jc.SpineMallocR3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jn.SpineMallocR4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jq.SpineMallocR5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.js.SpineMallocR6.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition W0 : list ulink := Wcan 0.
Definition FUEL : nat := 4000%nat.
Definition e3r := Eval vm_compute in (E3r W0 UStopLe 2).
Lemma E3r_eq : ltac2:(tb__ "0|0|
S0S22S7cS29S5cZ2A3S26A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma SK3 : ltac2:(tb__ "0|1|
S0S6S7S7SeSeA2SeA2M0A1S68SdG0S6bS13S1eS26A1A1A4S68SdG0S6bS8SdS8SdS2SdS97S8SdS66S29A1S5fA3A3S96A3S2SdS79S2SdS7aS5SdA1A3A3A3A4A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XX3 : ltac2:(tb__ "0|1|
S0S6S7SeSeA2M0A1S23S26A1S5G0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF3b : ltac2:(tb__ "0|0|
S0S4S6aS8SfS8SfS65S29S5cA2S64S62A1A3S7dA3S11S1eS26A1A1A2S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NX3 : ltac2:(tb__ "0|0|
S0S4S6cS10S1eS26A1A1PdcA2S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma WR0a : ltac2:(tb__ "0|0|
S0S4S15S1eS50S26A1A1A1S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FB0 : ltac2:(tb__ "0|0|
S0S4S93SfS1dS3dA1S8SfS11S1eS26A1A1S8SfS49S4aA3A3A3S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Definition R_1__R : option (list leafA) := ltac2:(tb__ "0|0|
S21S3aS2aS2S25Z4147cS5S25A1A3S41S26A1S3A5").
Local Strategy expand [R_1__R].
Definition r_1 := Eval vm_compute in ((fun ro1__ : option (list leafA) => (match ro1__ with Some l => l | None => [] end)) R_1__R).
Definition r_1_0 := Eval vm_compute in (nth 0 r_1 (mkLeafA (cR0 e3r) RsCut)).
Definition cr1 := Eval vm_compute in (cR1 (factsR e3r) (la_state r_1_0)).
Definition r_2 := Eval vm_compute in (match sym_runA segsA FUEL [0x41704; 0x41560] cr1 true with Some l => l | None => [] end).
Definition r_2_0 := Eval vm_compute in (nth 0 r_2 (mkLeafA cr1 RsCut)).
Definition r_2_1 := Eval vm_compute in (nth 1 r_2 (mkLeafA cr1 RsCut)).
Lemma R_1 : ltac2:(tb__ "0|1|
S0SaS6S20A1M0A1S21S3aS2aS2S25Z4147cS5S25A1A3S41S26A1S3A5S9G0S2S20S2cS5S20A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_1__R <: R_1__R = Some [r_1_0]). Qed.
Lemma LN_0 : ltac2:(tb__ "0|0|
S0S4S14S1eS41S26A1A1A1SbA3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_0 : ltac2:(tb__ "0|0|
S0S4S6cS3dS10S1eS41S26A1A1A1A2S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_r1 : ltac2:(tb__ "0|0|
S0S4S15S1eS3eS3fS26A1S1fS2cA1A2A1A1S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_r1 : ltac2:(tb__ "0|5|
S0SaS7S6S7SeSeA2M0A1M1S6SfA1M2A2M3A1S84S1eS1fS2cA1M4A1S1eS3eS3fS26A1G4A2A1A2S9G3ScG1G2S2G0ScSeSeS54S5bA4S2G0ScSeSeS48S45A4S2G0ScSeSeS51S57A4S5G0A1A3A3A3S5SfA1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NX_r1 : ltac2:(tb__ "0|1|
S0S4S6dS10S1eS3eS3fS26A1S1fS2cA1M0A2A1A1S10S1eG0A1A1A2S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_2 : ltac2:(tb__ "0|1|
S0SaS6S20A1M0A1S21S3aS2aS2S25Z41704S2S25Z41560S5S25A1A3A3S3eS3fS26A1S1fS2cA1A2S3A5S9G0S2S20S36S2S20S2dS5S20A1A3A3A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma LN_1 : ltac2:(tb__ "0|0|
S0S4S14S1eS3eS3fS26A1S1fS2cA1A2A1A1SbA3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_1 : ltac2:(tb__ "0|0|
S0S4S6cS3dS10S1eS3eS3fS26A1S1fS2cA1A2A1A1A2S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Definition nob := Eval vm_compute in ((length (ss_objs (ax_S e3r)) + 2)%nat).
Definition icc := Eval vm_compute in ((length (ss_objs (ax_S e3r)) - 2)%nat).
Definition R_t0N__R : option (list leafA) := ltac2:(tb__ "0|0|
S21S3aS2aS2S25Z41570S2S25Z41584S5S25A1A3A3S1fS2dA1S3A5").
Local Strategy expand [R_t0N__R].
Definition r_t0N := Eval vm_compute in ((fun ro3__ : option (list leafA) => (match ro3__ with Some l => l | None => [] end)) R_t0N__R).
Definition r_t0N_0 := Eval vm_compute in (nth 0 r_t0N (mkLeafA (la_state r_2_1) RsCut)).
Definition ct0N := Eval vm_compute in (cT0 (la_state r_t0N_0)).
Definition R_t1N__R : option (list leafA) := ltac2:(tb__ "0|0|
S21S3aS2aS2S25Z41570S2S25Z41584S5S25A1A3A3S42S2bA1S3A5").
Local Strategy expand [R_t1N__R].
Definition r_t1N := Eval vm_compute in ((fun ro2__ : option (list leafA) => (match ro2__ with Some l => l | None => [] end)) R_t1N__R).
Definition r_t1N_0 := Eval vm_compute in (nth 0 r_t1N (mkLeafA (cT1 ct0N) RsCut)).
Definition r_t1N_1 := Eval vm_compute in (nth 1 r_t1N (mkLeafA (cT1 ct0N) RsCut)).
Definition s_inN := Eval vm_compute in (infer_sub GR (ax_S (la_state r_t0N_0)) (ax_S ct0N)).
Definition s_bkN := Eval vm_compute in (infer_sub GR (ax_S (keepn (la_state r_t1N_0) nob)) (ax_S ct0N)).
Lemma SK_tN : ltac2:(tb__ "0|1|
S0S6S7S7SeSeA2SeA2M0A1S68SdG0S6bS13S1eS2bA1A1A4S68SdG0S6bS8SdS8eS29A1S2SdS79S2SdS7aS2SdS46S2SdS4dS5SdA1A3A3A3A3A3A4A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XX_tN : ltac2:(tb__ "0|1|
S0S6S7SeSeA2M0A1S23S2bA1S5G0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_tNb : ltac2:(tb__ "0|0|
S0S4S6aS8dS29S5cA2S11S1eS2bA1A1A2S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NX_tN : ltac2:(tb__ "0|0|
S0S4S6dS10S1eS2bA1A1S4eA2S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_t1N : ltac2:(tb__ "0|0|
S0S4S15S1eS42S2bA1A1A1S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_t1N : ltac2:(tb__ "0|1|
S0SaS6S20A1M0A1S21S3aS2aS2S25Z41570S2S25Z41584S5S25A1A3A3S42S2bA1S3A5S9G0S2S20S2eS2S20S34S5S20A1A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_t1N__R <: R_t1N__R = Some [r_t1N_0; r_t1N_1]). Qed.
Lemma LN_t1N : ltac2:(tb__ "0|0|
S0S4S14S1eS42S2bA1A1A1SbA3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma OB_bN : ltac2:(tb__ "0|1|
S0S6SdA1S13S1eS1fS2eA1A1A1M0S8SdS69SdS33G0A3S2SdS90S2SdS8fS5SdA1A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_xN : ltac2:(tb__ "0|1|
S0S6SdA1S13S1eS1fS34A1A1A1M0S8SdS69SdS33G0A3S2SdS90S2SdS8fS5SdA1A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma ENT_bkN : ltac2:(tb__ "0|0|
S0S4S24S52S1fS2eA1S33A2S2bS2fA3S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_bkN : ltac2:(tb__ "0|0|
S0S4S72S2fS3dA2S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma S_bk4N : ltac2:(tb__ "0|0|
S0SeS71S2fS40A2S16S6eS18S40A1S17Z4A1A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S_bk6N : ltac2:(tb__ "0|0|
S0SeS71S2fS43A2S16S6eS18S43A1S17Z4A1A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma FB_bNb : ltac2:(tb__ "0|0|
S0S4S6aS2SfS1aS6fS16S6eS18S40A1S17Z4A1A3S91A3S5SfA1A3S11S1eS1fS2eA1A1A1A2S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FB_xNb : ltac2:(tb__ "0|0|
S0S4S6aS2SfS1bS1aS6fS16S6eS18S40A1S17Z4A1A3S91A3A1S5SfA1A3S11S1eS1fS34A1A1A1A2S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_t0N : ltac2:(tb__ "0|1|
S0SaS6S20A1M0A1S21S3aS2aS2S25Z41570S2S25Z41584S5S25A1A3A3S1fS2dA1S3A5S9G0S2S20S37S5S20A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_t0N__R <: R_t0N__R = Some [r_t0N_0]). Qed.
Lemma LN_t0N : ltac2:(tb__ "0|0|
S0S4S14S1eS1fS2dA1A1A1SbA3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_t0N : ltac2:(tb__ "0|0|
S0S4S6cS3dS10S1eS1fS2dA1A1A1A2S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_inN : ltac2:(tb__ "0|0|
S0S4S24S1fS37A1S2bS30A3S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_inN : ltac2:(tb__ "0|0|
S0S4S72S30S3dA2S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma S_in4N : ltac2:(tb__ "0|0|
S0SeS71S30S40A2S16S6eS7eS17Z10A1A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S_in6N : ltac2:(tb__ "0|0|
S0SeS71S30S43A2S9dA3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Definition xlN := Eval vm_compute in (keepn (la_state r_t1N_1) nob).
Definition R_9N__R : option (list leafA) := ltac2:(tb__ "0|0|
S21S3aS2aS2S25Z40e5cS5S25A1A3S31S3A5").
Local Strategy expand [R_9N__R].
Definition r_9N := Eval vm_compute in ((fun ro4__ : option (list leafA) => (match ro4__ with Some l => l | None => [] end)) R_9N__R).
Definition r_9N_0 := Eval vm_compute in (nth 0 r_9N (mkLeafA xlN RsCut)).
Definition cellsfN := Eval vm_compute in (ob_cells (last (ss_objs (ax_S (cE1 (la_state r_9N_0) icc))) O_ri)).
Definition x3N := Eval vm_compute in (cE3 (cE2 (cE1 (la_state r_9N_0) icc))).
Definition r_zN := Eval vm_compute in (match sym_runA segsA FUEL [0x3c614] x3N true with Some l => l | None => [] end).
Definition r_zN_0 := Eval vm_compute in (nth 0 r_zN (mkLeafA x3N RsCut)).
Lemma R_9N : ltac2:(tb__ "0|1|
S0SaS6S20A1M0A1S21S3aS2aS2S25Z40e5cS5S25A1A3S31S3A5S9G0S2S20S28S5S20A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_9N__R <: R_9N__R = Some [r_9N_0]). Qed.
Lemma LN_9N : ltac2:(tb__ "0|0|
S0S4S14S1eS31A1A1SbA3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_9N : ltac2:(tb__ "0|0|
S0S4S6cS3dS10S1eS31A1A1A2S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_x1N : ltac2:(tb__ "0|0|
S0S4S15S1eS3bS1fS28A1S27A2A1A1S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_x1N : ltac2:(tb__ "0|5|
S0SaS7S6S7SeSeA2M0A1M1S6SfA1M2A2M3A1S84S1eS1fS28A1M4A1S1eS3bG4S27A2A1A2S9G3ScG1G2S2G0ScSeSeS48S45A4S5G0A1A3S5SfA1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NX_x1N : ltac2:(tb__ "0|1|
S0S4S6dS10S1eS3bS1fS28A1M0S27A2A1A1S10S1eG0A1A1A2S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XX_1N : ltac2:(tb__ "0|1|
S0S6S7SeSeA2M0A1S23S3bS1fS28A1S27A2A1S5G0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma IC_1N : ltac2:(tb__ "0|0|
S0SaSdA1S94SdS13S1eS3bS1fS28A1S27A2A1A1S27A3S9SdS4cA2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_1N : ltac2:(tb__ "0|2|
S0S6SdA1S13S1eS3bS1fS28A1S27A2M0A1A1M1S8SdS69SdS95S53G0A1U2A2G1A3S2SdS46S2SdS9aS35A1S5SdA1A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_1N : ltac2:(tb__ "0|0|
S0S4S55S35S9cS58S56S59A5S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SK_2N : ltac2:(tb__ "0|1|
S0S6S7S7SeSeA2SeA2M0A1S68SdG0S6bS13S1eS3cS3bS1fS28A1S27A2A1A1A1A4S68SdG0S6bS8SdS8eS29A1S2SdS79S2SdS7aS5SdA1A3A3A3A4A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XX_2N : ltac2:(tb__ "0|1|
S0S6S7SeSeA2M0A1S23S3cS3bS1fS28A1S27A2A1A1S5G0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_2Nb : ltac2:(tb__ "0|0|
S0S4S6aS8dS29S5cA2S11S1eS3cS3bS1fS28A1S27A2A1A1A1A2S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_3aN : ltac2:(tb__ "0|0|
S0S4S15S1eS4fS3cS3bS1fS28A1S27A2A1A1A1A1S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_3bN : ltac2:(tb__ "0|0|
S0S4S15S1eS47S3cS3bS1fS28A1S27A2A1A1A1A1S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FB_3N : ltac2:(tb__ "0|1|
S0S4S93SfS1dS10S1eS47S3cS3bS1fS28A1S27A2A1A1A1M0A1A1S8SfS4bS11G0A1A3A3S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_zN : ltac2:(tb__ "0|1|
S0SaS6S20A1M0A1S21S3aS2aS2S25Z3c614S5S25A1A3S44S3cS3bS1fS28A1S27A2A1A1S3A5S9G0S2S20S38S5S20A1A3A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma LN_zN : ltac2:(tb__ "0|0|
S0S4S14S1eS44S3cS3bS1fS28A1S27A2A1A1A1A1SbA3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_zN : ltac2:(tb__ "0|0|
S0S4S6cS3dS10S1eS44S3cS3bS1fS28A1S27A2A1A1A1A1A2S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Definition e3p := Eval vm_compute in (E3p W0 UStopLe 2).
Lemma E3p_eq : ltac2:(tb__ "0|0|
S0S22S7bS29S5cZ2A3S32A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Definition s_xN := Eval vm_compute in (s_exit (la_state r_zN_0) e3p).
Lemma ENT_xN : ltac2:(tb__ "0|0|
S0S4S24S1fS38A1S32S39A3S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SX_xN : sx_okb s_xN = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma S149_xN : wsub_get s_xN 149%positive = vK.
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S159_xN : wsub_get s_xN 159%positive = vCHX.
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.

Lemma HW0 : ltac2:(tb__ "0|0|
S0S67S5cS61A3S0S6S5eA1S29S5S5eA1A3F_;"). Proof. intros E; discriminate E. Qed.
Definition pop_N A Kc rb tp0 md0 TR KIT HKc rho HE ph PH0 faP HSRC HKF HNFP HFILLR HIDS HCACHE :=
  pop_all A Kc rb tp0 md0 TR KIT HKc W0 UStopLe rho HW0 HE ph PH0 faP HSRC HKF HNFP HFILLR HIDS HCACHE FUEL ct0N r_t1N_0 r_t1N_1 nob s_bkN
    SK_tN XX_tN (inclb_incl _ _ XF_tNb) NX_tN W_t1N R_t1N LN_t1N OB_bN OB_xN ENT_bkN SID_bkN S_bk4N S_bk6N (In_of_inclb _ _ FB_bNb) (In_of_inclb _ _ FB_xNb)
    (la_state r_2_1) r_t0N_0 s_inN e_srcN R_t0N LN_t0N NX_t0N ENT_inN SID_inN S_in4N S_in6N.
Definition entry_i := refill_entry 0 UStopLe e3r SK3 XX3 (inclb_incl _ _ XF3b) NX3 WR0a FB0.
Definition prefix_i A Kc rb tp0 md0 TR KIT HKc := refill_prefix A Kc rb tp0 md0 TR KIT HKc FUEL e3r r_1_0 r_2_0 r_2_1 R_1 LN_0 NX_0 W_r1 D_r1 NX_r1 R_2 LN_1 NX_1.
Definition exit_N A Kc rb tp0 md0 TR KIT HKc rho HE phX PHX HFILLX Hini HRIv HLEN HIDC :=
  exit_steps A Kc rb tp0 md0 TR KIT HKc W0 UStopLe rho HW0 HE phX PHX HFILLX Hini e16N vMFA vAU vMU HRIv HLEN HIDC FUEL xlN r_9N_0 r_zN_0 icc cellsfN
    R_9N LN_9N NX_9N W_x1N D_x1N NX_x1N XX_1N IC_1N OB_1N RI_1N SK_2N XX_2N (inclb_incl _ _ XF_2Nb) W_3aN W_3bN FB_3N R_zN LN_zN NX_zN.
Definition back_N CST XGL PFam HPF A Kc rb tp0 md0 TR KIT rho HW HE phF HREB HMK HLEN HPOP :=
  refill_back CST XGL PFam HPF A Kc rb tp0 md0 TR KIT W0 UStopLe rho HW HE phF HREB HMK HLEN e3p (la_state r_zN_0) s_xN ENT_xN SX_xN S149_xN S159_xN HPOP.
Lemma FJ_Nb : ltac2:(tb__ "0|0|
S0S4S6aS2SfS1bS1aS70S5aS45A3A1S5SfA1A3S11S1eS1fS2dA1A1A1A2S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.

Theorem refill_N_i : ltac2:(tb__ "0|5|
S6S7S25S25A2A1M0G0S7fS5dS6S7S22S86A2A1F_;F_;S9bR3R2R1A3S22S22S0S22R2S26A3S0S22R2S32A3S7fS5dS12S6S74Q40M1A1A1M2S77S77OF_;F_;S99R4R1A2S60R5A1S0S4S80R7A1S3A3S0S25S82R8S73G1S19R6PcM3A2A2A2Z0A3S85S3aS83R7R6RfR9R8A2A5S77S12S75S88RcR2R9R1S29S5cRaA7S9fS8bS81S73G1S19R3G3A2A2A1A1S89RdR3A2A2S12G2S6S76A1S75S87R12R11R8RfR7S9eS8bS81S73G1S19R8G3A2A2A1A1A1R4R3R2R1AaS1S98S3aS8cR13S81S73G1S19R9G3A2A2A1A2M4R5R4R2A5S63R1bR1aR13G4S1cR9A1S1cR5A1A6A2F_;Fmd;Ftr;Ftp';Fr;F_;FHE;Fmd0;Frb;S7fS12G2S12RbS78S3aS92S29S5cR4ReR3A5R12R1R2A5S85S3aS83R3R2R15R4ReA2A5A2FrX;Ftp';Frho';FA';S12S75S12S88RfR3RcR2S29S5cRdA7RcS78S3aS87R10RfR4RdR3S8aA6S1fS36A1R2RdA5R7A2F_;Fr';Fmd0;Frb;S12RaS78S3aS92S29S5cReRdRcA5R12R1RbA5R5A2FrhoE;F_;F_;F_;TQ;F_;F_;FHKc;FKIT;FTR;Ftp;Frho;FKc;FA;F_;F_;FE3P;FE3;FHPF;FPFam;FXGL;FCST;").
Proof.
  intros CST XGL PFam HPF E3 E3P -> ->.
  apply (refill_N CST XGL PFam W0 UStopLe e3r e3p (la_state r_2_0) (la_state r_2_1) xlN (la_state r_zN_0) (In_of_inclb _ _ FJ_Nb)).
  - intros A Kc rho rhoE tp w Hini Hcnt Hw. exact (entry_i A Kc rho rhoE tp w HW0 Hini Hcnt Hw).
  - intros A Kc rb tp0 md0 TR KIT HKc rho r tp Q HE. exact (prefix_i A Kc rb tp0 md0 TR KIT HKc W0 UStopLe rho r tp Q HE).
  - intros A Kc rb tp0 md0 TR KIT HKc rho HE ph PH0 faP. exact (pop_N A Kc rb tp0 md0 TR KIT HKc rho HE ph PH0 faP).
  - intros A Kc rb tp0 md0 TR KIT HKc rho HE phX. exact (exit_N A Kc rb tp0 md0 TR KIT HKc rho HE phX).
  - intros A Kc rb tp0 md0 TR KIT rho HE phF. exact (back_N CST XGL PFam HPF A Kc rb tp0 md0 TR KIT rho HW0 HE phF).
Qed.
End SpineMallocRi0.

(* [comment removed for export] *)
Module SpineMallocSecE4.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "rm"; "rl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "DG"; "aa_sec"; "sec_chunk"; "aa_Km"; "aa_geom"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "list"; "prod"; "pair"; "None"; "length"; "nil"; "option"; "false"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "@Corelib.Init.Logic"; "eq"; "not"; "and"; "False"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "secmapsize"; "stopJ_stable"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "ulink"; "UStopLeOrPc"; "ustop"; "mem_keptA"; "AE_A"; "Posts_malloc"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "div"; "of_nat"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jn.DepotCallS"; "AXK"; "dlink"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger"; "sepZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dblocks"; "dfp_static"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3"; "clsP"; "JGs"; "JGsC"; "slink"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "Sh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.SecBump"; "bumpP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocSec2"; "IMG_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineMallocSec4"; "slink4"].
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
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.CertMallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.id.CertMallocSN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocSec OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocSec2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.InvD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.SecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.SecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SecRoom OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineMallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jn.DepotCallS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jq.SecLinks OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.js.SpineMallocSecOK.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section OKE.
Variable nW : nat. Variable st : ustop. Variable nx : positive. Variable hi : bool.
Let W : list ulink := Wcan nW.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTS : ltac2:(tb__ "0|0|
SeS3fVCST;R1A2S3fS43R2A2S20F_;F_;Fa;").
Hypothesis HCSTD : ltac2:(tb__ "0|0|
SeS3fVCST;R1A2S1eS35R2A1A1F_;Fa;").
Let JGs : ltac2:(tb__ "0|0|
S5S5F_;S5S23S1ScQ40A1S1cFa;Frho;FKc;FA;FAX;") := ltac2:(tb__ "0|0|
S37VnW;Vst;Vnx;A3").
Let JGsC : ltac2:(tb__ "0|0|
S5S5F_;S5S23S1ScQ40A1S1cFa;Frho;FKc;FA;FAX;") := ltac2:(tb__ "0|0|
S38VnW;Vst;Vnx;A3").
Let Posts (A : AA) (Kc : KcA) : ltac2:(tb__ "0|0|
S10S11S41S3dA2A1") := ltac2:(tb__ "0|0|
S2aS29S42S0A1VCST;VXGL;VW;Vst;VA;VKc;A8").
Variables (E1 D2 T4a T4b C5a C5b : axst).

Hypothesis EG12 : ltac2:(tb__ "0|5|
S5S23S1ScQ40M0A1M1S10G1A1M2S1aOF_;S22VW;Vst;A2S24R6A1S36Vhi;SbG0R5A2S21SbG0S2R6PcM3A2A2A1A3S1S1G2S39SbG0R9A2S21SbG0S2RaG3A2A2A1RaR3A4S19S0S1bS0VJGs;S5R1LX;M4RdRcR4RaA5VD2;R3R2A5R8A3F_;FtpY;FrhoY;Frho';S1S19S0S1bS0VJGsC;G4RbRaR9R8A5VE1;R1R7A5R6A3FrhoX;F_;F_;F_;F_;FQ;Ftp;Fa;Frho;FKc;FA;").
Hypothesis EG3 : ltac2:(tb__ "0|7|
S5S23S1ScQ40M0A1M1S1aOF_;S22VW;Vst;A2S24R5A1S2dS2cS2fS14S8S7R7A1A2A1Z1A2S30Z2Z14A2A2SeS1fS2bS3eSbG0R6A2A1M2R1A2S2dR1S2cG2S2eS21SbG0S2R7PcM3A2A2A1Z8A2A2A2A2S1eS1dS16ScQ8A1M4A1S3R8SdG0R2A2A2S13G4A1A3A1F_;Fz;S1S1S10G1A1M5S44SaRcA1SbG0R9A2S21SbG0S2RaG3A2A2A1RaR3A5S19S0S1bS0VJGs;S5S40R1A1LX;RdRcR4RaA5VT4a;R3R2A5R9A3F_;FtY;FrY;Frho'';S1G5S19S0S1bS0VJGs;S5R1LX;M6RcRbRaR9A5VT4b;R2R1A5R8A3FtY;FrY;S1G5S19S0S1bS0VJGs;G6RdRcRbRaA5VD2;R2R1A5R9A3FtX;FrX;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;").
Hypothesis EG41a : ltac2:(tb__ "0|5|
S5S23S1ScQ40M0A1M1S1aOF_;S1dS27Vst;S26A3S1dS10S25A1VW;S15S25A1A3F_;S22VW;Vst;A2S24R6A1S6S1S1S10G1A1M2S11SeSeA2M3S3aG3R1S34R5A1A3S33R2S12SeSeSbG0RbA2S21SbG0S2RcPcA2A2A1A4A2F_;Fbn;S32R5RbR4A3S19S0S1bS0VJGs;S31S5S40R1A1LX;M4R6A2ReRdR5RbA5VC5a;R4R3A5RaA3F_;F_;Ftp';FrhoX;Frho';FG2;S1G2S19S0S1bS0VJGs;G4RbRaR9R8A5VT4a;R2R1A5R7A3FtX;FrX;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;").
Hypothesis EG41b : ltac2:(tb__ "0|5|
S5S23S1ScQ40M0A1M1S1aOF_;S1dS27Vst;S26A3S1dS10S25A1VW;S15S25A1A3F_;S22VW;Vst;A2S24R6A1S6S1S1S10G1A1M2S11SeSeA2M3S3aG3R1S34R5A1A3S33R2S12SeSeSbG0RbA2S21SbG0S2RcPcA2A2A1A4A2F_;Fbn;S32R5RbR4A3S19S0S1bS0VJGs;S31S5R1LX;M4R6A2ReRdR5RbA5VC5b;R4R3A5RaA3F_;F_;Ftp';FrhoX;Frho';FG2;S1G2S19S0S1bS0VJGs;G4RbRaR9R8A5VT4b;R2R1A5R7A3FtX;FrX;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;").
Hypothesis ETLa : ltac2:(tb__ "0|8|
S5S23S1S1ScQ40M0A1M1S10G1A1M2S6S22VW;Vst;A2S24R7A1SfS1dG1S2R7R1A2S2R8R1A2A3Fi;SfS1dS10ScQ8A1M3A1S4R8R1A2S4R9R1A2A3Fl;S28VCST;VXGL;RbRbS3R9A1S3R8A1A6S2bS2fS14S8S7RcA1A2A1S9RcA1A2S11SeSeA2M4S3aG4R1S34R8A1A3S33R2S12SeSeSbG0RbA2M5S21SbG0S2RcPcA2A2A1M6A4A2F_;Fbn;SeS1fS2bS3eG5A1M7R1A2S2dR1S2cG7S2eG6Z8A2A2A2A2S1eS1dS16G3A1S3RdSdG0R2A2A2S13G3A1A3A1F_;Fz;S1G2S19S0S1bS0VJGs;S31S5S40R1A1LX;RbA2R11R10ReRdA5VC5a;R2R1A5S3cS0S3bRfRcVPosts;R11R10A2A5A3FtX;FrX;F_;F_;F_;F_;F_;F_;F_;F_;FG2;Ftp0;Fa;Frho;Frho0;FKc;FA;").
Hypothesis ETLb : ltac2:(tb__ "0|8|
S5S23S1S1ScQ40M0A1M1S10G1A1M2S6S22VW;Vst;A2S24R7A1SfS1dG1S2R7R1A2S2R8R1A2A3Fi;SfS1dS10ScQ8A1M3A1S4R8R1A2S4R9R1A2A3Fl;S28VCST;VXGL;RbRbS3R9A1S3R8A1A6S2bS2fS14S8S7RcA1A2A1S9RcA1A2S11SeSeA2M4S3aG4R1S34R8A1A3S33R2S12SeSeSbG0RbA2M5S21SbG0S2RcPcA2A2A1M6A4A2F_;Fbn;SeS1fS2bS3eG5A1M7R1A2S2dR1S2cG7S2eG6Z8A2A2A2A2S1eS1dS16G3A1S3RdSdG0R2A2A2S13G3A1A3A1F_;Fz;S1G2S19S0S1bS0VJGs;S31S5R1LX;RbA2R11R10ReRdA5VC5b;R2R1A5S3cS0S3bRfRcVPosts;R11R10A2A5A3FtX;FrX;F_;F_;F_;F_;F_;F_;F_;F_;FG2;Ftp0;Fa;Frho;Frho0;FKc;FA;").

Theorem esec_ok_chain : ltac2:(tb__ "0|2|
S5S23S1ScQ40M0A1M1S10G1A1S1dS27Vst;S26A3S1dS10S25A1VW;S15S25A1A3F_;S22VW;Vst;A2S24R6A1S36Vhi;SbG0R5A2S21SbG0S2R6PcA2A2A1A3S1S19S0S1bS0VJGsC;S5R1LX;RaR9R8R7A5VE1;R1R6A5S3cS0S3bR8R6VPosts;RaR9A2A5A3FrhoX;F_;F_;F_;F_;Ftp;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a tp HW HUS HKc HC rhoX.
  set (ua := bv_unsigned a) in *. set (L := secmapsize (bv_unsigned (rw rho 12%positive))) in *.
  apply (EG12 A Kc rho a tp _ HUS HKc HC). intros rho1 rhoY tpY SL1.
  apply (etriple_pre_pure segsA _ _ (Z.of_nat (length (aa_sec A)) + 1 < 2 ^ 20 /\ Z.of_nat (length (aa_sec A)) <= aa_Km A)).
  { intros [tr [ms md]] Hw. exact (d2_pure nW st nx A Kc rho1 a rhoY tpY tr md (proj2 Hw)). }
  intros [HRM HL9].
  assert (E1r : rw rho1 12%positive = rw rho 12%positive) by (destruct SL1 as (W1 & _); apply W1).
  assert (RD1 : forall z, Sh ua <= z < Sh ua + L / 8 -> rm rho1 (Z_to_bv 64 z) <> None) by (destruct SL1 as (_ & _ & _ & D1); exact D1).
  apply (EG3 A Kc rho1 a _ HUS HKc HRM); [rewrite E1r; exact RD1 | |].
  - rewrite E1r. fold ua L. intros rho2 rY tY SL4.
    assert (E2r : rw rho2 12%positive = rw rho 12%positive) by (destruct SL4 as (W2 & _); rewrite W2; exact E1r).
    apply (EG41a A Kc rho2 a _ HW HUS HKc). rewrite E2r. fold ua L. intros G2 rho3 rhoX3 tp3 HDB DL.
    apply (etriple_pre_pure segsA _ _ _ (fun w Hw => c5_pure nW st nx CST XGL HCST HXGL HCSTS HCSTD (fun X : AA => bumpP X) G2 A Kc rho rho1 rho2 rho3 a rhoX3 tp3 (w_tr w) (cfg_model (w_cfg w))
             (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) SL1 SL4 DL HDB (proj2 Hw))).
    intros (HK & RD & HWr & HLr & HDB3).
    exact (ETLa A Kc rho rho3 a tp G2 HUS HKc HWr HLr HK HL9 HDB3 RD rhoX3 tp3).
  - intros rY tY.
    apply (EG41b A Kc rho1 a _ HW HUS HKc). rewrite E1r. fold ua L. intros G2 rho3 rhoX3 tp3 HDB DL.
    apply (etriple_pre_pure segsA _ _ _ (fun w Hw => c5_pure nW st nx CST XGL HCST HXGL HCSTS HCSTD (fun X : AA => X) G2 A Kc rho rho1 rho1 rho3 a rhoX3 tp3 (w_tr w) (cfg_model (w_cfg w))
             (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) SL1 (slink4_refl (aa_geom A) ua L rho1 RD1) DL HDB (proj2 Hw))).
    intros (HK & RD & HWr & HLr & HDB3).
    exact (ETLb A Kc rho rho3 a tp G2 HUS HKc HWr HLr HK HL9 HDB3 RD rhoX3 tp3).
Qed.

Lemma ecls_split : ltac2:(tb__ "0|5|
S5S23S1ScQ40M0A1M1S41S1S10G1A1S1aOF_;S36S18SbG0R5A2S21SbG0S2R6PcM2A2A2A1A3S19S0S1bS0VJGsC;S5R1LX;M3R9R8R7R6A5R5R4R3A5R2A3F_;S36S17SbG0R6A2S21SbG0S2R7G2A2A2A1A3S19S0S1bS0VJGsC;G3RaR9R8R7A5R6R5R4A5R3A3M4F_;G4F_;F_;FQ;Ftp;FrhoX;FE;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a E rhoX tp Q HH HL.
  apply (etriple_pre_pure segsA _ _ (clsP true (bv_unsigned a) (secmapsize (bv_unsigned (rw rho 12%positive)))
                                     \/ clsP false (bv_unsigned a) (secmapsize (bv_unsigned (rw rho 12%positive))))).
  - intros [tr [ms md]] Hw. pose proof (proj2 Hw) as HJ. cbn [w_tr w_cfg cfg_model fst snd] in HJ.
    destruct HJ as [HJ _]. unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3.JGs in HJ. cbn zeta in HJ. destruct HJ as (_ & _ & _ & HPD & _).
    destruct HPD as (_ & _ & _ & PDI & _). destruct PDI as (_ & _ & _ & _ & PDB).
    unfold clsP. destruct PDB as [X|X]; [right; exact X | left; exact X].
  - intros [X|X]; [exact (HH X) | exact (HL X)].
Qed.
End OKE.
End SpineMallocSecE4.

(* [comment removed for export] *)
Module SpineMallocRi2.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "cons"; "true"; "bool"; "nil"; "list"; "prod"; "app"; "Some"; "option"; "false"; "pair"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "sprop"; "ss_next"; "ss_facts"; "valuation"; "ss_objs"; "ss_lenient"; "swf"; "SAlu"; "SLit"; "SVar"; "rw"; "SPBranch"; "SPNot"; "rm"; "sprop_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "la_state"; "leafA"; "sym_runA"; "axst"; "ax_X"; "entailsA"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jt.SpineMallocRi2"; "e3r"; "icc"; "r_9N_0"; "W0"; "FUEL"; "ct0N"; "r_1_0"; "r_2_1"; "r_t1N_0"; "s_bkN"; "s_inN"; "xlN"; "e3p"; "nob"; "r_t1N_1"; "cellsfN"; "r_2_0"; "r_t0N_0"; "r_zN_0"; "s_xN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR"; "cE1"; "cE2"; "GR"; "cR1"; "factsR"; "PV4"; "cR0"; "cT1"; "PV6"; "cE3"; "vK"; "O_pcm"; "cE3b"; "k_e"; "F_r0"; "F_r1"; "F_x"; "O_pccK"; "O_ri"; "PNX"; "cE3a"; "cR0a"; "fa_e"; "keepn"; "nobj"; "ri_e"; "ri_has"; "vAU"; "vFA"; "vMFA"; "vMU"; "vNF"; "vRI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "KcA"; "ulink"; "A_globals"; "Kc_ok"; "UStopLeOrPc"; "malloc_depth"; "mem_keptA"; "pre_facts"; "unwind_factsS"; "unwind_objs"; "ustop"; "@Corelib.Lists.ListDef"; "map"; "firstn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3"; "inclb"; "skel"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "eqb"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_NE"; "BC_LTU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub_id_below"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP"; "O_pcc0"; "O_st"; "E3p"; "E3r"; "F_gen"; "pc_base"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_cache_inited"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "cls_of"; "cnt_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillJ"; "JR"; "entryR"; "gh_nf"; "ph0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel"; "kchunks"; "refillA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SpineMallocR2"; "BASEF"; "BASEO"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jc.SpineMallocR3"; "O_dstc"; "O_srcc"; "e_end"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1"; "JG"; "@Stdlib.Lists.List"; "forallb"; "nth_error"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1"; "RT_m1"; "sw_s1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillTR";
"TRok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jn.SpineMallocR4"; "O_rif"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jq.SpineMallocR5"; "posts_conv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.js.SpineMallocR6"; "e16N"; "e_srcN"; "phFN"; "@Stdlib.ZArith.BinInt.Z"; "le"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillTR RefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require io.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require js.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocR1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SpineMallocR2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jc.SpineMallocR3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jn.SpineMallocR4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jq.SpineMallocR5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.js.SpineMallocR6.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition W0 : list ulink := Wcan 2.
Definition FUEL : nat := 4000%nat.
Definition e3r := Eval vm_compute in (E3r W0 UStopLe 4).
Lemma E3r_eq : ltac2:(tb__ "0|0|
S0S22S7cS29S5cZ4A3S26A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma SK3 : ltac2:(tb__ "0|1|
S0S6S7S7SeSeA2SeA2M0A1S68SdG0S6bS13S1eS26A1A1A4S68SdG0S6bS8SdS8SdS2SdS97S8SdS66S29A1S5fA3A3S96A3S2SdS79S2SdS7aS5SdA1A3A3A3A4A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XX3 : ltac2:(tb__ "0|1|
S0S6S7SeSeA2M0A1S23S26A1S5G0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF3b : ltac2:(tb__ "0|0|
S0S4S6aS8SfS8SfS65S29S5cA2S64S62A1A3S7dA3S11S1eS26A1A1A2S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NX3 : ltac2:(tb__ "0|0|
S0S4S6cS10S1eS26A1A1PdcA2S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma WR0a : ltac2:(tb__ "0|0|
S0S4S15S1eS50S26A1A1A1S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FB0 : ltac2:(tb__ "0|0|
S0S4S93SfS1dS3dA1S8SfS11S1eS26A1A1S8SfS49S4aA3A3A3S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Definition R_1__R : option (list leafA) := ltac2:(tb__ "0|0|
S21S3aS2aS2S25Z4147cS5S25A1A3S41S26A1S3A5").
Local Strategy expand [R_1__R].
Definition r_1 := Eval vm_compute in ((fun ro1__ : option (list leafA) => (match ro1__ with Some l => l | None => [] end)) R_1__R).
Definition r_1_0 := Eval vm_compute in (nth 0 r_1 (mkLeafA (cR0 e3r) RsCut)).
Definition cr1 := Eval vm_compute in (cR1 (factsR e3r) (la_state r_1_0)).
Definition r_2 := Eval vm_compute in (match sym_runA segsA FUEL [0x41704; 0x41560] cr1 true with Some l => l | None => [] end).
Definition r_2_0 := Eval vm_compute in (nth 0 r_2 (mkLeafA cr1 RsCut)).
Definition r_2_1 := Eval vm_compute in (nth 1 r_2 (mkLeafA cr1 RsCut)).
Lemma R_1 : ltac2:(tb__ "0|1|
S0SaS6S20A1M0A1S21S3aS2aS2S25Z4147cS5S25A1A3S41S26A1S3A5S9G0S2S20S2cS5S20A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_1__R <: R_1__R = Some [r_1_0]). Qed.
Lemma LN_0 : ltac2:(tb__ "0|0|
S0S4S14S1eS41S26A1A1A1SbA3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_0 : ltac2:(tb__ "0|0|
S0S4S6cS3dS10S1eS41S26A1A1A1A2S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_r1 : ltac2:(tb__ "0|0|
S0S4S15S1eS3eS3fS26A1S1fS2cA1A2A1A1S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_r1 : ltac2:(tb__ "0|5|
S0SaS7S6S7SeSeA2M0A1M1S6SfA1M2A2M3A1S84S1eS1fS2cA1M4A1S1eS3eS3fS26A1G4A2A1A2S9G3ScG1G2S2G0ScSeSeS54S5bA4S2G0ScSeSeS48S45A4S2G0ScSeSeS51S57A4S5G0A1A3A3A3S5SfA1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NX_r1 : ltac2:(tb__ "0|1|
S0S4S6dS10S1eS3eS3fS26A1S1fS2cA1M0A2A1A1S10S1eG0A1A1A2S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_2 : ltac2:(tb__ "0|1|
S0SaS6S20A1M0A1S21S3aS2aS2S25Z41704S2S25Z41560S5S25A1A3A3S3eS3fS26A1S1fS2cA1A2S3A5S9G0S2S20S36S2S20S2dS5S20A1A3A3A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma LN_1 : ltac2:(tb__ "0|0|
S0S4S14S1eS3eS3fS26A1S1fS2cA1A2A1A1SbA3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_1 : ltac2:(tb__ "0|0|
S0S4S6cS3dS10S1eS3eS3fS26A1S1fS2cA1A2A1A1A2S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Definition nob := Eval vm_compute in ((length (ss_objs (ax_S e3r)) + 2)%nat).
Definition icc := Eval vm_compute in ((length (ss_objs (ax_S e3r)) - 2)%nat).
Definition R_t0N__R : option (list leafA) := ltac2:(tb__ "0|0|
S21S3aS2aS2S25Z41570S2S25Z41584S5S25A1A3A3S1fS2dA1S3A5").
Local Strategy expand [R_t0N__R].
Definition r_t0N := Eval vm_compute in ((fun ro3__ : option (list leafA) => (match ro3__ with Some l => l | None => [] end)) R_t0N__R).
Definition r_t0N_0 := Eval vm_compute in (nth 0 r_t0N (mkLeafA (la_state r_2_1) RsCut)).
Definition ct0N := Eval vm_compute in (cT0 (la_state r_t0N_0)).
Definition R_t1N__R : option (list leafA) := ltac2:(tb__ "0|0|
S21S3aS2aS2S25Z41570S2S25Z41584S5S25A1A3A3S42S2bA1S3A5").
Local Strategy expand [R_t1N__R].
Definition r_t1N := Eval vm_compute in ((fun ro2__ : option (list leafA) => (match ro2__ with Some l => l | None => [] end)) R_t1N__R).
Definition r_t1N_0 := Eval vm_compute in (nth 0 r_t1N (mkLeafA (cT1 ct0N) RsCut)).
Definition r_t1N_1 := Eval vm_compute in (nth 1 r_t1N (mkLeafA (cT1 ct0N) RsCut)).
Definition s_inN := Eval vm_compute in (infer_sub GR (ax_S (la_state r_t0N_0)) (ax_S ct0N)).
Definition s_bkN := Eval vm_compute in (infer_sub GR (ax_S (keepn (la_state r_t1N_0) nob)) (ax_S ct0N)).
Lemma SK_tN : ltac2:(tb__ "0|1|
S0S6S7S7SeSeA2SeA2M0A1S68SdG0S6bS13S1eS2bA1A1A4S68SdG0S6bS8SdS8eS29A1S2SdS79S2SdS7aS2SdS46S2SdS4dS5SdA1A3A3A3A3A3A4A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XX_tN : ltac2:(tb__ "0|1|
S0S6S7SeSeA2M0A1S23S2bA1S5G0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_tNb : ltac2:(tb__ "0|0|
S0S4S6aS8dS29S5cA2S11S1eS2bA1A1A2S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NX_tN : ltac2:(tb__ "0|0|
S0S4S6dS10S1eS2bA1A1S4eA2S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_t1N : ltac2:(tb__ "0|0|
S0S4S15S1eS42S2bA1A1A1S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_t1N : ltac2:(tb__ "0|1|
S0SaS6S20A1M0A1S21S3aS2aS2S25Z41570S2S25Z41584S5S25A1A3A3S42S2bA1S3A5S9G0S2S20S2eS2S20S34S5S20A1A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_t1N__R <: R_t1N__R = Some [r_t1N_0; r_t1N_1]). Qed.
Lemma LN_t1N : ltac2:(tb__ "0|0|
S0S4S14S1eS42S2bA1A1A1SbA3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma OB_bN : ltac2:(tb__ "0|1|
S0S6SdA1S13S1eS1fS2eA1A1A1M0S8SdS69SdS33G0A3S2SdS90S2SdS8fS5SdA1A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_xN : ltac2:(tb__ "0|1|
S0S6SdA1S13S1eS1fS34A1A1A1M0S8SdS69SdS33G0A3S2SdS90S2SdS8fS5SdA1A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma ENT_bkN : ltac2:(tb__ "0|0|
S0S4S24S52S1fS2eA1S33A2S2bS2fA3S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_bkN : ltac2:(tb__ "0|0|
S0S4S72S2fS3dA2S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma S_bk4N : ltac2:(tb__ "0|0|
S0SeS71S2fS40A2S16S6eS18S40A1S17Z4A1A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S_bk6N : ltac2:(tb__ "0|0|
S0SeS71S2fS43A2S16S6eS18S43A1S17Z4A1A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma FB_bNb : ltac2:(tb__ "0|0|
S0S4S6aS2SfS1aS6fS16S6eS18S40A1S17Z4A1A3S91A3S5SfA1A3S11S1eS1fS2eA1A1A1A2S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FB_xNb : ltac2:(tb__ "0|0|
S0S4S6aS2SfS1bS1aS6fS16S6eS18S40A1S17Z4A1A3S91A3A1S5SfA1A3S11S1eS1fS34A1A1A1A2S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_t0N : ltac2:(tb__ "0|1|
S0SaS6S20A1M0A1S21S3aS2aS2S25Z41570S2S25Z41584S5S25A1A3A3S1fS2dA1S3A5S9G0S2S20S37S5S20A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_t0N__R <: R_t0N__R = Some [r_t0N_0]). Qed.
Lemma LN_t0N : ltac2:(tb__ "0|0|
S0S4S14S1eS1fS2dA1A1A1SbA3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_t0N : ltac2:(tb__ "0|0|
S0S4S6cS3dS10S1eS1fS2dA1A1A1A2S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_inN : ltac2:(tb__ "0|0|
S0S4S24S1fS37A1S2bS30A3S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_inN : ltac2:(tb__ "0|0|
S0S4S72S30S3dA2S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma S_in4N : ltac2:(tb__ "0|0|
S0SeS71S30S40A2S16S6eS7eS17Z10A1A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S_in6N : ltac2:(tb__ "0|0|
S0SeS71S30S43A2S9dA3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Definition xlN := Eval vm_compute in (keepn (la_state r_t1N_1) nob).
Definition R_9N__R : option (list leafA) := ltac2:(tb__ "0|0|
S21S3aS2aS2S25Z40e5cS5S25A1A3S31S3A5").
Local Strategy expand [R_9N__R].
Definition r_9N := Eval vm_compute in ((fun ro4__ : option (list leafA) => (match ro4__ with Some l => l | None => [] end)) R_9N__R).
Definition r_9N_0 := Eval vm_compute in (nth 0 r_9N (mkLeafA xlN RsCut)).
Definition cellsfN := Eval vm_compute in (ob_cells (last (ss_objs (ax_S (cE1 (la_state r_9N_0) icc))) O_ri)).
Definition x3N := Eval vm_compute in (cE3 (cE2 (cE1 (la_state r_9N_0) icc))).
Definition r_zN := Eval vm_compute in (match sym_runA segsA FUEL [0x3c614] x3N true with Some l => l | None => [] end).
Definition r_zN_0 := Eval vm_compute in (nth 0 r_zN (mkLeafA x3N RsCut)).
Lemma R_9N : ltac2:(tb__ "0|1|
S0SaS6S20A1M0A1S21S3aS2aS2S25Z40e5cS5S25A1A3S31S3A5S9G0S2S20S28S5S20A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_9N__R <: R_9N__R = Some [r_9N_0]). Qed.
Lemma LN_9N : ltac2:(tb__ "0|0|
S0S4S14S1eS31A1A1SbA3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_9N : ltac2:(tb__ "0|0|
S0S4S6cS3dS10S1eS31A1A1A2S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_x1N : ltac2:(tb__ "0|0|
S0S4S15S1eS3bS1fS28A1S27A2A1A1S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_x1N : ltac2:(tb__ "0|5|
S0SaS7S6S7SeSeA2M0A1M1S6SfA1M2A2M3A1S84S1eS1fS28A1M4A1S1eS3bG4S27A2A1A2S9G3ScG1G2S2G0ScSeSeS48S45A4S5G0A1A3S5SfA1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NX_x1N : ltac2:(tb__ "0|1|
S0S4S6dS10S1eS3bS1fS28A1M0S27A2A1A1S10S1eG0A1A1A2S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XX_1N : ltac2:(tb__ "0|1|
S0S6S7SeSeA2M0A1S23S3bS1fS28A1S27A2A1S5G0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma IC_1N : ltac2:(tb__ "0|0|
S0SaSdA1S94SdS13S1eS3bS1fS28A1S27A2A1A1S27A3S9SdS4cA2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_1N : ltac2:(tb__ "0|2|
S0S6SdA1S13S1eS3bS1fS28A1S27A2M0A1A1M1S8SdS69SdS95S53G0A1U2A2G1A3S2SdS46S2SdS9aS35A1S5SdA1A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_1N : ltac2:(tb__ "0|0|
S0S4S55S35S9cS58S56S59A5S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SK_2N : ltac2:(tb__ "0|1|
S0S6S7S7SeSeA2SeA2M0A1S68SdG0S6bS13S1eS3cS3bS1fS28A1S27A2A1A1A1A4S68SdG0S6bS8SdS8eS29A1S2SdS79S2SdS7aS5SdA1A3A3A3A4A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XX_2N : ltac2:(tb__ "0|1|
S0S6S7SeSeA2M0A1S23S3cS3bS1fS28A1S27A2A1A1S5G0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_2Nb : ltac2:(tb__ "0|0|
S0S4S6aS8dS29S5cA2S11S1eS3cS3bS1fS28A1S27A2A1A1A1A2S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_3aN : ltac2:(tb__ "0|0|
S0S4S15S1eS4fS3cS3bS1fS28A1S27A2A1A1A1A1S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_3bN : ltac2:(tb__ "0|0|
S0S4S15S1eS47S3cS3bS1fS28A1S27A2A1A1A1A1S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FB_3N : ltac2:(tb__ "0|1|
S0S4S93SfS1dS10S1eS47S3cS3bS1fS28A1S27A2A1A1A1M0A1A1S8SfS4bS11G0A1A3A3S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_zN : ltac2:(tb__ "0|1|
S0SaS6S20A1M0A1S21S3aS2aS2S25Z3c614S5S25A1A3S44S3cS3bS1fS28A1S27A2A1A1S3A5S9G0S2S20S38S5S20A1A3A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma LN_zN : ltac2:(tb__ "0|0|
S0S4S14S1eS44S3cS3bS1fS28A1S27A2A1A1A1A1SbA3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_zN : ltac2:(tb__ "0|0|
S0S4S6cS3dS10S1eS44S3cS3bS1fS28A1S27A2A1A1A1A1A2S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Definition e3p := Eval vm_compute in (E3p W0 UStopLe 4).
Lemma E3p_eq : ltac2:(tb__ "0|0|
S0S22S7bS29S5cZ4A3S32A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Definition s_xN := Eval vm_compute in (s_exit (la_state r_zN_0) e3p).
Lemma ENT_xN : ltac2:(tb__ "0|0|
S0S4S24S1fS38A1S32S39A3S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SX_xN : sx_okb s_xN = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma S149_xN : wsub_get s_xN 149%positive = vK.
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S159_xN : wsub_get s_xN 159%positive = vCHX.
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.

Lemma HW0 : ltac2:(tb__ "0|0|
S0S67S5cS61A3S0S6S5eA1S29S5S5eA1A3F_;"). Proof. intros E; discriminate E. Qed.
Definition pop_N A Kc rb tp0 md0 TR KIT HKc rho HE ph PH0 faP HSRC HKF HNFP HFILLR HIDS HCACHE :=
  pop_all A Kc rb tp0 md0 TR KIT HKc W0 UStopLe rho HW0 HE ph PH0 faP HSRC HKF HNFP HFILLR HIDS HCACHE FUEL ct0N r_t1N_0 r_t1N_1 nob s_bkN
    SK_tN XX_tN (inclb_incl _ _ XF_tNb) NX_tN W_t1N R_t1N LN_t1N OB_bN OB_xN ENT_bkN SID_bkN S_bk4N S_bk6N (In_of_inclb _ _ FB_bNb) (In_of_inclb _ _ FB_xNb)
    (la_state r_2_1) r_t0N_0 s_inN e_srcN R_t0N LN_t0N NX_t0N ENT_inN SID_inN S_in4N S_in6N.
Definition entry_i := refill_entry 2 UStopLe e3r SK3 XX3 (inclb_incl _ _ XF3b) NX3 WR0a FB0.
Definition prefix_i A Kc rb tp0 md0 TR KIT HKc := refill_prefix A Kc rb tp0 md0 TR KIT HKc FUEL e3r r_1_0 r_2_0 r_2_1 R_1 LN_0 NX_0 W_r1 D_r1 NX_r1 R_2 LN_1 NX_1.
Definition exit_N A Kc rb tp0 md0 TR KIT HKc rho HE phX PHX HFILLX Hini HRIv HLEN HIDC :=
  exit_steps A Kc rb tp0 md0 TR KIT HKc W0 UStopLe rho HW0 HE phX PHX HFILLX Hini e16N vMFA vAU vMU HRIv HLEN HIDC FUEL xlN r_9N_0 r_zN_0 icc cellsfN
    R_9N LN_9N NX_9N W_x1N D_x1N NX_x1N XX_1N IC_1N OB_1N RI_1N SK_2N XX_2N (inclb_incl _ _ XF_2Nb) W_3aN W_3bN FB_3N R_zN LN_zN NX_zN.
Definition back_N CST XGL PFam HPF A Kc rb tp0 md0 TR KIT rho HW HE phF HREB HMK HLEN HPOP :=
  refill_back CST XGL PFam HPF A Kc rb tp0 md0 TR KIT W0 UStopLe rho HW HE phF HREB HMK HLEN e3p (la_state r_zN_0) s_xN ENT_xN SX_xN S149_xN S159_xN HPOP.
Lemma FJ_Nb : ltac2:(tb__ "0|0|
S0S4S6aS2SfS1bS1aS70S5aS45A3A1S5SfA1A3S11S1eS1fS2dA1A1A1A2S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.

Theorem refill_N_i : ltac2:(tb__ "0|5|
S6S7S25S25A2A1M0G0S7fS5dS6S7S22S86A2A1F_;F_;S9bR3R2R1A3S22S22S0S22R2S26A3S0S22R2S32A3S7fS5dS12S6S74Q40M1A1A1M2S77S77OF_;F_;S99R4R1A2S60R5A1S0S4S80R7A1S3A3S0S25S82R8S73G1S19R6PcM3A2A2A2Z0A3S85S3aS83R7R6RfR9R8A2A5S77S12S75S88RcR2R9R1S29S5cRaA7S9fS8bS81S73G1S19R3G3A2A2A1A1S89RdR3A2A2S12G2S6S76A1S75S87R12R11R8RfR7S9eS8bS81S73G1S19R8G3A2A2A1A1A1R4R3R2R1AaS1S98S3aS8cR13S81S73G1S19R9G3A2A2A1A2M4R5R4R2A5S63R1bR1aR13G4S1cR9A1S1cR5A1A6A2F_;Fmd;Ftr;Ftp';Fr;F_;FHE;Fmd0;Frb;S7fS12G2S12RbS78S3aS92S29S5cR4ReR3A5R12R1R2A5S85S3aS83R3R2R15R4ReA2A5A2FrX;Ftp';Frho';FA';S12S75S12S88RfR3RcR2S29S5cRdA7RcS78S3aS87R10RfR4RdR3S8aA6S1fS36A1R2RdA5R7A2F_;Fr';Fmd0;Frb;S12RaS78S3aS92S29S5cReRdRcA5R12R1RbA5R5A2FrhoE;F_;F_;F_;TQ;F_;F_;FHKc;FKIT;FTR;Ftp;Frho;FKc;FA;F_;F_;FE3P;FE3;FHPF;FPFam;FXGL;FCST;").
Proof.
  intros CST XGL PFam HPF E3 E3P -> ->.
  apply (refill_N CST XGL PFam W0 UStopLe e3r e3p (la_state r_2_0) (la_state r_2_1) xlN (la_state r_zN_0) (In_of_inclb _ _ FJ_Nb)).
  - intros A Kc rho rhoE tp w Hini Hcnt Hw. exact (entry_i A Kc rho rhoE tp w HW0 Hini Hcnt Hw).
  - intros A Kc rb tp0 md0 TR KIT HKc rho r tp Q HE. exact (prefix_i A Kc rb tp0 md0 TR KIT HKc W0 UStopLe rho r tp Q HE).
  - intros A Kc rb tp0 md0 TR KIT HKc rho HE ph PH0 faP. exact (pop_N A Kc rb tp0 md0 TR KIT HKc rho HE ph PH0 faP).
  - intros A Kc rb tp0 md0 TR KIT HKc rho HE phX. exact (exit_N A Kc rb tp0 md0 TR KIT HKc rho HE phX).
  - intros A Kc rb tp0 md0 TR KIT rho HE phF. exact (back_N CST XGL PFam HPF A Kc rb tp0 md0 TR KIT rho HW0 HE phF).
Qed.
End SpineMallocRi2.

(* [comment removed for export] *)
Module SpineCallocR12.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "and"; "eq"; "not"; "iff"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "mul"; "of_nat"; "lt"; "div"; "modulo"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "la_state"; "leafA"; "sym_runA"; "@Corelib.Init.Datatypes"; "bool"; "cons"; "true"; "length"; "list"; "nil"; "Some"; "option"; "false"; "pair"; "prod"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SAlu"; "SLit"; "eval"; "ss_next"; "sv"; "sprop"; "valuation"; "ss_facts"; "ss_lenient"; "SMd"; "SPNot"; "SVar"; "holds"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CRefillJ"; "gh_new"; "JR"; "entryR"; "ghosts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "cs_free_array"; "cs_mapped_free_array"; "cs_allocated_user"; "cs_mapped_user"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_AND"; "ALU_SLL"; "ALU_SUB"; "M_DIVU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSR"; "vNEW"; "GR"; "F_new"; "cD"; "vAU"; "vMFA"; "vMU"; "vNF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jt.SpineCallocR12"; "F_geu"; "need_e"; "new_e"; "facap_okb"; "rup_e"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@Stdlib.Lists.List"; "In"; "forallb"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP"; "V_SIZE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "Size"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCredit"; "CLS30"; "FACAP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel"; "kchunks"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.SpineCallocR2"; "rigids"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA EntailA CFGA GlueA SummaryA LedgerA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Inv InvLaws PrimCredit PrimCreditLaws.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCredit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCreditLaws.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillModel RefillBits.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillTR CRefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require im.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require je.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jg.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require js.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineCallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillBits OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CRefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.im.CRefillJP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineCallocR1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.SpineCallocR2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.je.SpineCallocR3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j9.SpineCallocR7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jg.SpineCallocR8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jg.SpineCallocR9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jk.SpineCallocR10 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.js.SpineCallocR11.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation segs := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree.segsA.

Definition new_e : sv := ltac2:(tb__ "0|0|
S25S37S1cS36S1cS33S3fS1dZ40000A1A3S3dA3S27S4eA1A3").
Definition need_e : sv := ltac2:(tb__ "0|0|
S1cS35S1cS33S40S39A3S1dZ2A1A3").
Definition F_geu : sprop := SPBranch BC_GEU vMFA need_e.
Definition rup_e : sv := ltac2:(tb__ "0|0|
S1cS34S1cS33S42S1dZ3ffffA1A3S1dZfffffffffffc0000A1A3").

Definition facap_okb (c : Z) : bool := FACAP c <=? 536608768.
Lemma facap_okb_all : ltac2:(tb__ "0|0|
S2S11S49S0S44S50A3S13A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma facap_room : ltac2:(tb__ "0|0|
S0S1S5Z1R1A2S5R1Z1eA2A2S5S51R2A1Z1ffc0000A2F_;Fc;").
Proof. intros c Hc. pose proof (proj1 (forallb_forall _ _) facap_okb_all c (proj2 (In_CLS30 c) Hc)) as H. apply Z.leb_le in H. exact H. Qed.

Section VALS.
Variables (A : AA) (rb r : valuation).
Hypothesis CF : cfacts A rb.
Hypothesis PF : popfacts A rb.
Hypothesis RG : ltac2:(tb__ "0|0|
S53VA;Vrb;Vr;A3").
Hypothesis GH : ltac2:(tb__ "0|0|
S2dVA;Vrb;Vr;A3").
Let nv : Z := bv_unsigned (rw rb 12%positive).
Let c : Z := cls_of nv.
Let cs : class_state := cst_of A nv.

Lemma new_nums : ltac2:(tb__ "0|5|
S4fVc;A1S0S8S14S0S2fVcs;A1A2A1S0S31Vcs;A1S0S32Vcs;A1S0S30Vcs;A1S0S2aVA;Vrb;A2S0S1S1S5Z20R6A2S5R6Z10000A2A2S1S1S5Z0M0R4A2S5R4R3A2A2S1S5R3Zdffc0000A2S1S1S5Z4M1R1A2S5R1Z2001A2A2S1S5S52Vc;A1R1A2S1S5S6R4S7R1R6A2A2M2S6R3Z40000M3A2M4A2S1S9G4S6G2R6A2A2S1S5G0R5A2S1S5S7G1R5A2R2A2S1S5R2Z1ffc0000A2S1S2S0SbR2G3A2G0A3S2S0R1SaScG4R4A2R6A2A3A2A2A2A2A2A2A2A2A2A2A2Tnew;Tmfa;Tmu;Tau;Tnf;TS;").
Proof.
  intros S nf au mu mfa new.
  destruct (pop_nums A rb CF PF) as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8). cbn zeta in N1, N2, N3, N4, N5, N6, N7, N8. fold nv c cs in N1, N2, N3, N4, N5, N6, N7, N8. fold S nf au mu in N1, N2, N3, N4, N5, N6, N7, N8.
  unfold cfacts in CF. cbn zeta in CF. fold nv c cs in CF. destruct CF as ((_ & C1 & _) & (_ & _ & K3) & _ & (MF0 & MF1) & (_ & FC0 & _) & _). fold S in K3. fold nf mfa in MF0, MF1, FC0.
  pose proof (facap_room c C1) as FR.
  assert (EN : new = (mu + 262144 - au) / S) by (unfold new, gh_new, kUserMapSize; fold nv c cs; reflexivity).
  pose proof (Z.div_mod (mu + 262144 - au) S ltac:(clear -N1; lia)) as DM. pose proof (Z.mod_pos_bound (mu + 262144 - au) S ltac:(clear -N1; lia)) as MB.
  rewrite <- EN in DM. clearbody new.
  assert (Q1 : 262144 - S < new * S <= 262144 + S) by (clear -DM MB N4 N6 N1; nia).
  assert (Q2 : 4 <= new <= 8193) by (clear -Q1 N1; nia).
  assert (Q3 : kchunks c <= new) by (clear -Q1 N1 N2 K3; nia).
  split; [exact N1|]. split; [exact N4|]. split; [exact N5|]. split; [exact Q2|]. split; [exact Q3|].
  split; [clear -DM MB; nia|]. split; [clear -DM MB; nia|]. split; [clear -N3; lia|]. split; [clear -MF1; lia|]. split; [clear -FC0 FR; lia|]. split; [exact MF0 | exact EN].
Qed.

Lemma new_val : ltac2:(tb__ "0|0|
S2S46Q40A1S1eVr;S43A2S1eVr;S39A2A3").
Proof.
  destruct new_nums as (N1 & N2 & N3 & N4 & _ & _ & _ & _ & _ & _ & _ & EN). cbn zeta in N1, N2, N3, N4, EN. fold nv c cs in N1, N2, N3, N4, EN.
  destruct RG as (_ & E148 & _). fold nv c in E148.
  destruct GH as (_ & _ & _ & Q223 & Q224 & _ & _ & _ & Q228 & _). fold nv c cs in Q223, Q224.
  unfold new_e, vMU, vAU, vNEW, V_SIZE. cbn [eval]. apply bv_eq. rewrite divu_val by (rewrite E148, u64_lit; clear -N1; lia).
  rewrite sub_val, add_val, E148, Q223, Q224, Q228, !u64_lit by (clear -N1 N2 N3 N4; lia).
  rewrite (Z.mod_small (cs_mapped_user cs + 262144)) by (clear -N2 N3; lia). rewrite Z.mod_small by (clear -N2 N3; lia). symmetry. exact EN.
Qed.

Lemma F_new_hold : Forall (holds r) F_new.
Proof.
  destruct new_nums as (_ & _ & _ & N4 & _ & _ & _ & N8 & N9 & N10 & N11 & _). cbn zeta in N4, N8, N9, N10, N11. fold nv c cs in N4, N8, N9, N10, N11.
  destruct GH as (_ & _ & Q222 & _ & _ & _ & _ & _ & Q228 & _). fold nv c cs in Q222.
  unfold F_new. repeat apply Forall_cons; try apply Forall_nil; cbn [holds]; unfold vNEW, vMFA; cbn [eval]; rewrite ?Q222, ?Q228, ?u64_lit by (clear -N4 N8 N9 N10; lia).
  - clear -N4; lia.
  - clear -N4; lia.
  - exact N10.
  - split; [clear; lia | change (2 ^ 18) with 262144; exact N11].
Qed.

Lemma need_val : ltac2:(tb__ "0|0|
S2S0S47Q40S1eVr;S42A2A2S7Z4S6S8S14S0S2fVcs;A1A2A1S2aVA;Vrb;A2A2A2A3").
Proof.
  destruct new_nums as (_ & _ & _ & N4 & _ & _ & _ & N8 & N9 & N10 & _). cbn zeta in N4, N8, N9, N10. fold nv c cs in N4, N8, N9, N10.
  destruct GH as (_ & Q221 & _ & _ & _ & _ & _ & _ & Q228 & _). unfold gh_nf in Q221. fold nv c cs in Q221.
  unfold need_e, vNF, vNEW. cbn [eval]. rewrite sll_val, add_val, Q221, Q228, !u64_lit by (clear -N4 N8 N9 N10; lia).
  change (2 mod 64) with 2. rewrite Z.shiftl_mul_pow2 by (clear; lia). rewrite (Z.mod_small (_ + _)) by (clear -N4 N8 N9 N10; lia).
  rewrite Z.mod_small by (clear -N4 N8 N9 N10; lia). clear; lia.
Qed.

Lemma geu_iff : ltac2:(tb__ "0|0|
S4S28Vr;S41A2S3S9S30Vcs;A1S7Z4S6S8S14S0S2fVcs;A1A2A1S2aVA;Vrb;A2A2A2A2A1A2").
Proof.
  destruct new_nums as (_ & _ & _ & _ & _ & _ & _ & N8 & N9 & N10 & _). cbn zeta in N8, N9, N10. fold nv c cs in N8, N9, N10.
  destruct GH as (_ & _ & Q222 & _). fold nv c cs in Q222.
  unfold F_geu. cbn [holds]. unfold branch_taken, bv_ltu. rewrite need_val. unfold vMFA. cbn [eval]. rewrite Q222, u64_lit by (clear -N8 N9 N10; lia).
  rewrite negb_true_iff, Z.ltb_ge. clear; lia.
Qed.

Lemma rup_val : ltac2:(tb__ "0|0|
S9S30Vcs;A1S7Z4S6S8S14S0S2fVcs;A1A2A1S2aVA;Vrb;A2A2A2A2S2S46Q40A1S1eVr;S45A2S1eVr;S1cS33S3eS1dZ40000A1A3A2A3F_;").
Proof.
  intros HLT. pose proof need_val as NV.
  destruct new_nums as (_ & _ & _ & N4 & _ & _ & _ & N8 & N9 & N10 & N11 & _). cbn zeta in N4, N8, N9, N10, N11. fold nv c cs in N4, N8, N9, N10, N11.
  destruct GH as (_ & _ & Q222 & _). fold nv c cs in Q222.
  set (need := 4 * (Z.of_nat (length (cs_free_array cs)) + gh_new A rb)) in *. set (mfa := cs_mapped_free_array cs) in *.
  unfold rup_e. cbn [eval]. apply bv_eq. rewrite and_val, !add_val, NV. unfold vMFA. cbn [eval]. rewrite Q222.
  replace (bv_unsigned (Z_to_bv 64 18446744073709289472)) with 18446744073709289472 by reflexivity. rewrite !u64_lit by (clear -N9 N10; lia).
  rewrite (Z.mod_small (need + 262143)) by (unfold need; clear -N4 N8 N9 N10; lia).
  rewrite land_m18_up by (unfold need; clear -N4 N8 N9 N10; lia).
  rewrite (Z.mod_small (mfa + 262144)) by (clear -N9 N10 N8; lia).
  destruct (proj1 (Z.mod_divide mfa 262144 ltac:(clear; lia)) N11) as [q Hq].
  assert (E : (need + 262143) / 262144 = q + 1).
  { symmetry. apply Z.div_unique with (need + 262143 - (q + 1) * 262144); [left; unfold need in *; clear -HLT Hq N4 N9; lia | clear; lia]. }
  rewrite E, Hq. clear; lia.
Qed.
End VALS.

Section POPMID.
Variables (A : AA) (Kc : KcA) (rb : valuation) (tp0 : list word) (md0 : Model).
Variable TR : assn -> assn -> Prop.
Hypothesis KIT : TRok Kc TR.
Hypothesis HKc : Kc_ok Kc.
Variables (W : list ulink) (st : ustop) (rho : valuation).
Hypothesis HE : ltac2:(tb__ "0|0|
S2cVA;Vrb;Vtp0;Vmd0;VW;Vst;Vrho;A7").
Hypothesis PF : popfacts A rb.
Notation JRp := (JR A Kc rb tp0 md0).
Let nv : Z := bv_unsigned (rw rb 12%positive).
Let cs : class_state := cst_of A nv.
Variable ph : phase.

Variable F : nat.
Variables (E3 RU : axst) (LD LF0 LFm : leafA).
Let FR : list sprop := factsR E3.
Let CD : axst := ltac2:(tb__ "0|0|
S3cVFR;SeVLD;A1A2").
Hypothesis R_d : ltac2:(tb__ "0|1|
S2S18S15SfA1M0A1S10S2eVF;S12S0Z41884S16S0A1A3VRU;S13A5S17G0S12SfVLD;S16SfA1A3A2A3").
Hypothesis LN_u : ltac2:(tb__ "0|0|
S2S11S24SdVRU;A1A1S19A3").
Hypothesis NX_u : ltac2:(tb__ "0|0|
S2S11S4aS3aS1fSdVRU;A1A1A2S13A3").
Hypothesis W_d : ltac2:(tb__ "0|0|
S2S11S29SdVCD;A1A1S13A3").
Hypothesis D_d : ltac2:(tb__ "0|4|
S2S18S1bS15S1bS20S20A2M0A1M1S15S21A1M2A2M3A1S4dSdSeVLD;A1A1SdVCD;A1A2S17G3S1aG1G2S12G0S1aS20S20S43S39A4S16G0A1A3S3bA4A2A3").
Hypothesis NX_d : ltac2:(tb__ "0|0|
S2S11S4bS1fSdVCD;A1A1S1fSdSeVLD;A1A1A1A2S13A3").
Hypothesis R_f : ltac2:(tb__ "0|1|
S2S18S15SfA1M0A1S10S2eVF;S12S0Z3f404S12S0Z418c0S16S0A1A3A3VCD;S13A5S17G0S12SfVLF0;S12SfVLFm;S16SfA1A3A3A2A3").
Hypothesis LN_d : ltac2:(tb__ "0|0|
S2S11S24SdVCD;A1A1S19A3").
Hypothesis NXr_d : ltac2:(tb__ "0|0|
S2S11S4aS3aS1fSdVCD;A1A1A2S13A3").
Hypothesis F0_in : ltac2:(tb__ "0|0|
S48S21S41S23SdSeVLF0;A1A1A1A3").
Hypothesis Fm_in : ltac2:(tb__ "0|0|
S48S21S26S41A1S23SdSeVLFm;A1A1A1A3").

Theorem populate_mid : ltac2:(tb__ "0|2|
S22S15S46Q40A1A1S4cS3S9S30Vcs;A1S7Z4S6S8S14S0S2fVcs;A1A2A1S2aVA;Vrb;A2A2A2A2M0A1S22VTR;S38S2eS2bVA;VKc;Vrb;Vtp0;Vmd0;Vph;A6M1SeVLF0;A1R1R4A5R3A2Fr';F_;G0S22VTR;S38S2eG1SeVLFm;A1R1R5A5R4A2Fr';F_;VTR;S38S2eG1VRU;R5R4A5R3A2F_;F_;FQ;Ftp;Fr;").
Proof.
  intros r tp Q H0 Hm.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF.
  apply (jr_run A Kc rb tp0 md0 TR KIT HKc F [0x41884] RU [LD] ph r tp Q R_d LN_u NX_u).
  intros L r1 [<-|[]] _.
  apply (jr_restate A Kc rb tp0 md0 TR KIT (la_state LD) (ax_S CD) _ _ ph r1 tp Q W_d D_d NX_d).
  { intros tr md (HFz & HGh & _) _. pose proof (entry_rigids _ _ _ _ _ _ _ _ HE HFz) as RG. split.
    - unfold diffs_ok. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]. exact (new_val A rb r1 CF PF RG HGh).
    - exact (F_new_hold A rb r1 CF PF HGh). }
  change (ax_setS (la_state LD) (ax_S CD)) with CD.
  apply (jr_run A Kc rb tp0 md0 TR KIT HKc F [0x3f404; 0x418c0] CD [LF0; LFm] ph r1 tp Q R_f LN_d NXr_d).
  intros L r2 [<-|[<-|[]]] _.
  - apply (tr_facts Kc TR KIT). intros HF. pose proof (proj1 (Forall_forall _ _) HF _ F0_in) as BF.
    apply (tr_pure Kc TR KIT (~ (cs_mapped_free_array cs < 4 * (Z.of_nat (length (cs_free_array cs)) + gh_new A rb)))).
    { intros w [_ (HFz & HGh & _)]. exact (proj1 (geu_iff A rb r2 CF PF HGh) BF). }
    intros X. exact (H0 X r2).
  - apply (tr_facts Kc TR KIT). intros HF. pose proof (proj1 (Forall_forall _ _) HF _ Fm_in) as BF. cbn [holds] in BF.
    apply (tr_pure Kc TR KIT (cs_mapped_free_array cs < 4 * (Z.of_nat (length (cs_free_array cs)) + gh_new A rb))).
    { intros w [_ (HFz & HGh & _)].
      destruct (Z_lt_dec (cs_mapped_free_array cs) (4 * (Z.of_nat (length (cs_free_array cs)) + gh_new A rb))) as [X|X]; [exact X|].
      exfalso. apply BF. exact (proj2 (geu_iff A rb r2 CF PF HGh) X). }
    intros X. exact (Hm X r2).
Qed.
End POPMID.
End SpineCallocR12.

