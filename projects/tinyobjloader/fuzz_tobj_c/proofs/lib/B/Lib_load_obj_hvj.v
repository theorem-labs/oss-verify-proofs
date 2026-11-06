(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "cell"; "sobj"; "SPUle"; "SLit"; "SVar"; "c_off"; "ob_base"; "ob_lo"; "mkObj"; "ob_cells"; "ob_dflt"; "ob_hi"; "ss_pc"; "sv_eqb"; "SAlu"; "c_width"; "mkCell"; "mkSS"; "sprop_below"; "ss_facts"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_next"; "ss_objs"; "ss_regs"; "ss_resv"; "sstate"; "swf"; "@Corelib.Init.Datatypes"; "bool"; "cons"; "false"; "true"; "list"; "nil"; "andb"; "app"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_setS"; "axwf"; "entailsA"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hvj"; "K_vr"; "keep_cells"; "on_obj"; "s1V"; "s_vr"; "@Corelib.Lists.ListDef"; "map"; "@LinuxProcessSemantics.Riscv.Instr"; "aluop"; "mulop"; "ALU_ADD"; "@Stdlib.Lists.List"; "filter"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_defs"; "NP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv"; "L_vr3"; "L_vr4"; "L_vr5"; "L_vr6"; "L_vr7"; "L_vr8"; "cur0"; "cur_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loop.LOLAddr"; "c_vr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "list_set"; "@Stdlib.PArith.BinPos.Pos"; "add"; "@Stdlib.ZArith.BinInt.Z"; "eqb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CFGA GlueA SummaryA SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR TobjJAS TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.ObjZeroA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import ObjEmptyA PinA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.AddCellsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_defs Lib_load_obj_pro Lib_load_obj_pro2 Lib_load_obj_loop Lib_load_obj_disp Lib_load_obj_hv0 Lib_load_obj_hv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr LOAddr LOLAddr HVAddr.

Definition set_cell (off : Z) (v : sv) (o : sobj) : sobj := ltac2:(tb__ "0|3|
SaS8Vo;A1S9Vo;A1SdVo;A1S36S2S2S2S0S2Lx;S7R1A1S2cS1fS2L_;S49R1Voff;A2S12S7R2A1S11R2A1Vv;A3R2X1fx2Lz;S2dR2Li;S37S0S0R4Lb;La;M0Lop;M1G1S38G0Lop;M2G2S1fS2eS0R4La;Lw;Lsgn;S2dS0S2cR4Lk;Li;Ll;X0x8Lc;SbVo;A1A4ScVo;A1A5").
Definition keep_cells (f : Z -> bool) (o : sobj) : sobj := ltac2:(tb__ "0|3|
SaS8Vo;A1S9Vo;A1SdVo;A1S3aS2S2S0S1fLx;S7R1A1S2cVf;R1A1Lz;S2dS21Li;S37S0S0S21Lb;La;M0Lop;M1G1S38G0Lop;M2G2S1fS2eS0S21La;Lw;Lsgn;S2dS0S2cS21Lk;Li;Ll;X0x8Lc;SbVo;A1A3ScVo;A1A5").
Definition on_obj (b : sv) (lo : Z) (f : sobj -> sobj) (objs : list sobj) : list sobj := ltac2:(tb__ "0|0|
S36S3S3S3S1fS3L_;S25SfS8R1A1Vb;A2SfS9R1A1S5Vlo;A1A2A2Vf;R1A1R1X1fx2Lo;Vobjs;A4").
Definition s1V : sv := SAlu ALU_ADD (SVar 10) (SLit (-640)).
Definition gen_vr (L : axst) : axst := ltac2:(tb__ "0|1|
S28VL;A1S1dS19R1A1S2dS6R1A1S0S33S34N30S32S2cS21L_;A1S1aR3A1A4S23S3A1S26S1S20S1S4S5Z3A1R2A2S20S1S4R2S5Z8A1A2S20S1S4S43S44VL;A1M0A2S20S1S4G0S10S39S6P1e0A1S6P1e1A1A3A2S24S1A1A3A3A3A3S3aS1S14P2c0A1S15R4A1A3A3S23S1A1S29VL;S13SeR5A1S47S0S1bR5A1U1bR3A4S17R5A1S16R5A1S1cR5A1R2R1S48R4P1A2S18R5A1A9A2Tfacts;Tobjs;TnV;Tn;TS;").
Definition K_vr : axst := Eval vm_compute in gen_vr L_vr3.
Definition s_vr (L : axst) : wsub := ltac2:(tb__ "0|0|
S46S3cS28VL;A1S28S31A1A3").
Lemma hv_checks_join : ltac2:(tb__ "0|1|
S30S2fS1fS2aS31A1S22A3S30S2fS1fS1eS28S31A1M0A1S22A3S30S2fS2cSeG0A1S45A3S2fS1fS3bS27S27S2bR1S31S35R1A1A3LL;S20S27S3dS20S27S3eS20S27S3fS20S27S40S20S27S41S20S27S42S24S27A1A3A3A3A3A3A3A3S22A3A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

