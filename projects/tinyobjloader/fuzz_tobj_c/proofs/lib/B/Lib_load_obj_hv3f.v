(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "true"; "bool"; "cons"; "nil"; "nat"; "app"; "list"; "Some"; "length"; "option"; "prod"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "sprop"; "sobj"; "SVar"; "SPUle"; "sprop_eqb"; "sv"; "ss_facts"; "ss_next"; "ss_objs"; "DUnknown"; "SPEq"; "SPUlt"; "ob_cells"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "apply_axforms"; "AXMerge"; "AXRebase"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_lglue"; "frL"; "V_B"; "tvL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_base"; "entailsA"; "g8"; "has_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_defs"; "NP"; "g5"; "vLEN"; "vF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hvkit"; "oidx"; "extra_hv"; "robjs_chkR"; "sel_front"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bitem"; "bd_subst"; "@Stdlib.Lists.List"; "existsb"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loop"; "xLC"; "pH"; "pI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "nd_below"; "AHead"; "NDA"; "am_eqb"; "am_subst"; "fr_sub_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_armkit2"; "lines_chk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_bud"; "LAX"; "LAXK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv"; "optL'"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv3"; "brest_vr"; "objs_nl"; "sh_of"; "tv_fail"; "tv_vr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv3e"; "X_rlF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv3f"; "X_rlFb"; "X_rlFr"; "lx_chk"; "s_rlF"; "xf_tail"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loopE"; "X_latchE2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve"; "spm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "tv_sub_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF"; "V_below"; "bud_le2"; "wsub_id_on"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAG"; "tv_permb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS"; "shadow_release_stateA"; "shobj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "SHADOW_OFF"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@Stdlib.ZArith.BinInt.Z"; "pow"; "sub"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.ObjZeroA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import ObjEmptyA PinA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.AddCellsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_defs Lib_load_obj_pro Lib_load_obj_pro2 Lib_load_obj_loop Lib_load_obj_disp Lib_load_obj_lglue Lib_load_obj_bud Lib_load_obj_armkit Lib_load_obj_armkit2 Lib_load_obj_hv0 Lib_load_obj_hv Lib_load_obj_hvj Lib_load_obj_hvkit Lib_load_obj_hv3 Lib_load_obj_hv3m Lib_load_obj_hv3e Lib_load_obj_loopE.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr LOAddr LOLAddr HVAddr.

Definition xf_tail (T : axst) : list axform := ltac2:(tb__ "0|2|
S4S1bS1eS2cS50Z78A1SdZ0A1VT;A3A1S5S1bA1M0A3S8S1bA1S43S1cVT;R1A2A1S23S7S1bR2S4S1bS2fS4S6S2cS10PaA1M1SdN78A1R1A3S4S6S2cG1SdN70A1R1A3S5S6A1A3A3SaSfS16S22R1A1A1A2A2S4S1bS1dU0A1G0A3A3A3TT1;Tpre;").

Definition lx_chk (tv : list (sv * sv)) (bd : list bitem) (tvj : list (sv * sv)) (bdj : list bitem) (X L Lr Lb : axst) (s : wsub) : Prop := ltac2:(tb__ "0|a|
S1S0S8SfA1S16S22VL;A1M0A1S7SfS45VL;A1M1S4SfS58S29Z4Z12S1aS46VL;A1A1S17A5S5SfA1A3A3A3S1S0S13S24VL;A1SdS59A1A3S1S0S3S27S4SeS18S26S29A1S2bA2S4SeS11S10S29A1SdS5cS5bZ2Z3dA2Z1A2A1A2S5SeA1A3A3S14G0A1M2A2S2A3S1S0S3S3aS15G0A1M3S3cVtv;S1fVbd;S3bS35S2A2M4A4M5A2S2A3S1S0S3S2eG2Vtv;S1fS2dG1A5S2A3S1S0S3S40G2A1S2A3S1S0S23S57VL;G1P6eS5ScS33S33A2A1A4VLr;A3S1S0SbS23A1S1cVLr;S4eVLr;A1A2S9S23VLb;A2A3S1S0S38S51S28S22VLb;A1M6S22VX;A1A3Vs;A3S1S0S3S25VLb;VX;Vs;A3S2A3S1S0S3S39Vs;S28A2S2A3S1S0S3S5aS28S15G6A1M7A2S2A3S1S0S3S3aG7G5A2S2A3S1S0S3S52Vs;Vtv;Vtvj;A3S2A3S1S0S3S3fVs;S1fS1fA3S2A3S1S0S3S54S14G6A1S31Vs;Vbdj;A2Vbd;A3S2A3S1S0S3S3dS3eVs;G4A2G4A2S2A3S1S0S3S55S20Vs;A2S2A3S1S0S13S37Vs;P1ccM8A2S10G8A1A3S1S0S13S37Vs;P1d3M9A2S10G9A1A3S1S0S3S56Vtvj;S21A2S2A3S1S0S3S53G3S20A2S2A3S1S0S3S32SeS12S19S36S34A2A1G2A3S2A3S1S0S3S32SeS12S11S34S2aA2A1G2A3S2A3S0S3S32SeS12S11S2aSdZ4000000A1A2A1G2A3S2A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").

Definition X_rlFr : axst := Eval vm_compute in shadow_release_stateA X_rlF (objs_nl X_rlF) 110 [].
Definition X_rlFb : axst := Eval vm_compute in optL' (apply_axforms X_rlFr (xf_tail X_rlFr)).
Definition s_rlF : wsub := Eval vm_compute in infer_sub NP (ax_S X_rlFb) (ax_S X_latchE2).
Lemma hv3_checks_rlF : ltac2:(tb__ "0|1|
S4cS47S44S48S4S30S41Z0M0A1S4S30S42G0A1S5S30A1A3A3S4fS49S4bS4aS4dA9").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
