(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "true"; "bool"; "cons"; "Some"; "nil"; "S"; "option"; "nat"; "prod"; "list"; "app"; "fst"; "pair"; "andb"; "length"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_setS"; "ax_X"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "apply_axforms"; "AXSplit"; "AXMerge"; "AXUnbase"; "AXSelect"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "sv"; "sstate"; "cell"; "swf"; "ss_next"; "sprop"; "SVar"; "sobj"; "ss_facts"; "sv_eqb"; "SPUle"; "sprop_eqb"; "sprop_below"; "ss_objs"; "valuation"; "ob_base"; "ob_hi"; "@Corelib.Numbers.BinNums"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_land"; "s_blr"; "E_blr"; "s_landAE"; "s_landBE"; "XR_after0"; "XR_body0"; "iK"; "R_blr"; "T_blr0"; "T_blr0a"; "T_blr1"; "T_blr1a"; "cps_land"; "E_blr1"; "E_blr2"; "K0a"; "K0b"; "M_afterE"; "M_bodyE"; "XkB"; "iD"; "E_blr0"; "XR_after1"; "XR_body1"; "iC"; "rt_at"; "rt_drop"; "rt_news"; "tv_pass"; "tv_site"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_lglue"; "frL"; "tvL"; "@Stdlib.Lists.List"; "forallb"; "existsb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_defs"; "NP"; "FUEL_lo"; "find_idxb"; "idxB"; "vLEN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.ObjZeroA"; "zero_cells_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_land_chk2.BLR"; "Pre_blr"; "P_ret0"; "P_ret1"; "nd_pre"; "tvP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "of_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs"; "c1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_bud"; "z0"; "ndLE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "sv_subst"; "wsub_get"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "tv_below"; "tv_sub_eqb"; "import_tv"; "ivar_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "fr_below"; "AHead"; "am_eqb"; "am_subst"; "nd_bd"; "fr_sub_eqb"; "ndesc"; "ANone"; "nd_am"; "nd_tv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_land_chk"; "tv1"; "V_P"; "add_objs"; "add_objs_wf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_land_chk2"; "Ab0"; "Ab1"; "Rt_a0"; "Rt_b0"; "Za1_a0"; "Za1_b0"; "Za2_a0"; "Za2_b0"; "Za3_a0"; "Za3_b0"; "Za4_a0"; "Za4_b0"; "Zs1_a0"; "Zs1_b0"; "Zs2_a0"; "Zs2_b0"; "Zs3_a0"; "Zs3_b0"; "Zs4_a0"; "Zs4_b0"; "i1256_a0"; "i1256_b0"; "i480_a0"; "i480_b0"; "i880_a0"; "i880_b0"; "i96_a0"; "i96_b0"; "tvLand_a0"; "tvLand_b0"; "C10_a0"; "C10_b0"; "C11_a0"; "C11_b0"; "C12_a0"; "C12_b0"; "C13_a0"; "C13_b0"; "C9_a0"; "C9_b0"; "D1_a0"; "D1_b0"; "D2_a0"; "D2_b0"; "nulls_a0"; "nulls_b0"; "xfb"; "XF_a0"; "XF_b0"; "bdLand_a0"; "bdLand_b0"; "bd_bli"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@Corelib.Lists.ListDef"; "map"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_setX"; "ax_with_facts";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bd_subst"; "bitem"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "xrs_inclb"; "T_afterA3"; "pdescA"; "pd_okA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Lib_build_line_index_rom.BLRAddr"; "FR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_defs.LOAddr"; "FR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_land_chk2.BLRP"; "PDk_blr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loop"; "datasA"; "pH"; "vsP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_pro"; "fnodup"; "xnodup"; "vARn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve"; "c8"; "B32"; "spm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "sv_vars_all"; "wsub_dom_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_subA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVAy"; "null_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p0.ObjRetileB"; "retile_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF"; "V_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAG"; "tv_permb"; "@Stdlib.ZArith.BinInt.Z"; "opp"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs"; "kb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_exits"; "K_afterE"; "X_bodyE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "call_checkTA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia Permutation.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CFGA GlueA SummaryA SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV TobjJVAy TobjArena ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TobjJVA InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAM2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR TobjJAS TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p4.TobjJAD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import ResidualA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.ObjZeroA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import DrvGlueC ObjEmptyA PinA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code Asan_set_shadow_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Asan_set_shadow_iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.Asan_memcpy48_iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Lib_rom_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ny.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ns.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require oc.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Lib_build_line_index_rom OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Lib_build_line_index_rom_pf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_defs Lib_load_obj_pro Lib_load_obj_pro2 Lib_load_obj_loop Lib_load_obj_lglue Lib_load_obj_bud Lib_load_obj_exits Lib_load_obj_land Lib_load_obj_land_chk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p0.ObjRetileB.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Module BLR. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Lib_build_line_index_rom. End BLR.
Module BLRP. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Lib_build_line_index_rom_pf. End BLRP.
Import ScanDoubleAddr VRAddr RA.ReallocAddr LOAddr LOLAddr.

Definition tvLand_b0 : list (sv * sv) := Eval vm_compute in map (xr_subst s_landBE) tvL.
Definition nulls_b0 : list (sv * sv) := Eval vm_compute in firstn 18 tvLand_b0.
Definition bdLand_b0 : list bitem := Eval vm_compute in bd_subst s_landBE (nd_bd ndLE).

Definition Rt_b0 : sstate := Eval vm_compute in match retile_at (ax_S XR_body0) (rt_at XR_body0) rt_drop rt_news with Some S1 => S1 | None => ax_S XR_body0 end.
Definition XF_b0 : list axform := Eval vm_compute in canon_xf (ax_setS XR_body0 Rt_b0).
Definition C9_b0 : axst := Eval vm_compute in optL (apply_axforms (ax_setS XR_body0 Rt_b0) XF_b0).
Definition i96_b0 : nat := Eval vm_compute in idxB C9_b0 bA 96.
Definition D1_b0 : axst := Eval vm_compute in optL (apply_axforms C9_b0 [AXSplit i96_b0 (SLit 104)]).
Definition Za1_b0 : axst := Eval vm_compute in zs1 D1_b0 (S i96_b0) 112.
Definition Zs1_b0 : sstate := Eval vm_compute in zs2 Za1_b0 (S i96_b0) [c8 104 (SLit 0)].
Definition D2_b0 : axst := Eval vm_compute in optL (apply_axforms (ax_setS Za1_b0 Zs1_b0) [AXMerge (S i96_b0)]).
Definition C10_b0 : axst := Eval vm_compute in optL (apply_axforms D2_b0 [AXMerge i96_b0]).
Definition i480_b0 : nat := Eval vm_compute in idxB C10_b0 bA 480.
Definition Za2_b0 : axst := Eval vm_compute in zs1 C10_b0 i480_b0 488.
Definition Zs2_b0 : sstate := Eval vm_compute in zs2 Za2_b0 (S i480_b0) [c1 488 (SLit 0)].
Definition C11_b0 : axst := Eval vm_compute in optL (apply_axforms (ax_setS Za2_b0 Zs2_b0) [AXMerge i480_b0]).
Definition i1256_b0 : nat := Eval vm_compute in idxB C11_b0 bA 1256.
Definition Za3_b0 : axst := Eval vm_compute in zs1 C11_b0 i1256_b0 1264.
Definition Zs3_b0 : sstate := Eval vm_compute in zs2 Za3_b0 (S i1256_b0) [c1 1264 (SLit 0)].
Definition C12_b0 : axst := Eval vm_compute in optL (apply_axforms (ax_setS Za3_b0 Zs3_b0) [AXMerge i1256_b0]).
Definition i880_b0 : nat := Eval vm_compute in idxB C12_b0 bA 880.
Definition Za4_b0 : axst := Eval vm_compute in zs1 C12_b0 i880_b0 900.
Definition Zs4_b0 : sstate := Eval vm_compute in zs2 Za4_b0 i880_b0 [c1 885 (SLit 0)].
Definition C13_b0 : axst := Eval vm_compute in optL (apply_axforms (ax_setS Za4_b0 Zs4_b0) [AXMerge i880_b0]).

Lemma pipe_b0 : ltac2:(tb__ "0|9|
S1S0S8S1eA1M0SccS12S34A1S48S34A1S49S4aA4S5S1eS7eA2A3S1S0S3S20S7eA1S2A3S1S0S8S11A1M1S17S13S34S7eA2SabA2S5S11Sa2A2A3S1S0G1S17Sa2S4S16S18S96S1cZ68M2A1A2S6S16A1M3A3A2S5S11Sa4A2A3S1S0G1S17Sa4S4S16S18S7S96A1M4S1cZ70A1A2G3A3A2S5S11S80A2A3S1S0G0S56S12S80A1G4S4S1fSc3G2S1cZ0A1M5A2S6S1fA1M6A3A3S5S1eS88A2A3S1S0S3S20S88A1S2A3S1S0G1S17S13S80S88A2S4S16S19G4A1G3A3A2S5S11Sa6A2A3S1S0G1S17Sa6S4S16S19S96A1G3A3A2S5S11S9aA2A3S1S0G1S17S9aS4S16S18S92S1cZ1e8M7A1A2G3A3A2S5S11S82A2A3S1S0G0S56S12S82A1S7S92A1S4S1fS62G7G5A2G6A3A3S5S1eS8aA2A3S1S0S3S20S8aA1S2A3S1S0G1S17S13S82S8aA2S4S16S19S92A1G3A3A2S5S11S9cA2A3S1S0G1S17S9cS4S16S18S90S1cZ4f0M8A1A2G3A3A2S5S11S84A2A3S1S0G0S56S12S84A1S7S90A1S4S1fS62G8G5A2G6A3A3S5S1eS8cA2A3S1S0S3S20S8cA1S2A3S1S0G1S17S13S84S8cA2S4S16S19S90A1G3A3A2S5S11S9eA2A3S1S0G1S17S9eS4S16S18S94S1cZ384A1A2G3A3A2S5S11S86A2A3S1S0G0S56S12S86A1S94S4S1fS62Z375G5A2G6A3A3S5S1eS8eA2A3S1S0S3S20S8eA1S2A3S1S0G1S17S13S86S8eA2S4S16S19S94A1G3A3A2S5S11Sa0A2A3S0S11Sa0S3fA3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma add_datas_b0 : ltac2:(tb__ "0|1|
S1S0S11S79S41SbdSbfA1M0A2Sd3A3S0S3S7aS41G0A2S2A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma land_checks_b0 : ltac2:(tb__ "0|3|
S1S0S3S15S3fS41S32A3S2A3S1S0S3S67S32S51A2S2A3S1S0S3S60S51S21S12S3fA1A1M0A2S2A3S1S0S3S69S32S98S4eA3S2A3S1S0S3S71S32S4dS4dA3S2A3S1S0S3S6eS6fS32S6dSbeS2A2A2S6dS1cZ0A1M1S2A2A2S2A3S1S0S3SceScSaS1dS1dA2M2S77Sa8A3S98A2S2A3S1S0S3S4fG2ScbSa8A3S2A3S1S0S3S68G0S98A2S2A3S1S0S3S6cG0S4dA2S2A3S1S0SbSb5A1Sb4S32S70S64A1A2SadA3S0S3S4fS2eS2eS26S66S32R1A2G1A2Lx;Sb0S9S2eS61Sb1U190U36A2A4A3S2A3A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition tvLand_a0 : list (sv * sv) := Eval vm_compute in map (xr_subst s_landAE) tvL.
Definition nulls_a0 : list (sv * sv) := Eval vm_compute in firstn 18 tvLand_a0.
Definition bdLand_a0 : list bitem := Eval vm_compute in bd_subst s_landAE (nd_bd ndLE).

Definition Rt_a0 : sstate := Eval vm_compute in match retile_at (ax_S XR_after0) (rt_at XR_after0) rt_drop rt_news with Some S1 => S1 | None => ax_S XR_after0 end.
Definition XF_a0 : list axform := Eval vm_compute in canon_xf (ax_setS XR_after0 Rt_a0).
Definition C9_a0 : axst := Eval vm_compute in optL (apply_axforms (ax_setS XR_after0 Rt_a0) XF_a0).
Definition i96_a0 : nat := Eval vm_compute in idxB C9_a0 bA 96.
Definition D1_a0 : axst := Eval vm_compute in optL (apply_axforms C9_a0 [AXSplit i96_a0 (SLit 104)]).
Definition Za1_a0 : axst := Eval vm_compute in zs1 D1_a0 (S i96_a0) 112.
Definition Zs1_a0 : sstate := Eval vm_compute in zs2 Za1_a0 (S i96_a0) [c8 104 (SLit 0)].
Definition D2_a0 : axst := Eval vm_compute in optL (apply_axforms (ax_setS Za1_a0 Zs1_a0) [AXMerge (S i96_a0)]).
Definition C10_a0 : axst := Eval vm_compute in optL (apply_axforms D2_a0 [AXMerge i96_a0]).
Definition i480_a0 : nat := Eval vm_compute in idxB C10_a0 bA 480.
Definition Za2_a0 : axst := Eval vm_compute in zs1 C10_a0 i480_a0 488.
Definition Zs2_a0 : sstate := Eval vm_compute in zs2 Za2_a0 (S i480_a0) [c1 488 (SLit 0)].
Definition C11_a0 : axst := Eval vm_compute in optL (apply_axforms (ax_setS Za2_a0 Zs2_a0) [AXMerge i480_a0]).
Definition i1256_a0 : nat := Eval vm_compute in idxB C11_a0 bA 1256.
Definition Za3_a0 : axst := Eval vm_compute in zs1 C11_a0 i1256_a0 1264.
Definition Zs3_a0 : sstate := Eval vm_compute in zs2 Za3_a0 (S i1256_a0) [c1 1264 (SLit 0)].
Definition C12_a0 : axst := Eval vm_compute in optL (apply_axforms (ax_setS Za3_a0 Zs3_a0) [AXMerge i1256_a0]).
Definition i880_a0 : nat := Eval vm_compute in idxB C12_a0 bA 880.
Definition Za4_a0 : axst := Eval vm_compute in zs1 C12_a0 i880_a0 900.
Definition Zs4_a0 : sstate := Eval vm_compute in zs2 Za4_a0 i880_a0 [c1 885 (SLit 0)].
Definition C13_a0 : axst := Eval vm_compute in optL (apply_axforms (ax_setS Za4_a0 Zs4_a0) [AXMerge i880_a0]).

Lemma pipe_a0 : ltac2:(tb__ "0|9|
S1S0S8S1eA1M0SccS12S33A1S48S33A1S49S4aA4S5S1eS7dA2A3S1S0S3S20S7dA1S2A3S1S0S8S11A1M1S17S13S33S7dA2SaaA2S5S11Sa1A2A3S1S0G1S17Sa1S4S16S18S95S1cZ68M2A1A2S6S16A1M3A3A2S5S11Sa3A2A3S1S0G1S17Sa3S4S16S18S7S95A1M4S1cZ70A1A2G3A3A2S5S11S7fA2A3S1S0G0S56S12S7fA1G4S4S1fSc3G2S1cZ0A1M5A2S6S1fA1M6A3A3S5S1eS87A2A3S1S0S3S20S87A1S2A3S1S0G1S17S13S7fS87A2S4S16S19G4A1G3A3A2S5S11Sa5A2A3S1S0G1S17Sa5S4S16S19S95A1G3A3A2S5S11S99A2A3S1S0G1S17S99S4S16S18S91S1cZ1e8M7A1A2G3A3A2S5S11S81A2A3S1S0G0S56S12S81A1S7S91A1S4S1fS62G7G5A2G6A3A3S5S1eS89A2A3S1S0S3S20S89A1S2A3S1S0G1S17S13S81S89A2S4S16S19S91A1G3A3A2S5S11S9bA2A3S1S0G1S17S9bS4S16S18S8fS1cZ4f0M8A1A2G3A3A2S5S11S83A2A3S1S0G0S56S12S83A1S7S8fA1S4S1fS62G8G5A2G6A3A3S5S1eS8bA2A3S1S0S3S20S8bA1S2A3S1S0G1S17S13S83S8bA2S4S16S19S8fA1G3A3A2S5S11S9dA2A3S1S0G1S17S9dS4S16S18S93S1cZ384A1A2G3A3A2S5S11S85A2A3S1S0G0S56S12S85A1S93S4S1fS62Z375G5A2G6A3A3S5S1eS8dA2A3S1S0S3S20S8dA1S2A3S1S0G1S17S13S85S8dA2S4S16S19S93A1G3A3A2S5S11S9fA2A3S0S11S9fS3eA3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma add_datas_a0 : ltac2:(tb__ "0|1|
S1S0S11S79S40SbdSbfA1M0A2Sd2A3S0S3S7aS40G0A2S2A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma land_checks_a0 : ltac2:(tb__ "0|3|
S1S0S3S15S3eS40S31A3S2A3S1S0S3S67S31S51A2S2A3S1S0S3S60S51S21S12S3eA1A1M0A2S2A3S1S0S3S69S31S97S4eA3S2A3S1S0S3S71S31S4dS4dA3S2A3S1S0S3S6eS6fS31S6dSbeS2A2A2S6dS1cZ0A1M1S2A2A2S2A3S1S0S3SceScSaS1dS1dA2M2S77Sa7A3S97A2S2A3S1S0S3S4fG2ScbSa7A3S2A3S1S0S3S68G0S97A2S2A3S1S0S3S6cG0S4dA2S2A3S1S0SbSb5A1Sb4S31S70S64A1A2SacA3S0S3S4fS2eS2eS26S66S31R1A2G1A2Lx;Sb0S9S2eS61Sb1U190U36A2A4A3S2A3A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition xfb (T : axst) : list axform := ltac2:(tb__ "0|3|
S4S16S1aU1M0SbaA2S4S16S1bS4S9G0S4S9U0M1Sb1U2M2Sd0S10S24S2aS12VT;A1A1A2G2A2A2A3A3A1S4S16S19G1A1S6S16A1A3A3A3").
Definition Ab1 : axst := Eval vm_compute in optL (apply_axforms T_blr1a (xfb T_blr1a)).
Definition Ab0 : axst := Eval vm_compute in optL (apply_axforms T_blr0a (xfb T_blr0a)).
Lemma back_checks : ltac2:(tb__ "0|9|
S1S0S8S11A1M0S17S3aSa9S3aA1A2S5S11S7cA2A3S1S0S3Sb6Sc1S14S7cA1M1A1M2G1A2S2A3S1S0S3S4fS22S29S21S12S7cA1M3A1A1Sc0S25G3A1A1M4A3S2A3S1S0S11Sb3Sb2S7cG2A2G4A2S39A3S1S0G0S17S38Sa9S38A1A2S5S11S7bA2A3S1S0S3Sb6Sc1S14S7bA1M5A1M6G5A2S2A3S1S0S3S4fS22S29S21S12S7bA1M7A1A1Sc0S25G7A1A1M8A3S2A3S0S11Sb3Sb2S7bG6A2G8A2S37A3A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition bd_bli : list bitem := Eval vm_compute in bd_subst s_blr (nd_bd BLR.nd_pre).
Lemma site_checks : ltac2:(tb__ "0|1c|
S1S0S3Sb6S42S14S30A1A2S2A3S1S0S8SbS24A1M0A1ScaS30S57S2fA3S5G0S36A2A3S1S0S3Sc9S30S57S2fS36Sb0SaSaS11S72A2M1S2bS2bOF_;F_;M2A2M3S11G3SdS11S72SdG1G2R1A3A3Ld;SbcA4A5S2A3S1S0S3Sd4S51S2fA2S2A3S1S0S3Sc7S2fSafA2S2A3S1S0S3S60S51S21S12S30A1A1M4A2S2A3S1S0S3S69S2fS4bS75S5aA1A3S2A3S1S0S3S6eS6fS2fS74S5aA1A2S73A2S2A3S1S0S3S4fSaSb8G2A2M5G5Sb9S57SafS2fG4SdSb8G2R1A3A5Ld;SbcA3S2A3S1S0SbSb5A1Sb4S2fS70S5aA1A2SaeA3S1S0S8S11A1M6S17S44S54S44S23PaA1ScfSbbA1A3S9S4S16S18R1S1cN148M7A1A2S4S16S18S7R1A1M8S1cN128A1A2S4S16S1aG8G7A2S6S16A1M9A3A3A3Ti;A2S5S11S3cA2A3S1S0G6S17S3cS53S24S24SfS26S2cR1A1Sc5SbbA1A2S26S2dR1A1S1cZ0A1MaA2A2Lo;S2aS12S3cA1A1U0A4S9S4S16S18R1S1cScfSbaA1MbA1A2S4S16S1aR1GbA2G9A3A3Ti;A2S5S11S3dA2A3S1S0S11Sb2S3dS4SaS1dS1dA2McSeS1dS1dGaGaA4S14S3dA1A3A2S30A3S1S0S3S68G4ScGcS4cS4bA3A2S2A3S1S0S3S6cG4S4dA2S2A3S1S0SbGcA1MdS6aSc8S2fS57S59S30A4MeS5bA2S4GcSeS1dS1dS43Sd1Z10S35A2A4S6GcA1A3MfA3S1S0GdS6aSc8S2fS57S58S30A4M10S5bA2GfA3S1S0S1dS65GeS23P8cM11A1M12A2S43A3S1S0S1dS65GeS23P8dM13A1A2S47A3S1S0S1dS65GeS23P8eM14A1M15A2S35A3S1S0S1dS65G10G12A2S43A3S1S0S1dS65G10G15A2S35A3S1S0S3S4fS2eS2eSc6S6bSafS2fG4S12S59A1A4S23R1A1M16A2Lv;S4S2eG11S4S2eG13S4S2eG14S6S2eA1A3M17A3A3A3S2A3S1S0S3S4fS2eS2eSc6S6bSafS2fG4S12S58A1A4G16A2Lv;S4S2eG11G17A3A3S2A3S1S0S1dS65S2fS23PdA1A2S55A3S1S0S11Sb7S57S30S2fS36S59S42A6S3aA3S1S0S11Sb7S57S30S2fS36S58S42A6S38A3S1S0S3S50S22S28S27S35S1cSc4A1A2A1M18S25S12S3aA1A1M19A3S2A3S1S0S3S50S22S28S27S47S35A2A1G19A3S2A3S1S0S3S50S22S28S27S1cSd5A1Sc2A2A1M1aG19A3S2A3S1S0S3S50S22G18S25S12S38A1A1M1bA3S2A3S0S3S50S22G1aG1bA3S2A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Lemma run_checks : ltac2:(tb__ "0|7|
S1S0S3S5eS76S52S3bS21S12S39A1A1M0S4S11S39S6S11A1M1A3S4S11S46S4S11S45G1A3A3A6S2A3S1S0S3S5eS76S52S3bS21S12S37A1A1M2S4S11S37G1A3S4S11S34S4S11S33G1A3A3A6S2A3S1S0S3S5fS76S52S3bG0S4S5cS5dS39Z259M3S63A3S6S5cA1M4A3S4S5cS5dS46Z258M5S63A3S4S5cS5dS45G5S63A3G4A3A3A6S2A3S1S0S3S5fS76S52S3bG2S4S5cS5dS37G3S63A3G4A3S4S5cS5dS34G5S63A3S4S5cS5dS33G5S63A3G4A3A3A6S2A3S1S0S3S60S51G0A2S2A3S1S0S3S60S51G2A2S2A3S1S0S3ScdG0S78A2S2A3S1S0S3ScdG2S78A2S2A3S1S0S3S68G0S77A2S2A3S1S0S3S6cG0S4dA2S2A3S1S0S3S68G2S77A2S2A3S1S0S3S6cG2S4dA2S2A3S1S0S3S60S21S12S30A1A1M6G0A2S2A3S0S3S60G6G2A2S2A3A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

