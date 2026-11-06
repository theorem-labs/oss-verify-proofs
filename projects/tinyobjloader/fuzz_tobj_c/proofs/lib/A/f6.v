(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAD.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
From LinuxProcessSemantics.LinuxProcessSem Require StackLayout Fs Monad Specs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require g5.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap Mprotect.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require StartTop.

(* [comment removed for export] *)
Module Lib_load_obj_land.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "nat"; "nil"; "prod"; "app"; "bool"; "false"; "true"; "S"; "length"; "None"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "cell"; "sprop"; "SPUle"; "sobj"; "ss_objs"; "FcsrFrm0"; "SAlu"; "SPUlt"; "SVar"; "mkSS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "apply_axforms"; "AXMerge"; "AXSplit"; "AXUnbase"; "AXSelect"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs"; "optL"; "idxB"; "vF"; "optS"; "sel2last"; "vDp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f6.Lib_load_obj_land"; "zsub"; "splits_from"; "MJ"; "E_blr"; "bb_hi"; "cps_proR"; "fofs"; "iC"; "iD"; "iK"; "unb_all"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop"; "bA"; "pI"; "nx_facts"; "vsP"; "xLC"; "kL"; "HNEXT"; "LSAc"; "NZ32e"; "X_loopA"; "kLE"; "loop_factsA"; "pERR"; "pNX"; "rate_factsLo"; "@Corelib.Lists.ListDef"; "seq"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs"; "c1"; "c4"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop.LOLAddr"; "pc_after"; "pc_body"; "pc_errx"; "pc_latch"; "@Corelib.Init.Nat"; "add"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.en.Lib_build_line_index_rom.BLRAddr"; "FR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro"; "vARn"; "ax_tidy"; "@Stdlib.PArith.BinPos.Pos"; "of_nat"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "mkA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_exits"; "coreJ"; "jfregsA"; "jregsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f6.Lib_load_obj_land.BLR"; "Pre_blr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve"; "c8"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.ObjZeroA"; "zero_cells_at"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV TobjArena ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TobjJVA InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR TobjJAS TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAD.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require ResidualA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require DrvGlueC ObjEmptyA PinA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAM2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ResidualA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.ObjZeroA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.DrvGlueC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ObjEmptyA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.PinA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Asan_set_shadow_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs Lib_rom_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Asan_set_shadow_iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.Asan_memcpy48_iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_rom_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ej.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require em.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require el.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require en.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.en.Lib_build_line_index_rom OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_build_line_index_rom_pf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_defs Lib_load_obj_pro.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eo.Lib_load_obj_pro2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_exits.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Module BLR. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.en.Lib_build_line_index_rom. End BLR.
Module BLRP. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_build_line_index_rom_pf. End BLRP.
Import ScanDoubleAddr VRAddr RA.ReallocAddr LOAddr LOLAddr.

Definition cps_proR : list Z := bli_entry :: cps_pro.
Definition E_blr0 : axst := Eval vm_compute in leafL_at cps_proR T_vend bli_entry 0.

Definition E_blr1 : axst := Eval vm_compute in
  let i := idxB E_blr0 (SVar 10) (- FR) in
  optL (apply_axforms E_blr0 [AXSplit i (SLit (-216)); AXSplit (S i) (SLit (-184)); AXUnbase (S i) (-216)]).
Definition E_blr2 : axst := Eval vm_compute in
  let i := find_idxb (fun o => sv_eqb (ob_base o) (spm FR) && sv_eqb (ob_hi o) (SLit 0)) (ss_objs (ax_S E_blr1)) 0%nat in
  optL (apply_axforms E_blr1 [AXSplit i (SLit (- BLRAddr.FR)); AXUnbase i (- BLRAddr.FR)]).
Definition E_blr : axst := Eval vm_compute in ax_setX E_blr2 ((SLit 0, SLit 0) :: ax_X E_blr2).
Definition s_blr : wsub := ltac2:(tb__ "0|2|
S0S4SdSeA2M0S1SdSeP13S16S50S27SfS4cA1A3A4S0G0S1SdSePfSfZ0A1M1A4S0G0S1SdSeP10G1A4S0G0S1SdSeP11G1A4S57PaS1bS2bA1S1bS55A1A3A3A3A3A3").
Definition R_blr : list sobj := Eval vm_compute in optR (entails_frA E_blr BLR.Pre_blr s_blr).

Definition XkB : list (sv * sv) := ax_X E_blr.

Definition tv_pass : list (sv * sv) := ltac2:(tb__ "0|2|
S0S4SeSeA2M0S1SeSeSfZ0A1M1G1A4S3G0A1A3").
Definition tv_site : list (sv * sv) := [blkAR].

Definition blr_back (T : axst) : axst := ltac2:(tb__ "0|3|
S4eS22S1dVT;S0S1cS20U1M0S4cA2S0S1cS21S0S2G0S0S2U0M1S42U2M2S4bSaS13S14S1bVT;A1A1A2G2A2A2A3A3A1S0S1cS1eG1A1S3S1cA1A3A3A3A2A1A1").
Definition T_blr1a : axst := Eval vm_compute in T_afterA3 BLR.Pre_blr E_blr s_blr R_blr BLR.P_ret1 XkB.
Definition T_blr0a : axst := Eval vm_compute in T_afterA3 BLR.Pre_blr E_blr s_blr R_blr BLR.P_ret0 XkB.
Definition T_blr1 : axst := Eval vm_compute in blr_back T_blr1a.
Definition T_blr0 : axst := Eval vm_compute in blr_back T_blr0a.

Definition iD : sv := SVar 1823. Definition iC : sv := SVar 1824. Definition iK : sv := SVar 1825.

Definition cps_land : list Z := ltac2:(tb__ "0|0|
S0ScS49S0ScS47S0ScS46S0ScS48S2dA3A3A3A3").
Definition XR_body1 : axst := Eval vm_compute in leafL_at cps_land T_blr1 pc_body 0.
Definition XR_after1 : axst := Eval vm_compute in leafL_at cps_land T_blr1 pc_after 0.
Definition XR_body0 : axst := Eval vm_compute in leafL_at cps_land T_blr0 pc_body 0.
Definition XR_after0 : axst := Eval vm_compute in leafL_at cps_land T_blr0 pc_after 0.

Definition fofs (l : list Z) : list Z := map (fun z => z + 544) l.
Fixpoint splits_from (i : nat) (l : list Z) : list axform :=
  match l with [] => [] | b :: r => AXSplit i (SLit b) :: splits_from (S i) r end.
Definition bb_hi : list Z := ltac2:(tb__ "0|0|
S0ScZ78S0ScZ98S0ScZb8S0ScZd8S0ScZf8S0ScZ118S0ScZ138S0ScZ140S0ScZ160S0ScZ180S0ScZ1a0S0ScZ1c0S0ScZ1e0S0ScZ1f0S0ScZ210S0ScZ230S0ScZ250S0ScZ270S0ScZ290S0ScZ2b0S0ScZ2d0S0ScZ2f0S0ScZ310S0ScZ330S0ScZ350S0ScZ370S0ScZ3a8S0ScZ3c8S0ScZ3e8S0ScZ408S0ScZ428S0ScZ448S0ScZ468S0ScZ488S0ScZ4a8S0ScZ4c8S0ScZ4e8S3ScA1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Fixpoint unb_all (n : nat) (A : axst) : axst :=
  match n with O => A | S n' =>
    let i := find_idxb (fun o => sv_eqb (ob_base o) vF && match ob_lo o with SLit l => (544 <=? l) && (l <? 1848) | _ => false end) (ss_objs (ax_S A)) 0%nat in
    if (i <? length (ss_objs (ax_S A)))%nat then unb_all n' (optL (apply_axforms A [AXUnbase i 544])) else A end.
Definition zsub (A : axst) (i : nat) (mid : Z) (lowfree : bool) (cs : list cell) : axst := ltac2:(tb__ "0|1|
S22S1dVA;S0S1cS1fVi;SfVmid;A1A2S3S1cA1M0A3A2A1S1aS6S2Llowfree;Vlowfree;Vi;S9Vi;A1X6x2S2S25R2S58S1bR2A1R1Vcs;A3A2S1aS22S1dR1S0S1cS1eVi;A1G0A3A2A1TA2;Tj;TA1;").
Definition canon_K (errzero : bool) (A0 : axst) : axst := ltac2:(tb__ "0|f|
S22S1dVA0;S29S23VA0;S24Z280A3S2eS2cA1A2A2A1S1aS22S1dR1S29S23R1S24Z200A3S0ScZ220S0ScZ228S0ScZ240S3ScA1M0A3A3A3A2A2A1S1aS22S1dR1S29S23R1S18PaA1M1Nb8A3S0ScNa0M2S0ScN98M3S0ScN90G0A3A3A3A2A2A1S1aS22S1dR1S0S1cS1fS23R1S24Z0M4A3SfZ20A1A2S3S1cA1M5A3A2A1S1aS32U2dR1A2S1aS22S1dR1S0S1cS20S23R1G1G2A3G2A2G5A3A2A1S1aS22S1dR1S0S1cS20S23R1G1G3A3G2A2G5A3A2A1S1aS23R1S4dG4A3S2S23R2S4dZ30A3S2S22S1dR3S0S1cS21S26R3R2R1A3A1G5A3A2A1S1aS22S1dR1S0S1cS1eS4bSaS13S14S1bR1A1A1A2U2A2A1G5A3A2A1S1aS6S1aLerrzero;Verrzero;S28R1S23R1S33Z60M6A3M7Z70M8S8S0S10S45G6SfG4A1M9A2S0S10S56Z68MaG9A2S3S10A1MbA3McA3A5G7S2S22S1dR2S0S1cS1fR1SfGaA1A2G5A3A2A1S1aS28R1S9R2A1G8S8GcA5S1aS22S1dR1S0S1cS1eR3A1G5A3A2A1TB2;TB1;Ti;X6x2S1aS28R1S23R1S33Z1e0A3Z1e8MdS7S0S10S44GdG9A2GbA3A5S1aS28R1S23R1S33Z4e8A3Z4ecMeS7S0S10S45GeG9A2S0S10S44Z4f0G9A2GbA3A3A5S1aS28R1S23R1S33Z370A3Z388S8S0S10S44Z375G9A2GbA3A5TA12;TA11;TA10;TA9;TA8;TiH;TiL;TA7;TA6;TA5;TA4;TA3;TA2;TA1;").
Definition K1b : axst := Eval vm_compute in canon_K true XR_body1.
Definition K1a : axst := Eval vm_compute in canon_K true XR_after1.
Definition K0b : axst := Eval vm_compute in canon_K false XR_body0.
Definition K0a : axst := Eval vm_compute in canon_K false XR_after0.

Definition M_bodyN : axst := ltac2:(tb__ "0|1|
S3aS47S0S4S2SeA2M0S1S2SeU17S34A4S3G0A1A3S38S36A1S5S11S0S11S17S34S37A2S35A3S41S40S36A2A3A4").
Definition MJ (pc : Z) (k : cst) (facts : list sprop) : axst := ltac2:(tb__ "0|0|
S51S19Vpc;S54S3S4S2SeA2A1A1S53S15SbSeA1S52Vk;A1S5S11Vfacts;S3eVk;A1A3S39S7A9S3cVk;A1A2").
Definition M_after0 : axst := ltac2:(tb__ "0|0|
S2aS46S38S36A1S0S11S12S37S34A2S35A3A3").
Definition M_afterE : axst := ltac2:(tb__ "0|0|
S2aS46S3dS0S11S12S37S34A2S0S11S3bS3fA1S35A3A3A3").
Definition M_bodyE : axst := Eval vm_compute in ax_setS X_bodyE (set_objs (ax_S X_bodyE) (firstn (length (ss_objs (ax_S X_bodyE)) - 18) (ss_objs (ax_S X_bodyE)))).

Definition s_fix : wsub := ltac2:(tb__ "0|3|
S5S4SdSeA2M0S43S2G0S2S1SdSeS4fS4aU190R1A2A1SfZ0A1M1A4Li;S42U0M2U36A2A4S5G0S0G0S1SdSeP1ccG1A4S0G0S1SdSeP1cfG1A4S0G0S1SdSeP1d0G1A4S0G0S1SdSeP1d1G1A4S0G0S1SdSeP1d2S30A4S0G0S1SdSeP1d3S2fA4S0G0S1SdSeP1d4S31A4S0G0S1SdSeP1ddSfZffffffffffffffffA1A4S0G0S1SdSeP1deG1A4S0G0S1SdSeP1eaG1A4S3G0A1A3A3A3A3A3A3A3A3A3A3S43S2G0S2S1SdSeS4fS4aU244R1A2A1G1A4Li;S42G2UbA2A4A3A3").
Definition s_landB : wsub := Eval vm_compute in s_fix ++ infer_sub 500 (ax_S K1b) (ax_S M_bodyN).
Definition s_landA : wsub := Eval vm_compute in s_fix ++ infer_sub 500 (ax_S K1a) (ax_S M_after0).
Definition s_landBE : wsub := Eval vm_compute in (461%positive, SLit 2) :: s_fix ++ infer_sub 500 (ax_S K0b) (ax_S M_bodyE).
Definition s_landAE : wsub := Eval vm_compute in (461%positive, SLit 2) :: s_fix ++ infer_sub 500 (ax_S K0a) (ax_S M_afterE).

End Lib_load_obj_land.

(* [comment removed for export] *)
Module StartHandoffBlocks.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "sub"; "pow"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv_unsigned"; "bv"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "and"; "or"; "eq"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "eval"; "@Corelib.Init.Datatypes"; "pair"; "cons"; "prod"; "list"; "nil"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "mmap_place_ok_none"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "m_vmmaps"; "alloc_top"; "vm_maps"; "vm_reserved"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Placement"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start6"; "q12x"; "LIMz"; "m16"; "n17"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g5.StartHandoffApart"; "GMe"; "ZLOW"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start7"; "kHighMemBeg"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "segments_reserved"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.Start4"; "m10"; "m11"; "m8"; "m9"; "n7"; "n9"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fl.Start5"; "m12"; "m13"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g4.Start8"; "rhoOK"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt LedgerA StepA SoundA GlueA MmapA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Init Placement PlacementA StartLib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Start4States.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fl.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Start6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Start7 Start8M.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require g2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fz.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require g4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require g5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Init OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Placement OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.PlacementA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartLib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e3.StartArgF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start4States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.Start4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fl.Start5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fl.Start6States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fs.Start6bStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start8M OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g2.Start8Out OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fz.Start8CallA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fz.Start8CallB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g4.Start8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g5.StartHandoffApart.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Ltac blia := unfold SHADOW_BAND_LO, SHADOW_BAND_HI, SHADOW_RW_LO_END, SHADOW_RW_HI_BEG, kHighMemBeg in *; lia.

Lemma LIMz_le_q12x : ltac2:(tb__ "0|0|
S8S0Z0R1A2S0S1cR2A1S1bR2A1A2F_;Fx;").
Proof.
  intros x Hx. unfold LIMz, q12x, shx.
  pose proof (Z.div_mod x 4096 ltac:(lia)). pose proof (Z.mod_pos_bound x 4096 ltac:(lia)).
  pose proof (Z.mod_pos_bound (x / 8 + 2147450880 - 131072) 4096 ltac:(lia)).
  assert ((x - x mod 4096) / 8 <= x / 8) by (apply Z.div_le_mono; lia). lia.
Qed.

Lemma LIMz_lt_top : ltac2:(tb__ "0|0|
S8S0Z7fff80000000R1A2S0S1S1cR2A1S4Z2Z14A2A2S3R2Z800000A2A2F_;Fx;").
Proof.
  intros x Hx. unfold LIMz.
  pose proof (Z.div_mod x 4096 ltac:(lia)). pose proof (Z.mod_pos_bound x 4096 ltac:(lia)).
  pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.mod_pos_bound x 8 ltac:(lia)).
  assert ((x - x mod 4096) / 8 <= x / 8) by (apply Z.div_le_mono; lia). lia.
Qed.

Lemma u64_of_lit : ltac2:(tb__ "0|1|
S8S9S0Z0R1A2S2R1S4Z2Z40A2A2A2SbS8S6Q40M0S5G0R2A2A2R2A3F_;Fz;").
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. exact Hz. Qed.

Section Blocks.
Variables (m : Model) (a1 a2 : word).
Hypothesis Hres : ltac2:(tb__ "0|1|
SbS12S11S7Q40A1M0G0A2A1S18S15Vm;A1A1S23S24A1A3").
Hypothesis Hmaps : ltac2:(tb__ "0|3|
SbS12S11S7Q40M0A1M1G1A2M2A1S17S15Vm;A1A1S10G2SfG1G1Va2;S5G0Z38e000A2A4S10G2SfG1G1Va1;S5G0Z10000A2A4S10G2SfG1G1S5G0Z2008fff7000A2S5G0Zdfff0001000A2A4S10G2SfG1G1S5G0Z8fff7000A2S5G0Z20000000000A2A4S10G2SfG1G1S5G0Z7fff7000A2S5G0Z10000000A2A4S13G2A1A3A3A3A3A3A3").
Hypothesis Htop : init_sp_ok (m_vmmaps m).
Hypothesis Ha1 : ltac2:(tb__ "0|2|
S9S0Z646000S6Q40Va1;A2M0A2S9SaS0S1G0Z10000A2M1S1aA2S0S19G0A2A2S0G1S16S15Vm;A1A1A2A2A2").
Hypothesis Ha2 : ltac2:(tb__ "0|2|
S9S0Z646000S6Q40Va2;A2M0A2S9SaS0S1G0Z38e000A2M1S1aA2S0S19G0A2A2S0G1S16S15Vm;A1A1A2A2A2").
Variables (P b4 b5 b6 : word).
Hypothesis HPL : ltac2:(tb__ "0|0|
S14S5Q40Z0A2Vm;S29VP;A4").
Hypothesis HPL4 : ltac2:(tb__ "0|0|
S14S5Q40Z0A2S27Vm;VP;A2S2aVb4;A4").
Hypothesis HPL5 : ltac2:(tb__ "0|1|
S14S5Q40M0Z0A2S28Vm;VP;Vb4;A3S5G0Z1000A2Vb5;A4").
Hypothesis HPL6 : ltac2:(tb__ "0|1|
S14S5Q40M0Z0A2S25Vm;VP;Vb4;Vb5;A4S5G0Z10000A2Vb6;A4").
Variables (b7 b8 b9 : word).
Hypothesis HPL7 : ltac2:(tb__ "0|1|
S14S5Q40M0Z0A2S26Vm;VP;Vb4;Vb5;Vb6;A5S5G0Z1000A2Vb7;A4").
Hypothesis HPL8 : ltac2:(tb__ "0|1|
S14S5Q40M0Z0A2S2bVm;VP;Vb4;Vb5;Vb6;Vb7;A6S5G0Z1000A2Vb8;A4").
Hypothesis HPL9 : ltac2:(tb__ "0|1|
S14S5Q40M0Z0A2S2cVm;VP;Vb4;Vb5;Vb6;Vb7;Vb8;A7S5G0Z1000A2Vb9;A4").
Variables (x : Z) (b10 : word).
Hypothesis Hx : 0x7fff80000000 <= x <= 2 ^ 47.
Hypothesis H16 : x mod 16 = 0.
Hypothesis Hxtop : ltac2:(tb__ "0|0|
SbS8S16S15Vm;A1A1S3Vx;Z800000A2A3").
Hypothesis HPL10 : ltac2:(tb__ "0|1|
S14S5Q40M0Z0A2S1dVm;VP;Vb4;Vb5;Vb6;Vb7;Vb8;Vb9;Vx;A9S5G0S1eA2Vb10;A4").

Variables (rho : valuation) (b12 b13 b14 : word).
Hypothesis HROK : ltac2:(tb__ "0|0|
S2dVm;Va1;Va2;VP;Vb4;Vb5;Vb6;Vb7;Vb8;Vb9;Vx;Vb10;Vrho;Ad").
Hypothesis H159 : rw rho 159%positive = b12.
Hypothesis H160 : rw rho 160%positive = b13.
Hypothesis H161 : rw rho 161%positive = b14.
Hypothesis W12 : ltac2:(tb__ "0|2|
S9SaS0S1S6Q40Vb12;A2M0Z100000A2M1S1aA2S0S19G0A2A2S0G1S3Vx;Z800000A2A2A2").
Hypothesis W13 : ltac2:(tb__ "0|3|
S9SaS0S1S6Q40Vb13;A2M0Z800000M1A2M2S1aA2S0S19G0A2A2S0G2S3Vx;G1A2A2A2").
Hypothesis W14 : ltac2:(tb__ "0|2|
S9SaS0S1S6Q40Vb14;A2M0Z1000A2M1S1aA2S0S19G0A2A2S0G1S3Vx;Z800000A2A2A2").

Local Notation blocks16 := (Start6.blocks16 m a1 a2 Hres Hmaps Htop Ha1 Ha2 P b4 b5 b6 HPL HPL4 HPL5 HPL6 b7 b8 b9 HPL7 HPL8 HPL9) (only parsing).
Local Notation b10_facts := (Start7.b10_facts m a1 a2 Hres Hmaps Htop P b4 b5 b6 HPL HPL4 HPL5 HPL6 b7 b8 b9 HPL7 HPL8 HPL9 x b10 Hxtop HPL10) (only parsing).
Local Notation P_facts := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.Start4.P_facts m a1 a2 Hres Hmaps Htop P HPL) (only parsing).
Local Notation RI_val := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.Start4.RI_val m a1 a2 Hres Hmaps Htop P HPL) (only parsing).
Local Notation RI_range := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.Start4.RI_range m a1 a2 Hres Hmaps Htop P HPL) (only parsing).
Local Notation SB_val := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.Start4.SB_val m a1 a2 Hres Hmaps Htop P HPL) (only parsing).
Local Notation b4_facts := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.Start4.b4_facts m a1 a2 Hres Hmaps Htop P HPL b4 HPL4) (only parsing).
Local Notation b5_facts := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.Start4.b5_facts m a1 a2 Hres Hmaps Htop P HPL b4 HPL4 b5 HPL5) (only parsing).
Local Notation b6_facts := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.Start4.b6_facts m a1 a2 Hres Hmaps Htop P HPL b4 HPL4 b5 HPL5 b6 HPL6) (only parsing).
Local Notation b7_facts := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fl.Start5.b7_facts m a1 a2 Hres Hmaps Htop P b4 b5 b6 HPL HPL4 HPL5 HPL6 b7 HPL7) (only parsing).
Local Notation b8_facts := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fl.Start5.b8_facts m a1 a2 Hres Hmaps Htop P b4 b5 b6 HPL HPL4 HPL5 HPL6 b7 HPL7 b8 HPL8) (only parsing).

Definition prof (rho : valuation) (e : sv) (sz : Z) : Prop :=
  let b := bv_unsigned (eval rho e) in
  ((b + sz <= SHADOW_BAND_LO \/ SHADOW_BAND_HI <= b) /\ b + sz <= x - 8388608)
  \/ (0x2008fff7000 <= b /\ b + sz <= LIMz x)
  \/ (e = SLit LOWPG /\ sz = 0x4c00) \/ (e = SLit 0x7fffc000 /\ sz = 4096) \/ (e = SLit 0x80015000 /\ sz = 4096).

Lemma GM_prof : forall e sz, In (e, sz) GMe -> prof rho e sz.
Proof.
  intros e sz Hin. pose proof HROK as (HV & H36 & H77 & H78 & H83 & Hx1 & V35 & _).
  pose proof HV as (H27 & H28 & H29 & H30 & H31 & H32 & H33 & H34 & Hv1).
  unfold GMe, G24, G23b, G22b, G18, G17 in Hin. rewrite <- !app_assoc in Hin.
  apply in_app_iff in Hin as [Hin|Hin].
  -
    assert (Hin14 : In (e, sz) G14b) by (unfold G14b; apply in_app_iff; left; exact Hin).
    destruct (blocks16 rho HV H36 H77 H78 e sz Hin14) as [Hb|(-> & -> & Hl & Hh)].
    + left. split; [exact Hb|].

      pose proof P_facts as (Pal & Pceil & _ & PLB & _). pose proof RI_val as RV. pose proof RI_range as (R1 & R2 & R3). pose proof SB_val as SB.
      pose proof b4_facts as (_ & _ & C4 & _). pose proof b5_facts as (_ & _ & _ & C5 & _). pose proof (b6_facts) as (_ & _ & C6 & _).
      pose proof b7_facts as (_ & _ & C7 & _). pose proof b8_facts as (_ & _ & C8 & _).
      pose proof Ha1 as (_ & _ & C1). pose proof Ha2 as (_ & _ & C2). rewrite Hxtop in *.
      unfold G13b, G12b, G11c in Hin. rewrite <- !app_assoc in Hin. cbn [List.app In] in Hin.
      destruct Hin as [E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]; injection E as <- <-; cbn [eval].
      * rewrite H27. lia.
      * rewrite H28. lia.
      * unfold ri30. cbn [eval]. rewrite H30. pose proof (urange (spacebeg P)). rewrite U_add_small by lia. lia.
      *
        pose proof (Start6.priZ_facts m a1 a2 Hres Hmaps Htop P b4 b5 b6 HPL rho HV) as (PR1 & _). rewrite Hx1 in PR1.
        unfold shRI_base. cbn [eval]. pose proof (urange (rw rho 31%positive)). unfold priZ in PR1.
        pose proof (LIMz_lt_top x ltac:(lia)). rewrite U_add_small by lia. lia.
      * rewrite H33. lia.
      * rewrite H34. lia.
      * rewrite H36. lia.
      * rewrite H77. lia.
    + right. left. rewrite Hx1 in Hl. split; [exact Hh | exact Hl].
  - cbn [List.app In] in Hin. pose proof b10_facts as (_ & L2 & L3 & _). unfold Start7.TOPz in L3.
    repeat (destruct Hin as [E|Hin]; [injection E as <- <-|]); [..|destruct Hin]; unfold prof; cbv zeta; cbn [eval];
    first [ left; rewrite H83; split; [exact L2 | lia]
          | left; rewrite H159; exact W12
          | left; rewrite H160; exact W13
          | left; rewrite H161; exact W14
          | right; right; left; split; reflexivity
          | right; right; right; left; split; reflexivity
          | right; right; right; right; split; reflexivity ].
Qed.

Lemma q12x_lo : ltac2:(tb__ "0|1|
S9S0Z10006fef9000S1bVx;A1M0A2S0G0S22A2A2").
Proof.
  clear - Hx. unfold q12x, shx, kHighMemBeg.
  pose proof (Z.mod_pos_bound (x / 8 + 2147450880 - 131072) 4096 ltac:(lia)).
  assert (17591917608960 <= x / 8) by (apply Z.div_le_lower_bound; lia).
  assert (x / 8 <= 17592186044416) by (apply Z.div_le_upper_bound; lia).
  split; lia.
Qed.

Lemma GM_low : ltac2:(tb__ "0|1|
SdS8S21S11SdS8A2SfSdS8R2R1A4S1fA3S8S20R1A1ScS9S0S6Q40SeVrho;R5A2A2M0R2A2S2R2S1G0R4A2A2A2A1F_;Fy;F_;Fsz;Fe;").
Proof.
  intros e sz Hin y Hy. pose proof (GM_prof e sz Hin) as PR. unfold prof, ZLOW in *. cbv zeta in PR.
  pose proof (LIMz_le_q12x x ltac:(lia)). pose proof q12x_lo as [Q1 Q2].
  destruct PR as [[B C]|[[B C]|[[-> ->]|[[-> ->]|[-> ->]]]]]; cbn [eval]; unfold LOWPG; rewrite ?u64_of_lit by lia; pose proof (LIMz_lt_top x ltac:(lia)); blia.
Qed.

Lemma GM_high : ltac2:(tb__ "0|1|
SdS8S21S11SdS8A2SfSdS8R2R1A4S1fA3S8S9S0S1bVx;A1R1A2S2R1S22A2A2ScS9S0S6Q40SeVrho;R5A2A2M0R2A2S2R2S1G0R4A2A2A2A1F_;Fy;F_;Fsz;Fe;").
Proof.
  intros e sz Hin y Hy. pose proof (GM_prof e sz Hin) as PR. unfold prof in *. cbv zeta in PR.
  pose proof (LIMz_le_q12x x ltac:(lia)). pose proof q12x_lo as [Q1 Q2].
  destruct PR as [[B C]|[[B C]|[[-> ->]|[[-> ->]|[-> ->]]]]]; cbn [eval]; unfold LOWPG; rewrite ?u64_of_lit by lia; pose proof (LIMz_lt_top x ltac:(lia)); blia.
Qed.

Lemma GM_argf : ltac2:(tb__ "0|1|
SdS8S21S11SdS8A2SfSdS8R2R1A4S1fA3S8S9S0Vx;R1A2S2R1S4Z2Z2fA2A2A2ScS9S0S6Q40SeVrho;R5A2A2M0R2A2S2R2S1G0R4A2A2A2A1F_;Fy;F_;Fsz;Fe;").
Proof.
  intros e sz Hin y Hy. pose proof (GM_prof e sz Hin) as PR. unfold prof in *. cbv zeta in PR.
  pose proof (LIMz_le_q12x x ltac:(lia)). pose proof q12x_lo as [Q1 Q2].
  destruct PR as [[B C]|[[B C]|[[-> ->]|[[-> ->]|[-> ->]]]]]; cbn [eval]; unfold LOWPG; rewrite ?u64_of_lit by lia; pose proof (LIMz_lt_top x ltac:(lia)); blia.
Qed.
End Blocks.
End StartHandoffBlocks.

(* [comment removed for export] *)
Module StartMainFds.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "m_fds"; "m_fs"; "Model"; "FdEntry"; "VmMaps"; "vm_add_lazy"; "vm_forget_range"; "with_vmmaps"; "@Corelib.Numbers.BinNums"; "Z"; "@stdpp.bitvector.definitions"; "bv"; "@Corelib.Init.Datatypes"; "list"; "prod"; "@LinuxProcessSemantics.LinuxProcessSem.Fs"; "Fs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f6.StartMainFds"; "FF"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect"; "mprotect_model_next"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start7"; "out18"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.StartNodes"; "eager_model"; "lazy_none_model"; "lazy_rw_model"; "null_none_model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e8.StartNodes3"; "null_rw_model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartTop"; "Mmain"; "mS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.SysSpecStart"; "mmap_fixed_rw_ok_model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "munmap_model"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt MmapA MmapFixedA MmapFixedA2 MmapBrkA MmapNodesA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require SysSpecStart SysStartA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Start2 Start3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fl.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Start6 Start7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require g4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require StartTop.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.SysSpecStart OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.SysStartA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.StartNodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.StartNodes2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e8.StartNodes3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e8.Start1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.Start4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fl.Start5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g4.Start8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartTop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.MuslMalloc40Nodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.MuslMalloc40Post.
Import ListNotations. Close Scope bv_scope. Open Scope Z_scope.
Definition FF (f : Model -> Model) : Prop := ltac2:(tb__ "0|1|
S4S1S0ScSdSbQ40A1S5A2A1S2Vf;R1A1M0A1S2R1A1A3S0SeS3G0A1S3R1A1A3A2Fmd;").
Lemma FF_comp : ltac2:(tb__ "0|2|
S4S4F_;M0G0SfR2A1M1G1SfS4R5R4R1A1A1Lmd;A1F_;F_;Fg;Ff;").
Proof. intros f g Hf Hg md. destruct (Hf (g md)) as [A B]. destruct (Hg md) as [C D]. rewrite A, B, C, D. auto. Qed.
Lemma FF_with_vmmaps : ltac2:(tb__ "0|0|
S6SfS9R1A1A1Fh;"). Proof. intros h md. destruct md; split; reflexivity. Qed.
Lemma FF_vm_add_lazy : ltac2:(tb__ "0|1|
SbQ40A1M0G0SfS7R2R1A2A1Fn;Fa;"). Proof. intros a n md. destruct md; split; reflexivity. Qed.
Lemma FF_vm_forget_range : ltac2:(tb__ "0|0|
SaSaSfS8R2R1A2A1Fhi;Flo;"). Proof. intros lo hi md. destruct md; split; reflexivity. Qed.
Lemma FF_lazy_rw : ltac2:(tb__ "0|0|
SaSaSfS14R2R1A2A1Fn;Fa;"). Proof. intros a n md. unfold lazy_rw_model. destruct md; split; reflexivity. Qed.
Lemma FF_lazy_none : ltac2:(tb__ "0|0|
SaSaSfS13R2R1A2A1Fn;Fa;"). Proof. intros a n md. unfold lazy_none_model. destruct md; split; reflexivity. Qed.
Lemma FF_null_none : ltac2:(tb__ "0|2|
SaS4SbQ40A1M0S1S0ScSdG0S5A2A1S2S15R3R2R1A3M1A1S2R2A1A3S0SeS3G1A1S3R2A1A3A2Fa;Fmd;Fn;").
Proof. intros n md a. unfold null_none_model. destruct md; split; reflexivity. Qed.
Lemma FF_eager : ltac2:(tb__ "0|2|
SaS4SbQ40A1M0S1S0ScSdG0S5A2A1S2S12R3R2R1A3M1A1S2R2A1A3S0SeS3G1A1S3R2A1A3A2Fa;Fmd;Fn;").
Proof. intros n md a. unfold eager_model. destruct md; split; reflexivity. Qed.
Lemma FF_null_rw : ltac2:(tb__ "0|2|
SaS4SbQ40A1M0S1S0ScSdG0S5A2A1S2S16R3R2R1A3M1A1S2R2A1A3S0SeS3G1A1S3R2A1A3A2Fa;Fmd;Fn;").
Proof. intros n md a. unfold null_rw_model. destruct md; split; reflexivity. Qed.
Lemma FF_munmap : ltac2:(tb__ "0|2|
S4SbQ40A1M0G0S1S0ScSdG0S5A2A1S2S1aR3R2R1A3M1A1S2R3A1A3S0SeS3G1A1S3R3A1A3A2Fn;Fa;Fmd;").
Proof. intros md a n. unfold munmap_model, with_mmap_destroyed. destruct md; split; reflexivity. Qed.
Lemma FF_fixed_rw : ltac2:(tb__ "0|2|
SbQ40A1M0S4G0G0S1S0ScSdG0S5A2A1S2S19R4R3R2R1A4M1A1S2R3A1A3S0SeS3G1A1S3R3A1A3A2Fn;Fa;Fmd;Ffl;").
Proof. intros fl md a n. unfold mmap_fixed_rw_ok_model, with_mmap_replacement, with_mmap_backing. destruct (mmap_noreserve_b fl); destruct md; split; reflexivity. Qed.
Lemma FF_mprotect : ltac2:(tb__ "0|2|
S4SbQ40A1M0G0S1S0ScSdG0S5A2A1S2S10R3R2R1A3M1A1S2R3A1A3S0SeS3G1A1S3R3A1A3A2Fn;Fa;Fmd;").
Proof. intros md a n. unfold mprotect_model_next. destruct md; split; reflexivity. Qed.

Lemma FF_mS : ltac2:(tb__ "0|2|
S4SbQ40A1M0G0S1S0ScSdG0S5A2A1S2S18R3R2R1A3M1A1S2R3A1A3S0SeS3G1A1S3R3A1A3A2Fa2;Fa1;Fm;").
Proof.
  intros m a1 a2. unfold StartTop.mS, StartTop.mA1, StartTop.mB, m6, m5, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e8.Start1.m4, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e8.Start1.m3, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e8.Start1.m2.
  destruct (FF_eager 0x38e000 (eager_model 0x10000 (lazy_rw_model 0x2008fff7000 0xdfff0001000 (lazy_none_model 0x8fff7000 0x20000000000 (lazy_rw_model 0x7fff7000 0x10000000 m))) a1) a2) as [-> ->].
  destruct (FF_eager 0x10000 (lazy_rw_model 0x2008fff7000 0xdfff0001000 (lazy_none_model 0x8fff7000 0x20000000000 (lazy_rw_model 0x7fff7000 0x10000000 m))) a1) as [-> ->].
  destruct (FF_lazy_rw 0x2008fff7000 0xdfff0001000 (lazy_none_model 0x8fff7000 0x20000000000 (lazy_rw_model 0x7fff7000 0x10000000 m))) as [-> ->].
  destruct (FF_lazy_none 0x8fff7000 0x20000000000 (lazy_rw_model 0x7fff7000 0x10000000 m)) as [-> ->]. apply FF_lazy_rw.
Qed.
Ltac ffstep := first
  [ rewrite (proj1 (FF_eager _ _ _)) | rewrite (proj2 (FF_eager _ _ _))
  | rewrite (proj1 (FF_null_none _ _ _)) | rewrite (proj2 (FF_null_none _ _ _))
  | rewrite (proj1 (FF_null_rw _ _ _)) | rewrite (proj2 (FF_null_rw _ _ _))
  | rewrite (proj1 (FF_munmap _ _ _)) | rewrite (proj2 (FF_munmap _ _ _))
  | rewrite (proj1 (FF_fixed_rw _ _ _ _)) | rewrite (proj2 (FF_fixed_rw _ _ _ _))
  | rewrite (proj1 (FF_mprotect _ _ _)) | rewrite (proj2 (FF_mprotect _ _ _))
  | rewrite (proj1 (FF_with_vmmaps _ _)) | rewrite (proj2 (FF_with_vmmaps _ _))
  | rewrite (proj1 (FF_vm_forget_range _ _ _)) | rewrite (proj2 (FF_vm_forget_range _ _ _))
  | rewrite (proj1 (FF_vm_add_lazy _ _ _)) | rewrite (proj2 (FF_vm_add_lazy _ _ _))
  | rewrite (proj1 (FF_mS _ _ _)) | rewrite (proj2 (FF_mS _ _ _)) ].
Lemma Mmain_fds : ltac2:(tb__ "0|2|
S4SbQ40A1M0G0G0G0G0G0G0G0G0SaG0S11G0G0G0S1S0ScSdG0S5A2A1S2S17R10RfReRdRcRbRaR9R8R7R6R5R4R3R2R1A10M1A1S2R10A1A3S0SeS3G1A1S3R10A1A3A2Fb14;Fb13;Fb12;Fo;Fb10;Fx;Fb9;Fb8;Fb7;Fb6;Fb5;Fb4;FP;Fa2;Fa1;Fm;").
Proof.
  intros. unfold StartTop.Mmain, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g4.Start8.m24, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g4.Start8.m23a, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g4.Start8.m22, Start7.out18_model, out0_model, out1_model, mgrant, mf_exp, mf_res, mg_dead, mg_ok, mg,
    Start7.mE, m17, m16, Start6.mF, m15, m14, m13, m12, m11, m10, m9, m8, m7.
  destruct o as [[|a]|[| | |a]|[| | |a] g]; cbn beta iota; split; repeat ffstep; reflexivity.
Qed.
End StartMainFds.

