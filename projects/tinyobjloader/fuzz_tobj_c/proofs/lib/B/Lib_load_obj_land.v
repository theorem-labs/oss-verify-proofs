(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "nat"; "nil"; "prod"; "app"; "bool"; "false"; "true"; "S"; "length"; "None"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "cell"; "sprop"; "SPUle"; "sobj"; "ss_objs"; "FcsrFrm0"; "SAlu"; "SPUlt"; "SVar"; "c_off"; "mkSS"; "sv_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "apply_axforms"; "AXMerge"; "AXSplit"; "AXUnbase"; "AXSelect"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_defs"; "optL"; "idxB"; "vF"; "optS"; "sel2last"; "vDp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_land"; "zsub"; "splits_from"; "MJ"; "E_blr"; "bb_hi"; "cps_proR"; "fofs"; "iC"; "iD"; "iK"; "rt1256"; "rt_at"; "rt_drop"; "rt_news"; "unb_all"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loop"; "bA"; "pI"; "nx_facts"; "vsP"; "xLC"; "kL"; "HNEXT"; "LSAc"; "NZ32e"; "X_loopA"; "kLE"; "loop_factsA"; "pERR"; "pNX"; "rate_factsLo"; "@Corelib.Lists.ListDef"; "seq"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs"; "c1"; "c4"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loop.LOLAddr"; "pc_after"; "pc_body"; "pc_errx"; "pc_latch"; "@Corelib.Init.Nat"; "add"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Lib_build_line_index_rom.BLRAddr"; "FR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_pro"; "vARn"; "ax_tidy"; "@Stdlib.PArith.BinPos.Pos"; "of_nat"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "mkA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_exits"; "coreJ"; "jfregsA"; "jregsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_land.BLR"; "Pre_blr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve"; "c8"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p0.ObjRetileB"; "retile_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.ObjZeroA"; "zero_cells_at"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_defs Lib_load_obj_pro Lib_load_obj_pro2 Lib_load_obj_loop Lib_load_obj_lglue Lib_load_obj_bud Lib_load_obj_exits.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p0.ObjRetileB.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Module BLR. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Lib_build_line_index_rom. End BLR.
Module BLRP. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Lib_build_line_index_rom_pf. End BLRP.
Import ScanDoubleAddr VRAddr RA.ReallocAddr LOAddr LOLAddr.

Definition cps_proR : list Z := bli_entry :: cps_pro.
Definition E_blr0 : axst := Eval vm_compute in leafL_at cps_proR T_vend bli_entry 0.

Definition E_blr1 : axst := Eval vm_compute in
  let i := idxB E_blr0 (SVar 10) (- FR) in
  optL (apply_axforms E_blr0 [AXSplit i (SLit (-328)); AXSplit (S i) (SLit (-296)); AXUnbase (S i) (-328)]    ).
Definition E_blr2 : axst := Eval vm_compute in
  let i := find_idxb (fun o => sv_eqb (ob_base o) (spm FR) && sv_eqb (ob_hi o) (SLit 0)) (ss_objs (ax_S E_blr1)) 0%nat in
  optL (apply_axforms E_blr1 [AXSplit i (SLit (- BLRAddr.FR)); AXUnbase i (- BLRAddr.FR)]).
Definition E_blr : axst := Eval vm_compute in ax_setX E_blr2 ((SLit 0, SLit 0) :: ax_X E_blr2).
Definition s_blr : wsub := ltac2:(tb__ "0|2|
S0S4SdSeA2M0S1SdSeP13S16S56S29SfS52A1A3A4S0G0S1SdSePfSfZ0A1M1A4S0G0S1SdSeP10G1A4S0G0S1SdSeP11G1A4S5dPaS1dS2dA1S1dS5bA1A3A3A3A3A3").
Definition R_blr : list sobj := Eval vm_compute in optR (entails_frA E_blr BLR.Pre_blr s_blr).

Definition XkB : list (sv * sv) := ax_X E_blr.

Definition tv_pass : list (sv * sv) := ltac2:(tb__ "0|2|
S0S4SeSeA2M0S1SeSeSfZ0A1M1G1A4S3G0A1A3").
Definition tv_site : list (sv * sv) := [blkAR].

Definition blr_back (T : axst) : axst := ltac2:(tb__ "0|3|
S54S24S1fVT;S0S1eS22U1M0S52A2S0S1eS23S0S2G0S0S2U0M1S48U2M2S51SaS13S14S1dVT;A1A1A2G2A2A2A3A3A1S0S1eS20G1A1S3S1eA1A3A3A3A2A1A1").
Definition T_blr1a : axst := Eval vm_compute in T_afterA3 BLR.Pre_blr E_blr s_blr R_blr BLR.P_ret1 XkB.
Definition T_blr0a : axst := Eval vm_compute in T_afterA3 BLR.Pre_blr E_blr s_blr R_blr BLR.P_ret0 XkB.
Definition T_blr1 : axst := Eval vm_compute in blr_back T_blr1a.
Definition T_blr0 : axst := Eval vm_compute in blr_back T_blr0a.

Definition iD : sv := SVar 424. Definition iC : sv := SVar 425. Definition iK : sv := SVar 426.

Definition cps_land : list Z := ltac2:(tb__ "0|0|
S0ScS4fS0ScS4dS0ScS4cS0ScS4eS2fA3A3A3A3").
Definition XR_body1 : axst := Eval vm_compute in leafL_at cps_land T_blr1 pc_body 0.
Definition XR_after1 : axst := Eval vm_compute in leafL_at cps_land T_blr1 pc_after 0.
Definition XR_body0 : axst := Eval vm_compute in leafL_at cps_land T_blr0 pc_body 0.
Definition XR_after0 : axst := Eval vm_compute in leafL_at cps_land T_blr0 pc_after 0.

Definition fofs (l : list Z) : list Z := map (fun z => z + 448) l.
Fixpoint splits_from (i : nat) (l : list Z) : list axform :=
  match l with [] => [] | b :: r => AXSplit i (SLit b) :: splits_from (S i) r end.
Definition bb_hi : list Z := ltac2:(tb__ "0|0|
S0ScZ78S0ScZ98S0ScZb8S0ScZd8S0ScZf8S0ScZ118S0ScZ138S0ScZ140S0ScZ160S0ScZ180S0ScZ1a0S0ScZ1c0S0ScZ1e0S0ScZ1f0S0ScZ210S0ScZ230S0ScZ250S0ScZ270S0ScZ290S0ScZ2b0S0ScZ2d0S0ScZ2f0S0ScZ310S0ScZ330S0ScZ350S0ScZ370S0ScZ3a8S0ScZ3c8S0ScZ3e8S0ScZ408S0ScZ428S0ScZ448S0ScZ468S0ScZ488S0ScZ4a8S0ScZ4c8S0ScZ4e8S3ScA1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Fixpoint unb_all (n : nat) (A : axst) : axst :=
  match n with O => A | S n' =>
    let i := find_idxb (fun o => sv_eqb (ob_base o) vF && match ob_lo o with SLit l => (448 <=? l) && (l <? 1752) | _ => false end) (ss_objs (ax_S A)) 0%nat in
    if (i <? length (ss_objs (ax_S A)))%nat then unb_all n' (optL (apply_axforms A [AXUnbase i 448])) else A end.
Definition zsub (A : axst) (i : nat) (mid : Z) (lowfree : bool) (cs : list cell) : axst := ltac2:(tb__ "0|1|
S24S1fVA;S0S1eS21Vi;SfVmid;A1A2S3S1eA1M0A3A2A1S1cS6S2Llowfree;Vlowfree;Vi;S9Vi;A1X6x2S2S27R2S5fS1dR2A1R1Vcs;A3A2S1cS24S1fR1S0S1eS20Vi;A1G0A3A2A1TA2;Tj;TA1;").

Definition rt_at (A : axst) : nat := idxB A vF 544.
Definition rt_drop (c : cell) : bool := ltac2:(tb__ "0|0|
S1bS19Vc;A1SfZ6a8A1A2").
Definition rt_news : list cell := ltac2:(tb__ "0|0|
S0S10S4bZ6a8SfZffffffffffffffffA1A2S0S10S4bZ6acSfZ0A1A2S3S10A1A3A3").
Definition rt1256 (A : axst) : axst := ltac2:(tb__ "0|0|
S27VA;S5eS1dVA;A1S35VA;A1S36S37A4A2").
Definition canon_K (errzero : bool) (A00 : axst) : axst := ltac2:(tb__ "0|10|
S34VA00;A1S1cS24S1fR1S2bS25R1S26Z220A3S30S2eA1A2A2A1S1cS24S1fR1S2bS25R1S26Z1c0A3S0ScZ1c8S0ScZ1e0M0S3ScA1M1A3A3A2A2A1S1cS24S1fR1S2bS25R1S18PaA1M2N128A3S0ScN88M3S0ScN80M4S0ScN78G1A3A3A3A2A2A1S1cS24S1fR1S0S1eS21S25R1S26Z0M5A3SfZ20A1A2S3S1eA1M6A3A2A1S1cS38U2dR1A2S1cS24S1fR1S0S1eS22S25R1G2G3A3G3A2G6A3A2A1S1cS24S1fR1S0S1eS22S25R1G2G4A3G3A2G6A3A2A1S1cS25R1S53G5A3S2S25R2S53Z30A3S2S24S1fR3S0S1eS23S28R3R2R1A3A1G6A3A2A1S1cS24S1fR1S0S1eS20S51SaS13S14S1dR1A1A1A2U2A2A1G6A3A2A1S1cS6S1cLerrzero;Verrzero;S2aR1S25R1S39Z60M7A3M8Z70M9S8S0S10S4bG7SfG5A1MaA2S0S10S5cZ68MbGaA2S3S10A1McA3MdA3A5G8S2S24S1fR2S0S1eS21R1SfGbA1A2G6A3A2A1S1cS2aR1S9R2A1G9S8GdA5S1cS24S1fR1S0S1eS20R3A1G6A3A2A1TB2;TB1;Ti;X6x2S1cS2aR1S25R1S39G0A3Z1e8MeS7S0S10S4aGeGaA2GcA3A5S1cS2aR1S25R1S39Z4e8A3Z4f0MfS7S0S10S4aGfGaA2GcA3A5S1cS2aR1S25R1S39Z370A3Z384S8S0S10S4aZ375GaA2GcA3A5TA12;TA11;TA10;TA9;TA8;TiH;TiL;TA7;TA6;TA5;TA4;TA3;TA2;TA1;TA0;").
Definition K1b : axst := Eval vm_compute in canon_K true XR_body1.
Definition K1a : axst := Eval vm_compute in canon_K true XR_after1.
Definition K0b : axst := Eval vm_compute in canon_K false XR_body0.
Definition K0a : axst := Eval vm_compute in canon_K false XR_after0.

Definition M_bodyN : axst := ltac2:(tb__ "0|1|
S40S4dS0S4S2SeA2M0S1S2SeU16S3aA4S3G0A1A3S3eS3cA1S5S11S0S11S17S3aS3dA2S3bA3S47S46S3cA2A3A4").
Definition MJ (pc : Z) (k : cst) (facts : list sprop) : axst := ltac2:(tb__ "0|0|
S57S1aVpc;S5aS3S4S2SeA2A1A1S59S15SbSeA1S58Vk;A1S5S11Vfacts;S44Vk;A1A3S3fS7A9S42Vk;A1A2").
Definition M_after0 : axst := ltac2:(tb__ "0|0|
S2cS4cS3eS3cA1S0S11S12S3dS3aA2S3bA3A3").
Definition M_afterE : axst := ltac2:(tb__ "0|0|
S2cS4cS43S0S11S12S3dS3aA2S0S11S41S45A1S3bA3A3A3").
Definition M_bodyE : axst := Eval vm_compute in ax_setS X_bodyE (set_objs (ax_S X_bodyE) (firstn (length (ss_objs (ax_S X_bodyE)) - 18) (ss_objs (ax_S X_bodyE)))).

Definition s_fix : wsub := ltac2:(tb__ "0|3|
S5S4SdSeA2M0S49S2G0S2S1SdSeS55S50U190R1A2A1SfZ0A1M1A4Li;S48U0M2U36A2A4S5G0S0G0S1SdSeP1ccG1A4S0G0S1SdSeP1cfG1A4S0G0S1SdSeP1d0G1A4S0G0S1SdSeP1d1G1A4S0G0S1SdSeP1d2S32A4S0G0S1SdSeP1d3S31A4S0G0S1SdSeP1d4S33A4S0G0S1SdSeP1ddSfZffffffffffffffffA1A4S0G0S1SdSeP1deG1A4S0G0S1SdSeP1eaG1A4S3G0A1A3A3A3A3A3A3A3A3A3A3S49S2G0S2S1SdSeS55S50U244R1A2A1G1A4Li;S48G2UbA2A4A3A3").
Definition s_landB : wsub := Eval vm_compute in s_fix ++ infer_sub 500 (ax_S K1b) (ax_S M_bodyN).
Definition s_landA : wsub := Eval vm_compute in s_fix ++ infer_sub 500 (ax_S K1a) (ax_S M_after0).
Definition s_landBE : wsub := Eval vm_compute in (461%positive, SLit 2) :: s_fix ++ infer_sub 500 (ax_S K0b) (ax_S M_bodyE).
Definition s_landAE : wsub := Eval vm_compute in (461%positive, SLit 2) :: s_fix ++ infer_sub 500 (ax_S K0a) (ax_S M_afterE).

