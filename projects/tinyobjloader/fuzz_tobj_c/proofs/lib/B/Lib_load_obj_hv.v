(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "bool"; "nil"; "true"; "list"; "option"; "pair"; "Some"; "andb"; "false"; "prod"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "axwf"; "la_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "ss_pc"; "SLit"; "cell"; "sprop"; "sv_eqb"; "SAlu"; "SPUle"; "SVar"; "c_val"; "ob_base"; "ob_cells"; "ob_lo"; "ss_facts"; "ss_objs"; "swf"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double"; "Pre_sd"; "P_none"; "P_num"; "@LinuxProcessSemantics.Riscv.Instr"; "aluop"; "ALU_ADD"; "mulop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double.ScanDoubleAddr"; "sd_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXSplit"; "AXUnbase"; "apply_axforms"; "@Stdlib.Lists.List"; "forallb"; "filter"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv"; "s_sd"; "E_sd1"; "E_sd1r"; "K_hv0c"; "E_da1"; "E_da2"; "E_da3"; "E_sd2"; "E_sd3"; "E_sd4"; "E_sd5"; "E_sd6"; "E_sd7"; "E_sd8"; "L_vr3"; "L_vr4"; "L_vr5"; "L_vr6"; "L_vr7"; "L_vr8"; "R_sd"; "T_sd0"; "X_hv"; "cur0"; "cur_of"; "i_nums"; "nums_mat"; "sd_ok"; "xf_sd1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv0"; "cps_hv"; "runL"; "E_hv0"; "K_hv0"; "leafL"; "@Stdlib.ZArith.BinInt.Z"; "eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loop.LOLAddr"; "c_da"; "c_vr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "call_checkA"; "import_postA"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_defs"; "optR"; "vBUF"; "vLEN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv0.HVAddr"; "hv_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loop"; "pE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_setX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.AddCellsA"; "add_cells8_ok"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_defs Lib_load_obj_pro Lib_load_obj_pro2 Lib_load_obj_loop Lib_load_obj_disp Lib_load_obj_hv0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr LOAddr LOLAddr HVAddr.

Definition i_nums : nat := 2%nat.
Definition nums_mat : list Z := ltac2:(tb__ "0|0|
S0S21N110S0S21N108S0S21N100S2S21A1A3A3A3").
Definition K_hv0c : axst := Eval vm_compute in ax_setS K_hv0 (add_cells8 (ax_S K_hv0) i_nums nums_mat).

Definition E_sd1r : axst := Eval vm_compute in leafL (runL 400 cps_hv K_hv0c) sd_entry 0.

Definition xf_sd1 : list axform := ltac2:(tb__ "0|1|
S0S2dS2eU7S13N30A1A2S0S2dS2eU5M0S13N70A1A2S0S2dS2fG0N78A2S2S2dA1A3A3A3").
Definition optL' (x : option axst) : axst := match x with Some a => a | None => Pre_lo end.
Definition E_sd1 : axst := Eval vm_compute in optL' (apply_axforms E_sd1r xf_sd1).

Definition s_sd (E : axst) : wsub := ltac2:(tb__ "0|1|
S0SaS22S10A2M0S6S22S10PfS5eA4S0G0S6S22S10P11S61A4S0G0S6S22S10P12S5fA4S62PaScVE;A1ScS26A1A3A3A3A3").
Definition R_sd (E : axst) : list sobj := ltac2:(tb__ "0|0|
S5dS59VE;S26S33VE;A1A3A1").
Definition T_sd0 (E L : axst) : axst := ltac2:(tb__ "0|0|
S58S1eScVE;A1A1S5bS33VE;A1S26VL;VE;S47VE;A1A5A2").

Definition cur_of (A : axst) : sv := ltac2:(tb__ "0|5|
S4S11A1M0S10Lx;S32S11S11S8S16S1bR1A1S17S2aS19PaA1S13N88A1A3A2S16S1dR1A1S13Z0A1M1A2A2Lo;S1fScVA;A1A1A3G1S11G0S4S14A1M2S10Lx;S1cR2A1G1S14G2S10S10Lx;S1aR2A1S21G1Lz;S22G1Li;S29S10S10S29S10Lop;R3R1G1G1G1G1G1G1G1G1G1X29xaLv;La;Lop;S29S10S10G1Lb;La;M3Lop;S2bG3Lop;M4G4S1S23S10G1La;Lw;Lsgn;S22S10S21G1Lk;Li;Ll;X10x8Ll;Lc;X4x2Ll;Lo;X4x2").
Definition cur0 : sv := SAlu ALU_ADD (SVar 473) (SLit 1).

Definition T_sd (E L : axst) : axst := ltac2:(tb__ "0|0|
S48VE;VL;A2SbS58S0S15S18S4aS4bR1A1A2S2S15A1A3R1A2TT0;").
Definition sd_ok (E : axst) : bool := ltac2:(tb__ "0|2|
S5S4S11A1M0A1S1Lx;S59VE;S26S33VE;A1M1A3G0S5aVE;S26G1R1S0SbS27S0SbS28S2SbA1A3A3A5LR;S9X5x2").

Definition X_hv : list (sv * sv) := ax_X K_body.
Definition E_next (Ty : axst) : axst := ltac2:(tb__ "0|0|
S63S54S51U190S50VTy;A3S2cU0A3S49A2").

Definition T_sd1n : axst := Eval vm_compute in T_sd E_sd1 P_none.   Definition T_sd1y : axst := Eval vm_compute in T_sd E_sd1 P_num.
Definition E_sd2 : axst := Eval vm_compute in E_next T_sd1y.
Definition T_sd2n : axst := Eval vm_compute in T_sd E_sd2 P_none.   Definition T_sd2y : axst := Eval vm_compute in T_sd E_sd2 P_num.
Definition E_sd3 : axst := Eval vm_compute in E_next T_sd2y.
Definition T_sd3n : axst := Eval vm_compute in T_sd E_sd3 P_none.   Definition T_sd3y : axst := Eval vm_compute in T_sd E_sd3 P_num.
Definition E_sd4 : axst := Eval vm_compute in E_next T_sd3y.
Definition T_sd4n : axst := Eval vm_compute in T_sd E_sd4 P_none.   Definition T_sd4y : axst := Eval vm_compute in T_sd E_sd4 P_num.
Definition E_sd5 : axst := Eval vm_compute in E_next T_sd4y.
Definition T_sd5n : axst := Eval vm_compute in T_sd E_sd5 P_none.   Definition T_sd5y : axst := Eval vm_compute in T_sd E_sd5 P_num.
Definition E_sd6 : axst := Eval vm_compute in E_next T_sd5y.
Definition T_sd6n : axst := Eval vm_compute in T_sd E_sd6 P_none.   Definition T_sd6y : axst := Eval vm_compute in T_sd E_sd6 P_num.
Definition E_sd7 : axst := Eval vm_compute in E_next T_sd6y.
Definition T_sd7n : axst := Eval vm_compute in T_sd E_sd7 P_none.   Definition T_sd7y : axst := Eval vm_compute in T_sd E_sd7 P_num.
Definition E_sd8 : axst := Eval vm_compute in E_next T_sd7y.
Definition T_sd8n : axst := Eval vm_compute in T_sd E_sd8 P_none.   Definition T_sd8y : axst := Eval vm_compute in T_sd E_sd8 P_num.

Lemma hv_checks_sd : ltac2:(tb__ "0|2|
S25S24S21S12ScS52A1A1S60A3S25S24S1S20ScS53A1M0A1S3A3S25S24S1S64G0S4cS4dA3S3A3S25S24S1SeS36A1S3A3S25S24S21S12ScS35A1A1S2cA3S25S24S4S21A1S5cSdS21SdS12ScSfR1A1A1A1LL;S51U190S50S36A3A4S0S21S2cS2S21A1A3A3S25S24S5SbA1S30S35S4fA2S7SbS34A2A3S25S24S1S31SbS4eS0SbS34S0SbS3aS0SbS3bS0SbS3cS0SbS3dS0SbS3eS0SbS3fS0SbS40S2SbA1A3A3A3A3A3A3A3M1A3A3S3A3S24S1S31SbSbS55S12ScR1A1A1S2cA2LE;G1A3S3A3A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition cps_v : list Z := ltac2:(tb__ "0|0|
S0S21S57S0S21S56S50A3A3").
Definition E_da1 : axst := Eval vm_compute in leafL (runL 600 cps_v T_sd1n) c_da 0.
Definition E_da2 : axst := Eval vm_compute in leafL (runL 600 cps_v T_sd2n) c_da 0.
Definition E_da3 : axst := Eval vm_compute in leafL (runL 600 cps_v T_sd3n) c_da 0.
Definition L_vr3 : axst := Eval vm_compute in leafL (runL 600 cps_v T_sd4n) c_vr 0.
Definition L_vr4 : axst := Eval vm_compute in leafL (runL 600 cps_v T_sd5n) c_vr 0.
Definition L_vr5 : axst := Eval vm_compute in leafL (runL 600 cps_v T_sd6n) c_vr 0.
Definition L_vr6 : axst := Eval vm_compute in leafL (runL 600 cps_v T_sd7n) c_vr 0.
Definition L_vr7 : axst := Eval vm_compute in leafL (runL 600 cps_v T_sd8n) c_vr 0.
Definition L_vr8 : axst := Eval vm_compute in leafL (runL 600 cps_v T_sd8y) c_vr 0.
Lemma hv_checks_ends : ltac2:(tb__ "0|2|
S25S24S1S31SbSbS55S12ScR1A1A1M0S56A2LE;S0SbS37S0SbS38S0SbS39S2SbA1M1A3A3A3A3S3A3S24S1S31SbSbS55G0S57A2LE;S0SbS41S0SbS42S0SbS43S0SbS44S0SbS45S0SbS46G1A3A3A3A3A3A3A3S3A3A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
