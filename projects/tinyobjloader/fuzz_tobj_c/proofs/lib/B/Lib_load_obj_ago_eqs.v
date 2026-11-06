(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "bool"; "true"; "pair"; "cons"; "nat"; "prod"; "app"; "nil"; "length"; "false"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bitem"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "ss_facts"; "ss_next"; "SLit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "AHead"; "NDA"; "nd_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_lglue"; "frL"; "tvL"; "V_B"; "extraLO"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAG"; "bd_permb"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_ago_eqs"; "Yf_go"; "Xs_nop"; "Xs_ok"; "Ys_nop"; "Ys_ok"; "Xf_fz"; "Xf_go"; "bdX_nop"; "bdX_ok"; "bd_fzX"; "bd_go_fX"; "comm_nop"; "comm_ok"; "commf_fz"; "commf_go"; "extra_go"; "nd_fzX"; "nd_go_fX"; "nd_nopX"; "nd_okX"; "cutsG"; "exitsG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_bud"; "RL"; "VLA"; "z0"; "LAX"; "LAXK"; "ndX0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF"; "bud_pay2"; "V_below"; "ejcertAF"; "@Stdlib.Arith.PeanoNat.Nat"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_ago"; "kept_fs"; "kept_go"; "T_fs_fz"; "T_fs_nop"; "T_fs_ok"; "T_go_f"; "nd_go_ok"; "E_fs"; "E_fs0"; "E_go"; "LAr1"; "LAr1K"; "LAr2"; "LAr2K"; "R_fs"; "R_go"; "T_go_ok"; "Xk_fs"; "Xk_go"; "bd_fs_fz"; "bd_fs_nop"; "bd_fs_ok"; "bd_go_f"; "qHk"; "qHn"; "qHz"; "tvL_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs"; "kb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_armkit2"; "lines_chk"; "robjs_chkC"; "xextraLO"; "xrs_chkC"; "robj_ent"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_defs"; "NP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loop"; "xLD"; "xLK"; "X_latch"; "pH"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_avn"; "PhisV"; "cps_arm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loopE"; "X_latchE2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loopEf"; "ndXEf"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR TobjJAS TobjJAT TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAFb OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.TobjJAH OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.ObjZeroA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import ObjEmptyA PinA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Lib_rom_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require no.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nz.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_finalize_shape.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_defs Lib_load_obj_pro Lib_load_obj_pro2 Lib_load_obj_loop Lib_load_obj_disp Lib_load_obj_lglue Lib_load_obj_hv0 Lib_load_obj_bud Lib_load_obj_exits Lib_load_obj_loopE Lib_load_obj_loopEf Lib_load_obj_armkit Lib_load_obj_armkit2 Lib_load_obj_avn Lib_load_obj_ago.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr LOAddr LOLAddr HVAddr.

Definition Xf_go : list bitem := ltac2:(tb__ "0|0|
S3ScS47S3ScS48S7ScA1A3A3").
Definition Yf_go : list bitem := ltac2:(tb__ "0|1|
S3ScS36Z0M0A1S3ScS37G0A1S7ScA1A3A3").
Definition commf_go : list bitem := Eval vm_compute in bd_minus bd_go_f Xf_go.
Definition bd_go_fX : list bitem := Yf_go ++ commf_go.
Definition nd_go_fX : ndesc := ltac2:(tb__ "0|0|
S15S18S17S27S14S62S9A2A4").
Lemma ago_checks_payf1 : ltac2:(tb__ "0|2|
SbSaS0S1bS53S6ScS2bS23A3A2S1A3SbSaS0S1bS6ScS2bS1dA3S27A2S1A3SbSaS0S39SeS12S42A1M0A1S10Z0M1A1G1S23S1dA5S1A3SaS0S16SfG0A1S2eA2S1A3A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition Lnop : axst := Eval vm_compute in leafL (runL 200 cps_arm T_fs_nop) pc_latch 0.
Definition s_latch_nop : wsub := Eval vm_compute in infer_sub NP (ax_S Lnop) (ax_S X_latch).
Definition bdX_nop : list bitem := Eval vm_compute in bd_subst s_latch_nop (bdX 0).
Definition nd_nopX : ndesc := ltac2:(tb__ "0|0|
S15S18S17S24S14S55S1A2A4").
Definition comm_nop : list bitem := Eval vm_compute in bd_common bd_fs_nop bdX_nop.
Definition Xs_nop : list bitem := Eval vm_compute in bd_minus bd_fs_nop bdX_nop.
Definition Ys_nop : list bitem := Eval vm_compute in bd_minus bdX_nop bd_fs_nop.

Definition Lok : axst := Eval vm_compute in leafL (runL 200 cps_arm T_fs_ok) pc_latch 0.
Definition s_latch_ok : wsub := Eval vm_compute in infer_sub NP (ax_S Lok) (ax_S X_latch).
Definition bdX_ok : list bitem := Eval vm_compute in bd_subst s_latch_ok (bdX 0).
Definition nd_okX : ndesc := ltac2:(tb__ "0|0|
S15S57S17S25S14S54S1A2A4").
Definition comm_ok : list bitem := Eval vm_compute in bd_common bd_fs_ok bdX_ok.
Definition Xs_ok : list bitem := Eval vm_compute in bd_minus bd_fs_ok bdX_ok.
Definition Ys_ok : list bitem := Eval vm_compute in bd_minus bdX_ok bd_fs_ok.

Lemma ago_checks_pay2 : ltac2:(tb__ "0|5|
SbSaS0S1bS51S6ScS28S1eA3A2S1A3SbSaS0S1bS6ScS28S20A3S24A2S1A3SbSaS0S39SeS12S40A1M0A1S10Z0M1A1M2G1S1eS20A5S1A3SbSaS0S16SfG0A1S2fA2S1A3SbSaS0S1bS52S6ScS29S1fA3A2S1A3SbSaS0S1bS6ScS29S21A3S25A2S1A3SbSaS0S39SeS12S41A1M3A1G2G1S1fS21A5S1A3SbSaS0S16SfG3A1S30A2S1A3SbSaS0S3cS8ScS1eA2UcM4A2S1A3SbSaS0S3cS8ScS20A2G4A2S1A3SbSaS0S3cS8ScS1fA2G4A2S1A3SaS0S3cS8ScS21A2G4A2S1A3A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition Xf_fz : list bitem := ltac2:(tb__ "0|0|
S3ScS49S3ScS4aS7ScA1A3A3").
Definition commf_fz : list bitem := Eval vm_compute in bd_minus bd_fs_fz Xf_fz.
Definition bd_fzX : list bitem := Yf_go ++ commf_fz.
Definition nd_fzX : ndesc := ltac2:(tb__ "0|0|
S15S18S17S26S14S56S9A2A4").
Lemma ago_checks_payf2 : ltac2:(tb__ "0|2|
SbSaS0S1bS50S6ScS2aS22A3A2S1A3SbSaS0S1bS6ScS2aS1dA3S26A2S1A3SbSaS0S39SeS12S3fA1M0A1S10Z0M1A1G1S22S1dA5S1A3SaS0S16SfG0A1S2dA2S1A3A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition cutsG : list efnode := ltac2:(tb__ "0|7|
S3S5S5S5S11S13A2M0S4A2M1S5S1cSdA2M2A2M3S2G1G2S2G0S4S2S11S13S4dS43A4U1M4A4S2S1cSdS33S34ZaS35A2A4M5A4S3G3S2G1G2S2G0S4S2S11S13S42S2eA4G4A4G5A4S3G3S2G1G2S2G0S4S2S11S13S40S2fA4G4A4S2S1cSdS33S34Z5S35A2A4M6A4S3G3S2G1G2S2G0S4S2S11S13S41S30A4G4A4G6A4S3G3S2G1G2S2G0S4S2S11S13S3fS2dA4G4A4G6A4S7G3A1A3A3A3A3A3").
Definition exitsG : list efnode := ltac2:(tb__ "0|6|
S3S5S5S5S11S13A2M0S4A2M1S5S1cSdA2M2A2M3S2G1G2S2G0S4S2S11S13S45S43A4U1M4A4S2S1cSdS33S34Z7S35A2A4A4S3G3S2G1G2S2G0S4S2S11S13S61S38A4G4A4S2S1cSdS33S34Z1S35A2A4M5A4S3G3S2G1G2S2G0S4S2S11S13S67S68A4G4A4G5A4S7G3A1A3A3A3").
Lemma ecertG_ok : ltac2:(tb__ "0|0|
SaS0S3bS64S5eS65Uc8S66S5eS31S32A8S1A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Definition extra_go (o : sobj) : bool := ltac2:(tb__ "0|0|
S0S0L_;S1aVo;A1S1S5dVo;A1X0x2").
Lemma ago_checks3 : ltac2:(tb__ "0|3|
SbSaS0S5aSeS12S46A1A1M0S3eS17S2cS4cA5S1A3SbSaS0S5cG0S3eS17S5bS4fA5S1A3SbSaS0S59G0A1S1A3SbSaS0S5aSeS12S44A1M1A1M2S3dS17S2cS4bA5S1A3SbSaS0S5cG2S3dS17S5bS4eA5S1A3SbSaS0S59G2A1S1A3SaS0S3aSfG1A1S19A2S1A3A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma lines_in_kept_go : ltac2:(tb__ "0|0|
S63S5SdSdA2S2SdSdS5fS58Z10S60A2A4S3eA3").
Proof. cbn. repeat (first [left; reflexivity | right]). Qed.
Lemma lines_in_kept_fs : ltac2:(tb__ "0|0|
S63S5SdSdA2S2SdSdS5fS58Z10S60A2A4S3dA3").
Proof. cbn. repeat (first [left; reflexivity | right]). Qed.
