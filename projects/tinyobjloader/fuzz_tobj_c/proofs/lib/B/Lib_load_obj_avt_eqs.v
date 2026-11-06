(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "bool"; "true"; "pair"; "prod"; "cons"; "nat"; "nil"; "app"; "length"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SPUle"; "sprop"; "sprop_eqb"; "sv"; "SLit"; "ss_facts"; "SAlu"; "ss_next"; "@Stdlib.Lists.List"; "existsb"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bitem"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "AHead"; "NDA"; "nd_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_defs"; "vLEN"; "NP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loop"; "pNX"; "pPOS"; "pLNL"; "pH"; "X_latch"; "xLD"; "xLK"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_lglue"; "frL"; "extraLO"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_avt"; "kept_vt"; "T_vt_ok"; "c_avt"; "E_vt"; "E_vt1"; "R_vt"; "S_vt_okR"; "T_vt_f"; "Xk_vt"; "bd_vt_ok"; "ndX_vt"; "nd_vt_f"; "tv_vt"; "tv_vt_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_avt_eqs"; "Xs_vt"; "Ys_vt"; "bdX_vt"; "comm_vt"; "nd_vt_okX"; "cutsT2"; "exitsT2"; "extra_vt"; "ndXE_vt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_bud"; "RL"; "VLA"; "z0"; "LAX"; "LAXK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAG"; "bd_permb"; "@Stdlib.Arith.PeanoNat.Nat"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs"; "kb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_armkit2"; "lines_chk"; "robj_ent"; "robjs_chkC"; "xextraLO"; "xrs_chkC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_avn"; "PhisV"; "cps_arm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loopE"; "X_latchE2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF"; "bud_pay2"; "ejcertAF"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_opt_push1 Lib_handle_vt.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o6.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_opt_push1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_vt OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o6.Lib_handle_vt_pf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_defs Lib_load_obj_pro Lib_load_obj_pro2 Lib_load_obj_loop Lib_load_obj_disp Lib_load_obj_lglue Lib_load_obj_hv0 Lib_load_obj_bud Lib_load_obj_exits Lib_load_obj_loopE Lib_load_obj_armkit Lib_load_obj_armkit2 Lib_load_obj_avn Lib_load_obj_avt.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr LOAddr LOLAddr HVAddr HVTAddr.

Definition Lok_vt : axst := Eval vm_compute in leafL (runL 200 cps_arm T_vt_ok) pc_latch 0.
Definition s_latch_vt : wsub := Eval vm_compute in infer_sub NP (ax_S Lok_vt) (ax_S X_latch).
Definition bdX_vt : list bitem := Eval vm_compute in bd_subst s_latch_vt (bdX 0).
Definition nd_vt_okX : ndesc := ltac2:(tb__ "0|0|
S1aS36S26S39S19S21S1A2A4").
Definition comm_vt : list bitem := Eval vm_compute in bd_common bd_vt_ok bdX_vt.
Definition Xs_vt : list bitem := Eval vm_compute in bd_minus bd_vt_ok bdX_vt.
Definition Ys_vt : list bitem := Eval vm_compute in bd_minus bdX_vt bd_vt_ok.
Lemma avt_checks_pay : ltac2:(tb__ "0|3|
SaS9S0S45S32S7S15S3aS37A3A2S1A3SaS9S0S45S7S15S3aS38A3S39A2S1A3SaS9S0S51S10S17S2aA1M0A1SfZ0M1A1G1S37S38A5S1A3SaS9S0S46S8S15S37A2UaM2A2S1A3SaS9S0S46S8S15S38A2G2A2S1A3S9S0S1bS12G0A1S3bA2S1A3A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition ndXE_vt : ndesc := ltac2:(tb__ "0|1|
S1aS35S26S4S15S43Z0M0A1S4S15S44G0A1S6S15A1A3A3S19S21S1A2A4").
Definition cutsT2 : list efnode := ltac2:(tb__ "0|6|
S4S3S3S3S16S18A2M0S5A2M1S3S25SeA2M2A2M3S2G1G2S2G0S5S2S16S18S2aS3bA4U1M4A4S2S25SeS40S41ZaS42A2A4M5A4S4G3S2G1G2S2G0S5S2S16S18S30S34A4G4A4G5A4S6G3A1A3A3").
Definition exitsT2 : list efnode := ltac2:(tb__ "0|6|
S4S3S3S3S16S18A2M0S5A2M1S3S25SeA2M2A2M3S2G1G2S2G0S5S2S16S18S22S33A4U1M4A4S2S25SeS40S41Z1S42A2A4M5A4S4G3S2G1G2S2G0S5S2S16S18S50S3fA4G4A4G5A4S6G3A1A3A3").
Lemma ecertT_ok : ltac2:(tb__ "0|0|
S9S0S52S47S1dS4eUc8S4fS1dS3cS3dA8S1A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Definition extra_vt (o : sobj) : bool := ltac2:(tb__ "0|0|
S0S0L_;S27Vo;A1S1S4aVo;A1X0x2").
Lemma avt_checks2 : ltac2:(tb__ "0|2|
SaS9S0S4bS10S17S2cA1A1M0S29S26S3eS2eA5S1A3SaS9S0S4dG0S29S26S4cS31A5S1A3SaS9S0S49G0A1S1A3SaS9S0S13ScSdSbS2bS1eA2A1S10S17S2dA1A1M1A3S1A3SaS9S0S13ScSdSbS1eS11S28S1cSfZ1A1A3A2A1G1A3S1A3SaS9S0S13ScSdSbS1cSfZ4000000A1A2A1G1A3S1A3SaS9S0S13ScSdSbS1eS1fA2A1G1A3S1A3S9S0S13ScSdSbS11S28S1fS20A3S1cA2A1G1A3S1A3A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Lemma avt_checks3 : ltac2:(tb__ "0|2|
SaS9S0S13ScSdSbS2bS1eA2A1S10S2fA1M0A3S1A3SaS9S0S13ScSdSbS1eS1fA2A1G0A3S1A3SaS9S0S13ScSdSbS11S28S1fS20A3S1cA2A1G0A3S1A3SaS9S0S13ScSdSbS1cSfZ4000000A1M1A2A1G0A3S1A3SaS9S0S13ScSdSbS1fG1A2A1G0A3S1A3S9S0S13ScSdSbS20G1A2A1G0A3S1A3A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma lines_in_kept_vt : ltac2:(tb__ "0|0|
S14S3SeSeA2S2SeSeS23S48Z10S24A2A4S29A3").
Proof. cbn. do 16 right. left. reflexivity. Qed.
