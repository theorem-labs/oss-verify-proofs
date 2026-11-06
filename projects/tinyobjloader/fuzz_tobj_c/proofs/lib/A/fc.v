(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f7.
From Stdlib Require Permutation.

(* [comment removed for export] *)
Module Lib_load_obj_avt_eqs.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "bool"; "true"; "pair"; "prod"; "cons"; "nat"; "nil"; "app"; "length"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SPUle"; "sprop"; "sprop_eqb"; "sv"; "SLit"; "ss_facts"; "SAlu"; "ss_next"; "@Stdlib.Lists.List"; "existsb"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bitem"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "AHead"; "NDA"; "nd_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs"; "vLEN"; "NP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop"; "pNX"; "pPOS"; "pLNL"; "pH"; "X_latch"; "xLD"; "xLK"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue"; "frL"; "extraLO"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_avt"; "kept_vt"; "T_vt_ok"; "c_avt"; "E_vt"; "E_vt1"; "R_vt"; "S_vt_okR"; "T_vt_f"; "Xk_vt"; "bd_vt_ok"; "ndX_vt"; "nd_vt_f"; "tv_vt"; "tv_vt_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fc.Lib_load_obj_avt_eqs"; "Xs_vt"; "Ys_vt"; "bdX_vt"; "comm_vt"; "nd_vt_okX"; "cutsT2"; "exitsT2"; "extra_vt"; "ndXE_vt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud"; "RL"; "VLA"; "z0"; "LAX"; "LAXK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG"; "bd_permb"; "@Stdlib.Arith.PeanoNat.Nat"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs"; "kb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit2"; "lines_chk"; "robj_ent"; "robjs_chkC"; "xextraLO"; "xrs_chkC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_avn"; "PhisV"; "cps_arm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_loopE"; "X_latchE2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF"; "bud_pay2"; "ejcertAF"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR TobjJAS TobjJAT TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require ObjEmptyA PinA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAFb OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.TobjJAH OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.ObjZeroA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ObjEmptyA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.PinA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs Lib_rom_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_rom_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_opt_push1 Lib_handle_vt.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eo.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_opt_push1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_vt OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eo.Lib_handle_vt_pf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_defs Lib_load_obj_pro.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eo.Lib_load_obj_pro2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_disp OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_hv0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_exits OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_loopE OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_avn OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_avt.
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
End Lib_load_obj_avt_eqs.

(* [comment removed for export] *)
Module Lib_load_obj_avt_pf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "prod"; "pair"; "list"; "nat"; "true"; "fst"; "snd"; "Some"; "app"; "bool"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sv"; "holds"; "sprop"; "ss_facts"; "eval"; "ss_next"; "SAlu"; "SLit"; "sobj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "PTrue"; "JA_pre"; "ANone"; "JA"; "TPA"; "amode"; "fbinA"; "ffinA"; "frinA"; "nd_am"; "ok_frameKA"; "tvinA"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "smatchA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "etriple"; "triple"; "world"; "@Corelib.Init.Logic"; "and"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eo.Lib_handle_vt_pf"; "P0_vt"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue"; "tblB"; "frL"; "P0_lo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF"; "efmeasA"; "phiK"; "JAF"; "phi_reads"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "mul"; "pow"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud"; "ndA1"; "RL"; "VLA"; "z0"; "ndX0"; "ndXE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_disp"; "E_hvt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "rho_sub"; "wsub"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_avn"; "PhisV"; "h0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_avt"; "kept_vt"; "PDk_vt"; "R_vt"; "E_vt"; "E_vt1"; "Xk_vt"; "avt_cell_new"; "avt_cell_old"; "passed_vt"; "room_vt"; "s_vt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "J_ofPA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs"; "NPH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_avt.HVT"; "Pre_vt"; "nd0"; "Posts_vt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fc.Lib_load_obj_avt_eqs"; "cutsT2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs"; "NP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop"; "X_latch"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_loopE"; "X_latchE2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "BXok_d"; "bxt"; "uval"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.TobjJAH"; "ndh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK"; "PostsCk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double.ScanDoubleAddr"; "pow10_tab"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "call_linkP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "AE_A"; "alloc_contractsA"; "alloc_contractsA_ex"; "alloc_lawsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_geom"; "topG"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_SLL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_fuzz_iface"; "in_lits"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "FBx"; "T_ok"; "tvd"; "tvz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3"; "import_okPA3"; "import_postA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "FFx"; "robjs_okF"; "xrs_okF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "ccount"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR TobjJAS TobjJAT TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require ObjEmptyA PinA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAFb OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.TobjJAH OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.ObjZeroA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ObjEmptyA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.PinA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_rom_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eh.Lib_builder_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_rom_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_opt_push1 Lib_handle_vt.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eo.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_opt_push1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_vt OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eo.Lib_handle_vt_pf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_defs Lib_load_obj_pro.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eo.Lib_load_obj_pro2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_disp OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_hv0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_exits OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_loopE OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_avn OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_avt OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fc.Lib_load_obj_avt_eqs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr LOAddr LOLAddr HVAddr HVTAddr.

Lemma PhisV_reads : ltac2:(tb__ "0|3|
S40S2S4S1A1M0S11OF_;M1A2M2G2S3aS7G0G1R1A3S8G0G1R1A3A2Lp;S50A3").
Proof. constructor; [exact tblL_reads | constructor; [exact tblB_reads | constructor]]. Qed.

Lemma h0_ltH : (h0 < NPH)%positive. Proof. reflexivity. Qed.
Lemma HamC_vt : nd_am HVT.nd0 = ANone. Proof. reflexivity. Qed.
Lemma HamPD_vt : ltac2:(tb__ "0|1|
S40S2SeS1bA2M0G0S31S21S25S8SeS1bR1A3A1S1eA3Ld;S68A3"). Proof. repeat constructor. Qed.
Lemma P0_vt_mono : ltac2:(tb__ "0|2|
S4S2S0S0A2M0A1M1G1G1S4S2G0S0A2A1S11G0S33G0R1R5A3S33G0R2R5A3F_;Fbn;S32R6R5R3R2A4S32R7R5R4R3A4F_;F_;Fr;FFFc;FF';FF;FCST;").
Proof.
  intros CST F F' FFc r HS ((A & B & C) & E). split; [|exact E]. split; [|split; [exact B | exact C]].
  intros a Ha. apply (pclMA_mono CST r F F' FFc FFc a HS (fun x H => H)). exact (A a Ha).
Qed.

Lemma uval_sll1 : ltac2:(tb__ "0|1|
S11S12S3cS6fR2R1A2S3fZ2M0Z3eA2A2S31S0S6fR3S18S7dR2S19Z1A1A3A2S3eG0S6fR3R2A2A2A3F_;Ft;Frho;").
Proof.
  intros rho t Ht. pose proof (uval_range rho t) as R. unfold uval in *. cbn [eval]. rewrite sll_val.
  change (1 mod 64) with 1. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2. rewrite Z.mod_small by lia. lia.
Qed.
Lemma sll1_add2_eq : ltac2:(tb__ "0|0|
S11S31S28Q40A1S16R1S59A2S16R1S58A2A3Frho;").
Proof.
  intros rho. unfold avt_cell_old, avt_cell_new, t1. apply bv_eq. cbn [eval].
  rewrite add_val, !sll_val, add_val, !lit_unsigned. change (1 mod 64) with 1. rewrite !Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
  change (2 mod 2 ^ 64) with 2. change (1 mod 2 ^ 64) with 1.
  rewrite Zplus_mod_idemp_l. rewrite Zmult_mod_idemp_l. f_equal. lia.
Qed.

Lemma room_vt_holds : ltac2:(tb__ "0|0|
S11S40S14S13R1A1S15SfS56A1A1A3S40S14S13R2A1S5bA3F_;Frho;").
Proof.
  intros rho HF. pose proof avt_checks2 as (_ & _ & _ & CT & CN & CL & _).
  pose proof (holds_mem _ _ _ HF CT) as FT. pose proof (holds_mem _ _ _ HF CN) as FN. pose proof (holds_mem _ _ _ HF CL) as FL.
  rewrite h_ule in FT, FN, FL. rewrite uval_lit in FL by lia.
  pose proof (uval_range rho pNX) as RN. pose proof (uval_range rho c_avt) as RC.
  rewrite uval_add_small in FN by (rewrite uval_lit by lia; lia). rewrite uval_lit in FN by lia.
  assert (E1 : uval rho (SAlu ALU_SLL c_avt (SLit 1)) = 2 * uval rho c_avt) by (apply uval_sll1; lia).
  assert (E2 : uval rho (SAlu ALU_ADD (SAlu ALU_SLL c_avt (SLit 1)) (SLit 2)) = 2 * uval rho c_avt + 2) by (rewrite uval_add_small by (rewrite E1, uval_lit by lia; lia); rewrite E1, uval_lit by lia; lia).
  assert (E3 : uval rho (kb 4 (SAlu ALU_ADD (SAlu ALU_SLL c_avt (SLit 1)) (SLit 2))) = 4 * (2 * uval rho c_avt + 2)) by (unfold kb; rewrite uval_mul_lit by (rewrite ?E2; lia); rewrite E2; reflexivity).
  unfold room_vt. constructor; [|constructor; [|constructor]]; apply (proj2 (h_ule _ _ _)).
  - rewrite uval_lit by lia. lia.
  - rewrite E3. rewrite uval_lit by (unfold B_EW, Lib_vec_reserve.B_EW; lia). unfold B_EW, Lib_vec_reserve.B_EW. lia.
Qed.

Section Sum.
Variable AInv : ltac2:(tb__ "0|0|
S7aS11S4S28Q40A1A1S43OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
S79SdVAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
S0S62VCST;R1A2S30S3bZ0R2A2S3cR2S75A2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S0S62VXGL;R1A2S30S3bZ0R2A2S3cR2S75A2A2F_;Fa;").
Hypothesis HXlits : ltac2:(tb__ "0|0|
S0S7eR1A1S62VXGL;R2A2F_;Fa;").
Hypothesis LFLAG : law_flag_stmt AInv.
Hypothesis LFSH : law_fshadow_stmt AInv.
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S4S2S2S0S0A2S0A2A1").
Variable BX : bxt.
Hypothesis HBX : BXok_d 7 BX.
Variable rho0 : valuation.

Hypothesis HFF1 : ltac2:(tb__ "0|1|
S31S5S88Z1S41S2S2S0S0A2M0S0A2G0S7G0S0A2VFF;A4A2U0A3").
Let HNP : NP_okA NP := NP_okA_intro NP eq_refl.
Let P0 : ltac2:(tb__ "0|0|
S11OFr;") := ltac2:(tb__ "0|0|
S36VCST;VFB;VFF;A3").
Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S1fVAInv;VCST;VXGL;S6aVKc;Vrho0;VP0;VFB;VFF;VBX;S1cVnd;Ac").
Let JAFv (Phi : valuation -> Prop) (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S39VAInv;VCST;VXGL;S6aVKc;Vrho0;VP0;VFB;VFF;VBX;S1cVPhi;Vnd;Ad").

Lemma HXpow : ltac2:(tb__ "0|0|
S0S30S3bS72R1A2S3cR1S3dS72Zb8A2A2A2S62VXGL;R2A2F_;Fa;").
Proof.
  intros a Ha. apply HXlits. apply (in_litsL_In _ 145824 184 a); [|unfold pow10_tab, ScanDoubleAddr.pow10_tab in Ha; cbn in Ha |- *; lia].
  unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_fuzz_iface.X_lits. cbn [In]. do 17 right. left. reflexivity.
Qed.

Lemma HIN_vt : ltac2:(tb__ "0|1|
S11S4fS7aS11S4S28Q40A1A1S43S40S14S13R6A1S15SfS55A1A1A3VP0;Vrho0;A1S73S6aVrho0;R8A3VAInv;R7R6R5R4A4S20Vrho0;R8A2S80RbS7cS7bR9A1A1A2S22VFB;RaA2S23VFF;RbA2S27VFB;RcReSaS2S12S12A2S52S5aA3M0A4S81RfG0A2S82R10G0A2S24VFF;RfR11S35A4S30S86VCST;Vrho0;VFB;VFF;R12S52S35S54A8S30S87VCST;VXGL;Vrho0;VFB;VFF;R12S52S35S57A9S32VCST;S7fVFB;R12S52A3S85VFF;R12S35A3S4dS4cR12S54R11A3S5cA2A4A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FAi;Fms;Frho;").
Proof.
  intros rho ms Ai rho1 tp1 md1 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR.
  pose proof avt_checks2 as (CR & CX & CLN & _).
  pose proof (T_ok_T0 rho0 rho Ai HT HTK) as HT0.
  assert (HNk : tvinA FB Ai rho kept_vt) by (apply (tvinA_sublist FB Ai rho (kept_vt ++ passed_vt)); [intros t Ht; apply in_or_app; left; exact Ht | exact HN]).
  assert (HDk : tvd rho kept_vt) by (exact (tvd_app_l rho kept_vt passed_vt HD)).
  assert (HZk : tvz rho kept_vt) by (apply (tvz_sublist rho (kept_vt ++ passed_vt)); [intros t Ht; apply in_or_app; left; exact Ht | exact HZ]).
  split; [|split].
  - apply (robjs_chkC_sound AInv CST ALA HCST rho0 FB FF Ai rho _ kept_vt frL extra_vt R_vt rho1 tp1 md1 HM HF HT HT0 HNk HDk HZk HFR CR).
    intros o a Ho HE Hr. unfold extra_vt in HE. apply lazy_orb_prop in HE as [HE|HE].
    + exact (extraLO_pclMA CST rho0 FB FF rho kept_vt frL o a Hav HP0 HE Hr).
    + exact (robj_ent_pclMA CST rho0 FB FF rho _ _ kept_vt frL o a HF CLN HT0 HZk lines_in_kept_vt HE Hr).
  - apply (xrs_chkC_sound AInv CST XGL ALA HXlits rho0 FB FF Ai rho _ kept_vt frL xextraLO Xk_vt rho1 tp1 md1 HM HF HT HT0 HNk HDk HZk HFR CX).
    intros r a Hr HE Ha. left. exact (xextraLO_pclMA CST rho0 FB FF rho kept_vt frL r a Hav HP0 HE Ha).
  - pose proof avt_checks as (_ & _ & _ & _ & Cta & _).
    destruct HP0 as (Ptxt & Pcfg & Plnk).
    assert (AG : forall v e, e = SVar v -> (v < NP)%positive -> uval rho e = uval rho0 e).
    { intros v e -> Hv. unfold uval. cbn [eval]. rewrite <- (proj1 Hav v Hv). reflexivity. }
    unfold P0_vt, P0_builder. rewrite !rw_call'.
    change (wsub_get s_vt 15) with vBUF. change (wsub_get s_vt 18) with vLEN. change (wsub_get s_vt 12) with bA. change (wsub_get s_vt 58) with alA.
    repeat change (bv_unsigned (eval rho ?e)) with (uval rho e).
    fact HF (SPUle vF (SLit 140737479964672)) HvF. rewrite h_ule, uval_lit in HvF by lia.
    assert (E544 : uval rho (SLit 544) = 544) by (apply uval_lit; lia). assert (E464 : uval rho (SLit 464) = 464) by (apply uval_lit; lia).
    assert (EbA : uval rho bA = uval rho vF + 544) by (unfold bA; rewrite <- E544; apply uval_add_small; rewrite E544; lia).
    assert (EalA : uval rho alA = uval rho vF + 464) by (unfold alA; rewrite <- E464; apply uval_add_small; rewrite E464; lia).
    assert (HinF : In (uval rho vF, fs_frame_size 5, uval rho vFL) (FFx FF rho frL)).
    { apply In_FFx. right. exists (vF, 5, vFL). split; [left; reflexivity | reflexivity]. }
    change (fs_frame_size 5) with 2048 in HinF.
    split; [split; [|split]|].
    + intros a Ha. unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC.pclMA. rewrite (T0_calleeA NP rho0 s_vt rho R_vt ms Hav Cta). fold (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC.pclMA CST rho0 (FBx FB rho kept_vt) (FFx FF rho frL) a).
      apply (pclMA_mono CST rho0 FB (FBx FB rho kept_vt) FF (FFx FF rho frL) a); [intros x Hx; apply In_FBx; left; exact Hx | intros x Hx; apply In_FFx; left; exact Hx |].
      apply Ptxt. rewrite <- (AG 13%positive vBUF eq_refl ltac:(reflexivity)), <- (AG 14%positive vLEN eq_refl ltac:(reflexivity)). exact Ha.
    + exists (uval rho vF), 2048, (uval rho vFL). split; [exact HinF|]. rewrite EbA. lia.
    + exists (uval rho vF), 2048, (uval rho vFL). split; [exact HinF|]. rewrite EalA. lia.
    + unfold FFx. rewrite map_app, ccount_app. cbn [map fst frL]. rewrite HFF1. reflexivity.
Qed.

Section X.
Variable TR : assn -> assn -> Prop.
Variable FAM : ltac2:(tb__ "0|0|
S0S4S28Q40A1A1S2cF_;F_;").
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S2aSeS11S4S28Q40A1A1S2cS40S14S13R3A1S15SfR4A1A1A3VTR;S29SdR6R5R4R3A5R2A2M0F_;G0F_;FQ;Ftp;Frho;FS;FJ;").
Hypothesis TR_ex : forall (T : Type) (J : T -> jpredA) S rho tp (Q : assn),
  (forall x, TR (SPA segs (J x) S rho tp) Q) -> TR (SPA segs (fun r p t m => exists x, J x r p t m) S rho tp) Q.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S2cS2cS2cS2fR3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_pureP : ltac2:(tb__ "0|1|
S2cOS2cS2fR4R1A1R4F_;Fw;R3VTR;R5R3A2M0F_;G0F_;F_;FQ;FX;FP;").
Hypothesis TR_callP : ltac2:(tb__ "0|5|
S2aS2aSeSeS4eS4S1aA1M0S4S2SeS5eA2M1A1S4S2S12S12A2M2A1S2cS11S4S28Q40A1A1M3G2S33G2R1R5A3S33G2R2S10RbA1A3F_;Fr;S31ScG0A1S61RaR9R8A3S9G0R7A2A3S31SbS60RbRaR9R8S41G1SeS7SeS5eA2R7A4A5S6A3S11G3VTR;S29SdRfRdR2R1A5S5dSdS17SfRdA1A1R2R1RaA5A2Ftp1;Frho1;S4S44A1M4S4fS43S2bSdR9R8R10S3G4S63R3S64R2R1A2A4A5R13RaR9R4R2A4R13S4dS4cRbRfS42R3RaR4A3A3R10A2RaR5R3A4F_;F_;Fmd;Fms;Ftr;SeS5eG4S4fS43S11G3G4S4fS43S33G1S3SeS5eRaR9A4R14A3S2bSdR12R11R19S3G4S63R9S64R8R7A2A4A5R1cR13R12RaR8A4S73S17SfR1aA1A1S4dS4cR14R18S42R9R13RaA3A3R19A2R8A3S2bSdR9R8ReS3G4S63R7S64R6R5A2A4A5ReS4dS4cR16R1aS42RbR15RcA3A3R1bA2R15RaR9R8R6A6S30S83R17S42RcR16RdA3R1bR1cR1dR10R1eR19RbA9S11S74R18S42RdR17ReA3R1cR1dSfR1eA1SfR1fA1SfR11A1R1RcA9VTR;S29SdS5fR11S4dS4cR19R1dS42ReR18RfA3A3R1eA2R18RdRcA5S84R1eR1fR12R20R1dR1bA6R2RcA5R1aA2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S29SdR11RfR8R7A5R9A2F_;F_;F_;F_;F_;F_;Ftp;Frho;FQ;FXk;FPosts;FR;Fs;FPre;FC;FJp;FJ;").
Hypothesis TR_JAF : ltac2:(tb__ "0|0|
S11OF_;S1bSeS11S4S28Q40A1A1S2cR6R3A1VTR;S29SdVJAv;R6A1R5R4R3A5R2A2F_;VTR;S29SdVJAFv;R7R6A2R5R4R3A5R2A2F_;FQ;Ftp;Frho;FA;Fnd;FPhi;").
Hypothesis CHVT : ltac2:(tb__ "0|1|
S4S2S0S0A2M0A1S4S2G0S0A2A1S6eS11S4S28Q40A1A1S6dZ5R3A2VTR;S29SdS1dVAInv;VCST;VXGL;VKc;S32VCST;R6R5A3R6R5R4S1cS70S51S6S67A3AaS66R3R2A5S5dSdS65R3R2S71VAInv;VCST;VXGL;VKc;S32VCST;A1S1cS53R6R5R4AaA5A2F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Hypothesis CUTV : ltac2:(tb__ "0|5|
SeS1bS5S2S0S12A2M0S11S4S28Q40A1A1M1S0G1S33S2S2S2SeS1bA2M2S5A2M3G0A2S3G3G0S3G2S5S3SeS1bR8R7A4R6A4R5A4S69A3S38S50R7R5A3S30S3bZ0S37S3G3G0S3G2S5S3SeS1bRaR9A4R8A4R7A4R6A2M4A2S3cG4R4A2A2VTR;S29SdVJAv;RaA1RbR7R6A5VFAM;R5R4A2A2F_;F_;F_;Ftp0;Fb;Ftp;Frho;Frv;Fk;Fnd;FT;").

Theorem arm_vt : ltac2:(tb__ "0|2|
S11S4S28Q40A1A1M0G0VTR;S29SdVJAFv;S34S45A2S4bR3R2A5VFAM;S37S3S2S2SeS1bA2M1S5A2S2S0S12A2S3G1S5S3SeS1bS4bS45A4U1A4S3S0S12S46S47Z11S48A2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros HPHI.
  pose proof avt_checks as (Cxf & CE & Cent & Cchk & Cta & Cdom & Ctvs & Cam & Cpd & Cptv & Cptv' & Cpbd & Cxk & Chand & Cpay & Cnb & Cbr & Cnp & Cnx & Cfb).
  pose proof avt_checks2 as (_ & _ & CLN & _).
  set (ndv := NDA tv_vt frL bd_vt (AHead pH true)).

  apply (TR_pre (SPA segs (JAv ndv) E_vt rho tp)).
  { intros w Hw. rewrite <- CE. apply (SPA_refacts_JA segs); [| exact Cfb |].
    - apply (SPA_axforms segs (JAv ndv) xf_vt rho E_hvt E_vt1 tp w Cxf).
      unfold ndv, tv_vt. apply (SPA_bd_permb segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue _ frL (bdA A1) bd_vt _ E_hvt rho tp w Cpbd).
      apply (SPA_tv_permb segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tvL _ frL (bdA A1) _ E_hvt rho tp w Cptv). exact Hw.
    - intros tr md _ HF1. apply Forall_app. split; [exact (room_vt_holds rho HF1) | exact HF1]. }
  apply TR_facts. intros HF.
  apply (TR_pureP _ (uval rho xLD <> 0)).
  { intros [tr [ms md]] [_ (Ai & kc & Hav & _ & _ & HT & _ & _ & (_ & _ & HZ) & _)]. cbn [nd_tv ndv] in HZ.
    pose proof (T_of_TPA NP rho0 rho Ai Hav ltac:(reflexivity) HT) as HTK.
    apply (lines_nz rho _ (topG (aa_geom Ai)) tv_vt HF CLN HTK HZ). unfold tv_vt. apply in_or_app. left. exact lines_in_kept_vt. }
  intros Hdnz.

  unfold ndv, tv_vt.
  apply (client_callT_k segs AInv CST XGL ALA HCST HXGL NP Kc rho0 P0 FB FF BX PTrue HKc HBX (P0_vt CST) PTrue (fun _ H => H) (fun _ _ _ H => H)
           HVT.Pre_vt (ndh h0 true HVT.nd0) PDk_vt NPH eq_refl eq_refl eq_refl TR TR_facts TR_ex TR_pre TR_callP CHVT eq_refl
           E_vt s_vt R_vt Xk_vt rho tp kept_vt passed_vt frL bd_vt brest_vt (AHead pH true) (FAM (efmeasA (E_hvt, ndA1, 1%nat, (RL, VLA 17 z0)) rho) tp0)
           Cxk Cent Cchk Cta Cdom Cnp Cnb Cbr Ctvs Cam).
  - rewrite Chand. apply (payA_of_bud_pay2 NP rho0 P0). exact Cpay.
  - exact Cpd.
  - intros Ai ms HF' HP0 Hav HBf HFF HN HD HZ HFR (rho1 & tp1 & md1 & HM) HT HTK.
    exact (HIN_vt rho ms Ai rho1 tp1 md1 HF' HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR).
  -
    intros [[Ld ndL] PsiL] rho' tp' Hd Hag HK _. rewrite Cnx in Hag.
    assert (HPHI' : tblB rho').
    { fact HF (SPUle (SVar 30) (SLit 140737479966720)) HtB. rewrite h_ule, uval_lit in HtB by lia.
      fact HF (SPUle (SLit 140735332483072) (SVar 30)) HtA. rewrite h_ule, uval_lit in HtA by lia.
      destruct (lines_blk rho _ (uval rho (SVar 30)) HF CLN ltac:(split; [reflexivity | lia])) as (_ & HiC & HcK & Hk32 & _ & HdT).
      apply (tblB_kept rho rho' (V_B_agree rho rho' Hag)); [| exact HiC | exact HcK | exact HPHI].
      apply (keptK_lines CST FB FF rho0 rho kept_vt frL rho' HK lines_in_kept_vt Hdnz); [lia | unfold B32, Lib_vec_reserve.B32; lia]. }
    fact HF (SPUle xLC vLEN) HcL. rewrite h_ule in HcL. fact HF (SPUle vLEN (SLit 67108864)) HL26. rewrite h_ule, uval_lit in HL26 by lia.
    fact HF (SPUlt pI xLC) HiC. rewrite h_ult in HiC.
    pose proof avt_checks_nd as (Cndo & Cndf & CTo & CTf). pose proof avt_checks_back as (Bo & Bf & Tio & Tif & Rwf & Rsd & Rnx & RT & Rfb).
    cbn [PDk_vt liftPD PDh HVT.Posts_vt map In fst snd] in Hd. destruct Hd as [Hd|[Hd|[]]]; injection Hd as <- <- <-; cbn [fst snd].
    +
      rewrite CTf, Cndf.
      apply (TR_pre (SPA segs (JAv nd_vt_f) T_vt_f rho' tp')).
      { intros w Hw. rewrite <- Tif. apply SPA_tidy. exact (SPA_axforms segs (JAv nd_vt_f) (xfb_vt T_vt_f0) rho' T_vt_f0 B_vt_f tp' w Bf Hw). }
      apply (CUTV T_vt_f nd_vt_f 1%nat (RL, VLA 10 z0) rho' tp'); [right; left; reflexivity | exact HPHI' |].
      apply (VLA_lt rho rho' 17 10 z0 E_hvt T_vt_f ndA1 nd_vt_f 1%nat 1%nat); [symmetry; apply (proj1 Hag); reflexivity | symmetry; apply (proj1 Hag); reflexivity | exact HiC | lia | unfold z0; rewrite uval_lit by lia; lia | lia | lia].
    +
      rewrite CTo, Cndo.
      apply (TR_pre (SPA segs (JAv nd_vt_ok) T_vt_ok rho' tp')).
      { intros w Hw. rewrite <- RT. apply (SPA_refacts_JA segs); [| exact Rfb |].
        - apply (SPA_restate segs (JAv nd_vt_ok) rho' T_vt_ok1 S_vt_okR tp' w _ _ Rwf Rsd Rnx).
          + constructor; [|constructor]. cbn [fst snd]. apply sll1_add2_eq.
          + constructor.
          + rewrite <- Tio. apply SPA_tidy. exact (SPA_axforms segs (JAv nd_vt_ok) (xfb_vt T_vt_ok0) rho' T_vt_ok0 B_vt_ok tp' w Bo Hw).
        -
          intros tr md _ HF1. pose proof avt_checks3 as (M1 & M2 & M3 & M4 & M5 & M6).
          pose proof (holds_mem _ _ _ HF1 M1) as F1. pose proof (holds_mem _ _ _ HF1 M2) as F2. pose proof (holds_mem _ _ _ HF1 M3) as F3. pose proof (holds_mem _ _ _ HF1 M4) as F4.
          pose proof (holds_mem _ _ _ HF1 M5) as F5. pose proof (holds_mem _ _ _ HF1 M6) as F6.
          rewrite h_ule in F1, F2, F3, F4, F5, F6. rewrite uval_lit in F4, F5, F6 by lia.
          pose proof (uval_range rho' pPOS) as RP. pose proof (uval_range rho' pLNL) as RL. pose proof (uval_range rho' c_avt) as RC. pose proof (uval_range rho' pNX) as RN.
          rewrite uval_add_small in F3 by lia.
          apply Forall_app. split; [|exact HF1]. constructor; [|constructor]. unfold rate_t1, t1, pE0. apply (proj2 (h_ule _ _ _)).
          rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia.
          rewrite uval_add_small by (rewrite uval_add_small, uval_lit by lia; lia). rewrite uval_add_small by lia. rewrite uval_lit by lia. lia. }
      apply TR_facts. intros HFo. pose proof avt_checks_pay as (PP1 & PP2 & PPay & _ & _ & _).
      apply (TR_pre (SPA segs (JAv nd_vt_okX) T_vt_ok rho' tp')).
      { intros w Hw. unfold nd_vt_okX, nd_vt_ok in *.
        exact (SPA_bd_repay AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tv_vt_ok frL (AHead pH true) bd_vt_ok comm_vt Xs_vt Ys_vt bdX_vt _ T_vt_ok rho' tp' w PP1 PP2 HFo PPay Hw). }
      apply (CUTV T_vt_ok nd_vt_okX 1%nat (RL, VLA 10 z0) rho' tp'); [left; reflexivity | exact HPHI' |].
      apply (VLA_lt rho rho' 17 10 z0 E_hvt T_vt_ok ndA1 nd_vt_okX 1%nat 1%nat); [symmetry; apply (proj1 Hag); reflexivity | symmetry; apply (proj1 Hag); reflexivity | exact HiC | lia | unfold z0; rewrite uval_lit by lia; lia | lia | lia].
Qed.
End X.

Section Safety.
Variable ok : world -> Prop.
Hypothesis Hok : ltac2:(tb__ "0|0|
S26SdVKc;Vok;A3").
Hypothesis AC : ltac2:(tb__ "0|0|
S77SdS76VAInv;VCST;VXGL;A5").
Variable FAMQ : list word -> assn.
Hypothesis XLATCH : ltac2:(tb__ "0|1|
S11S4S28Q40A1A1M0G0S2eSdVok;S29SdVJAFv;S34S49A2S6bR3R2A5VFAMQ;R1A1A4Ftp0;Ftp;Frho;").
Hypothesis XLATCHE2 : ltac2:(tb__ "0|1|
S11S4S28Q40A1A1M0G0S2eSdVok;S29SdVJAFv;S34S4aA2S6cR3R2A5VFAMQ;R1A1A4Ftp0;Ftp;Frho;").

Lemma CHVT_T : ltac2:(tb__ "0|1|
S4S2S0S0A2M0A1S4S2G0S0A2A1S6eS11S4S28Q40A1A1S6dZ5R3A2S2eSdVok;S29SdS1dVAInv;VCST;VXGL;VKc;S32VCST;R6R5A3R6R5R4S1cS70S51S6S67A3AaS66R3R2A5S5dSdS65R3R2S71VAInv;VCST;VXGL;VKc;S32VCST;A1S1cS53R6R5R4AaA5A4F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Proof.
  intros FBc FFc BXc rho1 tp1 HB. unfold PDk_vt.
  eapply (sum_PostsC_k segs AInv CST XGL Kc (P0_vt CST) PTrue HVT.Pre_vt (ndh h0 true HVT.nd0) (PDh HVT.Posts_vt h0 true) NPH); [|exact Hok|exact HB].
  intros ok' FBc' FFc' BXc' rho2 tp2 Hok' HB'.
  eapply (JA_frame_sum segs AInv CST XGL ALA Kc (P0_vt CST) PTrue HVT.Pre_vt HVT.nd0 HVT.Posts_vt NPH h0 true h0_ltH HamC_vt HamPD_vt (P0_vt_mono CST) ok'); [|exact HB'].
  intros FBc'' FFc'' BXc'' rho3 tp3 HB''. exact (handle_vt_sum AInv CST XGL ALA HCST HXGL HXpow LFLAG LFSH Kc HKc FBc'' FFc'' BXc'' HB'' rho3 ok' Hok' AC tp3).
Qed.

Lemma CUTV_T : ltac2:(tb__ "0|5|
SeS1bS5S2S0S12A2M0S11S4S28Q40A1A1M1S0G1S33S2S2S2SeS1bA2M2S5A2M3G0A2S3G3G0S3G2S5S3SeS1bR8R7A4R6A4R5A4S69A3S38S50R7R5A3S30S3bZ0S37S3G3G0S3G2S5S3SeS1bRaR9A4R8A4R7A4R6A2M4A2S3cG4R4A2A2S2eSdVok;S29SdVJAv;RaA1RbR7R6A5VFAMQ;R4A1A4F_;F_;F_;Ftp0';Fb;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof.
  intros T nd k rv rho tp b tp0' Hin Hphi _.
  apply (triple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisV k) ok nd T rho tp _ Hphi).
  apply (cfg_sound_JAF segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc PhisV PhisV_reads 200%nat cps_arm NP (map efdrop cutsT2) (map efdrop exitsT2) ok (FAMQ tp0') Hok
           (ejcertAF_jcertAF segs NP PhisV _ _ _ _ _ ecertT_ok)); [| apply in_map_iff; exists (T, nd, k, rv); split; [reflexivity | exact Hin]].
  intros X ndX kX rho1 tp1 HinX. apply in_map_iff in HinX as ([[[X' nd'] k'] rv'] & E & HinX). cbn in E. injection E as <- <- <-.
  cbn [exitsT2 exitsT In app] in HinX. destruct HinX as [E|[E|[]]]; injection E as <- <- <- <-; cbn [efdrop fst snd].
  - eapply triple_conseq; [| intros w Hw; right; exact Hw | exact (XLATCH rho1 tp1 tp0')].
    intros w Hw. unfold ndX0, ndL. apply (SPA_tv_permb_F segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tblB tv_vt tvL frL (bdX 0) (AHead pH true) X_latch rho1 tp1 w (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 avt_checks))))))))))). exact Hw.
  - eapply triple_conseq; [| intros w Hw; right; exact Hw | exact (XLATCHE2 rho1 tp1 tp0')].
    intros w Hw. unfold ndXE, ndL. apply (SPA_tv_permb_F segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tblB tv_vt tvL frL [LAX 0; LAXK 0] (AHead pH true) X_latchE2 rho1 tp1 w (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 avt_checks))))))))))). exact Hw.
Qed.

Theorem arm_vt_T : ltac2:(tb__ "0|1|
S11S4S28Q40A1A1M0G0S2eSdVok;S29SdVJAFv;S34S45A2S4bR3R2A5VFAMQ;R1A1A4Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0.
  exact (arm_vt (triple segs ok) (fun _ tp0 => FAMQ tp0) (TRs_facts segs ok) (TRs_ex segs ok) (TRs_pre segs ok) (TRs_pureP segs ok) (call_soundPA3 segs ok)
           (fun Phi nd A rho tp Q H => triple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue Phi ok nd A rho tp Q H)
           CHVT_T CUTV_T rho tp tp0).
Qed.
End Safety.

Section Existence.
Hypothesis ACX : ltac2:(tb__ "0|0|
S78SdS76VAInv;VCST;VXGL;A5").
Variable FAM : ltac2:(tb__ "0|0|
S0S4S28Q40A1A1S2cF_;F_;").
Hypothesis FAM_mono : ltac2:(tb__ "0|0|
S0S0S4S28Q40A1A1S2fS3bR4R3A2VFAM;R5R3R2A3VFAM;R5R4R3A3F_;F_;Fw;Ftp0;Fb';Fb;").
Hypothesis XLATCH : ltac2:(tb__ "0|2|
S11S4S28Q40A1A1M0G0S2dSdS29SdVJAFv;S34S49A2S6bR3R2A5VFAM;S37S3S2S2SeS1bA2M1S5A2S2S0S12A2S3G1S5S3SeS1bS6bS49A4U1A4S3S0S12S46S47Z1S48A2A4A4R3A2R1A2A3Ftp0;Ftp;Frho;").
Hypothesis XLATCHE2 : ltac2:(tb__ "0|2|
S11S4S28Q40A1A1M0G0S2dSdS29SdVJAFv;S34S4aA2S6cR3R2A5VFAM;S37S3S2S2SeS1bA2M1S5A2S2S0S12A2S3G1S5S3SeS1bS6cS4aA4U1A4S3S0S12S46S47Z1S48A2A4A4R3A2R1A2A3Ftp0;Ftp;Frho;").

Lemma CHVT_E : ltac2:(tb__ "0|1|
S4S2S0S0A2M0A1S4S2G0S0A2A1S6eS11S4S28Q40A1A1S6dZ5R3A2S2dSdS29SdS1dVAInv;VCST;VXGL;VKc;S32VCST;R6R5A3R6R5R4S1cS70S51S6S67A3AaS66R3R2A5S5dSdS65R3R2S71VAInv;VCST;VXGL;VKc;S32VCST;A1S1cS53R6R5R4AaA5A3F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Proof.
  intros FBc FFc BXc rho1 tp1 HB. unfold PDk_vt.
  eapply (sum_PostsC_k_ex segs AInv CST XGL Kc (P0_vt CST) PTrue HVT.Pre_vt (ndh h0 true HVT.nd0) (PDh HVT.Posts_vt h0 true) NPH); [|exact HB].
  intros FBc' FFc' BXc' rho2 tp2 HB'.
  eapply (JA_frame_sum_ex segs AInv CST XGL ALA Kc (P0_vt CST) PTrue HVT.Pre_vt HVT.nd0 HVT.Posts_vt NPH h0 true h0_ltH HamC_vt HamPD_vt (P0_vt_mono CST)); [|exact HB'].
  intros FBc'' FFc'' BXc'' rho3 tp3 HB''. exact (handle_vt_sum_ex AInv CST XGL ALA HCST HXGL HXpow LFLAG LFSH Kc HKc FBc'' FFc'' BXc'' HB'' rho3 ACX tp3).
Qed.

Lemma CUTV_E : ltac2:(tb__ "0|5|
SeS1bS5S2S0S12A2M0S11S4S28Q40A1A1M1S0G1S33S2S2S2SeS1bA2M2S5A2M3G0A2S3G3G0S3G2S5S3SeS1bR8R7A4R6A4R5A4S69A3S38S50R7R5A3S30S3bZ0S37S3G3G0S3G2S5S3SeS1bRaR9A4R8A4R7A4R6A2M4A2S3cG4R4A2A2S2dSdS29SdVJAv;RaA1RbR7R6A5VFAM;R5R4A2A3F_;F_;F_;Ftp0';Fb;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof.
  intros T nd k rv rho tp b tp0' Hin Hphi Hm.
  apply (etriple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisV k) nd T rho tp _ Hphi).
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (FAM_mono _ b tp0' w ltac:(apply Z.lt_le_incl; exact (proj2 Hm)) Hw) |].
  apply (cfg_complete_JAF_b segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc PhisV PhisV_reads 200%nat cps_arm NP cutsT2 exitsT2 (fun b w => FAM b tp0' w)
           (fun b b' w Hb Hw => FAM_mono b b' tp0' w Hb Hw) ecertT_ok); [|exact Hin].
  intros X ndX kX rvX rho1 tp1 HinX. cbn [exitsT2 exitsT In app] in HinX. destruct HinX as [E|[E|[]]]; injection E as <- <- <- <-.
  - eapply etriple_conseq; [| intros w Hw; right; exact Hw | exact (XLATCH rho1 tp1 tp0')].
    intros w Hw. unfold ndX0, ndL. apply (SPA_tv_permb_F segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tblB tv_vt tvL frL (bdX 0) (AHead pH true) X_latch rho1 tp1 w (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 avt_checks))))))))))). exact Hw.
  - eapply etriple_conseq; [| intros w Hw; right; exact Hw | exact (XLATCHE2 rho1 tp1 tp0')].
    intros w Hw. unfold ndXE, ndL. apply (SPA_tv_permb_F segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tblB tv_vt tvL frL [LAX 0; LAXK 0] (AHead pH true) X_latchE2 rho1 tp1 w (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 avt_checks))))))))))). exact Hw.
Qed.

Theorem arm_vt_E : ltac2:(tb__ "0|2|
S11S4S28Q40A1A1M0G0S2dSdS29SdVJAFv;S34S45A2S4bR3R2A5VFAM;S37S3S2S2SeS1bA2M1S5A2S2S0S12A2S3G1S5S3SeS1bS4bS45A4U1A4S3S0S12S46S47Z11S48A2A4A4R3A2R1A2A3Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0.
  exact (arm_vt (etriple segs) FAM (TRe_facts segs) (TRe_ex segs) (TRe_pre segs) (TRe_pureP segs) (call_completePA3 segs)
           (fun Phi nd A rho tp Q H => etriple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue Phi nd A rho tp Q H)
           CHVT_E CUTV_E rho tp tp0).
Qed.
End Existence.
End Sum.
End Lib_load_obj_avt_pf.

(* [comment removed for export] *)
Module Lib_load_obj_hv4.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "true"; "cons"; "bool"; "app"; "nat"; "nil"; "prod"; "pair"; "list"; "Some"; "fst"; "S"; "option"; "length"; "negb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "apply_axforms"; "AXUnbase"; "AXSplit"; "AXRebase"; "AXMerge"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "sv"; "sprop"; "SAlu"; "sobj"; "SPUle"; "sprop_eqb"; "ss_facts"; "ss_objs"; "DUnknown"; "SPEq"; "SVar"; "ss_next"; "valuation"; "SPUlt"; "ob_cells"; "sv_eqb"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "ax_base"; "axwf"; "g8"; "has_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fc.Lib_load_obj_hv4"; "s_o1c"; "E_o1c"; "R_o1"; "brest_o1"; "kept_o1"; "Xk_o1"; "E_o1r"; "T_op0_0"; "T_op1_0"; "bd_o1"; "payC_o1"; "B_op0"; "B_op1"; "PDk_o1"; "T_op0"; "T_op0r"; "T_op1"; "T_op1r"; "X_1"; "d_avw"; "hand_o1"; "payX_o1"; "payY_o1"; "reo_chk4"; "tv_o1"; "tv_op0"; "tv_op1"; "xfb_o1"; "avw_base"; "bd_op1"; "bdrest_o1"; "k_avw"; "nd_op0"; "nd_op1"; "passed_o1"; "s128"; "vD1"; "vK1"; "xf_o1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_hvkit"; "oidx"; "extra_hv"; "s1A"; "robjs_chkR"; "sel_front"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs"; "vF"; "g5"; "vDp"; "NP"; "vLEN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue"; "frL"; "V_B"; "A1"; "LA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fc.Lib_load_obj_hv4.OP1"; "Pre_op"; "P_op0"; "P_op1"; "PD_op"; "nd0"; "nd0'"; "nd1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bitem"; "bd_subst"; "bd_below"; "bd_wpos"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_hv3"; "h0"; "tv_keep"; "bd_keep"; "nd_keep"; "objs_nl"; "sh_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f7.Lib_load_obj_hv3m"; "E_o1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "NDA"; "ndesc"; "AHead"; "am_subst"; "nd_am"; "nd_bd"; "nd_tv"; "nd_below"; "am_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_hv"; "optL'"; "X_hv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop"; "pH"; "xLC"; "alA"; "bA"; "pI"; "xLD"; "xLK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs"; "kb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit2"; "lines_chk"; "robjs_chkC"; "xextraLO"; "xrs_chkC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG"; "bd_permb"; "tv_permb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.TobjJAH"; "ndh"; "PDh"; "@Stdlib.Lists.List"; "existsb"; "forallb"; "In"; "filter"; "@Stdlib.ZArith.BinInt.Z"; "sub"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro"; "ax_tidy"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_subA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "import_tv"; "tv_sub_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC";
"T_afterA3"; "pdescA"; "xrs_inclb"; "pd_okA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF"; "V_below"; "bud_pay2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "SHADOW_OFF"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud"; "AK1"; "LAK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "wsub_dom_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK"; "liftPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "call_checkTA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS"; "local_ok"; "shadow_release_stateA"; "shadow_reopen_stateA"; "shobj"; "@Stdlib.PArith.BinPos.Pos"; "leb"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR TobjJAS TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require ObjEmptyA PinA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.TobjJAH OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.ObjZeroA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ObjEmptyA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.PinA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.AddCellsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_opt_push1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_defs Lib_load_obj_pro.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eo.Lib_load_obj_pro2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_disp OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_hv0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_hv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_hvj OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_hvkit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_hv3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f7.Lib_load_obj_hv3m.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr LOAddr LOLAddr HVAddr.

Module OP1. Include Lib_opt_push1. End OP1.
Definition avw_t : T3 := v_avw vsP.
Definition d_avw : sv := t_d avw_t. Definition c_avw : sv := t_c avw_t. Definition k_avw : sv := t_k avw_t.

Definition E_o1r : axst := Eval vm_compute in shadow_release_stateA E_o1 (objs_nl E_o1) 110 [(160, 4); (176, 4)].
Definition xf_o1 (T : axst) : list axform := ltac2:(tb__ "0|a|
S3S11S14S57S59S5eVT;A3M0S17N80M1A1A2S3S11S13G0G1A2S7S11A1M2A3A3SaS11A1M3S83S12VT;R1A2A1S29S3S11S13S57S88S17Z98M4A1R1A3G4A2G2A3G3S83S12R2R1A2A1S29S57S5cS17Z20A1R1A3S6S5S11R5S5S11R3S3S11S14R1S17Za0M5A1A2S3S11S14SdR1A1M6S17Za4A1A2S3S11S14SdG6A1M7S17Zb0M8A1A2S3S11S14SdG7A1M9S17Zb4A1A2S3S11S13G6G5A2S3S11S13G9G8A2G2A3A3A3A3A3A3A3A3Tj;TT2;Tpre2;TT1;Tpre1;").
Definition E_o1c : axst := Eval vm_compute in optL' (apply_axforms E_o1r (xf_o1 E_o1r)).
Definition s_o1c : wsub := ltac2:(tb__ "0|1|
S3S8S72S18A2M0S9S72S18S73S85A4S3G0S9S72S18P13S1aS70S5eS17Z80A1A3A4SadPaS2aS31A1S2aS65A1A3A3A3").
Definition R_o1 : list sobj := Eval vm_compute in optR (entails_frA E_o1c OP1.Pre_op s_o1c).
Definition PDk_o1 : list pdescK := ltac2:(tb__ "0|0|
SafS95S68S73S2A3A1").

Definition passed_o1 : list (sv * sv) := ltac2:(tb__ "0|1|
S3S8S18S18A2M0S9S18S18S43S8dZ4S4fA2A4S7G0A1A3").
Definition kept_o1 : list (sv * sv) := Eval vm_compute in skipn 1 tv_keep.
Definition tv_o1 : list (sv * sv) := kept_o1 ++ passed_o1.
Definition hand_o1 : list bitem := Eval vm_compute in bd_subst s_o1c (nd_bd (ndh h0 true OP1.nd0)).
Definition bdrest_o1 : list bitem := Eval vm_compute in firstn 2 bd_keep ++ skipn 2 bdrest_vr.
Definition bd_o1 : list bitem := Eval vm_compute in (firstn 2 bdrest_vr ++ LA (A1 - 72) :: LAK AK1 :: bdrest_o1).
Definition brest_o1 : list bitem := ltac2:(tb__ "0|0|
S3S6cS64S9aS63Z60A2A1S3S6cSacSabA1S4eA3A3").
Definition payX_o1 : list bitem := Eval vm_compute in [nth 0 bdrest_vr (LA 0); LA (A1 - 72)].
Definition payY_o1 : list bitem := Eval vm_compute in [nth 0 hand_o1 (LA 0); LA (A1 - 96)].
Definition payC_o1 : list bitem := Eval vm_compute in (nth 1 bdrest_vr (LA 0) :: LAK AK1 :: bdrest_o1).
Definition Xk_o1 : list (sv * sv) := Eval vm_compute in List.filter (fun r => negb (sv_eqb (fst r) d_avw)) (ax_X E_o1c).

Lemma hv4_checks_rel : ltac2:(tb__ "0|9|
S1S0SaS1bA1S1fS2aS79A1M0A1S5S1bS77S79A1M1S3S1bSb4S5dZ4M2Z1eM3S26S78S79A1A1M4S20A5S7S1bA1A3A3A3S1S0S18S2cS79A1S17Sa9A1A3S1S0S4S2fS3S19S21S2eS5dA1S5cA2S3S19S1cS22S5dA1S17S9aS9bZ2Z3dA2Z1A2A1A2S7S19A1A3A3S1eG0A1M5A2S2A3S1S0S4S97S8S71S71A2M6Sb1G4S20G2G3A4S3G6S9S71S71Za0G2A4S3G6S9S71S71Zb0G2A4S7G6A1A3A3M7A3S2A3S1S0S4S81S23G0A1M8S76A2S2A3S1S0S4S5aG5S74S61S58G1A5S2A3S1S0S4S8eG5A1S2A3S1S0S29Sb2S79G1P6eG7A4S36A3S1S0S4Sa7G8S62A2S2A3S1S0S4S96S19S1dS25S89S86A2A1G5A3S2A3S1S0S4S96S19S1dS1cS86S60A2A1G5A3S2A3S0S4S96S19S1dS1cS60S17Z4000000A1A2A1G5A3S2A3A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Lemma hv4_checks_o1 : ltac2:(tb__ "0|b|
S1S0SeS29A1S12S36S56S36A1A2SbS29S31A2A3S1S0SeSaS1bA1M0A1S9fS31S65S30A3SbG0S32A2A3S1S0S4S9eS31S65S30S32SaaS8S8S29S7bA2M1S24S24OF_;F_;M2A2M3S29G3ScS29S7bScG1G2R1A3A3Ld;S3dA4A5S2A3S1S0S4Sb0S5fS30A2S2A3S1S0S4SaeS30Sa0A2S2A3S1S0S4Sa2S30S52S80S94S73S2S69A3M4A1A3S2A3S1S0S4S82S7dS30S7eG4A1A2S7cS85S2A2M5A2S2A3S1S0S4S97S8Sa4G2A2M6G6Sa6S65Sa0S30S23S2aS31A1M7A1M8ScSa4G2R1A3A5Ld;S3dA3S2A3S1S0S4S93S74S48A2S2A3S1S0S4S92S75S39A2S2A3S1S0S4Sa5S35S2bS31A1A2S2A3S1S0SaS6cA1S6dS30S7fG4A1A2S44A3S1S0S4S92S39S5S6cS3aS45A3A2S2A3S1S0S4S92S5S6cS3aS46A3S5S6cS44S33A3A2S2A3S1S0S4S6fS3aA1S2A3S1S0S4Sa8S1eG7A1M9S17Z0MaA1GaS45S46A5S2A3S1S0S4S81G8S7aS48S61S39G5A4A2S2A3S1S0S4S6eG8S33A2S2A3S1S0S4Sb5S5fG8A2S2A3S1S0S4S8fG9S34S61S58S32A5S2A3S1S0S4S91G9S34S61S90S35A5S2A3S1S0S4S8eG9A1S2A3S1S0S4Sa7G8S62A2S2A3S1S0S18S8cS30PcA2S1aS70S5cS17Z2b8A1A3A3S1S0S18S8cS30P24A2S87A3S1S0S18S8cS30P21A2S1aS70S5cS17Za0A1A3A3S0S18S8cS30P22A2S1aS70S5cS17Zb0A1A3A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition T_op1_0 : axst := Eval vm_compute in T_afterA3 OP1.Pre_op E_o1c s_o1c R_o1 OP1.P_op1 Xk_o1.
Definition T_op0_0 : axst := Eval vm_compute in T_afterA3 OP1.Pre_op E_o1c s_o1c R_o1 OP1.P_op0 Xk_o1.
Definition isub_op1 : wsub := Eval vm_compute in import_subA s_o1c OP1.Pre_op OP1.P_op1 E_o1c.
Definition isub_op0 : wsub := Eval vm_compute in import_subA s_o1c OP1.Pre_op OP1.P_op0 E_o1c.
Definition vD1 : sv := Eval vm_compute in sv_subst isub_op1 (SVar 140).
Definition vC1 : sv := Eval vm_compute in sv_subst isub_op1 (SVar 141).
Definition vK1 : sv := Eval vm_compute in sv_subst isub_op1 (SVar 142).
Definition tv_op1 : list (sv * sv) := Eval vm_compute in (kept_o1 ++ import_tv isub_op1 (nd_tv (ndh h0 true OP1.nd1))).
Definition bd_op1 : list bitem := Eval vm_compute in (bd_subst isub_op1 (nd_bd (ndh h0 true OP1.nd1)) ++ brest_o1).
Definition tv_op0 : list (sv * sv) := Eval vm_compute in (kept_o1 ++ import_tv isub_op0 (nd_tv (ndh h0 true OP1.nd0'))).
Definition nd_op1 : ndesc := ltac2:(tb__ "0|0|
S7aS4aS61S4dS7cS85S2A2A4").
Definition nd_op0 : ndesc := ltac2:(tb__ "0|0|
S7aS49S61S33S7cS85S2A2A4").
Definition s128 : sv := SAlu ALU_ADD (SVar 10) (SLit (-640)).
Definition avw_base : sv := SAlu ALU_ADD vF (SLit 696).
Definition xfb_o1 (T : axst) : list axform := ltac2:(tb__ "0|a|
S3S11S13S57S53S1aS70S5eS17Z80M0A1A3VT;A3G0A2S3S11S13S57S4cS17Z0A1M1VT;A3N98A2S3S11S15S57S1aS70S5cS17Za0A1M2A3G1VT;A3A1S3S11S15S57S1aS70S5cS17Zb0A1M3A3G1VT;A3A1S7S11A1M4A3A3A3A3SaS11A1M5S83S12VT;R1A2A1S29S3S11S5bS3S6S57S59S5eR1A3S3S6S57S59S17N80A1R1A3S7S6A1M6A3A3SfS1bS1fS2aR1A1A1A2M7A2S3S11S16U0A1M8G4A3M9A3G5S83S12R2R1A2A1S29S5S11R4S5S11R2S3S11S5bS3S6S57S5cS17Z20A1R1A3S3S6S57S5cG2R1A3S3S6S57S5cS17Za4A1R1A3S3S6S57S5cG3R1A3S3S6S57S5cS17Zb4A1R1A3G6A3A3A3A3A3G7A2S3S11G8S3S11G8S3S11G8G9A3A3A3A3A3A3TT2;Tg1;TT1;Tpre;").
Definition B_op1 : axst := Eval vm_compute in optL' (apply_axforms T_op1_0 (xfb_o1 T_op1_0)).
Definition B_op0 : axst := Eval vm_compute in optL' (apply_axforms T_op0_0 (xfb_o1 T_op0_0)).
Definition T_op1r : axst := Eval vm_compute in ax_tidy B_op1.
Definition T_op0r : axst := Eval vm_compute in ax_tidy B_op0.
Definition X_1 : list (sv * sv) := ltac2:(tb__ "0|1|
S3S8S18S18A2M0S9S18S18S54S8dZ4S55A2A4S99G0G0S10S27ScS18S18R1A3S43A2A1Lr;S84A3A3").
Definition T_op1 : axst := Eval vm_compute in shadow_reopen_stateA T_op1r X_1 g5 4 30.
Definition T_op0 : axst := Eval vm_compute in shadow_reopen_stateA T_op0r X_1 g5 4 30.

Definition reo_chk4 (tv : list (sv * sv)) (X : list (sv * sv)) (Tb T : axst) : Prop := ltac2:(tb__ "0|2|
S1S0S18S2cVTb;A1S17Sa9A1A3S1S0S4S2fS3S19S21S2eS5dA1S5cA2S3S19S1cS22S5dA1S17S9aS9bZ2Z3dA2Z1A2A1A2S7S19A1A3A3S1eS2aVTb;A1M0A1M1A2S2A3S1S0S4Sa5VX;S2bVTb;A1A2S2A3S1S0S29Sb3VTb;VX;S5dZ4Z1eA5VT;A3S1S0S4S28S2aVT;A1A1S2A3S1S0S4S5aG1Vtv;S61S58S1fG0A1A5S2A3S0S4S8eG1A1S2A3A2A2A2A2A2A2").
Lemma hv4_checks_o1_nd : ltac2:(tb__ "0|6|
S1S0S7bS7aS5S8S18S18A2M0S34Sa1S9dS30S65S67S31A4M1S80S94S73S2S6bA3M2A1A2A3S61S5S6cS6dG1S7fG2A1A2S33A3S7dG1S7eG2A1A2A4S51A3S1S0S7bS7aS5G0S34Sa1S9dS30S65S66S31A4M3S80S94S73S2S6aA3M4A1A2A3S61S5S6cS6dG3S7fG4A1A2S33A3S7dG3S7eG4A1A2A4S50A3S1S0S29Sa3S65S31S30S32S67S35A6S38A3S1S0S29Sa3S65S31S30S32S66S35A6S37A3S1S0SeS29A1M5S12S38S4bS38A1A2SbS29S3cA2A3S1S0G5S12S37S4bS37A1A2SbS29S3bA2A3S1S0S29S9cS3cA1S41A3S1S0S29S9cS3bA1S3fA3S1S47S4aS42S41S40A4S1S47S49S42S3fS3eA4S1S0S4S2dS40A1S2A3S1S0S4S2dS3eA1S2A3S98G0S9S18S18S8aS8dZ10S8bA2A4S34A3A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. vm_compute. repeat split; try reflexivity. repeat (first [left; reflexivity | right]). Qed.
End Lib_load_obj_hv4.

(* [comment removed for export] *)
Module Lib_load_obj_land_pf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@Corelib.Init.Datatypes"; "list"; "bool"; "true"; "cons"; "app"; "prod"; "pair"; "Some"; "nil"; "option"; "nat"; "fst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "ss_next"; "sv"; "ss_facts"; "sprop"; "SVar"; "SLit"; "sobj"; "holds"; "cell"; "sstate"; "DUnknown"; "SAlu"; "eval"; "ob_base"; "ob_cells"; "ob_dflt"; "obj_hi_of"; "obj_lo_of"; "odefault"; "rw"; "sprop_below"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_X"; "ax_setS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "smatchA"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "uval"; "bitem"; "bd_below"; "BXok_d"; "bxt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop"; "T3"; "X_bodyN"; "datasA"; "t_d"; "t_k"; "O_dataA"; "v_acol"; "v_av"; "v_avn"; "v_avt"; "v_avtw"; "v_avw"; "v_co"; "v_fv"; "v_lc"; "v_li"; "v_mi"; "v_mm"; "v_pi"; "v_rp"; "v_sg"; "v_sh"; "v_tr"; "v_ts"; "vecs"; "vsP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue"; "frL"; "tblL"; "ldef"; "P0_lo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_land_chk"; "ENDOW"; "tv1"; "PhiP0"; "PhiP1"; "bdLand_a1"; "bdLand_b1"; "add_objs"; "add_objs_wf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "NDA"; "ANone"; "PTrue"; "JA"; "JA_pre"; "amode"; "nd_tv"; "ndesc"; "ok_frameKA"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "pow"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_sub"; "rho_absorb"; "wsub"; "in_ranges"; "wsub_get"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF"; "bud_le2"; "JAF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f6.Lib_load_obj_land"; "E_blr"; "tv_site"; "K0a"; "K0b"; "K1a"; "K1b"; "R_blr"; "E_blr0"; "T_blr0"; "T_blr1"; "XkB"; "s_landA"; "s_landAE"; "s_landBE"; "XR_after0"; "XR_after1"; "XR_body0"; "XR_body1"; "s_blr"; "s_landB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "etriple"; "triple"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs"; "NP"; "vF"; "vOUT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud"; "ndA1"; "ndLE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@Stdlib.Lists.List"; "In"; "forallb"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fc.Lib_load_obj_land_pf.Sum"; "emp_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "call_linkP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "J_ofPA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "FBx"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "FFx"; "pclMA"; "robjs_okF"; "xrs_okF"; "xrs_inclb"; "@LinuxProcessSemantics.LinuxProcessSem.Run";
"config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_exits"; "K_after0"; "K_afterE"; "X_bodyE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f7.Lib_load_obj_land_chk2"; "bdLand_a0"; "bdLand_b0"; "bd_bli"; "xfb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fc.Lib_load_obj_land_pf.BLRP"; "P0_blr"; "PDk_blr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro"; "fnodup"; "vARn"; "xnodup"; "blkAR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "axform"; "AXMerge"; "AXSplit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "payA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "AE_A"; "V_TOP"; "alloc_contractsA"; "alloc_contractsA_ex"; "alloc_lawsA"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "of_nat"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs"; "kb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_fuzz_iface"; "in_lits"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fc.Lib_load_obj_land_pf.BLR"; "Pre_blr"; "nd_pre"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve"; "B32"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_setX"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.ObjZeroA"; "zero_cells_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3"; "import_okPA3"; "import_postA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK"; "PostsCk"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eo.Lib_load_obj_pro2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_exits OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f6.Lib_load_obj_land OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_land_chk OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f7.Lib_load_obj_land_chk2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Module BLR. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.en.Lib_build_line_index_rom. End BLR.
Module BLRP. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_build_line_index_rom_pf. End BLRP.
Import ScanDoubleAddr VRAddr RA.ReallocAddr LOAddr LOLAddr.

Section Sum.
Variable AInv : ltac2:(tb__ "0|0|
SbbS10S4S30Q40A1A1S96OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
Sc2S3VAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
S2eSbcVCST;R1A2S1S67Z0R2A2S69R2SbdA2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S2eSbcVXGL;R1A2S1S67Z0R2A2S69R2SbdA2A2F_;Fa;").
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S4S9S9S2eS2eA2S2eA2A1").
Variable BX : bxt.
Hypothesis HBX : BXok_d 7 BX.
Variable PA : AA -> Prop.
Variable rho0 : valuation.
Let HTOP : InitState.segs_top segs <= IMG_HI := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eb.Lib_arena_alloc.HTOP_ok.
Let HNP : NP_okA NP := NP_okA_intro NP eq_refl.
Let P0 : ltac2:(tb__ "0|0|
S10OFr;") := ltac2:(tb__ "0|0|
S55VCST;VFB;VFF;A3").
Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S61VAInv;VCST;VXGL;S8eVKc;Vrho0;VP0;VFB;VFF;VBX;VPA;Vnd;Ac").
Let JAFv (Phi : valuation -> Prop) (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S72VAInv;VCST;VXGL;S8eVKc;Vrho0;VP0;VFB;VFF;VBX;VPA;VPhi;Vnd;Ad").

Hypothesis HXlits : ltac2:(tb__ "0|0|
S2eSc7R1A1SbcVXGL;R2A2F_;Fa;").

Hypothesis HPAany : ltac2:(tb__ "0|0|
SbbSbbVPA;R2A1S60R2A1VPA;R3A1F_;F_;FA';FA;").

Lemma SPA_zsub : ltac2:(tb__ "0|2|
S2cS10S28S28S1aS28SeS2eSeS4S19A1S4S30Q40A1A1S87S0SdS28A1M0Sb6RaS7Sb7Sb9R6S16R5A1A2ScSb7A1M1A3A2SbS28R9A2A3S0SdS1aA1SceS27RaA1R5R4A3SbS1aR9A2A3S0S5S26RaA1S6A3S0G0Sb6S2aRcRbA2S7Sb7Sb8R9A1G1A3A2SbS28RaA2A3S2bS3R10ReRfR6R5A6S2bS3R11RcR10R7R6A6F_;F_;F_;F_;F_;Fw;Ftp;Fcs;Fj;Fmid;Fi;FA3;FS2;FA1;FA;Frho;FJ;").
Proof.
  intros J rho A A1 S2 A3 i mid j cs tp w H1 H2 Hwf H3 Hw.
  apply (SPA_axforms segs J [AXMerge i] rho (ax_setS A1 S2) A3 tp w H3).
  apply (SPA_zero_cells segs J rho A1 j cs S2 tp w H2 Hwf).
  exact (SPA_axforms segs J [AXSplit i (SLit mid)] rho A A1 tp w H1 Hw).
Qed.

Definition emp_at (rho : valuation) (o : sobj) : Prop := ltac2:(tb__ "0|2|
S1S0S4S19A1S1fVo;A1ScS19A1A3S1S0S23S20Vo;A1S1bA3S1S0S2eS21Vrho;Vo;A2S22Vrho;Vo;A2M0A3S1S67Z0S68S31Q40S1dVrho;S1eVo;A1A2A2G0A2M1A2S67G1S6aZ2Z40A2A2A2A2A2A2").
Lemma SPA_add_objs : ltac2:(tb__ "0|0|
S2cS10S4S17A1S28S4S30Q40A1A1S87S0S5S5dR3R4A2S6A3S8bS17S99R6A1R5A3S2bS3R8R5R7R4R3A6S2bS3R9S5cR6R7A2R8R5R4A6F_;F_;F_;Fw;Ftp;FA;Fds;Frho;FJ;").
Proof.
  intros J rho ds. induction ds as [|o r IH]; intros A tp w Hwf Hemp Hw; [exact Hw|]. cbn [add_objs].
  cbn [add_objs_wf] in Hwf. apply andb_prop in Hwf as [Hwf H3]. apply andb_prop in Hwf as [H1 H2].
  apply Forall_cons_iff in Hemp as [(E1 & E2 & E3 & E4) Hemp].
  apply (IH _ tp w H3 Hemp). apply (SPA_add_empty segs J rho A o tp w H1 E1 E2 H2); [|exact Hw]. intros _. split; [exact E3 | exact E4].
Qed.
Lemma emp_data : ltac2:(tb__ "0|1|
S10S38S2eS1S69Z0M0R1A2S69R1Z1000A2A2S0S2eS33R4S3bR3A1A2G0A3S0S2eS33R5S3cR4A1A2G0A3S99R6S3dR5R4A2A2F_;F_;F_;Fe;Ft;Frho;").
Proof.
  intros rho t e He Hd Hk. unfold emp_at, O_dataA, obj_hi_of, obj_lo_of. cbn [ob_cells ob_dflt ob_hi ob_lo ob_base].
  split; [reflexivity|]. split; [reflexivity|]. rewrite soff_lit_small by lia.
  pose proof (uval_range rho (t_k t)) as Rk.
  assert (EK : uval rho (kb e (t_k t)) = e * uval rho (t_k t)). { unfold kb. apply uval_mul_lit; [lia|]. rewrite Hk. lia. }
  split.
  - unfold soff. rewrite bv_signed_U. change (bv_unsigned (eval rho (kb e (t_k t)))) with (uval rho (kb e (t_k t))). rewrite EK, Hk.
    rewrite Z.mul_0_r. reflexivity.
  - change (bv_unsigned (eval rho (t_d t))) with (uval rho (t_d t)). rewrite Hd. lia.
Qed.
Lemma datas_emp : ltac2:(tb__ "0|1|
S10S50S38S94S38R1S7S38S3fR2A1S7S38S43R2A1S7S38S40R2A1S7S38S41R2A1S7S38S42R2A1S7S38S3eR2A1S7S38S4dR2A1S7S38S48R2A1S7S38S45R2A1S7S38S49R2A1S7S38S4cR2A1S7S38S47R2A1S7S38S46R2A1S7S38S4aR2A1S7S38S44R2A1S7S38S4bR2A1S7S38S4eR2A1S7S38S4fR2A1ScS38A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3S1S0S2eS33R4S3bR2A1A2Z0M0A3S0S2eS33R4S3cR2A1A2G0A3A2F_;Ft;S8bS17S99R3A1S3aR2A1A3F_;Fv;Frho;").
Proof.
  intros rho v H. unfold datasA.
  repeat (apply Forall_cons; [apply emp_data; [lia | match goal with |- uval _ (t_d ?t) = 0 => apply (proj1 (H t ltac:(cbn; tauto))) end
                                                     | match goal with |- uval _ (t_k ?t) = 0 => apply (proj2 (H t ltac:(cbn; tauto))) end] |]). apply Forall_nil.
Qed.

Lemma datas_emp_land : ltac2:(tb__ "0|0|
S10S6eS2fS94S2fR1S8cSeS2fSc4S8dU190U36A2A4A3S0S12S70R3R2A2S16Z0A1A3F_;Fx;S8bS17S99S6cR3R2A2A1S3aS51A1A3F_;Fs;Frho;").
Proof.
  intros rho s Hs. apply datas_emp. intros t Ht.
  assert (Z0 : forall x : positive, In x (map Pos.of_nat (seq 400 54)) -> uval (rho_sub rho s) (SVar x) = 0).
  { intros x Hx. unfold uval. rewrite <- eval_subst. cbn [sv_subst]. rewrite (Hs x Hx). apply (uval_lit rho 0). lia. }
  cbn in Ht. unfold vsP, t3 in Ht.
  repeat (destruct Ht as [<-|Ht]; [split; apply Z0; lazy; tauto|]). destruct Ht.
Qed.

Lemma land_bodyN : ltac2:(tb__ "0|2|
S4S34A1S10S4S30Q40A1A1S87S0S5S35S11S27S78A1M0A1R4A2S6A3S0S5S71S13G0A1S5bR5A3S6A3S59R5A1S2bS3VJAv;S5eS57S52S8S34R7S56A3S5fA4A1S84R6R5R4A6S1S53S6cR7S86A2M1A1S2bS3VJAFv;S53S91A2S39G1R6R5A6A2F_;F_;F_;F_;Fw;Ftp;Frho;Fbd0;").
Proof.
  intros bd0 rho tp w Hbd Hbud HPhi Hw.
  pose proof pipe_b1 as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18).
  pose proof land_checks_b1 as (Cent & Cid & Cnp & Ctv & Cfr & Cam & Cperm & Cnull & Ctvb & Cfrb & Cbd & Cz).
  pose proof (SPA_axforms segs _ XF_b1 rho XR_body1 C9_b1 tp w P1 Hw) as Hw1.
  pose proof (SPA_zsub _ rho C9_b1 Za1_b1 Zs1_b1 C10_b1 _ _ _ _ tp w P2 P3 P4 P5 Hw1) as Hw2.
  pose proof (SPA_zsub _ rho C10_b1 Za2_b1 Zs2_b1 C11_b1 _ _ _ _ tp w P6 P7 P8 P9 Hw2) as Hw3.
  pose proof (SPA_zsub _ rho C11_b1 Za3_b1 Zs3_b1 C12_b1 _ _ _ _ tp w P10 P11 P12 P13 Hw3) as Hw4a.
  pose proof (SPA_zsub _ rho C12_b1 Za4_b1 Zs4_b1 C13_b1 _ _ _ _ tp w P14 P15 P16 P17 Hw4a) as Hw4. rewrite P18 in Hw4.
  pose proof (JA_add_nulls segs AInv CST XGL NP Kc rho0 P0 FB FF BX PA tv1 nulls_b1 frL (bd0 ++ ENDOW) K1b rho tp w Cnull Hw4) as Hw6.
  pose proof (SPA_tv_permb segs AInv CST XGL NP Kc rho0 P0 FB FF BX PA (tv1 ++ nulls_b1) tvLand_b1 frL (bd0 ++ ENDOW) ANone K1b rho tp w Cperm Hw6) as Hw7.
  pose proof (JA_arena_init segs AInv CST XGL NP Kc rho0 P0 FB FF BX PA HBX tvLand_b1 frL bd0 K1b rho tp w Hw7) as Hw8.
  assert (Hw9 : SPA segs (JAv ndA1) M_bodyN (rho_sub rho s_landB) tp w).
  { apply (SPA_entails_JA2 segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PA HKc K1b M_bodyN s_landB (NDA tvLand_b1 frL bd0 (AHead (SLit 0) true)) ndA1 rho tp w
             Cent Cid Cnp); cbn [nd_tv nd_fr nd_bd nd_am ndA1 ndLE ndL].
    - unfold nd_below. cbn [nd_tv nd_fr nd_bd nd_am]. rewrite Ctvb, Cfrb, Hbd. reflexivity.
    - exact Ctv.
    - exact Cfr.
    - change (bud_le2 (ss_facts (ax_S K1b)) (bd_subst s_landB (nd_bd ndA1)) bd0 = true). rewrite Cbd. exact Hbud.
    - exact Cam.
    - exact Hw8. }
  assert (Hw10 : SPA segs (JAv ndA1) X_bodyN (rho_sub rho s_landB) tp w).
  { rewrite <- (proj1 add_datas_b1). apply (SPA_add_objs _ _ (datasA vsP) M_bodyN tp w (proj2 add_datas_b1)); [|exact Hw9].
    apply datas_emp_land. intros x Hx. apply sv_eqb_sound. exact (proj1 (forallb_forall _ _) Cz x Hx). }
  assert (HT : tblL (rho_sub rho s_landB)).
  { destruct HPhi as [(T & H1 & H2 & H3) HP0].

    split.
    2: { intros z Hz. assert (ED' : uval (rho_sub rho s_landB) xLD = uval rho iD) by (unfold uval; rewrite <- eval_subst; reflexivity).
         assert (EK' : uval (rho_sub rho s_landB) xLK = uval rho iK) by (unfold uval; rewrite <- eval_subst; reflexivity).
         change (rm (rho_sub rho s_landB)) with (rm rho). rewrite ED', EK' in Hz. exact (HP0 z Hz). }
    exists T.
    assert (ED : uval (rho_sub rho s_landB) xLD = uval rho iD) by (unfold uval; rewrite <- eval_subst; reflexivity).
    assert (EC : uval (rho_sub rho s_landB) xLC = uval rho iC) by (unfold uval; rewrite <- eval_subst; reflexivity).
    assert (EL : uval (rho_sub rho s_landB) vLEN = uval rho vLEN) by (unfold uval; rewrite <- eval_subst; reflexivity).
    assert (EI : uval (rho_sub rho s_landB) pI = 0) by (unfold uval; rewrite <- eval_subst; change (sv_subst s_landB pI) with (SLit 0); apply (uval_lit rho 0); lia).
    assert (EN : uval (rho_sub rho s_landB) pNX = 0) by (unfold uval; rewrite <- eval_subst; change (sv_subst s_landB pNX) with (SLit 0); apply (uval_lit rho 0); lia).
    assert (EM : rm (rho_sub rho s_landB) = rm rho) by reflexivity.
    rewrite ED, EC, EL, EI, EN, EM. split; [exact H2|]. split; [exact H3|]. split; [exact H1|].
    intros p Hp. exact (proj1 (proj1 H3 0%nat p Hp)). }
  split; [exact HT|]. apply SPA_JAF_intro; [exact Hw10 | exact HT].
Qed.

Lemma land_after0 : ltac2:(tb__ "0|2|
S4S34A1S10S4S30Q40A1A1S87S0S5S35S11S27S77A1M0A1R4A2S6A3S0S5S71S13G0A1S5aR5A3S6A3S59R5A1S2bS3VJAv;S5eS57S52S8S34R7S56A3S5fA4A1S82R6R5R4A6S1S53S6cR7S7eA2M1A1S2bS3VJAFv;S53S91A2Sa9G1R6R5A6A2F_;F_;F_;F_;Fw;Ftp;Frho;Fbd0;").
Proof.
  intros bd0 rho tp w Hbd Hbud HPhi Hw.
  pose proof pipe_a1 as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18).
  pose proof land_checks_a1 as (Cent & Cid & Cnp & Ctv & Cfr & Cam & Cperm & Cnull & Ctvb & Cfrb & Cbd & Cz).
  pose proof (SPA_axforms segs _ XF_a1 rho XR_after1 C9_a1 tp w P1 Hw) as Hw1.
  pose proof (SPA_zsub _ rho C9_a1 Za1_a1 Zs1_a1 C10_a1 _ _ _ _ tp w P2 P3 P4 P5 Hw1) as Hw2.
  pose proof (SPA_zsub _ rho C10_a1 Za2_a1 Zs2_a1 C11_a1 _ _ _ _ tp w P6 P7 P8 P9 Hw2) as Hw3.
  pose proof (SPA_zsub _ rho C11_a1 Za3_a1 Zs3_a1 C12_a1 _ _ _ _ tp w P10 P11 P12 P13 Hw3) as Hw4a.
  pose proof (SPA_zsub _ rho C12_a1 Za4_a1 Zs4_a1 C13_a1 _ _ _ _ tp w P14 P15 P16 P17 Hw4a) as Hw4. rewrite P18 in Hw4.
  pose proof (JA_add_nulls segs AInv CST XGL NP Kc rho0 P0 FB FF BX PA tv1 nulls_a1 frL (bd0 ++ ENDOW) K1a rho tp w Cnull Hw4) as Hw6.
  pose proof (SPA_tv_permb segs AInv CST XGL NP Kc rho0 P0 FB FF BX PA (tv1 ++ nulls_a1) tvLand_a1 frL (bd0 ++ ENDOW) ANone K1a rho tp w Cperm Hw6) as Hw7.
  pose proof (JA_arena_init segs AInv CST XGL NP Kc rho0 P0 FB FF BX PA HBX tvLand_a1 frL bd0 K1a rho tp w Hw7) as Hw8.
  assert (Hw9 : SPA segs (JAv ndA1) M_after0 (rho_sub rho s_landA) tp w).
  { apply (SPA_entails_JA2 segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PA HKc K1a M_after0 s_landA (NDA tvLand_a1 frL bd0 (AHead (SLit 0) true)) ndA1 rho tp w
             Cent Cid Cnp); cbn [nd_tv nd_fr nd_bd nd_am ndA1 ndLE ndL].
    - unfold nd_below. cbn [nd_tv nd_fr nd_bd nd_am]. rewrite Ctvb, Cfrb, Hbd. reflexivity.
    - exact Ctv.
    - exact Cfr.
    - change (bud_le2 (ss_facts (ax_S K1a)) (bd_subst s_landA (nd_bd ndA1)) bd0 = true). rewrite Cbd. exact Hbud.
    - exact Cam.
    - exact Hw8. }
  assert (Hw10 : SPA segs (JAv ndA1) K_after0 (rho_sub rho s_landA) tp w).
  { rewrite <- (proj1 add_datas_a1). apply (SPA_add_objs _ _ (datasA vsP) M_after0 tp w (proj2 add_datas_a1)); [|exact Hw9].
    apply datas_emp_land. intros x Hx. apply sv_eqb_sound. exact (proj1 (forallb_forall _ _) Cz x Hx). }
  assert (HT : tblL (rho_sub rho s_landA)).
  { destruct HPhi as [(T & H1 & H2 & H3) HP0].

    split.
    2: { intros z Hz. assert (ED' : uval (rho_sub rho s_landA) xLD = uval rho iD) by (unfold uval; rewrite <- eval_subst; reflexivity).
         assert (EK' : uval (rho_sub rho s_landA) xLK = uval rho iK) by (unfold uval; rewrite <- eval_subst; reflexivity).
         change (rm (rho_sub rho s_landA)) with (rm rho). rewrite ED', EK' in Hz. exact (HP0 z Hz). }
    exists T.
    assert (ED : uval (rho_sub rho s_landA) xLD = uval rho iD) by (unfold uval; rewrite <- eval_subst; reflexivity).
    assert (EC : uval (rho_sub rho s_landA) xLC = uval rho iC) by (unfold uval; rewrite <- eval_subst; reflexivity).
    assert (EL : uval (rho_sub rho s_landA) vLEN = uval rho vLEN) by (unfold uval; rewrite <- eval_subst; reflexivity).
    assert (EI : uval (rho_sub rho s_landA) pI = 0) by (unfold uval; rewrite <- eval_subst; change (sv_subst s_landA pI) with (SLit 0); apply (uval_lit rho 0); lia).
    assert (EN : uval (rho_sub rho s_landA) pNX = 0) by (unfold uval; rewrite <- eval_subst; change (sv_subst s_landA pNX) with (SLit 0); apply (uval_lit rho 0); lia).
    assert (EM : rm (rho_sub rho s_landA) = rm rho) by reflexivity.
    rewrite ED, EC, EL, EI, EN, EM. split; [exact H2|]. split; [exact H3|]. split; [exact H1|].
    intros p Hp. exact (proj1 (proj1 H3 0%nat p Hp)). }
  split; [exact HT|]. apply SPA_JAF_intro; [exact Hw10 | exact HT].
Qed.

Lemma land_bodyE : ltac2:(tb__ "0|1|
S4S34A1S10S4S30Q40A1A1S87S0S5S35S11S27S76A1M0A1R4A2S6A3S0S5S71S13G0A1SadR5A3S6A3S2bS3VJAv;S5eS57S52S8S34R6S56A3S5fA4A1S83R5R4R3A6S2bS3VJAv;S92A1SabS6cR6S80A2R5R4A6F_;F_;F_;Fw;Ftp;Frho;Fbd0;").
Proof.
  intros bd0 rho tp w Hbd Hbud Hw.
  pose proof pipe_b0 as (P1 & Q1 & P2 & P3 & P4 & P5 & Q2 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18).
  pose proof land_checks_b0 as (Cent & Cid & Cnp & Ctv & Cfr & Cam & Cperm & Cnull & Ctvb & Cfrb & Cbd & Cz).
  pose proof (SPA_axforms segs _ XF_b0 rho XR_body0 C9_b0 tp w P1 Hw) as Hw1.
  pose proof (SPA_axforms segs _ [AXSplit i96_b0 (SLit 104)] rho C9_b0 D1_b0 tp w Q1 Hw1) as Hw1b.
  pose proof (SPA_zsub _ rho D1_b0 Za1_b0 Zs1_b0 D2_b0 _ _ _ _ tp w P2 P3 P4 P5 Hw1b) as Hw1c.
  pose proof (SPA_axforms segs _ [AXMerge i96_b0] rho D2_b0 C10_b0 tp w Q2 Hw1c) as Hw2.
  pose proof (SPA_zsub _ rho C10_b0 Za2_b0 Zs2_b0 C11_b0 _ _ _ _ tp w P6 P7 P8 P9 Hw2) as Hw3.
  pose proof (SPA_zsub _ rho C11_b0 Za3_b0 Zs3_b0 C12_b0 _ _ _ _ tp w P10 P11 P12 P13 Hw3) as Hw4a.
  pose proof (SPA_zsub _ rho C12_b0 Za4_b0 Zs4_b0 C13_b0 _ _ _ _ tp w P14 P15 P16 P17 Hw4a) as Hw4. rewrite P18 in Hw4.
  pose proof (JA_add_nulls segs AInv CST XGL NP Kc rho0 P0 FB FF BX PA tv1 nulls_b0 frL (bd0 ++ ENDOW) K0b rho tp w Cnull Hw4) as Hw6.
  pose proof (SPA_tv_permb segs AInv CST XGL NP Kc rho0 P0 FB FF BX PA (tv1 ++ nulls_b0) tvLand_b0 frL (bd0 ++ ENDOW) ANone K0b rho tp w Cperm Hw6) as Hw7.
  pose proof (JA_arena_init segs AInv CST XGL NP Kc rho0 P0 FB FF BX PA HBX tvLand_b0 frL bd0 K0b rho tp w Hw7) as Hw8.
  assert (Hw9 : SPA segs (JAv ndLE) M_bodyE (rho_sub rho s_landBE) tp w).
  { apply (SPA_entails_JA2 segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PA HKc K0b M_bodyE s_landBE (NDA tvLand_b0 frL bd0 (AHead (SLit 0) true)) ndLE rho tp w
             Cent Cid Cnp); cbn [nd_tv nd_fr nd_bd nd_am ndA1 ndLE ndL].
    - unfold nd_below. cbn [nd_tv nd_fr nd_bd nd_am]. rewrite Ctvb, Cfrb, Hbd. reflexivity.
    - exact Ctv.
    - exact Cfr.
    - change (bud_le2 (ss_facts (ax_S K0b)) (bd_subst s_landBE (nd_bd ndLE)) bd0 = true). rewrite Cbd. exact Hbud.
    - exact Cam.
    - exact Hw8. }
  assert (Hw10 : SPA segs (JAv ndLE) X_bodyE (rho_sub rho s_landBE) tp w).
  { rewrite <- (proj1 add_datas_b0). apply (SPA_add_objs _ _ (datasA vsP) M_bodyE tp w (proj2 add_datas_b0)); [|exact Hw9].
    apply datas_emp_land. intros x Hx. apply sv_eqb_sound. exact (proj1 (forallb_forall _ _) Cz x Hx). }
  exact Hw10.
Qed.

Lemma land_afterE : ltac2:(tb__ "0|1|
S4S34A1S10S4S30Q40A1A1S87S0S5S35S11S27S75A1M0A1R4A2S6A3S0S5S71S13G0A1SacR5A3S6A3S2bS3VJAv;S5eS57S52S8S34R6S56A3S5fA4A1S81R5R4R3A6S2bS3VJAv;S92A1SaaS6cR6S7fA2R5R4A6F_;F_;F_;Fw;Ftp;Frho;Fbd0;").
Proof.
  intros bd0 rho tp w Hbd Hbud Hw.
  pose proof pipe_a0 as (P1 & Q1 & P2 & P3 & P4 & P5 & Q2 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18).
  pose proof land_checks_a0 as (Cent & Cid & Cnp & Ctv & Cfr & Cam & Cperm & Cnull & Ctvb & Cfrb & Cbd & Cz).
  pose proof (SPA_axforms segs _ XF_a0 rho XR_after0 C9_a0 tp w P1 Hw) as Hw1.
  pose proof (SPA_axforms segs _ [AXSplit i96_a0 (SLit 104)] rho C9_a0 D1_a0 tp w Q1 Hw1) as Hw1b.
  pose proof (SPA_zsub _ rho D1_a0 Za1_a0 Zs1_a0 D2_a0 _ _ _ _ tp w P2 P3 P4 P5 Hw1b) as Hw1c.
  pose proof (SPA_axforms segs _ [AXMerge i96_a0] rho D2_a0 C10_a0 tp w Q2 Hw1c) as Hw2.
  pose proof (SPA_zsub _ rho C10_a0 Za2_a0 Zs2_a0 C11_a0 _ _ _ _ tp w P6 P7 P8 P9 Hw2) as Hw3.
  pose proof (SPA_zsub _ rho C11_a0 Za3_a0 Zs3_a0 C12_a0 _ _ _ _ tp w P10 P11 P12 P13 Hw3) as Hw4a.
  pose proof (SPA_zsub _ rho C12_a0 Za4_a0 Zs4_a0 C13_a0 _ _ _ _ tp w P14 P15 P16 P17 Hw4a) as Hw4. rewrite P18 in Hw4.
  pose proof (JA_add_nulls segs AInv CST XGL NP Kc rho0 P0 FB FF BX PA tv1 nulls_a0 frL (bd0 ++ ENDOW) K0a rho tp w Cnull Hw4) as Hw6.
  pose proof (SPA_tv_permb segs AInv CST XGL NP Kc rho0 P0 FB FF BX PA (tv1 ++ nulls_a0) tvLand_a0 frL (bd0 ++ ENDOW) ANone K0a rho tp w Cperm Hw6) as Hw7.
  pose proof (JA_arena_init segs AInv CST XGL NP Kc rho0 P0 FB FF BX PA HBX tvLand_a0 frL bd0 K0a rho tp w Hw7) as Hw8.
  assert (Hw9 : SPA segs (JAv ndLE) M_afterE (rho_sub rho s_landAE) tp w).
  { apply (SPA_entails_JA2 segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PA HKc K0a M_afterE s_landAE (NDA tvLand_a0 frL bd0 (AHead (SLit 0) true)) ndLE rho tp w
             Cent Cid Cnp); cbn [nd_tv nd_fr nd_bd nd_am ndA1 ndLE ndL].
    - unfold nd_below. cbn [nd_tv nd_fr nd_bd nd_am]. rewrite Ctvb, Cfrb, Hbd. reflexivity.
    - exact Ctv.
    - exact Cfr.
    - change (bud_le2 (ss_facts (ax_S K0a)) (bd_subst s_landAE (nd_bd ndLE)) bd0 = true). rewrite Cbd. exact Hbud.
    - exact Cam.
    - exact Hw8. }
  assert (Hw10 : SPA segs (JAv ndLE) K_afterE (rho_sub rho s_landAE) tp w).
  { rewrite <- (proj1 add_datas_a0). apply (SPA_add_objs _ _ (datasA vsP) M_afterE tp w (proj2 add_datas_a0)); [|exact Hw9].
    apply datas_emp_land. intros x Hx. apply sv_eqb_sound. exact (proj1 (forallb_forall _ _) Cz x Hx). }
  exact Hw10.
Qed.

Lemma land_after0_cnt : ltac2:(tb__ "0|2|
S10S1S0S2eS33S6cR1S7eA2M0S15P191A1A2Z0M1A3S0S2eS33G0S15P19aA1A2G1A3A2Frho;").
Proof.
  intros rho. pose proof land_checks_a1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Cz).
  assert (Z0 : forall x : positive, In x (map Pos.of_nat (seq 400 54)) -> uval (rho_sub rho s_landA) (SVar x) = 0).
  { intros x Hx. unfold uval. rewrite <- eval_subst. cbn [sv_subst]. rewrite (sv_eqb_sound _ _ (proj1 (forallb_forall _ _) Cz x Hx)). apply (uval_lit rho 0). lia. }
  split; apply Z0; lazy; tauto.
Qed.
Lemma land_ldefBE : ltac2:(tb__ "0|0|
S10S58R1A1S54S6cR2S80A2A1F_;Frho;").
Proof.
  intros rho HP0 z Hz.
  assert (ED' : uval (rho_sub rho s_landBE) xLD = uval rho iD) by (unfold uval; rewrite <- eval_subst; reflexivity).
  assert (EK' : uval (rho_sub rho s_landBE) xLK = uval rho iK) by (unfold uval; rewrite <- eval_subst; reflexivity).
  change (rm (rho_sub rho s_landBE)) with (rm rho). rewrite ED', EK' in Hz. exact (HP0 z Hz).
Qed.
Lemma land_ldefAE : ltac2:(tb__ "0|0|
S10S58R1A1S54S6cR2S7fA2A1F_;Frho;").
Proof.
  intros rho HP0 z Hz.
  assert (ED' : uval (rho_sub rho s_landAE) xLD = uval rho iD) by (unfold uval; rewrite <- eval_subst; reflexivity).
  assert (EK' : uval (rho_sub rho s_landAE) xLK = uval rho iK) by (unfold uval; rewrite <- eval_subst; reflexivity).
  change (rm (rho_sub rho s_landAE)) with (rm rho). rewrite ED', EK' in Hz. exact (HP0 z Hz).
Qed.

Lemma site_factsZ : ltac2:(tb__ "0|4|
S10S8bS14S18R1A1S13S27S73A1A1A3S1S67S68S31Q40S24R2SbfA2A2M0Z1a00A2S33R2S15PaA1A2M1A2S1S67G1Z800000000000M2A2S1S67G0S33R2S90A2M3A2S1S67S68G3Z138A2G2A2S67S68S33R2S8fA2Z800A2Z7fffff800000A2A2A2A2A2F_;Frho;").
Proof.
  intros rho HF.
  factz HF (SPUle (SAlu ALU_ADD (SVar 30) (SLit 6656)) (SVar 10)) H1. factz HF (SPUle (SVar 10) (SLit 140737488355328)) H2.
  factz HF (SPUle (SVar 30) vOUT) H3. factz HF (SPUle (SAlu ALU_ADD vOUT (SLit 312)) (SLit 140737488355328)) H4.
  factz HF (SPUle vF (SLit 140737479964672)) H5. factz HF (SPUle vOUT (SLit 140737488355328)) H6. factz HF (SPUle (SVar 30) (SLit 140737479966720)) H7.
  rewrite uval_lit in H2 by lia. rewrite uval_lit in H4 by lia. rewrite uval_lit in H5 by lia. rewrite uval_lit in H6 by lia. rewrite uval_lit in H7 by lia.
  pose proof (uval_range rho (SVar 30)) as R30. pose proof (uval_range rho vOUT) as RO. pose proof (uval_range rho (SVar 10)) as R10.
  rewrite uval_add_small in H4 by (rewrite uval_lit by lia; lia). rewrite uval_lit in H4 by lia.
  rewrite uval_add_small in H1 by (rewrite uval_lit by lia; lia). rewrite uval_lit in H1 by lia.
  change (uval rho (SVar 30)) with (bv_unsigned (rw rho V_TOP)) in *. repeat split; lia.
Qed.

Lemma pclMA_x : ltac2:(tb__ "0|0|
S10S4S9S12S12A2A1S4S9S9S12S2eA2S12A2A1S2eSa3VCST;Vrho0;VFB;VFF;R1A5Sa3VCST;Vrho0;Sa1VFB;R5R4A3Sa2VFF;R5R3A3R2A5F_;Fa;Ffr;Ftv;Frho;").
Proof.
  intros rho tv fr a H. apply (pclMA_mono CST rho0 FB _ FF _ a); [intros x Hx; apply In_FBx; left; exact Hx | intros x Hx; apply In_FFx; left; exact Hx | exact H].
Qed.
Lemma f5_pclMA : ltac2:(tb__ "0|1|
S10S4S9S12S12A2A1S2eS1S67S33R3S8fA2M0R1A2S69R1S68G0Z800A2A2A2Sa3VCST;Vrho0;Sa1VFB;R4R3A3Sa2VFF;R4S52A3R2A5F_;Fa;Ftv;Frho;").
Proof.
  intros rho tv a Ha. right; right; right. exists (uval rho vF), 2048, (uval rho vFL). split; [|exact Ha].
  apply In_FFx. right. exists (vF, 5, vFL). split; [left; reflexivity|]. reflexivity.
Qed.
Lemma ar_pclMA : ltac2:(tb__ "0|1|
S10S4S9S9S12S2eA2S12A2A1S2eS2S0S2eS33R3Sb3A2Z0A3A1S1S67S33R4Sb3A2M0R2A2S69R2S68G0Z40A2A2A2Sa3VCST;Vrho0;Sa1VFB;R5S74A3Sa2VFF;R5R4A3R3A5F_;F_;Fa;Ffr;Frho;").
Proof.
  intros rho fr a Hnz Ha. right; right; left. exists (uval rho vARn), 64. split; [|exact Ha].
  apply In_FBx. right. exists blkAR. split; [left; reflexivity|]. split; [unfold tnz, blkAR; cbn [fst]; unfold uval in Hnz; exact Hnz|].
  unfold tvv, blkAR. cbn [fst snd]. unfold uval. rewrite U_lit. reflexivity.
Qed.

Lemma uval_spm6656 : ltac2:(tb__ "0|2|
S10S67Z1a00M0S33R1S15PaA1M1A2A2S0S2eS33R2S1cSc5G1S16N1a00A1A3A2S6bS33R2G1A2G0A2A3F_;Frho;").
Proof.
  intros rho Hk. unfold uval in *. rewrite U_add, U_lit. pose proof (U_range (eval rho (SVar 10))) as R. unfold M64v in *.
  set (x := bv_unsigned (eval rho (SVar 10))) in *.
  rewrite Zplus_mod_idemp_r. replace (x + -6656) with (x - 6656) by lia. apply Z.mod_small. lia.
Qed.
Ltac in_lits_tac := unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_fuzz_iface.in_lits; cbn -[Z.add Z.le Z.lt]; repeat match goal with |- _ \/ _ => first [left; lia | right] end; lia.

Lemma HIN_RX : ltac2:(tb__ "0|0|
S10S8bS14S18R1A1S13S27S73A1A1A3VP0;Vrho0;A1S9aS8eVrho0;R3A3S1Sa4VCST;Vrho0;VFB;VFF;R4S74S52S79A8Sa5VCST;VXGL;Vrho0;VFB;VFF;R4S74S52S7dA9A2F_;F_;F_;Frho;").
Proof.
  intros rho HF HP0 Hav. destruct (site_factsZ rho HF) as (Zsp & Zsp47 & Zo & Zo47 & ZF).
  pose proof (T0_agreeA rho0 NP rho Hav eq_refl) as ET. destruct HP0 as (Ptxt & Pcfg & Plnk).
  assert (AG : forall v e, e = SVar v -> (v < NP)%positive -> uval rho e = uval rho0 e).
  { intros v e -> Hv. unfold uval. cbn [eval]. rewrite <- (proj1 Hav v Hv). reflexivity. }
  pose proof (uval_range rho vF) as RF. pose proof (uval_range rho vARn) as RA. pose proof (uval_range rho (SVar 28)) as R28. pose proof (uval_range rho vCFGp) as R15.
  factz HF (SPUle (SLit IMG_HI) vARn) HAnz. unfold IMG_HI in HAnz. rewrite uval_lit in HAnz by lia.
  pose proof (uval_range rho (SVar 30)) as R30. change (uval rho (SVar 30)) with (bv_unsigned (rw rho V_TOP)) in R30. pose proof (uval_range rho (SVar 10)) as R10.
  assert (STK : forall a, bv_unsigned (rw rho V_TOP) <= a < 140737488355328 -> pclMA CST rho0 (FBx FB rho tv_site) (FFx FF rho frL) a).
  { intros a Ha. left. rewrite ET. exact Ha. }
  split.
  - intros o a Ho Hr. unfold R_blr in Ho. cbn in Ho.
    destruct Ho as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]];
      unfold obj_range, obj_lo_of, obj_hi_of in Hr; cbn [ob_base ob_lo ob_hi fst snd] in Hr; rewrite ?soff_lit_small in Hr by lia;
      repeat change (bv_unsigned (eval rho ?e)) with (uval rho e) in Hr.
    all: first [ apply ar_pclMA; unfold vARn, pAR in *; lia
               | apply f5_pclMA; unfold vF in *; lia
               | apply STK; unfold vOUT in *; lia
               | apply pclMA_x; apply Plnk; rewrite <- (AG 28%positive (SVar 28) eq_refl ltac:(reflexivity)); lia
               | apply pclMA_x; apply Pcfg; rewrite <- (AG 15%positive vCFGp eq_refl ltac:(reflexivity)); unfold vCFGp in *; lia
               | match goal with H : (_ <= ?a < _) |- pclMA _ _ _ _ ?a => let t := type of H in idtac "ROBJ-LEFT" t end ].
    all: fail.
  - intros r a Hr Ha. unfold XkB in Hr. cbn in Hr.
    repeat (destruct Hr as [Hr|Hr]); try contradiction; subst r; cbn [fst snd] in Ha;
      repeat change (bv_unsigned (eval rho ?e)) with (uval rho e) in Ha; rewrite ?uval_lit in Ha by lia.
    all: first [ right; apply HXlits; in_lits_tac
               | lia
               | left; apply pclMA_x; apply Ptxt; rewrite <- (AG 13%positive vBUF eq_refl ltac:(reflexivity)), <- (AG 14%positive vLEN eq_refl ltac:(reflexivity)); unfold vBUF, vLEN in *; lia
               | left; apply pclMA_x; apply Pcfg; rewrite <- (AG 15%positive vCFGp eq_refl ltac:(reflexivity)); unfold vCFGp in *; lia
               | left; apply STK; unfold vOUT in *; lia
               | left; apply ar_pclMA; unfold vARn, pAR in *; lia
               | left; apply f5_pclMA; rewrite uval_add_small in Ha by (rewrite uval_lit by lia; unfold vF in *; lia); rewrite uval_lit in Ha by lia; unfold vF in *; lia
               | left; apply STK; rewrite (uval_spm6656 rho) in Ha by lia; lia
               | match goal with H : (_ <= ?a < _) |- _ => let t := type of H in idtac "XRS-LEFT" t end ].
    all: fail.
Qed.
Lemma HIN_blr : ltac2:(tb__ "0|0|
S10S98S8bS14S18R2A1S13S27S73A1A1A3VP0;Vrho0;A1S9aS8eVrho0;R4A3S1Sa4VCST;Vrho0;VFB;VFF;R5S74S52S79A8S1Sa5VCST;VXGL;Vrho0;VFB;VFF;R5S74S52S7dA9Sb0VCST;Sa1VFB;R5S74A3Sa2VFF;R5S52A3S6cS6dR5S79R4A3S85A2A4A2A2F_;F_;F_;Fms;Frho;").
Proof.
  intros rho ms HF HP0 Hav. destruct (HIN_RX rho HF HP0 Hav) as [HR HX]. split; [exact HR|]. split; [exact HX|].
  destruct (site_factsZ rho HF) as (Zsp & Zsp47 & Zo & Zo47 & ZF). destruct HP0 as (Ptxt & Pcfg & Plnk).
  assert (AG : forall v e, e = SVar v -> (v < NP)%positive -> uval rho e = uval rho0 e).
  { intros v e -> Hv. unfold uval. cbn [eval]. rewrite <- (proj1 Hav v Hv). reflexivity. }
  pose proof (uval_range rho vF) as RF.
  set (r := rho_sub (rho_absorb rho R_blr ms) s_blr).
    assert (EV : forall e, uval r e = uval rho (sv_subst s_blr e)) by (intros e; unfold uval, r; rewrite <- eval_subst, eval_absorb; reflexivity).
    assert (ET0 : TobjJV.T0 r = TobjJV.T0 rho0) by (unfold r; apply (T0_calleeA NP rho0 s_blr rho R_blr ms Hav); OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
  split; [split|].
  - intros a Ha. rewrite !EV in Ha. change (sv_subst s_blr BLR.vBUF) with vBUF in Ha. change (sv_subst s_blr BLR.vLEN) with vLEN in Ha.
      rewrite (AG 13%positive vBUF eq_refl ltac:(reflexivity)), (AG 14%positive vLEN eq_refl ltac:(reflexivity)) in Ha.
      pose proof (pclMA_x rho tv_site frL a (Ptxt a Ha)) as X. unfold pclMA in X |- *. rewrite ET0. exact X.
  - rewrite EV. change (sv_subst s_blr BLR.vALC) with (SAlu ALU_ADD vF (SLit 464)). rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia.
      exists (uval rho vF), 2048, (uval rho vFL). split; [|lia]. apply In_FFx. right. exists (vF, 5, vFL). split; [left; reflexivity | reflexivity].
  - intros z Hz. exfalso. rewrite !EV in Hz. change (sv_subst s_blr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.Lib_vec_reserve_rom.vDt) with (SLit 0) in Hz. change (sv_subst s_blr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.Lib_vec_reserve_rom.vK) with (SLit 0) in Hz.
      rewrite !uval_lit in Hz by lia. lia.
Qed.

Lemma Forall_fnodup : ltac2:(tb__ "0|0|
S14OF_;S4S14A1S8bS14R2R1A3S8bS14R3Sb2R2A1A3F_;Fl;FP;").
Proof.
  intros P l H. induction l as [|x r IH]; [constructor|]. cbn [fnodup]. apply Forall_cons_iff in H as [Hx Hr].
  destruct (existsb (sprop_eqb x) r); [exact (IH Hr) | constructor; [exact Hx | exact (IH Hr)]].
Qed.
Lemma SPA_back : ltac2:(tb__ "0|2|
S2cS10S28S28S28S4S30Q40A1A1S87S0SdS28A1Sb6R5SafR5A1A2SbS28R4A2A3S0S5Sa6Sb4S29R5A1M0A1G0A2S6A3S0S5S95S14S25S11S27R6A1M1A1A1Sb2S13G1A1A1A3S6A3S0S28SccScbR7Sb4S29R7A1A1A2Sb2S13S27R7A1A1A1A2R6A3S2bS3RbR9RaR6R5A6S2bS3RcR8RbR7R6A6F_;F_;F_;F_;F_;Fw;Ftp;FT';FA;FT;Frho;FJ;").
Proof.
  intros J rho T A T' tp w H1 H2 H3 H4 Hw. rewrite <- H4.
  apply (SPA_refacts segs J rho (ax_setX A (xnodup (ax_X A)))); [| exact H3 | intros HF; apply Forall_fnodup; exact HF].
  apply (SPA_x_incl segs J rho A); [exact H2|]. exact (SPA_axforms segs J (xfb T) rho T A tp w H1 Hw).
Qed.

Lemma blk_not_R : ltac2:(tb__ "0|4|
S4S34A1S63S28S10S10S4S30Q40M0A1A1S87S12S12S2bS3VJAv;S5eS7S9S12S12A2M1Sb5S7G1SaS12S12R2R1A4ScG1A1A3A3S52R9R8A4A1R7R5R4R3A6S9aS11S27S73A1A1R7R6A3S2S0S2eS33R7R4A2Z0M2A3A1S2S0S2eS33R8Sb3A2G2A3A1Sa4VCST;Vrho0;VFB;VFF;RaS74S52S79A8S2eS1S67S33RbR8A2M3R1A2S69R1S68G3S33RbR7A2A2A2A2S2S6fRdS79S32G0R2A2A3A1F_;Fz;F_;F_;F_;F_;F_;Fn;Fd;Fw;Ftp;Frho';Frho;FS;Fam;Fbd;").
Proof.
  intros bd am S rho rho' tp [tr [ms md]] d n [_ (Ai & kc & HJ)] Hag Hnz HnzA HR z Hz (o & Ho & Hr).
  pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & (HN & HD & HZ) & HFR & HK0 & HP0 & _). cbn [nd_tv nd_fr nd_bd nd_am] in HN, HD, HZ, HFR.
  assert (Hin : In (d, n) [blkAR; (d, n)]) by (right; left; reflexivity). assert (HinA : In blkAR [blkAR; (d, n)]) by (left; reflexivity).
  assert (Hne : tvv rho' (d, n) <> tvv rho' blkAR).
  { destruct HD as [HD1 _]. intros E. apply (HD1 (d, n) ltac:(left; reflexivity)); [unfold tnz, blkAR; cbn [fst]; unfold uval in HnzA; exact HnzA | exact Hnz | symmetry; exact E]. }
  pose proof (uval_range rho' d) as Rd. pose proof (uval_range rho' n) as Rn.
  destruct (proj1 (Forall_forall _ _) HN (d, n) Hin Hnz) as (_ & Hlive & Hnfb). unfold tvv in Hlive, Hnfb. cbn [fst snd] in Hlive, Hnfb.
  assert (Hz64 : 0 <= z < 2 ^ 64).
  { split; [lia|]. destruct (law_blocks _ _ _ ALA Ai _ _ _ HM) as (_ & HBl & _). destruct (HBl _ _ Hlive) as (_ & _ & _ & G4 & _).
    pose proof (topG_range (aa_geom Ai)). unfold uval in *. lia. }
  pose proof (HR o (bv_unsigned (Z_to_bv 64 z)) Ho Hr) as HP. rewrite U_Z_to_bv in HP by exact Hz64.
  apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC.live_not_pclMA segs AInv CST ALA HCST rho0 Ai rho' tp md (FBx FB rho tv_site) (FFx FF rho frL) (bv_unsigned (eval rho' d)) (bv_unsigned (eval rho' n)) z HM).
  -
    intros bn Hbn. apply In_FBx in Hbn as [Hbn|(t & Ht & Htnz & <-)]; [exact (HB _ Hbn)|].
    destruct Ht as [<-|[]]. destruct (proj1 (Forall_forall _ _) HN blkAR HinA HnzA) as (_ & HlA & _).
    replace (tvv rho blkAR) with (tvv rho' blkAR); [exact HlA|]. unfold tvv, blkAR, vARn, pAR. cbn [fst snd eval]. rewrite <- (proj1 Hag 272%positive) by reflexivity. reflexivity.
  - replace (FFx FF rho frL) with (FFx FF rho' frL); [exact (ffinA_FFx FF Ai rho' frL HFF HFR)|].
    unfold FFx, frL, frv, uval, vF, vFL. cbn [map fst snd eval]. rewrite <- (proj1 Hag 110%positive) by reflexivity. rewrite <- (proj1 Hag 120%positive) by reflexivity. reflexivity.
  - exact HT.
  - exact Hlive.
  - intros HinF. apply In_FBx in HinF as [HinF|(t & Ht & Htnz & Et)]; [exact (Hnfb HinF)|]. destruct Ht as [<-|[]].
    apply Hne. unfold tvv in Et |- *. cbn [fst snd] in Et |- *. rewrite <- Et. unfold blkAR, vARn, pAR. cbn [fst snd eval]. rewrite <- (proj1 Hag 272%positive) by reflexivity. reflexivity.
  - unfold uval in Hz. exact Hz.
  - exact HP.
Qed.

Lemma d_nz_of_JAv : ltac2:(tb__ "0|1|
S65S10S4S30Q40A1A1S4S97A1S96S12S12VJAv;R7R6R5R4R3A5S94S9S12S12A2SaS12S12R3Sc6Z10R2A2A4S64R8A1A3S67S33R8R3A2ScaA2S2S0S2eS33R9R4A2Z0M0A3A1S2S0S2eS33RaR6A2G0A3A1F_;F_;F_;F_;Fk;Fd;Fmd;Ftr;Ftp;Frho;Fnd;").
Proof.
  intros nd rho tp tr md d k HJ Hin Hk Hk0 Hd.
  pose proof (JA_null_size0 AInv CST XGL NP Kc rho0 P0 FB FF BX PA nd rho tp tr md (d, kb 16 k) HJ Hin Hd) as Z0.
  cbn [snd] in Z0. change (bv_unsigned (eval rho (kb 16 k))) with (uval rho (kb 16 k)) in Z0.
  unfold kb, B32 in *. rewrite uval_mul_lit in Z0 by lia. lia.
Qed.

Section X.
Variable TR : assn -> assn -> Prop.
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S2cS28S10S4S30Q40A1A1S88S8bS14S18R3A1S13S27R4A1A1A3VTR;S2bS3R6R5R4R3A5R2A2M0F_;G0F_;FQa;Ftp;Frho;FS;FJ;").
Hypothesis TR_ex : forall (T : Type) (J : T -> jpredA) S rho tp (Qa : assn),
  (forall x, TR (SPA segs (J x) S rho tp) Qa) -> TR (SPA segs (fun r p t m => exists x, J x r p t m) S rho tp) Qa.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S88S88S88S87R3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQa;FP';FP;").
Hypothesis TR_pureP : ltac2:(tb__ "0|1|
S88OS88S87R4R1A1R4F_;Fw;R3VTR;R5R3A2M0F_;G0F_;F_;FQa;FX;FP;").
Hypothesis TR_callP : ltac2:(tb__ "0|5|
S2cS2cS28S28S6eS4S17A1M0S4S9S28S9cA2M1A1S4S9S12S12A2M2A1S88S10S4S30Q40A1A1M3G2S94G2R1R5A3S94G2R2S29RbA1A3F_;Fr;S0SdG0A1Sa0RaR9R8A3SbG0R7A2A3S0S5S9fRbRaR9R8S8cG1S28SfS28S9cA2R7A4A5S6A3S10G3VTR;S2bS3RfRdR2R1A5S9dS3S11S27RdA1A1R2R1RaA5A2Ftp1;Frho1;S4S97A1M4S98S96S2dS3R9R8R10SaG4Sa7R3Sa8R2R1A2A4A5R13RaR9R4R2A4R13S6cS6dRbRfS93R3RaR4A3A3R10A2RaR5R3A4F_;F_;Fmd;Fms;Ftr;S28S9cG4S98S96S10G3G4S98S96S94G1SaS28S9cRaR9A4R14A3S2dS3R12R11R19SaG4Sa7R9Sa8R8R7A2A4A5R1cR13R12RaR8A4S9aS11S27R1aA1A1S6cS6dR14R18S93R9R13RaA3A3R19A2R8A3S2dS3R9R8ReSaG4Sa7R7Sa8R6R5A2A4A5ReS6cS6dR16R1aS93RbR15RcA3A3R1bA2R15RaR9R8R6A6S1ScfR17S93RcR16RdA3R1bR1cR1dR10R1eR19RbA9S10S9bR18S93RdR17ReA3R1cR1dS27R1eA1S27R1fA1S27R11A1R1RcA9VTR;S2bS3S9eR11S6cS6dR19R1dS93ReR18RfA3A3R1eA2R18RdRcA5Sd0R1eR1fR12R20R1dR1bA6R2RcA5R1aA2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S2bS3R11RfR8R7A5R9A2F_;F_;F_;F_;F_;F_;Ftp;Frho;FQa;FXk;FPosts;FR;Fs;FPre;FC;FJp;FJ;").

Hypothesis CBLR : ltac2:(tb__ "0|1|
S4S9S2eS2eA2M0A1S4S9G0S2eA2A1S37S10S4S30Q40A1A1S36Z5R3A2VTR;S2bS3S62VAInv;VCST;VXGL;VKc;Sb0VCST;R6R5A3R6R5R4S60Sc9AaSc8R3R2A5S9dS3ScdR3R2Sd1VAInv;VCST;VXGL;VKc;Sb0VCST;A1S60Sb1R6R5R4AaA5A2F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").

Variable brest : list bitem.
Variable Q : assn.
Hypothesis CONT1 : ltac2:(tb__ "0|0|
S10S4S30Q40A1A1S59R2A1VTR;S2bS3VJAv;S5eS57S52Vbrest;S5fA4A1S7cR3R2A5VQ;A2F_;Ftp';Frho';").
Hypothesis CONT0 : ltac2:(tb__ "0|0|
S10S4S30Q40A1A1S58R2A1VTR;S2bS3VJAv;S5eS57S52Vbrest;S5fA4A1S7bR3R2A5VQ;A2F_;Ftp';Frho';").

Lemma X_E_blr : ltac2:(tb__ "0|3|
S4S34A1S10S4S30Q40A1A1S0S5S35S11S27S73A1M0A1M1R3A2S6A3S0S5S35G1Vbrest;A2S6A3SbaS8eVrho0;VP0;S13G0A1S16Z0M2A1G2R5S8S34SaeVbrest;A3A8VTR;S2bS3VJAv;S5eS74S52R6S5fA4A1S7aR5R4A5VQ;A2F_;F_;F_;Ftp;Frho;Fbd;").
Proof.
  intros bd rho tp Hbd Hbr HPAY.
  pose proof site_checks as (CXk & Ce & Cchk & Ctp & Cdom & Cnf & Cpass & Cam & Cpd & Cbd & Cx1 & Cx2 & Cx3 & Ctvb & Cfrb & Cit1 & Cit0 & Ci40 & Ci41 & Ci42 & Cj40 & Cj42 & Civ1 & Civ0 & Cs13).

  eapply TR_pre with (P := SPA segs (JAv (NDA (tv_site ++ tv_pass) frL bd ANone)) E_blr rho tp).
  { intros w Hw. rewrite <- Cx3. apply (JA_add_nulls segs AInv CST XGL NP Kc rho0 P0 FB FF BX PA tv_site tv_pass frL bd); [reflexivity|].
    apply SPA_x_publish_empty; [lia | reflexivity |].
    exact (SPA_axforms segs _ _ rho E_blr1 E_blr2 tp w Cx2 (SPA_axforms segs _ _ rho E_blr0 E_blr1 tp w Cx1 Hw)). }
  apply TR_facts. intros HF.
  apply (TR_pureP _ (P0 rho0 /\ agree_vals NP rho0 rho)).
  { intros [tr [ms md]] [_ (Ai & kc & HJ)]. pose proof HJ as (Hav & _ & _ & _ & _ & _ & _ & _ & _ & HP0 & _). split; [exact HP0 | exact Hav]. }
  intros [HP0 Hav].
  pose proof (HIN_blr rho) as HIN. pose proof (proj1 (HIN_RX rho HF HP0 Hav)) as HR.
  apply (client_callT_k segs AInv CST XGL ALA HCST HXGL NP Kc rho0 P0 FB FF BX PA HKc HBX (BLRP.P0_blr CST) PTrue (fun _ _ => I) HPAany BLR.Pre_blr BLR.nd_pre BLRP.PDk_blr NF
           eq_refl eq_refl eq_refl TR TR_facts TR_ex TR_pre TR_callP CBLR eq_refl
           E_blr s_blr R_blr XkB rho tp tv_site tv_pass frL bd brest ANone Q CXk Ce Cchk Ctp Cdom Cnf).
  - unfold nd_below. cbn [nd_tv nd_fr nd_bd nd_am]. rewrite Ctvb, Cfrb, Hbd. reflexivity.
  - exact Hbr.
  - exact Cpass.
  - exact Cam.
  - rewrite Cbd. exact HPAY.
  - exact Cpd.
  - intros Ai ms HF' HP0' Hav' HBf HFF HN HD HZ HFR HM HT HTK. exact (HIN ms HF' HP0' Hav').
  - intros [[Ld ndL] PsiL] rho' tp' Hd Hag HK HPSI. cbn [BLRP.PDk_blr In] in Hd.
    pose proof site_checks as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CT1 & CT0 & F1k & F1ck & F1a & F0k & F0a).
    pose proof back_checks as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8).
    assert (EL' : uval rho' vLEN = uval rho vLEN) by (unfold uval, vLEN; cbn [eval]; rewrite <- (proj1 Hag 14%positive eq_refl); reflexivity).
    destruct Hd as [Hd|[Hd|[]]]; injection Hd as <- <- <-; cbn [fst snd nd_tv nd_bd nd_am BLR.ndP ND am_subst app] in HPSI |- *;
      destruct HPSI as (r0c & rhoL & HPsi & Hd1 & Hd2 & Hd3).
    +
      rewrite Cit0, CT0. cbn [app].
      apply TR_facts. intros HF2.
      pose proof (holds_mem _ _ _ HF2 F0k) as FkB. pose proof (holds_mem _ _ _ HF2 F0a) as FaI. zf FkB. zf FaI.
      repeat change (bv_unsigned (eval rho' ?e)) with (uval rho' e) in FkB, FaI. unfold B32 in FkB. unfold IMG_HI in FaI. rewrite uval_lit in FkB, FaI by lia.
      assert (E_D : uval rho' iD = uval rhoL (SVar 140)) by (unfold uval; rewrite <- (Hd3 (SVar 140)) by exact (proj1 (andb_prop _ _ Civ0)); rewrite Cj40; reflexivity).
      assert (E_K : uval rho' iK = uval rhoL (SVar 142)) by (unfold uval; rewrite <- (Hd3 (SVar 142)) by exact (proj1 (andb_prop _ _ (proj2 (andb_prop _ _ Civ0)))); rewrite Cj42; reflexivity).
      apply (TR_pureP _ (uval rho' iK <> 0 -> forall z, uval rho' iD <= z < uval rho' iD + uval rho' (kb 16 iK) -> ~ in_ranges rho R_blr (Z_to_bv 64 z))).
      { intros w Hw HK0. destruct w as [tr [ms md]].
        assert (HnzD : uval rho' iD <> 0) by (destruct Hw as [_ HJw]; exact (d_nz_of_JAv _ _ _ _ _ iD iK HJw ltac:(right; left; reflexivity) ltac:(unfold B32; lia) HK0)).
        exact (blk_not_R brest ANone _ rho rho' tp' _ iD (kb 16 iK) Hw Hag HnzD ltac:(lia) HR). }
      intros NR.
      assert (HP : PhiP0 rho').
      { intros z Hz. pose proof (uval_range rho' iK) as RK.
        assert (EK16 : uval rho' (kb 16 iK) = 16 * uval rho' iK) by (unfold kb; apply uval_mul_lit; lia).
        destruct (Z.eq_dec (uval rho' iK) 0) as [K0|Kn0]; [lia|].
        destruct (Hd2 _ (NR Kn0 z ltac:(rewrite EK16; exact Hz))) as [_ E2]. rewrite E2. apply HPsi. rewrite <- E_D, <- E_K. exact Hz. }
      eapply TR_pre; [|exact (CONT0 rho' tp' HP)]. intros w Hw. exact (SPA_back _ rho' T_blr0a Ab0 T_blr0 tp' w B5 B6 B7 B8 Hw).
    +
      rewrite Cit1, CT1. cbn [app].
      apply TR_facts. intros HF2.
      pose proof (holds_mem _ _ _ HF2 F1k) as FkB. pose proof (holds_mem _ _ _ HF2 F1a) as FaI. pose proof (holds_mem _ _ _ HF2 F1ck) as Fck. zf FkB. zf FaI. zf Fck.
      repeat change (bv_unsigned (eval rho' ?e)) with (uval rho' e) in FkB, FaI, Fck. unfold B32 in FkB. unfold IMG_HI in FaI. rewrite uval_lit in FkB, FaI by lia.
      assert (E_D : uval rho' iD = uval rhoL (SVar 140)) by (unfold uval; rewrite <- (Hd3 (SVar 140)) by exact (proj1 (andb_prop _ _ Civ1)); rewrite Ci40; reflexivity).
      assert (E_C : uval rho' iC = uval rhoL (SVar 141)) by (unfold uval; rewrite <- (Hd3 (SVar 141)) by exact (proj1 (andb_prop _ _ (proj2 (andb_prop _ _ Civ1)))); rewrite Ci41; reflexivity).
      assert (E_K : uval rho' iK = uval rhoL (SVar 142)) by (unfold uval; rewrite <- (Hd3 (SVar 142)) by exact (proj1 (andb_prop _ _ (proj2 (andb_prop _ _ (proj2 (andb_prop _ _ Civ1)))))); rewrite Ci42; reflexivity).
      assert (E_L : uval r0c BLR.vLEN = uval rho' vLEN) by (unfold uval; rewrite Hd1; change (sv_subst s_blr BLR.vLEN) with vLEN; symmetry; exact EL').
      apply (TR_pureP _ (uval rho' iK <> 0 -> forall z, uval rho' iD <= z < uval rho' iD + uval rho' (kb 16 iK) -> ~ in_ranges rho R_blr (Z_to_bv 64 z))).
      { intros w Hw HK0. destruct w as [tr [ms md]].
        assert (HnzD : uval rho' iD <> 0) by (destruct Hw as [_ HJw]; exact (d_nz_of_JAv _ _ _ _ _ iD iK HJw ltac:(right; left; reflexivity) ltac:(unfold B32; lia) HK0)).
        exact (blk_not_R brest ANone _ rho rho' tp' _ iD (kb 16 iK) Hw Hag HnzD ltac:(lia) HR). }
      intros NR.
      pose proof (uval_range rho' iK) as RK. pose proof (uval_range rho' iC) as RC.
      assert (EK16 : uval rho' (kb 16 iK) = 16 * uval rho' iK) by (unfold kb; apply uval_mul_lit; lia).
      destruct HPsi as [(T & HT1 & HT2 & HT3) HDEF].
      assert (HP : PhiP1 rho').
      { split.
        - exists T. split; [rewrite E_C; exact HT1|]. split; [|rewrite <- E_L; exact HT3].
          apply (decodes_ext (rm rhoL)); [|rewrite E_D; exact HT2]. intros z Hz.
          destruct (Z.eq_dec (uval rho' iK) 0) as [K0|Kn0]; [lia|].
          destruct (Hd2 _ (NR Kn0 z ltac:(rewrite EK16; lia))) as [_ E2]. exact E2.
        - intros z Hz. destruct (Z.eq_dec (uval rho' iK) 0) as [K0|Kn0]; [lia|].
          destruct (Hd2 _ (NR Kn0 z ltac:(rewrite EK16; exact Hz))) as [_ E2]. rewrite E2. apply HDEF. rewrite <- E_D, <- E_K. exact Hz. }
      eapply TR_pre; [|exact (CONT1 rho' tp' HP)]. intros w Hw. exact (SPA_back _ rho' T_blr1a Ab1 T_blr1 tp' w B1 B2 B3 B4 Hw).
Qed.
End X.

Section Pack.
Variable ok : world -> Prop.
Hypothesis Hok : ltac2:(tb__ "0|0|
S66S3VKc;Vok;A3").
Hypothesis AC : ltac2:(tb__ "0|0|
Sc0S3SbeVAInv;VCST;VXGL;A5").
Variable bd0 : list bitem.
Variable Q : assn.

Hypothesis TGT_bodyN : ltac2:(tb__ "0|0|
S10S4S30Q40A1A1S53R2A1S8aS3Vok;S2bS3VJAFv;S53S91A2S39R3R2A5VQ;A4F_;Ftp;Frho2;").
Hypothesis TGT_after0 : ltac2:(tb__ "0|1|
S10S4S30Q40A1A1S53R2A1S1S0S2eS33R3S15P191A1A2Z0M0A3S0S2eS33R3S15P19aA1A2G0A3A2S8aS3Vok;S2bS3VJAFv;S53S91A2Sa9R4R3A5VQ;A4F_;F_;Ftp;Frho2;").
Hypothesis TGT_bodyE : ltac2:(tb__ "0|0|
S10S4S30Q40A1A1S54R2A1S8aS3Vok;S2bS3VJAv;S92A1SabR3R2A5VQ;A4F_;Ftp;Frho2;").
Hypothesis TGT_afterE : ltac2:(tb__ "0|0|
S10S4S30Q40A1A1S54R2A1S8aS3Vok;S2bS3VJAv;S92A1SaaR3R2A5VQ;A4F_;Ftp;Frho2;").
Hypothesis Hb1 : ltac2:(tb__ "0|0|
S0S5S35S11S27S78A1A1Vbd0;A2S6A3"). Hypothesis Hl1 : ltac2:(tb__ "0|0|
S0S5S71S13S27S78A1A1S5bVbd0;A3S6A3").
Hypothesis Hb2 : ltac2:(tb__ "0|0|
S0S5S35S11S27S77A1A1Vbd0;A2S6A3"). Hypothesis Hl2 : ltac2:(tb__ "0|0|
S0S5S71S13S27S77A1A1S5aVbd0;A3S6A3").
Hypothesis Hb3 : ltac2:(tb__ "0|0|
S0S5S35S11S27S76A1A1Vbd0;A2S6A3"). Hypothesis Hl3 : ltac2:(tb__ "0|0|
S0S5S71S13S27S76A1A1SadVbd0;A3S6A3").
Hypothesis Hb4 : ltac2:(tb__ "0|0|
S0S5S35S11S27S75A1A1Vbd0;A2S6A3"). Hypothesis Hl4 : ltac2:(tb__ "0|0|
S0S5S71S13S27S75A1A1SacVbd0;A3S6A3").
Hypothesis Hbr : ltac2:(tb__ "0|0|
S0S5S35S11S27S73A1A1S8S34Vbd0;S56A3A2S6A3").

Lemma bd_below_run : ltac2:(tb__ "0|0|
S28S0S5Sc3S11S27S73A1A1S11S27R1A1A1A2S6A3S0S5S35S11S27R2A1A1S8S34Vbd0;S56A3A2S6A3F_;FT;").
Proof.
  intros T Hle. apply forallb_forall. intros it Hit. apply (proj1 (forallb_forall _ _) Hbr) in Hit.
  apply forallb_forall. intros ca Hca. eapply sv_below_mono; [apply Pos.leb_le; exact Hle | exact (proj1 (forallb_forall _ _) Hit ca Hca)].
Qed.

Lemma run1_sound : ltac2:(tb__ "0|0|
S10S4S30Q40A1A1S59R2A1S8aS3Vok;S2bS3VJAv;S5eS57S52S8S34Vbd0;S56A3S5fA4A1S7cR3R2A5VQ;A4F_;Ftp;Frho;").
Proof.
  intros rho tp HP. pose proof run_checks as (C1 & _ & _ & _ & Cn1 & _ & CV1 & _ & Ct1 & Cf1 & _ & _ & Ce1 & _).
  apply (triple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PA PhiP1 ok _ T_blr1 rho tp Q HP).
  apply (cfg_soundA segs FUEL_lo cps_land (ss_next (ax_S T_blr1)) [T_blr1] [XR_body1; XR_after1] (JAFv PhiP1 (NDA tv1 frL (bd0 ++ ENDOW) ANone)) ok Q tp).
  - exact (ok_frameA_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PA PhiP1 ok _ Hok).
  - apply (stableA_JAF segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PA HKc V_P PhiP1 PhiP1_reads); [apply Pos.leb_le; exact Cn1 | | exact CV1].
    unfold nd_below. cbn [nd_tv nd_fr nd_bd nd_am]. rewrite Ct1, Cf1, (bd_below_run T_blr1 Ce1). reflexivity.
  - exact C1.
  - intros E rhoE [<-|[<-|[]]]; (eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw |]).
    + apply (TRs_pureP segs ok _ (tblL (rho_sub rhoE s_landB))).
      { intros w Hw. destruct (SPA_JAF_elim segs AInv CST XGL NP Kc rho0 P0 FB FF BX PA PhiP1 _ _ _ _ w Hw) as [Hw' HPe]. exact (proj1 (land_bodyN bd0 rhoE tp w Hb1 Hl1 HPe Hw')). }
      intros HT. eapply triple_conseq; [ | intros w Hw; exact Hw | apply (TGT_bodyN (rho_sub rhoE s_landB) tp HT)].
      intros w Hw. destruct (SPA_JAF_elim segs AInv CST XGL NP Kc rho0 P0 FB FF BX PA PhiP1 _ _ _ _ w Hw) as [Hw' HPe]. exact (proj2 (land_bodyN bd0 rhoE tp w Hb1 Hl1 HPe Hw')).
    + apply (TRs_pureP segs ok _ (tblL (rho_sub rhoE s_landA))).
      { intros w Hw. destruct (SPA_JAF_elim segs AInv CST XGL NP Kc rho0 P0 FB FF BX PA PhiP1 _ _ _ _ w Hw) as [Hw' HPe]. exact (proj1 (land_after0 bd0 rhoE tp w Hb2 Hl2 HPe Hw')). }
      intros HT. eapply triple_conseq; [ | intros w Hw; exact Hw | apply (TGT_after0 (rho_sub rhoE s_landA) tp HT (land_after0_cnt rhoE))].
      intros w Hw. destruct (SPA_JAF_elim segs AInv CST XGL NP Kc rho0 P0 FB FF BX PA PhiP1 _ _ _ _ w Hw) as [Hw' HPe]. exact (proj2 (land_after0 bd0 rhoE tp w Hb2 Hl2 HPe Hw')).
  - left. reflexivity.
Qed.

Lemma run0_sound : ltac2:(tb__ "0|0|
S10S4S30Q40A1A1S58R2A1S8aS3Vok;S2bS3VJAv;S5eS57S52S8S34Vbd0;S56A3S5fA4A1S7bR3R2A5VQ;A4F_;Ftp;Frho;").
Proof.
  intros rho tp HP. pose proof run_checks as (_ & C0 & _ & _ & _ & Cn0 & _ & CV0 & _ & _ & Ct0 & Cf0 & _ & Ce0).
  apply (triple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PA PhiP0 ok _ T_blr0 rho tp Q HP).
  apply (cfg_soundA segs FUEL_lo cps_land (ss_next (ax_S T_blr0)) [T_blr0] [XR_body0; XR_after0] (JAFv PhiP0 (NDA tv1 frL (bd0 ++ ENDOW) ANone)) ok Q tp).
  - exact (ok_frameA_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PA PhiP0 ok _ Hok).
  - apply (stableA_JAF segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PA HKc V_P PhiP0 PhiP0_reads); [apply Pos.leb_le; exact Cn0 | | exact CV0].
    unfold nd_below. cbn [nd_tv nd_fr nd_bd nd_am]. rewrite Ct0, Cf0, (bd_below_run T_blr0 Ce0). reflexivity.
  - exact C0.
  - intros E rhoE [<-|[<-|[]]]; (eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw |]).
    + apply (TRs_pureP segs ok _ (ldef (rho_sub rhoE s_landBE))).
      { intros w Hw. destruct (SPA_JAF_elim segs AInv CST XGL NP Kc rho0 P0 FB FF BX PA PhiP0 _ _ _ _ w Hw) as [_ HPe]. exact (land_ldefBE rhoE HPe). }
      intros HLd. eapply triple_conseq; [ | intros w Hw; exact Hw | apply (TGT_bodyE (rho_sub rhoE s_landBE) tp HLd)].
      intros w Hw. destruct (SPA_JAF_elim segs AInv CST XGL NP Kc rho0 P0 FB FF BX PA PhiP0 _ _ _ _ w Hw) as [Hw' _]. exact (land_bodyE bd0 rhoE tp w Hb3 Hl3 Hw').
    + apply (TRs_pureP segs ok _ (ldef (rho_sub rhoE s_landAE))).
      { intros w Hw. destruct (SPA_JAF_elim segs AInv CST XGL NP Kc rho0 P0 FB FF BX PA PhiP0 _ _ _ _ w Hw) as [_ HPe]. exact (land_ldefAE rhoE HPe). }
      intros HLd. eapply triple_conseq; [ | intros w Hw; exact Hw | apply (TGT_afterE (rho_sub rhoE s_landAE) tp HLd)].
      intros w Hw. destruct (SPA_JAF_elim segs AInv CST XGL NP Kc rho0 P0 FB FF BX PA PhiP0 _ _ _ _ w Hw) as [Hw' _]. exact (land_afterE bd0 rhoE tp w Hb4 Hl4 Hw').
  - left. reflexivity.
Qed.

Theorem blr_land_sound : ltac2:(tb__ "0|2|
S4S34A1S10S4S30Q40A1A1S0S5S35S11S27S73A1M0A1R3A2S6A3SbaS8eVrho0;VP0;S13G0A1S16Z0M1A1G1R4S8S34SaeS8S34Vbd0;S56A3A3A8S8aS3Vok;S2bS3VJAv;S5eS74S52R5S5fA4A1S7aR4R3A5VQ;A4F_;F_;Ftp;Frho;Fbd;").
Proof.
  intros bd rho tp Hbd HPAY.
  apply (X_E_blr (triple segs ok) (TRs_facts segs ok) (TRs_ex segs ok) (TRs_pre segs ok) (TRs_pureP segs ok) (call_soundPA3 segs ok)
           (fun FBc FFc BXc rho1 tp1 HB => BLRP.build_line_index_rom_sum AInv CST XGL ALA HCST HXGL Kc HKc FBc FFc BXc HB rho1 ok Hok AC tp1)
           (bd0 ++ ENDOW) Q run1_sound run0_sound bd rho tp Hbd Hbr HPAY).
Qed.
End Pack.

Section PackX.
Hypothesis ACX : ltac2:(tb__ "0|0|
Sc1S3SbeVAInv;VCST;VXGL;A5").
Variable bd0 : list bitem.
Variable Q : world -> Prop.
Hypothesis TGT_bodyN : ltac2:(tb__ "0|0|
S10S4S30Q40A1A1S53R2A1S89S3S2bS3VJAFv;S53S91A2S39R3R2A5VQ;A3F_;Ftp;Frho2;").
Hypothesis TGT_after0 : ltac2:(tb__ "0|1|
S10S4S30Q40A1A1S53R2A1S1S0S2eS33R3S15P191A1A2Z0M0A3S0S2eS33R3S15P19aA1A2G0A3A2S89S3S2bS3VJAFv;S53S91A2Sa9R4R3A5VQ;A3F_;F_;Ftp;Frho2;").
Hypothesis TGT_bodyE : ltac2:(tb__ "0|0|
S10S4S30Q40A1A1S54R2A1S89S3S2bS3VJAv;S92A1SabR3R2A5VQ;A3F_;Ftp;Frho2;").
Hypothesis TGT_afterE : ltac2:(tb__ "0|0|
S10S4S30Q40A1A1S54R2A1S89S3S2bS3VJAv;S92A1SaaR3R2A5VQ;A3F_;Ftp;Frho2;").
Hypothesis Hb1 : ltac2:(tb__ "0|0|
S0S5S35S11S27S78A1A1Vbd0;A2S6A3"). Hypothesis Hl1 : ltac2:(tb__ "0|0|
S0S5S71S13S27S78A1A1S5bVbd0;A3S6A3").
Hypothesis Hb2 : ltac2:(tb__ "0|0|
S0S5S35S11S27S77A1A1Vbd0;A2S6A3"). Hypothesis Hl2 : ltac2:(tb__ "0|0|
S0S5S71S13S27S77A1A1S5aVbd0;A3S6A3").
Hypothesis Hb3 : ltac2:(tb__ "0|0|
S0S5S35S11S27S76A1A1Vbd0;A2S6A3"). Hypothesis Hl3 : ltac2:(tb__ "0|0|
S0S5S71S13S27S76A1A1SadVbd0;A3S6A3").
Hypothesis Hb4 : ltac2:(tb__ "0|0|
S0S5S35S11S27S75A1A1Vbd0;A2S6A3"). Hypothesis Hl4 : ltac2:(tb__ "0|0|
S0S5S71S13S27S75A1A1SacVbd0;A3S6A3").
Hypothesis Hbr : ltac2:(tb__ "0|0|
S0S5S35S11S27S73A1A1S8S34Vbd0;S56A3A2S6A3").

Lemma bd_below_runX : ltac2:(tb__ "0|0|
S28S0S5Sc3S11S27S73A1A1S11S27R1A1A1A2S6A3S0S5S35S11S27R2A1A1S8S34Vbd0;S56A3A2S6A3F_;FT;").
Proof.
  intros T Hle. apply forallb_forall. intros it Hit. apply (proj1 (forallb_forall _ _) Hbr) in Hit.
  apply forallb_forall. intros ca Hca. eapply sv_below_mono; [apply Pos.leb_le; exact Hle | exact (proj1 (forallb_forall _ _) Hit ca Hca)].
Qed.

Lemma run1_complete : ltac2:(tb__ "0|0|
S10S4S30Q40A1A1S59R2A1S89S3S2bS3VJAv;S5eS57S52S8S34Vbd0;S56A3S5fA4A1S7cR3R2A5VQ;A3F_;Ftp;Frho;").
Proof.
  intros rho tp HP. pose proof run_checks as (_ & _ & C1 & _ & Cn1 & _ & CV1 & _ & Ct1 & Cf1 & _ & _ & Ce1 & _).
  apply (etriple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PA PhiP1 _ T_blr1 rho tp Q HP).
  apply (cfg_complete_autoA segs FUEL_lo cps_land (ss_next (ax_S T_blr1)) [mkVNA T_blr1 601 z0] [mkVNA XR_body1 600 z0; mkVNA XR_after1 600 z0]
           (JAFv PhiP1 (NDA tv1 frL (bd0 ++ ENDOW) ANone)) Q tp) with (n := mkVNA T_blr1 601 z0).
  - apply (stableA_JAF segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PA HKc V_P PhiP1 PhiP1_reads); [apply Pos.leb_le; exact Cn1 | | exact CV1].
    unfold nd_below. cbn [nd_tv nd_fr nd_bd nd_am]. rewrite Ct1, Cf1, (bd_below_runX T_blr1 Ce1). reflexivity.
  - intros n [<-|[]]. cbn [vna_state]. apply Pos.le_refl.
  - exact C1.
  - intros E rhoE [<-|[<-|[]]]; cbn [vna_state]; (eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw |]).
    + apply (TRe_pureP segs _ (tblL (rho_sub rhoE s_landB))).
      { intros w Hw. destruct (SPA_JAF_elim segs AInv CST XGL NP Kc rho0 P0 FB FF BX PA PhiP1 _ _ _ _ w Hw) as [Hw' HPe]. exact (proj1 (land_bodyN bd0 rhoE tp w Hb1 Hl1 HPe Hw')). }
      intros HT. eapply etriple_conseq; [ | intros w Hw; exact Hw | apply (TGT_bodyN (rho_sub rhoE s_landB) tp HT)].
      intros w Hw. destruct (SPA_JAF_elim segs AInv CST XGL NP Kc rho0 P0 FB FF BX PA PhiP1 _ _ _ _ w Hw) as [Hw' HPe]. exact (proj2 (land_bodyN bd0 rhoE tp w Hb1 Hl1 HPe Hw')).
    + apply (TRe_pureP segs _ (tblL (rho_sub rhoE s_landA))).
      { intros w Hw. destruct (SPA_JAF_elim segs AInv CST XGL NP Kc rho0 P0 FB FF BX PA PhiP1 _ _ _ _ w Hw) as [Hw' HPe]. exact (proj1 (land_after0 bd0 rhoE tp w Hb2 Hl2 HPe Hw')). }
      intros HT. eapply etriple_conseq; [ | intros w Hw; exact Hw | apply (TGT_after0 (rho_sub rhoE s_landA) tp HT (land_after0_cnt rhoE))].
      intros w Hw. destruct (SPA_JAF_elim segs AInv CST XGL NP Kc rho0 P0 FB FF BX PA PhiP1 _ _ _ _ w Hw) as [Hw' HPe]. exact (proj2 (land_after0 bd0 rhoE tp w Hb2 Hl2 HPe Hw')).
  - left. reflexivity.
Qed.

Lemma run0_complete : ltac2:(tb__ "0|0|
S10S4S30Q40A1A1S58R2A1S89S3S2bS3VJAv;S5eS57S52S8S34Vbd0;S56A3S5fA4A1S7bR3R2A5VQ;A3F_;Ftp;Frho;").
Proof.
  intros rho tp HP. pose proof run_checks as (_ & _ & _ & C0 & _ & Cn0 & _ & CV0 & _ & _ & Ct0 & Cf0 & _ & Ce0).
  apply (etriple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PA PhiP0 _ T_blr0 rho tp Q HP).
  apply (cfg_complete_autoA segs FUEL_lo cps_land (ss_next (ax_S T_blr0)) [mkVNA T_blr0 601 z0] [mkVNA XR_body0 600 z0; mkVNA XR_after0 600 z0]
           (JAFv PhiP0 (NDA tv1 frL (bd0 ++ ENDOW) ANone)) Q tp) with (n := mkVNA T_blr0 601 z0).
  - apply (stableA_JAF segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PA HKc V_P PhiP0 PhiP0_reads); [apply Pos.leb_le; exact Cn0 | | exact CV0].
    unfold nd_below. cbn [nd_tv nd_fr nd_bd nd_am]. rewrite Ct0, Cf0, (bd_below_runX T_blr0 Ce0). reflexivity.
  - intros n [<-|[]]. cbn [vna_state]. apply Pos.le_refl.
  - exact C0.
  - intros E rhoE [<-|[<-|[]]]; cbn [vna_state]; (eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw |]).
    + apply (TRe_pureP segs _ (ldef (rho_sub rhoE s_landBE))).
      { intros w Hw. destruct (SPA_JAF_elim segs AInv CST XGL NP Kc rho0 P0 FB FF BX PA PhiP0 _ _ _ _ w Hw) as [_ HPe]. exact (land_ldefBE rhoE HPe). }
      intros HLd. eapply etriple_conseq; [ | intros w Hw; exact Hw | apply (TGT_bodyE (rho_sub rhoE s_landBE) tp HLd)].
      intros w Hw. destruct (SPA_JAF_elim segs AInv CST XGL NP Kc rho0 P0 FB FF BX PA PhiP0 _ _ _ _ w Hw) as [Hw' _]. exact (land_bodyE bd0 rhoE tp w Hb3 Hl3 Hw').
    + apply (TRe_pureP segs _ (ldef (rho_sub rhoE s_landAE))).
      { intros w Hw. destruct (SPA_JAF_elim segs AInv CST XGL NP Kc rho0 P0 FB FF BX PA PhiP0 _ _ _ _ w Hw) as [_ HPe]. exact (land_ldefAE rhoE HPe). }
      intros HLd. eapply etriple_conseq; [ | intros w Hw; exact Hw | apply (TGT_afterE (rho_sub rhoE s_landAE) tp HLd)].
      intros w Hw. destruct (SPA_JAF_elim segs AInv CST XGL NP Kc rho0 P0 FB FF BX PA PhiP0 _ _ _ _ w Hw) as [Hw' _]. exact (land_afterE bd0 rhoE tp w Hb4 Hl4 Hw').
  - left. reflexivity.
Qed.

Theorem blr_land_complete : ltac2:(tb__ "0|2|
S4S34A1S10S4S30Q40A1A1S0S5S35S11S27S73A1M0A1R3A2S6A3SbaS8eVrho0;VP0;S13G0A1S16Z0M1A1G1R4S8S34SaeS8S34Vbd0;S56A3A3A8S89S3S2bS3VJAv;S5eS74S52R5S5fA4A1S7aR4R3A5VQ;A3F_;F_;Ftp;Frho;Fbd;").
Proof.
  intros bd rho tp Hbd HPAY.
  apply (X_E_blr (etriple segs) (TRe_facts segs) (TRe_ex segs) (TRe_pre segs) (TRe_pureP segs) (call_completePA3 segs)
           (fun FBc FFc BXc rho1 tp1 HB => BLRP.build_line_index_rom_sum_ex AInv CST XGL ALA HCST HXGL Kc HKc FBc FFc BXc HB rho1 ACX tp1)
           (bd0 ++ ENDOW) Q run1_complete run0_complete bd rho tp Hbd Hbr HPAY).
Qed.
End PackX.

End Sum.

Print Assumptions blr_land_sound.
Print Assumptions blr_land_complete.
End Lib_load_obj_land_pf.

