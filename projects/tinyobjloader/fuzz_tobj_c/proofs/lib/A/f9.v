(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f4 f7.
From Stdlib Require Permutation.

(* [comment removed for export] *)
Module Lib_load_obj_ap_eqs.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "true"; "bool"; "prod"; "nil"; "nat"; "app"; "list"; "@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bitem"; "batom"; "ASv"; "BI"; "AMin"; "bd_subst"; "bd_wpos"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SVar"; "ss_facts"; "ss_next"; "SLit"; "SAlu"; "SPUle"; "sprop"; "sprop_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f9.Lib_load_obj_ap_eqs"; "s_latch_p"; "Lok_p"; "nd_p_okX"; "Ys_p"; "bdX_p"; "Xf_p"; "Xs_p"; "Yf_p"; "bd_p_fX"; "comm_p"; "commf_p"; "nd_p_fX"; "cutsP"; "exitsP"; "extra_p"; "ndXE_p"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue"; "frL"; "V_B"; "extraLO"; "tvL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "AHead"; "NDA"; "nd_below"; "am_eqb"; "am_subst"; "fr_sub_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs"; "NP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop"; "pH"; "X_latch"; "pLNL"; "pPOS"; "xLD"; "xLK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f4.Lib_load_obj_ap"; "tv_p"; "kept_p"; "tv_p_ok"; "LAr"; "T_p_f"; "T_p_okR"; "qCURp"; "tv_p_f"; "E_p"; "R_p"; "Xk_p"; "bd_p_f"; "bd_p_ok"; "gPI'"; "k_pi"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG"; "bd_permb"; "tv_permb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud"; "LAX"; "LAXK"; "AK1"; "LAK"; "RL"; "VLA"; "bdX"; "z0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub_id_below"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs"; "kb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit2"; "lines_chk"; "robj_ent"; "robjs_chkC"; "xextraLO"; "xrs_chkC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_avn"; "PhisV"; "cps_arm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_loopE"; "X_latchE2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "tv_sub_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF"; "bud_le2"; "bud_pay2"; "ejcertAF"; "wsub_id_on"; "@Stdlib.Lists.List"; "In"; "existsb"; "@Stdlib.PArith.BinPos.Pos"; "leb"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_p.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ek.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_vec_reserveN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_p OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ek.Lib_handle_p_pf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_defs Lib_load_obj_pro.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eo.Lib_load_obj_pro2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_disp OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_hv0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_exits OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_loopE OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_avn OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f4.Lib_load_obj_ap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr LOAddr LOLAddr HVAddr HPAddr.

Definition Lok_p : axst := Eval vm_compute in leafL (runL 200 cps_arm T_p_okR) pc_latch 0.
Definition s_latch_p : wsub := ltac2:(tb__ "0|0|
S0S4ScS14A2S1ScS14P24aS4fA4S68S3bS31S1eA1S31S3dA1A3A3").
Definition bdX_p : list bitem := Eval vm_compute in bd_subst s_latch_p (bdX 0).
Definition nd_p_okX : ndesc := ltac2:(tb__ "0|0|
S36S44S2dS21S35S3cS2A2A4").
Definition ndX_p : ndesc := ltac2:(tb__ "0|0|
S36S42S2dS59Z0A1S35S3cS2A2A4").
Definition comm_p : list bitem := Eval vm_compute in bd_common bd_p_ok bdX_p.
Definition Xs_p : list bitem := Eval vm_compute in bd_minus bd_p_ok bdX_p.
Definition Ys_p : list bitem := Eval vm_compute in bd_minus bdX_p bd_p_ok.

Lemma ap_checks_pay : ltac2:(tb__ "0|27|
SaS9S3S51S4eS7SdS26S23A3A2S2A3SaS9S3S51S7SdS26S20A3S21A2S2A3SaS9S3S13S20A1S2A3SaS9S8SdA1M0S23S0SdS10Z48Z0M1S0S4SbSeA2M2S1SbSeZ1M3SfS19S5dS3eS3fA3A1A4S0G2S1SbSeN1SfS48A1A4S5G2A1M4A3A3G1A4S0SdS45S0SdS56S55A1S0SdS10G3G1S0G2S1SbSeZ18SfS15P1a6A1M5A1M6A4M7S0G2S1SbSeZ60M8S11G5G3G1G3A4A4M9S0G2S1SbSeZ8MaSfS15P1a9A1MbA1McA4MdS0G2S1SbSeG8S11GbG3G1G3A4A4MeS0G2S1SbSeGaSfS15P1acA1MfA1M10A4M11S0G2S1SbSeG8S11GfG3G1G3A4A4M12S0G2S1SbSeGaSfS15P1afA1M13A1M14A4M15S0G2S1SbSeG8S11G13G3G1G3A4A4M16S0G2S1SbSeZ78M17SfS15P1b2A1A1M18A4M19S0G2S1SbSeZ68SfS15P1b5A1A1M1aA4M1bS0G2S1SbSeG17SfS15P1b8A1A1M1cA4G4A3A3A3A3A3A3A3A3A3A3A3G1A4S0SdS10G1G3S0G2S1SbSeZ70M1dG6A4M1eS0G2S1SbSeZ50M1fGcA4M20S0G2S1SbSeG1fG10A4M21S0G2S1SbSeG1fG14A4M22S0G2S1SbSeG1dG18A4M23S0G2S1SbSeG1fG1aA4M24S0G2S1SbSeG1dG1cA4G4A3A3A3A3A3A3A3G1A4S5SdA1M25A3A3A3A3A3A3SaS9G0S20S0SdS53G1A1S0SdS54G1A1S0SdS10G3G1S0G2G7S0G2G9S0G2GdS0G2GeS0G2G11S0G2G12S0G2G15S0G2G16S0G2G19S0G2G1bS0G2S1SbSeG17SfS15P2faA1A1M26A4G4A3A3A3A3A3A3A3A3A3A3A3G1A4S0SdS10G1G3S0G2G1eS0G2G20S0G2G21S0G2G22S0G2G23S0G2G24S0G2S1SbSeG1dG26A4G4A3A3A3A3A3A3A3G1A4G25A3A3A3A3A3SaS9S14S48S15P2f8A1A3S9S3S37S17S31S47A1A1S1fA2S2A3A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Lemma ap_checks_exit : ltac2:(tb__ "0|5|
SaS9S3S33S1eS3dS1dA3S2A3SaS9S3S5cS1dS3bA2S2A3SaS9S3S70S3bS17S31S1eA1M0A1M1A2S2A3SaS9S3S37G1S1fA2S2A3SaS9S3S69S1dS44S42A3S2A3SaS9S3S3aS1dS2dS2dA3S2A3SaS9S3S6aS16G0A1S12S1dS59Z0A1A2S21A3S2A3SaS9S3S38S39S1dS35S3cS2A2M2A2G2A2S2A3SaS9S3S6dS2eS1dA2S2A3SaS9S14S5bS1dP1ccM3A2S15G3A1A3SaS9S14S5bS1dP1d3M4A2S15G4A1A3S9S3S52S42S30A2S2A3A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition Xf_p : list bitem := ltac2:(tb__ "0|0|
S0SdS45S0SdS56S55A1S5SdA1A3A3").
Definition Yf_p : list bitem := ltac2:(tb__ "0|1|
S0SdS53Z0M0A1S0SdS54G0A1S5SdA1A3A3").
Definition commf_p : list bitem := Eval vm_compute in bd_minus bd_p_f Xf_p.
Definition bd_p_fX : list bitem := Yf_p ++ commf_p.
Definition nd_p_fX : ndesc := ltac2:(tb__ "0|0|
S36S49S2dS25S35S3cS2A2A4").
Definition ndXE_p : ndesc := ltac2:(tb__ "0|1|
S36S42S2dS0SdS53Z0M0A1S0SdS54G0A1S5SdA1A3A3S35S3cS2A2A4").
Lemma ap_checks_payf : ltac2:(tb__ "0|2|
SaS9S3S51S4dS7SdS27S22A3A2S2A3SaS9S3S51S7SdS27S24A3S25A2S2A3SaS9S3S6bS16S31S46A1M0A1S18Z0M1A1G1S22S24A5S2A3SaS9S3S37S17G0A1S28A2S2A3S9S8S4S14S14A2A1S49S44A3A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition cutsP : list efnode := ltac2:(tb__ "0|6|
S0S4S4S4S32S34A2M0S6A2M1S4SbS14A2M2A2M3S1G1G2S1G0S6S1S32S34S47S1fA4U1M4A4S1SbS14S57S58ZaS5aA2A4M5A4S0G3S1G1G2S1G0S6S1S32S34S46S28A4G4A4G5A4S5G3A1A3A3").
Definition exitsP : list efnode := ltac2:(tb__ "0|6|
S0S4S4S4S32S34A2M0S6A2M1S4SbS14A2M2A2M3S1G1G2S1G0S6S1S32S34S1eS1fA4U1M4A4S1SbS14S57S58Z1S5aA2A4M5A4S0G3S1G1G2S1G0S6S1S32S34S67S2cA4G4A4G5A4S5G3A1A3A3").
Lemma ecertP_ok : ltac2:(tb__ "0|0|
S9S3S6cS5eS3bS65Uc8S66S3bS29S2aA8S2A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Definition extra_p (o : sobj) : bool := ltac2:(tb__ "0|0|
S3S3L_;S2fVo;A1S2S61Vo;A1X3x2").
Lemma ap_checks2 : ltac2:(tb__ "0|1|
SaS9S3S62S16S31S4aA1A1M0S43S2dS2bS4bA5S2A3SaS9S3S64G0S43S2dS63S4cA5S2A3SaS9S3S60G0A1S2A3S9S3S6fS1bS1cS1aS50S18ZffffffffA1A2A1G0A3S2A3A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma lines_in_kept_p : ltac2:(tb__ "0|0|
S6eS4S14S14A2S1S14S14S40S5fZ10S41A2A4S43A3").
Proof. cbn. do 17 right. left. reflexivity. Qed.
End Lib_load_obj_ap_eqs.

(* [comment removed for export] *)
Module Lib_load_obj_ap_pf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@Corelib.Init.Datatypes"; "prod"; "pair"; "list"; "nat"; "true"; "fst"; "snd"; "Some"; "app"; "bool"; "cons"; "nil"; "option"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sv"; "sprop"; "holds"; "ss_facts"; "ss_next"; "sobj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "PTrue"; "JA_pre"; "ANone"; "JA"; "TPA"; "amode"; "fbinA"; "ffinA"; "frinA"; "nd_am"; "ok_frameKA"; "tvinA"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "smatchA"; "@Corelib.Init.Logic"; "and"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ek.Lib_handle_p_pf"; "P0_hp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue"; "tblB"; "frL"; "P0_lo"; "@Stdlib.Lists.List"; "In"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF"; "efmeasA"; "phiK"; "JAF"; "phi_reads"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_sub"; "rho_absorb"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud"; "ndA1"; "RL"; "VLA"; "ndX0"; "z0"; "ndXE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_disp"; "E_hp"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f4.Lib_load_obj_ap"; "kept_p"; "PDk_p"; "R_p"; "T_p_ok"; "E_p"; "Xk_p"; "passed_p"; "rate_gp"; "s_p"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_avn"; "PhisV"; "h0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop"; "X_latch"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "J_ofPA"; "call_checkPA"; "entails_frA"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs"; "NPH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f4.Lib_load_obj_ap.HP"; "Pre_hp"; "nd0"; "Posts_hp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f9.Lib_load_obj_ap_eqs"; "Xs_p"; "Ys_p"; "cutsP"; "Lok_p"; "nd_p_okX"; "s_latch_p"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs"; "NP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_loopE"; "X_latchE2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "BXok_d"; "bxt"; "bd_nn"; "bsumK"; "bsumV"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.TobjJAH"; "ndh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK"; "PostsCk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "call_linkP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "AE_A"; "alloc_contractsA";
"alloc_contractsA_ex"; "alloc_lawsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_geom"; "topG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_fuzz_iface"; "in_lits"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "FBx"; "T_ok"; "tvd"; "tvz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3"; "import_okPA3"; "import_postA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "FFx"; "robjs_okF"; "xrs_okF"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_p.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ek.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_vec_reserveN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_p OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ek.Lib_handle_p_pf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_defs Lib_load_obj_pro.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eo.Lib_load_obj_pro2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_disp OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_hv0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_exits OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_loopE OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_avn OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f4.Lib_load_obj_ap OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f9.Lib_load_obj_ap_eqs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr LOAddr LOLAddr HVAddr HPAddr.

Lemma PhisV_reads : ltac2:(tb__ "0|3|
S38S1S3SfA1M0S13OF_;M1A2M2G2S3dS6G0G1R1A3S7G0G1R1A3A2Lp;S55A3").
Proof. constructor; [exact tblL_reads | constructor; [exact tblB_reads | constructor]]. Qed.

Lemma h0_ltH : (h0 < NPH)%positive. Proof. reflexivity. Qed.
Lemma HamC_p : nd_am HP.nd0 = ANone. Proof. reflexivity. Qed.
Lemma HamPD_p : ltac2:(tb__ "0|1|
S38S1S10S1aA2M0G0S2cS20S24S7S10S1aR1A3A1S1dA3Ld;S62A3"). Proof. repeat constructor. Qed.
Lemma P0_hp_mono : ltac2:(tb__ "0|2|
S3S1SeSeA2M0A1M1G1G1S3S1G0SeA2A1S13G0S35G0R1R5A3S35G0R2R5A3F_;Fbn;S31R6R5R3R2A4S31R7R5R4R3A4F_;F_;Fr;FFFc;FF';FF;FCST;").
Proof.
  intros CST F F' FFc r HS ((A & B & C) & E). split; [|exact E]. split; [|split; [exact B | exact C]].
  intros a Ha. apply (pclMA_mono CST r F F' FFc FFc a HS (fun x H => H)). exact (A a Ha).
Qed.

Lemma pay_p : ltac2:(tb__ "0|0|
S13S38S15S16R1A1S17S11S4fA1A1A3S6dS63R2A2S2bS36S6fS64R3A2S6fS63R3A2A2S2bS36S6eS64R3A2S6eS63R3A2A2S6dS64R3A2A2A2F_;F_;Fr;").
Proof.
  intros r HF _. pose proof ap_checks_pay as (_ & _ & _ & EX & EY & EQ & _). rewrite EX, EY. rewrite EQ.
  fact HF (SPUle (SVar 480) (SLit 67108864)) F1. fact HF (SPUle (SAlu ALU_ADD (SVar 480) (SVar 481)) (SVar 14)) F2.
  fact HF (SPUle (SVar 14) (SLit 67108864)) F3. fact HF (SPUle (SVar 490) (SVar 480)) F4. fact HF (SPUle (SVar 480) (SVar 476)) F5.
  fact HF (SPUle (SVar 760) (SAlu ALU_ADD (SVar 481) (SVar 480))) F6. fact HF (SPUle (SAlu ALU_ADD (SVar 762) (SVar 476)) (SAlu ALU_ADD (SVar 440) (SVar 760))) F7.
  fact HF (SPUle (SVar 440) (SLit 4294967295)) F8. fact HF (SPUle (SVar 762) (SVar 763)) F9. fact HF (SPUle (SVar 763) (SLit 4294967295)) F10.
  fact HF (SPUle (SVar 476) (SAlu ALU_ADD (SVar 481) (SVar 480))) F11.
  rewrite h_ule in F1, F2, F3, F4, F5, F6, F7, F8, F9, F10, F11. rewrite uval_lit in F1, F3, F8, F10 by lia.
  pose proof (uval_range r (SVar 481)) as R481. pose proof (uval_range r (SVar 480)) as R480. pose proof (uval_range r (SVar 760)) as R760.
  pose proof (uval_range r (SVar 762)) as R762. pose proof (uval_range r (SVar 476)) as R476. pose proof (uval_range r (SVar 440)) as R440. pose proof (uval_range r (SVar 490)) as R490.
  pose proof (uval_range r (SVar 422)) as R422. pose proof (uval_range r (SVar 425)) as R425. pose proof (uval_range r (SVar 428)) as R428.
  pose proof (uval_range r (SVar 431)) as R431. pose proof (uval_range r (SVar 434)) as R434. pose proof (uval_range r (SVar 437)) as R437.
  fact HF (SPUle (SVar 481) (SLit 67108864)) F12. rewrite h_ule, uval_lit in F12 by lia.
  assert (E1 : uval r (SAlu ALU_ADD (SVar 480) (SVar 481)) = uval r (SVar 480) + uval r (SVar 481)) by (apply uval_add_small; lia).
  rewrite E1 in F2.
  assert (E2 : uval r (SAlu ALU_ADD (SVar 481) (SVar 480)) = uval r (SVar 481) + uval r (SVar 480)) by (apply uval_add_small; lia).
  rewrite E2 in F6, F11.
  assert (E3 : uval r (SAlu ALU_ADD (SVar 762) (SVar 476)) = uval r (SVar 762) + uval r (SVar 476)) by (apply uval_add_small; lia).
  assert (E4 : uval r (SAlu ALU_ADD (SVar 440) (SVar 760)) = uval r (SVar 440) + uval r (SVar 760)) by (apply uval_add_small; lia).
  rewrite E3, E4 in F7.
  unfold LAr, LAX, LAK, LAXK, A1, AK1, pLNL, pPOS, pNX, vLEN. cbv beta iota delta [bsumV bsumK bival lfval aval bi_v bi_k bi_f bi_c]. rewrite E2.
  split; [lia|]. split; [lia|].
  unfold bd_nn. repeat constructor; cbv beta iota delta [bival lfval aval bi_v bi_k bi_f bi_c]; rewrite ?E2; lia.
Qed.

Lemma rate_gp_holds : ltac2:(tb__ "0|0|
S13S38S15S16R1A1S17S11S4fA1A1A3S38S15S16R2A1SbS15S53ScS15A1A3A3F_;Fr;").
Proof.
  intros r HF. pose proof ap_checks_pay as (_ & _ & _ & _ & _ & EQ & _).
  fact HF (SPUle (SVar 480) (SLit 67108864)) F1. fact HF (SPUle (SAlu ALU_ADD (SVar 480) (SVar 481)) (SVar 14)) F2.
  fact HF (SPUle (SVar 14) (SLit 67108864)) F3. fact HF (SPUle (SVar 490) (SVar 480)) F4. fact HF (SPUle (SVar 480) (SVar 476)) F5.
  fact HF (SPUle (SVar 760) (SAlu ALU_ADD (SVar 481) (SVar 480))) F6. fact HF (SPUle (SVar 586) (SVar 490)) F7. fact HF (SPUle (SVar 476) (SVar 760)) F8.
  fact HF (SPUle (SVar 481) (SLit 67108864)) F9.
  rewrite h_ule in F1, F2, F3, F4, F5, F6, F7, F8, F9. rewrite uval_lit in F1, F3, F9 by lia.
  pose proof (uval_range r (SVar 481)) as R481. pose proof (uval_range r (SVar 480)) as R480. pose proof (uval_range r (SVar 760)) as R760.
  pose proof (uval_range r (SVar 476)) as R476. pose proof (uval_range r (SVar 586)) as R586. pose proof (uval_range r (SVar 490)) as R490.
  assert (E2 : uval r (SAlu ALU_ADD (SVar 481) (SVar 480)) = uval r (SVar 481) + uval r (SVar 480)) by (apply uval_add_small; lia). rewrite E2 in F6.
  assert (ES : uval r (SAlu ALU_SUB qCURp pCP) = uval r (SVar 760) - uval r (SVar 476)) by (rewrite EQ; unfold pCP; apply uval_sub_le; exact F8).
  constructor; [|constructor]. unfold rate_gp, gPI', pE0, gPI, pPOS, pLNL. apply (proj2 (h_ule _ _ _)).
  rewrite uval_add_small by (rewrite ES; lia). rewrite ES.
  rewrite uval_add_small by (rewrite uval_add_small, uval_lit by lia; lia). rewrite uval_add_small by lia. rewrite uval_lit by lia. lia.
Qed.

Section Sum.
Variable AInv : ltac2:(tb__ "0|0|
S7aS13S3S27Q40A1A1S42OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
S79S0VAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
SeS72VCST;R1A2S2bS36Z0R2A2S37R2S75A2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
SeS72VXGL;R1A2S2bS36Z0R2A2S37R2S75A2A2F_;Fa;").
Hypothesis HXlits : ltac2:(tb__ "0|0|
SeS7dR1A1S72VXGL;R2A2F_;Fa;").
Hypothesis LFLAG : law_flag_stmt AInv.
Hypothesis LFSH : law_fshadow_stmt AInv.
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S3S1S1SeSeA2SeA2A1").
Variable BX : bxt.
Hypothesis HBX : BXok_d 7 BX.
Variable rho0 : valuation.

Hypothesis HFF0 : ccount 0 (map fst FF) = 0%nat.
Let HNP : NP_okA NP := NP_okA_intro NP eq_refl.
Let P0 : ltac2:(tb__ "0|0|
S13OFr;") := ltac2:(tb__ "0|0|
S34VCST;VFB;VFF;A3").
Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S1eVAInv;VCST;VXGL;S69VKc;Vrho0;VP0;VFB;VFF;VBX;S1bVnd;Ac").
Let JAFv (Phi : valuation -> Prop) (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S3cVAInv;VCST;VXGL;S69VKc;Vrho0;VP0;VFB;VFF;VBX;S1bVPhi;Vnd;Ad").

Lemma HIN_p : ltac2:(tb__ "0|1|
S13S4bS7aS13S3S27Q40A1A1S42S38S15S16R6A1S17S11S50A1A1A3VP0;Vrho0;A1S73S69Vrho0;R8A3VAInv;R7R6R5R4A4S1fVrho0;R8A2S7fRbS7cS7bR9A1A1A2S21VFB;RaA2S22VFF;RbA2S26VFB;RcReS9S1S14S14A2S4cS52A3M0A4S80RfG0A2S81R10G0A2S23VFF;RfR11S33A4S2bS85VCST;Vrho0;VFB;VFF;R12S4cS33S4eA8S2bS86VCST;VXGL;Vrho0;VFB;VFF;R12S4cS33S51A9S31VCST;S7eVFB;R12S4cA3S84VFF;R12S33A3S3eS3fR12S4eR11A3S54A2A4A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FAi;Fms;Frho;").
Proof.
  intros rho ms Ai rho1 tp1 md1 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR.
  pose proof ap_checks2 as (CR & CX & CLN & _).
  pose proof (T_ok_T0 rho0 rho Ai HT HTK) as HT0.
  assert (HNk : tvinA FB Ai rho kept_p) by (apply (tvinA_sublist FB Ai rho (kept_p ++ passed_p)); [intros t Ht; apply in_or_app; left; exact Ht | exact HN]).
  assert (HDk : tvd rho kept_p) by (exact (tvd_app_l rho kept_p passed_p HD)).
  assert (HZk : tvz rho kept_p) by (apply (tvz_sublist rho (kept_p ++ passed_p)); [intros t Ht; apply in_or_app; left; exact Ht | exact HZ]).
  split; [|split].
  - apply (robjs_chkC_sound AInv CST ALA HCST rho0 FB FF Ai rho _ kept_p frL extra_p R_p rho1 tp1 md1 HM HF HT HT0 HNk HDk HZk HFR CR).
    intros o a Ho HE Hr. unfold extra_p in HE. apply lazy_orb_prop in HE as [HE|HE].
    + exact (extraLO_pclMA CST rho0 FB FF rho kept_p frL o a Hav HP0 HE Hr).
    + exact (robj_ent_pclMA CST rho0 FB FF rho _ _ kept_p frL o a HF CLN HT0 HZk lines_in_kept_p HE Hr).
  - apply (xrs_chkC_sound AInv CST XGL ALA HXlits rho0 FB FF Ai rho _ kept_p frL xextraLO Xk_p rho1 tp1 md1 HM HF HT HT0 HNk HDk HZk HFR CX).
    intros r a Hr HE Ha. left. exact (xextraLO_pclMA CST rho0 FB FF rho kept_p frL r a Hav HP0 HE Ha).
  - pose proof ap_checks as (_ & _ & _ & Cta & _).
    destruct HP0 as (Ptxt & Pcfg & Plnk).
    assert (AG : forall v e, e = SVar v -> (v < NP)%positive -> uval rho e = uval rho0 e).
    { intros v e -> Hv. unfold uval. cbn [eval]. rewrite <- (proj1 Hav v Hv). reflexivity. }
    unfold P0_hp, P0_builder. rewrite !rw_call'.
    change (wsub_get s_p 15) with vBUF. change (wsub_get s_p 18) with vLEN. change (wsub_get s_p 12) with bA. change (wsub_get s_p 58) with alA.
    repeat change (bv_unsigned (eval rho ?e)) with (uval rho e).
    fact HF (SPUle vF (SLit 140737479964672)) HvF. rewrite h_ule, uval_lit in HvF by lia.
    assert (E544 : uval rho (SLit 544) = 544) by (apply uval_lit; lia). assert (E464 : uval rho (SLit 464) = 464) by (apply uval_lit; lia).
    assert (EbA : uval rho bA = uval rho vF + 544) by (unfold bA; rewrite <- E544; apply uval_add_small; rewrite E544; lia).
    assert (EalA : uval rho alA = uval rho vF + 464) by (unfold alA; rewrite <- E464; apply uval_add_small; rewrite E464; lia).
    assert (HinF : In (uval rho vF, fs_frame_size 5, uval rho vFL) (FFx FF rho frL)).
    { apply In_FFx. right. exists (vF, 5, vFL). split; [left; reflexivity | reflexivity]. }
    change (fs_frame_size 5) with 2048 in HinF.
    split; [split; [|split]|].
    + intros a Ha. unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC.pclMA. rewrite (T0_calleeA NP rho0 s_p rho R_p ms Hav Cta). fold (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC.pclMA CST rho0 (FBx FB rho kept_p) (FFx FF rho frL) a).
      apply (pclMA_mono CST rho0 FB (FBx FB rho kept_p) FF (FFx FF rho frL) a); [intros x Hx; apply In_FBx; left; exact Hx | intros x Hx; apply In_FFx; left; exact Hx |].
      apply Ptxt. rewrite <- (AG 13%positive vBUF eq_refl ltac:(reflexivity)), <- (AG 14%positive vLEN eq_refl ltac:(reflexivity)). exact Ha.
    + exists (uval rho vF), 2048, (uval rho vFL). split; [exact HinF|]. rewrite EbA. lia.
    + exists (uval rho vF), 2048, (uval rho vFL). split; [exact HinF|]. rewrite EalA. lia.
    + unfold FFx. rewrite map_app, ccount_app. cbn [map fst frL]. rewrite HFF0. reflexivity.
Qed.

Section X.
Variable TR : assn -> assn -> Prop.
Variable FAM : ltac2:(tb__ "0|0|
SeS3S27Q40A1A1S2dF_;F_;").
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S29S10S13S3S27Q40A1A1S2dS38S15S16R3A1S17S11R4A1A1A3VTR;S28S0R6R5R4R3A5R2A2M0F_;G0F_;FQ;Ftp;Frho;FS;FJ;").
Hypothesis TR_ex : forall (T : Type) (J : T -> jpredA) S rho tp (Q : assn),
  (forall x, TR (SPA segs (J x) S rho tp) Q) -> TR (SPA segs (fun r p t m => exists x, J x r p t m) S rho tp) Q.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S2dS2dS2dS30R3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_pureP : ltac2:(tb__ "0|1|
S2dOS2dS30R4R1A1R4F_;Fw;R3VTR;R5R3A2M0F_;G0F_;F_;FQ;FX;FP;").
Hypothesis TR_callP : ltac2:(tb__ "0|5|
S29S29S10S10S40S3S19A1M0S3S1S10S59A2M1A1S3S1S14S14A2M2A1S2dS13S3S27Q40A1A1M3G2S35G2R1R5A3S35G2R2S12RbA1A3F_;Fr;S2cSdG0A1S5cRaR9R8A3S8G0R7A2A3S2cSaS5bRbRaR9R8S39G1S10S6S10S59A2R7A4A5S5A3S13G3VTR;S28S0RfRdR2R1A5S58S0S18S11RdA1A1R2R1RaA5A2Ftp1;Frho1;S3S43A1M4S4bS42S2aS0R9R8R10S2G4S5dR3S5eR2R1A2A4A5R13RaR9R4R2A4R13S3eS3fRbRfS41R3RaR4A3A3R10A2RaR5R3A4F_;F_;Fmd;Fms;Ftr;S10S59G4S4bS42S13G3G4S4bS42S35G1S2S10S59RaR9A4R14A3S2aS0R12R11R19S2G4S5dR9S5eR8R7A2A4A5R1cR13R12RaR8A4S73S18S11R1aA1A1S3eS3fR14R18S41R9R13RaA3A3R19A2R8A3S2aS0R9R8ReS2G4S5dR7S5eR6R5A2A4A5ReS3eS3fR16R1aS41RbR15RcA3A3R1bA2R15RaR9R8R6A6S2bS82R17S41RcR16RdA3R1bR1cR1dR10R1eR19RbA9S13S74R18S41RdR17ReA3R1cR1dS11R1eA1S11R1fA1S11R11A1R1RcA9VTR;S28S0S5aR11S3eS3fR19R1dS41ReR18RfA3A3R1eA2R18RdRcA5S83R1eR1fR12R20R1dR1bA6R2RcA5R1aA2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S28S0R11RfR8R7A5R9A2F_;F_;F_;F_;F_;F_;Ftp;Frho;FQ;FXk;FPosts;FR;Fs;FPre;FC;FJp;FJ;").
Hypothesis TR_JAF : ltac2:(tb__ "0|0|
S13OF_;S1aS10S13S3S27Q40A1A1S2dR6R3A1VTR;S28S0VJAv;R6A1R5R4R3A5R2A2F_;VTR;S28S0VJAFv;R7R6A2R5R4R3A5R2A2F_;FQ;Ftp;Frho;FA;Fnd;FPhi;").
Hypothesis CHP : ltac2:(tb__ "0|1|
S3S1SeSeA2M0A1S3S1G0SeA2A1S6cS13S3S27Q40A1A1S6bZ5R3A2VTR;S28S0S1cVAInv;VCST;VXGL;VKc;S31VCST;R6R5A3R6R5R4S1bS70S56S5S61A3AaS60R3R2A5S58S0S5fR3R2S71VAInv;VCST;VXGL;VKc;S31VCST;A1S1bS4dR6R5R4AaA5A2F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Hypothesis CUTV : ltac2:(tb__ "0|5|
S10S1aS4S1SeS14A2M0S13S3S27Q40A1A1M1SeG1S35S1S1S1S10S1aA2M2S4A2M3G0A2S2G3G0S2G2S4S2S10S1aR8R7A4R6A4R5A4S65A3S3bS55R7R5A3S2bS36Z0S3aS2G3G0S2G2S4S2S10S1aRaR9A4R8A4R7A4R6A2M4A2S37G4R4A2A2VTR;S28S0VJAv;RaA1RbR7R6A5VFAM;R5R4A2A2F_;F_;F_;Ftp0;Fb;Ftp;Frho;Frv;Fk;Fnd;FT;").

Theorem arm_p : ltac2:(tb__ "0|2|
S13S3S27Q40A1A1M0G0VTR;S28S0VJAFv;S32S44A2S4aR3R2A5VFAM;S3aS2S1S1S10S1aA2M1S4A2S1SeS14A2S2G1S4S2S10S1aS4aS44A4U1A4S2SeS14S45S46Z11S48A2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros HPHI.
  pose proof ap_checks as (Cxf & Cent & Cchk & Cta & Cdom & Ctvs & Cam & Cpd & Cptv & Cptv' & Cpbd & Cxk & PP1 & PP2 & PWc & PPay & Cnb & Cbr & Cnp & Cnx).
  pose proof ap_checks2 as (_ & _ & CLN & _).
  set (ndv := NDA tv_p frL bd_p (AHead pH true)).

  apply (TR_pre (SPA segs (JAv ndv) E_p rho tp)).
  { intros w Hw. apply (SPA_axforms segs (JAv ndv) xf_p rho E_hp E_p tp w Cxf).
    unfold ndv, tv_p. apply (SPA_bd_permb segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue _ frL (bdA A1) bd_p _ E_hp rho tp w Cpbd).
    apply (SPA_tv_permb segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tvL _ frL (bdA A1) _ E_hp rho tp w Cptv). exact Hw. }
  apply TR_facts. intros HF.
  apply (TR_pureP _ (uval rho xLD <> 0)).
  { intros [tr [ms md]] [_ (Ai & kc & Hav & _ & _ & HT & _ & _ & (_ & _ & HZ) & _)]. cbn [nd_tv ndv] in HZ.
    pose proof (T_of_TPA NP rho0 rho Ai Hav ltac:(reflexivity) HT) as HTK.
    apply (lines_nz rho _ (topG (aa_geom Ai)) tv_p HF CLN HTK HZ). unfold tv_p. apply in_or_app. left. exact lines_in_kept_p. }
  intros Hdnz.

  unfold ndv, tv_p.
  apply (client_callT_k segs AInv CST XGL ALA HCST HXGL NP Kc rho0 P0 FB FF BX PTrue HKc HBX (P0_hp CST) PTrue (fun _ H => H) (fun _ _ _ H => H)
           HP.Pre_hp (ndh h0 true HP.nd0) PDk_p NPH eq_refl eq_refl eq_refl TR TR_facts TR_ex TR_pre TR_callP CHP eq_refl
           E_p s_p R_p Xk_p rho tp kept_p passed_p frL bd_p brest_p (AHead pH true) (FAM (efmeasA (E_hp, ndA1, 1%nat, (RL, VLA 17 z0)) rho) tp0)
           Cxk Cent Cchk Cta Cdom Cnp Cnb Cbr Ctvs Cam).
  -
    unfold payA. apply (pay_okF_split _ _ _ _ bd_p _ payC_p payX_p payY_p PP1 PP2 PWc PPay).
  - exact Cpd.
  - intros Ai ms HF' HP0 Hav HBf HFF HN HD HZ HFR (rho1 & tp1 & md1 & HM) HT HTK.
    exact (HIN_p rho ms Ai rho1 tp1 md1 HF' HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR).
  -
    intros [[Ld ndL] PsiL] rho' tp' Hd Hag HK _. rewrite Cnx in Hag.
    assert (HPHI' : tblB rho').
    { fact HF (SPUle (SVar 30) (SLit 140737479966720)) HtB. rewrite h_ule, uval_lit in HtB by lia.
      fact HF (SPUle (SLit 140735332483072) (SVar 30)) HtA. rewrite h_ule, uval_lit in HtA by lia.
      destruct (lines_blk rho _ (uval rho (SVar 30)) HF CLN ltac:(split; [reflexivity | lia])) as (_ & HiC & HcK & Hk32 & _ & HdT).
      apply (tblB_kept rho rho' (V_B_agree rho rho' Hag)); [| exact HiC | exact HcK | exact HPHI].
      apply (keptK_lines CST FB FF rho0 rho kept_p frL rho' HK lines_in_kept_p Hdnz); [lia | unfold B32, Lib_vec_reserve.B32; lia]. }
    fact HF (SPUle xLC vLEN) HcL. rewrite h_ule in HcL. fact HF (SPUle vLEN (SLit 67108864)) HL26. rewrite h_ule, uval_lit in HL26 by lia.
    fact HF (SPUlt pI xLC) HiC. rewrite h_ult in HiC.
    pose proof ap_checks_nd as (Cndo & Cndf & CTo & CTf & Bo & Bf & Tio & Tif & RT & Rfb).
    cbn [PDk_p liftPD PDh HP.Posts_hp map In fst snd] in Hd. destruct Hd as [Hd|[Hd|[]]]; injection Hd as <- <- <-; cbn [fst snd].
    +
      rewrite CTf, Cndf.
      apply (TR_pre (SPA segs (JAv nd_p_f) T_p_f rho' tp')).
      { intros w Hw. rewrite <- Tif. apply SPA_tidy. exact (SPA_axforms segs (JAv nd_p_f) (xfb_p T_p_f0) rho' T_p_f0 B_p_f tp' w Bf Hw). }
      apply TR_facts. intros HFf. pose proof ap_checks_payf as (QP1 & QP2 & QPay & _ & _).
      apply (TR_pre (SPA segs (JAv nd_p_fX) T_p_f rho' tp')).
      { intros w Hw. unfold nd_p_fX, nd_p_f in *.
        exact (SPA_bd_repay AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tv_p_f frL (AHead pH true) bd_p_f commf_p Xf_p Yf_p bd_p_fX _ T_p_f rho' tp' w QP1 QP2 HFf QPay Hw). }
      apply (CUTV T_p_f nd_p_fX 1%nat (RL, VLA 10 z0) rho' tp'); [right; left; reflexivity | exact HPHI' |].
      apply (VLA_lt rho rho' 17 10 z0 E_hp T_p_f ndA1 nd_p_fX 1%nat 1%nat); [symmetry; apply (proj1 Hag); reflexivity | symmetry; apply (proj1 Hag); reflexivity | exact HiC | lia | unfold z0; rewrite uval_lit by lia; lia | lia | lia].
    +
      rewrite CTo, Cndo.
      apply (TR_pre (SPA segs (JAv nd_p_ok) T_p_ok rho' tp')).
      { intros w Hw. rewrite <- Tio. apply SPA_tidy. exact (SPA_axforms segs (JAv nd_p_ok) (xfb_p T_p_ok0) rho' T_p_ok0 B_p_ok tp' w Bo Hw). }
      apply TR_facts. intros HFo. pose proof ap_checks_pay as (PQ1 & PQ2 & PWy & _).

      apply (TR_pre (SPA segs (JAv nd_p_okX) T_p_okR rho' tp')).
      { intros w Hw. rewrite <- RT. apply (SPA_refacts_JA segs); [| exact Rfb | intros tr md _ _; apply Forall_app; split; [exact (rate_gp_holds rho' HFo) | exact HFo]].
        unfold nd_p_okX, nd_p_ok in *.
        exact (SPA_bd_repay_sem AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tv_p_ok frL (AHead pH true) bd_p_ok comm_p Xs_p Ys_p bdX_p _ T_p_ok rho' tp' w PQ1 PQ2 PWy HFo (pay_p rho') Hw). }
      apply (CUTV T_p_okR nd_p_okX 1%nat (RL, VLA 10 z0) rho' tp'); [left; reflexivity | exact HPHI' |].
      apply (VLA_lt rho rho' 17 10 z0 E_hp T_p_okR ndA1 nd_p_okX 1%nat 1%nat); [symmetry; apply (proj1 Hag); reflexivity | symmetry; apply (proj1 Hag); reflexivity | exact HiC | lia | unfold z0; rewrite uval_lit by lia; lia | lia | lia].
Qed.
End X.

Lemma Lok_p_latch : ltac2:(tb__ "0|1|
S13S3S27Q40A1A1S30S32R3A1S28S0VJAv;S67A1S66R4R3R2A6S2bS32S3eR5S68A2M0A1S28S0VJAv;S47A1S57G0R4R3A6A2F_;F_;Fw;Ftp;Frho;").
Proof.
  intros rho tp w HP HS. pose proof ap_checks_exit as (Xe & Xid & Xnp & Xnb & Xtv & Xfr & Xbd & Xam & XV & _ & _ & Xperm).
  destruct (latch_exit AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc Lok_p X_latch s_latch_p nd_p_okX tv_p (bdX 0) (AHead pH true) tblB V_B rho tp w
              tblB_reads Xe Xid Xnp Xnb Xtv Xfr Xbd Xam XV HP HS) as [HP' HS'].
  split; [exact HP'|]. unfold ndX0, ndL. exact (SPA_tv_permb segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tv_p tvL frL (bdX 0) (AHead pH true) X_latch _ tp w Xperm HS').
Qed.

Section Safety.
Variable ok : world -> Prop.
Hypothesis Hok : ltac2:(tb__ "0|0|
S25S0VKc;Vok;A3").
Hypothesis AC : ltac2:(tb__ "0|0|
S77S0S76VAInv;VCST;VXGL;A5").
Variable FAMQ : list word -> assn.
Hypothesis XLATCH : ltac2:(tb__ "0|1|
S13S3S27Q40A1A1M0G0S2fS0Vok;S28S0VJAFv;S32S47A2S57R3R2A5VFAMQ;R1A1A4Ftp0;Ftp;Frho;").
Hypothesis XLATCHE2 : ltac2:(tb__ "0|1|
S13S3S27Q40A1A1M0G0S2fS0Vok;S28S0VJAFv;S32S49A2S6aR3R2A5VFAMQ;R1A1A4Ftp0;Ftp;Frho;").

Lemma CHP_T : ltac2:(tb__ "0|1|
S3S1SeSeA2M0A1S3S1G0SeA2A1S6cS13S3S27Q40A1A1S6bZ5R3A2S2fS0Vok;S28S0S1cVAInv;VCST;VXGL;VKc;S31VCST;R6R5A3R6R5R4S1bS70S56S5S61A3AaS60R3R2A5S58S0S5fR3R2S71VAInv;VCST;VXGL;VKc;S31VCST;A1S1bS4dR6R5R4AaA5A4F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Proof.
  intros FBc FFc BXc rho1 tp1 HB. unfold PDk_p.
  eapply (sum_PostsC_k segs AInv CST XGL Kc (P0_hp CST) PTrue HP.Pre_hp (ndh h0 true HP.nd0) (PDh HP.Posts_hp h0 true) NPH); [|exact Hok|exact HB].
  intros ok' FBc' FFc' BXc' rho2 tp2 Hok' HB'.
  eapply (JA_frame_sum segs AInv CST XGL ALA Kc (P0_hp CST) PTrue HP.Pre_hp HP.nd0 HP.Posts_hp NPH h0 true h0_ltH HamC_p HamPD_p (P0_hp_mono CST) ok'); [|exact HB'].
  intros FBc'' FFc'' BXc'' rho3 tp3 HB''. exact (handle_p_sum AInv CST XGL ALA HCST HXGL LFLAG LFSH Kc HKc FBc'' FFc'' BXc'' HB'' rho3 ok' Hok' AC tp3).
Qed.

Lemma CUTV_T : ltac2:(tb__ "0|5|
S10S1aS4S1SeS14A2M0S13S3S27Q40A1A1M1SeG1S35S1S1S1S10S1aA2M2S4A2M3G0A2S2G3G0S2G2S4S2S10S1aR8R7A4R6A4R5A4S65A3S3bS55R7R5A3S2bS36Z0S3aS2G3G0S2G2S4S2S10S1aRaR9A4R8A4R7A4R6A2M4A2S37G4R4A2A2S2fS0Vok;S28S0VJAv;RaA1RbR7R6A5VFAMQ;R4A1A4F_;F_;F_;Ftp0';Fb;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof.
  intros T nd k rv rho tp b tp0' Hin Hphi _.
  apply (triple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisV k) ok nd T rho tp _ Hphi).
  apply (cfg_sound_JAF segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc PhisV PhisV_reads 200%nat cps_arm NP (map efdrop cutsP) (map efdrop exitsP) ok (FAMQ tp0') Hok
           (ejcertAF_jcertAF segs NP PhisV _ _ _ _ _ ecertP_ok)); [| apply in_map_iff; exists (T, nd, k, rv); split; [reflexivity | exact Hin]].
  intros X ndX kX rho1 tp1 HinX. apply in_map_iff in HinX as ([[[X' nd'] k'] rv'] & E & HinX). cbn in E. injection E as <- <- <-.
  cbn [exitsP In] in HinX. destruct HinX as [E|[E|[]]]; injection E as <- <- <- <-; cbn [efdrop fst snd].
  -
    apply (triple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisV 1) ok). intros HP1.
    eapply triple_conseq; [| intros w Hw; right; exact Hw | exact (XLATCH (rho_sub rho1 s_latch_p) tp1 tp0')].
    intros w Hw. destruct (Lok_p_latch rho1 tp1 w HP1 Hw) as [HP' Hw']. exact (SPA_JAF_intro segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tblB ndX0 X_latch _ tp1 w Hw' HP').
  - eapply triple_conseq; [| intros w Hw; right; exact Hw | exact (XLATCHE2 rho1 tp1 tp0')].
    intros w Hw. unfold ndXE, ndL. apply (SPA_tv_permb_F segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tblB tv_p tvL frL [LAX 0; LAXK 0] (AHead pH true) X_latchE2 rho1 tp1 w (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 ap_checks_exit)))))))))))). exact Hw.
Qed.

Theorem arm_p_T : ltac2:(tb__ "0|1|
S13S3S27Q40A1A1M0G0S2fS0Vok;S28S0VJAFv;S32S44A2S4aR3R2A5VFAMQ;R1A1A4Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0.
  exact (arm_p (triple segs ok) (fun _ tp0 => FAMQ tp0) (TRs_facts segs ok) (TRs_ex segs ok) (TRs_pre segs ok) (TRs_pureP segs ok) (call_soundPA3 segs ok)
           (fun Phi nd A rho tp Q H => triple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue Phi ok nd A rho tp Q H)
           CHP_T CUTV_T rho tp tp0).
Qed.
End Safety.

Section Existence.
Hypothesis ACX : ltac2:(tb__ "0|0|
S78S0S76VAInv;VCST;VXGL;A5").
Variable FAM : ltac2:(tb__ "0|0|
SeS3S27Q40A1A1S2dF_;F_;").
Hypothesis FAM_mono : ltac2:(tb__ "0|0|
SeSeS3S27Q40A1A1S30S36R4R3A2VFAM;R5R3R2A3VFAM;R5R4R3A3F_;F_;Fw;Ftp0;Fb';Fb;").
Hypothesis XLATCH : ltac2:(tb__ "0|2|
S13S3S27Q40A1A1M0G0S2eS0S28S0VJAFv;S32S47A2S57R3R2A5VFAM;S3aS2S1S1S10S1aA2M1S4A2S1SeS14A2S2G1S4S2S10S1aS57S47A4U1A4S2SeS14S45S46Z1S48A2A4A4R3A2R1A2A3Ftp0;Ftp;Frho;").
Hypothesis XLATCHE2 : ltac2:(tb__ "0|2|
S13S3S27Q40A1A1M0G0S2eS0S28S0VJAFv;S32S49A2S6aR3R2A5VFAM;S3aS2S1S1S10S1aA2M1S4A2S1SeS14A2S2G1S4S2S10S1aS6aS49A4U1A4S2SeS14S45S46Z1S48A2A4A4R3A2R1A2A3Ftp0;Ftp;Frho;").

Lemma CHP_E : ltac2:(tb__ "0|1|
S3S1SeSeA2M0A1S3S1G0SeA2A1S6cS13S3S27Q40A1A1S6bZ5R3A2S2eS0S28S0S1cVAInv;VCST;VXGL;VKc;S31VCST;R6R5A3R6R5R4S1bS70S56S5S61A3AaS60R3R2A5S58S0S5fR3R2S71VAInv;VCST;VXGL;VKc;S31VCST;A1S1bS4dR6R5R4AaA5A3F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Proof.
  intros FBc FFc BXc rho1 tp1 HB. unfold PDk_p.
  eapply (sum_PostsC_k_ex segs AInv CST XGL Kc (P0_hp CST) PTrue HP.Pre_hp (ndh h0 true HP.nd0) (PDh HP.Posts_hp h0 true) NPH); [|exact HB].
  intros FBc' FFc' BXc' rho2 tp2 HB'.
  eapply (JA_frame_sum_ex segs AInv CST XGL ALA Kc (P0_hp CST) PTrue HP.Pre_hp HP.nd0 HP.Posts_hp NPH h0 true h0_ltH HamC_p HamPD_p (P0_hp_mono CST)); [|exact HB'].
  intros FBc'' FFc'' BXc'' rho3 tp3 HB''. exact (handle_p_sum_ex AInv CST XGL ALA HCST HXGL LFLAG LFSH Kc HKc FBc'' FFc'' BXc'' HB'' rho3 ACX tp3).
Qed.

Lemma CUTV_E : ltac2:(tb__ "0|5|
S10S1aS4S1SeS14A2M0S13S3S27Q40A1A1M1SeG1S35S1S1S1S10S1aA2M2S4A2M3G0A2S2G3G0S2G2S4S2S10S1aR8R7A4R6A4R5A4S65A3S3bS55R7R5A3S2bS36Z0S3aS2G3G0S2G2S4S2S10S1aRaR9A4R8A4R7A4R6A2M4A2S37G4R4A2A2S2eS0S28S0VJAv;RaA1RbR7R6A5VFAM;R5R4A2A3F_;F_;F_;Ftp0';Fb;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof.
  intros T nd k rv rho tp b tp0' Hin Hphi Hm.
  apply (etriple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisV k) nd T rho tp _ Hphi).
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (FAM_mono _ b tp0' w ltac:(apply Z.lt_le_incl; exact (proj2 Hm)) Hw) |].
  apply (cfg_complete_JAF_b segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc PhisV PhisV_reads 200%nat cps_arm NP cutsP exitsP (fun b w => FAM b tp0' w)
           (fun b b' w Hb Hw => FAM_mono b b' tp0' w Hb Hw) ecertP_ok); [|exact Hin].
  intros X ndX kX rvX rho1 tp1 HinX. cbn [exitsP In] in HinX. destruct HinX as [E|[E|[]]]; injection E as <- <- <- <-.
  - apply (etriple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisV 1)). intros HP1.
    eapply etriple_conseq; [| intros w Hw; right; exact Hw |].
    2: { pose proof ap_checks_exit as (_ & _ & _ & _ & _ & _ & _ & _ & _ & W460 & W467 & _).
         rewrite <- (efmeasA_VLA_sub X_latch Lok_p ndX0 nd_p_okX 1%nat 1%nat RL 1 s_latch_p rho1 W460 W467).
         exact (XLATCH (rho_sub rho1 s_latch_p) tp1 tp0'). }
    intros w Hw. destruct (Lok_p_latch rho1 tp1 w HP1 Hw) as [HP' Hw']. exact (SPA_JAF_intro segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tblB ndX0 X_latch _ tp1 w Hw' HP').
  - eapply etriple_conseq; [| intros w Hw; right; exact Hw | exact (XLATCHE2 rho1 tp1 tp0')].
    intros w Hw. unfold ndXE, ndL. apply (SPA_tv_permb_F segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tblB tv_p tvL frL [LAX 0; LAXK 0] (AHead pH true) X_latchE2 rho1 tp1 w (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 ap_checks_exit)))))))))))). exact Hw.
Qed.

Theorem arm_p_E : ltac2:(tb__ "0|2|
S13S3S27Q40A1A1M0G0S2eS0S28S0VJAFv;S32S44A2S4aR3R2A5VFAM;S3aS2S1S1S10S1aA2M1S4A2S1SeS14A2S2G1S4S2S10S1aS4aS44A4U1A4S2SeS14S45S46Z11S48A2A4A4R3A2R1A2A3Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0.
  exact (arm_p (etriple segs) FAM (TRe_facts segs) (TRe_ex segs) (TRe_pre segs) (TRe_pureP segs) (call_completePA3 segs)
           (fun Phi nd A rho tp Q H => etriple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue Phi nd A rho tp Q H)
           CHP_E CUTV_E rho tp tp0).
Qed.
End Existence.
End Sum.
End Lib_load_obj_ap_pf.

(* [comment removed for export] *)
Module Lib_load_obj_epiD3.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "positive"; "Z"; "N"; "@Corelib.Init.Datatypes"; "false"; "bool"; "nat"; "true"; "cons"; "list"; "nil"; "Some"; "prod"; "option"; "pair"; "app"; "negb"; "None"; "fst"; "length"; "orb"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "ss_objs"; "swf"; "ob_base"; "SVar"; "ss_pc"; "sv_eqb"; "DUnknown"; "cell"; "ob_lo"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "ax_X"; "axwf"; "la_reason"; "la_state"; "@LinuxProcessSemantics.Riscv.Instr"; "aluop"; "mulop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "axform"; "AXSelect"; "AXMerge"; "AXRebase"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs"; "Pre_f8"; "optL"; "L_f8"; "g5"; "objs_butlast"; "optR"; "xf_shback"; "xf_shcall"; "sel_last"; "vDp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "stop_reason"; "RsCut"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f9.Lib_load_obj_epiD3"; "Ee_s8"; "Pre_sf"; "Ee_s8a"; "Ee_sf"; "Te_s81"; "Ee_sfB"; "Ee_sfC"; "Re_s8"; "Te_s8"; "Te_s80"; "Te_s82"; "Te_s8r"; "dflt_obj"; "Ee_sf0"; "L_sf"; "Re_sf"; "Te_sf"; "s_s8"; "s_sf"; "sx_s8a"; "xf_merge"; "xf_rebase"; "xf_sh"; "Ee_sfA"; "Ee_sfD"; "X_sx"; "fr_off"; "frame_idx"; "insert_by"; "is_sh"; "needs_rebase"; "sh_idx"; "sx_T82"; "sx_T8r"; "@Corelib.Lists.ListDef"; "map"; "seq"; "nth"; "repeat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f7.Lib_load_obj_epiD2"; "nobj"; "cps_ad"; "E_s80"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "call_checkPA"; "@Stdlib.Lists.List"; "filter"; "existsb"; "fold_right"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_hv0"; "runL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro"; "ax_tidy"; "vBo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "T_afterA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS"; "shadow_release_stateA"; "shadow_reopen_stateA"; "shobj"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs.LOAddr"; "lo_ret"; "sf5_pc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop"; "alA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "T_afterA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "V_DEPTH"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "@Stdlib.ZArith.BinInt.Z"; "add"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG SymSummary SymObj SymFrame.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv ObjXform ObjUnbase TobjJV.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR TobjJAS TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAD.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require ObjEmptyA PinA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.TobjJAH OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.ObjZeroA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ObjEmptyA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.PinA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_defs Lib_load_obj_pro.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eo.Lib_load_obj_pro2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_disp OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_hv0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_exits OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_loopE OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_avn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builder_dispose.
Import ListNotations. Close Scope bv_scope. Open Scope Z_scope. Import ScanDoubleAddr LOAddr LOLAddr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import MemoFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_epiD1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f7.Lib_load_obj_epiD2.

Definition X_sx (E : axst) : list (sv * sv) := ltac2:(tb__ "0|2|
S67SbS15S15A2M0G0SfS13S1cS11S15S15R1A3M1S6cA2S1cG1S75A2A2A1Lr;S25VE;A1A3").
Definition sx_s8a (E : axst) : axst := ltac2:(tb__ "0|0|
S70VE;S55VE;A1S33Z44Ze7A5").
Definition sx_s8 (E : axst) : axst := ltac2:(tb__ "0|1|
S31S2bS4fVE;A1M0S37G0Z44A2A2A1").
Definition s_s8 (E8 : axst) : wsub := ltac2:(tb__ "0|0|
S7SbS0S15A2SdS0S15S77S39A4S6dPaS23VE8;A1S23S30A1A3A3").
Definition sx_T80 (E8 : axst) : axst := ltac2:(tb__ "0|1|
S6eS30VE8;S4dVE8;A1M0S35S65VE8;S30G0A3A1S32A5").
Definition sx_T81 (T0 : axst) : axst := ltac2:(tb__ "0|0|
S31S2bVT0;S36VT0;A1A2A1").
Definition sx_T82 (T1 : axst) : axst := ltac2:(tb__ "0|0|
S6fVT1;S34VT1;A1P6eS9SbS1S1A2A1A4").
Definition sx_T8r (T2 : axst) : axst := ltac2:(tb__ "0|0|
S70VT2;S25VT2;A1S33Z20Z40A5").
Definition sx_T8 (T2 : axst) : axst := ax_tidy (sx_T8r T2).

Definition is_sh (o : sobj) : bool := match ob_base o with SVar 140 => true | SAlu ALU_ADD (SVar 140) (SLit _) => true | _ => false end.
Definition dflt_obj : sobj := plain_obj (SLit 0) (SLit 0).
Definition sh_idx (A : axst) : list nat := ltac2:(tb__ "0|0|
S67S5S5S59S60S16R1S17S23VA;A1A1S48A4A1Li;S5fU0S62VA;A1A2A3").
Definition xf_sh (A : axst) : list axform := ltac2:(tb__ "0|3|
S8S5A1M0S8S2cA1M1Lx;S5bVA;A1S9S2cA1M2S5G0G0G1Ll;R1S7S2cS2dS38VA;R2A2A1G2A3S5G0G2Ll0;Ln;X8x2Ll;Li;X8x2").
Definition sx_sfA (E0 : axst) : axst := ltac2:(tb__ "0|0|
S31S2bVE0;S52VE0;A1A2A1").
Definition sx_sfB (EA : axst) : axst := ltac2:(tb__ "0|0|
S6fVEA;S34VEA;A1P6eS9SbS1S1A2A1A4").

Definition fr_off (o : sobj) : option Z := ltac2:(tb__ "0|1f|
S15ScS1A1M0Lx;M1S19Vo;A1S1S10S1A1M2Lz;M3S0S0G0Li;M4R1S0G2Lp;M5S0S0G0Lp;M6R1S0S0G0Lp0;M7R1S0S0G0Lp1;M8R1S0S0G0Lp2;M9R1S0G2Lp3;MaS0S0G0Lp3;MbR1S0S0G0Lp4;McR1S0G2Lp5;MdGdG1S1fVo;A1MeS1SaS1R1A2Llo;S0G2Li0;MfS29S15S15G2Lb;La;M10Lop;M11G11S2aG10Lop;M12G12S4S2S15G2La;Lw;Lsgn;M13S0S15S1G2Lk;M14Li0;Ll;M15X15x8X0x3Lp4;S0G2Lp4;M16G2X0x3Lp3;G2X0x3Lp2;S0G2Lp2;M17G2X0x3Lp1;S0G2Lp1;M18G2X0x3Lp0;S0G2Lp0;M19G2X0x3Lp;G2X0x3Li;S29S15S15S29G0Lop;R3S15G0La;R2G3S0G4R1G5S0G6R1S0G7R1S0G8R1S0G9R1GaS0GbR1S0GcR1GdGdS15G0Lb;R8S1G1GeS1SaS1S79R2R1A2A2Llo;GfS29S15S15G2Lb0;La0;M1aLop0;M1bG1bS2aG1aLop0;M1cG1cS4S2S15G2La0;Lw;Lsgn;M1dG15X15x8Lc;GfG1bG1bG1cG1cG1dG15X15x8X0x3Lp4;G16G2X0x3Lp3;G2X0x3Lp2;G17G2X0x3Lp1;G18G2X0x3Lp0;G19G2X0x3Lp;G2X0x3Li;G1bG1bG1cG1cG1dS0S15G14Li;Ll;M1eX15x8G2G2G2G2G2G2G2G2G2X29xaLb;La;Lop;G11G12G12G13G1eX15x8").
Definition needs_rebase (o : sobj) : bool := match ob_base o with SAlu ALU_ADD (SVar 110) (SLit _) => true | _ => false end.
Definition xf_rebase (A : axst) : list axform := ltac2:(tb__ "0|0|
S5eS5S2cS5S2fR1A1Li;S67S5S5S5aS60S16R1S17S23VA;A1A1S48A4A1Li;S5fU0S62VA;A1A2A3A4").
Fixpoint insert_by (k : Z) (i : nat) (l : list (Z * nat)) : list (Z * nat) :=
  match l with [] => [(k, i)] | (k', j) :: r => if k <=? k' then (k, i) :: l else (k', j) :: insert_by k i r end.
Definition frame_idx (A : axst) : list nat := ltac2:(tb__ "0|2|
S5eSbS1S5A2M0S5S14S1S5A2S69S8G0A1M1S5S5G1ScS1A1G1Lx;S56S60S16R2S17S23VA;A1A1S48A4A1S1S58R1R3R2A3Lk;R1Xcx2Lacc;Li;S9G0A1S5fU0S62VA;A1A2A5A4").
Definition xf_merge (A : axst) : list axform := ltac2:(tb__ "0|1|
S57VA;A1S8S5A1S7S2cS2dSeS5R1S67S5S5SfS68S5S78R1A1R2A3A1Li;S5fU0M0S62VA;A1A2A3A3A1S61S2cS2eG0A1S72S12S5R1A2U2A2A3A3Tfi;").
Definition sx_sfC (EB : axst) : axst := ltac2:(tb__ "0|0|
S31S2bVEB;S51VEB;A1A2A1").
Definition sx_sfD (EC : axst) : axst := ltac2:(tb__ "0|0|
S31S2bVEC;S50VEC;A1A2A1").
Definition sx_sf (ED : axst) : axst := flag_carve_stateA ED 120.
Definition Pre_sf : axst := Pre_stack_free AE_A 5.
Definition L_sf : axst := L_stack_free AE_A 5.
Definition s_sf (E : axst) : wsub := ltac2:(tb__ "0|1|
S7SbS0S15A2M0SdS0S15P10S1aP78A1A4S7G0SdS0S15PfS1aP13A1A4S6dPaS23VE;A1S23S3dA1A3A3A3").
Definition sx_Tsf (E : axst) : axst := ltac2:(tb__ "0|1|
S6bS76S3dVE;S4eVE;A1M0S35S65VE;S3dG0A3A1S4aS25VE;A1A6A1").

Definition Ee_s8a : axst := Eval vm_compute in sx_s8a E_s80.
Definition Ee_s8 : axst := Eval vm_compute in sx_s8 E_s80.
Definition Re_s8 : list sobj := Eval vm_compute in optR (entails_frA Ee_s8 Pre_f8 (s_s8 Ee_s8)).
Definition Te_s80 : axst := Eval vm_compute in sx_T80 Ee_s8.
Definition Te_s81 : axst := Eval vm_compute in sx_T81 Te_s80.
Definition Te_s82 : axst := Eval vm_compute in sx_T82 Te_s81.
Definition Te_s8r : axst := Eval vm_compute in sx_T8r Te_s82.
Definition Te_s8 : axst := Eval vm_compute in ax_tidy Te_s8r.
Definition Ee_sf0 : axst := Eval vm_compute in leafL (runL 300 cps_ad Te_s8) sf5_pc 0.
Definition Ee_sfA : axst := Eval vm_compute in sx_sfA Ee_sf0.
Definition Ee_sfB : axst := Eval vm_compute in sx_sfB Ee_sfA.
Definition Ee_sfC : axst := Eval vm_compute in sx_sfC Ee_sfB.
Definition Ee_sfD : axst := Eval vm_compute in sx_sfD Ee_sfC.
Definition Ee_sf : axst := Eval vm_compute in sx_sf Ee_sfD.
Definition Re_sf : list sobj := Eval vm_compute in optR (entails_frA Ee_sf Pre_sf (s_sf Ee_sf)).
Definition Te_sf : axst := Eval vm_compute in sx_Tsf Ee_sf.
Definition P_errL : axst := Eval vm_compute in leafL (runL 300 cps_ad Te_sf) lo_ret 0.

Lemma epiD3_checks_s8 : ltac2:(tb__ "0|5|
S21S20S4S18S23S3eA1A1S6A3S21S20S22S4fS64A1S3eA3S21S20ScS22A1M0S2bS3eS37S3eZ44M1A2A2SaS22S3cA2A3S21S20ScS8S16A1M2A1S65S3cS30S4dS3cA1M3A3SaG2S43A2A3S21S20S4S66S3cS30G3S43S7S22S32S9S22A1A3A5S6A3S21S20S22S6eS30S3cG3S43S32A5S45A3S21S20G0S2bS45S36S45A1A2SaS22S40A2A3S21S20G2S17S23S40A1A1SeS16S34S40A1S7S16S71S33G1Ze7S9S1eA1S1dA5S9S16A1A3A3A3S21S20S22S5cS40A1S46A3S21S20S4S18S23S46A1A1S6A3S21S20S22S5dS46A1S47A3S21S20S4S18S23S47A1A1S6A3S21S20S22S6bS47A1S44A3S21S20S4S26S44A1S6A3S20S8SbS1S3aA2M4A1S5eS24G4S24SdS1S3aS1bS23S28R1A1A1A1S27R1A1A4LL;S6aU12cS63S44A3A4S7G4SdS1S3aS74S3bA4S9G4A1A3A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.

Lemma epiD3_checks_sf : ltac2:(tb__ "0|4|
S21S20ScS22A1M0S2bS49S52S49A1A2SaS22S53A2A3S21S20S4S18S23S41A1A1S6A3S21S20G0S2bS41S51S41A1A2SaS22S42A2A3S21S20G0S2bS42S50S42A1A2SaS22S54A2A3S21S20S4S26S3fA1S6A3S21S20ScS8S16A1M1A1S65S3fS3dS4eS3fA1M2A3SaG1S4bA2A3S21S20S4S66S3fS3dG2S4bS7S22S4aS9S22A1A3A5S6A3S21S20S4S26S4cA1S6A3S20S8SbS1S3aA2M3A1S5eS24G3S24SdS1S3aS1bS23S28R1A1A1A1S27R1A1A4LL;S6aU12cS63S4cA3A4S7G3SdS1S3aS73S3bA4S9G3A1A3A3A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.
End Lib_load_obj_epiD3.

(* [comment removed for export] *)
Module Lib_load_obj_af_eqs.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "true"; "bool"; "prod"; "nil"; "nat"; "app"; "list"; "@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SVar"; "sprop"; "SPUle"; "ss_facts"; "ss_next"; "SAlu"; "SLit"; "sprop_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bitem"; "batom"; "ASv"; "AMin"; "BI"; "bd_subst"; "bd_wpos"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f9.Lib_load_obj_af_eqs"; "s_latch_f"; "xE1"; "Lok_f"; "nd_f_okX"; "T_f_okR"; "Ys_f"; "bdX_f"; "Xf_f"; "Xs_f"; "Yf_f"; "bd_f_fX"; "comm_f"; "commf_f"; "finKf"; "finVf"; "nd_f_fX"; "qCfvf"; "qCmif"; "qCmmf"; "qCsgf"; "cutsQ"; "exitsQ"; "extra_f"; "ndXE_f"; "rates_f"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue"; "frL"; "V_B"; "extraLO"; "tvL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "AHead"; "NDA"; "nd_below"; "am_eqb"; "am_subst"; "fr_sub_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs"; "NP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop"; "pH"; "X_latch"; "pLNL"; "pPOS"; "xLD"; "xLK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_af"; "tv_f"; "gFV'"; "gMI'"; "gMM'"; "gSG'"; "kept_f"; "tv_f_ok"; "LAr_f"; "T_f_f"; "T_f_ok"; "gCO'"; "gRP'"; "gTR'"; "gTS'"; "tv_f_f"; "E_f"; "R_f"; "Xk_f"; "bd_f_f"; "bd_f_ok"; "qAf"; "qCURf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG"; "bd_permb"; "tv_permb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs"; "kb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud"; "LAX"; "LAXK"; "AK1"; "LAK"; "RL"; "VLA"; "bdX"; "z0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub_id_below"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit2"; "lines_chk"; "robj_ent"; "robjs_chkC"; "xextraLO"; "xrs_chkC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_avn"; "PhisV"; "cps_arm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_loopE"; "X_latchE2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "tv_sub_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF"; "bud_le2"; "bud_pay2"; "ejcertAF"; "wsub_id_on"; "@Stdlib.Lists.List"; "In"; "forallb"; "@Stdlib.PArith.BinPos.Pos"; "leb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CFGA GlueA SummaryA SummaryA2 MemoFast.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_defs Lib_handle_f_s2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require en.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_defs Lib_load_obj_pro.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eo.Lib_load_obj_pro2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_disp OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_hv0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_exits OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_loopE OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_avn OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_af.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr LOAddr LOLAddr HVAddr.

Definition xE1 : sv := SAlu ALU_ADD pE0 (SLit 1).
Definition qCmif : sv := Eval vm_compute in sv_subst isub_ok_f HF2.qCmi.
Definition qCfvf : sv := Eval vm_compute in sv_subst isub_ok_f HF2.qCfv.
Definition qCmmf : sv := Eval vm_compute in sv_subst isub_ok_f HF2.qCmm.
Definition qCsgf : sv := Eval vm_compute in sv_subst isub_ok_f HF2.qCsg.
Definition rates_f : list sprop := ltac2:(tb__ "0|1|
S0SfS10S4dS63Z3S1eA2M0A2S0SfS10S4cS1eA2S0SfS10S4eS1eA2S0SfS10S4fS1eA2S0SfS10S55S1eA2S0SfS10S56G0A2S0SfS10S57G0A2S0SfS10S58S63Z25S1eA2A2S0SfS10S2eS4dA2S0SfS10S2dS4cA2S0SfS10S2fS4eA2S0SfS10S30S4fA2S5SfA1A3A3A3A3A3A3A3A3A3A3A3A3").
Definition T_f_okR : axst := Eval vm_compute in ax_add_facts rates_f T_f_ok.
Lemma af_checks_rt : ltac2:(tb__ "0|2|
SaS9S3bS79S54S7SfS35S11S3aS54A1M0A1A3M1A2S21A3SaS9S3S80SfS15S12G0A1A1G1A3S2A3SaS9SdS60SeP302A1A3SaS9SdS5fSeP310A1A3SaS9SdS2eSeP304A1A3SaS9SdS2dSeP307A1A3SaS9SdS2fSeP30aA1A3S9SdS30SeP30dA1A3A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.

Definition Lok_f : axst := Eval vm_compute in leafL (runL 200 cps_arm T_f_okR) pc_latch 0.
Definition s_latch_f : wsub := ltac2:(tb__ "0|1|
S0S4ScSdA2M0S1ScSdP244S4dA4S0G0S1ScSdP245S4cA4S0G0S1ScSdP246S4eA4S0G0S1ScSdP247S4fA4S0G0S1ScSdP24bS55A4S0G0S1ScSdP24cS56A4S0G0S1ScSdP24dS57A4S0G0S1ScSdP24eS58A4S78S44S3aS1fA1S3aS46A1A3A3A3A3A3A3A3A3A3").
Definition bdX_f : list bitem := Eval vm_compute in bd_subst s_latch_f (bdX 0).
Definition nd_f_okX : ndesc := ltac2:(tb__ "0|0|
S3fS51S36S23S3eS45S2A2A4").
Definition ndX_f : ndesc := ltac2:(tb__ "0|0|
S3fS4bS36S6aZ0A1S3eS45S2A2A4").
Definition comm_f : list bitem := Eval vm_compute in bd_common bd_f_ok bdX_f.
Definition Xs_f : list bitem := Eval vm_compute in bd_minus bd_f_ok bdX_f.
Definition Ys_f : list bitem := Eval vm_compute in bd_minus bdX_f bd_f_ok.

Definition finVf (c1 c2 c3 c4 : sv) : bitem := ltac2:(tb__ "0|6|
S1aZ1M0Z0M1S0S4SbS17A2M2S1SbS17Z18S18Vc1;A1A4S0G2S1SbS17Z60M3S19Vc1;G0G1G0A4A4S0G2S1SbS17Z8M4S18Vc2;A1A4S0G2S1SbS17G3S19Vc2;G0G1G0A4A4S0G2S1SbS17G4S18Vc3;A1A4S0G2S1SbS17G3S19Vc3;G0G1G0A4A4S0G2S1SbS17G4S18Vc4;A1A4S0G2S1SbS17G3S19Vc4;G0G1G0A4A4S0G2S1SbS17Z78M5S18SeP1b2A1A1A4S0G2S1SbS17Z68S18SeP1b5A1A1A4S0G2S1SbS17G5S18SeP1b8A1A1A4S5G2A1A3A3A3A3A3A3A3A3A3A3A3G1A4").
Definition finKf (c1 c2 c3 c4 : sv) : bitem := ltac2:(tb__ "0|4|
S1aZ0M0Z1S0S4SbS17A2M1S1SbS17Z70M2S18Vc1;A1A4S0G1S1SbS17Z50M3S18Vc2;A1A4S0G1S1SbS17G3S18Vc3;A1A4S0G1S1SbS17G3S18Vc4;A1A4S0G1S1SbS17G2S18SeP1b2A1A1A4S0G1S1SbS17G3S18SeP1b5A1A1A4S0G1S1SbS17G2S18SeP1b8A1A1A4S5G1A1A3A3A3A3A3A3A3G0A4").
Lemma af_checks_pay : ltac2:(tb__ "0|c|
SaS9S3S61S5eS7S16S28S25A3A2S2A3SaS9S3S61S7S16S28S22A3S23A2S2A3SaS9S3S1cS22A1S2A3SaS9S8S16A1M0S25S0S16S1aZ300Z0M1S0S4SbS17A2M2S1SbS17Z1S18S13S6eS47S48A3A1A4S0G2S1SbS17N1S18SeP302A1A1A4S5G2A1A3A3G1A4S0S16S52S0S16S67S66A1S0S16S2bSeP1a6A1M3SeP1a9A1M4SeP1acA1M5SeP1afA1M6A4S0S16S2aG3G4G5G6A4S5S16A1M7A3A3A3A3A3A3SaS9G0S22S0S16S64G1A1S0S16S65G1A1S0S16S2bSeP304A1M8SeP307A1M9SeP30aA1MaSeP30dA1MbA4S0S16S2aG8G9GaGbA4G7A3A3A3A3A3S9S3S40S12S3aS21A1A1S20A2S2A3A2A2A2A2A2").
Proof. conj_vmc. Qed.

Lemma af_checks_exit : ltac2:(tb__ "0|5|
SaS9S3S3cS1fS46S1dA3S2A3SaS9S3S6dS1dS44A2S2A3SaS9S3S81S44S12S3aS1fA1M0A1M1A2S2A3SaS9S3S40G1S20A2S2A3SaS9S3S7aS1dS51S4bA3S2A3SaS9S3S43S1dS36S36A3S2A3SaS9S3S7bS11G0A1S1bS1dS6aZ0A1A2S23A3S2A3SaS9S3S41S42S1dS3eS45S2A2M2A2G2A2S2A3SaS9S3S7eS37S1dA2S2A3SaS9SdS6cS1dP1ccM3A2SeG3A1A3SaS9SdS6cS1dP1d3M4A2SeG4A1A3S9S3S62S4bS39A2S2A3A2A2A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.

Definition Xf_f : list bitem := ltac2:(tb__ "0|0|
S0S16S52S0S16S67S66A1S5S16A1A3A3").
Definition Yf_f : list bitem := ltac2:(tb__ "0|1|
S0S16S64Z0M0A1S0S16S65G0A1S5S16A1A3A3").
Definition commf_f : list bitem := Eval vm_compute in bd_minus bd_f_f Xf_f.
Definition bd_f_fX : list bitem := Yf_f ++ commf_f.
Definition nd_f_fX : ndesc := ltac2:(tb__ "0|0|
S3fS59S36S27S3eS45S2A2A4").
Definition ndXE_f : ndesc := ltac2:(tb__ "0|1|
S3fS4bS36S0S16S64Z0M0A1S0S16S65G0A1S5S16A1A3A3S3eS45S2A2A4").
Lemma af_checks_payf : ltac2:(tb__ "0|2|
SaS9S3S61S5dS7S16S29S24A3A2S2A3SaS9S3S61S7S16S29S26A3S27A2S2A3SaS9S3S7cS11S3aS53A1M0A1S14Z0M1A1G1S24S26A5S2A3SaS9S3S40S12G0A1S2cA2S2A3S9S8S4SdSdA2A1S59S51A3A2A2A2A2").
Proof. conj_vmc. Qed.

Definition cutsQ : list efnode := ltac2:(tb__ "0|6|
S0S4S4S4S3bS3dA2M0S6A2M1S4SbSdA2M2A2M3S1G1G2S1G0S6S1S3bS3dS21S20A4U1M4A4S1SbSdS68S69ZaS6bA2A4M5A4S0G3S1G1G2S1G0S6S1S3bS3dS53S2cA4G4A4G5A4S5G3A1A3A3").
Definition exitsQ : list efnode := ltac2:(tb__ "0|6|
S0S4S4S4S3bS3dA2M0S6A2M1S4SbSdA2M2A2M3S1G1G2S1G0S6S1S3bS3dS1fS20A4U1M4A4S1SbSdS68S69Z1S6bA2A4M5A4S0G3S1G1G2S1G0S6S1S3bS3dS77S34A4G4A4G5A4S5G3A1A3A3").
Lemma ecertQ_ok : ltac2:(tb__ "0|0|
S9S3S7dS6fS44S75Uc8S76S44S31S32A8S2A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Definition extra_f (o : sobj) : bool := ltac2:(tb__ "0|0|
S3S3L_;S38Vo;A1S2S71Vo;A1X3x2").
Lemma af_checks2 : ltac2:(tb__ "0|1|
SaS9S3S72S11S3aS5aA1A1M0S50S36S33S5bA5S2A3SaS9S3S74G0S50S36S73S5cA5S2A3S9S3S70G0A1S2A3A2A2").
Proof. conj_vmc. Qed.
Lemma lines_in_kept_f : ltac2:(tb__ "0|0|
S7fS4SdSdA2S1SdSdS49S63Z10S4aA2A4S50A3").
Proof. cbn. do 9 right. left. reflexivity. Qed.
End Lib_load_obj_af_eqs.

(* [comment removed for export] *)
Module Lib_load_obj_af_pf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@Corelib.Init.Datatypes"; "prod"; "pair"; "list"; "nat"; "true"; "cons"; "bool"; "fst"; "app"; "nil"; "Some"; "option"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sv"; "sprop"; "holds"; "ss_facts"; "ss_next"; "SLit"; "sobj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "smatchA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "PTrue"; "JA_pre"; "JA"; "TPA"; "fbinA"; "ffinA"; "frinA"; "ok_frameKA"; "tvinA"; "@Corelib.Init.Logic"; "and"; "eq"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue"; "tblB"; "frL"; "P0_lo"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_af.HFI"; "P0_hf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF"; "efmeasA"; "phiK"; "JAF"; "phi_reads"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_sub"; "rho_absorb"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud"; "ndA1"; "RL"; "VLA"; "ndX0"; "z0"; "ndXE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_disp"; "E_hf"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_af"; "kept_f"; "PDk_f"; "E_f"; "R_f"; "T_f_ok"; "payX_f"; "E_f1"; "Xk_f"; "passed_f"; "payY_f"; "room_f"; "s_f"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_avn"; "PhisV"; "h0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop"; "X_latch"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "J_ofPA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bd_nn"; "BXok_d"; "bitem"; "bxt"; "bd_wpos"; "bsumK"; "bsumV"; "pay_sem"; "AMin"; "aval"; "pay_okF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "AE_A"; "alloc_contractsA"; "alloc_contractsA_ex"; "alloc_lawsA"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs"; "NPH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_af.HF"; "Pre_hf"; "nd0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f9.Lib_load_obj_af_eqs"; "Xs_f"; "Ys_f"; "cutsQ"; "Lok_f"; "nd_f_okX"; "rates_f"; "s_latch_f"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs"; "NP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_loopE"; "X_latchE2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.TobjJAH"; "ndh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK"; "PostsCk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary";
"agree_vals"; "call_linkP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG"; "bd_permb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "ccount"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_geom"; "topG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Asan_set_shadow_iface"; "set_shadow_contractA"; "set_shadow_contractA_ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_fuzz_iface"; "in_lits"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "FBx"; "T_ok"; "tvd"; "tvz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3"; "import_okPA3"; "import_postA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "FFx"; "robjs_okF"; "xrs_okF"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Asan_set_shadow_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_defs Lib_handle_f_s2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require en.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_defs Lib_load_obj_pro.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eo.Lib_load_obj_pro2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_disp OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_hv0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_exits OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_loopE OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_avn OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_af OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f9.Lib_load_obj_af_eqs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr LOAddr LOLAddr HVAddr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma PhisV_reads : ltac2:(tb__ "0|3|
S2dS3S5S1A1M0S10OF_;M1A2M2G2S3bSaG0G1R1A3SfG0G1R1A3A2Lp;S56A3").
Proof. constructor; [exact tblL_reads | constructor; [exact tblB_reads | constructor]]. Qed.
Lemma h0_ltH : (h0 < NPH)%positive. Proof. reflexivity. Qed.

Lemma pay_okF_split_semF : ltac2:(tb__ "0|1|
S10OF_;S5S12A1S11S0S5S60A1M0G0G0G0G0S2aS9S80R5SbS60R3R2A3A2S7A3S2aS9S80SbS60R4R2A3R5A2S7A3S2aS9S62R5A1S7A3S2aS9S62R4A1S7A3S2bZ0RaA2S10S2dS12S13R1A1ReA3S5eR9R2A2S65R3RfReRaR9A5F_;F_;Frho;S68RfReRdRcRbRaA6F_;F_;F_;F_;F_;F_;FY;FX;Fcommon;Fbto;Fbfrom;FcostK;FcostV;Ffacts;Fpre;").
Proof.
  intros pre facts costV costK bfrom bto common X Y HP1 HP2 Hwc Hwy Hk Hsem.
  pose proof (bd_permb_sound _ _ HP1) as P1. pose proof (bd_permb_sound _ _ HP2) as P2.
  split; [|split; [exact Hk|]].
  - unfold bd_wpos in *. apply forallb_forall. intros it Hit.
    assert (Hin : In it (common ++ Y)) by (eapply Permutation_in; [apply Permutation_sym; exact P2 | exact Hit]).
    apply in_app_or in Hin as [Hin|Hin]; [exact (proj1 (forallb_forall _ _) Hwc it Hin) | exact (proj1 (forallb_forall _ _) Hwy it Hin)].
  - intros rho HF Hpre Hwf Hnf.
    assert (Hn2 : bd_nn (common ++ X) rho).
    { unfold bd_nn in *. apply Forall_forall. intros it Hit. apply (proj1 (Forall_forall _ _) Hnf). eapply Permutation_in; [apply Permutation_sym; exact P1 | exact Hit]. }
    unfold bd_nn in Hn2. apply Forall_app in Hn2 as [Hnc Hnx].
    destruct (Hsem rho HF Hnx) as (Q1 & Q2 & Q6).
    unfold pay_sem. rewrite (bsumV_perm bfrom (common ++ X) rho P1), (bsumK_perm bfrom (common ++ X) rho P1).
    rewrite <- (bsumV_perm (common ++ Y) bto rho P2), <- (bsumK_perm (common ++ Y) bto rho P2).
    rewrite !bsumV_app, !bsumK_app. split; [lia|]. split; [lia|].
    unfold bd_nn. apply Forall_forall. intros it Hit.
    assert (Hin : In it (common ++ Y)) by (eapply Permutation_in; [apply Permutation_sym; exact P2 | exact Hit]).
    apply in_app_or in Hin as [Hin|Hin]; [exact (proj1 (Forall_forall _ _) Hnc it Hin) | exact (proj1 (Forall_forall _ _) Q6 it Hin)].
Qed.

Lemma room_f_holds : ltac2:(tb__ "0|0|
S10S2dS12S13R1A1S14S19S50A1A1A3S2dS12S13R2A1S54A3F_;Fr;").
Proof.
  intros r HF.
  fact HF (SPUle (SVar 480) (SVar 476)) F1. fact HF (SPUle (SAlu ALU_ADD (SVar 480) (SVar 481)) (SVar 14)) F2. fact HF (SPUle (SVar 14) (SLit 67108864)) F3.
  fact HF (SPUle (SVar 490) (SVar 480)) F4. fact HF (SPUle (SVar 580) (SMd M_MUL (SLit 3) (SVar 490))) F5. fact HF (SPUle (SVar 590) (SMd M_MUL (SLit 37) (SVar 490))) F6.
  fact HF (SPUle (SVar 422) (SVar 580)) F7. fact HF (SPUle (SVar 480) (SLit 67108864)) F8. fact HF (SPUle (SVar 481) (SLit 67108864)) F9.
  fact HF (SPUle (SVar 476) (SAlu ALU_ADD (SVar 480) (SVar 481))) F10.
  rewrite h_ule in F1, F2, F3, F4, F5, F6, F7, F8, F9, F10. rewrite uval_lit in F3, F8, F9 by lia.
  pose proof (uval_range r (SVar 480)) as R480. pose proof (uval_range r (SVar 481)) as R481. pose proof (uval_range r (SVar 476)) as R476. pose proof (uval_range r (SVar 490)) as R490.
  pose proof (uval_range r (SVar 580)) as R580. pose proof (uval_range r (SVar 590)) as R590. pose proof (uval_range r (SVar 422)) as R422.
  assert (E1 : uval r (SAlu ALU_ADD (SVar 480) (SVar 481)) = uval r (SVar 480) + uval r (SVar 481)) by (apply uval_add_small; lia). rewrite E1 in F2, F10.
  assert (E2 : uval r (SAlu ALU_ADD (SVar 481) (SVar 480)) = uval r (SVar 481) + uval r (SVar 480)) by (apply uval_add_small; lia).
  assert (M3 : uval r (SMd M_MUL (SLit 3) (SVar 490)) = 3 * uval r (SVar 490)) by (apply uval_mul_lit; lia). rewrite M3 in F5.
  assert (M37 : uval r (SMd M_MUL (SLit 37) (SVar 490)) = 37 * uval r (SVar 490)) by (apply uval_mul_lit; lia). rewrite M37 in F6.
  assert (K1 : forall k e, 0 <= k <= 64 -> uval r e <= 2 ^ 32 -> uval r (SMd M_MUL (SLit k) e) = k * uval r e) by (intros k e Hk He; pose proof (uval_range r e); apply uval_mul_lit; [lia | nia]).
  unfold room_f.
  constructor; [apply (proj2 (h_ule _ _ _))|constructor; [apply (proj2 (h_ule _ _ _))|constructor; [apply (proj2 (h_ule _ _ _))|constructor]]].
  - rewrite uval_add_small; rewrite !K1, ?E2 by lia; [|lia]. rewrite uval_add_small; rewrite ?K1, ?uval_lit by lia; lia.
  - rewrite uval_add_small; rewrite !K1, ?E2 by lia; [|lia]. rewrite uval_add_small; rewrite ?K1, ?uval_lit by lia; lia.
  - rewrite uval_add_small; rewrite !K1, ?E2 by lia; [|lia]. rewrite uval_add_small; rewrite ?K1, ?uval_lit by lia; lia.
Qed.

Lemma pay_site_f : ltac2:(tb__ "0|1|
S10S2dS12S13R1A1S14S19S4cA1A1A3S5eS4fR2A2S65R3S16Z0M0A1G0S4fS53A5F_;F_;Fr;").
Proof.
  intros r HF _.
  fact HF (SPUle (SVar 480) (SVar 476)) F1. fact HF (SPUle (SAlu ALU_ADD (SVar 480) (SVar 481)) (SVar 14)) F2. fact HF (SPUle (SVar 14) (SLit 67108864)) F3.
  fact HF (SPUle (SVar 490) (SVar 480)) F4. fact HF (SPUle (SVar 476) (SAlu ALU_ADD (SVar 480) (SVar 481))) F10.
  fact HF (SPUle (SVar 480) (SLit 67108864)) F8. fact HF (SPUle (SVar 481) (SLit 67108864)) F9.
  rewrite h_ule in F1, F2, F3, F4, F8, F9, F10. rewrite uval_lit in F3, F8, F9 by lia.
  pose proof (uval_range r (SVar 480)) as R480. pose proof (uval_range r (SVar 481)) as R481. pose proof (uval_range r (SVar 476)) as R476. pose proof (uval_range r (SVar 490)) as R490.
  pose proof (uval_range r (SVar 14)) as R14.
  assert (E1 : uval r (SAlu ALU_ADD (SVar 480) (SVar 481)) = uval r (SVar 480) + uval r (SVar 481)) by (apply uval_add_small; lia). rewrite E1 in F2, F10.
  assert (E2 : uval r (SAlu ALU_ADD (SVar 481) (SVar 480)) = uval r (SVar 481) + uval r (SVar 480)) by (apply uval_add_small; lia).
  unfold pay_sem. rewrite uval_lit by lia.
  assert (EY : payY_f = [LAr_f; BI 768 0 [(1, ASv (SAlu ALU_ADD (SVar 481) (SVar 480))); (-1, ASv (SVar 476))] 0]) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
  rewrite EY. unfold payX_f, LAr_f, LA, A1, HF.cVF, pLNL, pNX, vLEN.
  cbv beta iota delta [bsumV bsumK bival lfval aval bi_v bi_k bi_f bi_c]. rewrite E2.
  split; [lia|]. split; [lia|].
  unfold bd_nn. repeat constructor; cbv beta iota delta [bival lfval aval bi_v bi_k bi_f bi_c]; rewrite ?E2; lia.
Qed.

Lemma amin1_rng : ltac2:(tb__ "0|3|
S10S11S29S2bZ0M0S67R2S66R1Z1M1G0G1A4A2M2A2S2bG2G1A2A2Fe;Fr;").
Proof. intros r e. cbn [aval]. lia. Qed.

Lemma pay_f : ltac2:(tb__ "0|0|
S10S2dS12S13R1A1S14S19S4eA1A1A3S5eS72R2A2S29S2bS64S73R3A2S64S72R3A2A2S29S2bS63S73R3A2S63S72R3A2A2S5eS73R3A2A2A2F_;F_;Fr;").
Proof.
  intros r HF _. pose proof af_checks_pay as (_ & _ & _ & EX & EY & _). rewrite EX, EY.
  fact HF (SPUle (SVar 480) (SLit 67108864)) F1. fact HF (SPUle (SAlu ALU_ADD (SVar 480) (SVar 481)) (SVar 14)) F2.
  fact HF (SPUle (SVar 14) (SLit 67108864)) F3. fact HF (SPUle (SVar 490) (SVar 480)) F4. fact HF (SPUle (SVar 480) (SVar 476)) F5.
  fact HF (SPUle (SVar 770) (SAlu ALU_ADD (SVar 481) (SVar 480))) F6. fact HF (SPUle (SVar 481) (SLit 67108864)) F9.
  fact HF (SPUle (SAlu ALU_ADD (SVar 784) (SVar 476)) (SVar 770)) PA1. fact HF (SPUle (SVar 476) (SVar 770)) F8.
  fact HF (SPUle (SVar 784) (SVar 785)) B1. fact HF (SPUle (SVar 785) (SLit 4294967295)) B2.
  fact HF (SPUle (SVar 772) (SAlu ALU_ADD (SVar 422) (SMd M_MUL (SLit 3) (SVar 784)))) C1. fact HF (SPUle (SVar 775) (SAlu ALU_ADD (SVar 425) (SVar 784))) C2.
  fact HF (SPUle (SVar 778) (SAlu ALU_ADD (SVar 428) (SVar 784))) C3. fact HF (SPUle (SVar 781) (SAlu ALU_ADD (SVar 431) (SVar 784))) C4.
  fact HF (SPUle (SVar 422) (SVar 580)) G1. fact HF (SPUle (SVar 425) (SVar 581)) G2. fact HF (SPUle (SVar 428) (SVar 582)) G3. fact HF (SPUle (SVar 431) (SVar 583)) G4.
  fact HF (SPUle (SVar 580) (SMd M_MUL (SLit 3) (SVar 490))) R1. fact HF (SPUle (SVar 581) (SVar 490)) R2. fact HF (SPUle (SVar 582) (SVar 490)) R3. fact HF (SPUle (SVar 583) (SVar 490)) R4.
  rewrite h_ule in F1, F2, F3, F4, F5, F6, F8, F9, PA1, B1, B2, C1, C2, C3, C4, G1, G2, G3, G4, R1, R2, R3, R4. rewrite uval_lit in F1, F3, F9, B2 by lia.
  pose proof (uval_range r (SVar 785)) as R785.
  pose proof (uval_range r (SVar 481)) as R481. pose proof (uval_range r (SVar 480)) as R480. pose proof (uval_range r (SVar 770)) as R770. pose proof (uval_range r (SVar 784)) as R784.
  pose proof (uval_range r (SVar 476)) as R476. pose proof (uval_range r (SVar 490)) as R490. pose proof (uval_range r (SVar 14)) as R14.
  pose proof (uval_range r (SVar 422)) as R422. pose proof (uval_range r (SVar 425)) as R425. pose proof (uval_range r (SVar 428)) as R428. pose proof (uval_range r (SVar 431)) as R431.
  pose proof (uval_range r (SVar 772)) as R772. pose proof (uval_range r (SVar 775)) as R775. pose proof (uval_range r (SVar 778)) as R778. pose proof (uval_range r (SVar 781)) as R781.
  pose proof (uval_range r (SVar 434)) as R434. pose proof (uval_range r (SVar 437)) as R437. pose proof (uval_range r (SVar 440)) as R440.
  pose proof (uval_range r (SVar 580)) as R580. pose proof (uval_range r (SVar 581)) as R581. pose proof (uval_range r (SVar 582)) as R582. pose proof (uval_range r (SVar 583)) as R583.
  assert (E1 : uval r (SAlu ALU_ADD (SVar 480) (SVar 481)) = uval r (SVar 480) + uval r (SVar 481)) by (apply uval_add_small; lia). rewrite E1 in F2.
  assert (E2 : uval r (SAlu ALU_ADD (SVar 481) (SVar 480)) = uval r (SVar 481) + uval r (SVar 480)) by (apply uval_add_small; lia). rewrite E2 in F6.
  assert (E3 : uval r (SAlu ALU_ADD (SVar 784) (SVar 476)) = uval r (SVar 784) + uval r (SVar 476)) by (apply uval_add_small; lia). rewrite E3 in PA1.
  assert (M3 : uval r (SMd M_MUL (SLit 3) (SVar 490)) = 3 * uval r (SVar 490)) by (apply uval_mul_lit; lia). rewrite M3 in R1.
  assert (M3a : uval r (SMd M_MUL (SLit 3) (SVar 784)) = 3 * uval r (SVar 784)) by (apply uval_mul_lit; lia).
  assert (E4 : uval r (SAlu ALU_ADD (SVar 422) (SMd M_MUL (SLit 3) (SVar 784))) = uval r (SVar 422) + 3 * uval r (SVar 784)) by (rewrite uval_add_small; rewrite M3a; lia). rewrite E4 in C1.
  assert (E5 : uval r (SAlu ALU_ADD (SVar 425) (SVar 784)) = uval r (SVar 425) + uval r (SVar 784)) by (apply uval_add_small; lia). rewrite E5 in C2.
  assert (E6 : uval r (SAlu ALU_ADD (SVar 428) (SVar 784)) = uval r (SVar 428) + uval r (SVar 784)) by (apply uval_add_small; lia). rewrite E6 in C3.
  assert (E7 : uval r (SAlu ALU_ADD (SVar 431) (SVar 784)) = uval r (SVar 431) + uval r (SVar 784)) by (apply uval_add_small; lia). rewrite E7 in C4.
  pose proof (amin1_rng r (SVar 422)) as M1. pose proof (amin1_rng r (SVar 425)) as M2. pose proof (amin1_rng r (SVar 428)) as M3'. pose proof (amin1_rng r (SVar 431)) as M4.
  pose proof (amin1_rng r (SVar 772)) as M5. pose proof (amin1_rng r (SVar 775)) as M6. pose proof (amin1_rng r (SVar 778)) as M7. pose proof (amin1_rng r (SVar 781)) as M8.
  unfold finVf, finKf, LAr_f, LAX, LAK, LAXK, A1, AK1, HF.cVF, pLNL, pPOS, pNX, vLEN. cbv beta iota delta [bsumV bsumK bival lfval bi_v bi_k bi_f bi_c].
  repeat match goal with |- context [aval r (ASv ?e)] => change (aval r (ASv e)) with (uval r e) end. rewrite E2.
  clear HF EX EY. split; [lia|]. split; [lia|].
  unfold bd_nn. repeat constructor; cbv beta iota delta [bival lfval bi_v bi_k bi_f bi_c];
    repeat match goal with |- context [aval r (ASv ?e)] => change (aval r (ASv e)) with (uval r e) end; rewrite ?E2; lia.
Qed.

Lemma rates_f_holds : ltac2:(tb__ "0|0|
S10S2dS12S13R1A1S14S19S4eA1A1A3S2dS12S13R2A1S77A3F_;Fr;").
Proof.
  intros r HF. pose proof af_checks_rt as (_ & _ & EQ & EQA & EQ1 & EQ2 & EQ3 & EQ4).
  fact HF (SPUle (SVar 480) (SLit 67108864)) F1. fact HF (SPUle (SAlu ALU_ADD (SVar 480) (SVar 481)) (SVar 14)) F2.
  fact HF (SPUle (SVar 14) (SLit 67108864)) F3. fact HF (SPUle (SVar 490) (SVar 480)) F4. fact HF (SPUle (SVar 480) (SVar 476)) F5.
  fact HF (SPUle (SVar 770) (SAlu ALU_ADD (SVar 481) (SVar 480))) F6. fact HF (SPUle (SVar 476) (SVar 770)) F8. fact HF (SPUle (SVar 481) (SLit 67108864)) F9.
  fact HF (SPUle (SAlu ALU_ADD (SVar 784) (SVar 476)) (SAlu ALU_ADD (SVar 481) (SVar 480))) A0.
  fact HF (SPUle (SVar 784) (SVar 785)) B1. fact HF (SPUle (SVar 785) (SLit 4294967295)) B2.
  fact HF (SPUle (SVar 772) (SAlu ALU_ADD (SVar 422) (SMd M_MUL (SLit 3) (SVar 784)))) C1. fact HF (SPUle (SVar 775) (SAlu ALU_ADD (SVar 425) (SVar 784))) C2.
  fact HF (SPUle (SVar 778) (SAlu ALU_ADD (SVar 428) (SVar 784))) C3. fact HF (SPUle (SVar 781) (SAlu ALU_ADD (SVar 431) (SVar 784))) C4.
  fact HF (SPUle (SVar 422) (SVar 580)) G1. fact HF (SPUle (SVar 425) (SVar 581)) G2. fact HF (SPUle (SVar 428) (SVar 582)) G3. fact HF (SPUle (SVar 431) (SVar 583)) G4.
  fact HF (SPUle (SVar 580) (SMd M_MUL (SLit 3) (SVar 490))) R1. fact HF (SPUle (SVar 581) (SVar 490)) R2. fact HF (SPUle (SVar 582) (SVar 490)) R3. fact HF (SPUle (SVar 583) (SVar 490)) R4.
  fact HF (SPUle (SVar 587) (SVar 490)) R5. fact HF (SPUle (SVar 588) (SMd M_MUL (SLit 3) (SVar 490))) R6. fact HF (SPUle (SVar 589) (SMd M_MUL (SLit 3) (SVar 490))) R7.
  fact HF (SPUle (SVar 590) (SMd M_MUL (SLit 37) (SVar 490))) R8.
  rewrite h_ule in F1, F2, F3, F4, F5, F6, F8, F9, A0, B1, B2, C1, C2, C3, C4, G1, G2, G3, G4, R1, R2, R3, R4, R5, R6, R7, R8. rewrite uval_lit in F1, F3, F9, B2 by lia.
  pose proof (uval_range r (SVar 785)) as R785.
  pose proof (uval_range r (SVar 481)) as R481. pose proof (uval_range r (SVar 480)) as R480. pose proof (uval_range r (SVar 770)) as R770. pose proof (uval_range r (SVar 784)) as R784.
  pose proof (uval_range r (SVar 476)) as R476. pose proof (uval_range r (SVar 490)) as R490. pose proof (uval_range r (SVar 14)) as R14.
  pose proof (uval_range r (SVar 422)) as R422. pose proof (uval_range r (SVar 425)) as R425. pose proof (uval_range r (SVar 428)) as R428. pose proof (uval_range r (SVar 431)) as R431.
  pose proof (uval_range r (SVar 772)) as R772. pose proof (uval_range r (SVar 775)) as R775. pose proof (uval_range r (SVar 778)) as R778. pose proof (uval_range r (SVar 781)) as R781.
  pose proof (uval_range r (SVar 580)) as R580. pose proof (uval_range r (SVar 581)) as R581. pose proof (uval_range r (SVar 582)) as R582. pose proof (uval_range r (SVar 583)) as R583.
  pose proof (uval_range r (SVar 587)) as R587. pose proof (uval_range r (SVar 588)) as R588. pose proof (uval_range r (SVar 589)) as R589. pose proof (uval_range r (SVar 590)) as R590.
  assert (E1 : uval r (SAlu ALU_ADD (SVar 480) (SVar 481)) = uval r (SVar 480) + uval r (SVar 481)) by (apply uval_add_small; lia). rewrite E1 in F2.
  assert (E2 : uval r (SAlu ALU_ADD (SVar 481) (SVar 480)) = uval r (SVar 481) + uval r (SVar 480)) by (apply uval_add_small; lia). rewrite E2 in F6, A0.
  assert (KM : forall k e, 0 <= k <= 64 -> uval r e <= 2 ^ 32 -> uval r (SMd M_MUL (SLit k) e) = k * uval r e) by (intros k e Hk He; pose proof (uval_range r e); apply uval_mul_lit; [lia | nia]).
  rewrite !KM in R1, R6, R7, R8 by lia.
  assert (E3 : uval r (SAlu ALU_ADD (SVar 784) (SVar 476)) = uval r (SVar 784) + uval r (SVar 476)) by (apply uval_add_small; lia). rewrite E3 in A0.
  assert (E4 : uval r (SAlu ALU_ADD (SVar 422) (SMd M_MUL (SLit 3) (SVar 784))) = uval r (SVar 422) + 3 * uval r (SVar 784)) by (rewrite uval_add_small; rewrite KM by lia; lia). rewrite E4 in C1.
  assert (E5 : uval r (SAlu ALU_ADD (SVar 425) (SVar 784)) = uval r (SVar 425) + uval r (SVar 784)) by (apply uval_add_small; lia). rewrite E5 in C2.
  assert (E6 : uval r (SAlu ALU_ADD (SVar 428) (SVar 784)) = uval r (SVar 428) + uval r (SVar 784)) by (apply uval_add_small; lia). rewrite E6 in C3.
  assert (E7 : uval r (SAlu ALU_ADD (SVar 431) (SVar 784)) = uval r (SVar 431) + uval r (SVar 784)) by (apply uval_add_small; lia). rewrite E7 in C4.
  assert (ES : uval r (SAlu ALU_SUB (SVar 770) (SVar 476)) = uval r (SVar 770) - uval r (SVar 476)) by (apply uval_sub_le; exact F8).
  assert (EE : uval r xE1 = uval r (SVar 480) + uval r (SVar 481) + 1).
  { unfold xE1, pE0, pPOS, pLNL. rewrite uval_add_small by (rewrite uval_add_small, uval_lit by lia; lia). rewrite uval_add_small by lia. rewrite uval_lit by lia. lia. }
  assert (GA : forall g k, 0 <= k <= 64 -> uval r g <= 2 ^ 40 -> uval r (SAlu ALU_ADD g (kb k (SVar 784))) = uval r g + k * uval r (SVar 784)).
  { intros g k Hk Hg. pose proof (uval_range r g). unfold kb. rewrite uval_add_small; rewrite KM by lia; nia. }
  assert (GB : forall g, uval r g <= 2 ^ 40 -> uval r (SAlu ALU_ADD g (SVar 784)) = uval r g + uval r (SVar 784)) by (intros g Hg; pose proof (uval_range r g); apply uval_add_small; lia).
  unfold rates_f, gMI', gFV', gMM', gSG', gCO', gRP', gTR', gTS', gMI, gFV, gMM, gSG, gCO, gRP, gTR, gTS. rewrite EQ, EQA, EQ1, EQ2, EQ3, EQ4. unfold pCP.
  repeat (apply Forall_cons; [apply (proj2 (h_ule _ _ _)); unfold kb; rewrite ?KM by (rewrite ?EE; lia); rewrite ?EE; fold (kb 3 (SVar 784)); fold (kb 37 (SVar 784));
                              rewrite ?GA, ?GB by lia; try (rewrite uval_add_small; rewrite ES; [|lia]); lia|]).
  constructor.
Qed.

Section Sum.
Variable AInv : ltac2:(tb__ "0|0|
S83S10S5S1bQ40A1A1S40OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
S6cS2VAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
S0S7dVCST;R1A2S29S2bZ0R2A2S2cR2S82A2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S0S7dVXGL;R1A2S29S2bZ0R2A2S2cR2S82A2A2F_;Fa;").
Hypothesis HXlits : ltac2:(tb__ "0|0|
S0S88R1A1S7dVXGL;R2A2F_;Fa;").
Hypothesis LFLAG : law_flag_stmt AInv.
Hypothesis LFSH : law_fshadow_stmt AInv.
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S5S3S3S0S0A2S0A2A1").
Variable BX : bxt.
Hypothesis HBX : BXok_d 7 BX.
Variable rho0 : valuation.

Hypothesis HFF3 : ltac2:(tb__ "0|1|
S2aS6S81Z3S2eS3S3S0S0A2M0S0A2G0SaG0S0A2VFF;A4A2U0A3").
Hypothesis HFF6 : ltac2:(tb__ "0|1|
S2aS6S81Z6S2eS3S3S0S0A2M0S0A2G0SaG0S0A2VFF;A4A2U0A3").
Let HNP : NP_okA NP := NP_okA_intro NP eq_refl.
Let P0 : ltac2:(tb__ "0|0|
S10OFr;") := ltac2:(tb__ "0|0|
S35VCST;VFB;VFF;A3").
Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S22VAInv;VCST;VXGL;S79VKc;Vrho0;VP0;VFB;VFF;VBX;S20Vnd;Ac").
Let JAFv (Phi : valuation -> Prop) (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S3aVAInv;VCST;VXGL;S79VKc;Vrho0;VP0;VFB;VFF;VBX;S20VPhi;Vnd;Ad").

Lemma HIN_f : ltac2:(tb__ "0|1|
S10S49S83S10S5S1bQ40A1A1S40S2dS12S13R6A1S14S19S4cA1A1A3VP0;Vrho0;A1S7eS79Vrho0;R8A3VAInv;R7R6R5R4A4S23Vrho0;R8A2S8aRbS85S84R9A1A1A2S24VFB;RaA2S25VFF;RbA2S28VFB;RcReSbS3S11S11A2S4aS52A3M0A4S8bRfG0A2S8cR10G0A2S26VFF;RfR11S34A4S29S90VCST;Vrho0;VFB;VFF;R12S4aS34S4dA8S29S91VCST;VXGL;Vrho0;VFB;VFF;R12S4aS34S51A9S37VCST;S89VFB;R12S4aA3S8fVFF;R12S34A3S3cS3dR12S4dR11A3S55A2A4A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FAi;Fms;Frho;").
Proof.
  intros rho ms Ai rho1 tp1 md1 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR.
  pose proof af_checks2 as (CR & CX & CLN).
  pose proof (T_ok_T0 rho0 rho Ai HT HTK) as HT0.
  assert (HNk : tvinA FB Ai rho kept_f) by (apply (tvinA_sublist FB Ai rho (kept_f ++ passed_f)); [intros t Ht; apply in_or_app; left; exact Ht | exact HN]).
  assert (HDk : tvd rho kept_f) by (exact (tvd_app_l rho kept_f passed_f HD)).
  assert (HZk : tvz rho kept_f) by (apply (tvz_sublist rho (kept_f ++ passed_f)); [intros t Ht; apply in_or_app; left; exact Ht | exact HZ]).
  split; [|split].
  - apply (robjs_chkC_sound AInv CST ALA HCST rho0 FB FF Ai rho _ kept_f frL extra_f R_f rho1 tp1 md1 HM HF HT HT0 HNk HDk HZk HFR CR).
    intros o a Ho HE Hr. unfold extra_f in HE. apply lazy_orb_prop in HE as [HE|HE].
    + exact (extraLO_pclMA CST rho0 FB FF rho kept_f frL o a Hav HP0 HE Hr).
    + exact (robj_ent_pclMA CST rho0 FB FF rho _ _ kept_f frL o a HF CLN HT0 HZk lines_in_kept_f HE Hr).
  - apply (xrs_chkC_sound AInv CST XGL ALA HXlits rho0 FB FF Ai rho _ kept_f frL xextraLO Xk_f rho1 tp1 md1 HM HF HT HT0 HNk HDk HZk HFR CX).
    intros r a Hr HE Ha. left. exact (xextraLO_pclMA CST rho0 FB FF rho kept_f frL r a Hav HP0 HE Ha).
  - pose proof af_checks as (_ & _ & _ & _ & _ & Cta & _).
    destruct HP0 as (Ptxt & Pcfg & Plnk).
    assert (AG : forall v e, e = SVar v -> (v < NP)%positive -> uval rho e = uval rho0 e).
    { intros v e -> Hv. unfold uval. cbn [eval]. rewrite <- (proj1 Hav v Hv). reflexivity. }
    unfold HFI.P0_hf, P0_builder. rewrite !rw_call'.
    change (wsub_get s_f 15) with vBUF. change (wsub_get s_f 18) with vLEN. change (wsub_get s_f 12) with bA. change (wsub_get s_f 58) with alA.
    repeat change (bv_unsigned (eval rho ?e)) with (uval rho e).
    fact HF (SPUle vF (SLit 140737479964672)) HvF. rewrite h_ule, uval_lit in HvF by lia.
    assert (E544 : uval rho (SLit 544) = 544) by (apply uval_lit; lia). assert (E464 : uval rho (SLit 464) = 464) by (apply uval_lit; lia).
    assert (EbA : uval rho bA = uval rho vF + 544) by (unfold bA; rewrite <- E544; apply uval_add_small; rewrite E544; lia).
    assert (EalA : uval rho alA = uval rho vF + 464) by (unfold alA; rewrite <- E464; apply uval_add_small; rewrite E464; lia).
    assert (HinF : In (uval rho vF, fs_frame_size 5, uval rho vFL) (FFx FF rho frL)).
    { apply In_FFx. right. exists (vF, 5, vFL). split; [left; reflexivity | reflexivity]. }
    change (fs_frame_size 5) with 2048 in HinF.
    split; [split; [|split]|split].
    + intros a Ha. unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC.pclMA. rewrite (T0_calleeA NP rho0 s_f rho R_f ms Hav Cta). fold (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC.pclMA CST rho0 (FBx FB rho kept_f) (FFx FF rho frL) a).
      apply (pclMA_mono CST rho0 FB (FBx FB rho kept_f) FF (FFx FF rho frL) a); [intros x Hx; apply In_FBx; left; exact Hx | intros x Hx; apply In_FFx; left; exact Hx |].
      apply Ptxt. rewrite <- (AG 13%positive vBUF eq_refl ltac:(reflexivity)), <- (AG 14%positive vLEN eq_refl ltac:(reflexivity)). exact Ha.
    + exists (uval rho vF), 2048, (uval rho vFL). split; [exact HinF|]. rewrite EbA. lia.
    + exists (uval rho vF), 2048, (uval rho vFL). split; [exact HinF|]. rewrite EalA. lia.
    + unfold FFx. rewrite map_app, ccount_app. cbn [map fst frL]. rewrite HFF3. reflexivity.
    + unfold FFx. rewrite map_app, ccount_app. cbn [map fst frL]. rewrite HFF6. reflexivity.
Qed.

Section X.
Variable TR : assn -> assn -> Prop.
Variable FAM : ltac2:(tb__ "0|0|
S0S5S1bQ40A1A1S2fF_;F_;").
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S1dS18S10S5S1bQ40A1A1S2fS2dS12S13R3A1S14S19R4A1A1A3VTR;S1cS2R6R5R4R3A5R2A2M0F_;G0F_;FQ;Ftp;Frho;FS;FJ;").
Hypothesis TR_ex : forall (T : Type) (J : T -> jpredA) S rho tp (Q : assn),
  (forall x, TR (SPA segs (J x) S rho tp) Q) -> TR (SPA segs (fun r p t m => exists x, J x r p t m) S rho tp) Q.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S2fS2fS2fS32R3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_pureP : ltac2:(tb__ "0|1|
S2fOS2fS32R4R1A1R4F_;Fw;R3VTR;R5R3A2M0F_;G0F_;F_;FQ;FX;FP;").
Hypothesis TR_callP : ltac2:(tb__ "0|5|
S1dS1dS18S18S3eS5S17A1M0S5S3S18S5aA2M1A1S5S3S11S11A2M2A1S2fS10S5S1bQ40A1A1M3G2S36G2R1R5A3S36G2R2S1aRbA1A3F_;Fr;S2aSeG0A1S5dRaR9R8A3SdG0R7A2A3S2aS9S5cRbRaR9R8S2eG1S18SaS18S5aA2R7A4A5S7A3S10G3VTR;S1cS2RfRdR2R1A5S59S2S15S19RdA1A1R2R1RaA5A2Ftp1;Frho1;S5S41A1M4S49S40S1eS2R9R8R10S4G4S6dR3S6eR2R1A2A4A5R13RaR9R4R2A4R13S3cS3dRbRfS3fR3RaR4A3A3R10A2RaR5R3A4F_;F_;Fmd;Fms;Ftr;S18S5aG4S49S40S10G3G4S49S40S36G1S4S18S5aRaR9A4R14A3S1eS2R12R11R19S4G4S6dR9S6eR8R7A2A4A5R1cR13R12RaR8A4S7eS15S19R1aA1A1S3cS3dR14R18S3fR9R13RaA3A3R19A2R8A3S1eS2R9R8ReS4G4S6dR7S6eR6R5A2A4A5ReS3cS3dR16R1aS3fRbR15RcA3A3R1bA2R15RaR9R8R6A6S29S8dR17S3fRcR16RdA3R1bR1cR1dR10R1eR19RbA9S10S7fR18S3fRdR17ReA3R1cR1dS19R1eA1S19R1fA1S19R11A1R1RcA9VTR;S1cS2S5bR11S3cS3dR19R1dS3fReR18RfA3A3R1eA2R18RdRcA5S8eR1eR1fR12R20R1dR1bA6R2RcA5R1aA2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S1cS2R11RfR8R7A5R9A2F_;F_;F_;F_;F_;F_;Ftp;Frho;FQ;FXk;FPosts;FR;Fs;FPre;FC;FJp;FJ;").
Hypothesis TR_JAF : ltac2:(tb__ "0|0|
S10OF_;S1fS18S10S5S1bQ40A1A1S2fR6R3A1VTR;S1cS2VJAv;R6A1R5R4R3A5R2A2F_;VTR;S1cS2VJAFv;R7R6A2R5R4R3A5R2A2F_;FQ;Ftp;Frho;FA;Fnd;FPhi;").
Hypothesis CHF : ltac2:(tb__ "0|1|
S5S3S0S0A2M0A1S5S3G0S0A2A1S61S10S5S1bQ40A1A1S5fZ6R3A2VTR;S1cS2S21VAInv;VCST;VXGL;VKc;S37VCST;R6R5A3R6R5R4S20S7bS57S7S71A3AaS70R3R2A5S59S2S6fR3R2S7cVAInv;VCST;VXGL;VKc;S37VCST;A1S20S4bR6R5R4AaA5A2F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Hypothesis CUTV : ltac2:(tb__ "0|5|
S18S1fS6S3S0S11A2M0S10S5S1bQ40A1A1M1S0G1S36S3S3S3S18S1fA2M2S6A2M3G0A2S4G3G0S4G2S6S4S18S1fR8R7A4R6A4R5A4S74A3S39S56R7R5A3S29S2bZ0S38S4G3G0S4G2S6S4S18S1fRaR9A4R8A4R7A4R6A2M4A2S2cG4R4A2A2VTR;S1cS2VJAv;RaA1RbR7R6A5VFAM;R5R4A2A2F_;F_;F_;Ftp0;Fb;Ftp;Frho;Frv;Fk;Fnd;FT;").

Theorem arm_f : ltac2:(tb__ "0|2|
S10S5S1bQ40A1A1M0G0VTR;S1cS2VJAFv;S33S42A2S48R3R2A5VFAM;S38S4S3S3S18S1fA2M1S6A2S3S0S11A2S4G1S6S4S18S1fS48S42A4U1A4S4S0S11S43S44Z11S46A2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros HPHI.
  pose proof af_checks as (Cxf & CEf & Cfb & Cent & Cchk & Cta & Cdom & Ctvs & Cam & Cpd & Cptv & Cptv' & Cpbd & Cxk & Chand & PP1 & PP2 & PWc & PWy & Cnb & Cbr & Cnp & Cnx & _).
  pose proof af_checks2 as (_ & _ & CLN).
  set (ndv := NDA tv_f frL bd_f (AHead pH true)).

  apply (TR_pre (SPA segs (JAv ndv) E_f rho tp)).
  { intros w Hw. rewrite <- CEf. apply (SPA_refacts_JA segs); [| exact Cfb |].
    - apply (SPA_axforms segs (JAv ndv) xf_f rho E_hf E_f1 tp w Cxf).
      unfold ndv, tv_f. apply (SPA_bd_permb segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue _ frL (bdA A1) bd_f _ E_hf rho tp w Cpbd).
      apply (SPA_tv_permb segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tvL _ frL (bdA A1) _ E_hf rho tp w Cptv). exact Hw.
    - intros tr md _ HF1. apply Forall_app. split; [exact (room_f_holds rho HF1) | exact HF1]. }
  apply TR_facts. intros HF.
  apply (TR_pureP _ (uval rho xLD <> 0)).
  { intros [tr [ms md]] [_ (Ai & kc & Hav & _ & _ & HT & _ & _ & (_ & _ & HZ) & _)]. cbn [nd_tv ndv] in HZ.
    pose proof (T_of_TPA NP rho0 rho Ai Hav ltac:(reflexivity) HT) as HTK.
    apply (lines_nz rho _ (topG (aa_geom Ai)) tv_f HF CLN HTK HZ). unfold tv_f. apply in_or_app. left. exact lines_in_kept_f. }
  intros Hdnz.

  unfold ndv, tv_f.
  apply (client_callT_k segs AInv CST XGL ALA HCST HXGL NP Kc rho0 P0 FB FF BX PTrue HKc HBX (HFI.P0_hf CST) PTrue (fun _ H => H) (fun _ _ _ H => H)
           HF.Pre_hf (ndh h0 true HF.nd0) PDk_f NPH eq_refl eq_refl eq_refl TR TR_facts TR_ex TR_pre TR_callP CHF eq_refl
           E_f s_f R_f Xk_f rho tp kept_f passed_f frL bd_f brest_f (AHead pH true) (FAM (efmeasA (E_hf, ndA1, 1%nat, (RL, VLA 17 z0)) rho) tp0)
           Cxk Cent Cchk Cta Cdom Cnp Cnb Cbr Ctvs Cam).
  -
    rewrite Chand. unfold payA.
    apply (pay_okF_split_semF _ _ (SLit 0) 0 bd_f _ payC_f payX_f payY_f PP1 PP2 PWc PWy (Z.le_refl 0)). intros r HFr Hnn. exact (pay_site_f r HFr Hnn).
  - exact Cpd.
  - intros Ai ms HF' HP0 Hav HBf HFF HN HD HZ HFR (rho1 & tp1 & md1 & HM) HT HTK.
    exact (HIN_f rho ms Ai rho1 tp1 md1 HF' HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR).
  -
    intros [[Ld ndL] PsiL] rho' tp' Hd Hag HK _. rewrite Cnx in Hag.
    assert (HPHI' : tblB rho').
    { fact HF (SPUle (SVar 30) (SLit 140737479966720)) HtB. rewrite h_ule, uval_lit in HtB by lia.
      fact HF (SPUle (SLit 140735332483072) (SVar 30)) HtA. rewrite h_ule, uval_lit in HtA by lia.
      destruct (lines_blk rho _ (uval rho (SVar 30)) HF CLN ltac:(split; [reflexivity | lia])) as (_ & HiC & HcK & Hk32 & _ & HdT).
      apply (tblB_kept rho rho' (V_B_agree rho rho' Hag)); [| exact HiC | exact HcK | exact HPHI].
      apply (keptK_lines CST FB FF rho0 rho kept_f frL rho' HK lines_in_kept_f Hdnz); [lia | unfold B32, Lib_vec_reserve.B32; lia]. }
    fact HF (SPUle xLC vLEN) HcL. rewrite h_ule in HcL. fact HF (SPUle vLEN (SLit 67108864)) HL26. rewrite h_ule, uval_lit in HL26 by lia.
    fact HF (SPUlt pI xLC) HiC. rewrite h_ult in HiC.
    pose proof af_checks_nd as (Cndo & Cndf & CTo & CTf & Bo & Bf & Tio & Tif & _).
    pose proof af_checks_rt as (RT & Rfb & _).
    cbn [PDk_f liftPD PDh HFI.PD_hf HFE.Posts_hf map In fst snd] in Hd. destruct Hd as [Hd|[Hd|[]]]; injection Hd as <- <- <-; cbn [fst snd].
    +
      rewrite CTf, Cndf.
      apply (TR_pre (SPA segs (JAv nd_f_f) T_f_f rho' tp')).
      { intros w Hw. rewrite <- Tif. apply SPA_tidy. exact (SPA_axforms segs (JAv nd_f_f) (xfb_f T_f_f0) rho' T_f_f0 B_f_f tp' w Bf Hw). }
      apply TR_facts. intros HFf. pose proof af_checks_payf as (QP1 & QP2 & QPay & _ & _).
      apply (TR_pre (SPA segs (JAv nd_f_fX) T_f_f rho' tp')).
      { intros w Hw. unfold nd_f_fX, nd_f_f in *.
        exact (SPA_bd_repay AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tv_f_f frL (AHead pH true) bd_f_f commf_f Xf_f Yf_f bd_f_fX _ T_f_f rho' tp' w QP1 QP2 HFf QPay Hw). }
      apply (CUTV T_f_f nd_f_fX 1%nat (RL, VLA 10 z0) rho' tp'); [right; left; reflexivity | exact HPHI' |].
      apply (VLA_lt rho rho' 17 10 z0 E_hf T_f_f ndA1 nd_f_fX 1%nat 1%nat); [symmetry; apply (proj1 Hag); reflexivity | symmetry; apply (proj1 Hag); reflexivity | exact HiC | lia | unfold z0; rewrite uval_lit by lia; lia | lia | lia].
    +
      rewrite CTo, Cndo.
      apply (TR_pre (SPA segs (JAv nd_f_ok) T_f_ok rho' tp')).
      { intros w Hw. rewrite <- Tio. apply SPA_tidy. exact (SPA_axforms segs (JAv nd_f_ok) (xfb_f T_f_ok0) rho' T_f_ok0 B_f_ok tp' w Bo Hw). }
      apply TR_facts. intros HFo. pose proof af_checks_pay as (PQ1 & PQ2 & PWy' & _).
      apply (TR_pre (SPA segs (JAv nd_f_okX) T_f_okR rho' tp')).
      { intros w Hw. rewrite <- RT. apply (SPA_refacts_JA segs); [| exact Rfb | intros tr md _ _; apply Forall_app; split; [exact (rates_f_holds rho' HFo) | exact HFo]].
        unfold nd_f_okX, nd_f_ok in *.
        exact (SPA_bd_repay_sem AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tv_f_ok frL (AHead pH true) bd_f_ok comm_f Xs_f Ys_f bdX_f _ T_f_ok rho' tp' w PQ1 PQ2 PWy' HFo (pay_f rho') Hw). }
      apply (CUTV T_f_okR nd_f_okX 1%nat (RL, VLA 10 z0) rho' tp'); [left; reflexivity | exact HPHI' |].
      apply (VLA_lt rho rho' 17 10 z0 E_hf T_f_okR ndA1 nd_f_okX 1%nat 1%nat); [symmetry; apply (proj1 Hag); reflexivity | symmetry; apply (proj1 Hag); reflexivity | exact HiC | lia | unfold z0; rewrite uval_lit by lia; lia | lia | lia].
Qed.
End X.

Lemma Lok_f_latch : ltac2:(tb__ "0|1|
S10S5S1bQ40A1A1S32S33R3A1S1cS2VJAv;S76A1S75R4R3R2A6S29S33S3cR5S78A2M0A1S1cS2VJAv;S45A1S58G0R4R3A6A2F_;F_;Fw;Ftp;Frho;").
Proof.
  intros rho tp w HP HS. pose proof af_checks_exit as (Xe & Xid & Xnp & Xnb & Xtv & Xfr & Xbd & Xam & XV & _ & _ & Xperm).
  destruct (latch_exit AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc Lok_f X_latch s_latch_f nd_f_okX tv_f (bdX 0) (AHead pH true) tblB V_B rho tp w
              tblB_reads Xe Xid Xnp Xnb Xtv Xfr Xbd Xam XV HP HS) as [HP' HS'].
  split; [exact HP'|]. unfold ndX0, ndL. exact (SPA_tv_permb segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tv_f tvL frL (bdX 0) (AHead pH true) X_latch _ tp w Xperm HS').
Qed.

Section Safety.
Variable ok : world -> Prop.
Hypothesis Hok : ltac2:(tb__ "0|0|
S27S2VKc;Vok;A3").
Hypothesis AC : ltac2:(tb__ "0|0|
S6aS2S69VAInv;VCST;VXGL;A5").
Hypothesis SSC : ltac2:(tb__ "0|0|
S0S36S0R1S8S0Z0S8S0Zf5S8S0Zf8ScS0A1A3A3A3A3S86S2S69VAInv;VCST;VXGL;R2A6F_;Fxx;").
Hypothesis CHFs : HFI.handle_f_stmt.
Variable FAMQ : list word -> assn.
Hypothesis XLATCH : ltac2:(tb__ "0|1|
S10S5S1bQ40A1A1M0G0S31S2Vok;S1cS2VJAFv;S33S45A2S58R3R2A5VFAMQ;R1A1A4Ftp0;Ftp;Frho;").
Hypothesis XLATCHE2 : ltac2:(tb__ "0|1|
S10S5S1bQ40A1A1M0G0S31S2Vok;S1cS2VJAFv;S33S47A2S7aR3R2A5VFAMQ;R1A1A4Ftp0;Ftp;Frho;").

Lemma CHF_T : ltac2:(tb__ "0|1|
S5S3S0S0A2M0A1S5S3G0S0A2A1S61S10S5S1bQ40A1A1S5fZ6R3A2S31S2Vok;S1cS2S21VAInv;VCST;VXGL;VKc;S37VCST;R6R5A3R6R5R4S20S7bS57S7S71A3AaS70R3R2A5S59S2S6fR3R2S7cVAInv;VCST;VXGL;VKc;S37VCST;A1S20S4bR6R5R4AaA5A4F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Proof.
  intros FBc FFc BXc rho1 tp1 HB. unfold PDk_f.
  eapply (sum_PostsC_k segs AInv CST XGL Kc (HFI.P0_hf CST) PTrue HF.Pre_hf (ndh h0 true HF.nd0) (PDh HFI.PD_hf h0 true) NPH); [|exact Hok|exact HB].
  intros ok' FBc' FFc' BXc' rho2 tp2 Hok' HB'.
  eapply (JA_frame_sum segs AInv CST XGL ALA Kc (HFI.P0_hf CST) PTrue HF.Pre_hf HF.nd0 HFI.PD_hf NPH h0 true h0_ltH HFI.HamC_hf HFI.HamPD_hf (HFI.P0_hf_mono CST) ok'); [|exact HB'].
  intros FBc'' FFc'' BXc'' rho3 tp3 HB''.
  exact (CHFs AInv CST XGL ALA HCST HXGL LFLAG LFSH Kc HKc FBc'' FFc'' BXc'' HB'' rho3 ok' Hok' AC SSC tp3).
Qed.

Lemma CUTV_T : ltac2:(tb__ "0|5|
S18S1fS6S3S0S11A2M0S10S5S1bQ40A1A1M1S0G1S36S3S3S3S18S1fA2M2S6A2M3G0A2S4G3G0S4G2S6S4S18S1fR8R7A4R6A4R5A4S74A3S39S56R7R5A3S29S2bZ0S38S4G3G0S4G2S6S4S18S1fRaR9A4R8A4R7A4R6A2M4A2S2cG4R4A2A2S31S2Vok;S1cS2VJAv;RaA1RbR7R6A5VFAMQ;R4A1A4F_;F_;F_;Ftp0';Fb;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof.
  intros T nd k rv rho tp b tp0' Hin Hphi _.
  apply (triple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisV k) ok nd T rho tp _ Hphi).
  apply (cfg_sound_JAF segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc PhisV PhisV_reads 200%nat cps_arm NP (map efdrop cutsQ) (map efdrop exitsQ) ok (FAMQ tp0') Hok
           (ejcertAF_jcertAF segs NP PhisV _ _ _ _ _ ecertQ_ok)); [| apply in_map_iff; exists (T, nd, k, rv); split; [reflexivity | exact Hin]].
  intros X ndX kX rho1 tp1 HinX. apply in_map_iff in HinX as ([[[X' nd'] k'] rv'] & E & HinX). cbn in E. injection E as <- <- <-.
  cbn [exitsQ In] in HinX. destruct HinX as [E|[E|[]]]; injection E as <- <- <- <-; cbn [efdrop fst snd].
  -
    apply (triple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisV 1) ok). intros HP1.
    eapply triple_conseq; [| intros w Hw; right; exact Hw | exact (XLATCH (rho_sub rho1 s_latch_f) tp1 tp0')].
    intros w Hw. destruct (Lok_f_latch rho1 tp1 w HP1 Hw) as [HP' Hw']. exact (SPA_JAF_intro segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tblB ndX0 X_latch _ tp1 w Hw' HP').
  - eapply triple_conseq; [| intros w Hw; right; exact Hw | exact (XLATCHE2 rho1 tp1 tp0')].
    intros w Hw. unfold ndXE, ndL. apply (SPA_tv_permb_F segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tblB tv_f tvL frL [LAX 0; LAXK 0] (AHead pH true) X_latchE2 rho1 tp1 w (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 af_checks_exit)))))))))))). exact Hw.
Qed.

Theorem arm_f_T : ltac2:(tb__ "0|1|
S10S5S1bQ40A1A1M0G0S31S2Vok;S1cS2VJAFv;S33S42A2S48R3R2A5VFAMQ;R1A1A4Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0.
  exact (arm_f (triple segs ok) (fun _ tp0 => FAMQ tp0) (TRs_facts segs ok) (TRs_ex segs ok) (TRs_pre segs ok) (TRs_pureP segs ok) (call_soundPA3 segs ok)
           (fun Phi nd A rho tp Q H => triple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue Phi ok nd A rho tp Q H)
           CHF_T CUTV_T rho tp tp0).
Qed.
End Safety.

Section Existence.
Hypothesis ACX : ltac2:(tb__ "0|0|
S6bS2S69VAInv;VCST;VXGL;A5").
Hypothesis SSCX : ltac2:(tb__ "0|0|
S0S36S0R1S8S0Z0S8S0Zf5S8S0Zf8ScS0A1A3A3A3A3S87S2S69VAInv;VCST;VXGL;R2A6F_;Fxx;").
Hypothesis CHFx : HFI.handle_f_stmt_ex.
Variable FAM : ltac2:(tb__ "0|0|
S0S5S1bQ40A1A1S2fF_;F_;").
Hypothesis FAM_mono : ltac2:(tb__ "0|0|
S0S0S5S1bQ40A1A1S32S2bR4R3A2VFAM;R5R3R2A3VFAM;R5R4R3A3F_;F_;Fw;Ftp0;Fb';Fb;").
Hypothesis XLATCH : ltac2:(tb__ "0|2|
S10S5S1bQ40A1A1M0G0S30S2S1cS2VJAFv;S33S45A2S58R3R2A5VFAM;S38S4S3S3S18S1fA2M1S6A2S3S0S11A2S4G1S6S4S18S1fS58S45A4U1A4S4S0S11S43S44Z1S46A2A4A4R3A2R1A2A3Ftp0;Ftp;Frho;").
Hypothesis XLATCHE2 : ltac2:(tb__ "0|2|
S10S5S1bQ40A1A1M0G0S30S2S1cS2VJAFv;S33S47A2S7aR3R2A5VFAM;S38S4S3S3S18S1fA2M1S6A2S3S0S11A2S4G1S6S4S18S1fS7aS47A4U1A4S4S0S11S43S44Z1S46A2A4A4R3A2R1A2A3Ftp0;Ftp;Frho;").

Lemma CHF_E : ltac2:(tb__ "0|1|
S5S3S0S0A2M0A1S5S3G0S0A2A1S61S10S5S1bQ40A1A1S5fZ6R3A2S30S2S1cS2S21VAInv;VCST;VXGL;VKc;S37VCST;R6R5A3R6R5R4S20S7bS57S7S71A3AaS70R3R2A5S59S2S6fR3R2S7cVAInv;VCST;VXGL;VKc;S37VCST;A1S20S4bR6R5R4AaA5A3F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Proof.
  intros FBc FFc BXc rho1 tp1 HB. unfold PDk_f.
  eapply (sum_PostsC_k_ex segs AInv CST XGL Kc (HFI.P0_hf CST) PTrue HF.Pre_hf (ndh h0 true HF.nd0) (PDh HFI.PD_hf h0 true) NPH); [|exact HB].
  intros FBc' FFc' BXc' rho2 tp2 HB'.
  eapply (JA_frame_sum_ex segs AInv CST XGL ALA Kc (HFI.P0_hf CST) PTrue HF.Pre_hf HF.nd0 HFI.PD_hf NPH h0 true h0_ltH HFI.HamC_hf HFI.HamPD_hf (HFI.P0_hf_mono CST)); [|exact HB'].
  intros FBc'' FFc'' BXc'' rho3 tp3 HB''.
  exact (CHFx AInv CST XGL ALA HCST HXGL LFLAG LFSH Kc HKc FBc'' FFc'' BXc'' HB'' rho3 ACX SSCX tp3).
Qed.

Lemma CUTV_E : ltac2:(tb__ "0|5|
S18S1fS6S3S0S11A2M0S10S5S1bQ40A1A1M1S0G1S36S3S3S3S18S1fA2M2S6A2M3G0A2S4G3G0S4G2S6S4S18S1fR8R7A4R6A4R5A4S74A3S39S56R7R5A3S29S2bZ0S38S4G3G0S4G2S6S4S18S1fRaR9A4R8A4R7A4R6A2M4A2S2cG4R4A2A2S30S2S1cS2VJAv;RaA1RbR7R6A5VFAM;R5R4A2A3F_;F_;F_;Ftp0';Fb;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof.
  intros T nd k rv rho tp b tp0' Hin Hphi Hm.
  apply (etriple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisV k) nd T rho tp _ Hphi).
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (FAM_mono _ b tp0' w ltac:(apply Z.lt_le_incl; exact (proj2 Hm)) Hw) |].
  apply (cfg_complete_JAF_b segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc PhisV PhisV_reads 200%nat cps_arm NP cutsQ exitsQ (fun b w => FAM b tp0' w)
           (fun b b' w Hb Hw => FAM_mono b b' tp0' w Hb Hw) ecertQ_ok); [|exact Hin].
  intros X ndX kX rvX rho1 tp1 HinX. cbn [exitsQ In] in HinX. destruct HinX as [E|[E|[]]]; injection E as <- <- <- <-.
  - apply (etriple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisV 1)). intros HP1.
    eapply etriple_conseq; [| intros w Hw; right; exact Hw |].
    2: { pose proof af_checks_exit as (_ & _ & _ & _ & _ & _ & _ & _ & _ & W460 & W467 & _).
         rewrite <- (efmeasA_VLA_sub X_latch Lok_f ndX0 nd_f_okX 1%nat 1%nat RL 1 s_latch_f rho1 W460 W467).
         exact (XLATCH (rho_sub rho1 s_latch_f) tp1 tp0'). }
    intros w Hw. destruct (Lok_f_latch rho1 tp1 w HP1 Hw) as [HP' Hw']. exact (SPA_JAF_intro segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tblB ndX0 X_latch _ tp1 w Hw' HP').
  - eapply etriple_conseq; [| intros w Hw; right; exact Hw | exact (XLATCHE2 rho1 tp1 tp0')].
    intros w Hw. unfold ndXE, ndL. apply (SPA_tv_permb_F segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tblB tv_f tvL frL [LAX 0; LAXK 0] (AHead pH true) X_latchE2 rho1 tp1 w (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 af_checks_exit)))))))))))). exact Hw.
Qed.

Theorem arm_f_E : ltac2:(tb__ "0|2|
S10S5S1bQ40A1A1M0G0S30S2S1cS2VJAFv;S33S42A2S48R3R2A5VFAM;S38S4S3S3S18S1fA2M1S6A2S3S0S11A2S4G1S6S4S18S1fS48S42A4U1A4S4S0S11S43S44Z11S46A2A4A4R3A2R1A2A3Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0.
  exact (arm_f (etriple segs) FAM (TRe_facts segs) (TRe_ex segs) (TRe_pre segs) (TRe_pureP segs) (call_completePA3 segs)
           (fun Phi nd A rho tp Q H => etriple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue Phi nd A rho tp Q H)
           CHF_E CUTV_E rho tp tp0).
Qed.
End Existence.
End Sum.
End Lib_load_obj_af_pf.

