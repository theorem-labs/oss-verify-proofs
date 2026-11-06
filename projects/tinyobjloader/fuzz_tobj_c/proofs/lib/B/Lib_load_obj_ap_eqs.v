(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "true"; "bool"; "prod"; "nil"; "nat"; "app"; "list"; "@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bitem"; "batom"; "ASv"; "BI"; "AMin"; "bd_subst"; "bd_wpos"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SVar"; "ss_facts"; "ss_next"; "SLit"; "SAlu"; "SPUle"; "sprop"; "sprop_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_ap_eqs"; "s_latch_p"; "Lok_p"; "nd_p_okX"; "Ys_p"; "bdX_p"; "Xf_p"; "Xs_p"; "Yf_p"; "bd_p_fX"; "comm_p"; "commf_p"; "nd_p_fX"; "cutsP"; "exitsP"; "extra_p"; "ndXE_p"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_lglue"; "frL"; "V_B"; "extraLO"; "tvL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "AHead"; "NDA"; "nd_below"; "am_eqb"; "am_subst"; "fr_sub_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_defs"; "NP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loop"; "pH"; "X_latch"; "pLNL"; "pPOS"; "xLD"; "xLK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_ap"; "tv_p"; "kept_p"; "tv_p_ok"; "LAr"; "T_p_f"; "T_p_okR"; "qCURp"; "tv_p_f"; "E_p"; "R_p"; "Xk_p"; "bd_p_f"; "bd_p_ok"; "gPI'"; "k_pi"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAG"; "bd_permb"; "tv_permb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_bud"; "LAX"; "LAXK"; "AK1"; "LAK"; "RL"; "VLA"; "bdX"; "z0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub_id_below"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs"; "kb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_armkit2"; "lines_chk"; "robj_ent"; "robjs_chkC"; "xextraLO"; "xrs_chkC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_avn"; "PhisV"; "cps_arm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loopE"; "X_latchE2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "tv_sub_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF"; "bud_le2"; "bud_pay2"; "ejcertAF"; "wsub_id_on"; "@Stdlib.Lists.List"; "In"; "existsb"; "@Stdlib.PArith.BinPos.Pos"; "leb"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_handle_p.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n9.Lib_vec_reserveN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_p OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o5.Lib_handle_p_pf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_defs Lib_load_obj_pro Lib_load_obj_pro2 Lib_load_obj_loop Lib_load_obj_disp Lib_load_obj_lglue Lib_load_obj_hv0 Lib_load_obj_bud Lib_load_obj_exits Lib_load_obj_loopE Lib_load_obj_armkit Lib_load_obj_armkit2 Lib_load_obj_avn Lib_load_obj_ap.
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
SaS9S3S51S4eS7SdS26S23A3A2S2A3SaS9S3S51S7SdS26S20A3S21A2S2A3SaS9S3S13S20A1S2A3SaS9S8SdA1M0S23S0SdS10Z48Z0M1S0S4SbSeA2M2S1SbSeZ1M3SfS19S5dS3fS3eA3A1A4S0G2S1SbSeN1SfS48A1A4S5G2A1M4A3A3G1A4S0SdS45S0SdS56S55A1S0SdS10G3G1S0G2S1SbSeZ18SfS15P1a6A1M5A1M6A4M7S0G2S1SbSeZ60M8S11G5G3G1G3A4A4M9S0G2S1SbSeZ8MaSfS15P1a9A1MbA1McA4MdS0G2S1SbSeG8S11GbG3G1G3A4A4MeS0G2S1SbSeGaSfS15P1acA1MfA1M10A4M11S0G2S1SbSeG8S11GfG3G1G3A4A4M12S0G2S1SbSeGaSfS15P1afA1M13A1M14A4M15S0G2S1SbSeG8S11G13G3G1G3A4A4M16S0G2S1SbSeZ78M17SfS15P1b2A1A1M18A4M19S0G2S1SbSeZ68SfS15P1b5A1A1M1aA4M1bS0G2S1SbSeG17SfS15P1b8A1A1M1cA4G4A3A3A3A3A3A3A3A3A3A3A3G1A4S0SdS10G1G3S0G2S1SbSeZ70M1dG6A4M1eS0G2S1SbSeZ50M1fGcA4M20S0G2S1SbSeG1fG10A4M21S0G2S1SbSeG1fG14A4M22S0G2S1SbSeG1dG18A4M23S0G2S1SbSeG1fG1aA4M24S0G2S1SbSeG1dG1cA4G4A3A3A3A3A3A3A3G1A4S5SdA1M25A3A3A3A3A3A3SaS9G0S20S0SdS53G1A1S0SdS54G1A1S0SdS10G3G1S0G2G7S0G2G9S0G2GdS0G2GeS0G2G11S0G2G12S0G2G15S0G2G16S0G2G19S0G2G1bS0G2S1SbSeG17SfS15P2faA1A1M26A4G4A3A3A3A3A3A3A3A3A3A3A3G1A4S0SdS10G1G3S0G2G1eS0G2G20S0G2G21S0G2G22S0G2G23S0G2G24S0G2S1SbSeG1dG26A4G4A3A3A3A3A3A3A3G1A4G25A3A3A3A3A3SaS9S14S48S15P2f8A1A3S9S3S37S17S31S47A1A1S1fA2S2A3A2A2A2A2A2A2").
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
