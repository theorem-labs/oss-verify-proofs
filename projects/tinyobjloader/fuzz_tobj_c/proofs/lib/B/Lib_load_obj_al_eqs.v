(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "true"; "bool"; "prod"; "nil"; "nat"; "app"; "list"; "@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "batom"; "bitem"; "ASv"; "BI"; "AMin"; "bd_subst"; "bd_wpos"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SVar"; "ss_facts"; "ss_next"; "SLit"; "SAlu"; "SPUle"; "sprop"; "sprop_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_al_eqs"; "s_latch_l"; "Lok_l"; "nd_l_okX"; "Ys_l"; "bdX_l"; "Xf_l"; "Xs_l"; "Yf_l"; "bd_l_fX"; "comm_l"; "commf_l"; "nd_l_fX"; "cutsQ"; "exitsQ"; "extra_l"; "ndXE_l"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_lglue"; "frL"; "V_B"; "extraLO"; "tvL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "AHead"; "NDA"; "nd_below"; "am_eqb"; "am_subst"; "fr_sub_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_defs"; "NP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loop"; "pH"; "X_latch"; "pLNL"; "pPOS"; "xLD"; "xLK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_al"; "tv_l"; "kept_l"; "tv_l_ok"; "LAr"; "T_l_f"; "T_l_okR"; "qCURl"; "tv_l_f"; "E_l"; "R_l"; "Xk_l"; "bd_l_f"; "bd_l_ok"; "gLC'"; "gLI'"; "k_li"; "qC2l"; "qCl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAG"; "bd_permb"; "tv_permb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_bud"; "LAX"; "LAXK"; "AK1"; "LAK"; "RL"; "VLA"; "bdX"; "z0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub_id_below"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs"; "kb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_armkit2"; "lines_chk"; "robj_ent"; "robjs_chkC"; "xextraLO"; "xrs_chkC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_avn"; "PhisV"; "cps_arm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loopE"; "X_latchE2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "tv_sub_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF"; "bud_le2"; "bud_pay2"; "ejcertAF"; "wsub_id_on"; "@Stdlib.Lists.List"; "In"; "existsb"; "@Stdlib.PArith.BinPos.Pos"; "leb"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_handle_l Lib_handle_l_s2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n9.Lib_vec_reserveN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_l OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_l_s2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_defs Lib_load_obj_pro Lib_load_obj_pro2 Lib_load_obj_loop Lib_load_obj_disp Lib_load_obj_lglue Lib_load_obj_hv0 Lib_load_obj_bud Lib_load_obj_exits Lib_load_obj_loopE Lib_load_obj_armkit Lib_load_obj_armkit2 Lib_load_obj_avn Lib_load_obj_al.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr LOAddr LOLAddr HVAddr HLAddr.

Definition Lok_l : axst := Eval vm_compute in leafL (runL 200 cps_arm T_l_okR) pc_latch 0.
Definition s_latch_l : wsub := ltac2:(tb__ "0|1|
S0S4ScS14A2M0S1ScS14P248S50A4S0G0S1ScS14P249S4fA4S6bS3bS31S1eA1S31S3dA1A3A3A3").
Definition bdX_l : list bitem := Eval vm_compute in bd_subst s_latch_l (bdX 0).
Definition nd_l_okX : ndesc := ltac2:(tb__ "0|0|
S36S44S2dS21S35S3cS2A2A4").
Definition ndX_l : ndesc := ltac2:(tb__ "0|0|
S36S42S2dS5cZ0A1S35S3cS2A2A4").
Definition comm_l : list bitem := Eval vm_compute in bd_common bd_l_ok bdX_l.
Definition Xs_l : list bitem := Eval vm_compute in bd_minus bd_l_ok bdX_l.
Definition Ys_l : list bitem := Eval vm_compute in bd_minus bdX_l bd_l_ok.

Lemma al_checks_pay : ltac2:(tb__ "0|29|
SaS9S3S54S4eS7SeS26S23A3A2S2A3SaS9S3S54S7SeS26S20A3S21A2S2A3SaS9S3S13S20A1S2A3SaS9S8SeA1M0S23S0SeS10Z48Z0M1S0S4SbSdA2M2S1SbSdZ1M3SfS19S60S3fS3eA3A1A4S0G2S1SbSdN1SfS48A1A4S5G2A1M4A3A3G1A4S0SeS45S0SeS59S58A1S0SeS10G3G1S0G2S1SbSdZ18SfS15P1a6A1M5A1M6A4M7S0G2S1SbSdZ60M8S11G5G3G1G3A4A4M9S0G2S1SbSdZ8MaSfS15P1a9A1MbA1McA4MdS0G2S1SbSdG8S11GbG3G1G3A4A4MeS0G2S1SbSdGaSfS15P1acA1MfA1M10A4M11S0G2S1SbSdG8S11GfG3G1G3A4A4M12S0G2S1SbSdGaSfS15P1afA1M13A1M14A4M15S0G2S1SbSdG8S11G13G3G1G3A4A4M16S0G2S1SbSdZ78M17SfS15P1b2A1A1M18A4S0G2S1SbSdZ68M19SfS15P1b5A1A1M1aA4S0G2S1SbSdG17SfS15P1b8A1A1M1bA4G4A3M1cA3A3A3A3A3A3A3A3A3A3G1A4S0SeS10G1G3S0G2S1SbSdZ70M1dG6A4M1eS0G2S1SbSdZ50M1fGcA4M20S0G2S1SbSdG1fG10A4M21S0G2S1SbSdG1fG14A4M22S0G2S1SbSdG1dG18A4S0G2S1SbSdG1fG1aA4S0G2S1SbSdG1dG1bA4G4A3M23A3A3A3A3A3A3G1A4S5SeA1M24A3A3A3A3A3A3SaS9G0S20S0SeS56G1A1S0SeS57G1A1S0SeS10G3G1S0G2G7S0G2G9S0G2GdS0G2GeS0G2G11S0G2G12S0G2G15S0G2G16S0G2S1SbSdG17SfS15P2faA1M25A1M26A4S0G2S1SbSdG19SfS15P2ffA1M27A1M28A4G1cA3A3A3A3A3A3A3A3A3A3G1A4S0SeS10G1G3S0G2G1eS0G2G20S0G2G21S0G2G22S0G2S1SbSdG1dG26A4S0G2S1SbSdG1fG28A4G23A3A3A3A3A3A3G1A4G24A3A3A3A3A3SaS9S14S48S15P2f8A1A3SaS9S14S53G25A3SaS9S14S52G27A3S9S3S37S17S31S47A1A1S1fA2S2A3A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Lemma al_checks_exit : ltac2:(tb__ "0|5|
SaS9S3S33S1eS3dS1dA3S2A3SaS9S3S5fS1dS3bA2S2A3SaS9S3S73S3bS17S31S1eA1M0A1M1A2S2A3SaS9S3S37G1S1fA2S2A3SaS9S3S6cS1dS44S42A3S2A3SaS9S3S3aS1dS2dS2dA3S2A3SaS9S3S6dS16G0A1S12S1dS5cZ0A1A2S21A3S2A3SaS9S3S38S39S1dS35S3cS2A2M2A2G2A2S2A3SaS9S3S70S2eS1dA2S2A3SaS9S14S5eS1dP1ccM3A2S15G3A1A3SaS9S14S5eS1dP1d3M4A2S15G4A1A3S9S3S55S42S30A2S2A3A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition Xf_l : list bitem := ltac2:(tb__ "0|0|
S0SeS45S0SeS59S58A1S5SeA1A3A3").
Definition Yf_l : list bitem := ltac2:(tb__ "0|1|
S0SeS56Z0M0A1S0SeS57G0A1S5SeA1A3A3").
Definition commf_l : list bitem := Eval vm_compute in bd_minus bd_l_f Xf_l.
Definition bd_l_fX : list bitem := Yf_l ++ commf_l.
Definition nd_l_fX : ndesc := ltac2:(tb__ "0|0|
S36S49S2dS25S35S3cS2A2A4").
Definition ndXE_l : ndesc := ltac2:(tb__ "0|1|
S36S42S2dS0SeS56Z0M0A1S0SeS57G0A1S5SeA1A3A3S35S3cS2A2A4").
Lemma al_checks_payf : ltac2:(tb__ "0|2|
SaS9S3S54S4dS7SeS27S22A3A2S2A3SaS9S3S54S7SeS27S24A3S25A2S2A3SaS9S3S6eS16S31S46A1M0A1S18Z0M1A1G1S22S24A5S2A3SaS9S3S37S17G0A1S28A2S2A3S9S8S4S14S14A2A1S49S44A3A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition cutsQ : list efnode := ltac2:(tb__ "0|6|
S0S4S4S4S32S34A2M0S6A2M1S4SbS14A2M2A2M3S1G1G2S1G0S6S1S32S34S47S1fA4U1M4A4S1SbS14S5aS5bZaS5dA2A4M5A4S0G3S1G1G2S1G0S6S1S32S34S46S28A4G4A4G5A4S5G3A1A3A3").
Definition exitsQ : list efnode := ltac2:(tb__ "0|6|
S0S4S4S4S32S34A2M0S6A2M1S4SbS14A2M2A2M3S1G1G2S1G0S6S1S32S34S1eS1fA4U1M4A4S1SbS14S5aS5bZ1S5dA2A4M5A4S0G3S1G1G2S1G0S6S1S32S34S6aS2cA4G4A4G5A4S5G3A1A3A3").
Lemma ecertQ_ok : ltac2:(tb__ "0|0|
S9S3S6fS61S3bS68Uc8S69S3bS29S2aA8S2A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Definition extra_l (o : sobj) : bool := ltac2:(tb__ "0|0|
S3S3L_;S2fVo;A1S2S64Vo;A1X3x2").
Lemma al_checks2 : ltac2:(tb__ "0|1|
SaS9S3S65S16S31S4aA1A1M0S43S2dS2bS4bA5S2A3SaS9S3S67G0S43S2dS66S4cA5S2A3SaS9S3S63G0A1S2A3S9S3S72S1bS1cS1aS51S18ZffffffffA1A2A1G0A3S2A3A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma lines_in_kept_l : ltac2:(tb__ "0|0|
S71S4S14S14A2S1S14S14S40S62Z10S41A2A4S43A3").
Proof. cbn. do 16 right. left. reflexivity. Qed.
