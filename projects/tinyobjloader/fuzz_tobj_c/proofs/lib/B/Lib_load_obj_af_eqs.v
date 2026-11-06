(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "true"; "bool"; "prod"; "nil"; "nat"; "app"; "list"; "@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SVar"; "sprop"; "SPUle"; "ss_facts"; "ss_next"; "SAlu"; "SLit"; "sprop_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bitem"; "batom"; "ASv"; "AMin"; "BI"; "bd_subst"; "bd_wpos"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_af_eqs"; "s_latch_f"; "xE1"; "Lok_f"; "nd_f_okX"; "T_f_okR"; "Ys_f"; "bdX_f"; "Xf_f"; "Xs_f"; "Yf_f"; "bd_f_fX"; "comm_f"; "commf_f"; "finKf"; "finVf"; "nd_f_fX"; "qCfvf"; "qCmif"; "qCmmf"; "qCsgf"; "cutsQ"; "exitsQ"; "extra_f"; "ndXE_f"; "rates_f"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_lglue"; "frL"; "V_B"; "extraLO"; "tvL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "AHead"; "NDA"; "nd_below"; "am_eqb"; "am_subst"; "fr_sub_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_defs"; "NP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loop"; "pH"; "X_latch"; "pLNL"; "pPOS"; "xLD"; "xLK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_af"; "tv_f"; "gFV'"; "gMI'"; "gMM'"; "gSG'"; "kept_f"; "tv_f_ok"; "LAr_f"; "T_f_f"; "T_f_ok"; "gCO'"; "gRP'"; "gTR'"; "gTS'"; "tv_f_f"; "E_f"; "R_f"; "Xk_f"; "bd_f_f"; "bd_f_ok"; "qAf"; "qCURf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAG"; "bd_permb"; "tv_permb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs"; "kb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_bud"; "LAX"; "LAXK"; "AK1"; "LAK"; "RL"; "VLA"; "bdX"; "z0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub_id_below"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_armkit2"; "lines_chk"; "robj_ent"; "robjs_chkC"; "xextraLO"; "xrs_chkC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_avn"; "PhisV"; "cps_arm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loopE"; "X_latchE2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "tv_sub_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF"; "bud_le2"; "bud_pay2"; "ejcertAF"; "wsub_id_on"; "@Stdlib.Lists.List"; "In"; "forallb"; "@Stdlib.PArith.BinPos.Pos"; "leb"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_handle_f_defs Lib_handle_f_s2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_defs Lib_load_obj_pro Lib_load_obj_pro2 Lib_load_obj_loop Lib_load_obj_disp Lib_load_obj_lglue Lib_load_obj_hv0 Lib_load_obj_bud Lib_load_obj_exits Lib_load_obj_loopE Lib_load_obj_armkit Lib_load_obj_armkit2 Lib_load_obj_avn Lib_load_obj_af.
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
SaS9S3S61S5eS7S16S28S25A3A2S2A3SaS9S3S61S7S16S28S22A3S23A2S2A3SaS9S3S1cS22A1S2A3SaS9S8S16A1M0S25S0S16S1aZ300Z0M1S0S4SbS17A2M2S1SbS17Z1S18S13S6eS48S47A3A1A4S0G2S1SbS17N1S18SeP302A1A1A4S5G2A1A3A3G1A4S0S16S52S0S16S67S66A1S0S16S2bSeP1a6A1M3SeP1a9A1M4SeP1acA1M5SeP1afA1M6A4S0S16S2aG3G4G5G6A4S5S16A1M7A3A3A3A3A3A3SaS9G0S22S0S16S64G1A1S0S16S65G1A1S0S16S2bSeP304A1M8SeP307A1M9SeP30aA1MaSeP30dA1MbA4S0S16S2aG8G9GaGbA4G7A3A3A3A3A3S9S3S40S12S3aS21A1A1S20A2S2A3A2A2A2A2A2").
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
